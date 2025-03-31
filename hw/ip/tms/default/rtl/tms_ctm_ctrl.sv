// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Andrew Dickson <andrew.dickson@axelera.ai>

// Thermal  Management Supervisor (TMS).
// automated Control for the PVT measurement
`ifndef TMS_CTM_CTRL_SV
`define TMS_CTM_CTRL_SV
module tms_ctm_ctrl #(
  parameter int  unsigned NB_TEMP_SENSE     = 12         ,
  parameter type          tms_pvt_bjt_sel_t = logic [5:0],
  parameter type          tms_pvt_sel_t     = logic [3:0]
) (
  // Clock, positive edge triggered
  input  wire                         i_clk              ,
  // Asynchronous reset, active low
  input  wire                         i_rst_n            ,
  // PVT Clock
  input  wire                         i_pvt_clk          ,
  // PVT reset
  input  wire                         i_pvt_rst_n        ,
  // CTM mode enable
  input  logic                        i_ctm_mode_ena     ,
  // PVT interface
  output logic                        o_en_ts            ,
  output logic                        o_en_adc_ts        ,
  output tms_pvt_sel_t                o_sel_ts           ,
  output tms_pvt_bjt_sel_t            o_bjt_sel_ts       ,
  // start of conversion
  output logic                        o_soc_ts           ,
  // end of conversion. Synced to i_clk at top level
  input  logic                        i_eoc_ts
);

//==============================================================================
// Local parameters
localparam int unsigned     DELAYW           = 13                       ;

// Setup delay is specificed at >4us. 13bit count gives max value 8191. With 0.833ns clock delay is ~6.8us
localparam type             tms_delay_t      = logic [DELAYW       -1:0];

localparam type             tms_sel_t        = logic [NB_TEMP_SENSE-1:0];

localparam int unsigned     SENSEW           = 4;
localparam type             tms_sense_mode_t = logic [SENSEW       -1:0];

// temp sensor mode. From datasheet Table 4.3
localparam tms_sense_mode_t SENSOR_MODE      = 4'b0000                  ;

// Synchronizer
localparam int unsigned     NB_SYNC_STAGES   = 2                        ;
localparam logic            SYNC_RESET_VALUE = 1'h0                     ;

localparam int unsigned     NB_SIG_SYNC      = 3                        ;
localparam type             tms_sync_t       = logic [NB_SIG_SYNC  -1:0];

//==============================================================================
// types
typedef enum {CTM_IDLE, CTM_START, CTM_SETUP, CTM_CONV, CTM_DATA, CTM_NXT} ctm_state_t;

//==============================================================================
// signal declarations
ctm_state_t      cur_state       ;
ctm_state_t      nxt_state       ;

logic            en_ts           ;
logic            en_adc_ts       ;
logic            soc_ts          ;
// set probe number
tms_sel_t        sel_cnt         ;

// delay counter
tms_delay_t      delay           ;

// set sense mode
tms_sense_mode_t sense_mode      ;

logic            eoc_ts_redge    ;
logic            eoc_ts_fedge    ;

tms_sync_t       sync_in         ;
tms_sync_t       sync_out        ;

//==============================================================================
// RTL

// Sync single bit outputs from i_clk to the pvt clock
// sync inputs are:  soc_ts, en_adc_ts, en_ts;
always_comb begin
  sync_in = {soc_ts, en_adc_ts, en_ts};
end

for (genvar i=0; i<NB_SIG_SYNC; i++) begin : gen_sync
  axe_tcl_seq_sync #(
    .SyncStages ( NB_SYNC_STAGES   ),
    .ResetValue ( SYNC_RESET_VALUE )
  ) u_axe_tcl_eoc_ts_sync (
    .i_clk      ( i_pvt_clk        ),
    .i_rst_n    ( i_rst_n          ),
    .i_d        ( sync_in [i]      ),
    .o_q        ( sync_out[i]      )
  );
end

// Sync outputs to PVT
always_comb begin
  o_en_ts     = sync_out[0];
  o_en_adc_ts = sync_out[1];
  o_soc_ts    = sync_out[2];
end

//==============================================================================
// RTL
// Edge detect end of conversion
tms_edge_detect u_tms_ts_eoc_edge_detect (
  .i_clk   ( i_clk        ),
  .i_rst_n ( i_rst_n      ),
  .din     ( i_eoc_ts     ),
  .redge   ( eoc_ts_redge ),
  .fedge   ( eoc_ts_fedge ),
  .aedge   (              )  // not used
);


//==============================================================================
// Registers
// Module outputs. Presync
// State machine output decode
// Delay counter
always_ff @ (posedge i_clk or negedge i_rst_n) begin
  if (!i_rst_n) begin
    en_ts        <= 1'h0;
    en_adc_ts    <= 1'h0;
    soc_ts       <= 1'h0;
    sense_mode   <=   '0;
    sel_cnt      <= {{NB_TEMP_SENSE-1{1'h0}}, 1'h1};
    delay        <=   '0;
  end else begin
    en_ts      <= (cur_state == CTM_IDLE) ? 1'h0 : 1'h1;
    en_adc_ts  <= (cur_state == CTM_IDLE) ? 1'h0 : 1'h1;
    soc_ts     <= (cur_state == CTM_IDLE) ? 1'h0 :
                  (cur_state == CTM_NXT ) ? 1'h0 : 1'h1;
    sense_mode <= (cur_state == CTM_IDLE) ?   '0 : SENSOR_MODE;

    if (cur_state == CTM_IDLE) begin
      sel_cnt <= {{NB_TEMP_SENSE-1{1'h0}}, 1'h1};
    end else begin
      // increment channel after measurement completes
      if (eoc_ts_fedge) begin
        sel_cnt <= sel_cnt + {{NB_TEMP_SENSE-1{1'h0}}, 1'h1};
      end else if (sel_cnt >= NB_TEMP_SENSE+1) begin
      // Limit max count to a value channel
        sel_cnt <= {{NB_TEMP_SENSE-1{1'h0}}, 1'h1};
      end else begin
        sel_cnt <= sel_cnt;
      end
    end

    if (cur_state == CTM_SETUP || cur_state == CTM_NXT) begin
      delay  <= delay + {{DELAYW-1{1'h0}}, 1'h1};
    end else begin
      delay  <= '0;
    end
  end
end

// multi bit outputs to pvt - not synced.
// o_bjt_sel_ts. selects active channel
// o_sel_ts.     sets sensor mode. Which is kept constant in auto mode.
always_comb begin
  o_bjt_sel_ts = sel_cnt;
  o_sel_ts     = SENSOR_MODE;
end

//==============================================================================
// Control SM
always_comb begin
  nxt_state = cur_state;

  case(cur_state)
    CTM_IDLE : begin
      if (i_ctm_mode_ena) begin
        nxt_state = CTM_START;
      end
    end
    CTM_START : begin
      nxt_state = CTM_SETUP;
    end
    // Delay TSETUP delay
    CTM_SETUP : begin
      if ((&delay)) begin
        nxt_state = CTM_CONV;
      end
    end
    // wait for ECO
    CTM_CONV : begin
      if (eoc_ts_redge) begin
        nxt_state = CTM_DATA;
      end
    end
    // Wait eoc to be cleared
    CTM_DATA : begin
      if (eoc_ts_fedge) begin
        nxt_state = CTM_NXT;
      end
    end
    // Delay before next measurement.. State 4 from timing diag
    CTM_NXT : begin
      if ((&delay)) begin
        // check mode is still enabled.
        // Otherwise return to idle
        if (!i_ctm_mode_ena) begin
          nxt_state = CTM_IDLE;
        end else begin
          nxt_state = CTM_START;
        end
      end
    end
    default : begin
      nxt_state = CTM_IDLE;
    end
  endcase
end

// state register
always_ff @ (posedge i_clk or negedge i_rst_n) begin
  if (!i_rst_n) begin
    cur_state <= CTM_IDLE;
  end else begin
    cur_state <= nxt_state;
  end
end

endmodule

`endif // TMS_CTM_CTRL_SV
