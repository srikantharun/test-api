// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Andrew Dickson <andrew.dickson@axelera.ai>

// Thermal  Management Supervisor (TMS).
// Continouous Temperature Monitor
//
`ifndef TMS_CTM_SV
`define TMS_CTM_SV
module tms_ctm #(
  // Channel number
  parameter int  unsigned CH_NUM = 0                                   ,
  // Width of the PVT data
  parameter int  unsigned PVT_TW = 12                                  ,
  // Single Temperature type definition
  parameter type tms_ctm_temp_t = logic [PVT_TW-1:0]                   ,
  // Probe selection type
  parameter type tms_ctm_sel_t  = logic [       5:0]
)(
  // Clock, positive edge triggered
  input  wire                         i_clk                            ,
  // Asynchronous reset, active low
  input  wire                         i_rst_n                          ,

  // pvt sensor input. Pvt clock
  input  tms_ctm_temp_t               i_pvt_temp_value                 ,
  // pvt Conversion complete. Pvt clock
  input  logic                        i_pvt_eoc_ts                     ,
  /// Remote probe selection signal 6'b00_0000: Main probe inside PVT sensor 6'b00_0001 to 6'b11_1111:
  input  tms_ctm_sel_t                i_pvt_bjt_sel_ts                 ,

  // temperature control inputs from csr
  // offset compensation
  input  tms_ctm_temp_t               i_csr_offset_comp                ,
  // thermal shutdown threshold
  input  tms_ctm_temp_t               i_csr_thermal_shutdown_threshold ,
  // thermal warning threshold
  input  tms_ctm_temp_t               i_csr_thermal_warning_threshold  ,
  // throttle on temperature
  input  tms_ctm_temp_t               i_csr_throttle_on_temp           ,
  // throttle off temperature
  input  tms_ctm_temp_t               i_csr_throttle_off_temp          ,

  // thermal throttle override
  input  logic                        i_thermal_throttle               ,
  // temperature status signals to csr
  // thermal shutdown
  output logic                        o_thermal_shutdown               ,
  // thermal wanrning
  output logic                        o_thermal_warning                ,
  // thermal throttle
  output logic                        o_thermal_throttle               ,

  // minimum temperature
  output tms_ctm_temp_t               o_csr_min_temp_value             ,
  // maximimum temperature
  output tms_ctm_temp_t               o_csr_max_temp_value             ,
  // current temperature
  output tms_ctm_temp_t               o_csr_cur_temp_value             ,

  // Enable for threshold outputs
  input  logic                        i_csr_shtdwn_ena                 ,
  input  logic                        i_csr_warn_ena                   ,
  input  logic                        i_csr_throttle_ena               ,

  // register enable. to store temp results in CSR
  output logic                        o_ctm_reg_ena
);

//==============================================================================
// Local parameters
// Offset compensation calculation signed/unsigned selections
// 0: unsigned
// 1: singed
localparam logic        OFFSET_COMP_SIGN_CTRL = 0                    ;

// delay for data valid to match data delay after eoc
localparam int unsigned NB_DELAY              = 2                    ;

// offset compensation result type
// mulitplier add width for both inputs
localparam type         tms_ctm_offset_res_t  = logic[(PVT_TW*2)-1:0];

// delay bus type
localparam type         tms_ctm_delay_t       = logic[NB_DELAY  -1:0];

//==============================================================================
// signal declarations
// pvt end of conversion synchronizer.
logic                data_valid_pre     ;
logic                data_valid         ;
tms_ctm_delay_t      data_valid_d       ;
logic                channel_selected   ;

// offset compensation result
tms_ctm_offset_res_t pvt_temp_offset_res;
// offset compensation roundigng result
tms_ctm_temp_t       pvt_temp_offset_rnd;

// thermal throttle
logic                 thermal_throttle  ;
// thermal shutdown
logic                 thermal_shutdown  ;
// thermal wanrning
logic                 thermal_warning   ;

//==============================================================================
// RTL

//==============================================================================
// PVT input offset compensation
// check if this channel is active
// bjt_sel selects the active probe.
always_comb begin
  channel_selected = (i_pvt_bjt_sel_ts == tms_ctm_sel_t'(CH_NUM));
  // Determine if this channel is active. Update results at pct EOC.
  data_valid       = i_pvt_eoc_ts & channel_selected;
end

// offset compensation
DW02_mult_2_stage #(
  .A_width ( PVT_TW ),
  .B_width ( PVT_TW )
) u_tms_pvt_temp_offset_compensation (
  // measured temperature
  .A       ( i_pvt_temp_value      ),
  // offset compensation register
  .B       ( i_csr_offset_comp     ),
  // Data sign
  .TC      ( OFFSET_COMP_SIGN_CTRL ),
  // Clock
  .CLK     ( i_clk                 ),
  // Mulitplier product
  .PRODUCT ( pvt_temp_offset_res   )
);

// trunces the result
always_comb begin
  pvt_temp_offset_rnd = pvt_temp_offset_res[(PVT_TW*2)-1-:PVT_TW];
end

//==============================================================================
// compare offset temperature with threshold
always_ff @ (posedge i_clk or negedge i_rst_n) begin
  if (!i_rst_n) begin
    thermal_shutdown <= 1'h0;
    thermal_warning  <= 1'h0;
    thermal_throttle <= 1'h0;
    data_valid_d     <=   '0;
    o_ctm_reg_ena    <= 1'h0;
  end else begin
    // delay value to match data delay
    data_valid_d  <= {data_valid_d[0], data_valid};
    // crs register write enable. Allow one cycle for CTM calculation
    o_ctm_reg_ena <=  data_valid_d[NB_DELAY-1];

    // check measured temperature levels vs programmed thresholds
    if (data_valid_d[NB_DELAY-1]) begin
      // Thermal shutdown. temp above threshold
      if (pvt_temp_offset_rnd > i_csr_thermal_shutdown_threshold) begin
        thermal_shutdown   <= 1'h1;
      end else begin
        thermal_shutdown   <= 1'h0;
      end
      // Thermal wanrning. Temp above threshold
      if (pvt_temp_offset_rnd > i_csr_thermal_warning_threshold) begin
        thermal_warning    <= 1'h1;
      end else begin
        thermal_warning    <= 1'h0;
      end
      // Thermal throttle.
      // Throttle on . temp above on  threshold
      // Throttle off. temp below off threshold
      if (pvt_temp_offset_rnd > i_csr_throttle_on_temp) begin
        thermal_throttle <= 1'h1;
      end else if (pvt_temp_offset_rnd < i_csr_throttle_off_temp) begin
        thermal_throttle <= 1'h0;
      end
    end
  end
end

//==============================================================================
// thermal shutdown output. Use CSR shutdown ena to control the output
always_comb begin
 if (i_csr_shtdwn_ena) begin
   o_thermal_shutdown = thermal_shutdown;
 end else begin
   o_thermal_shutdown = 1'h0;
 end
end

//==============================================================================
always_comb begin
  if (i_csr_warn_ena) begin
    o_thermal_warning = thermal_warning;
  end else begin
    o_thermal_warning = 1'h0;
  end
end

//==============================================================================
// force thermal throttle on
always_comb begin
  if (i_thermal_throttle) begin
    o_thermal_throttle = 1'h1;
  end else if (i_csr_throttle_ena) begin
   o_thermal_throttle = thermal_throttle;
  end else begin
    o_thermal_throttle = 1'h0;
  end
end

//==============================================================================
// temperature min/cur/max values
always_ff @ (posedge i_clk or negedge i_rst_n) begin
  if (!i_rst_n) begin
    // set initial min value to 0.5 max value
    o_csr_min_temp_value  <= {1'h1, {PVT_TW-1{1'h0}}};
    o_csr_max_temp_value  <= '0;
    o_csr_cur_temp_value  <= '0;
  end else begin
    // store the temperate limits and current value
    if (data_valid_d[NB_DELAY-1]) begin
      // calculate minimum temp
      if (pvt_temp_offset_rnd < o_csr_min_temp_value) begin
        o_csr_min_temp_value <= pvt_temp_offset_rnd;
      end
      // calcualte maximum temp
      if (pvt_temp_offset_rnd > o_csr_max_temp_value) begin
        o_csr_max_temp_value <= pvt_temp_offset_rnd;
      end
      // current temperature
      o_csr_cur_temp_value   <= pvt_temp_offset_rnd;
    end
  end
end

endmodule
`endif // TMS_CTM_SV
