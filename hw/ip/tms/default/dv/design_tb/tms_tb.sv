// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Andrew Dickson <andrew.dickson@axelera.ai>


// tms_tb Testbench top level.
// TB for the TMS. All the tests are included via the file tms_tests.svh
// The uvm package and macros are included to support printing.

module tms_tb;
  import uvm_pkg::*;
  `include "uvm_macros.svh"

  `define DUT tms_tb.i_tms_dut
  `define PVT `DUT.u_pvt_wrapper.u_tu_pvt0501a01_ln05lpe_4007002
  `define CTM `DUT.gen_tms_ctm


  // Set to 1.2 GHz
  localparam realtime TbCycleTime  = 0.8333ns;
  localparam realtime JTAG_CLK_PER = 50.0ns;
  localparam realtime PVT_CLK_PER  = 125.0ns;

  // Setup AT timing
  localparam realtime TbApplTime = 0.1 * TbCycleTime;
  localparam realtime TbTestTime = 0.9 * TbCycleTime;

  localparam int  unsigned NB_EXT_TEMP_SENSE = 11                                    ;
  localparam int  unsigned NB_INT_TEMP_SENSE = 1                                     ;
  localparam int  unsigned NB_TEMP_SENSE     = NB_EXT_TEMP_SENSE + NB_INT_TEMP_SENSE ;
  localparam int  unsigned PAW               = 16                                    ;
  localparam int  unsigned PDW               = 32                                    ;
  localparam int  unsigned PSTRBW            = 4                                     ;
  localparam int  unsigned PPROTW            = 3                                     ;
  localparam int  unsigned PVT_PROBEW        = 63                                    ;
  localparam int  unsigned PVT_VOLW          = 14                                    ;
  // Width of temp bus
  localparam int  unsigned TW                = 12                                    ;
  // ps EOC
  localparam int  unsigned PS_EOC_POS        = 25                                    ;
  localparam int  unsigned PS_DATA_MSB       = 24                                    ;
  localparam int  unsigned IRQW              =  3                                    ;

  localparam type          tms_tsense_t      = logic [NB_EXT_TEMP_SENSE-1:0]         ;
  localparam type          tms_temp_t        = logic [NB_TEMP_SENSE    -1:0]         ;
  localparam type          tms_paddr_t       = logic [PAW              -1:0]         ;
  localparam type          tms_pdata_t       = logic [PDW              -1:0]         ;
  localparam type          tms_pstrb_t       = logic [PSTRBW           -1:0]         ;
  localparam type          tms_pprot_t       = logic [PPROTW           -1:0]         ;
  localparam type          tms_pvt_temp_t    = logic [TW               -1:0]         ;
  localparam type          tms_irq_t         = logic [IRQW             -1:0]         ;

  // fail stop count to stop test with errors
  localparam int           FAIL_STOP_CNT     = 5                                     ;

  // temperature array type. 2-D -> one for each CTM + width to match temperature data
  // width.
  localparam type          tms_temp_reg_t    = logic [NB_TEMP_SENSE][TW-1:0]         ;

  localparam tms_paddr_t   LAST_REG_ADDR     = tms_csr_reg_pkg::TMS_CSR_THERMAL_WARNING_CTRL_OFFSET;

  typedef enum {READ, WRITE} tms_reg_dir_t;
  typedef enum {APB , JTAG} tms_regs_access_t;

  // Clock / Reset genereration and stop of simulation
  logic                        tb_clk                        ;
  logic                        tb_rst_n                      ;
  logic                        tb_pvt_clk                    ;
  logic                        tb_pvt_rst_n                  ;

  tms_tsense_t                 i_remote_tsensor           ;

  // APB bus
  tms_paddr_t                  i_cfg_apb4_s_paddr            ;
  tms_pdata_t                  i_cfg_apb4_s_pwdata           ;
  logic                        i_cfg_apb4_s_pwrite           ;
  logic                        i_cfg_apb4_s_psel             ;
  logic                        i_cfg_apb4_s_penable          ;
  tms_pstrb_t                  i_cfg_apb4_s_pstrb            ;
  tms_pprot_t                  i_cfg_apb4_s_pprot            ;
  logic                        o_cfg_apb4_s_pready           ;
  tms_pdata_t                  o_cfg_apb4_s_prdata           ;
  logic                        o_cfg_apb4_s_pslverr          ;

  // JTAG interface
  logic                        i_jtag_tck                    ;
  logic                        i_jtag_rst_n                  ;
  logic                        i_jtag_tms                    ;
  logic                        i_jtag_tdi                    ;
  logic                        o_jtag_tdo                    ;
  logic                        o_tdo_en                      ;

  // thermal control signals
  // thermal throttle override
  logic                        i_thermal_throttle            ;
  tms_temp_t                   o_thermal_throttle            ;
  logic                        o_thermal_throttle_warning    ;
  tms_temp_t                   o_thermal_warning             ;
  logic                        o_thermal_shutdown            ;
  tms_irq_t                    o_irq                         ;

  // remode probe connections
  // don't uses types. needs to be wire
  wire  [PVT_PROBEW-1:0]       io_pvt_ibias_ts               ;
  wire  [PVT_PROBEW-1:0]       io_pvt_vsense_ts              ;
  wire                         io_pvt_test_out_ts            ;
  wire  [PVT_VOLW  -1:0]       io_pvt_vol_ts                 ;

  // PVT supplies
  wire                         io_pvt_dvdd075a_ts            ;
  wire                         io_pvt_dvss0a_ts              ;
  wire                         io_pvt_avdd18a_ts             ;
  wire                         io_pvt_avss0a_ts              ;
  wire                         io_pvt_avss_gd                ;

  tms_temp_reg_t               predicted_ctm_min_temp        ;
  tms_temp_reg_t               predicted_ctm_max_temp        ;
  tms_temp_reg_t               predicted_ctm_cur_temp        ;
  tms_temp_t                   predicted_ctm_thermal_shutdown;
  tms_temp_t                   predicted_ctm_thermal_warning ;
  tms_temp_t                   predicted_ctm_thermal_throttle;


  int                          fail_cnt                      ;
  tms_pdata_t                  prdata                        ;
  bit                          cnt;

  class regs_ctrl;
    rand tms_paddr_t       addr ;
    rand tms_pdata_t       wdata;
    rand tms_reg_dir_t     dir  ;
    rand tms_regs_access_t regs_access;

    constraint c_limits {
      addr[1:0] == 0;
      addr <= LAST_REG_ADDR + 'h10;
    }
  endclass

  regs_ctrl                     regs_txn                   ;

  tms_pdata_t                   regs_wdata[100];
  tms_pdata_t                   regs_min[6];
  tms_pdata_t                   regs_max[6];
  tms_pdata_t                   regs_cur[6];

  event ev_debug0;
  event ev_debug1;

  //============================================================================
  `include "tb_tasks.svh"
  `include "tms_tests.svh"

  //============================================================================
  localparam int unsigned ResetCycles = 5;

  initial begin : proc_clk_rst_gen
    tb_clk       = 1'b0;
    tb_rst_n     = 1'b0;
    tb_pvt_clk   = 1'b0;
    tb_pvt_rst_n = 1'b0;

    fork
      begin : fork_clk_gen
        forever begin
          #(TbCycleTime/2);
          tb_clk = ~tb_clk;
        end
      end
      begin : fork_rst_gen
        repeat (ResetCycles) @(negedge tb_clk);
        tb_rst_n     = 1'b1;
        tb_pvt_rst_n = 1'b1;
      end
    join
  end

  initial begin
    @(posedge tb_rst_n)
    forever begin
      @(posedge tb_clk)
      cnt++;
    end
  end

  //============================================================================
  // Stimuli generation
  initial begin
    int         i;
    int         ptr;
    tms_pdata_t chkdata;

    // reset
    init_inputs();
    drive_pvt_clk();
    fork
      drive_tck();
    join_none
    jtag_tdr_init();


    @(posedge tb_rst_n);
    repeat(2) @ (posedge tb_clk);
    `uvm_info("RESET", $sformatf("Reset Complete"), UVM_NONE)
    reset_jtag(50ns);
    // reset complete

    // start the CTM model task
    for (int i=0; i<NB_TEMP_SENSE; i++) begin
      ctm_model(i);
    end

    regs_txn = new();

    //==========================================================================
    // start tests
    // Check register reset values -> APB + JTAG
    register_reset_test();
    register_access_test();

    // tms_register_parll_access_test();

    // Check CTM operation
    ctm_auto_test();
    ctm_test();

    // Run this test separately.
    // ps_test();

    // test complete
    repeat(10) @ (posedge tb_clk);
    test_report(fail_cnt);
    $finish();
  end

  always @ (fail_cnt) begin
    if (fail_cnt >= FAIL_STOP_CNT) begin
      #10ns;
      `uvm_info("***TOO MANY FAILS***", $sformatf("***STOPPING TEST. Failure limit reached.***"), UVM_NONE)
      $stop();
    end
  end

  //============================================================================
  // Design Under Test (DUT)
  tms #(
    .NB_EXT_TEMP_SENSE ( NB_EXT_TEMP_SENSE ),
    .NB_INT_TEMP_SENSE ( NB_INT_TEMP_SENSE ),
    .PAW               ( PAW               ),
    .PDW               ( PDW               ),
    .PSTRBW            ( PSTRBW            ),
    .PPROTW            ( PPROTW            ),
    .PVT_PROBEW        ( PVT_PROBEW        ),
    .PVT_VOLW          ( PVT_VOLW          )
  ) i_tms_dut (
    .i_clk                      ( tb_clk                     ),
    .i_rst_n                    ( tb_rst_n                   ),
    .i_ao_rst_n                 ( tb_rst_n                   ),
    .i_pvt_clk                  ( tb_pvt_clk                 ),
    .i_pvt_rst_n                ( tb_pvt_rst_n               ),
    .i_cfg_apb4_s_paddr         ( i_cfg_apb4_s_paddr         ),
    .i_cfg_apb4_s_pwdata        ( i_cfg_apb4_s_pwdata        ),
    .i_cfg_apb4_s_pwrite        ( i_cfg_apb4_s_pwrite        ),
    .i_cfg_apb4_s_psel          ( i_cfg_apb4_s_psel          ),
    .i_cfg_apb4_s_penable       ( i_cfg_apb4_s_penable       ),
    .i_cfg_apb4_s_pstrb         ( i_cfg_apb4_s_pstrb         ),
    .i_cfg_apb4_s_pprot         ( i_cfg_apb4_s_pprot         ),
    .o_cfg_apb4_s_pready        ( o_cfg_apb4_s_pready        ),
    .o_cfg_apb4_s_prdata        ( o_cfg_apb4_s_prdata        ),
    .o_cfg_apb4_s_pslverr       ( o_cfg_apb4_s_pslverr       ),
    .i_jtag_tck                 ( i_jtag_tck                 ),
    .i_jtag_rst_n               ( i_jtag_rst_n               ),
    .i_thermal_throttle         ( i_thermal_throttle         ),
    .o_thermal_throttle         ( o_thermal_throttle         ),
    .o_thermal_throttle_warning ( o_thermal_throttle_warning ),
    .o_thermal_warning          ( o_thermal_warning          ),
    .o_thermal_shutdown         ( o_thermal_shutdown         ),
    .o_irq                      ( o_irq                      ),
    .io_pvt_ibias_ts            ( io_pvt_ibias_ts            ),
    .io_pvt_vsense_ts           ( io_pvt_vsense_ts           ),
    .io_pvt_test_out_ts         ( io_pvt_test_out_ts         ),
    .io_pvt_vol_ts              ( io_pvt_vol_ts              )
`ifdef POWER_PINS
                                                              ,
    .io_pvt_dvdd075a_ts         (  io_pvt_dvdd075a_ts        ),
    .io_pvt_dvss0a_ts           (  io_pvt_dvss0a_ts          ),
    .io_pvt_avdd18a_ts          (  io_pvt_avdd18a_ts         ),
    .io_pvt_avss0a_ts           (  io_pvt_avss0a_ts          ),
    .io_pvt_avss_gd             (  io_pvt_avss_gd            )
`endif
);

//==============================================================================
// remote probes
pvt_probe_wrapper #(
) u_pvt_probe_wrapper (
`ifdef POWER_PINS
  .io_avss_ts    ( ),
  .io_avss_gd    ( ),
`endif
  .io_ibias_ts   ( ),
  .io_vsense_ts  ( )
);

//==============================================================================
// Thermal status monitor and checkers
// Thermal shutdown - single bit OR of each channel status
always @ (o_thermal_shutdown) begin
  #10ns;
  check_thermal_shutdown(o_thermal_shutdown, predicted_ctm_thermal_shutdown);
end

// thermal warning - one per CTM channel
always @ (o_thermal_warning) begin
  #10ns;
  check_thermal_warning(o_thermal_warning, predicted_ctm_thermal_warning);
end

// thermal throttle - one per CTM.
always @ (o_thermal_throttle) begin
  #10ns;
  check_thermal_throttle(o_thermal_throttle, i_thermal_throttle, predicted_ctm_thermal_throttle);
end

// thermal throttle/wanrning mux
// mux contolled from reg: reg2hw.thermal_warning_ctrl
// 1-bit mux between 0: thermal warning and 1:thermal throttle
always @ (o_thermal_throttle_warning) begin
  #10ns;
  check_thermal_throttle_warning(o_thermal_throttle_warning, i_thermal_throttle, `DUT.reg2hw.thermal_warning_ctrl, predicted_ctm_thermal_warning, predicted_ctm_thermal_throttle);
end

//==============================================================================
// Debug enum for registers names
string reg_name;
always_comb begin
  reg_name = get_reg_name(i_tms_dut.u_tms_csr_reg_top.apb_i.paddr);
end

//==============================================================================
task automatic ctm_model(input int channel);
  int              pvt_sel             ;
  tms_pvt_temp_t   pvt_data            ;
  tms_pvt_temp_t   offset_comp_reg     ;
  bit [(TW*2)-1:0] offset_res          ;
  tms_pvt_temp_t   offset_rnd          ;
  // result registers
  tms_pvt_temp_t   min_temp            ;
  tms_pvt_temp_t   max_temp            ;
  tms_pvt_temp_t   cur_temp            ;
  tms_pvt_temp_t   thrm_shtdwn_thresh  ;
  tms_pvt_temp_t   thrm_warn_thresh    ;
  tms_pvt_temp_t   thrtl_on_temp       ;
  tms_pvt_temp_t   thrtl_off_temp      ;
  bit              ctm_thermal_shutdown;
  bit              ctm_thermal_warning ;
  bit              ctm_thermal_throttle;

  bit              ctm_thermal_shutdown_en;
  bit              ctm_thermal_warning_en;
  bit              ctm_thermal_throttle_en;

  // set initial value for min_temp
  min_temp                       = 'h800;
  max_temp                       =  0;
  predicted_ctm_min_temp         = '0;
  predicted_ctm_max_temp         = '0;
  predicted_ctm_cur_temp         = '0;
  predicted_ctm_thermal_shutdown = '0;
  predicted_ctm_thermal_warning  = '0;
  predicted_ctm_thermal_throttle = '0;
  ctm_thermal_shutdown_en        = 1'b0;
  ctm_thermal_warning_en         = 1'b0;
  ctm_thermal_throttle_en        = 1'b0;

  fork
    begin : fork_ctm_model
      forever begin
        @(posedge `PVT.EOC_TS);
        if (channel ==2) begin
          `uvm_info("DEBUG", $sformatf("DEBUG200 %0d,%x,%x", channel, i_thermal_throttle, `DUT.reg2hw.thermal_warning_ctrl), UVM_HIGH)
        end
        // get the active channel
        pvt_sel = `PVT.BJT_SEL_TS;

        ctm_thermal_shutdown_en = `DUT.reg2hw.ctm_thermal_ctrl[channel].shtdwn_ena;
        ctm_thermal_warning_en  = `DUT.reg2hw.ctm_thermal_ctrl[channel].warn_ena;
        ctm_thermal_throttle_en = `DUT.reg2hw.ctm_thermal_ctrl[channel].thrtl_ena;

        // This channel is active -> execute the CTM model calculations
        if ((channel+1) == pvt_sel) begin
          // get result
          pvt_data = `PVT.OUT_12BIT_TS;

          // get offset compensation value
          //offset_comp_reg = `CTM[channel].u_tms_ctm.i_csr_offset_comp;
          offset_comp_reg = `DUT.reg2hw.ctm_offset_comp[channel];

          offset_res = pvt_data * offset_comp_reg;
          offset_rnd = offset_res[(TW*2)-1:TW];
          `uvm_info("CTM_MODEL", $sformatf("DEBUG200 %0d,%0x,%0x,%0x,%0x", channel, pvt_data, offset_comp_reg, offset_res,offset_rnd), UVM_HIGH)

          // min/max/cur temp checkers
          if (offset_rnd < min_temp) begin
            min_temp = offset_rnd;
          end
          if (offset_rnd > max_temp) begin
            max_temp = offset_rnd;
          end
          cur_temp = offset_rnd;

          // delay
          repeat(10) @ (posedge tb_clk);

          // checkers
          check_temp(channel, "MIN", `DUT.ctm_min_temp[channel], min_temp);
          check_temp(channel, "MAX", `DUT.ctm_max_temp[channel], max_temp);
          check_temp(channel, "CUR", `DUT.ctm_cur_temp[channel], cur_temp);
          predicted_ctm_min_temp[channel] = min_temp;
          predicted_ctm_max_temp[channel] = max_temp;
          predicted_ctm_cur_temp[channel] = cur_temp;

          // thermal status
          thrm_shtdwn_thresh = `DUT.reg2hw.ctm_thrm_shtdwn_thresh[channel];
          thrm_warn_thresh   = `DUT.reg2hw.ctm_thrm_warn_thresh  [channel];
          thrtl_on_temp      = `DUT.reg2hw.ctm_thrtl_on_temp     [channel];
          thrtl_off_temp     = `DUT.reg2hw.ctm_thrtl_off_temp    [channel];

          if (ctm_thermal_shutdown_en && (offset_rnd > thrm_shtdwn_thresh)) begin
            ctm_thermal_shutdown = 1;
          end else begin
            ctm_thermal_shutdown = 0;
          end
          if (ctm_thermal_warning_en && (offset_rnd > thrm_warn_thresh)) begin
            ctm_thermal_warning  = 1;
          end else begin
            ctm_thermal_warning  = 0;
          end
          if (ctm_thermal_throttle_en && (offset_rnd > thrtl_on_temp)) begin
            ctm_thermal_throttle = 1;
          end else if (offset_rnd < thrtl_off_temp) begin
            ctm_thermal_throttle = 0;
          end

          // check threshold pins
          check_temp_threshold(channel, "SHTDWN", `DUT.ctm_thermal_shutdown[channel], ctm_thermal_shutdown);
          check_temp_threshold(channel, "WARN"  , `DUT.ctm_thermal_warning [channel], ctm_thermal_warning );
          check_temp_threshold(channel, "THRTL" , `DUT.ctm_thermal_throttle[channel], i_thermal_throttle ? 1'h1 : ctm_thermal_throttle, i_thermal_throttle);
          predicted_ctm_thermal_shutdown[channel] = ctm_thermal_shutdown;
          predicted_ctm_thermal_warning [channel] = ctm_thermal_warning ;
          predicted_ctm_thermal_throttle[channel] = ctm_thermal_throttle;

          if (channel == 2) begin
            `uvm_info("THROTTLE", $sformatf("DEBUG100 %0d,%x,%x,%x", channel, i_thermal_throttle, ctm_thermal_throttle, predicted_ctm_thermal_throttle[channel]), UVM_HIGH)
          end

        end
      end
    end
  join_none
endtask

endmodule
