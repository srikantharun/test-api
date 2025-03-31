// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Matt Morris <matt.morris@axelera.ai>


module pctl_ppmu
#( parameter int unsigned COUNT_W = 8)
(
  input  wire                 i_clk,
  input  wire                 i_rst_n,

  input  wire                 i_test_mode,

  input  logic [COUNT_W-1:0]  i_pre_rst_0_cycles,
  input  logic [COUNT_W-1:0]  i_pre_rst_1_cycles,
  input  logic [COUNT_W-1:0]  i_pre_rst_2_cycles,
  input  logic [COUNT_W-1:0]  i_pre_rel_cycles,

  input  logic                i_rst_remove,
  input  logic                i_rst_activate,

  output logic                o_rst_remove_clr,
  output logic                o_rst_activate_clr,
  output logic [3:0]          o_fsm_state,

  output logic                o_clken_n,
  output logic                o_partition_rst_n
);

  typedef logic [3:0] ppmu_fsm_state_t;
  //                                                       //  <fsm1> //  <fsm0> // RST_N   // CLKEN
  localparam ppmu_fsm_state_t PPMU_FSM_RESETHW    = 4'h8;  //     1   //     0   //   0     //   0
  localparam ppmu_fsm_state_t PPMU_FSM_PRE_RST_0  = 4'h2;  //     0   //     0   //   1     //   0
  localparam ppmu_fsm_state_t PPMU_FSM_PRE_RST_1  = 4'h0;  //     0   //     0   //   0     //   0
  localparam ppmu_fsm_state_t PPMU_FSM_PRE_RST_2  = 4'h1;  //     0   //     0   //   0     //   1
  localparam ppmu_fsm_state_t PPMU_FSM_RESET      = 4'h4;  //     0   //     1   //   0     //   0
  localparam ppmu_fsm_state_t PPMU_FSM_PRE_REL    = 4'h6;  //     0   //     1   //   1     //   0
  localparam ppmu_fsm_state_t PPMU_FSM_ACTIVE     = 4'h7;  //     0   //     1   //   1     //   1

  ppmu_fsm_state_t fsm_state_q, fsm_state_d;

  typedef logic [COUNT_W-1:0] ppmu_fsm_count_t;

  ppmu_fsm_count_t fsm_count_q, fsm_count_d;

  logic count_is_0;
  logic rst_n_dly_q;

  // Work around for Tessent issue reading enums prod/europa/#1259

  always_comb o_clken_n         = !fsm_state_q[0];

   axe_tcl_clk_mux2 u_rst_mux_bypass (
    .i_clk0(fsm_state_q[1]),
    .i_clk1(i_rst_n),
    .i_sel (i_test_mode),
    .o_clk (o_partition_rst_n)
  );

  always_comb o_rst_remove_clr   = !rst_n_dly_q && (fsm_state_q == PPMU_FSM_RESET);
  always_comb o_rst_activate_clr = (fsm_state_q == PPMU_FSM_ACTIVE);

  always_comb o_fsm_state = fsm_state_q;

  always_ff @ (posedge i_clk or negedge i_rst_n)
  if (!i_rst_n) begin
    fsm_state_q     <= PPMU_FSM_RESETHW;
    fsm_count_q     <= '0;
    rst_n_dly_q     <= 1'b0;
  end
  else begin
    fsm_state_q <= fsm_state_d;
    fsm_count_q <= fsm_count_d;
    rst_n_dly_q <= o_partition_rst_n;
  end

  always_comb count_is_0 = !(|fsm_count_q);

  always_comb begin
    fsm_state_d = fsm_state_q;
    fsm_count_d = fsm_count_q;
    unique case(fsm_state_q)

        PPMU_FSM_RESETHW : begin
            fsm_state_d = PPMU_FSM_PRE_RST_1;
            fsm_count_d = i_pre_rst_1_cycles;
        end

        PPMU_FSM_RESET : if (i_rst_remove) begin
            fsm_state_d = PPMU_FSM_PRE_REL;
            fsm_count_d = i_pre_rel_cycles;
        end

        PPMU_FSM_PRE_REL : if (count_is_0) begin
            fsm_state_d = PPMU_FSM_ACTIVE;
        end
        else fsm_count_d = fsm_count_q - ppmu_fsm_count_t'(1);

        PPMU_FSM_ACTIVE : if (i_rst_activate) begin
              fsm_state_d = PPMU_FSM_PRE_RST_0;
              fsm_count_d = i_pre_rst_0_cycles;
        end

        PPMU_FSM_PRE_RST_0 : if (count_is_0) begin
            fsm_state_d = PPMU_FSM_PRE_RST_1;
            fsm_count_d = i_pre_rst_1_cycles;
        end
        else fsm_count_d = fsm_count_q - ppmu_fsm_count_t'(1);

        PPMU_FSM_PRE_RST_1 : if (count_is_0) begin
            fsm_state_d = PPMU_FSM_PRE_RST_2;
            fsm_count_d = i_pre_rst_2_cycles;
        end
        else fsm_count_d = fsm_count_q - ppmu_fsm_count_t'(1);

        PPMU_FSM_PRE_RST_2 : if (count_is_0) begin
            fsm_state_d = PPMU_FSM_RESET;
        end
        else fsm_count_d = fsm_count_q - ppmu_fsm_count_t'(1);

        default : fsm_state_d = PPMU_FSM_PRE_RST_1;
    endcase
  end



endmodule
