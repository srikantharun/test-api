// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: IMC MBIST pattern generator
// MBIST implements MARCH-C algorithm for IMC bank
//
// Owner: Tiago Campos <tiago.campos@axelera.ai>

`ifndef IMC_BIST_AIC_GEN_MBIST_SV
`define IMC_BIST_AIC_GEN_MBIST_SV

module imc_bist_gen_mbist
  import imc_bist_pkg::expect_type_e;
  import imc_bist_pkg::E_GOLDEN_ZEROES;
  import imc_bist_pkg::E_GOLDEN_ONES;
  import imc_bist_pkg::E_GOLDEN_55;
  import imc_bist_pkg::E_GOLDEN_AA;
  import imc_bist_pkg::E_NEIGHBOR;
  import imc_bank_pkg::IMC_NB_ROWS;
  import imc_bank_pkg::IMC_NB_COLS_PER_BANK;
  import mvm_pkg::DATA_W;
  import imc_bank_pkg::IMC_ROW_PW;
  import imc_bank_pkg::IMC_WEIGHT_SET_PW;
  import imc_bank_pkg::IMC_BLOCK_ENABLE_W;
  import imc_bank_pkg::IMC_NB_DELAY_CYCLES;
(
  input wire i_clk,
  input wire i_rst_n,

  // <-> CTL
  input  logic start_pi,
  input  logic resume_pi,
  input  logic stop_pi,
  output logic busy_o,

  // <-> IMUX
  output logic write_enable_o,
  output logic [IMC_NB_COLS_PER_BANK-1:0][DATA_W-1:0] write_values_o,
  output logic [IMC_ROW_PW-1:0] write_row_o,
  output logic [IMC_WEIGHT_SET_PW-1:0] write_wss_o,

  // <-> IMUXC
  output logic compute_enable_o,
  output logic [IMC_BLOCK_ENABLE_W-1:0] compute_block_enable_o,
  output logic compute_gate_clock_o,
  output logic compute_signed_weights_o,
  output logic [IMC_NB_ROWS-1:0] compute_inp_o,
  output logic [IMC_WEIGHT_SET_PW-1:0] compute_wss_o,

  // <-> COMP
  output logic expect_strobe_o,
  output expect_type_e expect_type_o
);

  // MBIST:
  // Implements MARCH C-
  // Each state has a addr counter 0,...,8191
  // This accounts for:
  // - 512 rows
  // - * 4 weight sets
  // - * 2 iteration mode offset
  // It counts in either direction, i.e., 8191->0 and 0->8191
  //
  // The iteration mode can be row-first or set-first
  // Row-first encoding: addr = {wss, row, offset}
  // Set-first encoding: addr = {offset, row, wss}
  //
  // On row-first, we can't parallel read-write, so we must toggle between both each addr cycle
  // The offset encodes whether it's a read (0 for ASC, 1 for DESC) or a write (1 for ASC, 0 for DESC) cycle
  // R0_W1_ASC will look like this:
  // addr=0000: read row000set0, nowrite
  // addr=0001: noread         , write row000set0
  // addr=0002: read row001set0, nowrite
  // addr=0003: noread         , write row001set0
  // addr=0004: read row002set0, nowrite
  // ...
  // addr=1022: read row511set0, nowrite
  // addr=1023: noread         , write row511set0
  // addr=1024: read row000set1, nowrite
  // addr=1025: noread         , write row000set1
  // ...
  // addr=4094: read row511set3, nowrite
  // addr=4095: noread         , write row511set3
  // ...
  //
  // On set-first, we can parallel read-write, so we only need to respect offset on the leading and trailing cycles
  //   so we can process the pattern in 4097 cycles (1 leading read + 4095 parallel read+write + 1 trailing write)
  // The write happens on the previous addr
  // At addr=4096 (ASC) or addr=4095 (DESC), read pattern has ended and the trailing write is inserted
  // The offset encodes whether it's the last cycle (1 for ASC, 0 for DESC)
  // R0_W1_ASC will look like this:
  // addr=0000: read row000set0, nowrite
  // addr=0001: read row000set1, write row000set0
  // addr=0002: read row000set2, write row000set1
  // addr=0003: read row000set3, write row000set2
  // addr=0004: read row001set0, write row000set3
  // ...
  // addr=1023: read row255set3, write row255set2
  // addr=1025: read row129set0, write row128set3
  // ...
  // addr=2047: read row511set3, write row511set2
  // addr=2048: noread         , write row511set3
  // ...
  //
  // R0_W1_DESC will look like this:
  // ...
  // addr=8191: noread         , nowrite
  // addr=8190: noread         , nowrite
  // ...
  // addr=8191: read row575set3, nowrite
  // addr=8190: read row575set2, write row575set3
  // ...
  // addr=4097: read row000set1, write row000set2
  // addr=4096: read row000set0, write row000set1
  // addr=4095: noread         , write row000set0

  /// -----------------------
  /// ----- TYPES -----------
  /// -----------------------
  localparam int unsigned LVirtualAddrW = 1 + IMC_ROW_PW + IMC_WEIGHT_SET_PW;

  localparam int unsigned NStates = 7;
  typedef enum logic [NStates-1:0] {
    E_IDLE = 'd0,
    E_MARCH_C_0_W0_ANY = 'd1,
    E_MARCH_C_1_R0_W1_ASC = 'd2,
    E_MARCH_C_2_R1_W0_ASC = 'd4,
    E_MARCH_C_3_R0_W1_DESC = 'd8,
    E_MARCH_C_4_R1_W0_DESC = 'd16,
    E_MARCH_C_5_R0_ANY = 'd32
  } state_e;

  typedef struct packed {
    logic idle_from_invalid_state;
    logic march_c_0_from_any_march_c;
    logic march_c_0_from_idle;
    logic march_c_1_from_march_c_0;
    logic march_c_2_from_march_c_1;
    logic march_c_3_from_march_c_2;
    logic march_c_4_from_march_c_3;
    logic march_c_5_from_march_c_4;
    logic march_c_0_from_march_c_5;
    logic idle_from_march_c_5;
  } fsm_hint_t;

  localparam int unsigned NModes = 4;
  typedef enum logic [$clog2(NModes)-1:0] {
    E_ROW_FIRST = 2'b00,
    E_ROW_FIRST_ALT_WEIGHTS = 2'b01,
    E_SET_FIRST_CHECKERBOARD_0 = 2'b10,
    E_SET_FIRST_CHECKERBOARD_1 = 2'b11
  } iteration_mode_e;

  typedef enum logic {
    E_ASCENDING  = 1'b0,
    E_DESCENDING = 1'b1
  } direction_e;

  typedef enum logic [2:0] {
    E_DONT_READ   = 3'b000,
    E_READ_ZEROES = 3'b001,
    E_READ_ONES   = 3'b010,
    E_READ_55     = 3'b011,
    E_READ_AA     = 3'b100
  } read_strategy_e;

  typedef enum logic [2:0] {
    E_DONT_WRITE   = 3'b000,
    E_WRITE_ZEROES = 3'b001,
    E_WRITE_ONES   = 3'b010,
    E_WRITE_55     = 3'b011,
    E_WRITE_AA     = 3'b100
  } write_strategy_e;

  typedef struct packed {
    direction_e direction;
    read_strategy_e [3:0] reads;
    write_strategy_e [3:0] writes;
  } state_strategy_t;

  typedef struct packed {
    logic [IMC_WEIGHT_SET_PW-1:0] wss;
    logic [IMC_ROW_PW-1:0] row;
    logic offset;
  } virtual_addr_rowfirst_t;

  typedef struct packed {
    logic offset;
    logic [IMC_ROW_PW-1:0] row;
    logic [IMC_WEIGHT_SET_PW-1:0] wss;
  } virtual_addr_setfirst_t;

  typedef union packed {
    virtual_addr_rowfirst_t rowfirst;
    virtual_addr_setfirst_t setfirst;
    logic [LVirtualAddrW-1:0] raw;
  } virtual_addr_t;

  typedef struct packed {
    logic en;
    write_strategy_e values;
    logic [IMC_ROW_PW-1:0] row;
    logic [IMC_WEIGHT_SET_PW-1:0] wss;
  } write_op_t;

  typedef struct packed {
    logic en;
    expect_type_e expect_type;
    logic [IMC_ROW_PW-1:0] row;
    logic [IMC_WEIGHT_SET_PW-1:0] wss;
  } compute_op_t;

  typedef struct packed {
    write_op_t   write;
    compute_op_t compute;
  } imc_op_t;

  function automatic expect_type_e f_getExpectFromReadStrategy(input read_strategy_e i_rs);
    expect_type_e l_et;

    unique case (i_rs)
      default: l_et = E_GOLDEN_ZEROES;
      E_READ_ONES: l_et = E_GOLDEN_ONES;
      E_READ_55: l_et = E_GOLDEN_55;
      E_READ_AA: l_et = E_GOLDEN_AA;
    endcase

    f_getExpectFromReadStrategy = l_et;
  endfunction

  function automatic logic f_isLastCycle(
      input virtual_addr_t i_addr, input state_strategy_t i_strat, input iteration_mode_e i_mode);
    if (i_mode inside {E_ROW_FIRST, E_ROW_FIRST_ALT_WEIGHTS} && i_strat.direction == E_ASCENDING)
      f_isLastCycle = (i_addr.raw == 'd8191);
    else if (i_mode inside {E_ROW_FIRST, E_ROW_FIRST_ALT_WEIGHTS}
                            && i_strat.direction == E_DESCENDING)
      f_isLastCycle = (i_addr.raw == 0);
    else if (i_mode == E_SET_FIRST_CHECKERBOARD_0 || i_mode == E_SET_FIRST_CHECKERBOARD_1) begin
      // Offset indicates last cycle in set first mode
      f_isLastCycle = (i_addr.setfirst.offset == (i_strat.direction == E_ASCENDING));
    end else f_isLastCycle = 1'b1;  // Invalid state flushes FSM
  endfunction

  function automatic virtual_addr_t f_nextAddr(input virtual_addr_t i_addr,
                                               input state_strategy_t i_strat);
    virtual_addr_t l_addr;
    if (i_strat.direction == E_ASCENDING) l_addr.raw = i_addr.raw + 1'b1;
    else l_addr.raw = i_addr.raw - 1'b1;
    f_nextAddr = l_addr;
  endfunction

  // verilog_format: off // tiago: verible output is a disaster for these functions
  function automatic imc_op_t f_decodeOp_rowFirst_ascending(
    input virtual_addr_t i_addr,
    input state_strategy_t i_strat,
    input iteration_mode_e i_mode
  );
    imc_op_t l_imc_op;
    l_imc_op = '{
      compute: '{
        // rowfirst ascending - read if offset is 0
        en: (read_strategy_e'(i_strat.reads) != E_DONT_READ) & (~i_addr.rowfirst.offset),
        expect_type: f_getExpectFromReadStrategy(i_strat.reads[i_addr.rowfirst.wss]),
        row: i_addr.rowfirst.row,
        // If not computing, invert all wss bits
        // This is to avoid imc bank write/compute on same wss
        wss: {IMC_WEIGHT_SET_PW{i_addr.rowfirst.offset}}^i_addr.rowfirst.wss
      },
      write: '{
        // write if offset is 1
        en: (write_strategy_e'(i_strat.writes) != E_DONT_WRITE) & i_addr.rowfirst.offset,
        values: i_strat.writes[i_addr.rowfirst.wss],
        row: i_addr.rowfirst.row,
        wss: i_addr.rowfirst.wss
      }
    };
    f_decodeOp_rowFirst_ascending = l_imc_op;
  endfunction

  function automatic imc_op_t f_decodeOp_rowFirst_descending(
    input virtual_addr_t i_addr,
    input state_strategy_t i_strat,
    input iteration_mode_e i_mode
  );
    imc_op_t l_imc_op;
    l_imc_op = '{
      compute: '{
        // rowfirst descending - read if offset is 1
        en: (read_strategy_e'(i_strat.reads) != E_DONT_READ) & (i_addr.rowfirst.offset),
        expect_type: f_getExpectFromReadStrategy(i_strat.reads[i_addr.rowfirst.wss]),
        row: i_addr.rowfirst.row,
        // If not computing, invert all wss bits
        // This is to avoid imc bank write/compute on same wss
        wss: {IMC_WEIGHT_SET_PW{~i_addr.rowfirst.offset}}^i_addr.rowfirst.wss
      },
      write: '{
        // write if offset is 0
        en: (write_strategy_e'(i_strat.writes) != E_DONT_WRITE) & (~i_addr.rowfirst.offset),
        values: i_strat.writes[i_addr.rowfirst.wss],
        row: i_addr.rowfirst.row,
        wss: i_addr.rowfirst.wss
      }
    };
    f_decodeOp_rowFirst_descending = l_imc_op;
  endfunction

  function automatic imc_op_t f_decodeOp_setFirst_ascending(
    input virtual_addr_t i_addr,
    input state_strategy_t i_strat,
    input iteration_mode_e i_mode,
    input virtual_addr_t i_last_addr
  );
    imc_op_t l_imc_op;
    l_imc_op = '{
      compute: '{
        // setfirst ascending - read if it's not the last cycle
        // last cycle is signalled by offset==1
        en: (read_strategy_e'(i_strat.reads) != E_DONT_READ) & (~i_addr.setfirst.offset),
        expect_type: f_getExpectFromReadStrategy(i_strat.reads[i_addr.setfirst.wss]),
        row: i_addr.setfirst.row,
        // If not computing, invert all wss bits
        // This is to avoid imc bank write/compute on same wss
        wss: i_addr.setfirst.offset ? ~i_last_addr.setfirst.wss : i_addr.setfirst.wss
      },
      write: '{
        // write if it's not first cycle
        en: (write_strategy_e'(i_strat.writes) != E_DONT_WRITE) & (i_addr.raw != '0),
        values: i_strat.writes[i_last_addr.setfirst.wss],
        row: i_last_addr.setfirst.row,
        wss: i_last_addr.setfirst.wss
      }
    };
    f_decodeOp_setFirst_ascending = l_imc_op;
  endfunction

  function automatic imc_op_t f_decodeOp_setFirst_descending(
    input virtual_addr_t i_addr,
    input state_strategy_t i_strat,
    input iteration_mode_e i_mode,
    input virtual_addr_t i_last_addr
  );
    imc_op_t l_imc_op;
    l_imc_op = '{
      compute: '{
        // setfirst ascending - read if it's not the last cycle
        // last cycle is signalled by offset==0
        en: (read_strategy_e'(i_strat.reads) != E_DONT_READ) & (i_addr.setfirst.offset),
        expect_type: f_getExpectFromReadStrategy(i_strat.reads[i_addr.setfirst.wss]),
        row: i_addr.setfirst.row,
        // If not computing, invert all wss bits
        // This is to avoid imc bank write/compute on same wss
        wss: i_addr.setfirst.offset ? i_addr.setfirst.wss : ~i_last_addr.setfirst.wss
      },
      write: '{
        // write if it's not first cycle
        en: (write_strategy_e'(i_strat.writes) != E_DONT_WRITE) & (i_addr.raw != 'd8191),
        values: i_strat.writes[i_last_addr.setfirst.wss],
        row: i_last_addr.setfirst.row,
        wss: i_last_addr.setfirst.wss
      }
    };
    f_decodeOp_setFirst_descending = l_imc_op;
  endfunction
  // verilog_format: on

  function automatic imc_op_t f_decodeOp(
      input virtual_addr_t i_addr, input state_strategy_t i_strat, input iteration_mode_e i_mode,
      input virtual_addr_t i_last_addr);
    imc_op_t l_imc_op;
    if (i_mode inside {E_ROW_FIRST, E_ROW_FIRST_ALT_WEIGHTS}
                      && i_strat.direction == E_ASCENDING) begin
      l_imc_op = f_decodeOp_rowFirst_ascending(i_addr, i_strat, i_mode);
    end else if (i_mode inside {E_ROW_FIRST, E_ROW_FIRST_ALT_WEIGHTS}
                                && i_strat.direction == E_DESCENDING) begin
      l_imc_op = f_decodeOp_rowFirst_descending(i_addr, i_strat, i_mode);
    end else if (i_mode inside {E_SET_FIRST_CHECKERBOARD_0, E_SET_FIRST_CHECKERBOARD_1}
                                && i_strat.direction == E_ASCENDING) begin
      l_imc_op = f_decodeOp_setFirst_ascending(i_addr, i_strat, i_mode, i_last_addr);
    end else if (i_mode inside {E_SET_FIRST_CHECKERBOARD_0, E_SET_FIRST_CHECKERBOARD_1}
                                && i_strat.direction == E_DESCENDING) begin
      l_imc_op = f_decodeOp_setFirst_descending(i_addr, i_strat, i_mode, i_last_addr);
    end else l_imc_op = '0;
    f_decodeOp = l_imc_op;
  endfunction

  /// --------------------------------------
  /// ----- E_IDLE -------------------------
  /// --------------------------------------
  localparam logic [LVirtualAddrW-1:0] InitialAddrIdle = '0;
  localparam state_strategy_t StateStrategyIdle = '{
      direction: E_ASCENDING,
      reads: {E_DONT_READ, E_DONT_READ, E_DONT_READ, E_DONT_READ},
      writes: {E_DONT_WRITE, E_DONT_WRITE, E_DONT_WRITE, E_DONT_WRITE}
  };

  /// --------------------------------------
  /// ----- E_MARCH_C_0_W0_ANY -------------
  /// --------------------------------------
  localparam logic [LVirtualAddrW-1:0] InitialAddrMc0 = '0;
  localparam state_strategy_t StateStrategyMc0 = '{
      direction: E_ASCENDING,
      reads: {E_DONT_READ, E_DONT_READ, E_DONT_READ, E_DONT_READ},
      writes: {E_WRITE_ZEROES, E_WRITE_ZEROES, E_WRITE_ZEROES, E_WRITE_ZEROES}
  };
  localparam state_strategy_t StateStrategyMc0AltWeights = '{
      direction: E_ASCENDING,
      reads: {E_DONT_READ, E_DONT_READ, E_DONT_READ, E_DONT_READ},
      writes: {E_WRITE_55, E_WRITE_55, E_WRITE_55, E_WRITE_55}
  };
  localparam state_strategy_t StateStrategyMc0Checkerboard0 = '{
      direction: E_ASCENDING,
      reads: {E_DONT_READ, E_DONT_READ, E_DONT_READ, E_DONT_READ},
      writes: {E_WRITE_ZEROES, E_WRITE_ONES, E_WRITE_ZEROES, E_WRITE_ONES}
  };
  localparam state_strategy_t StateStrategyMc0Checkerboard1 = '{
      direction: E_ASCENDING,
      reads: {E_DONT_READ, E_DONT_READ, E_DONT_READ, E_DONT_READ},
      writes: {E_WRITE_ONES, E_WRITE_ZEROES, E_WRITE_ONES, E_WRITE_ZEROES}
  };

  /// --------------------------------------
  /// ----- E_MARCH_C_1_R0_W1_ASC ----------
  /// --------------------------------------
  localparam logic [LVirtualAddrW-1:0] InitialAddrMc1 = '0;
  localparam state_strategy_t StateStrategyMc1 = '{
      direction: E_ASCENDING,
      reads: {E_READ_ZEROES, E_READ_ZEROES, E_READ_ZEROES, E_READ_ZEROES},
      writes: {E_WRITE_ONES, E_WRITE_ONES, E_WRITE_ONES, E_WRITE_ONES}
  };
  localparam state_strategy_t StateStrategyMc1AltWeights = '{
      direction: E_ASCENDING,
      reads: {E_READ_55, E_READ_55, E_READ_55, E_READ_55},
      writes: {E_WRITE_AA, E_WRITE_AA, E_WRITE_AA, E_WRITE_AA}
  };
  localparam state_strategy_t StateStrategyMc1Checkerboard0 = '{
      direction: E_ASCENDING,
      reads: {E_READ_ZEROES, E_READ_ONES, E_READ_ZEROES, E_READ_ONES},
      writes: {E_WRITE_ONES, E_WRITE_ZEROES, E_WRITE_ONES, E_WRITE_ZEROES}
  };
  localparam state_strategy_t StateStrategyMc1Checkerboard1 = '{
      direction: E_ASCENDING,
      reads: {E_READ_ONES, E_READ_ZEROES, E_READ_ONES, E_READ_ZEROES},
      writes: {E_WRITE_ZEROES, E_WRITE_ONES, E_WRITE_ZEROES, E_WRITE_ONES}
  };

  /// --------------------------------------
  /// ----- E_MARCH_C_2_R1_W0_ASC ----------
  /// --------------------------------------
  localparam logic [LVirtualAddrW-1:0] InitialAddrMc2 = '0;
  localparam state_strategy_t StateStrategyMc2 = '{
      direction: E_ASCENDING,
      reads: {E_READ_ONES, E_READ_ONES, E_READ_ONES, E_READ_ONES},
      writes: {E_WRITE_ZEROES, E_WRITE_ZEROES, E_WRITE_ZEROES, E_WRITE_ZEROES}
  };
  localparam state_strategy_t StateStrategyMc2AltWeights = '{
      direction: E_ASCENDING,
      reads: {E_READ_AA, E_READ_AA, E_READ_AA, E_READ_AA},
      writes: {E_WRITE_55, E_WRITE_55, E_WRITE_55, E_WRITE_55}
  };
  localparam state_strategy_t StateStrategyMc2Checkerboard0 = '{
      direction: E_ASCENDING,
      reads: {E_READ_ONES, E_READ_ZEROES, E_READ_ONES, E_READ_ZEROES},
      writes: {E_WRITE_ZEROES, E_WRITE_ONES, E_WRITE_ZEROES, E_WRITE_ONES}
  };
  localparam state_strategy_t StateStrategyMc2Checkerboard1 = '{
      direction: E_ASCENDING,
      reads: {E_READ_ZEROES, E_READ_ONES, E_READ_ZEROES, E_READ_ONES},
      writes: {E_WRITE_ONES, E_WRITE_ZEROES, E_WRITE_ONES, E_WRITE_ZEROES}
  };

  /// --------------------------------------
  /// ----- E_MARCH_C_3_R0_W1_DESC ---------
  /// --------------------------------------
  localparam logic [LVirtualAddrW-1:0] InitialAddrMc3 = 'd8191;
  localparam state_strategy_t StateStrategyMc3 = '{
      direction: E_DESCENDING,
      reads: {E_READ_ZEROES, E_READ_ZEROES, E_READ_ZEROES, E_READ_ZEROES},
      writes: {E_WRITE_ONES, E_WRITE_ONES, E_WRITE_ONES, E_WRITE_ONES}
  };
  localparam state_strategy_t StateStrategyMc3AltWeights = '{
      direction: E_DESCENDING,
      reads: {E_READ_55, E_READ_55, E_READ_55, E_READ_55},
      writes: {E_WRITE_AA, E_WRITE_AA, E_WRITE_AA, E_WRITE_AA}
  };
  localparam state_strategy_t StateStrategyMc3Checkerboard0 = '{
      direction: E_DESCENDING,
      reads: {E_READ_ZEROES, E_READ_ONES, E_READ_ZEROES, E_READ_ONES},
      writes: {E_WRITE_ONES, E_WRITE_ZEROES, E_WRITE_ONES, E_WRITE_ZEROES}
  };
  localparam state_strategy_t StateStrategyMc3Checkerboard1 = '{
      direction: E_DESCENDING,
      reads: {E_READ_ONES, E_READ_ZEROES, E_READ_ONES, E_READ_ZEROES},
      writes: {E_WRITE_ZEROES, E_WRITE_ONES, E_WRITE_ZEROES, E_WRITE_ONES}
  };

  /// --------------------------------------
  /// ----- E_MARCH_C_4_R1_W0_DESC ---------
  /// --------------------------------------
  localparam logic [LVirtualAddrW-1:0] InitialAddrMc4 = 'd8191;
  localparam state_strategy_t StateStrategyMc4 = '{
      direction: E_DESCENDING,
      reads: {E_READ_ONES, E_READ_ONES, E_READ_ONES, E_READ_ONES},
      writes: {E_WRITE_ZEROES, E_WRITE_ZEROES, E_WRITE_ZEROES, E_WRITE_ZEROES}
  };
  localparam state_strategy_t StateStrategyMc4AltWeights = '{
      direction: E_DESCENDING,
      reads: {E_READ_AA, E_READ_AA, E_READ_AA, E_READ_AA},
      writes: {E_WRITE_55, E_WRITE_55, E_WRITE_55, E_WRITE_55}
  };
  localparam state_strategy_t StateStrategyMc4Checkerboard0 = '{
      direction: E_DESCENDING,
      reads: {E_READ_ONES, E_READ_ZEROES, E_READ_ONES, E_READ_ZEROES},
      writes: {E_WRITE_ZEROES, E_WRITE_ONES, E_WRITE_ZEROES, E_WRITE_ONES}
  };
  localparam state_strategy_t StateStrategyMc4Checkerboard1 = '{
      direction: E_DESCENDING,
      reads: {E_READ_ZEROES, E_READ_ONES, E_READ_ZEROES, E_READ_ONES},
      writes: {E_WRITE_ONES, E_WRITE_ZEROES, E_WRITE_ONES, E_WRITE_ZEROES}
  };

  /// --------------------------------------
  /// ----- E_MARCH_C_5_R0_ANY -------------
  /// --------------------------------------
  localparam logic [LVirtualAddrW-1:0] InitialAddrMc5 = 'd8191;
  localparam state_strategy_t StateStrategyMc5 = '{
      direction: E_DESCENDING,
      reads: {E_READ_ZEROES, E_READ_ZEROES, E_READ_ZEROES, E_READ_ZEROES},
      writes: {E_DONT_WRITE, E_DONT_WRITE, E_DONT_WRITE, E_DONT_WRITE}
  };
  localparam state_strategy_t StateStrategyMc5AltWeights = '{
      direction: E_DESCENDING,
      reads: {E_READ_55, E_READ_55, E_READ_55, E_READ_55},
      writes: {E_DONT_WRITE, E_DONT_WRITE, E_DONT_WRITE, E_DONT_WRITE}
  };
  localparam state_strategy_t StateStrategyMc5Checkerboard0 = '{
      direction: E_DESCENDING,
      reads: {E_READ_ZEROES, E_READ_ONES, E_READ_ZEROES, E_READ_ONES},
      writes: {E_DONT_WRITE, E_DONT_WRITE, E_DONT_WRITE, E_DONT_WRITE}
  };
  localparam state_strategy_t StateStrategyMc5Checkerboard1 = '{
      direction: E_DESCENDING,
      reads: {E_READ_ONES, E_READ_ZEROES, E_READ_ONES, E_READ_ZEROES},
      writes: {E_DONT_WRITE, E_DONT_WRITE, E_DONT_WRITE, E_DONT_WRITE}
  };

  // verilog_lint: waive-start line-length
  // verilog_format: off // tiago: want to preserve comment formatting
  localparam state_strategy_t [NStates-1:0] [NModes-1:0] StateStategyMatrix = {
    /*                        */ /* E_ROW_FIRST     */ /* E_ROW_FIRST_ALT_WEIGHTS   */ /* E_SET_FIRST_CHECKERBOARD_0   */ /* E_SET_FIRST_CHECKERBOARD_1    */
    /* E_IDLE                 */ {StateStrategyIdle, StateStrategyIdle           , StateStrategyIdle              , StateStrategyIdle              },
    /* E_MARCH_C_0_W0_ANY     */ {StateStrategyMc0 , StateStrategyMc0AltWeights, StateStrategyMc0Checkerboard0, StateStrategyMc0Checkerboard1},
    /* E_MARCH_C_1_R0_W1_ASC  */ {StateStrategyMc1 , StateStrategyMc1AltWeights, StateStrategyMc1Checkerboard0, StateStrategyMc1Checkerboard1},
    /* E_MARCH_C_2_R1_W0_ASC  */ {StateStrategyMc2 , StateStrategyMc2AltWeights, StateStrategyMc2Checkerboard0, StateStrategyMc2Checkerboard1},
    /* E_MARCH_C_3_R0_W1_DESC */ {StateStrategyMc3 , StateStrategyMc3AltWeights, StateStrategyMc3Checkerboard0, StateStrategyMc3Checkerboard1},
    /* E_MARCH_C_4_R1_W0_DESC */ {StateStrategyMc4 , StateStrategyMc4AltWeights, StateStrategyMc4Checkerboard0, StateStrategyMc4Checkerboard1},
    /* E_MARCH_C_5_R0_ANY     */ {StateStrategyMc5 , StateStrategyMc5AltWeights, StateStrategyMc5Checkerboard0, StateStrategyMc5Checkerboard1}
  };
  // verilog_format: on
  // verilog_lint: waive-stop line-length

  function automatic state_strategy_t f_advanceStateStrategy(input iteration_mode_e i_mode,
                                                             input state_e i_target_state);
    state_strategy_t l_ss;
    logic [$clog2(NStates)-1:0] l_lookup_index_state;
    logic [$clog2(NModes)-1:0] l_lookup_index_mode;

    l_ss = StateStrategyIdle;
    unique case (i_target_state)
      default: l_lookup_index_state = NStates - 1;
      E_MARCH_C_0_W0_ANY: l_lookup_index_state = NStates - 2;
      E_MARCH_C_1_R0_W1_ASC: l_lookup_index_state = NStates - 3;
      E_MARCH_C_2_R1_W0_ASC: l_lookup_index_state = NStates - 4;
      E_MARCH_C_3_R0_W1_DESC: l_lookup_index_state = NStates - 5;
      E_MARCH_C_4_R1_W0_DESC: l_lookup_index_state = NStates - 6;
      E_MARCH_C_5_R0_ANY: l_lookup_index_state = NStates - 7;
    endcase
    unique case (i_mode)
      default: l_lookup_index_mode = NModes - 1;
      E_ROW_FIRST_ALT_WEIGHTS: l_lookup_index_mode = NModes - 2;
      E_SET_FIRST_CHECKERBOARD_0: l_lookup_index_mode = NModes - 3;
      E_SET_FIRST_CHECKERBOARD_1: l_lookup_index_mode = NModes - 4;
    endcase
    l_ss = StateStategyMatrix[l_lookup_index_state][l_lookup_index_mode];
    f_advanceStateStrategy = l_ss;
  endfunction

  /// -----------------------
  /// ----- FLOPS/WIRES -----
  /// -----------------------
  logic resume_p_unc;

  // Global strategy
  iteration_mode_e r_cur_mode, s_cur_mode;
  logic clr_cur_mode, tgl_cur_mode;

  // FSM
  state_e rr_state, r_state, s_state;
  fsm_hint_t s_fsm_hint;
  logic rr_stopped, r_stopped, s_stopped, s_en;

  // Next addr
  virtual_addr_t s_cur_addr, r_cur_addr, s_cur_addr_transition, rr_cur_addr;

  // Current strategy
  state_strategy_t s_cur_strat, r_cur_strat, s_cur_strat_transition;

  imc_op_t s_imc_op, r_imc_op;

  logic [$clog2(IMC_NB_DELAY_CYCLES+1)-1:0] s_cnt_clock_gating, r_cnt_clock_gating;

  /// -----------------------
  /// ----- DESIGN ----------
  /// -----------------------
  always_ff @(posedge i_clk, negedge i_rst_n)
    if (!i_rst_n) r_cur_mode <= E_ROW_FIRST;
    else if (clr_cur_mode) r_cur_mode <= E_ROW_FIRST;
    else r_cur_mode <= s_cur_mode;

  always_comb
    case (r_cur_mode)
      default: s_cur_mode = tgl_cur_mode ? E_ROW_FIRST_ALT_WEIGHTS : E_ROW_FIRST;
      E_ROW_FIRST_ALT_WEIGHTS:
      s_cur_mode = tgl_cur_mode ? E_SET_FIRST_CHECKERBOARD_0 : E_ROW_FIRST_ALT_WEIGHTS;
      E_SET_FIRST_CHECKERBOARD_0:
      s_cur_mode = tgl_cur_mode ? E_SET_FIRST_CHECKERBOARD_1 : E_SET_FIRST_CHECKERBOARD_0;
      E_SET_FIRST_CHECKERBOARD_1:
      s_cur_mode = tgl_cur_mode ? E_ROW_FIRST : E_SET_FIRST_CHECKERBOARD_1;
    endcase

  // Ensure mode is row-first whenever launching
  assign clr_cur_mode = s_fsm_hint.march_c_0_from_idle | s_fsm_hint.march_c_0_from_any_march_c;
  // Switch from row-first to set-first when first iteration of march-c finishes
  assign tgl_cur_mode = s_fsm_hint.march_c_0_from_march_c_5;

  /// -----------------------
  /// ----- FSM ----------
  /// -----------------------
  // Calculate transitions
  assign s_fsm_hint.idle_from_invalid_state = ~(r_state inside {
    E_IDLE,
    E_MARCH_C_0_W0_ANY,
    E_MARCH_C_1_R0_W1_ASC,
    E_MARCH_C_2_R1_W0_ASC,
    E_MARCH_C_3_R0_W1_DESC,
    E_MARCH_C_4_R1_W0_DESC,
    E_MARCH_C_5_R0_ANY
  });
  // If we receive a start pulse we restart independently of internal state
  assign s_fsm_hint.march_c_0_from_any_march_c = ~s_fsm_hint.idle_from_invalid_state
                                               & (r_state != E_IDLE) & start_pi;
  assign s_fsm_hint.march_c_0_from_idle = (r_state == E_IDLE) & start_pi;
  assign s_fsm_hint.march_c_1_from_march_c_0 = (r_state == E_MARCH_C_0_W0_ANY) & f_isLastCycle(
      r_cur_addr, r_cur_strat, r_cur_mode
  );
  assign s_fsm_hint.march_c_2_from_march_c_1 = (r_state == E_MARCH_C_1_R0_W1_ASC) & f_isLastCycle(
      r_cur_addr, r_cur_strat, r_cur_mode
  );
  assign s_fsm_hint.march_c_3_from_march_c_2 = (r_state == E_MARCH_C_2_R1_W0_ASC) & f_isLastCycle(
      r_cur_addr, r_cur_strat, r_cur_mode
  );
  assign s_fsm_hint.march_c_4_from_march_c_3 = (r_state == E_MARCH_C_3_R0_W1_DESC) & f_isLastCycle(
      r_cur_addr, r_cur_strat, r_cur_mode
  );
  assign s_fsm_hint.march_c_5_from_march_c_4 = (r_state == E_MARCH_C_4_R1_W0_DESC) & f_isLastCycle(
      r_cur_addr, r_cur_strat, r_cur_mode
  );
  assign s_fsm_hint.march_c_0_from_march_c_5 = (r_state == E_MARCH_C_5_R0_ANY) & f_isLastCycle(
      r_cur_addr, r_cur_strat, r_cur_mode
  ) & (r_cur_mode != E_SET_FIRST_CHECKERBOARD_1);
  assign s_fsm_hint.idle_from_march_c_5 = (r_state == E_MARCH_C_5_R0_ANY) & f_isLastCycle(
      r_cur_addr, r_cur_strat, r_cur_mode
  ) & (r_cur_mode == E_SET_FIRST_CHECKERBOARD_1);

  // Apply transitions
  // Load initial virtual address and strategy on the transition
  always_comb begin : s_transitions_cproc
    s_state = r_state;
    s_cur_addr_transition = r_cur_addr;
    s_cur_strat_transition = r_cur_strat;
    if (s_fsm_hint.idle_from_invalid_state | s_fsm_hint.idle_from_march_c_5) begin
      s_state = E_IDLE;
      s_cur_addr_transition.raw = InitialAddrIdle;
      s_cur_strat_transition = StateStrategyIdle;
    end else if (s_fsm_hint.march_c_0_from_any_march_c |
                 s_fsm_hint.march_c_0_from_idle | s_fsm_hint.march_c_0_from_march_c_5) begin
      s_state = E_MARCH_C_0_W0_ANY;
      s_cur_addr_transition.raw = InitialAddrMc0;
      s_cur_strat_transition = s_fsm_hint.march_c_0_from_march_c_5 ? f_advanceStateStrategy(
          clr_cur_mode ? E_ROW_FIRST : s_cur_mode, E_MARCH_C_0_W0_ANY) : StateStrategyMc0;
    end else if (s_fsm_hint.march_c_1_from_march_c_0) begin
      s_state = E_MARCH_C_1_R0_W1_ASC;
      s_cur_addr_transition.raw = InitialAddrMc1;
      s_cur_strat_transition =
          f_advanceStateStrategy(clr_cur_mode ? E_ROW_FIRST : r_cur_mode, E_MARCH_C_1_R0_W1_ASC);
    end else if (s_fsm_hint.march_c_2_from_march_c_1) begin
      s_state = E_MARCH_C_2_R1_W0_ASC;
      s_cur_addr_transition.raw = InitialAddrMc2;
      s_cur_strat_transition =
          f_advanceStateStrategy(clr_cur_mode ? E_ROW_FIRST : r_cur_mode, E_MARCH_C_2_R1_W0_ASC);
    end else if (s_fsm_hint.march_c_3_from_march_c_2) begin
      s_state = E_MARCH_C_3_R0_W1_DESC;
      s_cur_addr_transition.raw = InitialAddrMc3;
      s_cur_strat_transition =
          f_advanceStateStrategy(clr_cur_mode ? E_ROW_FIRST : r_cur_mode, E_MARCH_C_3_R0_W1_DESC);
    end else if (s_fsm_hint.march_c_4_from_march_c_3) begin
      s_state = E_MARCH_C_4_R1_W0_DESC;
      s_cur_addr_transition.raw = InitialAddrMc4;
      s_cur_strat_transition =
          f_advanceStateStrategy(clr_cur_mode ? E_ROW_FIRST : r_cur_mode, E_MARCH_C_4_R1_W0_DESC);
    end else if (s_fsm_hint.march_c_5_from_march_c_4) begin
      s_state = E_MARCH_C_5_R0_ANY;
      s_cur_addr_transition.raw = InitialAddrMc5;
      s_cur_strat_transition =
          f_advanceStateStrategy(clr_cur_mode ? E_ROW_FIRST : r_cur_mode, E_MARCH_C_5_R0_ANY);
    end
  end : s_transitions_cproc

  // Store state
  always_ff @(posedge i_clk, negedge i_rst_n)
    if (!i_rst_n) r_state <= E_IDLE;
    else if (s_en) r_state <= s_state;

  // If stopped, unstop at start_pi (or resume_pi), otherwise stop if stop_pi
  assign s_stopped = r_stopped ? ~(start_pi | resume_pi) : (stop_pi | (r_state == E_IDLE));

  always_ff @(posedge i_clk, negedge i_rst_n)
    if (!i_rst_n) r_stopped <= 1'b1;
    else r_stopped <= s_stopped;

  // Evaluate s_stopped and r_stopped for loose leading/trailing enable
  assign s_en = ~(s_stopped & r_stopped);

  /// --------------------------------------
  /// ----- NEXT ADDR/STRAT ---------------
  /// --------------------------------------
  always_comb begin : s_cur_addr_cproc
    // If FSM transitions always load from reference data
    if (|s_fsm_hint) s_cur_addr = s_cur_addr_transition;
    else s_cur_addr = f_nextAddr(r_cur_addr, r_cur_strat);
  end : s_cur_addr_cproc

  always_ff @(posedge i_clk, negedge i_rst_n)
    if (!i_rst_n) r_cur_addr.raw <= '0;
    else if (s_en) r_cur_addr <= s_cur_addr;

  always_ff @(posedge i_clk, negedge i_rst_n)
    if (!i_rst_n) rr_cur_addr.raw <= '0;
    else if (s_en) rr_cur_addr <= r_cur_addr;

  // The strategy only changes on transition
  assign s_cur_strat = (|s_fsm_hint) ? s_cur_strat_transition : r_cur_strat;

  always_ff @(posedge i_clk, negedge i_rst_n)
    if (!i_rst_n) r_cur_strat <= StateStrategyIdle;
    else if (s_en) r_cur_strat <= s_cur_strat;

  /// --------------------------------------
  /// ----- DECODE OP ---------------
  /// --------------------------------------
  assign s_imc_op = f_decodeOp(r_cur_addr, r_cur_strat, r_cur_mode, rr_cur_addr);

  always_ff @(posedge i_clk, negedge i_rst_n)
    if (!i_rst_n) r_imc_op <= '0;
    else if (s_en) r_imc_op <= s_imc_op;

  always_ff @(posedge i_clk, negedge i_rst_n)
    if (!i_rst_n) rr_stopped <= '0;
    else rr_stopped <= r_stopped;

  always_ff @(posedge i_clk, negedge i_rst_n)
    if (!i_rst_n) rr_state <= E_IDLE;
    else if (s_en) rr_state <= r_state;

  // Compute clock gating, ungate the compute when we are computing and until bank is done computing
  // Last compute trailing counter
  always_comb begin : s_cnt_clock_gating_cproc
    if (r_imc_op.compute.en & (~r_stopped)) s_cnt_clock_gating = IMC_NB_DELAY_CYCLES;
    else if (|r_cnt_clock_gating) s_cnt_clock_gating = r_cnt_clock_gating - 1'b1;
    else s_cnt_clock_gating = '0;
  end

  always_ff @(posedge i_clk, negedge i_rst_n)
    if (!i_rst_n) r_cnt_clock_gating <= '0;
    else r_cnt_clock_gating <= s_cnt_clock_gating;

  // Helper to generate output compute data
  logic s_compute_op_valid;
  // Helper to generate output write data
  logic s_write_op_valid;
  logic [IMC_NB_COLS_PER_BANK-1:0][DATA_W-1:0] s_write_values_packed;

  logic [DATA_W-1:0] s_write_value_pattern;
  always_comb
    case (r_imc_op.write.values)
      default: s_write_value_pattern = 8'h00;
      E_WRITE_ONES: s_write_value_pattern = 8'hff;
      E_WRITE_55: s_write_value_pattern = 8'h55;
      E_WRITE_AA: s_write_value_pattern = 8'haa;
    endcase

  assign s_write_values_packed = {IMC_NB_COLS_PER_BANK{s_write_value_pattern}};

  assign s_write_op_valid = r_imc_op.write.row inside {[0:IMC_NB_ROWS-1]};
  assign s_compute_op_valid = r_imc_op.compute.row inside {[0:IMC_NB_ROWS-1]};

  /// --------------------------------------
  /// ----- DRIVE OUTPUTS ---------------
  /// --------------------------------------
  // <-> CTL
  assign busy_o = (r_state != E_IDLE) & (~r_stopped);

  // <-> IMUX
  assign write_enable_o = (~rr_stopped) & r_imc_op.write.en & s_write_op_valid;
  // streaming operator converts packed to unpacked
  assign{>>{write_values_o}} = s_write_values_packed;
  assign write_row_o = r_imc_op.write.row;
  assign write_wss_o = r_imc_op.write.wss;

  // <-> IMUXC
  // compute_enable even if only writing, to force the compute pipeline forward
  assign compute_enable_o = (~rr_stopped) & (rr_state != E_IDLE);
  assign compute_block_enable_o = {IMC_BLOCK_ENABLE_W{(~rr_stopped) & r_imc_op.compute.en}};
  assign compute_gate_clock_o = ~(r_imc_op.compute.en | (|r_cnt_clock_gating));
  assign compute_signed_weights_o = 1'b0;
  assign compute_inp_o = (IMC_NB_ROWS)'(r_imc_op.compute.en) << r_imc_op.compute.row;
  assign compute_wss_o = r_imc_op.compute.wss;

  // <-> COMP
  assign expect_strobe_o = r_imc_op.compute.en & (~rr_stopped) & s_compute_op_valid;
  assign expect_type_o = r_imc_op.compute.expect_type;
  //assign expect_type_o = E_NEIGHBOR;

  // Assertions
  //synopsys translate_off
`ifdef ASSERTIONS_ON
`endif  // ASSERTIONS_ON
  //synopsys translate_on

endmodule
`endif  // IMC_BIST_AIC_GEN_MBIST_SV
