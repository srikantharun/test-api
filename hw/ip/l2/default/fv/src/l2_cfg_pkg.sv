// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: L2 Formal Verification configuration package
// Owner: Manuel Oliveira <manuel.oliveira@axelera.ai>

`ifndef L2_CFG_PKG_SV
`define L2_CFG_PKG_SV

package l2_cfg_pkg;

  // =======================================================================
  // L2 Formal Verification configuration
  // =======================================================================
  // Complexity reduction: the following parameters were downscaled to accelerate convergency
  // L2_AXI_DATA_WIDTH: 512 -> 32
  // L2_AXI_ADDR_WIDTH: 24 -> 7
  // L2_MEM_SIZE: 16 MiB -> 128 B
  // L2_SRAM_DATA_WIDTH: 128 -> 8
  // L2_SRAM_DATA_DEPTH: 4096 -> 2

  // L2 AXI configuraton
  // ---------------------
  parameter int unsigned L2_AXI_DATA_WIDTH = 16;
  parameter int unsigned L2_AXI_ID_WIDTH = 4;
  parameter int unsigned L2_AXI_ADDR_WIDTH = 7;

  // L2 memory size
  //----------------------
  parameter int unsigned L2_MEM_SIZE = cc_utils_pkg::mem_capacity(128, cc_utils_pkg::B);

  // L2 Bank configuration
  //----------------------
  parameter int unsigned L2_NUM_BANKS = 16;
  // Caution: Dependent parameter, do not modify.
  parameter int unsigned L2_BANK_DATA_WIDTH = L2_AXI_DATA_WIDTH;

  // L2 Tech RAM instance
  //----------------------
  parameter int unsigned L2_SRAM_DATA_WIDTH = 8;
  parameter int unsigned L2_SRAM_DATA_DEPTH = 2;
  // Caution: Dependent parameter, do not modify.
  parameter int unsigned L2_NUM_SRAMS = L2_BANK_DATA_WIDTH / L2_SRAM_DATA_WIDTH;
  parameter int unsigned L2_SRAM_SIZE = L2_SRAM_DATA_DEPTH * L2_SRAM_DATA_WIDTH;
  parameter int unsigned L2_SRAM_SIZE_BYTES = L2_SRAM_SIZE / 8
                                            + (L2_SRAM_SIZE % 8 != 0);

  // L2 bank instance
  //-------------------
  // Caution: Dependent parameter, do not modify.
  parameter int unsigned L2_BANK_SIZE_BYTES = L2_MEM_SIZE / L2_NUM_BANKS;

  // L2 RAM instances
  //-------------------
  // Caution: Dependent parameter, do not modify.
  parameter int unsigned L2_NUM_RAMS = L2_BANK_SIZE_BYTES / (L2_NUM_SRAMS * L2_SRAM_SIZE_BYTES);

  // ---------------------------------------------------------------
  // Pipelining Settings
  // ---------------------------------------------------------------
  parameter int unsigned L2_REQ_LATENCY = 5;
  parameter int unsigned L2_RSP_LATENCY = 5;
  parameter int unsigned L2_RSP_GROUPS = 6;

  parameter int unsigned L2_REQ_WIRE_LATENCY[L2_NUM_BANKS] = {
    32'd3, //  0 Bank
    32'd3, //  1 Bank
    32'd3, //  2 Bank
    32'd3, //  3 Bank
    32'd3, //  4 Bank
    32'd3, //  5 Bank
    32'd2, //  6 Bank
    32'd2, //  7 Bank
    32'd2, //  8 Bank
    32'd2, //  9 Bank
    32'd2, // 10 Bank
    32'd2, // 11 Bank
    32'd1, // 12 Bank
    32'd1, // 13 Bank
    32'd1, // 14 Bank
    32'd1  // 15 Bank
  };

  parameter int unsigned L2_RSP_STAGE_LATENCY[L2_RSP_GROUPS] = {
    32'd1, //  Group 0
    32'd1, //  Group 1
    32'd2, //  Group 2
    32'd2, //  Group 3
    32'd3, //  Group 4
    32'd3  //  Group 5
  };

  parameter int unsigned L2_RSP_GROUP[L2_NUM_BANKS] = {
    32'd5, //  0 Bank
    32'd5, //  1 Bank
    32'd5, //  2 Bank
    32'd4, //  3 Bank
    32'd4, //  4 Bank
    32'd4, //  5 Bank
    32'd3, //  6 Bank
    32'd3, //  7 Bank
    32'd3, //  8 Bank
    32'd2, //  9 Bank
    32'd2, // 10 Bank
    32'd2, // 11 Bank
    32'd1, // 12 Bank
    32'd1, // 13 Bank
    32'd1, // 14 Bank
    32'd0  // 15 Bank
  };

  // SRAM Configuration Chain Settings
  // ---------------------------------
  // Arbitrary chain order for sram config signals
  parameter int unsigned L2_ARB_CHAIN_ORDER [L2_NUM_BANKS][L2_NUM_RAMS][L2_NUM_SRAMS] = '{
    '{
        '{32'd4, 32'd1},    // (0,0,0) and (0,0,1)
        '{32'd2, 32'd7}     // (0,1,0) and (0,1,1)
    },
    '{
        '{32'd0, 32'd5},    // (1,0,0) and (1,0,1)
        '{32'd6, 32'd3}     // (1,1,0) and (1,1,1)
    },
    '{
        '{32'd12, 32'd9},    // (2,0,0) and (2,0,1)
        '{32'd10, 32'd15}   // (2,1,0) and (2,1,1)
    },
    '{
        '{32'd8, 32'd13},  // (3,0,0) and (3,0,1)
        '{32'd14, 32'd11}   // (3,1,0) and (3,1,1)
    },
    '{
        '{32'd20, 32'd17},  // (4,0,0) and (4,0,1)
        '{32'd18, 32'd23}   // (4,1,0) and (4,1,1)
    },
    '{
        '{32'd16, 32'd21},  // (5,0,0) and (5,0,1)
        '{32'd22, 32'd19}   // (5,1,0) and (5,1,1)
    },
    '{
        '{32'd28, 32'd25},  // (6,0,0) and (6,0,1)
        '{32'd26, 32'd31}   // (6,1,0) and (6,1,1)
    },
    '{
        '{32'd24, 32'd29},  // (7,0,0) and (7,0,1)
        '{32'd30, 32'd27}   // (7,1,0) and (7,1,1)
    },
    '{
        '{32'd36, 32'd33},  // (8,0,0) and (8,0,1)
        '{32'd34, 32'd39}   // (8,1,0) and (8,1,1)
    },
    '{
        '{32'd32, 32'd37},  // (9,0,0) and (9,0,1)
        '{32'd38, 32'd35}   // (9,1,0) and (9,1,1)
    },
    '{
        '{32'd44, 32'd41},  // (10,0,0) and (10,0,1)
        '{32'd42, 32'd47}   // (10,1,0) and (10,1,1)
    },
    '{
        '{32'd40, 32'd45},  // (11,0,0) and (11,0,1)
        '{32'd46, 32'd43}   // (11,1,0) and (11,1,1)
    },
    '{
        '{32'd52, 32'd49},  // (12,0,0) and (12,0,1)
        '{32'd50, 32'd55}   // (12,1,0) and (12,1,1)
    },
    '{
        '{32'd48, 32'd53},  // (13,0,0) and (13,0,1)
        '{32'd54, 32'd51}   // (13,1,0) and (13,1,1)
    },
    '{
        '{32'd60, 32'd57},  // (14,0,0) and (14,0,1)
        '{32'd58, 32'd63}   // (14,1,0) and (14,1,1)
    },
    '{
        '{32'd56, 32'd61},  // (15,0,0) and (15,0,1)
        '{32'd62, 32'd59}   // (15,1,0) and (15,1,1)
    }
};

endpackage
`endif  //L2_CFG_PKG_SV
