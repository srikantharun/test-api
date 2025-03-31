// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Address decoder that can be used for fabrics with external decoder
// Owner: Sander Geursen <sander.geursen@axelera.ai>
//        Luyi <yi.lu@axelera.ai>

`ifndef _AIC_FABRIC_ADDR_DECODER_SV_
`define _AIC_FABRIC_ADDR_DECODER_SV_

module aic_fabric_addr_decoder #(
  parameter int AW = 36,

  parameter int CORE_ID_LSB = 28,
  parameter int NR_CORE_IDS = 8,
  parameter int CORE_IDS [NR_CORE_IDS] = '{default:-1},

  parameter int DEFAULT_SLAVE = 0,
  parameter int NOT_THIS_CORE_SLAVE = 0,

  parameter int NR_SLAVES = 3,
  parameter int NR_REGIONS = 3,

  parameter bit SKIP_CORE_CHECK_IF_NOT_CORE=1'b0,

  parameter bit REGION_IS_CORE[NR_REGIONS] = '{default:0},
  parameter longint REGION_ST_ADDR[NR_REGIONS] = {36'h0, 36'h1000, 36'h4000},
  parameter longint REGION_END_ADDR[NR_REGIONS] = {36'hfff, 36'h1fff, 36'h6fff},
  parameter int REGION_SLAVE_ID[NR_REGIONS] = {8'd1, 8'd2, 8'd3},
  localparam int unsigned SL_SEL_B = $clog2(NR_SLAVES+1)
) (
  input logic [AW-1:0] addr_in,
  input logic [AW-1:CORE_ID_LSB] core_id,

  output logic [SL_SEL_B-1:0] sl_select
);

  // get the number of registers required per field:
  function automatic bit has_cid_set();
    has_cid_set = 0;
    foreach (CORE_IDS[r]) begin
      if(CORE_IDS[r] != -1)
        has_cid_set = 1;
    end
  endfunction
  localparam bit HAS_CORE_ID = has_cid_set();

  // check if there is an overlap in regions (not supported)
  for (genvar r=0; r<NR_REGIONS; r++) begin: gen_region_r
    for (genvar c=0; c<NR_REGIONS; c++) begin: gen_region_c
      if(r!=c) begin: gen_region_not_match // not checking the same region
        if ((REGION_ST_ADDR[c] >= REGION_ST_ADDR[r]) && (REGION_ST_ADDR[c] <= REGION_END_ADDR[r]))
          $fatal(1, "Region %d start address overlapping with region %d!", c, r);
        if ((REGION_END_ADDR[c] >= REGION_ST_ADDR[r]) && (REGION_END_ADDR[c] <= REGION_END_ADDR[r]))
          $fatal(1, "Region %d end address overlapping with region %d!", c, r);
      end
    end
  end

  ///////////////////////////////////////////////
  // address core check:
  logic is_this_core;
  logic [AW-1:CORE_ID_LSB] addr_core_id;
  logic not_connected;

  if (HAS_CORE_ID) begin: gen_id
    if(CORE_ID_LSB>=AW)
      $fatal(1, "CORE_ID_LSB should be smaller then AW! LSB is %d, while AW is %d", CORE_ID_LSB, AW);
    assign addr_core_id = addr_in[AW-1:CORE_ID_LSB];
  end else begin: gen_id_not
    // spyglass disable_block W528
    assign not_connected = |core_id;
    // spyglass enable_block W528
  end

  always_comb begin : pr_core_check
    automatic bit var_is_this_core;
    var_is_this_core = 1'b0;
    for(int i = 0; i < NR_CORE_IDS; i++) begin
      // only check if core_ids[i] is not -1 (disabled)
      if(HAS_CORE_ID && (CORE_IDS[i] != -1)) begin
        // check if incoming address has a core id
        if (int'(addr_core_id) == CORE_IDS[i]) begin

          // only one range will be active at the time
          // check if this address core id corresponds to the one on the port:
          if (addr_core_id == core_id)
            var_is_this_core = 1'b1;
        end
      end
    end
    is_this_core = var_is_this_core;
  end
  ///////////////////////////////////////////////

  ///////////////////////////////////////////////
  // region check:
  logic [NR_REGIONS-1:0] region_hit;
  logic [NR_REGIONS-1:0][SL_SEL_B-1:0] region_sl_sel;
  logic region_hit_orr;
  logic [SL_SEL_B-1:0] region_sel_orr;

  for (genvar r=0; r<NR_REGIONS; r++) begin : gen_region_check_
    aic_fabric_addr_decoder_region_check #(
      .AW(AW),
      .CORE_ID_LSB(CORE_ID_LSB),
      .NR_SLAVES(NR_SLAVES),

      .REGION_IS_CORE(REGION_IS_CORE[r]),
      .SKIP_CORE_CHECK_IF_NOT_CORE(SKIP_CORE_CHECK_IF_NOT_CORE),
      .REGION_ST_ADDR(REGION_ST_ADDR[r]),
      .REGION_END_ADDR(REGION_END_ADDR[r]),
      .REGION_SLAVE_ID(REGION_SLAVE_ID[r])
    ) i_region_chk (
      .addr_in(addr_in),
      .is_this_core(is_this_core),
      .hit(region_hit[r]),
      .sl_sel(region_sl_sel[r])
    );
  end

  always_comb begin : pr_region_orr
    logic [SL_SEL_B-1:0] region_sel_orr_var;

    for(int r = 0; r < NR_REGIONS; r++) begin
      // intendent to be assigned multiple times
      // spyglass disable_block W415a
      if(r == 0)
        region_sel_orr_var = region_sl_sel[r];
      else
        region_sel_orr_var = region_sel_orr_var | region_sl_sel[r];
      // spyglass enable_block W415a
    end
    region_sel_orr = region_sel_orr_var;
  end
  assign region_hit_orr = |region_hit;
  ///////////////////////////////////////////////

  ///////////////////////////////////////////////
  // slave select:
  always_comb begin : pr_sl_sel
    if(region_hit_orr)
      sl_select = region_sel_orr;
    else if (!is_this_core)
      sl_select = unsigned'(NOT_THIS_CORE_SLAVE);
    else
      sl_select = unsigned'(DEFAULT_SLAVE);
  end
  ///////////////////////////////////////////////

endmodule

`endif //_AIC_FABRIC_ADDR_DECODER_SV_
