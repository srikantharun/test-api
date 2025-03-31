// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owners: Tasos Psarras <anastasios.psarras@axelera.ai>
//         Roel Uytterhoeven <roel.uytterhoeven@axelera.ai>
//
// Description: #1265

module noc_common_addr_msb_setter (
    input  chip_pkg::chip_axi_addr_t i_axi_araddr_40b,
    output logic [40:0]              o_axi_araddr_41b
);
    logic msb_read_bit;
    logic rd_target_is_l2;
    logic rd_target_is_pcie;
    // FD targets: L2 & PCIe
    assign rd_target_is_l2 = (i_axi_araddr_40b >= aipu_addr_map_pkg::L2_ST_ADDR && i_axi_araddr_40b <= aipu_addr_map_pkg::L2_END_ADDR) ? 1'b1 : 1'b0;
    assign rd_target_is_pcie = (i_axi_araddr_40b >= aipu_addr_map_pkg::HOST_ST_ADDR && i_axi_araddr_40b <= aipu_addr_map_pkg::HOST_END_ADDR) ? 1'b1 : 1'b0;
    assign msb_read_bit = rd_target_is_l2 | rd_target_is_pcie;
    // Always pass on the 40b 'normal'address and prefix with the msb read bit
    assign o_axi_araddr_41b = {msb_read_bit, i_axi_araddr_40b};
endmodule

