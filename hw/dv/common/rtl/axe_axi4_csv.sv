// ===========================================================================================================//
// *** (C) Copyright Axelera AI 2021                                                                      *** //
// *** All Rights Reserved                                                                                *** //
// *** Axelera AI Confidential                                                                            *** //
// *** Owner : andrew.bond@axelera.ai                                                                     ***  //
// *** Description : This module logs an axi4 bus to csv file                                             *** //
// ===========================================================================================================//

module axe_axi4_csv #(
    parameter string       NAME                   = "",
    parameter int unsigned AXI_DATA_WIDTH         = 51,
    parameter int unsigned AXI_ADDR_WIDTH         = 40,
    parameter int unsigned AXI_ID_WIDTH           = 6
)
(
    // ===========================================================================================================
    // Clk & Rst declarations
    // ===========================================================================================================
    input bit aclk,
    input bit arstn,
    // ===========================================================================================================
    // AW Channel signal declarations
    // ===========================================================================================================
    input bit [AXI_ADDR_WIDTH-1  : 0]   awaddr,
    input bit [AXI_ID_WIDTH-1    : 0]   awid,
    input axi_pkg::axi_burst_t          awburst,
    input axi_pkg::axi_size_t           awsize,
    input axi_pkg::axi_cache_t          awcache,
    input axi_pkg::axi_len_t            awlen,
    input axi_pkg::axi_prot_t           awprot,
    input bit                           awlock,
    input bit                           awready,
    input bit                           awvalid,
    input bit[3:0]                      awqos,
    // ===========================================================================================================
    // W Channel signal declarations
    // ===========================================================================================================
    input bit [AXI_DATA_WIDTH-1    : 0] wdata,
    input bit [(AXI_DATA_WIDTH/8)-1: 0] wstrb,
    input bit                           wlast,
    input bit                           wready,
    input bit                           wvalid,
    // ===========================================================================================================
    // B Channel signal declarations
    // ===========================================================================================================
    input bit [AXI_ID_WIDTH-1      : 0] bid,
    input axi_pkg::axi_resp_t           bresp,
    input bit                           bready,
    input bit                           bvalid,
    // ===========================================================================================================
    // AR Channel signal declarations
    // ===========================================================================================================
    input bit [AXI_ADDR_WIDTH-1    : 0] araddr,
    input bit [AXI_ID_WIDTH-1      : 0] arid,
    input axi_pkg::axi_burst_t          arburst,
    input axi_pkg::axi_size_t           arsize,
    input axi_pkg::axi_cache_t          arcache,
    input axi_pkg::axi_len_t            arlen,
    input axi_pkg::axi_prot_t           arprot,
    input bit                           arlock,
    input bit                           arready,
    input bit                           arvalid,
    input bit[3:0]                      arqos,
    // ===========================================================================================================
    // R Channel signal declarations
    // ===========================================================================================================
    input bit [AXI_ID_WIDTH-1      : 0] rid,
    input bit [AXI_DATA_WIDTH-1    : 0] rdata,
    input axi_pkg::axi_resp_t           rresp,
    input bit                           rlast,
    input bit                           rready,
    input bit                           rvalid
);

    // Time unit and precision
    timeunit      1ps;
    timeprecision 1ps;

    chandle h;

    initial begin
        h = axe_csv_pkg::open_csv($psprintf("axi4_%s.csv", NAME),
        "time,port,phase,awid,awaddr,awburst,awsize,awcache,awlen,awprot,awlock,awqos,awid,wdata,wstrb,wlast,bid,bresp,arid,araddr,arburst,arsize,arcache,arlen,arprot,arlock,arqos,rid,rdata,rresp,rlast");

    end

    initial begin
        forever begin
            @(posedge aclk iff arstn);

            if (awvalid && awready) begin
                axe_csv_pkg::write_csv(h,
                                        '{
                                            $psprintf("%0d,%s,%s", $time, NAME,"AW"),
                                            $psprintf("0x%x,0x%x,%0d,%0d,%d,%0d,%0d,%0d,%0d", awid, awaddr, awburst, awsize, awcache, awlen, awprot, awlock, awqos),
                                            ",,",
                                            ",",
                                            ",,,,,,,,",
                                            ",,,"
                                        });
            end
        end
    end

    initial begin
        forever begin
            @(posedge aclk iff arstn);

            if (wvalid && wready) begin
                axe_csv_pkg::write_csv(h,
                                        '{
                                            $psprintf("%0d,%s,%s", $time, NAME,"W"),
                                            ",,,,,,,,",
                                            $psprintf("0x%x,0x%x,%0d",  wdata, wstrb, wlast),
                                            ",",
                                            ",,,,,,,,",
                                            ",,,"
                                        });
            end
        end
    end

    initial begin
        forever begin
            @(posedge aclk iff arstn);

            if (bvalid && bready) begin
                axe_csv_pkg::write_csv(h,
                                        '{
                                            $psprintf("%0d,%s,%s", $time, NAME,"B"),
                                            ",,,,,,,,",
                                            ",,",
                                            $psprintf("0x%x,%0d", bid, bresp),
                                            ",,,,,,,,",
                                            ",,,"
                                        });
            end
        end
    end

    initial begin
        forever begin
            @(posedge aclk iff arstn);

            if (arvalid && arready) begin
                axe_csv_pkg::write_csv(h,
                                        '{
                                            $psprintf("%0d,%s,%s", $time, NAME,"AR"),
                                            ",,,,,,,,",
                                            ",,",
                                            ",",
                                            $psprintf("0x%x,0x%x,%0d,%0d,%d,%0d,%0d,%0d,%0d", arid, araddr, arburst, arsize, arcache, arlen, arprot, arlock, arqos),
                                            ",,,"
                                        });
            end
        end
    end

    initial begin
        forever begin
            @(posedge aclk iff arstn);

            if (rvalid && rready) begin
                axe_csv_pkg::write_csv(h,
                                        '{
                                            $psprintf("%0d,%s,%s", $time, NAME,"R"),
                                            ",,,,,,,,",
                                            ",,",
                                            ",",
                                            ",,,,,,,,",
                                            $psprintf("0x%x,0x%x,%0d,%0d,", rid, rdata, rresp, rlast)
                                        });
            end
        end
    end

    final begin
        axe_csv_pkg::close_csv(null);
    end

endmodule : axe_axi4_csv
