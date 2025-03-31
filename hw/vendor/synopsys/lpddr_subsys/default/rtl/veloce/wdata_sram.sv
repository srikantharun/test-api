


module wdata_sram (
    input   logic           wdataram_clk,
    input   logic [255:0]   wdataram_din,
    input   logic [31:0]    wdataram_mask,
    input   logic           wdataram_wr,
    input   logic [6:0]     wdataram_waddr,
    input   logic           wdataram_re,
    input   logic [6:0]     wdataram_raddr,
    output  logic [255:0]   wdataram_dout
);

    // Construct the write data masks.
    logic [127:0] data_mask_first_half, data_mask_second_half;
    assign data_mask_first_half = ~{{8{wdataram_mask[15]}},{8{wdataram_mask[14]}},{8{wdataram_mask[13]}},{8{wdataram_mask[12]}},
                            {8{wdataram_mask[11]}},{8{wdataram_mask[10]}},{8{wdataram_mask[9] }},{8{wdataram_mask[8] }},
                            {8{wdataram_mask[7] }},{8{wdataram_mask[6] }},{8{wdataram_mask[5] }},{8{wdataram_mask[4] }},
                            {8{wdataram_mask[3] }},{8{wdataram_mask[2] }},{8{wdataram_mask[1] }},{8{wdataram_mask[0] }}};

    assign data_mask_second_half = ~{{8{wdataram_mask[31]}},{8{wdataram_mask[30]}},{8{wdataram_mask[29]}},{8{wdataram_mask[28]}},
                            {8{wdataram_mask[27]}},{8{wdataram_mask[26]}},{8{wdataram_mask[25]}},{8{wdataram_mask[24]}},
                            {8{wdataram_mask[23]}},{8{wdataram_mask[22]}},{8{wdataram_mask[21]}},{8{wdataram_mask[20]}},
                            {8{wdataram_mask[19]}},{8{wdataram_mask[18]}},{8{wdataram_mask[17]}},{8{wdataram_mask[16]}}};

    ln05lpe_a00_mc_rf2rwp_hsr_rvt_128x128m1b4c1r2_wrapper sram_first_half ( 
        .RA         (wdataram_raddr),
        .WA         (wdataram_waddr),
        .DI         (wdataram_din[127:0]),
        .RCK        (clk),
        .WCK        (clk),
        .REN        (wdataram_re),
        .WEN        (wdataram_wr),
        .BWEN       (data_mask_first_half),
        .DOUT       (wdataram_din[127:0]),
        .SI_D_L     (1'b0),
        .SI_D_R     (1'b0),
        .SO_D_L     (),
        .SO_D_R     (),
        .SE         (1'b0),
        .DFTRAM     (1'b0),
        .MCSRD      (2'b10),
        .KCS        (1'b0), // not sure about this setting
        .MCSWR      (2'b10),
        .ADME       (3'b100),
        .CRE1       (1'b0),
        .CRE2       (1'b0),
        .FCA1       ('0),
        .FCA2       ('0),
        .RREN1      (1'b0),
        .FRA1        ('0),
        .RREN2      (1'b0),
        .FRA2       ('0),
        .RET        (1'b0),
        .PDE        (1'b0),
        .PRN        ()
    );

    ln05lpe_a00_mc_rf2rwp_hsr_rvt_128x128m1b4c1r2_wrapper sram_second_half ( 
        .RA         (wdataram_raddr),
        .WA         (wdataram_waddr),
        .DI         (wdataram_din[255:128]),
        .RCK        (clk),
        .WCK        (clk),
        .REN        (wdataram_re),
        .WEN        (wdataram_wr),
        .BWEN       (data_mask_second_half),
        .DOUT       (wdataram_din[255:128]),
        .SI_D_L     (1'b0),
        .SI_D_R     (1'b0),
        .SO_D_L     (),
        .SO_D_R     (),
        .SE         (1'b0),
        .DFTRAM     (1'b0),
        .MCSRD      (2'b10),
        .KCS        (1'b0), // not sure about this setting
        .MCSWR      (2'b10),
        .ADME       (3'b100),
        .CRE1       (1'b0),
        .CRE2       (1'b0),
        .FCA1       ('0),
        .FCA2       ('0),
        .RREN1      (1'b0),
        .FRA1       ('0),
        .RREN2      (1'b0),
        .FRA2       ('0),
        .RET        (1'b0),
        .PDE        (1'b0),
        .PRN        ()
    );

endmodule
