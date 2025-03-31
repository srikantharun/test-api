// Intermediate assignment to dump RVVI signals
genvar i_rvvi_index, x_index, f_index, v_index, csr_index;
logic[63:0] dump_mhpmevent[1:0][29];
logic[63:0] dump_mhpmcounter[1:0][29];
logic[63:0] dump_mstatus;
logic[63:0] dump_mtvec;
logic[63:0] dump_mie;
logic[63:0] dump_mip;
logic[63:0] dump_mepc;
logic[63:0] dump_mcause;
logic[63:0] dump_mtval;
logic[63:0] dump_mideleg;

logic[63:0] dump_ra;
logic[63:0] dump_sp;
logic[63:0] dump_ga;
logic[63:0] dump_tp;
logic[63:0] dump_t0;
logic[63:0] dump_t1;
logic[63:0] dump_t2;
logic[63:0] dump_s0;
logic[63:0] dump_s1;
logic[63:0] dump_a0;
logic[63:0] dump_a1;
logic[63:0] dump_a2;
logic[63:0] dump_a3;
logic[63:0] dump_a4;
logic[63:0] dump_a5;
logic[63:0] dump_a6;
logic[63:0] dump_a7;
logic[63:0] dump_s2;
logic[63:0] dump_s3;
logic[63:0] dump_s4;
logic[63:0] dump_s5;
logic[63:0] dump_s6;
logic[63:0] dump_s7;
logic[63:0] dump_s8;
logic[63:0] dump_s9;
logic[63:0] dump_s10;
logic[63:0] dump_s11;
logic[63:0] dump_t3;
logic[63:0] dump_t4;
logic[63:0] dump_t5;
logic[63:0] dump_t6;
logic[63:0] dump_ft0;
logic[63:0] dump_ft1;
logic[63:0] dump_ft2;
logic[63:0] dump_ft3;
logic[63:0] dump_ft4;
logic[63:0] dump_ft5;
logic[63:0] dump_ft6;
logic[63:0] dump_ft7;
logic[63:0] dump_fs0;
logic[63:0] dump_fs1;
logic[63:0] dump_fa0;
logic[63:0] dump_fa1;
logic[63:0] dump_fa2;
logic[63:0] dump_fa3;
logic[63:0] dump_fa4;
logic[63:0] dump_fa5;
logic[63:0] dump_fa6;
logic[63:0] dump_fa7;
logic[63:0] dump_fs2;
logic[63:0] dump_fs3;
logic[63:0] dump_fs4;
logic[63:0] dump_fs5;
logic[63:0] dump_fs6;
logic[63:0] dump_fs7;
logic[63:0] dump_fs8;
logic[63:0] dump_fs9;
logic[63:0] dump_fs10;
logic[63:0] dump_fs11;
logic[63:0] dump_ft8;
logic[63:0] dump_ft9;
logic[63:0] dump_ft10;
logic[63:0] dump_ft11;

// CSRs
assign dump_mstatus = i_cva6v_rvvi.csr.mstatus;
assign dump_mtvec = i_cva6v_rvvi.csr.mtvec;
assign dump_mie = i_cva6v_rvvi.csr.mie;
assign dump_mip = i_cva6v_rvvi.csr.mip;
assign dump_mepc = i_cva6v_rvvi.csr.mepc;
assign dump_mcause = i_cva6v_rvvi.csr.mcause;
assign dump_mtval = i_cva6v_rvvi.csr.mtval;
assign dump_mideleg = i_cva6v_rvvi.csr.mideleg;

// Dump xreg and freg
always @(posedge clk_i or negedge rst_ni) begin
  if (!rst_ni) begin
    dump_ra   <=  0;
    dump_sp   <=  0;
    dump_ga   <=  0;
    dump_tp   <=  0;
    dump_t0   <=  0;
    dump_t1   <=  0;
    dump_t2   <=  0;
    dump_s0   <=  0;
    dump_s1   <=  0;
    dump_a0   <=  0;
    dump_a1   <=  0;
    dump_a2   <=  0;
    dump_a3   <=  0;
    dump_a4   <=  0;
    dump_a5   <=  0;
    dump_a6   <=  0;
    dump_a7   <=  0;
    dump_s2   <=  0;
    dump_s3   <=  0;
    dump_s4   <=  0;
    dump_s5   <=  0;
    dump_s6   <=  0;
    dump_s7   <=  0;
    dump_s8   <=  0;
    dump_s9   <=  0;
    dump_s10  <=  0;
    dump_s11  <=  0;
    dump_t3   <=  0;
    dump_t4   <=  0;
    dump_t5   <=  0;
    dump_t6   <=  0;
    dump_ft0  <=  0;
    dump_ft1  <=  0;
    dump_ft2  <=  0;
    dump_ft3  <=  0;
    dump_ft4  <=  0;
    dump_ft5  <=  0;
    dump_ft6  <=  0;
    dump_ft7  <=  0;
    dump_fs0  <=  0;
    dump_fs1  <=  0;
    dump_fa0  <=  0;
    dump_fa1  <=  0;
    dump_fa2  <=  0;
    dump_fa3  <=  0;
    dump_fa4  <=  0;
    dump_fa5  <=  0;
    dump_fa6  <=  0;
    dump_fa7  <=  0;
    dump_fs2  <=  0;
    dump_fs3  <=  0;
    dump_fs4  <=  0;
    dump_fs5  <=  0;
    dump_fs6  <=  0;
    dump_fs7  <=  0;
    dump_fs8  <=  0;
    dump_fs9  <=  0;
    dump_fs10 <=  0;
    dump_fs11 <=  0;
    dump_ft8  <=  0;
    dump_ft9  <=  0;
    dump_ft10 <=  0;
    dump_ft11 <=  0;
  end else begin
    if (i_cva6v_rvvi.rvvi_trace_o.x_wb[0][1])  dump_ra   <= i_cva6v_rvvi.rvvi_trace_o.x_wdata[0][1];
    if (i_cva6v_rvvi.rvvi_trace_o.x_wb[0][2])  dump_sp   <= i_cva6v_rvvi.rvvi_trace_o.x_wdata[0][2];
    if (i_cva6v_rvvi.rvvi_trace_o.x_wb[0][3])  dump_ga   <= i_cva6v_rvvi.rvvi_trace_o.x_wdata[0][3];
    if (i_cva6v_rvvi.rvvi_trace_o.x_wb[0][4])  dump_tp   <= i_cva6v_rvvi.rvvi_trace_o.x_wdata[0][4];
    if (i_cva6v_rvvi.rvvi_trace_o.x_wb[0][5])  dump_t0   <= i_cva6v_rvvi.rvvi_trace_o.x_wdata[0][5];
    if (i_cva6v_rvvi.rvvi_trace_o.x_wb[0][6])  dump_t1   <= i_cva6v_rvvi.rvvi_trace_o.x_wdata[0][6];
    if (i_cva6v_rvvi.rvvi_trace_o.x_wb[0][7])  dump_t2   <= i_cva6v_rvvi.rvvi_trace_o.x_wdata[0][7];
    if (i_cva6v_rvvi.rvvi_trace_o.x_wb[0][8])  dump_s0   <= i_cva6v_rvvi.rvvi_trace_o.x_wdata[0][8];
    if (i_cva6v_rvvi.rvvi_trace_o.x_wb[0][9])  dump_s1   <= i_cva6v_rvvi.rvvi_trace_o.x_wdata[0][9];
    if (i_cva6v_rvvi.rvvi_trace_o.x_wb[0][10]) dump_a0   <= i_cva6v_rvvi.rvvi_trace_o.x_wdata[0][10];
    if (i_cva6v_rvvi.rvvi_trace_o.x_wb[0][11]) dump_a1   <= i_cva6v_rvvi.rvvi_trace_o.x_wdata[0][11];
    if (i_cva6v_rvvi.rvvi_trace_o.x_wb[0][12]) dump_a2   <= i_cva6v_rvvi.rvvi_trace_o.x_wdata[0][12];
    if (i_cva6v_rvvi.rvvi_trace_o.x_wb[0][13]) dump_a3   <= i_cva6v_rvvi.rvvi_trace_o.x_wdata[0][13];
    if (i_cva6v_rvvi.rvvi_trace_o.x_wb[0][14]) dump_a4   <= i_cva6v_rvvi.rvvi_trace_o.x_wdata[0][14];
    if (i_cva6v_rvvi.rvvi_trace_o.x_wb[0][15]) dump_a5   <= i_cva6v_rvvi.rvvi_trace_o.x_wdata[0][15];
    if (i_cva6v_rvvi.rvvi_trace_o.x_wb[0][16]) dump_a6   <= i_cva6v_rvvi.rvvi_trace_o.x_wdata[0][16];
    if (i_cva6v_rvvi.rvvi_trace_o.x_wb[0][17]) dump_a7   <= i_cva6v_rvvi.rvvi_trace_o.x_wdata[0][17];
    if (i_cva6v_rvvi.rvvi_trace_o.x_wb[0][18]) dump_s2   <= i_cva6v_rvvi.rvvi_trace_o.x_wdata[0][18];
    if (i_cva6v_rvvi.rvvi_trace_o.x_wb[0][19]) dump_s3   <= i_cva6v_rvvi.rvvi_trace_o.x_wdata[0][19];
    if (i_cva6v_rvvi.rvvi_trace_o.x_wb[0][20]) dump_s4   <= i_cva6v_rvvi.rvvi_trace_o.x_wdata[0][20];
    if (i_cva6v_rvvi.rvvi_trace_o.x_wb[0][21]) dump_s5   <= i_cva6v_rvvi.rvvi_trace_o.x_wdata[0][21];
    if (i_cva6v_rvvi.rvvi_trace_o.x_wb[0][22]) dump_s6   <= i_cva6v_rvvi.rvvi_trace_o.x_wdata[0][22];
    if (i_cva6v_rvvi.rvvi_trace_o.x_wb[0][23]) dump_s7   <= i_cva6v_rvvi.rvvi_trace_o.x_wdata[0][23];
    if (i_cva6v_rvvi.rvvi_trace_o.x_wb[0][24]) dump_s8   <= i_cva6v_rvvi.rvvi_trace_o.x_wdata[0][24];
    if (i_cva6v_rvvi.rvvi_trace_o.x_wb[0][25]) dump_s9   <= i_cva6v_rvvi.rvvi_trace_o.x_wdata[0][25];
    if (i_cva6v_rvvi.rvvi_trace_o.x_wb[0][26]) dump_s10  <= i_cva6v_rvvi.rvvi_trace_o.x_wdata[0][26];
    if (i_cva6v_rvvi.rvvi_trace_o.x_wb[0][27]) dump_s11  <= i_cva6v_rvvi.rvvi_trace_o.x_wdata[0][27];
    if (i_cva6v_rvvi.rvvi_trace_o.x_wb[0][28]) dump_t3   <= i_cva6v_rvvi.rvvi_trace_o.x_wdata[0][28];
    if (i_cva6v_rvvi.rvvi_trace_o.x_wb[0][29]) dump_t4   <= i_cva6v_rvvi.rvvi_trace_o.x_wdata[0][29];
    if (i_cva6v_rvvi.rvvi_trace_o.x_wb[0][30]) dump_t5   <= i_cva6v_rvvi.rvvi_trace_o.x_wdata[0][30];
    if (i_cva6v_rvvi.rvvi_trace_o.x_wb[0][31]) dump_t6   <= i_cva6v_rvvi.rvvi_trace_o.x_wdata[0][31];
    if (i_cva6v_rvvi.rvvi_trace_o.f_wb[0][0])  dump_ft0  <= i_cva6v_rvvi.rvvi_trace_o.f_wdata[0][0];
    if (i_cva6v_rvvi.rvvi_trace_o.f_wb[0][1])  dump_ft1  <= i_cva6v_rvvi.rvvi_trace_o.f_wdata[0][1];
    if (i_cva6v_rvvi.rvvi_trace_o.f_wb[0][2])  dump_ft2  <= i_cva6v_rvvi.rvvi_trace_o.f_wdata[0][2];
    if (i_cva6v_rvvi.rvvi_trace_o.f_wb[0][3])  dump_ft3  <= i_cva6v_rvvi.rvvi_trace_o.f_wdata[0][3];
    if (i_cva6v_rvvi.rvvi_trace_o.f_wb[0][4])  dump_ft4  <= i_cva6v_rvvi.rvvi_trace_o.f_wdata[0][4];
    if (i_cva6v_rvvi.rvvi_trace_o.f_wb[0][5])  dump_ft5  <= i_cva6v_rvvi.rvvi_trace_o.f_wdata[0][5];
    if (i_cva6v_rvvi.rvvi_trace_o.f_wb[0][6])  dump_ft6  <= i_cva6v_rvvi.rvvi_trace_o.f_wdata[0][6];
    if (i_cva6v_rvvi.rvvi_trace_o.f_wb[0][7])  dump_ft7  <= i_cva6v_rvvi.rvvi_trace_o.f_wdata[0][7];
    if (i_cva6v_rvvi.rvvi_trace_o.f_wb[0][8])  dump_fs0  <= i_cva6v_rvvi.rvvi_trace_o.f_wdata[0][8];
    if (i_cva6v_rvvi.rvvi_trace_o.f_wb[0][9])  dump_fs1  <= i_cva6v_rvvi.rvvi_trace_o.f_wdata[0][9];
    if (i_cva6v_rvvi.rvvi_trace_o.f_wb[0][10]) dump_fa0  <= i_cva6v_rvvi.rvvi_trace_o.f_wdata[0][10];
    if (i_cva6v_rvvi.rvvi_trace_o.f_wb[0][11]) dump_fa1  <= i_cva6v_rvvi.rvvi_trace_o.f_wdata[0][11];
    if (i_cva6v_rvvi.rvvi_trace_o.f_wb[0][12]) dump_fa2  <= i_cva6v_rvvi.rvvi_trace_o.f_wdata[0][12];
    if (i_cva6v_rvvi.rvvi_trace_o.f_wb[0][13]) dump_fa3  <= i_cva6v_rvvi.rvvi_trace_o.f_wdata[0][13];
    if (i_cva6v_rvvi.rvvi_trace_o.f_wb[0][14]) dump_fa4  <= i_cva6v_rvvi.rvvi_trace_o.f_wdata[0][14];
    if (i_cva6v_rvvi.rvvi_trace_o.f_wb[0][15]) dump_fa5  <= i_cva6v_rvvi.rvvi_trace_o.f_wdata[0][15];
    if (i_cva6v_rvvi.rvvi_trace_o.f_wb[0][16]) dump_fa6  <= i_cva6v_rvvi.rvvi_trace_o.f_wdata[0][16];
    if (i_cva6v_rvvi.rvvi_trace_o.f_wb[0][17]) dump_fa7  <= i_cva6v_rvvi.rvvi_trace_o.f_wdata[0][17];
    if (i_cva6v_rvvi.rvvi_trace_o.f_wb[0][18]) dump_fs2  <= i_cva6v_rvvi.rvvi_trace_o.f_wdata[0][18];
    if (i_cva6v_rvvi.rvvi_trace_o.f_wb[0][19]) dump_fs3  <= i_cva6v_rvvi.rvvi_trace_o.f_wdata[0][19];
    if (i_cva6v_rvvi.rvvi_trace_o.f_wb[0][20]) dump_fs4  <= i_cva6v_rvvi.rvvi_trace_o.f_wdata[0][20];
    if (i_cva6v_rvvi.rvvi_trace_o.f_wb[0][21]) dump_fs5  <= i_cva6v_rvvi.rvvi_trace_o.f_wdata[0][21];
    if (i_cva6v_rvvi.rvvi_trace_o.f_wb[0][22]) dump_fs6  <= i_cva6v_rvvi.rvvi_trace_o.f_wdata[0][22];
    if (i_cva6v_rvvi.rvvi_trace_o.f_wb[0][23]) dump_fs7  <= i_cva6v_rvvi.rvvi_trace_o.f_wdata[0][23];
    if (i_cva6v_rvvi.rvvi_trace_o.f_wb[0][24]) dump_fs8  <= i_cva6v_rvvi.rvvi_trace_o.f_wdata[0][24];
    if (i_cva6v_rvvi.rvvi_trace_o.f_wb[0][25]) dump_fs9  <= i_cva6v_rvvi.rvvi_trace_o.f_wdata[0][25];
    if (i_cva6v_rvvi.rvvi_trace_o.f_wb[0][26]) dump_fs10 <= i_cva6v_rvvi.rvvi_trace_o.f_wdata[0][26];
    if (i_cva6v_rvvi.rvvi_trace_o.f_wb[0][27]) dump_fs11 <= i_cva6v_rvvi.rvvi_trace_o.f_wdata[0][27];
    if (i_cva6v_rvvi.rvvi_trace_o.f_wb[0][28]) dump_ft8  <= i_cva6v_rvvi.rvvi_trace_o.f_wdata[0][28];
    if (i_cva6v_rvvi.rvvi_trace_o.f_wb[0][29]) dump_ft9  <= i_cva6v_rvvi.rvvi_trace_o.f_wdata[0][29];
    if (i_cva6v_rvvi.rvvi_trace_o.f_wb[0][30]) dump_ft10 <= i_cva6v_rvvi.rvvi_trace_o.f_wdata[0][30];
    if (i_cva6v_rvvi.rvvi_trace_o.f_wb[0][31]) dump_ft11 <= i_cva6v_rvvi.rvvi_trace_o.f_wdata[0][31];
  end
end

generate
  for (i_rvvi_index=0; i_rvvi_index < CVA6VConfig.CVA6Cfg.NrCommitPorts; i_rvvi_index++) begin
    assign rvvi_dump_if[i_rvvi_index].valid = i_cva6v_rvvi.rvvi_trace_o.valid[i_rvvi_index];
    assign rvvi_dump_if[i_rvvi_index].order = i_cva6v_rvvi.rvvi_trace_o.order[i_rvvi_index];
    assign rvvi_dump_if[i_rvvi_index].insn = i_cva6v_rvvi.rvvi_trace_o.insn[i_rvvi_index];
    assign rvvi_dump_if[i_rvvi_index].trap = i_cva6v_rvvi.rvvi_trace_o.trap[i_rvvi_index];
    assign rvvi_dump_if[i_rvvi_index].debug_mode = i_cva6v_rvvi.rvvi_trace_o.debug_mode[i_rvvi_index];
    assign rvvi_dump_if[i_rvvi_index].pc_rdata = i_cva6v_rvvi.rvvi_trace_o.pc_rdata[i_rvvi_index];
    assign rvvi_dump_if[i_rvvi_index].x_wb = i_cva6v_rvvi.rvvi_trace_o.x_wb[i_rvvi_index];

    assign rvvi_dump_if[i_rvvi_index].f_wb = i_cva6v_rvvi.rvvi_trace_o.f_wb[i_rvvi_index];
    assign rvvi_dump_if[i_rvvi_index].v_wb = i_cva6v_rvvi.rvvi_trace_o.v_wb[i_rvvi_index];

    assign rvvi_dump_if[i_rvvi_index].csr_wb = i_cva6v_rvvi.rvvi_trace_o.csr_wb[i_rvvi_index];
    assign rvvi_dump_if[i_rvvi_index].lrsc_cancel = i_cva6v_rvvi.rvvi_trace_o.lrsc_cancel[i_rvvi_index];
    assign rvvi_dump_if[i_rvvi_index].pc_wdata = i_cva6v_rvvi.rvvi_trace_o.pc_wdata[i_rvvi_index];
    assign rvvi_dump_if[i_rvvi_index].intr = i_cva6v_rvvi.rvvi_trace_o.intr[i_rvvi_index];
    assign rvvi_dump_if[i_rvvi_index].halt = i_cva6v_rvvi.rvvi_trace_o.halt[i_rvvi_index];
    assign rvvi_dump_if[i_rvvi_index].ixl = i_cva6v_rvvi.rvvi_trace_o.ixl[i_rvvi_index];
    assign rvvi_dump_if[i_rvvi_index].mode = i_cva6v_rvvi.rvvi_trace_o.mode[i_rvvi_index];

    for (x_index=0; x_index < 32; x_index++) begin
      assign rvvi_dump_if[i_rvvi_index].x_wdata[x_index] = i_cva6v_rvvi.rvvi_trace_o.x_wdata[i_rvvi_index][x_index];
    end
    for (f_index=0; f_index < 32; f_index++) begin
      assign rvvi_dump_if[i_rvvi_index].f_wdata[f_index] = i_cva6v_rvvi.rvvi_trace_o.f_wdata[i_rvvi_index][f_index];
    end
    for (v_index=0; v_index < 32; v_index++) begin
      assign rvvi_dump_if[i_rvvi_index].v_wdata[v_index] = i_cva6v_rvvi.rvvi_trace_o.v_wdata[i_rvvi_index][v_index];
    end

    // TODO: 4k lines of assignment slows the sim significantly. Only target the indexes (i.e. specific CSR) required/critical
    for (csr_index=0; csr_index < 4096; csr_index++) begin
    //  assign rvvi_dump_if[i_rvvi_index].csr[csr_index] = i_cva6v_rvvi.rvvi_trace_o.csr[csr_index];
      if (csr_index >= 'h323 && csr_index <= 'h33F) begin
        assign dump_mhpmevent[i_rvvi_index][csr_index-'h323 ] = i_cva6v_rvvi.rvvi_trace_o.csr[csr_index];
      end
      if (csr_index >= 'hB83 && csr_index <= 'hB9F) begin
        assign dump_mhpmcounter[i_rvvi_index][csr_index-'hB83 ] = i_cva6v_rvvi.rvvi_trace_o.csr[csr_index];
      end
    end

  end
endgenerate

