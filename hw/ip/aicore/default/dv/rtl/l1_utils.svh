//TODO: change these functions to some memory_preloading_pkg compatible ones, following: https://git.axelera.ai/prod/europa/-/merge_requests/1446
  `define AIC_L1_PATH hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem
  task preload_l1_single_value(bit _value = 0);
   for (int i = 0; i < 4096; i++) begin
`ifdef TARGET_SF5A
      `AIC_L1_PATH.g_sbank[0].u_sub_bank.g_mini_bank[0].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(i, _value);
      `AIC_L1_PATH.g_sbank[0].u_sub_bank.g_mini_bank[1].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(i, _value);
      `AIC_L1_PATH.g_sbank[0].u_sub_bank.g_mini_bank[2].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(i, _value);
      `AIC_L1_PATH.g_sbank[0].u_sub_bank.g_mini_bank[3].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(i, _value);
      `AIC_L1_PATH.g_sbank[0].u_sub_bank.g_mini_bank[4].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(i, _value);
      `AIC_L1_PATH.g_sbank[0].u_sub_bank.g_mini_bank[5].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(i, _value);
      `AIC_L1_PATH.g_sbank[0].u_sub_bank.g_mini_bank[6].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(i, _value);
      `AIC_L1_PATH.g_sbank[0].u_sub_bank.g_mini_bank[7].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(i, _value);
      `AIC_L1_PATH.g_sbank[0].u_sub_bank.g_mini_bank[8].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(i, _value);
      `AIC_L1_PATH.g_sbank[0].u_sub_bank.g_mini_bank[9].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(i, _value);
      `AIC_L1_PATH.g_sbank[0].u_sub_bank.g_mini_bank[10].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(i, _value);
      `AIC_L1_PATH.g_sbank[0].u_sub_bank.g_mini_bank[11].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(i, _value);
      `AIC_L1_PATH.g_sbank[0].u_sub_bank.g_mini_bank[12].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(i, _value);
      `AIC_L1_PATH.g_sbank[0].u_sub_bank.g_mini_bank[13].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(i, _value);
      `AIC_L1_PATH.g_sbank[0].u_sub_bank.g_mini_bank[14].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(i, _value);
      `AIC_L1_PATH.g_sbank[0].u_sub_bank.g_mini_bank[15].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(i, _value);
      `AIC_L1_PATH.g_sbank[1].u_sub_bank.g_mini_bank[0].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(i, _value);
      `AIC_L1_PATH.g_sbank[1].u_sub_bank.g_mini_bank[1].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(i, _value);
      `AIC_L1_PATH.g_sbank[1].u_sub_bank.g_mini_bank[2].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(i, _value);
      `AIC_L1_PATH.g_sbank[1].u_sub_bank.g_mini_bank[3].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(i, _value);
      `AIC_L1_PATH.g_sbank[1].u_sub_bank.g_mini_bank[4].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(i, _value);
      `AIC_L1_PATH.g_sbank[1].u_sub_bank.g_mini_bank[5].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(i, _value);
      `AIC_L1_PATH.g_sbank[1].u_sub_bank.g_mini_bank[6].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(i, _value);
      `AIC_L1_PATH.g_sbank[1].u_sub_bank.g_mini_bank[7].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(i, _value);
      `AIC_L1_PATH.g_sbank[1].u_sub_bank.g_mini_bank[8].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(i, _value);
      `AIC_L1_PATH.g_sbank[1].u_sub_bank.g_mini_bank[9].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(i, _value);
      `AIC_L1_PATH.g_sbank[1].u_sub_bank.g_mini_bank[10].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(i, _value);
      `AIC_L1_PATH.g_sbank[1].u_sub_bank.g_mini_bank[11].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(i, _value);
      `AIC_L1_PATH.g_sbank[1].u_sub_bank.g_mini_bank[12].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(i, _value);
      `AIC_L1_PATH.g_sbank[1].u_sub_bank.g_mini_bank[13].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(i, _value);
      `AIC_L1_PATH.g_sbank[1].u_sub_bank.g_mini_bank[14].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(i, _value);
      `AIC_L1_PATH.g_sbank[1].u_sub_bank.g_mini_bank[15].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(i, _value);
      `AIC_L1_PATH.g_sbank[2].u_sub_bank.g_mini_bank[0].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(i, _value);
      `AIC_L1_PATH.g_sbank[2].u_sub_bank.g_mini_bank[1].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(i, _value);
      `AIC_L1_PATH.g_sbank[2].u_sub_bank.g_mini_bank[2].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(i, _value);
      `AIC_L1_PATH.g_sbank[2].u_sub_bank.g_mini_bank[3].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(i, _value);
      `AIC_L1_PATH.g_sbank[2].u_sub_bank.g_mini_bank[4].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(i, _value);
      `AIC_L1_PATH.g_sbank[2].u_sub_bank.g_mini_bank[5].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(i, _value);
      `AIC_L1_PATH.g_sbank[2].u_sub_bank.g_mini_bank[6].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(i, _value);
      `AIC_L1_PATH.g_sbank[2].u_sub_bank.g_mini_bank[7].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(i, _value);
      `AIC_L1_PATH.g_sbank[2].u_sub_bank.g_mini_bank[8].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(i, _value);
      `AIC_L1_PATH.g_sbank[2].u_sub_bank.g_mini_bank[9].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(i, _value);
      `AIC_L1_PATH.g_sbank[2].u_sub_bank.g_mini_bank[10].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(i, _value);
      `AIC_L1_PATH.g_sbank[2].u_sub_bank.g_mini_bank[11].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(i, _value);
      `AIC_L1_PATH.g_sbank[2].u_sub_bank.g_mini_bank[12].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(i, _value);
      `AIC_L1_PATH.g_sbank[2].u_sub_bank.g_mini_bank[13].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(i, _value);
      `AIC_L1_PATH.g_sbank[2].u_sub_bank.g_mini_bank[14].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(i, _value);
      `AIC_L1_PATH.g_sbank[2].u_sub_bank.g_mini_bank[15].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(i, _value);
      `AIC_L1_PATH.g_sbank[3].u_sub_bank.g_mini_bank[0].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(i, _value);
      `AIC_L1_PATH.g_sbank[3].u_sub_bank.g_mini_bank[1].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(i, _value);
      `AIC_L1_PATH.g_sbank[3].u_sub_bank.g_mini_bank[2].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(i, _value);
      `AIC_L1_PATH.g_sbank[3].u_sub_bank.g_mini_bank[3].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(i, _value);
      `AIC_L1_PATH.g_sbank[3].u_sub_bank.g_mini_bank[4].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(i, _value);
      `AIC_L1_PATH.g_sbank[3].u_sub_bank.g_mini_bank[5].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(i, _value);
      `AIC_L1_PATH.g_sbank[3].u_sub_bank.g_mini_bank[6].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(i, _value);
      `AIC_L1_PATH.g_sbank[3].u_sub_bank.g_mini_bank[7].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(i, _value);
      `AIC_L1_PATH.g_sbank[3].u_sub_bank.g_mini_bank[8].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(i, _value);
      `AIC_L1_PATH.g_sbank[3].u_sub_bank.g_mini_bank[9].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(i, _value);
      `AIC_L1_PATH.g_sbank[3].u_sub_bank.g_mini_bank[10].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(i, _value);
      `AIC_L1_PATH.g_sbank[3].u_sub_bank.g_mini_bank[11].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(i, _value);
      `AIC_L1_PATH.g_sbank[3].u_sub_bank.g_mini_bank[12].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(i, _value);
      `AIC_L1_PATH.g_sbank[3].u_sub_bank.g_mini_bank[13].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(i, _value);
      `AIC_L1_PATH.g_sbank[3].u_sub_bank.g_mini_bank[14].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(i, _value);
      `AIC_L1_PATH.g_sbank[3].u_sub_bank.g_mini_bank[15].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(i, _value);
`else
    for (int nsb = 0; nsb < 4; nsb++) begin
        for (int nmb = 0; nmb < 16; nmb++) begin
            uvm_hdl_deposit($sformatf("hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[%0d].u_sub_bank.g_mini_bank[%0d].u_mini_bank.g_macro[0].u_macro.memory_q[%0d]", nsb, nmb, i), _value);
        end
    end
`endif
   end
  endtask

  task preload_l1_file(string _elf_file);
    integer file;
    reg [127:0] data;
    int addr;


    file = $fopen($sformatf("%s.aicore_0.l1.sb_0.mb_0.128b.texthex", _elf_file), "r");
    addr = '0;
    data = '0;
    while(!$feof(file)) begin
        $fscanf(file, "%h\n", data);
`ifdef TARGET_SF5A
        hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[0].u_sub_bank.g_mini_bank[0].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(addr, data);
`else
        uvm_hdl_deposit($sformatf("hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[0].u_sub_bank.g_mini_bank[0].u_mini_bank.g_macro[0].u_macro.memory_q[%0d]", addr), data);
`endif

        addr += 1;
    end


    file = $fopen($sformatf("%s.aicore_0.l1.sb_0.mb_1.128b.texthex", _elf_file), "r");
    addr = '0;
    data = '0;
    while(!$feof(file)) begin
        $fscanf(file, "%h\n", data);
`ifdef TARGET_SF5A
        hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[0].u_sub_bank.g_mini_bank[1].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(addr, data);
`else
        uvm_hdl_deposit($sformatf("hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[0].u_sub_bank.g_mini_bank[1].u_mini_bank.g_macro[0].u_macro.memory_q[%0d]", addr), data);
`endif

        addr += 1;
    end


    file = $fopen($sformatf("%s.aicore_0.l1.sb_0.mb_2.128b.texthex", _elf_file), "r");
    addr = '0;
    data = '0;
    while(!$feof(file)) begin
        $fscanf(file, "%h\n", data);
`ifdef TARGET_SF5A
        hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[0].u_sub_bank.g_mini_bank[2].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(addr, data);
`else
        uvm_hdl_deposit($sformatf("hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[0].u_sub_bank.g_mini_bank[2].u_mini_bank.g_macro[0].u_macro.memory_q[%0d]", addr), data);
`endif

        addr += 1;
    end


    file = $fopen($sformatf("%s.aicore_0.l1.sb_0.mb_3.128b.texthex", _elf_file), "r");
    addr = '0;
    data = '0;
    while(!$feof(file)) begin
        $fscanf(file, "%h\n", data);
`ifdef TARGET_SF5A
        hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[0].u_sub_bank.g_mini_bank[3].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(addr, data);
`else
        uvm_hdl_deposit($sformatf("hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[0].u_sub_bank.g_mini_bank[3].u_mini_bank.g_macro[0].u_macro.memory_q[%0d]", addr), data);
`endif

        addr += 1;
    end


    file = $fopen($sformatf("%s.aicore_0.l1.sb_0.mb_4.128b.texthex", _elf_file), "r");
    addr = '0;
    data = '0;
    while(!$feof(file)) begin
        $fscanf(file, "%h\n", data);
`ifdef TARGET_SF5A
        hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[0].u_sub_bank.g_mini_bank[4].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(addr, data);
`else
        uvm_hdl_deposit($sformatf("hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[0].u_sub_bank.g_mini_bank[4].u_mini_bank.g_macro[0].u_macro.memory_q[%0d]", addr), data);
`endif

        addr += 1;
    end


    file = $fopen($sformatf("%s.aicore_0.l1.sb_0.mb_5.128b.texthex", _elf_file), "r");
    addr = '0;
    data = '0;
    while(!$feof(file)) begin
        $fscanf(file, "%h\n", data);
`ifdef TARGET_SF5A
        hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[0].u_sub_bank.g_mini_bank[5].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(addr, data);
`else
        uvm_hdl_deposit($sformatf("hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[0].u_sub_bank.g_mini_bank[5].u_mini_bank.g_macro[0].u_macro.memory_q[%0d]", addr), data);
`endif

        addr += 1;
    end


    file = $fopen($sformatf("%s.aicore_0.l1.sb_0.mb_6.128b.texthex", _elf_file), "r");
    addr = '0;
    data = '0;
    while(!$feof(file)) begin
        $fscanf(file, "%h\n", data);
`ifdef TARGET_SF5A
        hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[0].u_sub_bank.g_mini_bank[6].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(addr, data);
`else
        uvm_hdl_deposit($sformatf("hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[0].u_sub_bank.g_mini_bank[6].u_mini_bank.g_macro[0].u_macro.memory_q[%0d]", addr), data);
`endif

        addr += 1;
    end


    file = $fopen($sformatf("%s.aicore_0.l1.sb_0.mb_7.128b.texthex", _elf_file), "r");
    addr = '0;
    data = '0;
    while(!$feof(file)) begin
        $fscanf(file, "%h\n", data);
`ifdef TARGET_SF5A
        hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[0].u_sub_bank.g_mini_bank[7].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(addr, data);
`else
        uvm_hdl_deposit($sformatf("hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[0].u_sub_bank.g_mini_bank[7].u_mini_bank.g_macro[0].u_macro.memory_q[%0d]", addr), data);
`endif

        addr += 1;
    end


    file = $fopen($sformatf("%s.aicore_0.l1.sb_0.mb_8.128b.texthex", _elf_file), "r");
    addr = '0;
    data = '0;
    while(!$feof(file)) begin
        $fscanf(file, "%h\n", data);
`ifdef TARGET_SF5A
        hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[0].u_sub_bank.g_mini_bank[8].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(addr, data);
`else
        uvm_hdl_deposit($sformatf("hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[0].u_sub_bank.g_mini_bank[8].u_mini_bank.g_macro[0].u_macro.memory_q[%0d]", addr), data);
`endif

        addr += 1;
    end


    file = $fopen($sformatf("%s.aicore_0.l1.sb_0.mb_9.128b.texthex", _elf_file), "r");
    addr = '0;
    data = '0;
    while(!$feof(file)) begin
        $fscanf(file, "%h\n", data);
`ifdef TARGET_SF5A
        hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[0].u_sub_bank.g_mini_bank[9].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(addr, data);
`else
        uvm_hdl_deposit($sformatf("hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[0].u_sub_bank.g_mini_bank[9].u_mini_bank.g_macro[0].u_macro.memory_q[%0d]", addr), data);
`endif

        addr += 1;
    end


    file = $fopen($sformatf("%s.aicore_0.l1.sb_0.mb_10.128b.texthex", _elf_file), "r");
    addr = '0;
    data = '0;
    while(!$feof(file)) begin
        $fscanf(file, "%h\n", data);
`ifdef TARGET_SF5A
        hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[0].u_sub_bank.g_mini_bank[10].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(addr, data);
`else
        uvm_hdl_deposit($sformatf("hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[0].u_sub_bank.g_mini_bank[10].u_mini_bank.g_macro[0].u_macro.memory_q[%0d]", addr), data);
`endif

        addr += 1;
    end


    file = $fopen($sformatf("%s.aicore_0.l1.sb_0.mb_11.128b.texthex", _elf_file), "r");
    addr = '0;
    data = '0;
    while(!$feof(file)) begin
        $fscanf(file, "%h\n", data);
`ifdef TARGET_SF5A
        hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[0].u_sub_bank.g_mini_bank[11].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(addr, data);
`else
        uvm_hdl_deposit($sformatf("hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[0].u_sub_bank.g_mini_bank[11].u_mini_bank.g_macro[0].u_macro.memory_q[%0d]", addr), data);
`endif

        addr += 1;
    end


    file = $fopen($sformatf("%s.aicore_0.l1.sb_0.mb_12.128b.texthex", _elf_file), "r");
    addr = '0;
    data = '0;
    while(!$feof(file)) begin
        $fscanf(file, "%h\n", data);
`ifdef TARGET_SF5A
        hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[0].u_sub_bank.g_mini_bank[12].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(addr, data);
`else
        uvm_hdl_deposit($sformatf("hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[0].u_sub_bank.g_mini_bank[12].u_mini_bank.g_macro[0].u_macro.memory_q[%0d]", addr), data);
`endif

        addr += 1;
    end


    file = $fopen($sformatf("%s.aicore_0.l1.sb_0.mb_13.128b.texthex", _elf_file), "r");
    addr = '0;
    data = '0;
    while(!$feof(file)) begin
        $fscanf(file, "%h\n", data);
`ifdef TARGET_SF5A
        hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[0].u_sub_bank.g_mini_bank[13].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(addr, data);
`else
        uvm_hdl_deposit($sformatf("hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[0].u_sub_bank.g_mini_bank[13].u_mini_bank.g_macro[0].u_macro.memory_q[%0d]", addr), data);
`endif

        addr += 1;
    end


    file = $fopen($sformatf("%s.aicore_0.l1.sb_0.mb_14.128b.texthex", _elf_file), "r");
    addr = '0;
    data = '0;
    while(!$feof(file)) begin
        $fscanf(file, "%h\n", data);
`ifdef TARGET_SF5A
        hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[0].u_sub_bank.g_mini_bank[14].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(addr, data);
`else
        uvm_hdl_deposit($sformatf("hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[0].u_sub_bank.g_mini_bank[14].u_mini_bank.g_macro[0].u_macro.memory_q[%0d]", addr), data);
`endif

        addr += 1;
    end


    file = $fopen($sformatf("%s.aicore_0.l1.sb_0.mb_15.128b.texthex", _elf_file), "r");
    addr = '0;
    data = '0;
    while(!$feof(file)) begin
        $fscanf(file, "%h\n", data);
`ifdef TARGET_SF5A
        hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[0].u_sub_bank.g_mini_bank[15].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(addr, data);
`else
        uvm_hdl_deposit($sformatf("hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[0].u_sub_bank.g_mini_bank[15].u_mini_bank.g_macro[0].u_macro.memory_q[%0d]", addr), data);
`endif

        addr += 1;
    end


    file = $fopen($sformatf("%s.aicore_0.l1.sb_1.mb_0.128b.texthex", _elf_file), "r");
    addr = '0;
    data = '0;
    while(!$feof(file)) begin
        $fscanf(file, "%h\n", data);
`ifdef TARGET_SF5A
        hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[1].u_sub_bank.g_mini_bank[0].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(addr, data);
`else
        uvm_hdl_deposit($sformatf("hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[1].u_sub_bank.g_mini_bank[0].u_mini_bank.g_macro[0].u_macro.memory_q[%0d]", addr), data);
`endif

        addr += 1;
    end


    file = $fopen($sformatf("%s.aicore_0.l1.sb_1.mb_1.128b.texthex", _elf_file), "r");
    addr = '0;
    data = '0;
    while(!$feof(file)) begin
        $fscanf(file, "%h\n", data);
`ifdef TARGET_SF5A
        hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[1].u_sub_bank.g_mini_bank[1].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(addr, data);
`else
        uvm_hdl_deposit($sformatf("hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[1].u_sub_bank.g_mini_bank[1].u_mini_bank.g_macro[0].u_macro.memory_q[%0d]", addr), data);
`endif

        addr += 1;
    end


    file = $fopen($sformatf("%s.aicore_0.l1.sb_1.mb_2.128b.texthex", _elf_file), "r");
    addr = '0;
    data = '0;
    while(!$feof(file)) begin
        $fscanf(file, "%h\n", data);
`ifdef TARGET_SF5A
        hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[1].u_sub_bank.g_mini_bank[2].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(addr, data);
`else
        uvm_hdl_deposit($sformatf("hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[1].u_sub_bank.g_mini_bank[2].u_mini_bank.g_macro[0].u_macro.memory_q[%0d]", addr), data);
`endif

        addr += 1;
    end


    file = $fopen($sformatf("%s.aicore_0.l1.sb_1.mb_3.128b.texthex", _elf_file), "r");
    addr = '0;
    data = '0;
    while(!$feof(file)) begin
        $fscanf(file, "%h\n", data);
`ifdef TARGET_SF5A
        hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[1].u_sub_bank.g_mini_bank[3].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(addr, data);
`else
        uvm_hdl_deposit($sformatf("hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[1].u_sub_bank.g_mini_bank[3].u_mini_bank.g_macro[0].u_macro.memory_q[%0d]", addr), data);
`endif

        addr += 1;
    end


    file = $fopen($sformatf("%s.aicore_0.l1.sb_1.mb_4.128b.texthex", _elf_file), "r");
    addr = '0;
    data = '0;
    while(!$feof(file)) begin
        $fscanf(file, "%h\n", data);
`ifdef TARGET_SF5A
        hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[1].u_sub_bank.g_mini_bank[4].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(addr, data);
`else
        uvm_hdl_deposit($sformatf("hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[1].u_sub_bank.g_mini_bank[4].u_mini_bank.g_macro[0].u_macro.memory_q[%0d]", addr), data);
`endif

        addr += 1;
    end


    file = $fopen($sformatf("%s.aicore_0.l1.sb_1.mb_5.128b.texthex", _elf_file), "r");
    addr = '0;
    data = '0;
    while(!$feof(file)) begin
        $fscanf(file, "%h\n", data);
`ifdef TARGET_SF5A
        hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[1].u_sub_bank.g_mini_bank[5].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(addr, data);
`else
        uvm_hdl_deposit($sformatf("hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[1].u_sub_bank.g_mini_bank[5].u_mini_bank.g_macro[0].u_macro.memory_q[%0d]", addr), data);
`endif

        addr += 1;
    end


    file = $fopen($sformatf("%s.aicore_0.l1.sb_1.mb_6.128b.texthex", _elf_file), "r");
    addr = '0;
    data = '0;
    while(!$feof(file)) begin
        $fscanf(file, "%h\n", data);
`ifdef TARGET_SF5A
        hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[1].u_sub_bank.g_mini_bank[6].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(addr, data);
`else
        uvm_hdl_deposit($sformatf("hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[1].u_sub_bank.g_mini_bank[6].u_mini_bank.g_macro[0].u_macro.memory_q[%0d]", addr), data);
`endif

        addr += 1;
    end


    file = $fopen($sformatf("%s.aicore_0.l1.sb_1.mb_7.128b.texthex", _elf_file), "r");
    addr = '0;
    data = '0;
    while(!$feof(file)) begin
        $fscanf(file, "%h\n", data);
`ifdef TARGET_SF5A
        hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[1].u_sub_bank.g_mini_bank[7].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(addr, data);
`else
        uvm_hdl_deposit($sformatf("hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[1].u_sub_bank.g_mini_bank[7].u_mini_bank.g_macro[0].u_macro.memory_q[%0d]", addr), data);
`endif

        addr += 1;
    end


    file = $fopen($sformatf("%s.aicore_0.l1.sb_1.mb_8.128b.texthex", _elf_file), "r");
    addr = '0;
    data = '0;
    while(!$feof(file)) begin
        $fscanf(file, "%h\n", data);
`ifdef TARGET_SF5A
        hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[1].u_sub_bank.g_mini_bank[8].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(addr, data);
`else
        uvm_hdl_deposit($sformatf("hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[1].u_sub_bank.g_mini_bank[8].u_mini_bank.g_macro[0].u_macro.memory_q[%0d]", addr), data);
`endif

        addr += 1;
    end


    file = $fopen($sformatf("%s.aicore_0.l1.sb_1.mb_9.128b.texthex", _elf_file), "r");
    addr = '0;
    data = '0;
    while(!$feof(file)) begin
        $fscanf(file, "%h\n", data);
`ifdef TARGET_SF5A
        hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[1].u_sub_bank.g_mini_bank[9].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(addr, data);
`else
        uvm_hdl_deposit($sformatf("hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[1].u_sub_bank.g_mini_bank[9].u_mini_bank.g_macro[0].u_macro.memory_q[%0d]", addr), data);
`endif

        addr += 1;
    end


    file = $fopen($sformatf("%s.aicore_0.l1.sb_1.mb_10.128b.texthex", _elf_file), "r");
    addr = '0;
    data = '0;
    while(!$feof(file)) begin
        $fscanf(file, "%h\n", data);
`ifdef TARGET_SF5A
        hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[1].u_sub_bank.g_mini_bank[10].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(addr, data);
`else
        uvm_hdl_deposit($sformatf("hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[1].u_sub_bank.g_mini_bank[10].u_mini_bank.g_macro[0].u_macro.memory_q[%0d]", addr), data);
`endif

        addr += 1;
    end


    file = $fopen($sformatf("%s.aicore_0.l1.sb_1.mb_11.128b.texthex", _elf_file), "r");
    addr = '0;
    data = '0;
    while(!$feof(file)) begin
        $fscanf(file, "%h\n", data);
`ifdef TARGET_SF5A
        hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[1].u_sub_bank.g_mini_bank[11].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(addr, data);
`else
        uvm_hdl_deposit($sformatf("hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[1].u_sub_bank.g_mini_bank[11].u_mini_bank.g_macro[0].u_macro.memory_q[%0d]", addr), data);
`endif

        addr += 1;
    end


    file = $fopen($sformatf("%s.aicore_0.l1.sb_1.mb_12.128b.texthex", _elf_file), "r");
    addr = '0;
    data = '0;
    while(!$feof(file)) begin
        $fscanf(file, "%h\n", data);
`ifdef TARGET_SF5A
        hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[1].u_sub_bank.g_mini_bank[12].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(addr, data);
`else
        uvm_hdl_deposit($sformatf("hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[1].u_sub_bank.g_mini_bank[12].u_mini_bank.g_macro[0].u_macro.memory_q[%0d]", addr), data);
`endif

        addr += 1;
    end


    file = $fopen($sformatf("%s.aicore_0.l1.sb_1.mb_13.128b.texthex", _elf_file), "r");
    addr = '0;
    data = '0;
    while(!$feof(file)) begin
        $fscanf(file, "%h\n", data);
`ifdef TARGET_SF5A
        hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[1].u_sub_bank.g_mini_bank[13].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(addr, data);
`else
        uvm_hdl_deposit($sformatf("hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[1].u_sub_bank.g_mini_bank[13].u_mini_bank.g_macro[0].u_macro.memory_q[%0d]", addr), data);
`endif

        addr += 1;
    end


    file = $fopen($sformatf("%s.aicore_0.l1.sb_1.mb_14.128b.texthex", _elf_file), "r");
    addr = '0;
    data = '0;
    while(!$feof(file)) begin
        $fscanf(file, "%h\n", data);
`ifdef TARGET_SF5A
        hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[1].u_sub_bank.g_mini_bank[14].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(addr, data);
`else
        uvm_hdl_deposit($sformatf("hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[1].u_sub_bank.g_mini_bank[14].u_mini_bank.g_macro[0].u_macro.memory_q[%0d]", addr), data);
`endif

        addr += 1;
    end


    file = $fopen($sformatf("%s.aicore_0.l1.sb_1.mb_15.128b.texthex", _elf_file), "r");
    addr = '0;
    data = '0;
    while(!$feof(file)) begin
        $fscanf(file, "%h\n", data);
`ifdef TARGET_SF5A
        hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[1].u_sub_bank.g_mini_bank[15].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(addr, data);
`else
        uvm_hdl_deposit($sformatf("hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[1].u_sub_bank.g_mini_bank[15].u_mini_bank.g_macro[0].u_macro.memory_q[%0d]", addr), data);
`endif

        addr += 1;
    end


    file = $fopen($sformatf("%s.aicore_0.l1.sb_2.mb_0.128b.texthex", _elf_file), "r");
    addr = '0;
    data = '0;
    while(!$feof(file)) begin
        $fscanf(file, "%h\n", data);
`ifdef TARGET_SF5A
        hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[2].u_sub_bank.g_mini_bank[0].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(addr, data);
`else
        uvm_hdl_deposit($sformatf("hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[2].u_sub_bank.g_mini_bank[0].u_mini_bank.g_macro[0].u_macro.memory_q[%0d]", addr), data);
`endif

        addr += 1;
    end


    file = $fopen($sformatf("%s.aicore_0.l1.sb_2.mb_1.128b.texthex", _elf_file), "r");
    addr = '0;
    data = '0;
    while(!$feof(file)) begin
        $fscanf(file, "%h\n", data);
`ifdef TARGET_SF5A
        hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[2].u_sub_bank.g_mini_bank[1].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(addr, data);
`else
        uvm_hdl_deposit($sformatf("hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[2].u_sub_bank.g_mini_bank[1].u_mini_bank.g_macro[0].u_macro.memory_q[%0d]", addr), data);
`endif

        addr += 1;
    end


    file = $fopen($sformatf("%s.aicore_0.l1.sb_2.mb_2.128b.texthex", _elf_file), "r");
    addr = '0;
    data = '0;
    while(!$feof(file)) begin
        $fscanf(file, "%h\n", data);
`ifdef TARGET_SF5A
        hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[2].u_sub_bank.g_mini_bank[2].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(addr, data);
`else
        uvm_hdl_deposit($sformatf("hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[2].u_sub_bank.g_mini_bank[2].u_mini_bank.g_macro[0].u_macro.memory_q[%0d]", addr), data);
`endif

        addr += 1;
    end


    file = $fopen($sformatf("%s.aicore_0.l1.sb_2.mb_3.128b.texthex", _elf_file), "r");
    addr = '0;
    data = '0;
    while(!$feof(file)) begin
        $fscanf(file, "%h\n", data);
`ifdef TARGET_SF5A
        hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[2].u_sub_bank.g_mini_bank[3].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(addr, data);
`else
        uvm_hdl_deposit($sformatf("hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[2].u_sub_bank.g_mini_bank[3].u_mini_bank.g_macro[0].u_macro.memory_q[%0d]", addr), data);
`endif

        addr += 1;
    end


    file = $fopen($sformatf("%s.aicore_0.l1.sb_2.mb_4.128b.texthex", _elf_file), "r");
    addr = '0;
    data = '0;
    while(!$feof(file)) begin
        $fscanf(file, "%h\n", data);
`ifdef TARGET_SF5A
        hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[2].u_sub_bank.g_mini_bank[4].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(addr, data);
`else
        uvm_hdl_deposit($sformatf("hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[2].u_sub_bank.g_mini_bank[4].u_mini_bank.g_macro[0].u_macro.memory_q[%0d]", addr), data);
`endif

        addr += 1;
    end


    file = $fopen($sformatf("%s.aicore_0.l1.sb_2.mb_5.128b.texthex", _elf_file), "r");
    addr = '0;
    data = '0;
    while(!$feof(file)) begin
        $fscanf(file, "%h\n", data);
`ifdef TARGET_SF5A
        hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[2].u_sub_bank.g_mini_bank[5].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(addr, data);
`else
        uvm_hdl_deposit($sformatf("hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[2].u_sub_bank.g_mini_bank[5].u_mini_bank.g_macro[0].u_macro.memory_q[%0d]", addr), data);
`endif

        addr += 1;
    end


    file = $fopen($sformatf("%s.aicore_0.l1.sb_2.mb_6.128b.texthex", _elf_file), "r");
    addr = '0;
    data = '0;
    while(!$feof(file)) begin
        $fscanf(file, "%h\n", data);
`ifdef TARGET_SF5A
        hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[2].u_sub_bank.g_mini_bank[6].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(addr, data);
`else
        uvm_hdl_deposit($sformatf("hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[2].u_sub_bank.g_mini_bank[6].u_mini_bank.g_macro[0].u_macro.memory_q[%0d]", addr), data);
`endif

        addr += 1;
    end


    file = $fopen($sformatf("%s.aicore_0.l1.sb_2.mb_7.128b.texthex", _elf_file), "r");
    addr = '0;
    data = '0;
    while(!$feof(file)) begin
        $fscanf(file, "%h\n", data);
`ifdef TARGET_SF5A
        hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[2].u_sub_bank.g_mini_bank[7].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(addr, data);
`else
        uvm_hdl_deposit($sformatf("hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[2].u_sub_bank.g_mini_bank[7].u_mini_bank.g_macro[0].u_macro.memory_q[%0d]", addr), data);
`endif

        addr += 1;
    end


    file = $fopen($sformatf("%s.aicore_0.l1.sb_2.mb_8.128b.texthex", _elf_file), "r");
    addr = '0;
    data = '0;
    while(!$feof(file)) begin
        $fscanf(file, "%h\n", data);
`ifdef TARGET_SF5A
        hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[2].u_sub_bank.g_mini_bank[8].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(addr, data);
`else
        uvm_hdl_deposit($sformatf("hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[2].u_sub_bank.g_mini_bank[8].u_mini_bank.g_macro[0].u_macro.memory_q[%0d]", addr), data);
`endif

        addr += 1;
    end


    file = $fopen($sformatf("%s.aicore_0.l1.sb_2.mb_9.128b.texthex", _elf_file), "r");
    addr = '0;
    data = '0;
    while(!$feof(file)) begin
        $fscanf(file, "%h\n", data);
`ifdef TARGET_SF5A
        hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[2].u_sub_bank.g_mini_bank[9].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(addr, data);
`else
        uvm_hdl_deposit($sformatf("hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[2].u_sub_bank.g_mini_bank[9].u_mini_bank.g_macro[0].u_macro.memory_q[%0d]", addr), data);
`endif

        addr += 1;
    end


    file = $fopen($sformatf("%s.aicore_0.l1.sb_2.mb_10.128b.texthex", _elf_file), "r");
    addr = '0;
    data = '0;
    while(!$feof(file)) begin
        $fscanf(file, "%h\n", data);
`ifdef TARGET_SF5A
        hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[2].u_sub_bank.g_mini_bank[10].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(addr, data);
`else
        uvm_hdl_deposit($sformatf("hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[2].u_sub_bank.g_mini_bank[10].u_mini_bank.g_macro[0].u_macro.memory_q[%0d]", addr), data);
`endif

        addr += 1;
    end


    file = $fopen($sformatf("%s.aicore_0.l1.sb_2.mb_11.128b.texthex", _elf_file), "r");
    addr = '0;
    data = '0;
    while(!$feof(file)) begin
        $fscanf(file, "%h\n", data);
`ifdef TARGET_SF5A
        hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[2].u_sub_bank.g_mini_bank[11].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(addr, data);
`else
        uvm_hdl_deposit($sformatf("hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[2].u_sub_bank.g_mini_bank[11].u_mini_bank.g_macro[0].u_macro.memory_q[%0d]", addr), data);
`endif

        addr += 1;
    end


    file = $fopen($sformatf("%s.aicore_0.l1.sb_2.mb_12.128b.texthex", _elf_file), "r");
    addr = '0;
    data = '0;
    while(!$feof(file)) begin
        $fscanf(file, "%h\n", data);
`ifdef TARGET_SF5A
        hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[2].u_sub_bank.g_mini_bank[12].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(addr, data);
`else
        uvm_hdl_deposit($sformatf("hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[2].u_sub_bank.g_mini_bank[12].u_mini_bank.g_macro[0].u_macro.memory_q[%0d]", addr), data);
`endif

        addr += 1;
    end


    file = $fopen($sformatf("%s.aicore_0.l1.sb_2.mb_13.128b.texthex", _elf_file), "r");
    addr = '0;
    data = '0;
    while(!$feof(file)) begin
        $fscanf(file, "%h\n", data);
`ifdef TARGET_SF5A
        hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[2].u_sub_bank.g_mini_bank[13].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(addr, data);
`else
        uvm_hdl_deposit($sformatf("hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[2].u_sub_bank.g_mini_bank[13].u_mini_bank.g_macro[0].u_macro.memory_q[%0d]", addr), data);
`endif

        addr += 1;
    end


    file = $fopen($sformatf("%s.aicore_0.l1.sb_2.mb_14.128b.texthex", _elf_file), "r");
    addr = '0;
    data = '0;
    while(!$feof(file)) begin
        $fscanf(file, "%h\n", data);
`ifdef TARGET_SF5A
        hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[2].u_sub_bank.g_mini_bank[14].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(addr, data);
`else
        uvm_hdl_deposit($sformatf("hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[2].u_sub_bank.g_mini_bank[14].u_mini_bank.g_macro[0].u_macro.memory_q[%0d]", addr), data);
`endif

        addr += 1;
    end


    file = $fopen($sformatf("%s.aicore_0.l1.sb_2.mb_15.128b.texthex", _elf_file), "r");
    addr = '0;
    data = '0;
    while(!$feof(file)) begin
        $fscanf(file, "%h\n", data);
`ifdef TARGET_SF5A
        hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[2].u_sub_bank.g_mini_bank[15].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(addr, data);
`else
        uvm_hdl_deposit($sformatf("hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[2].u_sub_bank.g_mini_bank[15].u_mini_bank.g_macro[0].u_macro.memory_q[%0d]", addr), data);
`endif

        addr += 1;
    end


    file = $fopen($sformatf("%s.aicore_0.l1.sb_3.mb_0.128b.texthex", _elf_file), "r");
    addr = '0;
    data = '0;
    while(!$feof(file)) begin
        $fscanf(file, "%h\n", data);
`ifdef TARGET_SF5A
        hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[3].u_sub_bank.g_mini_bank[0].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(addr, data);
`else
        uvm_hdl_deposit($sformatf("hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[3].u_sub_bank.g_mini_bank[0].u_mini_bank.g_macro[0].u_macro.memory_q[%0d]", addr), data);
`endif

        addr += 1;
    end


    file = $fopen($sformatf("%s.aicore_0.l1.sb_3.mb_1.128b.texthex", _elf_file), "r");
    addr = '0;
    data = '0;
    while(!$feof(file)) begin
        $fscanf(file, "%h\n", data);
`ifdef TARGET_SF5A
        hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[3].u_sub_bank.g_mini_bank[1].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(addr, data);
`else
        uvm_hdl_deposit($sformatf("hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[3].u_sub_bank.g_mini_bank[1].u_mini_bank.g_macro[0].u_macro.memory_q[%0d]", addr), data);
`endif

        addr += 1;
    end


    file = $fopen($sformatf("%s.aicore_0.l1.sb_3.mb_2.128b.texthex", _elf_file), "r");
    addr = '0;
    data = '0;
    while(!$feof(file)) begin
        $fscanf(file, "%h\n", data);
`ifdef TARGET_SF5A
        hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[3].u_sub_bank.g_mini_bank[2].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(addr, data);
`else
        uvm_hdl_deposit($sformatf("hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[3].u_sub_bank.g_mini_bank[2].u_mini_bank.g_macro[0].u_macro.memory_q[%0d]", addr), data);
`endif

        addr += 1;
    end


    file = $fopen($sformatf("%s.aicore_0.l1.sb_3.mb_3.128b.texthex", _elf_file), "r");
    addr = '0;
    data = '0;
    while(!$feof(file)) begin
        $fscanf(file, "%h\n", data);
`ifdef TARGET_SF5A
        hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[3].u_sub_bank.g_mini_bank[3].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(addr, data);
`else
        uvm_hdl_deposit($sformatf("hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[3].u_sub_bank.g_mini_bank[3].u_mini_bank.g_macro[0].u_macro.memory_q[%0d]", addr), data);
`endif

        addr += 1;
    end


    file = $fopen($sformatf("%s.aicore_0.l1.sb_3.mb_4.128b.texthex", _elf_file), "r");
    addr = '0;
    data = '0;
    while(!$feof(file)) begin
        $fscanf(file, "%h\n", data);
`ifdef TARGET_SF5A
        hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[3].u_sub_bank.g_mini_bank[4].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(addr, data);
`else
        uvm_hdl_deposit($sformatf("hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[3].u_sub_bank.g_mini_bank[4].u_mini_bank.g_macro[0].u_macro.memory_q[%0d]", addr), data);
`endif

        addr += 1;
    end


    file = $fopen($sformatf("%s.aicore_0.l1.sb_3.mb_5.128b.texthex", _elf_file), "r");
    addr = '0;
    data = '0;
    while(!$feof(file)) begin
        $fscanf(file, "%h\n", data);
`ifdef TARGET_SF5A
        hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[3].u_sub_bank.g_mini_bank[5].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(addr, data);
`else
        uvm_hdl_deposit($sformatf("hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[3].u_sub_bank.g_mini_bank[5].u_mini_bank.g_macro[0].u_macro.memory_q[%0d]", addr), data);
`endif

        addr += 1;
    end


    file = $fopen($sformatf("%s.aicore_0.l1.sb_3.mb_6.128b.texthex", _elf_file), "r");
    addr = '0;
    data = '0;
    while(!$feof(file)) begin
        $fscanf(file, "%h\n", data);
`ifdef TARGET_SF5A
        hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[3].u_sub_bank.g_mini_bank[6].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(addr, data);
`else
        uvm_hdl_deposit($sformatf("hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[3].u_sub_bank.g_mini_bank[6].u_mini_bank.g_macro[0].u_macro.memory_q[%0d]", addr), data);
`endif

        addr += 1;
    end


    file = $fopen($sformatf("%s.aicore_0.l1.sb_3.mb_7.128b.texthex", _elf_file), "r");
    addr = '0;
    data = '0;
    while(!$feof(file)) begin
        $fscanf(file, "%h\n", data);
`ifdef TARGET_SF5A
        hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[3].u_sub_bank.g_mini_bank[7].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(addr, data);
`else
        uvm_hdl_deposit($sformatf("hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[3].u_sub_bank.g_mini_bank[7].u_mini_bank.g_macro[0].u_macro.memory_q[%0d]", addr), data);
`endif

        addr += 1;
    end


    file = $fopen($sformatf("%s.aicore_0.l1.sb_3.mb_8.128b.texthex", _elf_file), "r");
    addr = '0;
    data = '0;
    while(!$feof(file)) begin
        $fscanf(file, "%h\n", data);
`ifdef TARGET_SF5A
        hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[3].u_sub_bank.g_mini_bank[8].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(addr, data);
`else
        uvm_hdl_deposit($sformatf("hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[3].u_sub_bank.g_mini_bank[8].u_mini_bank.g_macro[0].u_macro.memory_q[%0d]", addr), data);
`endif

        addr += 1;
    end


    file = $fopen($sformatf("%s.aicore_0.l1.sb_3.mb_9.128b.texthex", _elf_file), "r");
    addr = '0;
    data = '0;
    while(!$feof(file)) begin
        $fscanf(file, "%h\n", data);
`ifdef TARGET_SF5A
        hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[3].u_sub_bank.g_mini_bank[9].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(addr, data);
`else
        uvm_hdl_deposit($sformatf("hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[3].u_sub_bank.g_mini_bank[9].u_mini_bank.g_macro[0].u_macro.memory_q[%0d]", addr), data);
`endif

        addr += 1;
    end


    file = $fopen($sformatf("%s.aicore_0.l1.sb_3.mb_10.128b.texthex", _elf_file), "r");
    addr = '0;
    data = '0;
    while(!$feof(file)) begin
        $fscanf(file, "%h\n", data);
`ifdef TARGET_SF5A
        hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[3].u_sub_bank.g_mini_bank[10].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(addr, data);
`else
        uvm_hdl_deposit($sformatf("hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[3].u_sub_bank.g_mini_bank[10].u_mini_bank.g_macro[0].u_macro.memory_q[%0d]", addr), data);
`endif

        addr += 1;
    end


    file = $fopen($sformatf("%s.aicore_0.l1.sb_3.mb_11.128b.texthex", _elf_file), "r");
    addr = '0;
    data = '0;
    while(!$feof(file)) begin
        $fscanf(file, "%h\n", data);
`ifdef TARGET_SF5A
        hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[3].u_sub_bank.g_mini_bank[11].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(addr, data);
`else
        uvm_hdl_deposit($sformatf("hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[3].u_sub_bank.g_mini_bank[11].u_mini_bank.g_macro[0].u_macro.memory_q[%0d]", addr), data);
`endif

        addr += 1;
    end


    file = $fopen($sformatf("%s.aicore_0.l1.sb_3.mb_12.128b.texthex", _elf_file), "r");
    addr = '0;
    data = '0;
    while(!$feof(file)) begin
        $fscanf(file, "%h\n", data);
`ifdef TARGET_SF5A
        hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[3].u_sub_bank.g_mini_bank[12].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(addr, data);
`else
        uvm_hdl_deposit($sformatf("hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[3].u_sub_bank.g_mini_bank[12].u_mini_bank.g_macro[0].u_macro.memory_q[%0d]", addr), data);
`endif

        addr += 1;
    end


    file = $fopen($sformatf("%s.aicore_0.l1.sb_3.mb_13.128b.texthex", _elf_file), "r");
    addr = '0;
    data = '0;
    while(!$feof(file)) begin
        $fscanf(file, "%h\n", data);
`ifdef TARGET_SF5A
        hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[3].u_sub_bank.g_mini_bank[13].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(addr, data);
`else
        uvm_hdl_deposit($sformatf("hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[3].u_sub_bank.g_mini_bank[13].u_mini_bank.g_macro[0].u_macro.memory_q[%0d]", addr), data);
`endif

        addr += 1;
    end


    file = $fopen($sformatf("%s.aicore_0.l1.sb_3.mb_14.128b.texthex", _elf_file), "r");
    addr = '0;
    data = '0;
    while(!$feof(file)) begin
        $fscanf(file, "%h\n", data);
`ifdef TARGET_SF5A
        hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[3].u_sub_bank.g_mini_bank[14].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(addr, data);
`else
        uvm_hdl_deposit($sformatf("hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[3].u_sub_bank.g_mini_bank[14].u_mini_bank.g_macro[0].u_macro.memory_q[%0d]", addr), data);
`endif

        addr += 1;
    end


    file = $fopen($sformatf("%s.aicore_0.l1.sb_3.mb_15.128b.texthex", _elf_file), "r");
    addr = '0;
    data = '0;
    while(!$feof(file)) begin
        $fscanf(file, "%h\n", data);
`ifdef TARGET_SF5A
        hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[3].u_sub_bank.g_mini_bank[15].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(addr, data);
`else
        uvm_hdl_deposit($sformatf("hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[3].u_sub_bank.g_mini_bank[15].u_mini_bank.g_macro[0].u_macro.memory_q[%0d]", addr), data);
`endif

        addr += 1;
    end


  endtask

