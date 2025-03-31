    //TODO: change these functions to some memory_preloading_pkg compatible ones, following: https://git.axelera.ai/prod/europa/-/merge_requests/1446
    `define AIC_SPM_PATH hdl_top.dut.u_ai_core.u_aic_infra_p.u_aic_infra.u_aic_spm.u_spm_mem

    function logic [71:0] add_spm_ecc (logic [63:0] data_wo_ecc);
      logic [71:0] data_w_ecc;

      data_w_ecc = 72'(data_wo_ecc);

      data_w_ecc[64] = 1'b0 ^ ^(data_w_ecc & 72'h00B9000000001FFFFF);
      data_w_ecc[65] = 1'b0 ^ ^(data_w_ecc & 72'h005E00000FFFE0003F);
      data_w_ecc[66] = 1'b0 ^ ^(data_w_ecc & 72'h0067003FF003E007C1);
      data_w_ecc[67] = 1'b0 ^ ^(data_w_ecc & 72'h00CD0FC0F03C207842);
      data_w_ecc[68] = 1'b0 ^ ^(data_w_ecc & 72'h00B671C711C4438884);
      data_w_ecc[69] = 1'b0 ^ ^(data_w_ecc & 72'h00B5B65926488C9108);
      data_w_ecc[70] = 1'b0 ^ ^(data_w_ecc & 72'h00CBDAAA4A91152210);
      data_w_ecc[71] = 1'b0 ^ ^(data_w_ecc & 72'h007AED348D221A4420);

      return data_w_ecc;
    endfunction


  task preload_spm_single_value(logic[63:0] _value = '0);
   logic [71:0] data_w_ecc;
   data_w_ecc = add_spm_ecc(_value);
   for (int i = 0; i < 8192; i++) begin
`ifdef TARGET_SF5A
    `AIC_SPM_PATH.g_bank_inst[0].u_spm_mem_bank.g_sub_bank_inst[0].u_spm_mem_sub_bank.g_mini_bank_inst[0].u_spm_mem_mini_bank.g_sram_inst[0].u_tc_sram.gen_macro.u_macro.u_mem.write_mem(i, data_w_ecc);
    `AIC_SPM_PATH.g_bank_inst[0].u_spm_mem_bank.g_sub_bank_inst[0].u_spm_mem_sub_bank.g_mini_bank_inst[0].u_spm_mem_mini_bank.g_sram_inst[1].u_tc_sram.gen_macro.u_macro.u_mem.write_mem(i, data_w_ecc);
    `AIC_SPM_PATH.g_bank_inst[0].u_spm_mem_bank.g_sub_bank_inst[0].u_spm_mem_sub_bank.g_mini_bank_inst[1].u_spm_mem_mini_bank.g_sram_inst[0].u_tc_sram.gen_macro.u_macro.u_mem.write_mem(i, data_w_ecc);
    `AIC_SPM_PATH.g_bank_inst[0].u_spm_mem_bank.g_sub_bank_inst[0].u_spm_mem_sub_bank.g_mini_bank_inst[1].u_spm_mem_mini_bank.g_sram_inst[1].u_tc_sram.gen_macro.u_macro.u_mem.write_mem(i, data_w_ecc);
    `AIC_SPM_PATH.g_bank_inst[1].u_spm_mem_bank.g_sub_bank_inst[0].u_spm_mem_sub_bank.g_mini_bank_inst[0].u_spm_mem_mini_bank.g_sram_inst[0].u_tc_sram.gen_macro.u_macro.u_mem.write_mem(i, data_w_ecc);
    `AIC_SPM_PATH.g_bank_inst[1].u_spm_mem_bank.g_sub_bank_inst[0].u_spm_mem_sub_bank.g_mini_bank_inst[0].u_spm_mem_mini_bank.g_sram_inst[1].u_tc_sram.gen_macro.u_macro.u_mem.write_mem(i, data_w_ecc);
    `AIC_SPM_PATH.g_bank_inst[1].u_spm_mem_bank.g_sub_bank_inst[0].u_spm_mem_sub_bank.g_mini_bank_inst[1].u_spm_mem_mini_bank.g_sram_inst[0].u_tc_sram.gen_macro.u_macro.u_mem.write_mem(i, data_w_ecc);
    `AIC_SPM_PATH.g_bank_inst[1].u_spm_mem_bank.g_sub_bank_inst[0].u_spm_mem_sub_bank.g_mini_bank_inst[1].u_spm_mem_mini_bank.g_sram_inst[1].u_tc_sram.gen_macro.u_macro.u_mem.write_mem(i, data_w_ecc);
`else
    for (int nb = 0; nb < 2; nb++) begin
        for (int nmb = 0; nmb < 2; nmb++) begin
            for (int ninst = 0; ninst < 2; ninst++) begin
                uvm_hdl_deposit($sformatf("hdl_top.dut.u_ai_core.u_aic_infra_p.u_aic_infra.u_aic_spm.u_spm_mem.g_bank_inst[%0d].u_spm_mem_bank.g_sub_bank_inst[0].u_spm_mem_sub_bank.g_mini_bank_inst[%0d].u_spm_mem_mini_bank.g_sram_inst[%0d].u_tc_sram.memory_q[%0d]", nb, nmb, ninst, i), data_w_ecc);
            end
        end
    end
`endif
   end
  endtask

  task preload_spm_file(string _elf_file);
    integer file;
    reg [63:0] data;
    int addr;
    logic [71:0] data_w_ecc;

    file = $fopen($sformatf("%s.aicore_0.spm.bk_0.sb_0.mb_0.inst_0.64b.texthex", _elf_file), "r");
    addr = '0;
    data = '0;
    while(!$feof(file)) begin
        $fscanf(file, "%h\n", data);
        data_w_ecc = add_spm_ecc(data);
`ifdef TARGET_SF5A
        `AIC_SPM_PATH.g_bank_inst[0].u_spm_mem_bank.g_sub_bank_inst[0].u_spm_mem_sub_bank.g_mini_bank_inst[0].u_spm_mem_mini_bank.g_sram_inst[0].u_tc_sram.gen_macro.u_macro.u_mem.write_mem(addr, data_w_ecc);
`else
        uvm_hdl_deposit($sformatf("hdl_top.dut.u_ai_core.u_aic_infra_p.u_aic_infra.u_aic_spm.u_spm_mem.g_bank_inst[0].u_spm_mem_bank.g_sub_bank_inst[0].u_spm_mem_sub_bank.g_mini_bank_inst[0].u_spm_mem_mini_bank.g_sram_inst[0].u_tc_sram.memory_q[%0d]", addr), data_w_ecc);
`endif
        addr += 1;
    end

    file = $fopen($sformatf("%s.aicore_0.spm.bk_0.sb_0.mb_0.inst_1.64b.texthex", _elf_file), "r");
    addr = '0;
    data = '0;
    while(!$feof(file)) begin
        $fscanf(file, "%h\n", data);
        data_w_ecc = add_spm_ecc(data);
`ifdef TARGET_SF5A
        `AIC_SPM_PATH.g_bank_inst[0].u_spm_mem_bank.g_sub_bank_inst[0].u_spm_mem_sub_bank.g_mini_bank_inst[0].u_spm_mem_mini_bank.g_sram_inst[1].u_tc_sram.gen_macro.u_macro.u_mem.write_mem(addr, data_w_ecc);
`else
        uvm_hdl_deposit($sformatf("hdl_top.dut.u_ai_core.u_aic_infra_p.u_aic_infra.u_aic_spm.u_spm_mem.g_bank_inst[0].u_spm_mem_bank.g_sub_bank_inst[0].u_spm_mem_sub_bank.g_mini_bank_inst[0].u_spm_mem_mini_bank.g_sram_inst[1].u_tc_sram.memory_q[%0d]", addr), data_w_ecc);
`endif
        addr += 1;
    end

    file = $fopen($sformatf("%s.aicore_0.spm.bk_0.sb_0.mb_1.inst_0.64b.texthex", _elf_file), "r");
    addr = '0;
    data = '0;
    while(!$feof(file)) begin
        $fscanf(file, "%h\n", data);
        data_w_ecc = add_spm_ecc(data);
`ifdef TARGET_SF5A
        `AIC_SPM_PATH.g_bank_inst[0].u_spm_mem_bank.g_sub_bank_inst[0].u_spm_mem_sub_bank.g_mini_bank_inst[1].u_spm_mem_mini_bank.g_sram_inst[0].u_tc_sram.gen_macro.u_macro.u_mem.write_mem(addr, data_w_ecc);
`else
        uvm_hdl_deposit($sformatf("hdl_top.dut.u_ai_core.u_aic_infra_p.u_aic_infra.u_aic_spm.u_spm_mem.g_bank_inst[0].u_spm_mem_bank.g_sub_bank_inst[0].u_spm_mem_sub_bank.g_mini_bank_inst[1].u_spm_mem_mini_bank.g_sram_inst[0].u_tc_sram.memory_q[%0d]", addr), data_w_ecc);
`endif
        addr += 1;
    end


    file = $fopen($sformatf("%s.aicore_0.spm.bk_0.sb_0.mb_1.inst_1.64b.texthex", _elf_file), "r");
    addr = '0;
    data = '0;
    while(!$feof(file)) begin
        $fscanf(file, "%h\n", data);
        data_w_ecc = add_spm_ecc(data);
`ifdef TARGET_SF5A
        `AIC_SPM_PATH.g_bank_inst[0].u_spm_mem_bank.g_sub_bank_inst[0].u_spm_mem_sub_bank.g_mini_bank_inst[1].u_spm_mem_mini_bank.g_sram_inst[1].u_tc_sram.gen_macro.u_macro.u_mem.write_mem(addr, data_w_ecc);
`else
        uvm_hdl_deposit($sformatf("hdl_top.dut.u_ai_core.u_aic_infra_p.u_aic_infra.u_aic_spm.u_spm_mem.g_bank_inst[0].u_spm_mem_bank.g_sub_bank_inst[0].u_spm_mem_sub_bank.g_mini_bank_inst[1].u_spm_mem_mini_bank.g_sram_inst[1].u_tc_sram.memory_q[%0d]", addr), data_w_ecc);
`endif
        addr += 1;
    end


    file = $fopen($sformatf("%s.aicore_0.spm.bk_1.sb_0.mb_0.inst_0.64b.texthex", _elf_file), "r");
    addr = '0;
    data = '0;
    while(!$feof(file)) begin
        $fscanf(file, "%h\n", data);
        data_w_ecc = add_spm_ecc(data);
`ifdef TARGET_SF5A
        `AIC_SPM_PATH.g_bank_inst[1].u_spm_mem_bank.g_sub_bank_inst[0].u_spm_mem_sub_bank.g_mini_bank_inst[0].u_spm_mem_mini_bank.g_sram_inst[0].u_tc_sram.gen_macro.u_macro.u_mem.write_mem(addr, data_w_ecc);
`else
        uvm_hdl_deposit($sformatf("hdl_top.dut.u_ai_core.u_aic_infra_p.u_aic_infra.u_aic_spm.u_spm_mem.g_bank_inst[1].u_spm_mem_bank.g_sub_bank_inst[0].u_spm_mem_sub_bank.g_mini_bank_inst[0].u_spm_mem_mini_bank.g_sram_inst[0].u_tc_sram.memory_q[%0d]", addr), data_w_ecc);
`endif
       addr += 1;
    end

    file = $fopen($sformatf("%s.aicore_0.spm.bk_1.sb_0.mb_0.inst_1.64b.texthex", _elf_file), "r");
    addr = '0;
    data = '0;
    while(!$feof(file)) begin
        $fscanf(file, "%h\n", data);
        data_w_ecc = add_spm_ecc(data);
`ifdef TARGET_SF5A
        `AIC_SPM_PATH.g_bank_inst[1].u_spm_mem_bank.g_sub_bank_inst[0].u_spm_mem_sub_bank.g_mini_bank_inst[0].u_spm_mem_mini_bank.g_sram_inst[1].u_tc_sram.gen_macro.u_macro.u_mem.write_mem(addr, data_w_ecc);
`else
        uvm_hdl_deposit($sformatf("hdl_top.dut.u_ai_core.u_aic_infra_p.u_aic_infra.u_aic_spm.u_spm_mem.g_bank_inst[1].u_spm_mem_bank.g_sub_bank_inst[0].u_spm_mem_sub_bank.g_mini_bank_inst[0].u_spm_mem_mini_bank.g_sram_inst[1].u_tc_sram.memory_q[%0d]", addr), data_w_ecc);
`endif
        addr += 1;
    end

    file = $fopen($sformatf("%s.aicore_0.spm.bk_1.sb_0.mb_1.inst_0.64b.texthex", _elf_file), "r");
    addr = '0;
    data = '0;
    while(!$feof(file)) begin
        $fscanf(file, "%h\n", data);
        data_w_ecc = add_spm_ecc(data);
`ifdef TARGET_SF5A
        `AIC_SPM_PATH.g_bank_inst[1].u_spm_mem_bank.g_sub_bank_inst[0].u_spm_mem_sub_bank.g_mini_bank_inst[1].u_spm_mem_mini_bank.g_sram_inst[0].u_tc_sram.gen_macro.u_macro.u_mem.write_mem(addr, data_w_ecc);
`else
        uvm_hdl_deposit($sformatf("hdl_top.dut.u_ai_core.u_aic_infra_p.u_aic_infra.u_aic_spm.u_spm_mem.g_bank_inst[1].u_spm_mem_bank.g_sub_bank_inst[0].u_spm_mem_sub_bank.g_mini_bank_inst[1].u_spm_mem_mini_bank.g_sram_inst[0].u_tc_sram.memory_q[%0d]", addr), data_w_ecc);
`endif
        addr += 1;
    end


    file = $fopen($sformatf("%s.aicore_0.spm.bk_1.sb_0.mb_1.inst_1.64b.texthex", _elf_file), "r");
    addr = '0;
    data = '0;
    while(!$feof(file)) begin
        $fscanf(file, "%h\n", data);
        data_w_ecc = add_spm_ecc(data);
`ifdef TARGET_SF5A
        `AIC_SPM_PATH.g_bank_inst[1].u_spm_mem_bank.g_sub_bank_inst[0].u_spm_mem_sub_bank.g_mini_bank_inst[1].u_spm_mem_mini_bank.g_sram_inst[1].u_tc_sram.gen_macro.u_macro.u_mem.write_mem(addr, data_w_ecc);
`else
        uvm_hdl_deposit($sformatf("hdl_top.dut.u_ai_core.u_aic_infra_p.u_aic_infra.u_aic_spm.u_spm_mem.g_bank_inst[1].u_spm_mem_bank.g_sub_bank_inst[0].u_spm_mem_sub_bank.g_mini_bank_inst[1].u_spm_mem_mini_bank.g_sram_inst[1].u_tc_sram.memory_q[%0d]", addr), data_w_ecc);
`endif
        addr += 1;
    end

  endtask
