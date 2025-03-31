
import sys
import random
import os

def ensure_directory_exists(directory):
    if not os.path.exists(directory):
        os.makedirs(directory)
        print(f"Directory '{directory}' created.")
    else:
        print(f"Directory '{directory}' already exists.")

def ensure_file_exists(file_path):
    if not os.path.exists(file_path):
        with open(file_path, 'w') as file:
            print(f"File '{file_path}' created.")
    else:
        print(f"File '{file_path}' already exists.")


#configs part
configs = []

config_sys = {
    "spm_axi_data_width" : 64,
    "spm_axi_strb_width" : 8,
    "spm_axi_addr_width" : 40,
    "spm_axi_id_width" : 4,
    "spm_axi_atop_width" : 6,
    "spm_mem_size_kb" : 8192,
    "spm_mem_macro_depth_k" : 8,
    "spm_nb_banks" : 4,
    "spm_nb_sub_banks" : 4,
    "spm_nb_mini_banks" : 4,
    "spm_nb_srams_per_mini_bank" : 2,
    "spm_nb_req_pipeline" : 3,
    "spm_nb_rsp_pipeline" : 3,
    "ecc_protection_en" : 1
    }

config_pve = {
    "spm_axi_data_width" : 64,
    "spm_axi_strb_width" : 8,
    "spm_axi_addr_width" : 40,
    "spm_axi_id_width" : 4,
    "spm_axi_atop_width" : 4,
    "spm_mem_size_kb" : 256,
    "spm_mem_macro_depth_k" : 2,
    "spm_nb_banks" : 2,
    "spm_nb_sub_banks" : 2,
    "spm_nb_mini_banks" : 2,
    "spm_nb_srams_per_mini_bank" : 2,
    "spm_nb_req_pipeline" : 3,
    "spm_nb_rsp_pipeline" : 3,
    "ecc_protection_en" : 1
    }

config_aicore = {
    "spm_axi_data_width" : 64,
    "spm_axi_strb_width" : 8,
    "spm_axi_addr_width" : 40,
    "spm_axi_id_width" : 9,
    "spm_axi_atop_width" : 9,
    "spm_mem_size_kb" : 512,
    "spm_mem_macro_depth_k" : 8,
    "spm_nb_banks" : 2,
    "spm_nb_sub_banks" : 1,
    "spm_nb_mini_banks" : 2,
    "spm_nb_srams_per_mini_bank" : 2,
    "spm_nb_req_pipeline" : 1,
    "spm_nb_rsp_pipeline" : 1,
    "ecc_protection_en" : 1
    }

configs = [config_pve, config_aicore, config_sys]

config = random.choice(configs)


backdoor_contents = ""
preload_contents = ""




#loop to generate the backdoor access
for nb in range(config["spm_nb_banks"]):
    for nsb in range(config["spm_nb_sub_banks"]):
        for nmb in range(config["spm_nb_mini_banks"]):
            for nsr in range(config["spm_nb_srams_per_mini_bank"]):
                backdoor_contents += f"""
        ecc_write_completed_ev.wait_trigger();
        ecc_write_completed_ev.reset();
        bit1_to_swap = $urandom_range(spm_config.spm_axi_data_width - 1, 0);
        if(ecc_2b_error) begin
            bit2_to_swap = $urandom_range(spm_config.spm_axi_data_width - 1, 0);
            while(bit2_to_swap == bit1_to_swap) begin
                bit2_to_swap = $urandom_range(spm_config.spm_axi_data_width - 1, 0);
            end
        end
        $display($sformatf("ECC TESTCASE: position bit swapped --- bit1 pos: %0d, bit2 pos: %0d", bit1_to_swap, bit2_to_swap));
        i_spm_dut.u_spm_mem.g_bank_inst[{nb}].u_spm_mem_bank.g_sub_bank_inst[{nsb}].u_spm_mem_sub_bank.g_mini_bank_inst[{nmb}].u_spm_mem_mini_bank.g_sram_inst[{nsr}].u_tc_sram.gen_macro.u_macro.u_mem.read_mem(line_address, ecc_data);
        $display($sformatf("ECC TESTCASE: data before manipulation: %0x", ecc_data));
        $display($sformatf("ECC TESTCASE: manipulation on bank: {nb}, subbank {nsb}, minibank {nmb}, nsram: {nsr}"));
        ecc_data[bit1_to_swap] = ~ecc_data[bit1_to_swap];
        if(ecc_2b_error) begin
            ecc_data[bit2_to_swap] = ~ecc_data[bit2_to_swap];
        end
        i_spm_dut.u_spm_mem.g_bank_inst[{nb}].u_spm_mem_bank.g_sub_bank_inst[{nsb}].u_spm_mem_sub_bank.g_mini_bank_inst[{nmb}].u_spm_mem_mini_bank.g_sram_inst[{nsr}].u_tc_sram.gen_macro.u_macro.u_mem.write_mem(line_address, ecc_data);
        $display($sformatf("ECC TESTCASE: data after manipulation: %0x", ecc_data));
        ecc_backdoor_access_executed_ev.trigger();
"""





preload_contents = f"""

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
"""

#loop to generate the preload backdoor access
for nb in range(config["spm_nb_banks"]):
    for nsb in range(config["spm_nb_sub_banks"]):
        for nmb in range(config["spm_nb_mini_banks"]):
            for nsr in range(config["spm_nb_srams_per_mini_bank"]):
                preload_contents += f"""
                i_spm_dut.u_spm_mem.g_bank_inst[{nb}].u_spm_mem_bank.g_sub_bank_inst[{nsb}].u_spm_mem_sub_bank.g_mini_bank_inst[{nmb}].u_spm_mem_mini_bank.g_sram_inst[{nsr}].u_tc_sram.gen_macro.u_macro.u_mem.write_mem(i, data_w_ecc);
"""
preload_contents += f"""
            `else
"""
for nb in range(config["spm_nb_banks"]):
    for nsb in range(config["spm_nb_sub_banks"]):
        for nmb in range(config["spm_nb_mini_banks"]):
            for nsr in range(config["spm_nb_srams_per_mini_bank"]):
                preload_contents += f"""
                uvm_hdl_deposit($sformatf("hdl_top.dut.u_ai_core.u_aic_infra_p.u_aic_infra.u_aic_spm.u_spm_mem.g_bank_inst[{nb}].u_spm_mem_bank.g_sub_bank_inst[{nsb}].u_spm_mem_sub_bank.g_mini_bank_inst[{nmb}].u_spm_mem_mini_bank.g_sram_inst[{nsr}].u_tc_sram.memory_q[%0d]", i), data_w_ecc);

"""

preload_contents += f"""
`endif
        end
    endtask
"""






contents = f"""

{preload_contents}

    // memory backkdoor access utils
    initial begin
        longint starting_address, number_of_srams, line_address;
        int bit1_to_swap;
        int bit2_to_swap;
        ecc_write_completed_ev = new();
        ecc_read_completed_ev = new();
        ecc_read_started_ev = new();
        ecc_backdoor_access_executed_ev = new();
        number_of_srams = spm_config.spm_nb_banks * spm_config.spm_nb_sub_banks * spm_config.spm_nb_mini_banks * spm_config.spm_nb_srams_per_mini_bank;
        //align to 64bits (8bytes)
        starting_address = 1;
        while (starting_address % 8 != 0) begin
            starting_address = $urandom_range(((spm_config.spm_mem_size_kb/number_of_srams)*1024)-1, 0);
        end
        // line addres is 8 times smalle because it doesn't address each byte
        line_address = starting_address/8;
        uvm_config_db#(longint)::set(uvm_root::get(), "*", "starting_address", starting_address);
        uvm_config_db#(uvm_event)::set(uvm_root::get(), "*", "ecc_write_completed_ev", ecc_write_completed_ev);
        uvm_config_db#(uvm_event)::set(uvm_root::get(), "*", "ecc_read_completed_ev", ecc_read_completed_ev);
        uvm_config_db#(uvm_event)::set(uvm_root::get(), "*", "ecc_read_started_ev", ecc_read_started_ev);
        uvm_config_db#(uvm_event)::set(uvm_root::get(), "*", "ecc_backdoor_access_executed_ev", ecc_backdoor_access_executed_ev);

{backdoor_contents}

    end



    function spm_config_t calc_config(int spm_mem_size_kb = 0, int spm_nb_banks = 0, int spm_nb_sub_banks = 0, int spm_nb_mini_banks = 0, int spm_nb_srams_per_mini_bank = 2);
        calc_config.spm_axi_data_width =             {config["spm_axi_data_width"]};
        calc_config.spm_axi_strb_width =             {config["spm_axi_strb_width"]};
        calc_config.spm_axi_addr_width =             {config["spm_axi_addr_width"]};
        calc_config.spm_axi_id_width =               {config["spm_axi_id_width"]};
        calc_config.spm_axi_atop_width =             {config["spm_axi_atop_width"]};
        calc_config.spm_mem_size_kb =                {config["spm_mem_size_kb"]};
        calc_config.spm_mem_macro_depth_k =          {config["spm_mem_macro_depth_k"]};
        calc_config.spm_nb_banks =                   {config["spm_nb_banks"]};
        calc_config.spm_nb_sub_banks =               {config["spm_nb_sub_banks"]};
        calc_config.spm_nb_mini_banks =              {config["spm_nb_mini_banks"]};
        calc_config.spm_nb_srams_per_mini_bank =     {config["spm_nb_srams_per_mini_bank"]};
        calc_config.spm_nb_req_pipeline =            {config["spm_nb_req_pipeline"]};
        calc_config.spm_nb_rsp_pipeline =            {config["spm_nb_rsp_pipeline"]};
        calc_config.ecc_protection_en =              {config["ecc_protection_en"]};
    endfunction





    `define DEF_SPM_AXI_DATA_WIDTH {config["spm_axi_data_width"]}
    `define DEF_SPM_AXI_STRB_WIDTH {config["spm_axi_strb_width"]}
    `define DEF_SPM_AXI_ADDR_WIDTH {config["spm_axi_addr_width"]}
    `define DEF_SPM_AXI_ID_WIDTH {config["spm_axi_id_width"]}
    `define DEF_SPM_AXI_ATOP_WIDTH {config["spm_axi_atop_width"]}
    `define DEF_SPM_MEM_SIZE_KB {config["spm_mem_size_kb"]}
    `define DEF_SPM_MEM_MACRO_DEPTH_K {config["spm_mem_macro_depth_k"]}
    `define DEF_SPM_NB_BANKS {config["spm_nb_banks"]}
    `define DEF_SPM_NB_SUB_BANKS {config["spm_nb_sub_banks"]}
    `define DEF_SPM_NB_MINI_BANKS {config["spm_nb_mini_banks"]}
    `define DEF_SPM_NB_SRAMS_PER_MINI_BANK {config["spm_nb_srams_per_mini_bank"]}
    `define DEF_SPM_NB_REQ_PIPELINE {config["spm_nb_req_pipeline"]}
    `define DEF_SPM_NB_RSP_PIPELINE {config["spm_nb_rsp_pipeline"]}
    `define DEF_ECC_PROTECTION_EN {config["ecc_protection_en"]}
"""



directory = "../dv/tb/generated"
file_name = "../dv/tb/generated/spm_config_generated.svh"

ensure_directory_exists(directory)
ensure_file_exists(file_name)


with open(file_name, "w") as f:
    f.write(contents)
