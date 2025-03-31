`ifndef DMC_ADDR_GEN_REF_MODEL_SV
`define DMC_ADDR_GEN_REF_MODEL_SV

/* reference model generally works in a simple way:
it is only used for IFD/ODR functionality. direct AXI writes/RVV don't require a ref model
this ref model receives a command recipe that was already generated/randomized thorugh cmd_in analysis port
the model then creates a json files from those, and runs a python script containing the ereference, to create a file containing list of addresses and masks and pad values based on the received cmd.
this list will be later used to make sure that addresses that the DUT block (IFD/ODR) generated matches the ones that the ref model generated. including masks/padding.
the addresses are then read from (inside L1) and the mask/padding is applied, and compared to the AXI data output, to make sure that the data is also correct.
Specifics:
  - IFDS:
    with IFDs, AXI data is the output of L1 masked, so we take the data from L1, mask it, and compare to AXI data.

  - ODRs:
    with ODRs, the ref model  generates an AXI master stream, and based on that stream and the addresses/masks file, we apply mask to data, and compare them to the data in L1, this is how we know if the written data is correct or not.

  - compression:
    compression is only possible in IFDW, and the compression is generated in ifdw_compression_seq and not here.

  - VTRSP:
    VTRSP is possible in both ODRs, and in IFDW. it is done in here in the following manner - once we have our stream, and our recipe file, we use them in a python file to perform transpose efficiently, and save the output to another file.
    this file is then read by the ref model, and it's outputs are masked (if necessary) and compared to the data that was written to L1. this is how we know if the data was written correctly.
    in case the incoming AXI stream is in pword32int16 format (512 bits = 32 words of 16 bits), and we need to cast in into pword64int8 format (512 bits = 64 words of 8 bits) we will perform this reduction here.
    you can find similar code in data_scoreboard file, with additional info on what's going on.

The output of this file is checked in the scoreboards:
  - dmc_addr_gen_scoreboard : this scoreboard checks the list of addresses, masks, pad values that were generated in DUT, compared to what we expect.
  - dmc_data_scoreboard     : this scoreboard checks the actual data that was received through AXI, compared to what we expect.
*/

class dmc_addr_gen_ref_model extends uvm_component;
  `uvm_component_utils(dmc_addr_gen_ref_model)

  addr_gen_cmd_t             addr_gen_cmd;
  bit                        regression = 0;
  bit                        sanity = 0;
  bit                        vsim = 0;
  dmc_addr_gen_seq_item  cmd_in_item, cmd_out_item;
 `ifdef AI_CORE_TOP_ENV_CHECK
  string                     refmodel_path = "$REPO_ROOT/hw/ip/aic_ls/default/dv/uvm/refmodels/dmc_addr_gen_ref_model"; // absolute path
 `else
  string                     refmodel_path = "$REPO_ROOT/hw/ip/aic_ls/default/dv/uvm/refmodels/dmc_addr_gen_ref_model"; // absolute path
 `endif

  string                     txt_filename = "*addr_gen_cmd.txt";
  string                     vtrsp_odr_stream_path;
  string                     vtrsp_odr_memory_path;
  string                     sim_dir = "$REPO_ROOT/hw/ip/aic_ls/default/dv/sim/";
  string                     icdf_dir = "icdf";
  string                     icdf_out_dir = "icdf_out";
  string                     absolute_icdf_dir = {sim_dir, icdf_dir};
  string                     absolute_icdf_out_dir = {sim_dir, icdf_out_dir};
  string                     python_version = "python3.10";
  string                     model_name;
  uvm_tlm_analysis_fifo#(dmc_addr_gen_seq_item) cmd_in;
  uvm_analysis_port#(dmc_addr_gen_seq_item)     cmd_out;
  uvm_analysis_port#(odr_stream_mem_t)              vtrsp_out; // post memory snaopshot of vector transposed data

  mem_baseaddr_t             l1_base_addr;
  mem_baseaddr_t             mem_baseaddr;
  bit                        m_addr_out_of_range_en;
  bit                        m_vtrsp_err_en;
  int unsigned               mem_bsize;
  bit                        m_last_addr_out_of_range;
  stream_info_t              m_stream_info_q[$];
  semaphore                  m_semaphore;
  int8_data_arr_t            m_int8_q[$];
  bit                        m_all_padded;

  event                      m_rst_evt;
  event                      m_rst_done_evt;
  uvm_event                  addr_generated_evt;

  function new(string name ="", uvm_component parent = null);
    super.new(name,parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    int unsigned seed;
    string testcase_name;
    super.build_phase(phase);
    cmd_in   = new("cmd_in", this);
    cmd_out  = new("cmd_out" , this);
    if (get_device_name() inside {"m_odr", "d_odr"}) begin  // we don't use vtrsp_out port for IFDW since it's done at data scoreaboard instead
      vtrsp_out  = new("vtrsp_out" , this);
    end
    void'($value$plusargs("REGRESSION=%0d", regression));
    void'($value$plusargs("SANITY=%0d", sanity));
    void'($value$plusargs("VSIM=%0d", vsim));
    `uvm_info(get_name(), $sformatf("Debug  VSIM: %0d", vsim), UVM_LOW)
    m_semaphore = new(1);
    addr_generated_evt = new("addr_generated_evt"); // initialize
  endfunction : build_phase

  function void run_system_cmd(string cmd, bit print_cmd = 1, bit is_fatal=1);
    if ($system(cmd) != 0) begin
      `uvm_error(get_name(), $sformatf("Exit status not 0 for %s", cmd));
      if (is_fatal) begin
        `uvm_fatal(get_name(), $sformatf("Exit status not 0 for %s", cmd));
      end
    end else begin
      if (print_cmd) begin
        `uvm_info(get_name(), $sformatf("Executing cmd: \n\n %s \n\n done!", cmd), UVM_NONE);
      end
    end
  endfunction

  function void update_model_name(int iteration);
    int unsigned seed;
    string testcase_name;
    if ($value$plusargs("UVM_TESTNAME=%s", testcase_name)) begin
      seed = $get_initial_random_seed();
    end else begin
      `uvm_fatal(get_name(), $sformatf("Tescase name not found!, %s", testcase_name))
    end
    model_name = $sformatf("%s_%s_%0d_%0d", testcase_name, get_name(), iteration, seed); // make it unique so it supports regression
  endfunction

  virtual task run_model();
    forever begin
      cmd_in.get(cmd_in_item);
      if (cmd_in_item.m_has_cmd) begin
        addr_gen_cmd = cmd_in_item.m_cmd;
        `uvm_info(get_name(), $sformatf("Received dmc_addr_gen_seq_item: %s", cmd_in_item.convert2string()), UVM_LOW)
        run_cmd();
        read_addr_gen_output();
      end
    end
  endtask

  virtual task run_phase(uvm_phase phase);
    dmc_addr_gen_seq_item itm;
    super.run_phase(phase);
    forever begin
      fork
        run_model();
        begin
          @ (m_rst_evt);
          m_stream_info_q.delete();
          while(cmd_in.try_get(itm));
          void'(m_semaphore.try_get());
          m_semaphore.put();
          @ (m_rst_done_evt);
        end
      join_any
      disable fork;
    end
  endtask : run_phase

  function string get_device_name();
    string dev_name, out_name;
    dev_name = get_name();
    dev_name = dev_name.substr(2, dev_name.len()-9); // minus m_ and _ref_mdl

    case (dev_name)
      "m_ifd0": out_name = "m_ifd_0";
      "m_ifd1": out_name = "m_ifd_1";
      "m_ifd2": out_name = "m_ifd_2";
      "m_ifdw": out_name = "m_ifd_w";
      "d_ifd0": out_name = "d_ifd_0";
      "d_ifd1": out_name = "d_ifd_1";
      "m_odr" : out_name = "m_odr";
      "d_odr" : out_name = "d_odr";
    endcase

    return out_name;
  endfunction

  function string create_icdf_dir();
    string bash_cmd = "";
    $sformat(bash_cmd, "mkdir -p ./refmodel/%s/", model_name); // mkdirend
    return bash_cmd;
  endfunction

  function void run_cmd();
    string bash_cmd;
    if (cmd_in_item == null) begin
      `uvm_fatal(get_name(), "cmd_in_item is null!")
    end

    mem_baseaddr = cmd_in_item.get_mem_base_addr();
    mem_bsize = (m_addr_out_of_range_en)? 0: cmd_in_item.m_mem_bsize;
    update_model_name(cmd_in_item.iteration); // need to update model name to not mess stuff up

    bash_cmd = create_icdf_dir();
    run_system_cmd(bash_cmd);

    case (cmd_in_item.m_cmd_format)  // create a JSON file to then use it to supply info to python reference
      CMDFORMAT_LINEAR        : create_linear_cmd_json();
      CMDFORMAT_DEF_BASED     : create_def_based_cmd_json("DEF_BASED");
      CMDFORMAT_OFFSET_BASED  : create_def_based_cmd_json("OFFSET_DEF_BASED");
      CMDFORMAT_3DIM_FALLBACK : create_3_dim_cmd_json();
      CMDFORMAT_4DIM_FALLBACK : create_4_dim_cmd_json();
      default: `uvm_fatal(get_name(), $sformatf("Invalid command format of %s !", cmd_in_item.m_cmd_format.name()))
    endcase
    run_cmd_output_creation();  // use python reference to create an ouput of expected addresses/masks/pad values/etc
  endfunction

  function void run_cmd_output_creation();
    string cmd_json_file_path = $sformatf("./refmodel/%s/cmd_%s.json", model_name, get_device_name());
    string cmd_output_file_path = $sformatf("./refmodel/%s/dp_ctrl_stream_%s.txt", model_name, get_device_name());
    string bash_cmd;
    bash_cmd = $sformatf("%s %s/cmd_addr_gen.py %s %s",python_version, refmodel_path, cmd_json_file_path, cmd_output_file_path);
    run_system_cmd(bash_cmd);
  endfunction

  function void create_linear_cmd_json();
    string cmd_json_file_path = $sformatf("./refmodel/%s/cmd_%s.json", model_name, get_device_name());
    string bash_cmd;

    `uvm_info(get_type_name(), $sformatf("Creating linear cmd in file %s", cmd_json_file_path), UVM_LOW)
    
    // writing to file using system command instead of svl built in command due to a problem where this writes aren't really happening during simulation, but only after it
    $sformat(bash_cmd, "echo -e '");
    $sformat(bash_cmd, "%s{\n", bash_cmd);  // open a json file
    $sformat(bash_cmd, "%s  \"cmd_type\": \"LINEAR\",\n", bash_cmd);  // LINEAR cmd
    $sformat(bash_cmd, "%s  \"mem_baseaddr\": %0d,\n", bash_cmd, mem_baseaddr);  // mem_baseaddr
    $sformat(bash_cmd, "%s  \"compression\": %0d,\n", bash_cmd, cmd_in_item.m_decomp_en);  // compression
    $sformat(bash_cmd, "%s  \"length\": %0d\n", bash_cmd, cmd_in_item.m_length);  // length
    $sformat(bash_cmd, "%s}\n", bash_cmd);  // closes a json file
    $sformat(bash_cmd, "%s' > %s", bash_cmd, cmd_json_file_path);
    run_system_cmd(.cmd(bash_cmd), .print_cmd(0));
  endfunction

  function void create_def_based_cmd_json(string cmd_type);
    // offset based and def based cmds are essentially the same in terms of generation
    string cmd_json_file_path = $sformatf("./refmodel/%s/cmd_%s.json", model_name, get_device_name());
    string bash_cmd;

    `uvm_info(get_type_name(), $sformatf("Creating def_based_cmd in file %s", cmd_json_file_path), UVM_LOW)
    
    // writing to file using system command instead of svl built in command due to a problem where this writes aren't really happening during simulation, but only after it
    $sformat(bash_cmd, "echo -e '");
    $sformat(bash_cmd, "%s{\n", bash_cmd);  // open a json file
    $sformat(bash_cmd, "%s  \"cmd_type\": \"%s\",\n", bash_cmd, cmd_type);  // DEF BASED CMD
    $sformat(bash_cmd, "%s  \"mem_baseaddr\": %0d,\n", bash_cmd, mem_baseaddr);
    $sformat(bash_cmd, "%s  \"pad_val\": %0d,\n", bash_cmd, cmd_in_item.m_pad_val);
    $sformat(bash_cmd, "%s  \"intra_pad_val\": %0d,\n", bash_cmd, cmd_in_item.m_intra_pad_val);
    $sformat(bash_cmd, "%s  \"format\": %0d,\n", bash_cmd, cmd_in_item.m_format);
    $sformat(bash_cmd, "%s  \"mask_start\": %0d,\n", bash_cmd, cmd_in_item.m_mask_start);
    $sformat(bash_cmd, "%s  \"mask_end\": %0d,\n", bash_cmd, cmd_in_item.m_mask_end);
    $sformat(bash_cmd, "%s  \"mem_offset\": %0d,\n", bash_cmd, cmd_in_item.m_mem_offset);
    $sformat(bash_cmd, "%s  \"ring_buf_size\": %0d,\n", bash_cmd, cmd_in_item.m_ring_buff_size);
    $sformat(bash_cmd, "%s  \"vect_dim\": %0d,\n", bash_cmd, cmd_in_item.m_vect_dim);
    $sformat(bash_cmd, "%s  \"vtrsp_mode\": %0d,\n", bash_cmd, cmd_in_item.m_vtrsp_mode);
    $sformat(bash_cmd, "%s  \"pad_mode\": %0d,\n", bash_cmd, cmd_in_item.m_pad_mode);
    
    // dim_offset
    $sformat(bash_cmd, "%s  \"dim_offset_a\": %0d,\n", bash_cmd, cmd_in_item.m_dim_offset_a);
    if (cmd_in_item.m_num_dim > 1) $sformat(bash_cmd, "%s  \"dim_offset_b\": %0d,\n", bash_cmd, cmd_in_item.m_dim_offset_b); // only necessary if we have more then 1 dimensions
    if (cmd_in_item.m_num_dim > 2) $sformat(bash_cmd, "%s  \"dim_offset_c\": %0d,\n", bash_cmd, cmd_in_item.m_dim_offset_c); // only necessary if we have more then 2 dimensions
    if (cmd_in_item.m_num_dim > 3) $sformat(bash_cmd, "%s  \"dim_offset_d\": %0d,\n", bash_cmd, cmd_in_item.m_dim_offset_d); // only necessary if we have more then 3 dimensions
    // dim_width
    $sformat(bash_cmd, "%s  \"dim_width_a\": %0d,\n", bash_cmd, cmd_in_item.m_dim_width_a);
    if (cmd_in_item.m_num_dim > 1) $sformat(bash_cmd, "%s  \"dim_width_b\": %0d,\n", bash_cmd, cmd_in_item.m_dim_width_b);
    if (cmd_in_item.m_num_dim > 2) $sformat(bash_cmd, "%s  \"dim_width_c\": %0d,\n", bash_cmd, cmd_in_item.m_dim_width_c);
    if (cmd_in_item.m_num_dim > 3) $sformat(bash_cmd, "%s  \"dim_width_d\": %0d,\n", bash_cmd, cmd_in_item.m_dim_width_d);
    // dim_width
    $sformat(bash_cmd, "%s  \"mem_stride_a\": %0d,\n", bash_cmd, cmd_in_item.m_mem_stride_a);
    if (cmd_in_item.m_num_dim > 1) $sformat(bash_cmd, "%s  \"mem_stride_b\": %0d,\n", bash_cmd, cmd_in_item.m_mem_stride_b);
    if (cmd_in_item.m_num_dim > 2) $sformat(bash_cmd, "%s  \"mem_stride_c\": %0d,\n", bash_cmd, cmd_in_item.m_mem_stride_c);
    if (cmd_in_item.m_num_dim > 3) $sformat(bash_cmd, "%s  \"mem_stride_d\": %0d,\n", bash_cmd, cmd_in_item.m_mem_stride_d);
    // dim_width
    $sformat(bash_cmd, "%s  \"inner_length_a\": %0d,\n", bash_cmd, cmd_in_item.m_inner_length_a);
    if (cmd_in_item.m_num_dim > 1) $sformat(bash_cmd, "%s  \"inner_length_b\": %0d,\n", bash_cmd, cmd_in_item.m_inner_length_b);
    if (cmd_in_item.m_num_dim > 2) $sformat(bash_cmd, "%s  \"inner_length_c\": %0d,\n", bash_cmd, cmd_in_item.m_inner_length_c);
    if (cmd_in_item.m_num_dim > 3) $sformat(bash_cmd, "%s  \"inner_length_d\": %0d,\n", bash_cmd, cmd_in_item.m_inner_length_d);
    // dim_width
    $sformat(bash_cmd, "%s  \"outer_length_a\": %0d,\n", bash_cmd, cmd_in_item.m_outer_length_a);
    if (cmd_in_item.m_num_dim > 1) $sformat(bash_cmd, "%s  \"outer_length_b\": %0d,\n", bash_cmd, cmd_in_item.m_outer_length_b);
    if (cmd_in_item.m_num_dim > 2) $sformat(bash_cmd, "%s  \"outer_length_c\": %0d,\n", bash_cmd, cmd_in_item.m_outer_length_c);
    if (cmd_in_item.m_num_dim > 3) $sformat(bash_cmd, "%s  \"outer_length_d\": %0d,\n", bash_cmd, cmd_in_item.m_outer_length_d);
    // dim_width
    $sformat(bash_cmd, "%s  \"inner_stride_a\": %0d,\n", bash_cmd, cmd_in_item.m_inner_stride_a);
    if (cmd_in_item.m_num_dim > 1) $sformat(bash_cmd, "%s  \"inner_stride_b\": %0d,\n", bash_cmd, cmd_in_item.m_inner_stride_b);
    if (cmd_in_item.m_num_dim > 2) $sformat(bash_cmd, "%s  \"inner_stride_c\": %0d,\n", bash_cmd, cmd_in_item.m_inner_stride_c);
    if (cmd_in_item.m_num_dim > 3) $sformat(bash_cmd, "%s  \"inner_stride_d\": %0d,\n", bash_cmd, cmd_in_item.m_inner_stride_d);
    // dim_width
    $sformat(bash_cmd, "%s  \"outer_stride_a\": %0d,\n", bash_cmd, cmd_in_item.m_outer_stride_a);
    if (cmd_in_item.m_num_dim > 1) $sformat(bash_cmd, "%s  \"outer_stride_b\": %0d,\n", bash_cmd, cmd_in_item.m_outer_stride_b);
    if (cmd_in_item.m_num_dim > 2) $sformat(bash_cmd, "%s  \"outer_stride_c\": %0d,\n", bash_cmd, cmd_in_item.m_outer_stride_c);
    if (cmd_in_item.m_num_dim > 3) $sformat(bash_cmd, "%s  \"outer_stride_d\": %0d,\n", bash_cmd, cmd_in_item.m_outer_stride_d);

    $sformat(bash_cmd, "%s  \"mem_bsize\": %0d\n", bash_cmd, mem_bsize);  // puuting it in the end to not fight with the ',' at the last line.
    $sformat(bash_cmd, "%s}\n", bash_cmd);  // closes a json file
    $sformat(bash_cmd, "%s' > %s", bash_cmd, cmd_json_file_path);
    run_system_cmd(.cmd(bash_cmd), .print_cmd(0));
  endfunction

  function void create_3_dim_cmd_json();
    string cmd_json_file_path = $sformatf("./refmodel/%s/cmd_%s.json", model_name, get_device_name());
    string bash_cmd;

    `uvm_info(get_type_name(), $sformatf("Creating 3_dim_cmd_json in file %s", cmd_json_file_path), UVM_LOW)

    // writing to file using system command instead of svl built in command due to a problem where this writes aren't really happening during simulation, but only after it
    $sformat(bash_cmd, "echo -e '");
    $sformat(bash_cmd, "%s{\n", bash_cmd);  // open a json file
    $sformat(bash_cmd, "%s  \"cmd_type\": \"THREE_DIM_FALLBACK\",\n", bash_cmd);  // FOUR DIM cmd
    $sformat(bash_cmd, "%s  \"mem_baseaddr\": %0d,\n", bash_cmd, mem_baseaddr);
    $sformat(bash_cmd, "%s  \"pad_val\": %0d,\n", bash_cmd, cmd_in_item.m_pad_val);
    $sformat(bash_cmd, "%s  \"intra_pad_val\": %0d,\n", bash_cmd, cmd_in_item.m_intra_pad_val);
    $sformat(bash_cmd, "%s  \"format\": %0d,\n", bash_cmd, cmd_in_item.m_format);
    $sformat(bash_cmd, "%s  \"mask_start\": %0d,\n", bash_cmd, cmd_in_item.m_mask_start);
    $sformat(bash_cmd, "%s  \"mask_end\": %0d,\n", bash_cmd, cmd_in_item.m_mask_end);
    $sformat(bash_cmd, "%s  \"mem_offset\": %0d,\n", bash_cmd, cmd_in_item.m_mem_offset);
    $sformat(bash_cmd, "%s  \"ring_buf_size\": %0d,\n", bash_cmd, cmd_in_item.m_ring_buff_size);
    $sformat(bash_cmd, "%s  \"vect_dim\": %0d,\n", bash_cmd, cmd_in_item.m_vect_dim);
    $sformat(bash_cmd, "%s  \"vtrsp_mode\": %0d,\n", bash_cmd, cmd_in_item.m_vtrsp_mode);
    $sformat(bash_cmd, "%s  \"pad_mode\": %0d,\n", bash_cmd, cmd_in_item.m_pad_mode);
    $sformat(bash_cmd, "%s  \"mem_bsize\": %0d,\n", bash_cmd, mem_bsize);
    // dim_offset
    $sformat(bash_cmd, "%s  \"dim_offset_a\": %0d,\n", bash_cmd, cmd_in_item.m_dim_offset_a);
    $sformat(bash_cmd, "%s  \"dim_offset_b\": %0d,\n", bash_cmd, cmd_in_item.m_dim_offset_b);
    $sformat(bash_cmd, "%s  \"dim_offset_c\": %0d,\n", bash_cmd, cmd_in_item.m_dim_offset_c);
    // dim_width
    $sformat(bash_cmd, "%s  \"dim_width_a\": %0d,\n", bash_cmd, cmd_in_item.m_dim_width_a);
    $sformat(bash_cmd, "%s  \"dim_width_b\": %0d,\n", bash_cmd, cmd_in_item.m_dim_width_b);
    $sformat(bash_cmd, "%s  \"dim_width_c\": %0d,\n", bash_cmd, cmd_in_item.m_dim_width_c);
    // dim_width
    $sformat(bash_cmd, "%s  \"mem_stride_a\": %0d,\n", bash_cmd, cmd_in_item.m_mem_stride_a);
    $sformat(bash_cmd, "%s  \"mem_stride_b\": %0d,\n", bash_cmd, cmd_in_item.m_mem_stride_b);
    $sformat(bash_cmd, "%s  \"mem_stride_c\": %0d,\n", bash_cmd, cmd_in_item.m_mem_stride_c);
    // dim_width
    $sformat(bash_cmd, "%s  \"inner_length_a\": %0d,\n", bash_cmd, cmd_in_item.m_inner_length_a);
    $sformat(bash_cmd, "%s  \"inner_length_b\": %0d,\n", bash_cmd, cmd_in_item.m_inner_length_b);
    $sformat(bash_cmd, "%s  \"inner_length_c\": %0d,\n", bash_cmd, cmd_in_item.m_inner_length_c);
    // dim_width
    $sformat(bash_cmd, "%s  \"outer_length_a\": %0d,\n", bash_cmd, cmd_in_item.m_outer_length_a);
    $sformat(bash_cmd, "%s  \"outer_length_b\": %0d,\n", bash_cmd, cmd_in_item.m_outer_length_b);
    $sformat(bash_cmd, "%s  \"outer_length_c\": %0d,\n", bash_cmd, cmd_in_item.m_outer_length_c);
    // dim_width
    $sformat(bash_cmd, "%s  \"inner_stride_a\": %0d,\n", bash_cmd, cmd_in_item.m_inner_stride_a);
    $sformat(bash_cmd, "%s  \"inner_stride_b\": %0d,\n", bash_cmd, cmd_in_item.m_inner_stride_b);
    $sformat(bash_cmd, "%s  \"inner_stride_c\": %0d,\n", bash_cmd, cmd_in_item.m_inner_stride_c);
    // dim_width
    $sformat(bash_cmd, "%s  \"outer_stride_a\": %0d,\n", bash_cmd, cmd_in_item.m_outer_stride_a);
    $sformat(bash_cmd, "%s  \"outer_stride_b\": %0d,\n", bash_cmd, cmd_in_item.m_outer_stride_b);
    $sformat(bash_cmd, "%s  \"outer_stride_c\": %0d\n", bash_cmd, cmd_in_item.m_outer_stride_c);
    $sformat(bash_cmd, "%s}\n", bash_cmd);  // closes a json file
    $sformat(bash_cmd, "%s' > %s", bash_cmd, cmd_json_file_path);
    run_system_cmd(.cmd(bash_cmd), .print_cmd(0));
  endfunction

  function void create_4_dim_cmd_json();
    string cmd_json_file_path = $sformatf("./refmodel/%s/cmd_%s.json", model_name, get_device_name());
    string bash_cmd;

    `uvm_info(get_type_name(), $sformatf("Creating 4_dim_cmd_json in file %s", cmd_json_file_path), UVM_LOW)

    // writing to file using system command instead of svl built in command due to a problem where this writes aren't really happening during simulation, but only after it
    $sformat(bash_cmd, "echo -e '");
    $sformat(bash_cmd, "%s{\n", bash_cmd);  // open a json file
    $sformat(bash_cmd, "%s  \"cmd_type\": \"FOUR_DIM_FALLBACK\",\n", bash_cmd);  // FOUR DIM cmd
    $sformat(bash_cmd, "%s  \"mem_baseaddr\": %0d,\n", bash_cmd, mem_baseaddr);
    $sformat(bash_cmd, "%s  \"pad_val\": %0d,\n", bash_cmd, cmd_in_item.m_pad_val);
    $sformat(bash_cmd, "%s  \"intra_pad_val\": %0d,\n", bash_cmd, cmd_in_item.m_intra_pad_val);
    $sformat(bash_cmd, "%s  \"format\": %0d,\n", bash_cmd, cmd_in_item.m_format);
    $sformat(bash_cmd, "%s  \"mask_start\": %0d,\n", bash_cmd, cmd_in_item.m_mask_start);
    $sformat(bash_cmd, "%s  \"mask_end\": %0d,\n", bash_cmd, cmd_in_item.m_mask_end);
    $sformat(bash_cmd, "%s  \"mem_offset\": %0d,\n", bash_cmd, cmd_in_item.m_mem_offset);
    $sformat(bash_cmd, "%s  \"ring_buf_size\": %0d,\n", bash_cmd, cmd_in_item.m_ring_buff_size);
    $sformat(bash_cmd, "%s  \"vect_dim\": %0d,\n", bash_cmd, cmd_in_item.m_vect_dim);
    $sformat(bash_cmd, "%s  \"vtrsp_mode\": %0d,\n", bash_cmd, cmd_in_item.m_vtrsp_mode);
    $sformat(bash_cmd, "%s  \"pad_mode\": %0d,\n", bash_cmd, cmd_in_item.m_pad_mode);
    $sformat(bash_cmd, "%s  \"mem_bsize\": %0d,\n", bash_cmd, mem_bsize);
    // dim_offset
    $sformat(bash_cmd, "%s  \"dim_offset_a\": %0d,\n", bash_cmd, cmd_in_item.m_dim_offset_a);
    $sformat(bash_cmd, "%s  \"dim_offset_b\": %0d,\n", bash_cmd, cmd_in_item.m_dim_offset_b);
    $sformat(bash_cmd, "%s  \"dim_offset_c\": %0d,\n", bash_cmd, cmd_in_item.m_dim_offset_c);
    $sformat(bash_cmd, "%s  \"dim_offset_d\": %0d,\n", bash_cmd, cmd_in_item.m_dim_offset_d);
    // dim_width
    $sformat(bash_cmd, "%s  \"dim_width_a\": %0d,\n", bash_cmd, cmd_in_item.m_dim_width_a);
    $sformat(bash_cmd, "%s  \"dim_width_b\": %0d,\n", bash_cmd, cmd_in_item.m_dim_width_b);
    $sformat(bash_cmd, "%s  \"dim_width_c\": %0d,\n", bash_cmd, cmd_in_item.m_dim_width_c);
    $sformat(bash_cmd, "%s  \"dim_width_d\": %0d,\n", bash_cmd, cmd_in_item.m_dim_width_d);
    // dim_width
    $sformat(bash_cmd, "%s  \"mem_stride_a\": %0d,\n", bash_cmd, cmd_in_item.m_mem_stride_a);
    $sformat(bash_cmd, "%s  \"mem_stride_b\": %0d,\n", bash_cmd, cmd_in_item.m_mem_stride_b);
    $sformat(bash_cmd, "%s  \"mem_stride_c\": %0d,\n", bash_cmd, cmd_in_item.m_mem_stride_c);
    $sformat(bash_cmd, "%s  \"mem_stride_d\": %0d,\n", bash_cmd, cmd_in_item.m_mem_stride_d);
    // dim_width
    $sformat(bash_cmd, "%s  \"inner_length_a\": %0d,\n", bash_cmd, cmd_in_item.m_inner_length_a);
    $sformat(bash_cmd, "%s  \"inner_length_b\": %0d,\n", bash_cmd, cmd_in_item.m_inner_length_b);
    $sformat(bash_cmd, "%s  \"inner_length_c\": %0d,\n", bash_cmd, cmd_in_item.m_inner_length_c);
    $sformat(bash_cmd, "%s  \"inner_length_d\": %0d,\n", bash_cmd, cmd_in_item.m_inner_length_d);
    // dim_width
    $sformat(bash_cmd, "%s  \"outer_length_a\": %0d,\n", bash_cmd, cmd_in_item.m_outer_length_a);
    $sformat(bash_cmd, "%s  \"outer_length_b\": %0d,\n", bash_cmd, cmd_in_item.m_outer_length_b);
    $sformat(bash_cmd, "%s  \"outer_length_c\": %0d,\n", bash_cmd, cmd_in_item.m_outer_length_c);
    $sformat(bash_cmd, "%s  \"outer_length_d\": %0d,\n", bash_cmd, cmd_in_item.m_outer_length_d);
    // dim_width
    $sformat(bash_cmd, "%s  \"inner_stride_a\": %0d,\n", bash_cmd, cmd_in_item.m_inner_stride_a);
    $sformat(bash_cmd, "%s  \"inner_stride_b\": %0d,\n", bash_cmd, cmd_in_item.m_inner_stride_b);
    $sformat(bash_cmd, "%s  \"inner_stride_c\": %0d,\n", bash_cmd, cmd_in_item.m_inner_stride_c);
    $sformat(bash_cmd, "%s  \"inner_stride_d\": %0d,\n", bash_cmd, cmd_in_item.m_inner_stride_d);
    // dim_width
    $sformat(bash_cmd, "%s  \"outer_stride_a\": %0d,\n", bash_cmd, cmd_in_item.m_outer_stride_a);
    $sformat(bash_cmd, "%s  \"outer_stride_b\": %0d,\n", bash_cmd, cmd_in_item.m_outer_stride_b);
    $sformat(bash_cmd, "%s  \"outer_stride_c\": %0d,\n", bash_cmd, cmd_in_item.m_outer_stride_c);
    $sformat(bash_cmd, "%s  \"outer_stride_d\": %0d\n", bash_cmd, cmd_in_item.m_outer_stride_d);
    $sformat(bash_cmd, "%s}\n", bash_cmd);  // closes a json file
    $sformat(bash_cmd, "%s' > %s", bash_cmd, cmd_json_file_path);
    run_system_cmd(.cmd(bash_cmd), .print_cmd(0));
  endfunction

  virtual task read_addr_gen_output();
    // read and parse the file that contains a list of addresses, masks, pad values, etc. and send them to the scoreboards
    string line;
    int file_handle, index;
    bit [35:0] addr;
    bit [AIC_DMC_PWORD_SIZE-1:0] msk;
    bit pad;
    int pad_val;
    int counter=0;
    int num_pword;
    bit casting;
    dmc_addr_gen_seq_item addr_item_q[$];
    stream_info_t stream_info;

    txt_filename = $sformatf("./refmodel/%s/dp_ctrl_stream_%s.txt", model_name, get_device_name());

    file_handle = $fopen(txt_filename, "r");
    if (file_handle) begin
        m_last_addr_out_of_range = 0;
        m_all_padded = 1;
        while($fgets(line,file_handle)) begin
            if (counter !=0) begin // skip txt file header
              void'($sscanf(line, "#%d addr: %h msk: %h pad: %d pad_val: %h", index, addr,msk,pad,pad_val));
              `uvm_info(get_type_name(), $sformatf("refmodel_dbg: %0d addr: %h msk: %h pad: %d pad_val: %h ... mem_baseaddr: 0x%0x mem_bsize: 0x%0x", index, addr,msk,pad,pad_val, mem_baseaddr, addr_gen_cmd.mem_bsize), UVM_HIGH)
              cmd_out_item = dmc_addr_gen_seq_item::type_id::create("out_item");
              cmd_out_item.do_copy(cmd_in_item);
              cmd_out_item.m_has_dpc_cmd = 1;
              cmd_out_item.m_dpc_cmd.dpc_addr = addr;
              cmd_out_item.m_dpc_cmd.dpc_msk = msk;
              cmd_out_item.m_dpc_cmd.dpc_format = cmd_out_item.m_format;
              cmd_out_item.m_dpc_cmd.dpc_config = cmd_out_item.header_vector_mode;
              cmd_out_item.m_dpc_cmd.dpc_pad = pad;
              cmd_out_item.m_dpc_cmd.dpc_pad_val = pad_val;
              cmd_out_item.m_dpc_cmd.dpc_intra_pad_val = cmd_out_item.m_intra_pad_val;
              cmd_out_item.m_dpc_cmd.err_addr_out_of_range = !(addr inside {[mem_baseaddr : mem_baseaddr + addr_gen_cmd.mem_bsize]}) && !pad;
              // Error addr out of range only when mem_bsize != 0
              cmd_out_item.m_dpc_cmd.err_addr_out_of_range = cmd_out_item.m_dpc_cmd.err_addr_out_of_range & (addr_gen_cmd.mem_bsize !=0);
              addr_item_q.push_back(cmd_out_item); // add into queue first because setting of dpc_last needs to be done.
              m_last_addr_out_of_range = cmd_out_item.m_dpc_cmd.err_addr_out_of_range || m_last_addr_out_of_range;
              if (pad==0 ) begin
                m_all_padded = 0;
                num_pword += 1;
              end
            end
            counter+=1;
        end
        $fclose(file_handle);
        if (addr_item_q.size() > 0) begin
          int a_size = addr_item_q.size()-1;
          addr_item_q[$].m_dpc_cmd.dpc_last = 1;
          addr_item_q[$].m_pword_len = num_pword; // for coverage
          if (addr_item_q[$].m_dpc_cmd.dpc_config && !addr_item_q[$].m_dpc_cmd.dpc_format) casting = 1;
        end
    end
    if (addr_item_q.size()==0) begin
      #100ns;
      `uvm_fatal(get_name(), "Got size of 0 for address generator! Please check the command used!")
    end else begin
      `uvm_info(get_name(), $sformatf("Got size of %0d for address generator!, casting = %0d", addr_item_q.size(), casting), UVM_LOW)
    end
    foreach (addr_item_q[i]) begin
      cmd_out.write(addr_item_q[i]);
      `uvm_info(get_name(), $sformatf("addr_item_q[%0d]: %h", i, addr_item_q[i].m_dpc_cmd.dpc_addr), UVM_HIGH)
      `uvm_info(get_name(), $sformatf("[%0d] VTRSP MODE: %0d PWORD: %0d",  i, addr_item_q[i].m_vtrsp_mode, addr_item_q[i].m_pword_len), UVM_HIGH)
    end
    stream_info.length = casting ? addr_item_q.size()*2 : addr_item_q.size(); // we need twice the command length size, in case of casting
    stream_info.used = 0;
    m_stream_info_q.push_back(stream_info);
    addr_generated_evt.trigger();
    #10ps;
    `uvm_info(get_name(), $sformatf("Address out of range: %0d", m_last_addr_out_of_range), UVM_HIGH)
  endtask

  // waits the most recent address gen stream info
  virtual task wait_address_gen_output(ref int unsigned len);
    int indx;
    int q_size;
    int effective_indx;
    m_semaphore.get();
    indx = -1;
    q_size = m_stream_info_q.size();
    foreach(m_stream_info_q[i]) begin
      if (m_stream_info_q[i].used == 0) begin
        indx = i;
        break;
      end
    end
    if (indx != -1) begin
      len = m_stream_info_q[indx].length;
      m_stream_info_q[indx].used = 1;
      effective_indx = indx;
    end else begin
      fork
        begin
          //wait (m_stream_info_q.size() >= q_size + 1);
          addr_generated_evt.wait_ptrigger();
          addr_generated_evt.reset();
        end
        begin
          #300us; // this will be enough to support outstanding commands
          `uvm_fatal(get_name(), "Timeout getting length from refmodel!")
        end
      join_any
      disable fork;
      len = m_stream_info_q[q_size].length;
      m_stream_info_q[q_size].used = 1;
      effective_indx = q_size;
    end
    `uvm_info(get_name(), $sformatf("Wait done with value of m_stream_info_q[%0d] %0d", effective_indx, len), UVM_LOW)
    m_semaphore.put();
  endtask

  task get_odr_stream(odr_stream_data_t odr_stream[$], bit int16_to_int8_casting, bit int16_not_int8);
    // this tests write odr stream to a file, so that we can VTRSP them
    string bash_cmd;
    int batch_size = 300, start_index;
    int odr_stream_size = odr_stream.size();
    string vtrsp_recipe_path = $sformatf("./refmodel/%s/vtrsp_recipe.json", model_name);

    if (m_vtrsp_err_en==1) return; // avoid ICDF assertion errors
    if (m_all_padded==1) begin
      `uvm_info(get_name(), "All padded data. Nothing to do.", UVM_LOW)
      return;
    end

    vtrsp_odr_stream_path = $sformatf("./refmodel/%s/vtrsp_odr_stream.json", model_name);
    vtrsp_odr_memory_path = $sformatf("./refmodel/%s/vtrsp_output.txt", model_name);

    `uvm_info(get_name(), $sformatf("ODR Stream size is %0d", odr_stream_size), UVM_LOW)

    $sformat(bash_cmd, "echo -e '");
    $sformat(bash_cmd, "%s[\n", bash_cmd); 
    $sformat(bash_cmd, "%s' > %s", bash_cmd, vtrsp_odr_stream_path);
    run_system_cmd(.cmd(bash_cmd), .print_cmd(0));
    while (odr_stream_size > 0) begin
      /* in some cases, the stream is too tolng to write it in one echo command. because of this we need to write it in part
      how this work is we write every time batch_size of the odr_stream, until we have less then batch_size, then we write what's left and close
      */
      if (odr_stream_size > batch_size) begin  // if we have more then batch_size left
        start_index = odr_stream.size()-odr_stream_size;
        bash_cmd = "";
        $sformat(bash_cmd, "echo -e '");
        for (int i = start_index; i < start_index+batch_size; i++) begin  // loop to write batch_size entries
          `uvm_info(get_name(), $sformatf("ODR Stream[%0d]: 0x%128x", i, odr_stream[i]), UVM_LOW)
          $sformat(bash_cmd, "%s  \"%128x\",\n", bash_cmd, odr_stream[i]);
        end
        $sformat(bash_cmd, "%s' >> %s", bash_cmd, vtrsp_odr_stream_path);
        odr_stream_size = odr_stream_size-batch_size;
        run_system_cmd(.cmd(bash_cmd), .print_cmd(0));
      end else begin  // if we have less then batch_size left
        start_index = odr_stream.size()-odr_stream_size;
        bash_cmd = "";
        $sformat(bash_cmd, "echo -e '");
        for (int i = start_index; i < odr_stream.size(); i++) begin  // loop to write what's left
          `uvm_info(get_name(), $sformatf("ODR Stream[%0d]: 0x%128x", i, odr_stream[i]), UVM_LOW)
          $sformat(bash_cmd, "%s  \"%128x\"%s\n", bash_cmd, odr_stream[i], i!=odr_stream.size()-1 ? ",":"");  // we add ',' for everything except the last entry!
        end
        $sformat(bash_cmd, "%s]\n", bash_cmd);  // closes a json file
        $sformat(bash_cmd, "%s' >> %s", bash_cmd, vtrsp_odr_stream_path);
        odr_stream_size = 0;
        run_system_cmd(.cmd(bash_cmd), .print_cmd(0));
      end
    end
    if (int16_to_int8_casting) bash_cmd = $sformatf("vtrsp_data_gen %s %s %s %s", vtrsp_odr_stream_path, vtrsp_recipe_path, vtrsp_odr_memory_path, "int16_to_int8_casting");  // now run python model to transpose the odr stream
    else bash_cmd = $sformatf("vtrsp_data_gen %s %s %s", vtrsp_odr_stream_path, vtrsp_recipe_path, vtrsp_odr_memory_path);  // now run python model to transpose the odr stream
    run_system_cmd(bash_cmd);
    read_memory_file(vtrsp_odr_memory_path, int16_to_int8_casting, int16_not_int8);
  endtask

  task read_memory_file(string name, bit int16_to_int8_casting, bit int16_not_int8);
    // run through the VTRSP output, apply masks, and send to data scoreboard
    int file_handle;
    odr_stream_mem_t mem;
    odr_stream_mem_t current_read_mem;
    bit[AIC_DMC_PWORD_SIZE-1:0] current_mask;
    bit[15:0] intra_pad_value;
    odr_stream_data_t          m_mem_q[odr_stream_addr_t];     // per command memory
    `uvm_info(get_name(), $sformatf("Reading memory file: %s", name), UVM_LOW)

    file_handle = $fopen(name, "r");
    if (file_handle) begin
      while (!$feof(file_handle)) begin
        $fscanf(file_handle, "addr: %d mask: %b intra_pad_value: %h data: %h", current_read_mem.addr, current_mask, intra_pad_value, current_read_mem.data);  // the file contains address, mask, data
        if ($feof(file_handle)) break; // if we've reached the end of the file, one last read is still performed (reading the EOF, basically) so we check again and then quit
        if (current_read_mem.addr == 0) continue;  // if address is 0, it's a drop, no need to add it. in case of casting from i16 to i8, it will just happen twice. no big change.
        if (int16_to_int8_casting) begin  // in case of vector_mode=1, format=0, we need to cast from int16 to int8, this means reducing two data lines to one
          odr_stream_data_t pword32i16_data[2];
          pword32i16_data[0] = current_read_mem.data;  // save the old data to first half of p32i16 data
          $fscanf(file_handle, "addr: %d mask: %b intra_pad_value: %h data: %h", current_read_mem.addr, current_mask, intra_pad_value, pword32i16_data[1]);  // read the second half of data. mask/intra_pad_value/address should be exactly the same, so no harm in overwriting for simplicity.
          current_read_mem.data = cast_int16_to_int8(pword32i16_data, current_mask, intra_pad_value);
        end else begin
          foreach (current_mask[i]) begin  // quickly apply mask
            if (!current_mask[i]) begin  // mask is 0. writing explicitly for convenience
              // in case we're in int16 mode, and we're in an odd index, we apply the upper 8 bit of the intra_pad value.
              // in any other case - int16 mode+even index/ int8 mode, we apply the lower 8 bit of the intra_pad value.
              current_read_mem.data[i*8+:8] = (int16_not_int8 && (i%2 != 0)) ? intra_pad_value[15:8] : intra_pad_value[7:0];
            end
          end
        end

        m_mem_q[current_read_mem.addr] = current_read_mem.data;  // in some cases, we have several writes to the same address. in this case, only the last one matters, so we only leave it.
        `uvm_info(get_name(), $sformatf("Assigning Addr: 0x%0x with Mask: 0x%0x and Data: 0x%128h", current_read_mem.addr, current_mask, current_read_mem.data), UVM_MEDIUM)
      end
      $fclose(file_handle);
      foreach (m_mem_q[i]) begin
        mem.addr = i;
        mem.data = m_mem_q[i];
        if (vtrsp_out != null) begin
          vtrsp_out.write(mem); // write to analysis port
        end
        `uvm_info(get_name(), $sformatf("Post memory snapshot. Address: 0x%0x, Data: 0x%0x", i, m_mem_q[i]), UVM_LOW)
      end
    end
  endtask

  function odr_stream_data_t cast_int16_to_int8(odr_stream_data_t pword32i16_data[], bit[AIC_DMC_PWORD_SIZE-1:0] current_mask, bit[15:0] intra_pad_value);
    /*
    This function casts from int16 format data to int8 format data. it does so the following way:
    we read from file 2 lines of data, they have different data, with the same address/mask/intra_pad_value, because the later come from the address generation block, which function in the int8 format (in this case, i.e. when dpc_cmd.format=0)
    since the data is in pword32int16 format, it means we have a total of 64 words, each 16 bits. we have a mask of 64 bits, so each bit of mask represents whether corresponding word will be masked or not.
    so we split the mask into lower 32 bits and upper. we use the lower bits to mask the first data line, and the upper to mask the second data line. where we mask the data, we replace it with intra_pad_value.
    after that we cast it down from 16 bits to 8 bits in the following manner - if the value is [-128:127], we leave it as is (already 8 bit), if it's lower then -128, we use -128, and if it's higher then 127, we use 127.
    */
    odr_stream_data_t pword64i8_data;
    odr_stream_mask_t mask[2];
    odr_stream_addr_t addr;

    foreach (mask[i]) begin
      mask[i] = current_mask[i*(AIC_DMC_PWORD_SIZE/2) +: (AIC_DMC_PWORD_SIZE/2)];  // take 32 bit of the mask. each bit represents whether a 32 bit number is used or not
      `uvm_info(get_name(), $sformatf("cast_int16_to_int8: mask is 0x%16x, pword32i16_data is 0x%128x", mask[i], pword32i16_data[i]), UVM_MEDIUM)
      for (int curr_num=0; curr_num < 32; curr_num++) begin
        bit signed [7:0]  int_8bit;
        bit signed [15:0] int_16bit;
        int_16bit = mask[i][curr_num] ? pword32i16_data[i][curr_num*16 +: 16] : intra_pad_value;
        int_8bit = (int_16bit > 127) ? 127 : ((int_16bit < -128) ? -128 : int_16bit[7:0]);
        pword64i8_data[i*256 + curr_num*8 +: 8] = int_8bit;
        `uvm_info(get_name(), $sformatf("cast_int16_to_int8: i is %0d, curr_num is %0d, Added 16/8 bit number 0x%0x/0x%0x!\nData is now 0x%0x", i, curr_num, int_16bit, int_8bit, pword64i8_data), UVM_HIGH)
      end
    end
    return pword64i8_data;
  endfunction

endclass
`endif
