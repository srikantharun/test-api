`ifndef DPU_STREAM_SEQUENCE_SV
`define DPU_STREAM_SEQUENCE_SV

class dpu_stream_sequence extends svt_axi_master_base_sequence;

  typedef union packed {
    struct packed {
      bit [47:0] data;
    } int48;

    struct packed {
      bit [15:0] unusedint32;
      bit [31:0] data;
    } int32;

    struct packed {
      bit [31:0] unusedint16;
      bit [15:0] data;
    } int16;

    struct packed {
      bit [39:0] unusedint8;
      bit [7:0] data;
    } int8;

    struct packed {
      bit [15:0] unusedfp32;
      bit sign;
      bit [7:0] exp;
      bit [22:0] frac;
    } fp32;

    struct packed {
      bit [23:0] unusedfp24;
      bit sign;
      bit [7:0] exp;
      bit [14:0] frac;
    } fp24;

    struct packed {
      bit [31:0] unusedfp16;
      bit sign;
      bit [4:0] exp;
      bit [9:0] frac;
    } fp16;
  } data_format_t;

  typedef  enum { SUBNORMAL, NORMAL, INF, NAN, RANDOM, MINUS_ZERO} data_rnd_type_t;

  typedef bit [PWORD_SIZE * IN_IFD0_WORD_DW -1 : 0] packed_data_t;
  typedef bit [PWORD_SIZE * IN_IFD0_WORD_DW -1 : 0] packed_data_queue_t [$];
  typedef data_format_t unpacked_data_t [PWORD_SIZE-1:0];


  //config vars
  enum {IFD_NONE, IFD0, IFD1} ifd_config;
  dp_ctrl_reg_t dp_ctrl_reg;
  bit lut_bins_monotonically_inscrease;

  rand unpacked_data_t data_stream;
  rand src_t data_format;

  dpu_cmd_descriptor_t cmd_desc;
  dpu_pkg::dpu_dp_cmd_t prog_mem[int];
  // exponent | fraction = 0  | fraction != 0
  //     0    |      +- 0     |   subnormal
  //  1 .. FE |     normal    |    normal
  //  FF      |  +- infinity  |     NaN
  rand data_rnd_type_t data_rnd_type;
  data_rnd_type_t fixed_data_type;

  bit fix_data_rnd_type;

  `uvm_object_utils(dpu_stream_sequence)

  constraint data_c {
    solve data_rnd_type before data_stream;
    data_format inside {[i0:b_c63]};
    if (fix_data_rnd_type) {
      data_rnd_type == fixed_data_type;
    }
    else {
      data_rnd_type dist {
        NORMAL     := 100,
        SUBNORMAL  := 20,
        INF        := 1,
        NAN        := 1,
        RANDOM     := 5,
        MINUS_ZERO := 1
      };
    }

    foreach (data_stream[i]) {
      //the values for lut bins array (first 16 elements of src) should be monotonically increasing
      if (lut_bins_monotonically_inscrease) {
        if (i != 0 && i < 16) {
          if (data_format inside {i0, pi0}) {
            //pword32
            if (cmd_desc.header.h_config[0]) {
              data_stream[i].int48.data[47] == data_stream[i-1].int48.data[47];
              //negative numbers
              if (data_stream[i].int48.data[47])
                data_stream[i].int48.data <= data_stream[i-1].int48.data;
              else
                data_stream[i].int48.data >= data_stream[i-1].int48.data;
            }
            else {
               data_stream[i].int32.data[31] == data_stream[0].int32.data[31];
              //negative numbers
              if (data_stream[0].int32.data[31])
                data_stream[i].int32.data <= data_stream[i-1].int32.data;
              else
                data_stream[i].int32.data >= data_stream[i-1].int32.data;
            }
          }
          else if (data_format inside {i1, pi1}) {
            if (cmd_desc.header.h_config[0]) {
              data_stream[i].int16.data[15] == data_stream[i-1].int16.data[15];
              if (data_stream[i].int16.data[15])
                data_stream[i].int16.data <= data_stream[i-1].int16.data;
              else
                data_stream[i].int16.data >= data_stream[i-1].int16.data;
            }
            else {
              data_stream[i].int8.data[7] == data_stream[i-1].int8.data[7];
              if (data_stream[i].int8.data[7])
                data_stream[i].int8.data <= data_stream[i-1].int8.data;
              else
                data_stream[i].int8.data >= data_stream[i-1].int8.data;
            }
          }
          else if (data_format inside {i0_f16, i1_f16, pi0_f16, pi1_f16}) {
            data_stream[i].fp16.sign == data_stream[i-1].fp16.sign;
            if (data_stream[i].fp16.sign)
              data_stream[i].fp16 <= data_stream[i-1].fp16;
            else
              data_stream[i].fp16 >= data_stream[i-1].fp16;
          }
          else if (data_format inside {i0_f24, i1_f24, pi0_f24, pi1_f24}) {
            data_stream[i].fp24.sign == data_stream[i-1].fp24.sign;
            if (data_stream[i].fp24.sign)
              data_stream[i].fp24 <= data_stream[i-1].fp24;
            else
              data_stream[i].fp24 >= data_stream[i-1].fp24;
          }
          else if (data_format inside {i0_f32, i1_f32, pi0_f32, pi1_f32}) {
            data_stream[i].fp32.sign == data_stream[i-1].fp32.sign;
            if (data_stream[i].fp32.sign)
              data_stream[i].fp32 <= data_stream[i-1].fp32;
            else
              data_stream[i].fp32 >= data_stream[i-1].fp32;
          }
        }
      }


      
      if (data_format inside {i0,pi0}) {
        if (!cmd_desc.header.h_config[0]) data_stream[i].int32.unusedint32 == 0;
      }
      else if (data_format inside {i1,pi1}) {
        if (cmd_desc.header.h_config[0]) data_stream[i].int16.unusedint16 == 0;
        else data_stream[i].int8.unusedint8 == 0;
      }
      else if (data_format inside {i0_f16, i1_f16, pi0_f16, pi1_f16}) {
        data_stream[i].fp16.unusedfp16 == 0;
        if (data_rnd_type == SUBNORMAL) {
          data_stream[i].fp16.exp == 0;
        }
        else if (data_rnd_type == NORMAL) {
          data_stream[i].fp16.exp inside {[1 : 'h1E]};
        }
        else if (data_rnd_type == INF) {
          data_stream[i].fp16.exp  == 'h1F;
          data_stream[i].fp16.frac == 0;
        }
        else if (data_rnd_type == NAN) {
          data_stream[i].fp16.exp  == 'h1F;
          data_stream[i].fp16.frac != 0;
        }
        else if (data_rnd_type == MINUS_ZERO) {
          data_stream[i].fp16.sign == 1;
          data_stream[i].fp16.exp  == 0;
          data_stream[i].fp16.frac == 0;
        }
      }
      else if (data_format inside {i0_f24, i1_f24, pi0_f24, pi1_f24}) {
        data_stream[i].fp24.unusedfp24 == 0;
        if (data_rnd_type == SUBNORMAL) {
          data_stream[i].fp24.exp == 0;
        }
        else if (data_rnd_type == NORMAL) {
          data_stream[i].fp24.exp inside {[1 : 'hFE]};
        }
        else if (data_rnd_type == INF) {
          data_stream[i].fp24.exp  == 'hFF;
          data_stream[i].fp24.frac == 0;
        }
        else if (data_rnd_type == NAN) {
          data_stream[i].fp24.exp  == 'hFF;
          data_stream[i].fp24.frac != 0;
        }
        else if (data_rnd_type == MINUS_ZERO) {
          data_stream[i].fp24.sign == 1;
          data_stream[i].fp24.exp  == 0;
          data_stream[i].fp24.frac == 0;
        }
      }
      else if (data_format inside {i0_f32, i1_f32, pi0_f32, pi1_f32}) {
        data_stream[i].fp32.unusedfp32 == 0;
        if (data_rnd_type == SUBNORMAL) {
          data_stream[i].fp32.exp == 0;
        }
        else if (data_rnd_type == NORMAL) {
          data_stream[i].fp32.exp inside {[1 : 'hFE]};
        }
        else if (data_rnd_type == INF) {
          data_stream[i].fp32.exp  == 'hFF;
          data_stream[i].fp32.frac == 0;
        }
        else if (data_rnd_type == NAN) {
          data_stream[i].fp32.exp  == 'hFF;
          data_stream[i].fp32.frac != 0;
        }
        else if (data_rnd_type == MINUS_ZERO) {
          data_stream[i].fp32.sign == 1;
          data_stream[i].fp32.exp  == 0;
          data_stream[i].fp32.frac == 0;
        }
      }
    }
  }


  /** Class Constructor */
  function new(string name="dpu_stream_sequence");
    super.new(name);
  endfunction

  task gen_data(int start,end_pos,iteration);
    `uvm_info(get_name, $sformatf("generating data: start: %0d, end: %0d, iteration: %0d", start, end_pos, iteration), UVM_HIGH)
    repeat (iteration) begin
      for (int i = start; i <= end_pos; i++)
          gen_data_and_write(prog_mem[i]);
    end
  endtask

  task body();
    super.body();

    if (ifd_config == IFD_NONE) `uvm_fatal(get_name, "Error! You should config ifd_config to either IFD0 or IFD1");

    `uvm_info(get_name, $sformatf("cmd received: %p", cmd_desc), UVM_HIGH)
    if (cmd_desc.header.format == aic_dp_cmd_gen_pkg::Bypass) begin
      prog_mem.delete();
      //bypass command is a mv with rfs = 1
      prog_mem[0].opcode  = OPC_UNARY;
      prog_mem[0].src1    = FUNC_MV64;
      prog_mem[0].src0    = i0_bp;
      prog_mem[0].dst     = l_bp;
      gen_data_and_write(prog_mem[0]);
    end
    else begin
      gen_data(cmd_desc.cmd.main_0.start, `_end_(cmd_desc.cmd.main_0), cmd_desc.cmd.main_0.iteration);
      if (cmd_desc.header.format >= aic_dp_cmd_gen_pkg::LoopsM2N0)
        gen_data(cmd_desc.cmd.main_1.start, `_end_(cmd_desc.cmd.main_1), cmd_desc.cmd.main_1.iteration);
      if (cmd_desc.header.format >= aic_dp_cmd_gen_pkg::LoopsM3N0)
        gen_data(cmd_desc.cmd.main_2.start, `_end_(cmd_desc.cmd.main_2), cmd_desc.cmd.main_2.iteration);
      if (cmd_desc.header.format inside {aic_dp_cmd_gen_pkg::LoopsM1N1, aic_dp_cmd_gen_pkg::LoopsM1N2,aic_dp_cmd_gen_pkg::LoopsM2N1, aic_dp_cmd_gen_pkg::LoopsM1N2, aic_dp_cmd_gen_pkg::LoopsM2N2, aic_dp_cmd_gen_pkg::LoopsM3N1, aic_dp_cmd_gen_pkg::LoopsM3N2})
        gen_data(cmd_desc.cmd.nested_0.start, `_end_(cmd_desc.cmd.nested_0), cmd_desc.cmd.nested_0.iteration);
      if (cmd_desc.header.format inside {aic_dp_cmd_gen_pkg::LoopsM1N2, aic_dp_cmd_gen_pkg::LoopsM1N2,aic_dp_cmd_gen_pkg::LoopsM2N2, aic_dp_cmd_gen_pkg::LoopsM3N2})
        gen_data(cmd_desc.cmd.nested_1.start, `_end_(cmd_desc.cmd.nested_1), cmd_desc.cmd.nested_1.iteration);
    end
    prog_mem.delete();
  endtask: body


  //check if any of the instruction's sources gets data from data stream inputs
  function src_t get_data_format(dpu_pkg::dpu_dp_cmd_t instr);
    bit s0_ifd, s1_ifd, s2_ifd;
    instr_src_t num_srcs = get_instr_num_srcs(instr);

    if (ifd_config == IFD0) begin
      s0_ifd = instr.src0 inside {[i0:pi0_f24]};
      s1_ifd = instr.src1 inside {[i0:pi0_f24]};
      s2_ifd = instr.src2 inside {[i0:pi0_f24]};
    end
    else begin
      s0_ifd = instr.src0 inside {[i1:pi1_f24]};
      s1_ifd = instr.src1 inside {[i1:pi1_f24]};
      s2_ifd = instr.src2 inside {[i1:pi1_f24]};
    end

    if (s0_ifd && num_srcs >= SINGLE_INSTR_SRC)
      return src_t'(instr.src0);

    //if they use the same source input , they will use the same input data
    if (s1_ifd && num_srcs >= DUAL_INSTR_SRC)
      return src_t'(instr.src1);

    if (s2_ifd && num_srcs == TRIPLE_INSTR_SRC)
      return src_t'(instr.src2);

    //don't care value, sources don't get data from ifds
    return a0;
  endfunction : get_data_format


  //properly packs the data according to data format specified in DPU ISA Spec: DATA Formats and Notation section
  function packed_data_queue_t pack_data(unpacked_data_t data, dpu_pkg::dpu_dp_cmd_t instr);
    packed_data_queue_t packed_data_q;
    bit s_i_f16, s_i_f24, s_i_f32;
    bit s_i_i32, s_i_i8, s_bp;
    bit req_data_i_int;
    instr_src_t num_srcs = get_instr_num_srcs(instr);
      s_bp = instr.src0 inside {i0_bp,pi0_bp,i1_bp,pi1_bp} && num_srcs >= SINGLE_INSTR_SRC ||
             instr.src1 inside {i0_bp,pi0_bp,i1_bp,pi1_bp} && num_srcs >= DUAL_INSTR_SRC ||
             instr.src2 inside {i0_bp,pi0_bp,i1_bp,pi1_bp} && num_srcs >= TRIPLE_INSTR_SRC;

    if (ifd_config == IFD0) begin

      s_i_i32 = instr.src0 inside {i0,pi0} && num_srcs >= SINGLE_INSTR_SRC ||
                instr.src1 inside {i0,pi0} && num_srcs >= DUAL_INSTR_SRC ||
                instr.src2 inside {i0,pi0} && num_srcs == TRIPLE_INSTR_SRC;

      s_i_f16 = instr.src0 inside {i0_f16,pi0_f16} && num_srcs >= SINGLE_INSTR_SRC ||
                instr.src1 inside {i0_f16,pi0_f16} && num_srcs >= DUAL_INSTR_SRC ||
                instr.src2 inside {i0_f16,pi0_f16} && num_srcs == TRIPLE_INSTR_SRC;
      
      s_i_f24 = instr.src0 inside {i0_f24,pi0_f24} && num_srcs >= SINGLE_INSTR_SRC ||
                instr.src1 inside {i0_f24,pi0_f24} && num_srcs >= DUAL_INSTR_SRC ||
                instr.src2 inside {i0_f24,pi0_f24} && num_srcs >= TRIPLE_INSTR_SRC;
      
      s_i_f32 = instr.src0 inside {i0_f32,pi0_f32} && num_srcs >= SINGLE_INSTR_SRC ||
                instr.src1 inside {i0_f32,pi0_f32} && num_srcs >= DUAL_INSTR_SRC ||
                instr.src2 inside {i0_f24,pi0_f24} && num_srcs == TRIPLE_INSTR_SRC;
    end                                    
    else begin                             
      s_i_i8  = instr.src0 inside {i1,pi1} && num_srcs >= SINGLE_INSTR_SRC ||
                instr.src1 inside {i1,pi1} && num_srcs >= DUAL_INSTR_SRC ||
                instr.src2 inside {i1,pi1} && num_srcs >= TRIPLE_INSTR_SRC;
      
      s_i_f16 = instr.src0 inside {i1_f16,pi1_f16} && num_srcs >= SINGLE_INSTR_SRC ||
                instr.src1 inside {i1_f16,pi1_f16} && num_srcs >= DUAL_INSTR_SRC ||
                instr.src2 inside {i1_f16,pi1_f16} && num_srcs == TRIPLE_INSTR_SRC;
      
      s_i_f24 = instr.src0 inside {i1_f24,pi1_f24} && num_srcs >= SINGLE_INSTR_SRC ||
                instr.src1 inside {i1_f24,pi1_f24} && num_srcs >= DUAL_INSTR_SRC ||
                instr.src2 inside {i1_f24,pi1_f24} && num_srcs == TRIPLE_INSTR_SRC;
      
      s_i_f32 = instr.src0 inside {i1_f32,pi1_f32} && num_srcs >= SINGLE_INSTR_SRC ||
                instr.src1 inside {i1_f32,pi1_f32} && num_srcs >= DUAL_INSTR_SRC ||
                instr.src2 inside {i1_f32,pi1_f32} && num_srcs == TRIPLE_INSTR_SRC;
    end

    req_data_i_int = !(s_i_f16 || s_i_f24 || s_i_f32);

    //f16x32 : 2 data streams needed to send all the 64 pwords
    //f32x16 : 4 data streams needed
    //i8,i32,bp 1 stream only
    //Check out DPU ISA: PWORD Packing section for more details
    if (req_data_i_int) begin
      packed_data_t packed_data;
      if (ifd_config == IFD0) begin
        //pword32 : int = 48 bits
        if (cmd_desc.header.h_config[0]) begin
          for (int i = 0, j = 0; i < PWORD_SIZE; i+=2, j++)
            packed_data[i*32 +: 48] = data[j];
          packed_data_q.push_back(packed_data);
        end
        else begin
          if (s_i_i32  || s_bp) begin
            //data is union, removing unused var
            for (int i = 0; i < PWORD_SIZE; i++)
              packed_data[i*32 +: 32] = data[i][31:0];
            packed_data_q.push_back(packed_data);
          end
          else begin
            for (int i = 0, j = 0; i < PWORD_SIZE; i++, j++) begin
              packed_data[j*64 +: 48] = data[i];
              if (i == 31 || i == 63) begin
                packed_data_q.push_back(packed_data);
                j = -1;
              end
            end
          end
        end
      end
      else begin
        //powrd32: int = 16 bits
        if (cmd_desc.header.h_config[0]) begin 
          for (int i = 0, j = 0; i < PWORD_SIZE; i+=2, j++)
            packed_data[i*8 +: 16] = data[j][15:0];
        end
        else begin
          if (s_i_i8 || s_bp) begin
            for (int i = 0; i < PWORD_SIZE; i++) 
              packed_data[i*8 +: 8] = data[i][7:0];
            packed_data_q.push_back(packed_data);
          end 
          else begin
            for (int i = 0, j = 0; i < PWORD_SIZE; i++, j++) begin
              packed_data[j*16 +:16] = data[i];
              if (i == 31 || i == 63) begin
                packed_data_q.push_back(packed_data);
                j = -1;
              end
            end
          end
        end
      end
    end
    else begin
      int num_packets = s_i_f16 ? 2 : (s_i_f24 ? 3 : 4);
      int stream_full = 64;
      int bit_pos;
      int data_idx;
      int pw_size = cmd_desc.header.h_config[0] ? 32 : PWORD_SIZE;
      packed_data_t packed_data;
      if (ifd_config == IFD0) 
        bit_pos = cmd_desc.header.h_config[0] ? 48 : 32;
      else
        bit_pos = cmd_desc.header.h_config[0] ? 16 : 8;

      for (int i = 0; i < pw_size; i++) begin
        for (int j = 0; j < num_packets; j++) begin
          packed_data[data_idx *bit_pos +: 8] = data[i][j*8 +: 8];
          data_idx++;
          if (data_idx >= stream_full) begin
            data_idx = 0;
            packed_data_q.push_back(packed_data);
          end
        end
      end
    end
    return packed_data_q;
  endfunction


  task gen_data_and_write(dpu_pkg::dpu_dp_cmd_t instr);
    packed_data_queue_t data_ifd_q;
    src_t dt_format = get_data_format(instr);
    
    `uvm_info(get_name, $sformatf("gen_data_and_write data_format: %p instr: %p, ", dt_format, instr ), UVM_HIGH)
    //don't generate data for these functions, they don't need data (takes data from internal regs)
    if (!(instr.opcode == OPC_UNARY && instr.src1 inside {FUNC_CLMV, FUNC_CHMV, FUNC_CLMVCL, FUNC_CLMVCH, FUNC_CHMVCL, FUNC_CHMVCH})) begin
      if (dt_format inside {[i0 : i0_f24], [pi0 : pi0_f24], [i1 : i1_f24], [pi1 : pi1_f24]}) begin
        `uvm_info(get_name, $sformatf("randomizing stream, data_type: %s,  data_format: %p instr: %p, ", data_rnd_type.name(), dt_format, instr ), UVM_HIGH)
        //generate a random number of data streams for rfs instructions
        if (instr.opcode inside {OPC_RFS,OPC_MADD_RFS}) begin
          int cnt = $urandom_range(1,4);
          repeat (cnt) begin
            if (instr.opcode == OPC_RFS && instr.src2 == FUNC_LUT && (ifd_config == IFD0 && instr.src1 inside {[i0:i0_f24]} ||
                                                                      ifd_config == IFD1 && instr.src1 inside {[i1:i1_f24]} )) 
              lut_bins_monotonically_inscrease = 1; 

            assert( this.randomize() with {data_format == dt_format;});
            data_ifd_q = {data_ifd_q, pack_data(data_stream, instr)};
          end
          `uvm_info(get_name, $sformatf("rfs instr, sending data stream: %p", data_ifd_q), UVM_HIGH)
          send_write(data_ifd_q);
        end
        else begin
          //src1 and src2 = a0: used to identify a MV before LUT operation
          if ( (instr.opcode == OPC_MV && instr.src1 == a0 && instr.src2 == a0)  ||
                instr.opcode == OPC_LUT && instr.src2 == FUNC_LUT && (ifd_config == IFD0 && instr.src1 inside {[i0:i0_f24]} ||
                                                                      ifd_config == IFD1 && instr.src1 inside {[i1:i1_f24]} )) begin
            lut_bins_monotonically_inscrease = 1;
            `uvm_info(get_name, "generated OPC_LUT bins data", UVM_HIGH)
            assert( this.randomize() with {data_format == dt_format;});
            data_ifd_q = {data_ifd_q, pack_data(data_stream, instr)};
            for (int i = 0; i < 16; i++) begin
              //`uvm_info(get_name, $sformatf("bins[%0d] : %0h <%0h, %0h, %0h>", i, data_stream[i], data_stream[i].fp16.sign, data_stream[i].fp16.exp, data_stream[i].fp16.frac), UVM_HIGH)
              `uvm_info(get_name, $sformatf("bins[%0d] : %0h %0d", i, data_stream[i].int32.data, $signed(data_stream[i].int32.data)), UVM_HIGH)
            end
          end
          else begin
            assert( this.randomize() with {data_format == dt_format;});
            data_ifd_q = {data_ifd_q, pack_data(data_stream, instr)};

            //MV64 in PW32 mode: double the data to mv all 64 pwords
            if (instr.opcode == OPC_UNARY && instr.src1 == FUNC_MV64 && cmd_desc.header.h_config[0]) begin  
              assert( this.randomize() with {data_format == dt_format;});
              data_ifd_q = {data_ifd_q, pack_data(data_stream, instr)};
            end
          end

          lut_bins_monotonically_inscrease = 0;
          `uvm_info(get_name, $sformatf("instr: %p sending data stream: \n %p", instr, data_ifd_q), UVM_HIGH)
          send_write(data_ifd_q);
        end
      end
    end
    else
      `uvm_info(get_name, "data not generated, invalid instr", UVM_HIGH)
  endtask


  task send_write(packed_data_queue_t data_q);
    bit status;
    svt_axi_master_transaction trans;
    svt_configuration get_cfg;
    p_sequencer.get_cfg(get_cfg);

    if (!$cast(cfg, get_cfg))
      `uvm_fatal(get_name, "Unable to $cast the configuration to a svt_axi_port_configuration class");

    if (data_q.size() == 0)
      `uvm_fatal(get_name, "Writing data with size = 0!")

    `uvm_info(get_name, $sformatf("Sending data stream with length: %0d", data_q.size()), UVM_HIGH)
    `uvm_create(trans)
    trans.port_cfg            = cfg;
    trans.xact_type           = svt_axi_transaction::DATA_STREAM;
    trans.enable_interleave   = 0;
    trans.stream_burst_length = data_q.size();
    trans.tdata               = new[trans.stream_burst_length];
    trans.tvalid_delay        = new[trans.stream_burst_length];
/*
    if (ifd_config == IFD1) begin
      bit [IFD1_STREAM_SIZE-1 : 0] packed_data_ifd1_q [$];
      foreach (data_q[i])
        packed_data_ifd1_q[i] = data_q[i][IFD1_STREAM_SIZE-1 : 0];
      trans.tdata = packed_data_ifd1_q;
    end
    else
*/
      trans.tdata = data_q;

    foreach (trans.tdata[i])
      trans.tvalid_delay[i] = $urandom_range(0,2);

    `uvm_send(trans)
    get_response(rsp);
    `uvm_info(get_name, "Done", UVM_HIGH)
  endtask

endclass: dpu_stream_sequence
`endif
