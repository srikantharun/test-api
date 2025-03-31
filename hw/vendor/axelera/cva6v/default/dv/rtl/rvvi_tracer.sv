module rvvi_tracer 
  import cva6v_ariane_pkg::*;
#(
  parameter cva6v_config_pkg::cva6_cfg_t CVA6Cfg = cva6v_config_pkg::cva6_cfg_empty,
  parameter type rvvi_instr_t = logic,
  //
  parameter logic [7:0] HART_ID      = '0,
  parameter int unsigned DEBUG_START = 0,
  parameter int unsigned DEBUG_STOP  = 0,
  parameter int unsigned MAX_V_WB    = 8, // max number of asserted bits in v_wb
  parameter int unsigned INTERMEDIATE_INSTR_COMPARE_NUM = 200, // number of intermediate txns to be compared, to not overload the 'final' block
  parameter int unsigned MAX_INSTR_COMPARE_NUM = 32000
)(
  input logic                           clk_i,
  input logic                           rst_ni,
  input rvvi_instr_t                    rvvi_i
);

  typedef struct {
    logic[63:0]  order;
    int unsigned index;
    string       instruction;
    logic[63:0]  instr_code;
    logic[63:0]  pc;
  } rvvi_ordered_inst_t;

  typedef struct {
    logic [63:0] start;
    logic [63:0] stop;
  } trap_idx_pair_t;

  typedef enum int {
    IDLE = 0,
    TRAP = 1,
    IRQ_TRAP_TAKEN = 2
  } irq_trap_taken_state_t;

  int                 f;
  logic [63:0]        pc64;
  int                 reg_index;
  int                 instr_size;
  int                 intermediate_instr_size;
  rvvi_ordered_inst_t ordered_instr_q [$];
  rvvi_ordered_inst_t ordered_instr_entry;
  rvvi_ordered_inst_t for_printing;
  rvvi_ordered_inst_t intermediate_for_printing;
  bit                 is_skipped = 0;
  bit                 stop_sampling = 0;

  // Declare an array of opcodes as constants
  localparam [31:0] EXIT_INSTR [3:0] = {
        32'h00100073,  // EBREAK opcode
        32'h00009002,  // C.EBREAK opcode
        32'h00000073,  // ECALL opcode
        32'h10500073   // WFI opcode
  };

  // IRQ handling logic
  trap_idx_pair_t irq_trap_idxs_q[$];
  trap_idx_pair_t irq_trap_idxs;
  irq_trap_taken_state_t irq_trap_taken_state = IDLE;
  int irq_trap_taken_cnt = 0;
  bit begin_irq_driving = 0;
  bit end_irq_driving = 0;

  initial begin
    f = $fopen($sformatf("trace_rvvi_hart_%h.dasm", HART_ID), "w");
  end

  final begin
    $display("IRQ Trap taken count: %d", irq_trap_taken_cnt);
    sort_rvvi_instr();
    drop_irq_handler_instructions();
    instr_size = ordered_instr_q.size();
    for (int j=0; j < instr_size; j++) begin
      for_printing = ordered_instr_q.pop_front();
      $fwrite(f, for_printing.instruction);
    end
    $fclose(f);
  end

  always_ff @(posedge clk_i) begin
    for (int i = 0; i < CVA6Cfg.NrCommitPorts; i++) begin
      pc64 = rvvi_i.pc_rdata[i];
      ordered_instr_entry.order = rvvi_i.order[i];
      ordered_instr_entry.pc = pc64;

      // Begin IRQ related logic
      if ($test$plusargs("enable_irqs")) begin
        if (rvvi_i.trap[i] == 1'b1) begin
          irq_trap_taken_state <= TRAP;
            irq_trap_idxs.start = ordered_instr_entry.order+1; // speculative start of trap handling order
        end else if (
          irq_trap_taken_state == IRQ_TRAP_TAKEN
          && rvvi_i.valid[i]
          && (rvvi_i.insn[i] == 64'h30200073 || rvvi_i.insn[i] == 64'h10200073)
        ) begin
          irq_trap_taken_cnt++;
          irq_trap_idxs.stop = ordered_instr_entry.order;
          irq_trap_idxs_q.push_back(irq_trap_idxs);
          $display(
            "[%t] %s for IRQ TRAP - resume sampling! Idxs %p",
            $time,
            (rvvi_i.insn[i] == 64'h30200073 ? "MRET" : "SRET"),
            irq_trap_idxs
          );
          irq_trap_taken_state <= IDLE;
        end else if (irq_trap_taken_state == TRAP) begin
          // csr update has 1-cycle delay i.r.t. trap_taken
          if (rvvi_i.csr[0][cva6v_riscv::CSR_MCAUSE][63] == 1'b1) begin
            irq_trap_taken_state <= IRQ_TRAP_TAKEN;
            if (i == 0) begin // print once
              $display("[%t] IRQ TRAP taken!", $time);
            end
          end else begin
            irq_trap_taken_state <= IDLE;
            irq_trap_idxs.start = '0;
            irq_trap_idxs.stop = '0;
          end
        end
        // Detect start of IRQ driving - .word 0 (unimp)
        if (rvvi_i.valid[i] && rvvi_i.insn[i] == 32'h00000000) begin
          begin_irq_driving = 1;
          $display("[%t] UNIMP detected - start driving IRQs!", $time);
        end
        // Detect end of test - ECALL
        if (rvvi_i.valid[i] && rvvi_i.insn[i] == 32'h00000073) begin
          end_irq_driving = 1;
          $display("[%t] ECALL detected - stop driving IRQs!", $time);
        end
      end
      // END of IRQ related logic

      // print the instruction information if the instruction is valid provided it is not a trap (with the exception of EXIT_INSTR)
      if (rvvi_i.valid[i] && (!rvvi_i.trap[i] || rvvi_i.insn[i] inside {EXIT_INSTR})) begin
        // Instruction information
        ordered_instr_entry.instruction = $sformatf("core   0: 0x%h (0x%h) DASM(%h)\n", pc64, rvvi_i.insn[i], rvvi_i.insn[i]);

        // Destination register information
        if (rvvi_i.insn[i][1:0] != 2'b11) begin
          $sformat(ordered_instr_entry.instruction, "%s%h 0x%h (0x%h)", ordered_instr_entry.instruction, rvvi_i.mode[i], pc64, rvvi_i.insn[i][15:0]);
          ordered_instr_entry.instr_code = rvvi_i.insn[i][15:0];
        end else begin
          $sformat(ordered_instr_entry.instruction, "%s%h 0x%h (0x%h)", ordered_instr_entry.instruction, rvvi_i.mode[i], pc64, rvvi_i.insn[i]);
          ordered_instr_entry.instr_code = rvvi_i.insn[i];
        end
        // Check vector
        if (rvvi_i.v_wb[i] != 0) begin
          check_v_wb(rvvi_i.v_wb[i]);
          for (int j=0; j < 32; j++) begin
            if (rvvi_i.v_wb[i][j] == 1'b1) begin
              $sformat(ordered_instr_entry.instruction, "%s v%0d 0x%h", ordered_instr_entry.instruction, j, rvvi_i.v_wdata[i][j]);
            end
          end
        // Check FP
        end else if (rvvi_i.f_wb[i]!=0) begin
            reg_index = get_single_index(.bits(rvvi_i.f_wb[i]), .skip0(0)); // F0 is valid
            $sformat(ordered_instr_entry.instruction, "%s f%2d 0x%h", ordered_instr_entry.instruction, reg_index, rvvi_i.f_wdata[i][reg_index]);
        // Check X register
        end else if (rvvi_i.x_wb[i] != 0) begin
          reg_index = get_single_index(.bits(rvvi_i.x_wb[i]), .skip0(1)); // ignore X0
          if (reg_index != -1) begin
            $sformat(ordered_instr_entry.instruction, "%s x%2d 0x%h", ordered_instr_entry.instruction, reg_index, rvvi_i.x_wdata[i][reg_index]);
          end
        end
        $sformat(ordered_instr_entry.instruction, "%s\n", ordered_instr_entry.instruction);

        ordered_instr_entry.index = ordered_instr_q.size();

        // TODO: Spike does not go to trap handler when doing wfi/ecall in U-mode
        if (rvvi_i.trap[i]==1'b1 && rvvi_i.insn[i]==32'h10500073) begin
          stop_sampling = 1;
        end
        if (!stop_sampling) begin
          ordered_instr_q.push_back(ordered_instr_entry);
        end

        if (ordered_instr_q.size()>=INTERMEDIATE_INSTR_COMPARE_NUM && irq_trap_taken_state == IDLE) begin
          is_skipped = check_skipped_number();
          if (is_skipped==0 || ordered_instr_q.size()>=MAX_INSTR_COMPARE_NUM) begin
          //if (is_skipped==0) begin
            sort_rvvi_instr();
            drop_irq_handler_instructions();
            intermediate_instr_size = ordered_instr_q.size();
            for (int j=0; j < intermediate_instr_size; j++) begin
              intermediate_for_printing = ordered_instr_q.pop_front();
              $fwrite(f, intermediate_for_printing.instruction);
            end
          end
        end

      end
    end
  end

  function automatic int get_single_index(input logic [31:0] bits, bit skip0=0);
    int start = skip0;
    for (int i = start; i < 32; i++) begin
      if (bits[i] == 1'b1) begin
        return i;
      end
    end
    return -1;
  endfunction

  function automatic void check_v_wb(logic[31:0] v_wb);
    if ($countones(v_wb) > MAX_V_WB) begin
      $error("Max number of asserted bits exceeded! Expected: %0d Actual: %0d", MAX_V_WB, $countones(v_wb));
    end
  endfunction

  function automatic void sort_rvvi_instr();
    automatic int unsigned current_order, last_order;
    automatic int unsigned first_indx[$], last_indx[$];
    automatic rvvi_ordered_inst_t instr_copy_q[$];

    ordered_instr_q.sort(x) with (x.order); // order only guaranteed, need index as well
    current_order = ordered_instr_q[0].order;
    last_order = ordered_instr_q[$].order;

    for (int curr_ordr=current_order; curr_ordr <= last_order; curr_ordr++) begin

      first_indx = ordered_instr_q.find_first_index(w) with (w.order == curr_ordr);
      last_indx  = ordered_instr_q.find_last_index(w) with (w.order == curr_ordr);

      if (first_indx.size()!=0 && last_indx.size() !=0 && first_indx[0]!=last_indx[0]) begin

        instr_copy_q.delete();
        for (int i=first_indx[0]; i <= last_indx[0]; i++) begin
          ordered_instr_entry = ordered_instr_q[i];
          instr_copy_q.push_back(ordered_instr_entry);
        end
        instr_copy_q.sort(x) with (x.index);
        for (int i=first_indx[0]; i <= last_indx[0]; i++) begin
          ordered_instr_q[i] = instr_copy_q[i-first_indx[0]];
        end
      end
    end
  endfunction

  function bit check_skipped_number();
    int order_q[$];
    int min_val[$], max_val[$];
    int i;
    bit skip_found;

    order_q.delete();
    foreach (ordered_instr_q[i]) begin
      order_q.push_back(ordered_instr_q[i].order);
    end

     // Return 0 if the queue is empty or has only one element
    if (order_q.size() <= 1) begin
      return 0;
    end

    // Use built-in min() and max() to find the minimum and maximum values
    min_val = order_q.min();
    max_val = order_q.max();

    // Check if any number is skipped between min_val and max_val
    skip_found = 0;
    for (i = min_val[0]; i <= max_val[0]; i++) begin
      if (!(i inside {order_q})) begin
        skip_found = 1;
        break;
      end
    end

    return skip_found;
  endfunction

  function automatic void drop_irq_handler_instructions();
    trap_idx_pair_t current_irq_trap_idxs;
    int loop_start_idx = 0;
    while (irq_trap_idxs_q.size() > 0) begin
      current_irq_trap_idxs = irq_trap_idxs_q.pop_front();
      $display("Popping IRQ handler instructions with order values: %p, starting new loop from idx %0d oredered_instr_q_size %0d, first instr order %0d", current_irq_trap_idxs, loop_start_idx, ordered_instr_q.size(), ordered_instr_q[0].order );
      for (int i = loop_start_idx; i < ordered_instr_q.size(); i++) begin
        if (ordered_instr_q[i].order >= current_irq_trap_idxs.start && ordered_instr_q[i].order <= current_irq_trap_idxs.stop) begin
          //$display("Popping instr w order: %0d", ordered_instr_q[i].order);
          ordered_instr_q.delete(i);
          i--; // adjust index to account for removal
        end else if (ordered_instr_q[i].order > current_irq_trap_idxs.stop) begin
          loop_start_idx = i; // start next iteration from here
          break;
        end
      end
    end
  endfunction


endmodule // rvvi_tracer
