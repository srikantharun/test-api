// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>


/// Execute an instruction / Distribute work to the respective sub-units.
///
/// The execution unit does the final decoding of the instruction stream and generates downstream commands for the
/// sub-units.  It is responsible of generating the correct addresses for the copy instructions when they are
/// translated into a copy command.  The unit has storage space for one instruction and assiciated metadata which it is
/// currently processing.  The decision into which state to jump depends on the valid intruction at the input stream.
///
/// !!! warning "In-Flight Instructions"
///
///     Instructions that reach this unit are considered in flight and will execute even if they cause a downstream error!
///
///
/// ## Finite State Machine
///
/// For the control handshaking a `FSM` is used.  Each instruction type corresponds to a state and `FSM` can transition
/// between any state.  It starts in the `IDLE` state and jumps into a respective instruction execution
/// state the moment a valid instruction is applied.  The moment the instruction stream becomes idle again it will
/// go back into the `IDLE` state the moment the instruction is executed.  There exists a special `EXE_DONE` state which
/// it will automatically jump into when the last instruction of a task list has been executed.  There it waits until
/// all downstream units indicate that they are idle.  This mechanism is mainly there to stall the execution unit of
/// starting a new task list before the previous one has finished.
///
/// !!! tip "Instruction Ordering"
///
///     The unit will only send out multiple instructions of the same type.  When the next instruction is of a different
///     type, the dispatch will wait until the other downstream execution units are idle.  This is to prevent instructions
///     form complteing out of order.  However limits the throughput depending on task-list layout.
///
///     !!! success "Task-List Performance"
///
///         When designing task list try to group as many of the same instruciton types together for optimal performance.
///
///
/// | State           | Description                                                                                                              |
/// |:--------------- |:------------------------------------------------------------------------------------------------------------------------ |
/// | `IDLE`          | The unit is idle and not executing anything. Will jump into a `EXE_*` state when there is a new valid instruction.       |
/// | `EXE_COMMAND`   | Calucate the copy values for a command copy operation and perform the handshake to the copy unit.                        |
/// | `EXE_PROGRAM`   | Calucate the copy values for a program copy operation and perform the handshake to the copy unit.                        |
/// | `EXE_TOKEN`     | Perform the handshake to the token unit.                                                                                 |
/// | `EXE_TIMESTAMP` | Send out the timestamp pulse.                                                                                            |
/// | `EXE_DONE`      | Is jumped to on any instruction marked as `last`. Will wait until all downstream units are idle and send the done pulse. |
///
module aic_cd_execute #(
  /// The number of destinations the unit interacts with
  parameter int unsigned NumDestinations = 17
)(
  /// Clock, positive edge triggered
  input  wire  i_clk,
  /// Asynchronous reset, active low
  input  wire  i_rst_n,

  ////////////
  // Status //
  ////////////
  /// We are not idle
  output logic o_busy,
  /// The token unit is busy
  input  logic i_token_unit_busy,
  /// The copy unit is busy
  input  logic i_copy_unit_busy,
  /// The task list has been completed
  output logic o_task_list_done,

  ///////////////////////////////////////////
  // Control Dispatcher Instruction Stream //
  ///////////////////////////////////////////
  /// The fetched and validated instruction
  input  aic_cd_pkg::instruction_t           i_instruction,
  /// The control offset belonging to this instruction
  input  aic_cd_pkg::control_offset_t        i_instruction_control_offset,
  /// The index of the transaction
  input  aic_cd_pkg::task_list_word_length_t i_instruction_index,
  /// This is the last instruction of this respective command
  input  logic                               i_instruction_last,
  /// This instruction is valid
  input  logic                               i_instruction_valid,
  /// Ready flag for the instruction
  output logic                               o_instruction_ready,

  //////////////////
  // Copy Request //
  //////////////////
  /// The copy command
  output aic_cd_pkg::copy_command_t   o_copy_command,
  /// The copy command is valid
  output logic                        o_copy_command_valid,
  /// Dowstream consumes copy command
  input  logic                        i_copy_command_ready,

  ///////////////////
  // Token Request //
  ///////////////////
  /// The token opcode
  output aic_cd_pkg::token_opcode_e   o_token_opcode,
  /// The mask which lines to trigger
  output aic_cd_pkg::token_mask_t     o_token_mask,
  /// The request is valid
  output logic                        o_token_valid,
  /// The request is ready / Has been done
  input  logic                        i_token_ready,

  ///////////////
  // Timestamp //
  ///////////////
  /// The id of the timestamp
  output aic_cd_pkg::timestamp_trigger_id_t o_timestamp_id,
  /// The pulse that the timestamp is active
  output logic                              o_timestamp_active_pulse,

  ///////////////////////
  // Config from CSR's //
  ///////////////////////
  /// The global address offset that must be added to all copy transactions
  input  axi_pkg::axi_largest_addr_t  i_aic_base_addr,
  /// The offset to the source data which is added to all copy transaction reads
  input  axi_pkg::axi_largest_addr_t  i_ctrl_data_base_addr,
  /// Address map of the destination command memory base address
  input  axi_pkg::axi_largest_addr_t  i_destination_addr_command[NumDestinations],
  /// Address map of the destination program memory base address
  input  axi_pkg::axi_largest_addr_t  i_destination_addr_program[NumDestinations]

);

  typedef enum logic [2:0] {
    IDLE,
    EXE_COMMAND,
    EXE_PROGRAM,
    EXE_TOKEN,
    EXE_TIMESTAMP,
    EXE_DONE
  } state_e;
  state_e                             state_q, state_d;
  logic                               state_change;
  aic_cd_pkg::instruction_t           instruction_q;
  aic_cd_pkg::control_offset_t        instruction_control_offset_q;
  aic_cd_pkg::task_list_word_length_t instruction_index_q;
  logic                               instruction_last_q;

  always_comb o_busy = (state_q != IDLE);

  // We only care if we switch execution types that a unit was busy, so we can delay the flagyby one cycle.
  // This breaks a combinational loop.
  logic token_unit_busy_q;
  logic copy_unit_busy_q;
  // DFFR: D-Flip-Flop, asynchronous low reset
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n) begin
      token_unit_busy_q <= 1'b0;
      copy_unit_busy_q  <= 1'b0;
    end else begin
      token_unit_busy_q <= i_token_unit_busy;
      copy_unit_busy_q  <= i_copy_unit_busy;
    end
  end

  // DFFRL: D-Flip-Flop, asynchronous low reset, load enable
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n)          state_q <= IDLE;
    else if (state_change) state_q <= state_d;
  end

  // DFFRL: D-Flip-Flop, asynchronous low reset, load enable
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n) begin
      instruction_q                <= aic_cd_pkg::instruction_t'(0);
      instruction_control_offset_q <= aic_cd_pkg::control_offset_t'(0);
      instruction_index_q          <= aic_cd_pkg::task_list_word_length_t'(0);
      instruction_last_q           <= 1'b0;
    end else if (i_instruction_valid && o_instruction_ready) begin
      instruction_q                <= i_instruction;
      instruction_control_offset_q <= i_instruction_control_offset;
      instruction_index_q          <= i_instruction_index;
      instruction_last_q           <= i_instruction_last;
    end
  end

  //////////////////////////
  // Finite State Machine //
  //////////////////////////

  /// Update to the correct state in the execution
  ///
  /// Ussage: update_execution_state(i_instruction, i_instruction_valid, instruction_last_q, o_instruction_ready, state_d, state_change);
  function automatic void update_execution_state (
    input  aic_cd_pkg::instruction_t instruction,
    input  logic                     instruction_valid,
    input  logic                     instruction_last,
    output logic                     instruction_ready,
    output state_e                   next_state
  );
    instruction_ready = 1'b0;
    next_state        = IDLE;

    if (instruction_last) begin
      next_state = EXE_DONE;
    end else if (instruction_valid) begin
      instruction_ready = 1'b1;
      unique case (aic_cd_pkg::get_opcode(instruction))
        aic_cd_pkg::OpcodeCommand:   next_state = EXE_COMMAND;
        aic_cd_pkg::OpcodeProgram:   next_state = EXE_PROGRAM;
        aic_cd_pkg::OpcodeToken:     next_state = EXE_TOKEN;
        aic_cd_pkg::OpcodeTimestamp: next_state = EXE_TIMESTAMP;
        default: /* Go to IDLE, is guarded by instruction validate */;
      endcase
    end
  endfunction

  always_comb begin
    state_d              = state_q;
    state_change         = 1'b0;
    o_instruction_ready  = 1'b0;

    o_copy_command       = aic_cd_pkg::copy_command_t'(0);
    o_copy_command_valid = 1'b0;

    o_token_opcode       = aic_cd_pkg::token_opcode_e'(aic_cd_pkg::TokenConsumeLocal);
    o_token_mask         = aic_cd_pkg::token_mask_t'(0);
    o_token_valid        = 1'b0;

    o_timestamp_id           = aic_cd_pkg::timestamp_trigger_id_t'(0);
    o_timestamp_active_pulse = 1'b0;

    o_task_list_done = 1'b0;

    unique case (state_q)
      IDLE: begin
        if (i_instruction_valid) begin
          o_instruction_ready = 1'b1;
          state_change        = 1'b1;
          unique case (aic_cd_pkg::get_opcode(i_instruction))
            aic_cd_pkg::OpcodeCommand:   state_d = EXE_COMMAND;
            aic_cd_pkg::OpcodeProgram:   state_d = EXE_PROGRAM;
            aic_cd_pkg::OpcodeToken:     state_d = EXE_TOKEN;
            aic_cd_pkg::OpcodeTimestamp: state_d = EXE_TIMESTAMP;
            default: /* do nothing */;
          endcase
        end
      end
      EXE_COMMAND: begin
        o_copy_command = '{
          opcode:             aic_cd_pkg::OpcodeCommand,
          instruction_index:  instruction_index_q,
          num_words:          aic_cd_pkg::num_words_to_copy(instruction_q),
          num_bytes:          aic_cd_pkg::copy_byte_length_t'(instruction_q.view_command.length),
          patch_id_1:         instruction_q.view_command.patch_id_1,
          patch_id_0:         instruction_q.view_command.patch_id_0,
          patch_mode:         instruction_q.view_command.patch_mode,
          destination_id:     instruction_q.view_command.dst_id,
          addr_destination:   axi_pkg::axi_largest_addr_t'(i_aic_base_addr)
                            + axi_pkg::axi_largest_addr_t'(i_destination_addr_command[instruction_q.view_command.dst_id]),
          addr_source:        axi_pkg::axi_largest_addr_t'(i_aic_base_addr)
                            + axi_pkg::axi_largest_addr_t'(i_ctrl_data_base_addr)
                            + axi_pkg::axi_largest_addr_t'(instruction_control_offset_q)
                            + axi_pkg::axi_largest_addr_t'(instruction_q.view_command.command_ptr),
          default: '0
        };
        if (!token_unit_busy_q) begin
          o_copy_command_valid = 1'b1;
          if (i_copy_command_ready) begin
            update_execution_state(i_instruction, i_instruction_valid, instruction_last_q, o_instruction_ready, state_d);
            state_change = 1'b1;
          end
        end
      end
      EXE_PROGRAM: begin
        o_copy_command = '{
          opcode:             aic_cd_pkg::OpcodeProgram,
          instruction_index:  instruction_index_q,
          num_words:          aic_cd_pkg::num_words_to_copy(instruction_q),
          num_bytes:          aic_cd_pkg::copy_byte_length_t'(instruction_q.view_program.length),
          destination_id:     instruction_q.view_program.dst_id,
          addr_destination:   axi_pkg::axi_largest_addr_t'(i_aic_base_addr)
                            + axi_pkg::axi_largest_addr_t'(i_destination_addr_program[instruction_q.view_program.dst_id])
                            + axi_pkg::axi_largest_addr_t'(instruction_q.view_program.dst_address),
          addr_source:        axi_pkg::axi_largest_addr_t'(i_aic_base_addr)
                            + axi_pkg::axi_largest_addr_t'(i_ctrl_data_base_addr)
                            + axi_pkg::axi_largest_addr_t'(instruction_control_offset_q)
                            + axi_pkg::axi_largest_addr_t'(instruction_q.view_program.program_ptr),
          default: '0
        };
        if (!token_unit_busy_q) begin
          o_copy_command_valid = 1'b1;
          if (i_copy_command_ready) begin
            update_execution_state(i_instruction, i_instruction_valid, instruction_last_q, o_instruction_ready, state_d);
            state_change = 1'b1;
          end
        end
      end
      EXE_TOKEN: begin
        o_token_opcode = instruction_q.view_token.token_opcode;
        o_token_mask   = instruction_q.view_token.token_mask;
        if (!copy_unit_busy_q) begin
          o_token_valid  = 1'b1;
          if (i_token_ready) begin
            update_execution_state(i_instruction, i_instruction_valid, instruction_last_q, o_instruction_ready, state_d);
            state_change = 1'b1;
          end
        end
      end
      EXE_TIMESTAMP: begin
        if (!token_unit_busy_q && !copy_unit_busy_q) begin
          o_timestamp_id           = instruction_q.view_timestamp.id;
          o_timestamp_active_pulse = 1'b1;
          update_execution_state(i_instruction, i_instruction_valid, instruction_last_q, o_instruction_ready, state_d);
          state_change = 1'b1;
        end
      end
      EXE_DONE: begin
        if (!token_unit_busy_q && !copy_unit_busy_q) begin
          o_task_list_done = 1'b1;
          state_d          = IDLE;
          state_change     = 1'b1;
        end
      end
      default: state_change = 1'b1;
    endcase
  end
endmodule
