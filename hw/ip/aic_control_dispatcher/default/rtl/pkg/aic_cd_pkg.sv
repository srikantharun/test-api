// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>


/// Static parameters and typedefs for the AI-Core Control Dispatcher
///
package aic_cd_pkg;

  ////////////////////////////
  // AXI Subordinate values //
  ////////////////////////////

  /// The number of subordinate endpoints
  parameter  int unsigned NUM_AXI_ENDPOINTS = 2;

  /// The name and index mapping of the endpoint
  typedef enum int unsigned {
    ENDPOINT_CSR = 0,
    ENDPOINT_CMD = 1
  } axi_sub_index_e;

  /////////////////////////////////
  // Base Struct for the Command //
  /////////////////////////////////

  /// The width of the Task List Pointer in Bits
  parameter int unsigned TASK_LIST_POINTER_WIDTH = 16;
  /// Type definition of the task list pointerf
  typedef logic [TASK_LIST_POINTER_WIDTH-1:0] task_list_pointer_t;

  /// The width of the Task List Length in Bits
  parameter int unsigned TASK_LIST_LENGTH_WIDTH = 16;
  /// Type definition of the task list pointer
  typedef logic [TASK_LIST_LENGTH_WIDTH-1:0]  task_list_word_length_t;

  /// The width of the Task List control Offset in Bits
  parameter int unsigned CONTROL_OFFSET_WIDTH = 24;
  /// Type definition of the task list pointer
  typedef logic [CONTROL_OFFSET_WIDTH-1:0]   control_offset_t;

  /// The width of an AIC_CD command
  parameter int unsigned AicCdCommandWidth =
      TASK_LIST_POINTER_WIDTH
    + TASK_LIST_LENGTH_WIDTH
    + CONTROL_OFFSET_WIDTH;

  ////////////////////////////////////////////////
  /// Struct for representing an AIC CD command //
  typedef struct packed {
    /// Address offset for the controll operations
    control_offset_t        control_offset;
    /// Length of the Task List
    task_list_word_length_t task_list_length;
    /// Pointer to the task List
    task_list_pointer_t     task_list_pointer;
  } aic_cd_command_struct_t;

  /// Union to represent the different commands
  typedef union packed {
    logic [AicCdCommandWidth-1:0] view_vector;
    aic_cd_command_struct_t       view_struct;
  } aic_cd_command_t;

  //////////////////
  // Instructions //
  //////////////////

  /// The width of an AIC_CD Instruction
  parameter int unsigned INSTRUCTION_WIDTH = 64;

  /// The Operation Code Width
  parameter int unsigned OPCODE_WIDTH = 2;
  /// The type definition for an Operation Code
  typedef logic [OPCODE_WIDTH-1:0] opcode_t;
  /////////////////////////////////////////////////////
  /// The type definition enum for an Operation Code //
  typedef enum opcode_t {
    OpcodeCommand   = opcode_t'(0),
    OpcodeProgram   = opcode_t'(2),
    OpcodeToken     = opcode_t'(1),
    OpcodeTimestamp = opcode_t'(3)
  } opcode_e;

  /// The width of the destination ID
  parameter int unsigned DESTINATION_ID_WIDTH = 6;
  /// Type definition for the destination ID
  typedef logic [DESTINATION_ID_WIDTH-1:0] destination_id_t;

  //////////////////////////////
  // Command Copy Instruction //
  /// The width of the command Pointer
  parameter int unsigned COMMAND_POINTER_WIDTH = 24;
  /// Type definition of the pointer
  typedef logic [COMMAND_POINTER_WIDTH-1:0] command_pointer_t;

  /// The width of the patch identification fields
  parameter int unsigned PATCH_ID_WIDTH = 8;
  /// Type definition of the pointer
  typedef logic [PATCH_ID_WIDTH-1:0] patch_id_t;

  /// The width of the command length fields
  parameter int unsigned COMMAND_BYTE_LENGTH_WIDTH = 8;
  /// Type definition of the pointer
  typedef logic [COMMAND_BYTE_LENGTH_WIDTH-1:0] command_byte_length_t;

  /// The width of the patch mode field
  parameter int unsigned PATCH_MODE_WIDTH = 8;
  /// Type definition of the pointer
  typedef logic [PATCH_MODE_WIDTH-1:0] patch_mode_t;

  //////////////////////////////////////////////////////////////////
  /// The type definition struct for the command copy instruction //
  typedef struct packed {
    /// Patch mode selection indicating the address patching pattern to be applied to the command (configurable via CSR)
    patch_mode_t          patch_mode;
    /// Byte length of the AI Core Block command
    command_byte_length_t length;
    /// ID of the base address of the memory pool address for the second address patching of the selected patch mode (configurable via CSR)
    patch_id_t            patch_id_1;
    /// ID of the base address of the memory pool address for the first address patching of the selected patch mode (configurable via CSR)
    patch_id_t            patch_id_0;
    /// Byte pointer to the first word of the AI Core Block command located in the control data memory region (can be offset by control_offset)
    command_pointer_t     command_ptr;
    /// ID of the destination AI Core Block (lookup for address map)
    destination_id_t      dst_id;
    /// Operation Code
    opcode_e              opcode;
  } command_instruction_t;

  //////////////////////////////
  // Program Copy Instruction //
  /// The width of the program Pointer
  parameter int unsigned PROGRAMM_POINTER_WIDTH = 24;
  /// Type definition of the pointer
  typedef logic [PROGRAMM_POINTER_WIDTH-1:0] program_pointer_t;

  /// The width of the destination address
  parameter int unsigned DESTINATION_ADDRESS_WIDTH = 16;
  /// Type definition of the pointer
  typedef logic [DESTINATION_ADDRESS_WIDTH-1:0] destination_address_t;

  /// The width of the program length fields
  parameter int unsigned PROGRAM_BYTE_LENGTH_WIDTH = 16;
  /// Type definition of the pointer
  typedef logic [PROGRAM_BYTE_LENGTH_WIDTH-1:0] program_byte_length_t;

  //////////////////////////////////////////////////////////////////
  /// The type definition struct for the program copy instruction //
  typedef struct packed {
    /// Byte length of the AI Core Block program
    program_byte_length_t length;
    /// Destination byte address in the AI Core Block program memory
    destination_address_t dst_address;
    /// Byte pointer to the first word of the AI Core Block program in the control data memory region (can be offset by control_offset)
    program_pointer_t     program_ptr;
    /// ID of the destination AI Core Block (lookup for address map)
    destination_id_t      dst_id;
    /// Operation Code
    opcode_e              opcode;
  } program_instruction_t;

  ////////////////////////////////////
  // Token Manipulation Instruction //
  /// The width of the token operation code
  parameter int unsigned TOKEN_OPCODE_WIDTH = 6;
  /// Type definition of the opcode
  typedef logic [TOKEN_OPCODE_WIDTH-1:0] token_opcode_t;
  /////////////////////////////////////////////////////
  /// The type definition enum for an Operation Code //
  typedef enum token_opcode_t {
    TokenConsumeLocal  = token_opcode_t'(0),
    TokenProduceLocal  = token_opcode_t'(1),
    TokenConsumeGlobal = token_opcode_t'(2),
    TokenProduceGlobal = token_opcode_t'(3)
  } token_opcode_e;

  /// The width of the token mapping mask
  parameter int unsigned TOKEN_MASK_WIDTH = 24;
  /// Type definition of the token mask
  typedef logic [TOKEN_MASK_WIDTH-1:0] token_mask_t;

  /// Reserved length of the token instruction (derived)
  parameter int unsigned TokenReservedWidth =
      INSTRUCTION_WIDTH
    - OPCODE_WIDTH
    - TOKEN_OPCODE_WIDTH
    - TOKEN_MASK_WIDTH;

  ////////////////////////////////////////////////////////////////////////
  /// The type definition struct for the token manipulation instruction //
  typedef struct packed {
    /// Reserved
    logic [TokenReservedWidth-1:0] reserved;
    /// Bit vector of the Token to be manipulated
    token_mask_t                   token_mask;
    /// Destination identifier
    token_opcode_e                 token_opcode;
    /// Operation Code
    opcode_e                       opcode;
  } token_instruction_t;

  //////////////////////////////////////
  // Timestamp generation instruction //
  /// The width of the timestamp trigger ID
  parameter int unsigned TIMESTAMP_TRIGGER_WIDTH = 2;
  /// Type difinition of the timestamp trigger ID
  typedef logic [TIMESTAMP_TRIGGER_WIDTH-1:0] timestamp_trigger_id_t;

  /// Reserved width of the timestamp instruction between opcode and ID
  parameter int unsigned TimestampOpcodeReservedWidth = 8 - TIMESTAMP_TRIGGER_WIDTH;

  /// Reserved width of the timestamp instruction
  parameter int unsigned TimestampReservedWidth =
      INSTRUCTION_WIDTH
    - OPCODE_WIDTH
    - TimestampOpcodeReservedWidth
    - TIMESTAMP_TRIGGER_WIDTH;

  ///////////////////////////////////////////////////////////////////////
  /// The type definition struct for the timestamp trigger instruction //
  typedef struct packed {
    /// Reserved
    logic [TimestampReservedWidth-1:0]       reserved;
    /// Bit vector of the Token to be manipulated
    timestamp_trigger_id_t                   id;
    /// Destination identifier
    logic [TimestampOpcodeReservedWidth-1:0] reserved_opcode;
    /// Operation Code
    opcode_e                                 opcode;
  } timestamp_instruction_t;

  ////////////////////////////////
  // Instruction Encoding Union //
  ////////////////////////////////
  typedef union packed {
    logic [INSTRUCTION_WIDTH-1:0] view_vector;
    command_instruction_t         view_command;
    program_instruction_t         view_program;
    token_instruction_t           view_token;
    timestamp_instruction_t       view_timestamp;
  } instruction_t;

  /// Extract the opcode from the instruciton union
  function automatic opcode_e get_opcode(
    /// The instruction to extract the opcode from
    instruction_t instruction
  );
    return aic_cd_pkg::opcode_e'(instruction.view_vector[0+:aic_cd_pkg::OPCODE_WIDTH]);
  endfunction

  ///////////////
  // Copy Data //
  ///////////////
  /// The data to be copied has a certain width
  ///
  /// We assume the copied data to be constant to make our life easier
  parameter int unsigned COPY_DATA_WIDTH = 64;
  parameter int unsigned CopyDataNumBytes = COPY_DATA_WIDTH >> $clog2(8);
  parameter int unsigned CopyDataNumBytesWidth = cc_math_pkg::index_width(CopyDataNumBytes);

/*
  if (CopyDataNumBytes != cc_math_pkg::next_power_of_2(CopyDataNumBytes))
    $fatal(1, "Localparam: 'CopyDataNumBytes' must be a power of 2;");
*/
  /// The number of bytes to be copied, is the max size between both
  parameter int unsigned CopyByteLengthWidth = PROGRAM_BYTE_LENGTH_WIDTH > COMMAND_BYTE_LENGTH_WIDTH ?
      PROGRAM_BYTE_LENGTH_WIDTH : COMMAND_BYTE_LENGTH_WIDTH;
  /// The copy operation has this many bytes to copy
  typedef logic [CopyByteLengthWidth-1:0] copy_byte_length_t;

  /// Then the maximum amount of words we can see per patch operation
  parameter int unsigned CopyMaxNumWords = (32'd2**CopyByteLengthWidth) / CopyDataNumBytes;
  /// The width of the number of words that can be copied
  parameter int unsigned CopyMaxNumWordsLength = cc_math_pkg::index_width(CopyMaxNumWords);
  typedef logic [CopyMaxNumWordsLength-1:0] copy_num_words_t;

  /// Calculate the number of words to copy pepending on the instruction
  function automatic copy_num_words_t num_words_to_copy(
    instruction_t instruction
  );
    opcode_e         opcode;
    copy_num_words_t full_words_to_copy;

    opcode = get_opcode(instruction);

    unique case (opcode)
      OpcodeCommand: full_words_to_copy = copy_num_words_t'(instruction.view_command.length >> CopyDataNumBytesWidth);
      OpcodeProgram: full_words_to_copy = copy_num_words_t'(instruction.view_program.length >> CopyDataNumBytesWidth);
      default:       full_words_to_copy = copy_num_words_t'(0);
    endcase;

    // Additional word needs to be copied when we are not word aligned in the number of bytes
    unique case (opcode)
      OpcodeCommand: return full_words_to_copy + copy_num_words_t'(|instruction.view_command.length[0+:CopyDataNumBytesWidth]);
      OpcodeProgram: return full_words_to_copy + copy_num_words_t'(|instruction.view_program.length[0+:CopyDataNumBytesWidth]);
      default:       return copy_num_words_t'(0);
    endcase
  endfunction

  /// The concrete copy command that goes to the specific copy sub-units.
  ///
  /// Uses largest axi addesses which are then casted to correct size at the destination so synthesis can optimize it.
  /// This is distributed to multiple different sub-units, so it is expected that not every unit accesses everything.
  /// This in turn also leads to synthesis optimizations.  The values of this data-structure is filled out by the
  /// [execution unit](../execute.md).
  ///
  typedef struct packed {
    /// Information what type of copy command we are dealing with.
    opcode_e                    opcode;
    /// The instruction index, used for error tracing.
    task_list_pointer_t         instruction_index;
    /// The number of words for this patch.
    copy_num_words_t            num_words;
    /// The number of bytes that need to be copied.
    copy_byte_length_t          num_bytes;
    /// Select patchg table entry for patch 1.
    patch_id_t                  patch_id_1;
    /// Select patchg table entry for patch 1.
    patch_id_t                  patch_id_0;
    /// The patch mode to select.
    patch_mode_t                patch_mode;
    /// ID of the destination AI Core Block (lookup for address map).
    destination_id_t            destination_id;
    /// The destination address.
    axi_pkg::axi_largest_addr_t addr_destination;
    /// The source adddress.
    axi_pkg::axi_largest_addr_t addr_source;
  } copy_command_t;


  ///////////////////////////////////////////
  // Error conditions in Instruction Fetch //
  ///////////////////////////////////////////
  /// The validation unit performs some value sanitation for each instruction that passes through it.
  /// It will report the following issues:
  ///
  typedef struct packed {
    /// The AXI bus response for this instruction answered with `SLV_ERR`.
    ///
    /// Instruction: `ALL`
    ///
    logic axi_response_slverr;
    /// The AXI bus response for this instruction answered with `DEC_ERR`.
    ///
    /// Instruction: `ALL`
    ///
    logic axi_response_decerr;
    /// The `dst_id` filed contains a value larger or equals the `NumDestinations` parameterizations of the instance.
    ///
    /// Instruction: `CMD / PRG`
    ///
    logic destination_id_mapping;
    /// The `patch_mode` field contains a value larger or equals the `NumPatchModeEntries` parameterizations of the instance.
    ///
    /// Instruction: `CMD`
    ///
    logic patch_mode_mapping;
    /// The `patch_id_0` field contains a value larger or equals the `NumPatchTableEntries` parameterizations of the instance.
    ///
    /// Instruction: `CMD`
    ///
    logic patch_id_0_mapping;
    /// The `patch_id_1` field contains a value larger or equals the `NumPatchTableEntries` parameterizations of the instance.
    ///
    /// Instruction: `CMD`
    ///
    logic patch_id_1_mapping;
    /// The `token_opcode` does not match any of the defines opcodes for local or global consuming or producing values.
    ///
    /// Instruction: `TOKEN_*`
    ///
    logic token_illegal_opcode;
    /// The `token_mask` field has no bits bits set in the mapped region according to `NumLocalTokens`.
    ///
    /// Instruction: `TOKEN_LOCAL_*`
    ///
    logic token_local_map_empty;
    /// The `token_mask` field has no bits bits set in the mapped region according to `NumGlobalTokens`.
    ///
    /// Instruction: `TOKEN_GLOBAL_*`
    ///
    logic token_global_map_empty;
    /// The `token_mask` field has bits set in the reserved part according to `NumLocalTokens`.
    ///
    /// Instruction: `TOKEN_LOCAL_*`
    ///
    logic token_local_mapping;
    /// The `token_mask` field has bits set in the reserved part according to `NumGlobalTokens`.
    ///
    /// Instruction: `TOKEN_GLOBAL_*`
    ///
    logic token_global_mapping;
  } instruction_validation_errors_t;

  ///////////////////////////////////////
  // Error conditions in the Copy Unit //
  ///////////////////////////////////////
  /// The errors that can be generated by the copy unit:
  ///
  typedef struct packed {
    /// The particular copy write had a `DECERR` response.
    ///
    /// Reports Instruction index: :white_check_mark:
    ///
    logic axi_write_response_decerr;
    /// The particular copy write had a `SVLERR` response.
    ///
    /// Reports Instruction index: :white_check_mark:
    ///
    logic axi_write_response_slverr;
    /// The particular copy read had a `DECERR` response.
    ///
    /// Reports Instruction index: :white_check_mark:
    ///
    logic axi_read_response_decerr;
    /// The particular copy read had a `SVLERR` response.
    ///
    /// Reports Instruction index: :white_check_mark:
    ///
    logic axi_read_response_slverr;
    /// A fill counter got poped when it was not tracking anything.
    ///
    /// Reports Instruction index: :negative_squared_cross_mark:
    ///
    logic fill_counter_done_pop;
    /// A fill counter over or underflowed.
    ///
    /// Reports Instruction index: :negative_squared_cross_mark:
    ///
    logic fill_counter_overflow;
    /// The copy operation has the data bytes misaligned.
    ///
    /// Reports Instruction index: :white_check_mark:
    ///
    logic copy_data_misaligned;
  } copy_errors_t;

endpackage
