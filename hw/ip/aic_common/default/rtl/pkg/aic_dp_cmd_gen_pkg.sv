// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>


/// Package with constants and type definitions for the AI-Core Datapath Command Generator
///
package aic_dp_cmd_gen_pkg;
  ////////////////////////////////////////
  // Command Block Format Specification //
  ////////////////////////////////////////

  /// Number of formats
  parameter int CMD_BLOCK_NUM_FORMATS = 10;
  /// Format descriptor data width
  parameter int CmdBlockFormatWidth = $clog2(CMD_BLOCK_NUM_FORMATS);
  typedef logic [CmdBlockFormatWidth-1:0] cmd_format_t;

  /// Config field width from the command block
  parameter int unsigned CMD_BLOCK_CONFIG_WIDTH = 8;
  typedef struct packed {
    logic [CMD_BLOCK_CONFIG_WIDTH-2:0] rsvd;
    logic                              vector_mode;
  } cmd_config_t;

  /// Type definition enum with format encoding
  typedef enum cmd_format_t {
    LoopsM1N0 = cmd_format_t'(4'h0),
    LoopsM1N1 = cmd_format_t'(4'h1),
    LoopsM1N2 = cmd_format_t'(4'h2),
    LoopsM2N0 = cmd_format_t'(4'h3),
    LoopsM2N1 = cmd_format_t'(4'h4),
    LoopsM2N2 = cmd_format_t'(4'h5),
    LoopsM3N0 = cmd_format_t'(4'h6),
    LoopsM3N1 = cmd_format_t'(4'h7),
    LoopsM3N2 = cmd_format_t'(4'h8),
    Bypass    = cmd_format_t'(4'h9)
  } cmd_format_e;

  /// Loop index specifier, deliberatly too wide to be reused in command
  parameter int unsigned LOOP_INDEX_WIDTH = 8;
  /// Type definition of the index
  typedef logic [LOOP_INDEX_WIDTH-1:0] loop_index_t;
  /// Mapping of the index to a stream
  typedef enum loop_index_t {
    MainIndex    = loop_index_t'(0),
    Nested0Index = loop_index_t'(1),
    Nested1Index = loop_index_t'(2)
  } loop_identifier_e;

  /// Number of main loops
  parameter int unsigned NUM_MAIN_LOOPS = 3;
  parameter int unsigned NUM_NESTED_LOOPS = 2;

  /// Helper function to extract the number of main loops from format
  function automatic loop_index_t num_main_loops_from_format(
    cmd_format_e command_format
  );
    unique case (command_format)
      LoopsM1N0,
      LoopsM1N1,
      LoopsM1N2: return loop_index_t'(1);
      LoopsM2N0,
      LoopsM2N1,
      LoopsM2N2: return loop_index_t'(2);
      LoopsM3N0,
      LoopsM3N1,
      LoopsM3N2: return loop_index_t'(3);
      default:   return loop_index_t'(0);
    endcase
  endfunction

  /// Helper function to extract the number of main loops from existance
  function automatic loop_index_t num_main_loops(
    logic main_exists[NUM_MAIN_LOOPS]
  );
    loop_index_t value;
    value = loop_index_t'(0);
    foreach (main_exists[index]) value += loop_index_t'(main_exists[index]);
    return value;
  endfunction

  /// Helper function to extract the number of nested loops from format
  function automatic loop_index_t num_nested_loops_from_format(
    cmd_format_e command_format
  );
    unique case (command_format)
      LoopsM1N1,
      LoopsM2N1,
      LoopsM3N1: return loop_index_t'(1);
      LoopsM1N2,
      LoopsM2N2,
      LoopsM3N2: return loop_index_t'(2);
      default:   return loop_index_t'(0);
    endcase
  endfunction

  /// Helper function to extract the number of nested loops from existance
  function automatic loop_index_t num_nested_loops(
    logic nested_exists[NUM_NESTED_LOOPS]
  );
    loop_index_t value;
    value = loop_index_t'(0);
    foreach (nested_exists[index]) value += loop_index_t'(nested_exists[index]);
    return value;
  endfunction

  ////////////////////////////////////////
  // The widths of the idividual fields //
  /// The width of all `Start*` fields
  parameter int LOOP_POINTER_WIDTH = 16;
  typedef logic [LOOP_POINTER_WIDTH-1:0] loop_pointer_t;
  typedef logic [LOOP_POINTER_WIDTH:0]  _loop_pointer_t;
  /// The width of all `Length*` fields
  parameter int LOOP_LENGTH_WIDTH = 16;
  typedef logic [LOOP_LENGTH_WIDTH-1:0] loop_length_t;

  /// The width of all `Iteration*` fields
  parameter int LOOP_ITERATION_WIDTH = 24;
  typedef logic [LOOP_ITERATION_WIDTH-1:0] loop_iteration_t;

  ////////////////////////////////////////////
  /// Aggregate type for a loop description //
  ////////////////////////////////////////////
  typedef struct packed {
    /// The number of iterations this loop needs to do
    loop_iteration_t iteration;
    /// The length of the loop
    loop_length_t    length;
    /// The start address of the loop
    loop_pointer_t   start;
  } loop_description_t;

  /// The width of the `extra` fields
  parameter int COMMAND_EXTRA_WIDTH = 8;
  typedef logic [COMMAND_EXTRA_WIDTH-1:0] command_extra_t;
  /// The width of all `reserved*` fields
  parameter int COMMAND_RESERVED_WIDTH = 8;
  typedef logic [COMMAND_RESERVED_WIDTH-1:0] command_reserved_t;

  /////////////////////////////////////////////////////////
  // The command structure to get from the command block //
  /////////////////////////////////////////////////////////
  /// Struct with command for the loop generation
  typedef struct packed {
    loop_index_t       nested_1_map_main;
    loop_description_t nested_1;
    loop_index_t       nested_0_map_main;
    loop_description_t nested_0;
    command_reserved_t reserved_1;
    loop_description_t main_2;
    command_reserved_t reserved_0;
    loop_description_t main_1;
    command_extra_t    extra;
    loop_description_t main_0;
  } cmdb_cmd_struct_t;

  /// Calculated Width of the full command
  parameter int CommandBlockCommandWidth = $bits(cmdb_cmd_struct_t);

  /// Union of the command for easy type casting
  typedef union packed {
    logic [CommandBlockCommandWidth-1:0] view_vector;
    cmdb_cmd_struct_t                    view_struct;
  } cmdb_cmd_t;

  //////////////////////////////////////////////////////
  // Internally break the command into smaller chunks //
  //////////////////////////////////////////////////////

  /// A loop descriptor additionally contains the loop index
  /// In case of an main loop it describes if it is main 0, 1 etc
  /// In case of an nested loop it describes to which main loop it is mapped
  typedef struct packed {
    /// Last loop of this particular command
    logic              last;
    /// This is a bypass command
    logic              bypass;
    /// Because nested 1 was alone it is treated as a nested 0 internally
    logic              nested_1_mapped_to_0;
    /// Description of the innner 1 loop
    loop_description_t nested_1;
    /// Description of the innner 0 loop
    loop_description_t nested_0;
    /// Description of the main loop
    ///
    /// The command is treated as a bypass command if main does not exist!
    loop_description_t main;
    /// Which loop number it is
    loop_index_t       index;
  } loop_descriptor_t;

  /// The end pointer of a loop
  ///
  /// Uses internal typeto account for overflows, should be casted to loop_pointer_t.
  ///
  function automatic _loop_pointer_t loop_end_pointer(
    loop_pointer_t start,
    loop_length_t  length
  );
    return _loop_pointer_t'(start) + _loop_pointer_t'(length) - _loop_pointer_t'(|length);
  endfunction

  /// A loop in the command exists
  function automatic logic loop_exists(
    loop_length_t    length,
    loop_iteration_t iterations
  );
    return (length != loop_length_t'(0)) && (iterations != loop_iteration_t'(0));
  endfunction

  /// Determine if the mapping points outside the command memory
  function automatic logic loop_maps_outside_memory(
    loop_pointer_t start,
    loop_length_t  length,
    int unsigned   memory_depth
  );
    return (start + length) > memory_depth;
  endfunction

  /// Calculate a segmentation fault for an nested loop
  ///
  /// nested_start has to be after or same than main_start
  /// nested_end has to be before or same than main_end
  function automatic logic nested_loop_has_segmentation_fault(
    loop_pointer_t main_start,
    loop_length_t  main_length,
    loop_pointer_t nested_start,
    loop_length_t  nested_length
  );
    _loop_pointer_t main_end;   // There might be overflow
    _loop_pointer_t nested_end; // There might be overflow

    main_end   = loop_end_pointer(.start(main_start),.length(main_length));
    nested_end = loop_end_pointer(.start(nested_start),.length(nested_length));

    return (nested_start < main_start) || (nested_end > main_end);
  endfunction

  //////////////////////////////////////
  // Metadata information as sideband //
  //////////////////////////////////////
  typedef struct packed {
    /// The command format
    cmd_format_e    format;
    /// The config from the command block
    cmd_config_t    cfg;
    /// The extra field from the command descriptor
    command_extra_t extra;
  } metadata_t;

  typedef struct packed {
    /// This is the last main iteration of a command
    logic            overall_last;
    /// The iteration count of the current nested 1 loop
    loop_iteration_t nested_1;
    /// The iteration count of the current nested 0 loop
    loop_iteration_t nested_0;
    /// The iteration count of the current main loop
    loop_iteration_t main;
    /// The index of the main loop being executed
    loop_index_t     main_index;
  } loop_iterations_t;

  //////////////////////////////////////////////
  // Error conditions for the address looping //
  //////////////////////////////////////////////
  typedef struct packed {
    /// The `cmd_format` field holds an illegal value.
    logic illegal_format;
    /// The command results in a program with length 0.
    logic empty_program;
    /// The first main loop overruns the program memory.
    logic main_0_length;
    /// The second main loop overruns the program memory.
    logic main_1_length;
    /// The third main loop overruns the program memory.
    logic main_2_length;
    /// The first nested loop overruns the program memory.
    logic nested_0_length;
    /// The second nested loop overruns the program memory.
    logic nested_1_length;
    /// The mapping of the first nested loop is illegal (wrong value in map_main field or mapped to an empty main loop).
    logic nested_0_mapping;
    /// The mapping of the second nested loop is illegal (wrong value in map_main field or mapped to an empty main loop).
    logic nested_1_mapping;
    /// The first nested loop (partially) lies outside of its containing main loop.
    logic nested_0_segfault;
    /// The second nested loop (partially) lies outside of its containing main loop.
    logic nested_1_segfault;
    /// The two nested loops within the same containing main loop are incorrectly ordered (second nested must not lie before first nested).
    logic nested_order;
    /// The two nested loops within the same containing main loop are incorrectly nested (second nested must not contain first nested).
    logic nested_nesting;
    /// The two nested loops within the same containing main loop partially overlap.
    logic nested_overlap;
  } loop_errors_t;

  function automatic logic error_empty_program(
    logic        main_exists[NUM_MAIN_LOOPS]
  );
    // Note: Array reduction function does not syntheisze in all tools
    logic exists;
    exists = 1'b0;
    foreach (main_exists[index]) exists |= main_exists[index];

    return !exists;
  endfunction

  function automatic logic error_nested_mapping(
    loop_index_t nested_map_main,
    logic        main_exists[NUM_MAIN_LOOPS]
  );
    // Error if we map outside the range or if we map to an empty loop
    return (nested_map_main >= NUM_MAIN_LOOPS) || !main_exists[nested_map_main];
  endfunction

  ///////////////////////////
  // Command Block Mapping //
  ///////////////////////////
  /// Header length is included
  parameter int CMD_BLOCK_NUM_BYTES[CMD_BLOCK_NUM_FORMATS] = {
    8 * 1, // LoopsM1N0
    8 * 2, // LoopsM1N1
    8 * 3, // LoopsM1N2
    8 * 2, // LoopsM2N0
    8 * 3, // LoopsM2N1
    8 * 4, // LoopsM2N2
    8 * 3, // LoopsM3N0
    8 * 4, // LoopsM3N1
    8 * 5, // LoopsM3N2
    8 * 0  // Bypass
  };

  /// The number of fields in the command
  parameter int CMD_BLOCK_NUM_FIELDS = 20;
  /// The width of a command line
  parameter int  CMD_BLOCK_LINE_WIDTH = 64;
  /// Field sizes for realignment in cmdblock_cmd_unpack
  parameter int CMD_BLOCK_FIELD_SIZES[CMD_BLOCK_NUM_FIELDS] = {
    LOOP_POINTER_WIDTH, LOOP_LENGTH_WIDTH, LOOP_ITERATION_WIDTH, COMMAND_EXTRA_WIDTH,
    LOOP_POINTER_WIDTH, LOOP_LENGTH_WIDTH, LOOP_ITERATION_WIDTH, COMMAND_RESERVED_WIDTH,
    LOOP_POINTER_WIDTH, LOOP_LENGTH_WIDTH, LOOP_ITERATION_WIDTH, COMMAND_RESERVED_WIDTH,
    LOOP_POINTER_WIDTH, LOOP_LENGTH_WIDTH, LOOP_ITERATION_WIDTH, LOOP_INDEX_WIDTH,
    LOOP_POINTER_WIDTH, LOOP_LENGTH_WIDTH, LOOP_ITERATION_WIDTH, LOOP_INDEX_WIDTH
  };

  //////////////////////////////////////////////////////////////////////////////
  // LSB Functions                                                            //
  // Determine by format for each field what the LSB for the command block is //
  //////////////////////////////////////////////////////////////////////////////

  function automatic int cmd_lsb_main_start(
    int unsigned loop_index,
    cmd_format_e format
  );
    if (num_main_loops_from_format(format) == 0)          return -1;
    if (num_main_loops_from_format(format) <= loop_index) return -1;

    return loop_index * CMD_BLOCK_LINE_WIDTH;
  endfunction

  function automatic int cmd_lsb_main_length(
    int unsigned loop_index,
    cmd_format_e format
  );
    if (num_main_loops_from_format(format) == 0)          return -1;
    if (num_main_loops_from_format(format) <= loop_index) return -1;

    return cmd_lsb_main_start(loop_index, format) + LOOP_POINTER_WIDTH;
  endfunction

  function automatic int cmd_lsb_main_iter(
    int unsigned loop_index,
    cmd_format_e format
  );
    if (num_main_loops_from_format(format) == 0)          return -1;
    if (num_main_loops_from_format(format) <= loop_index) return -1;

    return cmd_lsb_main_length(loop_index, format) + LOOP_LENGTH_WIDTH;
  endfunction

  function automatic int cmd_lsb_extra(
    int unsigned loop_index,
    cmd_format_e format
  );
    // We also map the reserved fields always to default
    if (num_main_loops_from_format(format) == 0) return -1;
    if (loop_index > 0)                          return -1;

    return LOOP_POINTER_WIDTH + LOOP_LENGTH_WIDTH + LOOP_ITERATION_WIDTH;
  endfunction

  function automatic int cmd_lsb_nested_start(
    int unsigned loop_index,
    cmd_format_e format
  );
    int unsigned main_offset;

    if (num_nested_loops_from_format(format) == 0)          return -1;
    if (num_nested_loops_from_format(format) <= loop_index) return -1;

    main_offset = num_main_loops_from_format(format) * CMD_BLOCK_LINE_WIDTH;

    return loop_index * CMD_BLOCK_LINE_WIDTH + main_offset;
  endfunction

  function automatic int cmd_lsb_nested_length(
    int unsigned loop_index,
    cmd_format_e format
  );
    if (num_nested_loops_from_format(format) == 0)          return -1;
    if (num_nested_loops_from_format(format) <= loop_index) return -1;

    return cmd_lsb_nested_start(loop_index, format) + LOOP_POINTER_WIDTH;
  endfunction

  function automatic int cmd_lsb_nested_iter(
    int unsigned loop_index,
    cmd_format_e format
  );
    if (num_nested_loops_from_format(format) == 0)          return -1;
    if (num_nested_loops_from_format(format) <= loop_index) return -1;

    return cmd_lsb_nested_length(loop_index, format) + LOOP_LENGTH_WIDTH;
  endfunction

  function automatic int cmd_lsb_nested_map_main(
    int unsigned loop_index,
    cmd_format_e format
  );
    if (num_nested_loops_from_format(format) == 0)          return -1;
    if (num_nested_loops_from_format(format) <= loop_index) return -1;

    return cmd_lsb_nested_iter(loop_index, format) + LOOP_ITERATION_WIDTH;
  endfunction

  //////////////////
  // 0: LoopsM1N0 //
  //////////////////
  parameter int CMD_LOOPS_M1_N0_LSBS[CMD_BLOCK_NUM_FIELDS] = {
    cmd_lsb_main_start(0, LoopsM1N0),   cmd_lsb_main_length(0, LoopsM1N0),   cmd_lsb_main_iter(0, LoopsM1N0),   cmd_lsb_extra(0, LoopsM1N0),
    cmd_lsb_main_start(1, LoopsM1N0),   cmd_lsb_main_length(1, LoopsM1N0),   cmd_lsb_main_iter(1, LoopsM1N0),   cmd_lsb_extra(1, LoopsM1N0),
    cmd_lsb_main_start(2, LoopsM1N0),   cmd_lsb_main_length(2, LoopsM1N0),   cmd_lsb_main_iter(2, LoopsM1N0),   cmd_lsb_extra(2, LoopsM1N0),
    cmd_lsb_nested_start(0, LoopsM1N0), cmd_lsb_nested_length(0, LoopsM1N0), cmd_lsb_nested_iter(0, LoopsM1N0), cmd_lsb_nested_map_main(0, LoopsM1N0),
    cmd_lsb_nested_start(1, LoopsM1N0), cmd_lsb_nested_length(1, LoopsM1N0), cmd_lsb_nested_iter(1, LoopsM1N0), cmd_lsb_nested_map_main(1, LoopsM1N0)
  };

  //////////////////
  // 1: LoopsM1N1 //
  //////////////////
  parameter int CMD_LOOPS_M1_N1_LSBS[CMD_BLOCK_NUM_FIELDS] = {
    cmd_lsb_main_start(0, LoopsM1N1),   cmd_lsb_main_length(0, LoopsM1N1),   cmd_lsb_main_iter(0, LoopsM1N1),   cmd_lsb_extra(0, LoopsM1N1),
    cmd_lsb_main_start(1, LoopsM1N1),   cmd_lsb_main_length(1, LoopsM1N1),   cmd_lsb_main_iter(1, LoopsM1N1),   cmd_lsb_extra(1, LoopsM1N1),
    cmd_lsb_main_start(2, LoopsM1N1),   cmd_lsb_main_length(2, LoopsM1N1),   cmd_lsb_main_iter(2, LoopsM1N1),   cmd_lsb_extra(2, LoopsM1N1),
    cmd_lsb_nested_start(0, LoopsM1N1), cmd_lsb_nested_length(0, LoopsM1N1), cmd_lsb_nested_iter(0, LoopsM1N1), cmd_lsb_nested_map_main(0, LoopsM1N1),
    cmd_lsb_nested_start(1, LoopsM1N1), cmd_lsb_nested_length(1, LoopsM1N1), cmd_lsb_nested_iter(1, LoopsM1N1), cmd_lsb_nested_map_main(1, LoopsM1N1)
  };

  //////////////////
  // 2: LoopsM1N2 //
  //////////////////
  parameter int CMD_LOOPS_M1_N2_LSBS[CMD_BLOCK_NUM_FIELDS] = {
    cmd_lsb_main_start(0, LoopsM1N2),   cmd_lsb_main_length(0, LoopsM1N2),   cmd_lsb_main_iter(0, LoopsM1N2),   cmd_lsb_extra(0, LoopsM1N2),
    cmd_lsb_main_start(1, LoopsM1N2),   cmd_lsb_main_length(1, LoopsM1N2),   cmd_lsb_main_iter(1, LoopsM1N2),   cmd_lsb_extra(1, LoopsM1N2),
    cmd_lsb_main_start(2, LoopsM1N2),   cmd_lsb_main_length(2, LoopsM1N2),   cmd_lsb_main_iter(2, LoopsM1N2),   cmd_lsb_extra(2, LoopsM1N2),
    cmd_lsb_nested_start(0, LoopsM1N2), cmd_lsb_nested_length(0, LoopsM1N2), cmd_lsb_nested_iter(0, LoopsM1N2), cmd_lsb_nested_map_main(0, LoopsM1N2),
    cmd_lsb_nested_start(1, LoopsM1N2), cmd_lsb_nested_length(1, LoopsM1N2), cmd_lsb_nested_iter(1, LoopsM1N2), cmd_lsb_nested_map_main(1, LoopsM1N2)
  };

  //////////////////
  // 3: LoopsM2N0 //
  //////////////////
  parameter int CMD_LOOPS_M2_N0_LSBS[CMD_BLOCK_NUM_FIELDS] = {
    cmd_lsb_main_start(0, LoopsM2N0),   cmd_lsb_main_length(0, LoopsM2N0),   cmd_lsb_main_iter(0, LoopsM2N0),   cmd_lsb_extra(0, LoopsM2N0),
    cmd_lsb_main_start(1, LoopsM2N0),   cmd_lsb_main_length(1, LoopsM2N0),   cmd_lsb_main_iter(1, LoopsM2N0),   cmd_lsb_extra(1, LoopsM2N0),
    cmd_lsb_main_start(2, LoopsM2N0),   cmd_lsb_main_length(2, LoopsM2N0),   cmd_lsb_main_iter(2, LoopsM2N0),   cmd_lsb_extra(2, LoopsM2N0),
    cmd_lsb_nested_start(0, LoopsM2N0), cmd_lsb_nested_length(0, LoopsM2N0), cmd_lsb_nested_iter(0, LoopsM2N0), cmd_lsb_nested_map_main(0, LoopsM2N0),
    cmd_lsb_nested_start(1, LoopsM2N0), cmd_lsb_nested_length(1, LoopsM2N0), cmd_lsb_nested_iter(1, LoopsM2N0), cmd_lsb_nested_map_main(1, LoopsM2N0)
  };

  //////////////////
  // 4: LoopsM2N1 //
  //////////////////
  parameter int CMD_LOOPS_M2_N1_LSBS[CMD_BLOCK_NUM_FIELDS] = {
    cmd_lsb_main_start(0, LoopsM2N1),   cmd_lsb_main_length(0, LoopsM2N1),   cmd_lsb_main_iter(0, LoopsM2N1),   cmd_lsb_extra(0, LoopsM2N1),
    cmd_lsb_main_start(1, LoopsM2N1),   cmd_lsb_main_length(1, LoopsM2N1),   cmd_lsb_main_iter(1, LoopsM2N1),   cmd_lsb_extra(1, LoopsM2N1),
    cmd_lsb_main_start(2, LoopsM2N1),   cmd_lsb_main_length(2, LoopsM2N1),   cmd_lsb_main_iter(2, LoopsM2N1),   cmd_lsb_extra(2, LoopsM2N1),
    cmd_lsb_nested_start(0, LoopsM2N1), cmd_lsb_nested_length(0, LoopsM2N1), cmd_lsb_nested_iter(0, LoopsM2N1), cmd_lsb_nested_map_main(0, LoopsM2N1),
    cmd_lsb_nested_start(1, LoopsM2N1), cmd_lsb_nested_length(1, LoopsM2N1), cmd_lsb_nested_iter(1, LoopsM2N1), cmd_lsb_nested_map_main(1, LoopsM2N1)
  };

  //////////////////
  // 5: LoopsM2N2 //
  //////////////////
  parameter int CMD_LOOPS_M2_N2_LSBS[CMD_BLOCK_NUM_FIELDS] = {
    cmd_lsb_main_start(0, LoopsM2N2),   cmd_lsb_main_length(0, LoopsM2N2),   cmd_lsb_main_iter(0, LoopsM2N2),   cmd_lsb_extra(0, LoopsM2N2),
    cmd_lsb_main_start(1, LoopsM2N2),   cmd_lsb_main_length(1, LoopsM2N2),   cmd_lsb_main_iter(1, LoopsM2N2),   cmd_lsb_extra(1, LoopsM2N2),
    cmd_lsb_main_start(2, LoopsM2N2),   cmd_lsb_main_length(2, LoopsM2N2),   cmd_lsb_main_iter(2, LoopsM2N2),   cmd_lsb_extra(2, LoopsM2N2),
    cmd_lsb_nested_start(0, LoopsM2N2), cmd_lsb_nested_length(0, LoopsM2N2), cmd_lsb_nested_iter(0, LoopsM2N2), cmd_lsb_nested_map_main(0, LoopsM2N2),
    cmd_lsb_nested_start(1, LoopsM2N2), cmd_lsb_nested_length(1, LoopsM2N2), cmd_lsb_nested_iter(1, LoopsM2N2), cmd_lsb_nested_map_main(1, LoopsM2N2)
  };

  //////////////////
  // 6: LoopsM3N0 //
  //////////////////
  parameter int CMD_LOOPS_M3_N0_LSBS[CMD_BLOCK_NUM_FIELDS] = {
    cmd_lsb_main_start(0, LoopsM3N0),   cmd_lsb_main_length(0, LoopsM3N0),   cmd_lsb_main_iter(0, LoopsM3N0),   cmd_lsb_extra(0, LoopsM3N0),
    cmd_lsb_main_start(1, LoopsM3N0),   cmd_lsb_main_length(1, LoopsM3N0),   cmd_lsb_main_iter(1, LoopsM3N0),   cmd_lsb_extra(1, LoopsM3N0),
    cmd_lsb_main_start(2, LoopsM3N0),   cmd_lsb_main_length(2, LoopsM3N0),   cmd_lsb_main_iter(2, LoopsM3N0),   cmd_lsb_extra(2, LoopsM3N0),
    cmd_lsb_nested_start(0, LoopsM3N0), cmd_lsb_nested_length(0, LoopsM3N0), cmd_lsb_nested_iter(0, LoopsM3N0), cmd_lsb_nested_map_main(0, LoopsM3N0),
    cmd_lsb_nested_start(1, LoopsM3N0), cmd_lsb_nested_length(1, LoopsM3N0), cmd_lsb_nested_iter(1, LoopsM3N0), cmd_lsb_nested_map_main(1, LoopsM3N0)
  };

  //////////////////
  // 7: LoopsM3N1 //
  //////////////////
  parameter int CMD_LOOPS_M3_N1_LSBS[CMD_BLOCK_NUM_FIELDS] = {
    cmd_lsb_main_start(0, LoopsM3N1),   cmd_lsb_main_length(0, LoopsM3N1),   cmd_lsb_main_iter(0, LoopsM3N1),   cmd_lsb_extra(0, LoopsM3N1),
    cmd_lsb_main_start(1, LoopsM3N1),   cmd_lsb_main_length(1, LoopsM3N1),   cmd_lsb_main_iter(1, LoopsM3N1),   cmd_lsb_extra(1, LoopsM3N1),
    cmd_lsb_main_start(2, LoopsM3N1),   cmd_lsb_main_length(2, LoopsM3N1),   cmd_lsb_main_iter(2, LoopsM3N1),   cmd_lsb_extra(2, LoopsM3N1),
    cmd_lsb_nested_start(0, LoopsM3N1), cmd_lsb_nested_length(0, LoopsM3N1), cmd_lsb_nested_iter(0, LoopsM3N1), cmd_lsb_nested_map_main(0, LoopsM3N1),
    cmd_lsb_nested_start(1, LoopsM3N1), cmd_lsb_nested_length(1, LoopsM3N1), cmd_lsb_nested_iter(1, LoopsM3N1), cmd_lsb_nested_map_main(1, LoopsM3N1)
  };

  //////////////////
  // 8: LoopsM3N2 //
  //////////////////
  parameter int CMD_LOOPS_M3_N2_LSBS[CMD_BLOCK_NUM_FIELDS] = {
    cmd_lsb_main_start(0, LoopsM3N2),   cmd_lsb_main_length(0, LoopsM3N2),   cmd_lsb_main_iter(0, LoopsM3N2),   cmd_lsb_extra(0, LoopsM3N2),
    cmd_lsb_main_start(1, LoopsM3N2),   cmd_lsb_main_length(1, LoopsM3N2),   cmd_lsb_main_iter(1, LoopsM3N2),   cmd_lsb_extra(1, LoopsM3N2),
    cmd_lsb_main_start(2, LoopsM3N2),   cmd_lsb_main_length(2, LoopsM3N2),   cmd_lsb_main_iter(2, LoopsM3N2),   cmd_lsb_extra(2, LoopsM3N2),
    cmd_lsb_nested_start(0, LoopsM3N2), cmd_lsb_nested_length(0, LoopsM3N2), cmd_lsb_nested_iter(0, LoopsM3N2), cmd_lsb_nested_map_main(0, LoopsM3N2),
    cmd_lsb_nested_start(1, LoopsM3N2), cmd_lsb_nested_length(1, LoopsM3N2), cmd_lsb_nested_iter(1, LoopsM3N2), cmd_lsb_nested_map_main(1, LoopsM3N2)
  };

  ///////////////
  // 9: Bypass //
  ///////////////
  parameter int CMD_BYPASS_LSBS[CMD_BLOCK_NUM_FIELDS] = {
    cmd_lsb_main_start(0, Bypass),   cmd_lsb_main_length(0, Bypass),   cmd_lsb_main_iter(0, Bypass),   cmd_lsb_extra(0, Bypass),
    cmd_lsb_main_start(1, Bypass),   cmd_lsb_main_length(1, Bypass),   cmd_lsb_main_iter(1, Bypass),   cmd_lsb_extra(1, Bypass),
    cmd_lsb_main_start(2, Bypass),   cmd_lsb_main_length(2, Bypass),   cmd_lsb_main_iter(2, Bypass),   cmd_lsb_extra(2, Bypass),
    cmd_lsb_nested_start(0, Bypass), cmd_lsb_nested_length(0, Bypass), cmd_lsb_nested_iter(0, Bypass), cmd_lsb_nested_map_main(0, Bypass),
    cmd_lsb_nested_start(1, Bypass), cmd_lsb_nested_length(1, Bypass), cmd_lsb_nested_iter(1, Bypass), cmd_lsb_nested_map_main(1, Bypass)
  };

  ///////////////////////////////
  // Default                   //
  // All Commands use the same //
  ///////////////////////////////
  parameter int CMD_BLOCK_LSBS[CMD_BLOCK_NUM_FIELDS] = {
    cmd_lsb_main_start(0, LoopsM3N2),   cmd_lsb_main_length(0, LoopsM3N2),   cmd_lsb_main_iter(0, LoopsM3N2),   cmd_lsb_extra(0, LoopsM3N2),
    cmd_lsb_main_start(1, LoopsM3N2),   cmd_lsb_main_length(1, LoopsM3N2),   cmd_lsb_main_iter(1, LoopsM3N2),   cmd_lsb_extra(0, LoopsM3N2) + 1*64,
    cmd_lsb_main_start(2, LoopsM3N2),   cmd_lsb_main_length(2, LoopsM3N2),   cmd_lsb_main_iter(2, LoopsM3N2),   cmd_lsb_extra(0, LoopsM3N2) + 2*64,
    cmd_lsb_nested_start(0, LoopsM3N2), cmd_lsb_nested_length(0, LoopsM3N2), cmd_lsb_nested_iter(0, LoopsM3N2), cmd_lsb_nested_map_main(0, LoopsM3N2),
    cmd_lsb_nested_start(1, LoopsM3N2), cmd_lsb_nested_length(1, LoopsM3N2), cmd_lsb_nested_iter(1, LoopsM3N2), cmd_lsb_nested_map_main(1, LoopsM3N2)
  };

  parameter longint CMD_DEFAULT[CMD_BLOCK_NUM_FIELDS] = {
    loop_pointer_t'(0), loop_length_t'(0), loop_iteration_t'(0), command_extra_t'(0),
    loop_pointer_t'(0), loop_length_t'(0), loop_iteration_t'(0), command_reserved_t'(0),
    loop_pointer_t'(0), loop_length_t'(0), loop_iteration_t'(0), command_reserved_t'(0),
    loop_pointer_t'(0), loop_length_t'(0), loop_iteration_t'(0), loop_index_t'(0),
    loop_pointer_t'(0), loop_length_t'(0), loop_iteration_t'(0), loop_index_t'(0)
  };

  ///////////////////////
  // Pack the Commands //
  ///////////////////////
  typedef int                        cmd_block_int_fileds_t[CMD_BLOCK_NUM_FIELDS];
  typedef longint                    cmd_block_longint_fields_t[CMD_BLOCK_NUM_FIELDS];
  typedef cmd_block_int_fileds_t     cmd_block_int_fields_format_t[CMD_BLOCK_NUM_FORMATS];
  typedef cmd_block_longint_fields_t cmd_block_longint_fields_format_t[CMD_BLOCK_NUM_FORMATS];

  function automatic cmd_block_int_fields_format_t _generate_lsb_array();
    cmd_block_int_fields_format_t return_value;
    return_value[LoopsM1N0] = CMD_LOOPS_M1_N0_LSBS;
    return_value[LoopsM1N1] = CMD_LOOPS_M1_N1_LSBS;
    return_value[LoopsM1N2] = CMD_LOOPS_M1_N2_LSBS;
    return_value[LoopsM2N0] = CMD_LOOPS_M2_N0_LSBS;
    return_value[LoopsM2N1] = CMD_LOOPS_M2_N1_LSBS;
    return_value[LoopsM2N2] = CMD_LOOPS_M2_N2_LSBS;
    return_value[LoopsM3N0] = CMD_LOOPS_M3_N0_LSBS;
    return_value[LoopsM3N1] = CMD_LOOPS_M3_N1_LSBS;
    return_value[LoopsM3N2] = CMD_LOOPS_M3_N2_LSBS;
    return_value[Bypass]    = CMD_BYPASS_LSBS;
    return return_value;
  endfunction

  function automatic cmd_block_longint_fields_format_t _generate_default_array();
    cmd_block_longint_fields_format_t return_value;
    return_value[LoopsM1N0] = CMD_DEFAULT;
    return_value[LoopsM1N1] = CMD_DEFAULT;
    return_value[LoopsM1N2] = CMD_DEFAULT;
    return_value[LoopsM2N0] = CMD_DEFAULT;
    return_value[LoopsM2N1] = CMD_DEFAULT;
    return_value[LoopsM2N2] = CMD_DEFAULT;
    return_value[LoopsM3N0] = CMD_DEFAULT;
    return_value[LoopsM3N1] = CMD_DEFAULT;
    return_value[LoopsM3N2] = CMD_DEFAULT;
    return_value[Bypass]    = CMD_DEFAULT;
    return return_value;
  endfunction

  /// Output index ampping
  parameter cmd_block_int_fileds_t CMD_BLOCK_FIELD_OUTP_IDX = {
    cmd_lsb_main_start(0, LoopsM3N2),   cmd_lsb_main_length(0, LoopsM3N2),   cmd_lsb_main_iter(0, LoopsM3N2),   cmd_lsb_extra(0, LoopsM3N2),
    cmd_lsb_main_start(1, LoopsM3N2),   cmd_lsb_main_length(1, LoopsM3N2),   cmd_lsb_main_iter(1, LoopsM3N2),   cmd_lsb_extra(0, LoopsM3N2) + 1*64,
    cmd_lsb_main_start(2, LoopsM3N2),   cmd_lsb_main_length(2, LoopsM3N2),   cmd_lsb_main_iter(2, LoopsM3N2),   cmd_lsb_extra(0, LoopsM3N2) + 2*64,
    cmd_lsb_nested_start(0, LoopsM3N2), cmd_lsb_nested_length(0, LoopsM3N2), cmd_lsb_nested_iter(0, LoopsM3N2), cmd_lsb_nested_map_main(0, LoopsM3N2),
    cmd_lsb_nested_start(1, LoopsM3N2), cmd_lsb_nested_length(1, LoopsM3N2), cmd_lsb_nested_iter(1, LoopsM3N2), cmd_lsb_nested_map_main(1, LoopsM3N2)
  };
  /// Default mapping for the command block
  parameter cmd_block_longint_fields_format_t CMD_BLOCK_DEFAULTS = _generate_default_array();
  /// LSB mapping for the command block
  parameter cmd_block_int_fields_format_t     CMD_BLOCK_FORMAT_IDX = _generate_lsb_array();
  /// Recommended value for the `CMD_FIFO_WIDTH` parameter of the `cmdblock` attached
  parameter int CMD_BLOCK_CMD_FIFO_WIDTH =
      (1 * CMD_BLOCK_LINE_WIDTH)  // Header length
    + (2 * CMD_BLOCK_LINE_WIDTH); // To get a M1N1 in there


  /////////////////////////////////////////////////////////
  // Dummy datapath command only to be used as a default //
  /////////////////////////////////////////////////////////
  typedef struct packed {
    logic [31:0] index;
    logic [31:0] data;
  } dummy_dp_command_t;

endpackage
