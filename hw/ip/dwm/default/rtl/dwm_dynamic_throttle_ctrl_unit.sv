// (C) Copyright 2025 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Yasen Kazandzhiev <yasen.kazandzhiev@axelera.ai>


module dwm_dynamic_throttle_ctrl_unit
  import dwm_throttle_ctrl_unit_pkg::*;
  import dwm_pkg::*;
#(
  /// Number of throttle requests
  parameter int unsigned N_THROTTLE_PINS = 2,
  /// Type of selection
  ///   0: takes the minimum value
  ///   1: takes the maximum value
  parameter int unsigned PICK_MAX_NOT_MIN = 0,
  /// Width of the throttle values
  parameter int unsigned TU_UTIL_WIDTH = 7,
  /// Define which throttle mode should be used at idle state
  parameter throttle_mode_e IDLE = E_MAX_LIMIT
)(
  /// Clock, positive edge triggered
  input  wire                                                              i_clk,
  /// Asynchronous reset, active low
  input  wire                                                              i_rst_n,

  /// Value used as default if the throttle is disabled
  input  logic [TU_UTIL_WIDTH-1:0]                                         i_static_settings,
  /// Clock division target is throttle is enabled
  input  logic [N_THROTTLE_PINS-1:0][TU_UTIL_WIDTH-1:0]                    i_throttle_value,
  /// Define the throttle mode
  input  dwm_throttle_ctrl_unit_pkg::throttle_mode_e [N_THROTTLE_PINS-1:0] i_throttle_mode,
  /// Enable the throttle unit
  input  logic            [N_THROTTLE_PINS-1:0]                            i_throttle_en,
  /// Indication to start throttling
  input  logic            [N_THROTTLE_PINS-1:0]                            i_throttle,
  /// Force the enable of the throttle logic
  input  logic            [N_THROTTLE_PINS-1:0]                            i_sw_overwrite,

  /// Baseline cycle time between increments of one for the clock division
  input  dctu_incr_decr_t [N_THROTTLE_PINS-1:0]                            i_throttle_incr_time,
  /// Baseline cycle time between decrements of one for the clock division
  input  dctu_incr_decr_t [N_THROTTLE_PINS-1:0]                            i_throttle_decr_time,
  /// Pre-scale factor for the baseline cycle times above (multiplier)
  input  dctu_prescale_t  [N_THROTTLE_PINS-1:0]                            i_throttle_prescale,

  /// Min or maximum value got fromm throttle units
  output logic [TU_UTIL_WIDTH-1:0]                                         o_data,
  /// Validate the output data
  output logic                                                             o_enable
);

  // $clog2 below returns the ceiling of the log base 2 of the argument (the log rounded up to an integer value)
  localparam int unsigned N_THROTTLE_PINS_LOG = $clog2(N_THROTTLE_PINS);

  typedef logic [TU_UTIL_WIDTH-1:0]     dctu_div_t;

  typedef struct packed {
    dctu_div_t    value;
    logic         en;
  } sel_val_t;

  throttle_mode_e [N_THROTTLE_PINS-1:0] throttle_mode_muxed;
  logic           [N_THROTTLE_PINS-1:0] combined_throttle_vld;
  logic           [N_THROTTLE_PINS-1:0] util_limit_en;
  dctu_div_t      [N_THROTTLE_PINS-1:0] util_limit;

  for (genvar I = 0; I < N_THROTTLE_PINS; I++) begin : g_throttle_ctrl_unit

    // Generate throttle valid request to combined_throttle input of throttle_ctrl_unit
    assign combined_throttle_vld[I] = (i_sw_overwrite[I] | (i_throttle_en[I] & i_throttle[I]));

    // Mux to select the final mode to throttle_ctrl_unit
    assign throttle_mode_muxed[I] = (combined_throttle_vld[I]) ? i_throttle_mode[I] : IDLE;

    // Instantiation of throttle_ctrl_unit
    dwm_throttle_ctrl_unit #(
     .TU_UTIL_WIDTH (TU_UTIL_WIDTH)
    ) u_throttle_ctrl_unit (
      .i_clk                     (i_clk),
      .i_rst_n                   (i_rst_n),
      .i_max_limit               (i_static_settings),
      .i_throttle_limit          (i_throttle_value[I]),
      .i_throttle_mode           (throttle_mode_muxed[I]),
      .i_combined_throttle       (combined_throttle_vld[I]),
      .i_soft_throttle_incr_time (i_throttle_incr_time[I]),
      .i_soft_throttle_decr_time (i_throttle_decr_time[I]),
      .i_soft_throttle_prescale  (i_throttle_prescale[I]),
      .o_util_limit_en           (util_limit_en[I]),
      .o_util_limit              (util_limit[I])
    );
  end : g_throttle_ctrl_unit

// Logic to select the minimum or maximum element (depedning on PICK_MAX_NOT_MIN parameter)

  if (N_THROTTLE_PINS == 1) begin : g_only_one_throttle_value
    always_comb begin
      o_enable = util_limit_en[0];
      o_data   = util_limit[0];
    end
  end // g_only_one_throttle_value

  else begin : g_multiple_throttle_values

    sel_val_t [N_THROTTLE_PINS_LOG-1:0][(N_THROTTLE_PINS/2):0] interm_result;
    sel_val_t [N_THROTTLE_PINS-1:0] init_values;

    // Assign outputs of throttle_ctrl_unit to struct for more convenience
    always_comb begin
      for (int unsigned i=0; i < N_THROTTLE_PINS; i++) begin
        init_values[i].en    = util_limit_en[i];
        init_values[i].value = util_limit[i];
      end
    end

    always_comb begin
      // External loop for the required number of levels of 2-input comparators to select the min/max element
      for (int unsigned level_idx=0; level_idx < N_THROTTLE_PINS_LOG; level_idx++) begin
        // Internal loop for the required number of 2-input comparators per each level
        for (int unsigned cmp_idx=0; cmp_idx <= ((N_THROTTLE_PINS-1)/(2**(level_idx+1))); cmp_idx++) begin
          if(level_idx==0) begin // If this is the first (lowest) level
            if((cmp_idx == ((N_THROTTLE_PINS-1)/(2**(level_idx+1)))) && (N_THROTTLE_PINS % 2)) begin
              // Take the last value without comparison since the total number of values is odd
              interm_result[level_idx][cmp_idx] = init_values[2*cmp_idx];
            end
            else begin
              // For all the others - compare each 2 consecutive output values from throttle_ctrl_unit modules
              interm_result[level_idx][cmp_idx] = f_select_minmax_value(init_values[(2*cmp_idx)+1], init_values[2*cmp_idx]);
            end
          end
          else begin  // For all other levels after the first (lowest) level
            // The following remainder will define if there should have comparator at the end for each level (after the first)
            // or we need to take directly the element from the previous level
            automatic int unsigned remainder_per_level = (N_THROTTLE_PINS % (2**(level_idx+1)));

            // If this is the last comparison per level and determine if we need to take directly the element from the previous level
            if((cmp_idx == ((N_THROTTLE_PINS-1)/(2**(level_idx+1)))) && (remainder_per_level != 0) && (remainder_per_level <= (2*level_idx))) begin
              interm_result[level_idx][cmp_idx] = interm_result[level_idx-1][2*cmp_idx];
            end
            else begin // Otherwise - compare every 2 values for this level
              interm_result[level_idx][cmp_idx] = f_select_minmax_value(interm_result[level_idx-1][(2*cmp_idx)+1], interm_result[level_idx-1][2*cmp_idx]);
            end
          end
        end
      end
    end

   // Flop the final min/max value and associated enable (the outputs to the clock divider)
   always_ff @(posedge i_clk or negedge i_rst_n) begin
     if (~i_rst_n) begin
       o_enable <= 1'b0;
       o_data   <= '0;
     end
     else begin
       o_enable <= interm_result[N_THROTTLE_PINS_LOG-1][0].en;
       o_data   <= interm_result[N_THROTTLE_PINS_LOG-1][0].value;
     end
   end

    // Function to select the min/max element among two input elements
    function automatic sel_val_t f_select_minmax_value(
      input sel_val_t i_element1,
      input sel_val_t i_element0
    );

      f_select_minmax_value.en = (i_element1.en | i_element0.en);

      case({i_element1.en, i_element0.en})
        2'b01: f_select_minmax_value.value = i_element0.value;
        2'b10: f_select_minmax_value.value = i_element1.value;
        2'b11: f_select_minmax_value.value = f_compare_values(i_element1.value, i_element0.value);
        default: f_select_minmax_value.value = '0; // data is invalid so the value does not matter
      endcase
    endfunction

    // Function to make the comparison between 2 values (comparator)
    function automatic dctu_div_t f_compare_values(
      input dctu_div_t i_value1,
      input dctu_div_t i_value0
    );

      if (PICK_MAX_NOT_MIN) begin // Select the max value
        f_compare_values = (i_value0 >= i_value1) ? i_value0 : i_value1;
      end
      else begin // Select the min value
        f_compare_values = (i_value0 <= i_value1) ? i_value0 : i_value1;
      end
    endfunction

  end // g_multiple_throttle_values

endmodule
