interface dp_cmd_gen_cmdb_if(input bit clk, input bit rst_n);

    aic_dp_cmd_gen_pkg::cmdb_cmd_t    cmdb_command;
    aic_dp_cmd_gen_pkg::cmd_format_e  cmdb_format;
    logic                             cmdb_valid;
    logic                             cmdb_ready;
    logic                             cmdb_done;
    aic_dp_cmd_gen_pkg::loop_errors_t cmdb_errors;
    int unsigned                      cycle_count;

    logic                             cmdb_flush;

    initial begin
      cmdb_flush  <= 1'b0;
      cycle_count <= 0;

      forever begin
        @(posedge clk);
        cycle_count <= cycle_count + 1;
      end
    end
endinterface : dp_cmd_gen_cmdb_if 

interface dp_cmd_gen_command_if #(parameter type dp_command_t) (input bit clk, input bit rst_n);

  dp_command_t                          command_data;
  aic_dp_cmd_gen_pkg::metadata_t        command_metadata;
  aic_dp_cmd_gen_pkg::loop_iterations_t command_iterations;
  logic                                 command_last;
  logic                                 command_valid;
  logic                                 command_ready;
  logic                                 command_done;

endinterface : dp_cmd_gen_command_if 
