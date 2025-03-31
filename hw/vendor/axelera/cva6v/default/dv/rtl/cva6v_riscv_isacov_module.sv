`timescale 1ps/1ps

// Include the coverage definition
`include "RISCV_coverage_cva6v.svh"

module cva6v_riscv_isacov_module ();

    // Parameters for rvviTrace interface, align with RISCV architecture specifications
    parameter int ILEN   = 32;  // Instruction length in bits
    parameter int XLEN   = 64;  // General Purpose Register (GPR) length in bits
    parameter int FLEN   = 32;  // Floating Point Register (FPR) length in bits
    parameter int VLEN   = 4096; // Vector register size in bits
    parameter int NHART  = 1;   // Number of harts (Hardware threads) supported
    parameter int RETIRE = 1;   // Number of instructions that can retire during valid event

    // Constants derived from parameters
    localparam int BASE_VALUE_BITS = 32;  // Assuming base_value is 32 bits
    localparam int NUM_FULL_REPEATS = VLEN / BASE_VALUE_BITS;
    localparam int REMAINING_BITS = VLEN % BASE_VALUE_BITS;

    // Clock and reset signals
    logic clk;
    logic rst_n;

    // Instantiate the rvviTrace interface
    rvviTrace #(ILEN, XLEN, FLEN, VLEN, NHART, RETIRE) rvvi_trace();

    // Instance of the coverage class
    coverage_cva6v #(ILEN, XLEN, FLEN, VLEN, NHART, RETIRE) cov;

    // Variables for file reading and sampling
    string spike_log_name;
    integer file;
    integer total_lines;
    integer processed_lines;

    // Variables to store parsed values (module scope)
    logic                      valid;       // Retired instruction
    logic [63:0]               order;       // Unique instruction order count
    logic [(ILEN-1):0]         insn;        // Instruction bit pattern
    logic                      trap;        // Trapped instruction
    logic                      halt;        // Halted instruction
    logic                      intr;        // Interrupt
    logic [1:0]                mode;        // Privilege mode of operation
    logic [1:0]                ixl;         // XLEN mode 32/64 bit

    logic [(XLEN-1):0]         pc_rdata;    // PC of insn
    logic [(XLEN-1):0]         pc_wdata;    // PC of next instruction

    // X Registers
    logic [31:0]               x_wb;        // X data writeback (change) flag
    logic [31:0][(XLEN-1):0]   x_wdata;     // X data value

    // F Registers
    logic [31:0]               f_wb;        // F data writeback (change) flag
    logic [31:0][(FLEN-1):0]   f_wdata;     // F data value

    // V Registers
    logic [31:0]               v_wb;        // V data writeback (change) flag
    logic [31:0][(VLEN-1):0]   v_wdata;     // V data value

    // Control & State Registers
    logic [4095:0]             csr_wb;      // CSR writeback (change) flag
    logic [4095:0][(XLEN-1):0] csr;         // Full CSR Address range

    logic                      lrsc_cancel; // Implementation-defined cancel

    string disass_quoted;
    string disass;
    string inst_name;

    // Function to trim leading and trailing spaces from a string
    function automatic string trim_spaces(input string str);
        automatic int start_idx;
        automatic int end_idx;
        automatic string result;
        automatic int i;

        start_idx = 0;
        end_idx = str.len() - 1;
        // Remove leading spaces
        while ((start_idx <= end_idx) && (str[start_idx] == " ")) begin
            start_idx++;
        end
        // Remove trailing spaces
        while ((end_idx >= start_idx) && (str[end_idx] == " ")) begin
            end_idx--;
        end
        if (start_idx > end_idx) begin
            return "";
        end else begin
            result = "";
            for (i = start_idx; i <= end_idx; i++) begin
                result = {result, str[i]};
            end
            return result;
        end
    endfunction

    // Function to find the index of a character in a string
    function automatic int find_char(input string str, input byte char_to_find);
        automatic int idx;
        for (idx = 0; idx < str.len(); idx++) begin
            if (str[idx] == char_to_find) begin
                return idx;
            end
        end
        return -1;
    endfunction

    // Function to get a substring from a string
    function automatic string substring(input string str, input int start_idx, input int end_idx);
        automatic string result;
        automatic int i;
        result = "";
        for (i = start_idx; i <= end_idx; i++) begin
            result = {result, str[i]};
        end
        return result;
    endfunction

    // Clock generation
    initial begin
        clk = 0;
        forever #50 clk = ~clk; // Toggle clk every 50ps (10 GHz clock)
    end

    // Reset generation
    initial begin
        rst_n = 0;
        #100 rst_n = 1; // Deassert reset after 100 ps
    end

    // Create an instance of the coverage class passing the rvviTrace interface reference
    initial begin
        integer temp_file;
        string temp_line;    // Wait for reset deassertion
        @(posedge rst_n);
        // Create coverage instance
        cov = new(rvvi_trace);
        if (!$value$plusargs("CSV_FILENAME=%s", spike_log_name)) begin
            $fatal("CSV filename not specified.");
        end

        // First pass to count total lines

        total_lines = 0;
        temp_file = $fopen(spike_log_name, "r");
        if (temp_file == 0) begin
            $fatal("Failed to open file %s for line counting", spike_log_name);
        end
        while (!$feof(temp_file)) begin
            if ($fgets(temp_line, temp_file) != 0) begin
                total_lines++;
            end
        end
        $fclose(temp_file);

        // Now open the file for actual processing
        file = $fopen(spike_log_name, "r");
        if (file == 0) begin
            $fatal("Failed to open file %s", spike_log_name);
        end

        processed_lines = 0;
    end

    // Continuous assignments to drive rvvi_trace interface signals
    assign rvvi_trace.clk = clk;
    assign rvvi_trace.valid[0][0] = valid;
    assign rvvi_trace.order[0][0] = order;
    assign rvvi_trace.insn[0][0] = insn;
    assign rvvi_trace.trap[0][0] = trap;
    assign rvvi_trace.halt[0][0] = halt;
    assign rvvi_trace.intr[0][0] = intr;
    assign rvvi_trace.mode[0][0] = mode;
    assign rvvi_trace.ixl[0][0] = ixl;
    assign rvvi_trace.pc_rdata[0][0] = pc_rdata;
    assign rvvi_trace.pc_wdata[0][0] = pc_wdata;
    assign rvvi_trace.x_wb[0][0] = x_wb;
    assign rvvi_trace.x_wdata[0][0] = x_wdata;
    assign rvvi_trace.f_wb[0][0] = f_wb;
    assign rvvi_trace.f_wdata[0][0] = f_wdata;
    assign rvvi_trace.v_wb[0][0] = v_wb;
    assign rvvi_trace.v_wdata[0][0] = v_wdata;
    assign rvvi_trace.csr_wb[0][0] = csr_wb;
    assign rvvi_trace.csr[0][0] = csr;
    assign rvvi_trace.lrsc_cancel[0][0] = lrsc_cancel;

    // Sampling at the clock edge
    always @(posedge clk) begin
        // Variable declarations at the top of the procedural block
        string line;
        integer status;
        string reg_value_str;
        int split_idx;
        int count;
        logic [BASE_VALUE_BITS-1:0] base_value;
        string base_value_str;
        string count_str;
        int reg_index;
        int csr_index;
        int i;
        integer idx;
        string token;
        integer field_count;
        string fields[0:20]; // Adjust the size based on the number of fields (0 to 20)

        if (rst_n) begin
            if (!$feof(file)) begin
                // Correct usage of $fgets
                status = $fgets(line, file);
                if (status != 0) begin
                    processed_lines++;
                    $display("Processing %0d/%0d lines", processed_lines, total_lines);

                    // Remove trailing newline if present
                    if (line.len() > 0 && (line[line.len()-1] == "\n" || line[line.len()-1] == "\r")) begin
                        line = line.substr(0, line.len()-2);
                    end

                    // Initialize variables for parsing
                    idx = 0;
                    field_count = 0;
                    token = "";

                    // Parse the line into fields based on semicolons
                    while (idx < line.len()) begin
                        if (line[idx] != ";") begin
                            token = {token, line[idx]};
                        end else begin
                            fields[field_count] = token;
                            field_count = field_count + 1;
                            token = "";
                        end
                        idx = idx + 1;
                    end
                    // Add the last token
                    fields[field_count] = token;
                    field_count = field_count + 1;

                    // Now assign fields to variables
                    if (field_count >= 21) begin
                        // Assign fields to variables using $sscanf
                        status = $sscanf(fields[0], "%d", valid);
                        status = $sscanf(fields[1], "%d", order);
                        status = $sscanf(fields[2], "%h", insn);
                        status = $sscanf(fields[3], "%d", trap);
                        status = $sscanf(fields[4], "%d", halt);
                        status = $sscanf(fields[5], "%d", intr);
                        status = $sscanf(fields[6], "%d", mode);
                        status = $sscanf(fields[7], "%d", ixl);
                        status = $sscanf(fields[8], "%h", pc_rdata);
                        status = $sscanf(fields[9], "%h", pc_wdata);

                        // Initialize writeback flags
                        x_wb = 32'b0;
                        f_wb = 32'b0;
                        v_wb = 32'b0;
                        csr_wb = 4096'b0;

                        // Parse and assign x_wb and x_wdata
                        if (fields[10] != "") begin
                            status = $sscanf(fields[10], "%d", reg_index);
                            if (reg_index >= 0 && reg_index < 32) begin
                                x_wb[reg_index] = 1'b1;
                                // Parse x_wdata[reg_index] from fields[11]
                                if (fields[11] != "") begin
                                    status = $sscanf(fields[11], "%h", x_wdata[reg_index]);
                                    // Print x_wdata
                                    $display("x_wb[%0d]=%b x_wdata[%0d]=%h", reg_index, x_wb[reg_index], reg_index, x_wdata[reg_index]);
                                end
                            end
                        end

                        // Parse and assign f_wb and f_wdata
                        if (fields[12] != "") begin
                            // Print fields for debugging
                            $display("fields[12]=%s fields[13]=%s", fields[12], fields[13]);
                            status = $sscanf(fields[12], "%d", reg_index);
                            if (reg_index >= 0 && reg_index < 32) begin
                                f_wb[reg_index] = 1'b1;
                                // Parse f_wdata[reg_index] from fields[13]
                                if (fields[13] != "") begin
                                    status = $sscanf(fields[13], "%h", f_wdata[reg_index]);
                                    // Print f_wdata
                                    $display("f_wb[%0d]=%b f_wdata[%0d]=%h", reg_index, f_wb[reg_index], reg_index, f_wdata[reg_index]);
                                end
                            end
                        end

                        // Parse and assign v_wb and v_wdata
                        if (fields[14] != "") begin
                            // Print fields for debugging
                            $display("fields[14]=%s fields[15]=%s", fields[14], fields[15]);
                            status = $sscanf(fields[14], "%d", reg_index);
                            if (reg_index >= 0 && reg_index < 32) begin
                                v_wb[reg_index] = 1'b1;
                                // Parse v_wdata[reg_index] from fields[15]
                                if (fields[15] != "") begin
                                    reg_value_str = trim_spaces(fields[15]);
                                    split_idx = find_char(reg_value_str, "^");
                                    if (split_idx != -1) begin
                                        // Format is '0x0^1024'
                                        base_value_str = substring(reg_value_str, 0, split_idx - 1);
                                        count_str = substring(reg_value_str, split_idx + 1, reg_value_str.len() - 1);
                                        status = $sscanf(count_str, "%d", count);
                                        status = $sscanf(base_value_str, "%h", base_value);

                                        // Build v_wdata[reg_index] using replication
                                        v_wdata[reg_index] = { NUM_FULL_REPEATS { base_value } };

                                        // Handle remaining bits if any
                                        if (REMAINING_BITS != 0) begin
                                            v_wdata[reg_index][NUM_FULL_REPEATS*BASE_VALUE_BITS +: REMAINING_BITS] = base_value[REMAINING_BITS-1:0];
                                        end
                                    end else begin
                                        // Assume reg_value_str is a hex string representing the vector register
                                        status = $sscanf(reg_value_str, "%h", v_wdata[reg_index]);
                                    end
                                    // Print v_wdata
                                    $display("v_wb[%0d]=%b v_wdata[%0d]=%h", reg_index, v_wb[reg_index], reg_index, v_wdata[reg_index]);
                                end
                            end
                        end

                        // Parse and assign csr_wb and csr
                        if (fields[16] != "") begin
                            status = $sscanf(fields[16], "%d", csr_index);
                            if (csr_index >= 0 && csr_index < 4096) begin
                                csr_wb[csr_index] = 1'b1;
                                // Parse csr[csr_index] from fields[17]
                                if (fields[17] != "") begin
                                    status = $sscanf(fields[17], "%h", csr[csr_index]);
                                end
                            end
                        end

                        status = $sscanf(fields[18], "%d", lrsc_cancel);
                        disass_quoted = fields[19];
                        inst_name = fields[20];

                        // Remove the surrounding double quotes from disass
                        if (disass_quoted.len() >= 2 && (disass_quoted[0] == "\"") && (disass_quoted[disass_quoted.len()-1] == "\"")) begin
                            disass = substring(disass_quoted, 1, disass_quoted.len() - 2);
                        end else begin
                            disass = disass_quoted;
                        end

                        // Call the sample function
                        cov.sample(0, 0, 0, disass);

                        // Optionally display the disassembly
                        $display("disass: %0s \n", disass);

                    end else begin
                        $error("Error parsing line: %s \n", line);
                    end
                end else begin
                    // End of file or read error
                    $fclose(file);
                    $finish; // Optionally terminate simulation
                end
            end else begin
                // End of file reached
                $display("Processed %0d/%0d lines", total_lines, total_lines);
                $fclose(file);
                $finish;
            end
        end
    end

endmodule
