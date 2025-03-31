//
// Copyright (c) 2005-2024 Imperas Software Ltd. All Rights Reserved.
//
// THIS SOFTWARE CONTAINS CONFIDENTIAL INFORMATION AND TRADE SECRETS
// OF IMPERAS SOFTWARE LTD. USE, DISCLOSURE, OR REPRODUCTION IS PROHIBITED
// EXCEPT AS MAY BE PROVIDED FOR IN A WRITTEN AGREEMENT WITH IMPERAS SOFTWARE LTD.
//
//

class RISCV_instruction
    #(
    parameter int ILEN   = 32,  // Instruction length in bits
    parameter int XLEN   = 64,  // GPR length in bits
    parameter int FLEN   = 32,  // FPR length in bits
    parameter int VLEN   = 4096, // Vector register size in bits
    parameter int NHART  = 1,   // Number of harts reported
    parameter int RETIRE = 1    // Number of instructions that can retire during valid event
);
    string ins_str;
    ops_t ops[6];
    int hart;
    int issue;
    bit trap;
    bit print_reg_values;
    riscvTraceData #(ILEN, XLEN, FLEN, VLEN) current;
    riscvTraceData #(ILEN, XLEN, FLEN, VLEN) prev;

    riscvTraceData #(ILEN, XLEN, FLEN, VLEN)traceDataQ[(NHART-1):0][(RETIRE-1):0][$:`NUM_RVVI_DATA];

    function new (int hart, int issue, riscvTraceData #(ILEN, XLEN, FLEN, VLEN)traceDataQ[(NHART-1):0][(RETIRE-1):0][$:`NUM_RVVI_DATA]);
        string insbin, ins_str, op[6], key, val;

        int num, i, j;
        string s;

        this.hart = hart;
        this.issue = issue;

        this.traceDataQ = traceDataQ;

        this.current = traceDataQ[hart][issue][`SAMPLE_CURRENT];
        this.prev = traceDataQ[hart][issue][`SAMPLE_PREV];

        this.trap = this.current.trap;

        s = this.current.disass;
        foreach (this.current.disass[c]) begin
            s[c] = (this.current.disass[c] == ",")? " " : this.current.disass[c];
        end

        num = $sscanf (s, "%s %s %s %s %s %s %s %s", insbin, ins_str, op[0], op[1], op[2], op[3], op[4], op[5]);
        this.ins_str = ins_str;

        // Check if stack reg list (used by cm.push/cm.pop) and combine full list into single operand
        if (op[0][0] == "{") begin
            int found = 0;
            for (i = 0; i < op[1].len(); i++) begin
                if (op[1][i] == "}") begin
                    op[0] = {op[0],",",op[1]};
                    op[1] = op[2];
                    num = num - 1;
                    found = 1;
                end
            end
            if (found == 0) begin
                for (i = 0; i < op[2].len(); i++) begin
                    if (op[2][i] == "}") begin
                        op[0] = {op[0],",",op[1],",",op[2]};
                        op[1] = op[3];
                        num = num - 2;
                    end
                end
            end
        end

        for (i=0; i<num-2; i++) begin
            key = op[i];
            this.ops[i].key=op[i]; // in case we dont update it as an indexed
            this.ops[i].val=""; // not used
            for (j = 0; j < key.len(); j++) begin
                if (key[j] == "(" && j != 0) begin  // if indexed addressing, convert offset(rs1) to op[i].key=offset op[i+1].key=rs1
                    this.ops[i].key = key.substr(0,j-1); // offset
                    this.ops[i+1].key = key.substr(j+1,key.len()-2);

                    // for xPulp - lose the rs1! post increment operator "!"
                    if (this.ops[i+1].key[this.ops[i+1].key.len()-1] == "!") begin
                        string opstr = this.ops[i+1].key.substr(0,this.ops[i+1].key.len()-2);
                        this.ops[i+1].key = opstr;
                    end

                    i++; // step over +1
                    break;
                end else if (key[j] == "(") begin  // if xpulp post increment convert (rs1) to op[i].key=rs1

                    // for xPulp - lose the (rs1) post increment brackets
                    if (this.ops[i].key[this.ops[i].key.len()-1] == ")") begin
                        string opstr = this.ops[i].key.substr(1,this.ops[i].key.len()-2);
                        this.ops[i].key = opstr;
                    end
                    break;
                end
            end
            //$display("indirect ins_str(%s) op[0](%0s).key(%s) op[1](%s).key(%s) op[2](%s).key(%s) op[3](%s).key(%s)",
            //    ins_str, op[0], this.ops[0].key, op[1], this.ops[1].key, op[2], this.ops[2].key, op[3], this.ops[3].key);
        end
        for (i=0; i<num-2; i++) begin
            if (this.ops[i].key[0] == "x") begin
                int idx = get_gpr_num(this.ops[i].key);
                //$display("SAMPLE: %0s op[%0d]=%0s gpr(%0d)", ins_str,i, this.ops[i].key, idx);
                if (idx < 0) begin
                    this.ops[i].val = this.ops[i].key; // it is an immed already there
                end else begin
                    this.ops[i].val = string'(this.current.x_wdata[idx]);
                end
            end else if (this.ops[i].key[0] == "f") begin
                int idx = get_fpr_num(this.ops[i].key);
                if (idx < 0) begin
                    this.ops[i].val = this.ops[i].key; // it is an immed already there
                end else begin
                    this.ops[i].val = string'(this.current.f_wdata[idx]);
                end

            end else begin
                this.ops[i].val = this.ops[i].key;
            end
        end
    endfunction

    virtual function  `XLEN_INT get_gpr_val(int hart, int issue, string key, int prev);
        int idx = get_gpr_num(key);
        $display("get gpr val = %0d , get gpr num= %0d ", traceDataQ[hart][issue][prev].x_wdata[idx] , idx);
        if (idx >= 0) begin
            return traceDataQ[hart][issue][prev].x_wdata[idx];
        end
        return 0;
    endfunction


    function `XLEN_INT get_fpr_val(int hart, int issue, string key, int prev);

        int idx = get_fpr_num(key);

        if (idx >= 0) begin
            return traceDataQ[hart][issue][prev].f_wdata[idx];
        end
        return 0;
    endfunction


    function `XLEN_INT get_pc();
        return current.pc_rdata;
    endfunction

    function gpr_name_t get_gpr_reg (string key);
        $display("reg gpr key = %0s", key);
        case (key)
                "x0": return x0;
            "zero": return x0;
            "x1": return x1;
            "ra": return x1;
            "x2": return x2;
            "sp": return x2;
            "x3": return x3;
            "gp": return x3;
            "x4": return x4;
            "tp": return x4;
            "x5": return x5;
            "t0": return x5;
            "x6": return x6;
            "t1": return x6;
            "x7": return x7;
            "t2": return x7;
            "x8": return x8;
            "s0": return x8;
            "x9": return x9;
            "s1": return x9;
            "x10": return x10;
            "a0": return x10;
            "x11": return x11;
            "a1": return x11;
            "x12": return x12;
            "a2": return x12;
            "x13": return x13;
            "a3": return x13;
            "x14": return x14;
            "a4": return x14;
            "x15": return x15;
            "a5": return x15;
    `ifndef COVER_BASE_RV32E
            "x16": return x16;
            "a6": return x16;
            "x17": return x17;
            "a7": return x17;
            "x18": return x18;
            "s2": return x18;
            "x19": return x19;
            "s3": return x19;
            "x20": return x20;
            "s4": return x20;
            "x21": return x21;
            "s5": return x21;
            "x22": return x22;
            "s6": return x22;
            "x23": return x23;
            "s7": return x23;
            "x24": return x24;
            "s8": return x24;
            "x25": return x25;
            "s9": return x25;
            "x26": return x26;
            "s10": return x26;
            "x27": return x27;
            "s11": return x27;
            "x28": return x28;
            "t3": return x28;
            "x29": return x29;
            "t4": return x29;
            "x30": return x30;
            "t5": return x30;
            "x31": return x31;
            "t6": return x31;
    `endif
            default: begin
                $display("ERROR: SystemVerilog Functional Coverage: get_gpr_reg(%0s) not found gpr", key);
                //TODO $finish(-1);
            end
            endcase
    endfunction




    function int get_imm(string s);
        int val;
        if (s[1] == "x") begin
            s = s.substr(2,s.len()-1);
            val = s.atohex ();
        end else if (s[0] == "-") begin
            s = s.substr(1,s.len()-1);
            val = 0 - s.atoi();
        end else begin
            val = s.atoi();
        end
        return val;
    endfunction


    function fpr_name_t get_fpr_reg (string key);
        case (key)
                "f0", "ft0": return f0;
            "abi_f0": return f0;
            "f1", "ft1": return f1;
            "abi_f1": return f1;
            "f2", "ft2": return f2;
            "abi_f2": return f2;
            "f3", "ft3": return f3;
            "abi_f3": return f3;
            "f4", "ft4": return f4;
            "abi_f4": return f4;
            "f5", "ft5": return f5;
            "abi_f5": return f5;
            "f6", "ft6": return f6;
            "abi_f6": return f6;
            "f7", "ft7": return f7;
            "abi_f7": return f7;
            "f8", "ft8": return f8;
            "abi_f8": return f8;
            "f9", "ft9": return f9;
            "abi_f9": return f9;
            "f10": return f10;
            "abi_f10": return f10;
            "f11", "ft11": return f11;
            "abi_f11": return f11;
            "f12", "ft12": return f12;
            "abi_f12": return f12;
            "f13", "ft13": return f13;
            "abi_f13": return f13;
            "f14", "ft14": return f14;
            "abi_f14": return f14;
            "f15", "ft15": return f15;
            "abi_f15": return f15;
            "f16", "ft16": return f16;
            "abi_f16": return f16;
            "f17", "ft17": return f17;
            "abi_f17": return f17;
            "f18", "ft18": return f18;
            "abi_f18": return f18;
            "f19", "ft19": return f19;
            "abi_f19": return f19;
            "f20": return f20;
            "abi_f20": return f20;
            "f21", "ft21": return f21;
            "abi_f21": return f21;
            "f22", "ft22": return f22;
            "abi_f22": return f22;
            "f23", "ft23": return f23;
            "abi_f23": return f23;
            "f24", "ft24": return f24;
            "abi_f24": return f24;
            "f25", "ft25": return f25;
            "abi_f25": return f25;
            "f26", "ft26": return f26;
            "abi_f26": return f26;
            "f27", "ft27": return f27;
            "abi_f27": return f27;
            "f28", "ft28": return f28;
            "abi_f28": return f28;
            "f29", "ft29": return f29;
            "abi_f29": return f29;
            "f30": return f30;
            "abi_f30": return f30;
            "f31", "ft31": return f31;
            "abi_f31": return f31;
            default: begin
                $display("ERROR: SystemVerilog Functional Coverage: get_fpr_reg(%0s) not found fpr", key);
                //todo $finish(-1);
            end
        endcase
    endfunction

    function vdr_name_t get_vdr_reg (string key);
        $display("reg vdr key = %0s", key);
        case (key)
            "v0": return v0;
            "v1": return v1;
            "v2": return v2;
            "v3": return v3;
            "v4": return v4;
            "v5": return v5;
            "v6": return v6;
            "v7": return v7;
            "v8": return v8;
            "v9": return v9;
            "v10": return v10;
            "v11": return v11;
            "v12": return v12;
            "v13": return v13;
            "v14": return v14;
            "v15": return v15;
            "v16": return v16;
            "v17": return v17;
            "v18": return v18;
            "v19": return v19;
            "v20": return v20;
            "v21": return v21;
            "v22": return v22;
            "v23": return v23;
            "v24": return v24;
            "v25": return v25;
            "v26": return v26;
            "v27": return v27;
            "v28": return v28;
            "v29": return v29;
            "v30": return v30;
            "v31": return v31;
            "v0_v1": return v0_v1;
            "v2_v3": return v2_v3;
            "v4_v5": return v4_v5;
            "v6_v7": return v6_v7;
            "v8_v9": return v8_v9;
            "v10_v11": return v10_v11;
            "v12_v13": return v12_v13;
            "v14_v15": return v14_v15;
            "v16_v17": return v16_v17;
            "v18_v19": return v18_v19;
            "v20_v21": return v20_v21;
            "v22_v23": return v22_v23;
            "v24_v25": return v24_v25;
            "v26_v27": return v26_v27;
            "v28_v29": return v28_v29;
            "v30_v31": return v30_v31;
            "v0_v3": return v0_v3;
            "v4_v7": return v4_v7;
            "v8_v11": return v8_v11;
            "v12_v15": return v12_v15;
            "v16_v19": return v16_v19;
            "v20_v23": return v20_v23;
            "v24_v27": return v24_v27;
            "v28_v31": return v28_v31;
            "v0_v7": return v0_v7;
            "v8_v15": return v8_v15;
            "v16_v23": return v16_v23;
            "v24_v31": return v24_v31;
            default: begin
                $display("ERROR: SystemVerilog Functional Coverage: get_vdr_reg(%0s) not found vdr", key);
                //TODO $finish(-1);
            end
        endcase
    endfunction


    function int get_csr_addr(int hart, string s);
        return rvviRefCsrIndex(hart, s);
    endfunction

    virtual function void add_rd(int offset);
        current.has_rd = 1;
        current.rd = ops[offset].key;
        current.rd_val = current.x_wdata[get_gpr_num(ops[offset].key)];
        $display("add_rd current.rd_val", current.rd_val);
        current.rd_val_pre = prev.x_wdata[get_gpr_num(ops[offset].key)];
        $display("add_rd current.rd_val_pre", current.rd_val_pre);
    endfunction

    virtual function void add_rs1(int offset);
        current.has_rs1 = 1;
        current.rs1 = ops[offset].key;
        current.rs1_val = prev.x_wdata[get_gpr_num(ops[offset].key)];
        $display("add_rs1 current.rrs1_val", current.rs1_val);
    endfunction

    virtual function void add_rs2(int offset);
        current.has_rs2 = 1;
        current.rs2 = ops[offset].key;
        current.rs2_val = prev.x_wdata[get_gpr_num(ops[offset].key)];
        $display("add_rs2 current.rs2_val", current.rs2_val);
    endfunction

    virtual function void add_rs3(int offset);
        current.has_rs3 = 1;
        current.rs3 = ops[offset].key;
        current.rs3_val = prev.x_wdata[get_gpr_num(ops[offset].key)];
    endfunction

    virtual function void add_imm(int offset);
        current.imm = get_imm(ops[offset].key);
    endfunction

    virtual function void add_imm2(int offset);
        current.imm2 = get_imm(ops[offset].key);
    endfunction

    virtual function void add_imm3(int offset);
        current.imm3 = get_imm(ops[offset].key);
    endfunction

    virtual function void add_imm_addr(int offset);
        current.imm = ops[offset].key.atohex();
    endfunction

    virtual function void add_csr(int offset);
        current.imm2 = rvviRefCsrIndex(current.hart, ops[offset].key);
    endfunction

    virtual function void add_mem_offset(int offset);
        current.imm = get_imm(ops[offset].key);
    endfunction

    virtual function void add_mem_address();
        current.mem_addr = current.rs1_val + current.imm;
    endfunction

    virtual function void add_fd(int offset, int finx=0);
        current.has_fd = 1;
        current.fd = ops[offset].key;
        if (finx) begin
            current.fd_val = current.x_wdata[get_gpr_num(ops[offset].key)];
            current.fd_val_pre = prev.x_wdata[get_gpr_num(ops[offset].key)];
        end
        else begin
            current.fd_val = current.f_wdata[get_fpr_num(ops[offset].key)];
            current.fd_val_pre = prev.f_wdata[get_fpr_num(ops[offset].key)];
        end
    endfunction

    virtual function void add_fs1(int offset, int finx=0);
        current.has_fs1 = 1;
        current.fs1 = ops[offset].key;
        if (finx) begin
            current.fs1_val = prev.x_wdata[get_gpr_num(ops[offset].key)];
        end
        else begin
            current.fs1_val = prev.f_wdata[get_fpr_num(ops[offset].key)];
        end
    endfunction

    virtual function void add_fs2(int offset, int finx=0);
        current.has_fs2 = 1;
        current.fs2 = ops[offset].key;
        if (finx) begin
            current.fs2_val = prev.x_wdata[get_gpr_num(ops[offset].key)];
        end
        else begin
            current.fs2_val = prev.f_wdata[get_fpr_num(ops[offset].key)];
        end
    endfunction

    virtual function void add_fs3(int offset, int finx=0);
        current.has_fs3 = 1;
        current.fs3 = ops[offset].key;
        if (finx) begin
            current.fs3_val = prev.x_wdata[get_gpr_num(ops[offset].key)];
        end
        else begin
            current.fs3_val = prev.f_wdata[get_fpr_num(ops[offset].key)];
        end
    endfunction

    virtual function void add_vd(int offset, int emul);
        int n;
        string s,e;
        current.has_vd = 1;
        current.vd = ops[offset].key;
        n = get_vdr_num(ops[offset].key);
        if (emul > 1 && emul <= 8) begin
            s.itoa(n);
            e.itoa(n+emul-1);
            current.vd = {"v",s,"_v",e};
            $display("vd=%s, lmul=%d",current.vd,emul);
        end
        current.vd_val = current.v_wdata[n];
        current.vd_val_pre = prev.v_wdata[n];
    endfunction

    virtual function void add_vs1(int offset, int emul);
        int n;
        string s,e;
        current.has_vs1 = 1;
        current.vs1 = ops[offset].key;
         n = get_vdr_num(ops[offset].key);
        if (emul > 1 && emul <= 8) begin
            s.itoa(n);
            e.itoa(n+emul-1);
            current.vs1 = {"v",s,"_v",e};
            $display("vs1=%s, lmul=%d",current.vs1,emul);
        end
        current.vs1_val = prev.v_wdata[get_vdr_num(ops[offset].key)];
    endfunction

    virtual function void add_vs2(int offset, int emul);
        int n;
        string s,e;
        current.has_vs2 = 1;
        current.vs2 = ops[offset].key;
         n = get_vdr_num(ops[offset].key);
        if (emul > 1 && emul <= 8) begin
            s.itoa(n);
            e.itoa(n+emul-1);
            current.vs2 = {"v",s,"_v",e};
            $display("vs2=%s, lmul=%d",current.vs2,emul);
        end
        current.vs2_val = prev.v_wdata[get_vdr_num(ops[offset].key)];
    endfunction

    virtual function void add_vs3(int offset, int emul);
        int n;
        string s,e;
        current.has_vs3 = 1;
        current.vs3 = ops[offset].key;
        n = get_vdr_num(ops[offset].key);
        if (emul > 1 && emul <= 8) begin
            s.itoa(n);
            e.itoa(n+emul-1);
            current.vs3 = {"v",s,"_v",e};
            $display("vs3=%s, lmul=%d",current.vs3,emul);
        end
        current.vs3_val = prev.v_wdata[get_vdr_num(ops[offset].key)];
    endfunction

    virtual function void add_vm(int offset);
        current.has_vm = 1;
        current.vm = ops[offset].key;
        current.vm_val = prev.v_wdata[get_vdr_num(ops[offset].key)];
    endfunction

 function void print_ins();
        int i, j, k, idx;

        $display("RISCV_instruction:");
        $display("  ins_str = %0s", ins_str);
        $display("  ops:");
        for (i = 0; i < 6; i++) begin
            $display("    ops[%0d]: key = %0s, val = %0s", i, ops[i].key, ops[i].val);
        end
        $display("  hart = %0d", hart);
        $display("  issue = %0d", issue);
        $display("  trap = %0b", trap);

        // Print current riscvTraceData
        $display("  current:");
        print_riscvTraceData(current, "current");

        // Print prev riscvTraceData
        $display("  prev:");
        print_riscvTraceData(prev, "prev");

        // Print traceDataQ
        $display("  traceDataQ:");
        for (i = 0; i < NHART; i++) begin
            for (j = 0; j < RETIRE; j++) begin
                if (traceDataQ[i][j].size() > 0) begin
                    $display("    traceDataQ[%0d][%0d]:", i, j);
                    for (k = 0; k < traceDataQ[i][j].size(); k++) begin
                        $display("      traceDataQ[%0d][%0d][%0d]:", i, j, k);
                        print_riscvTraceData(traceDataQ[i][j][k], $sformatf("traceDataQ[%0d][%0d][%0d]", i, j, k));
                    end
                end
            end
        end
    endfunction

    // Helper function to print riscvTraceData instance
    function automatic void print_riscvTraceData(riscvTraceData #(ILEN, XLEN, FLEN, VLEN) data, string name);
        int idx;
        $display("    %0s:", name);
        $display("      valid        = %0b", data.valid);
        $display("      order        = %0d", data.order);
        $display("      insn         = 0x%0h", data.insn);
        $display("      trap         = %0b", data.trap);
        $display("      halt         = %0b", data.halt);
        $display("      intr         = %0b", data.intr);
        $display("      mode         = %0b", data.mode);
        $display("      ixl          = %0b", data.ixl);
        $display("      pc_rdata     = 0x%0h", data.pc_rdata);
        $display("      pc_wdata     = 0x%0h", data.pc_wdata);

       print_reg_values=1;

        if (print_reg_values) begin
        // X Registers
        $display("      x_wdata:");
        for (idx = 0; idx < 32; idx++) begin
            $display("        x_wdata[%0d] = 0x%0h", idx, data.x_wdata[idx]);
        end
        $display("      x_wb:");
        for (idx = 0; idx < 32; idx++) begin
            $display("        x_wb[%0d] = %0b", idx, data.x_wb[idx]);
        end

        // F Registers
        $display("      f_wdata:");
        for (idx = 0; idx < 32; idx++) begin
            $display("        f_wdata[%0d] = 0x%0h", idx, data.f_wdata[idx]);
        end
        $display("      f_wb:");
        for (idx = 0; idx < 32; idx++) begin
            $display("        f_wb[%0d] = %0b", idx, data.f_wb[idx]);
        end

        // V Registers
        $display("      v_wdata:");
        for (idx = 0; idx < 32; idx++) begin
            $display("        v_wdata[%0d] = 0x%0h", idx, data.v_wdata[idx]);
        end
        $display("      v_wb:");
        for (idx = 0; idx < 32; idx++) begin
            $display("        v_wb[%0d] = %0b", idx, data.v_wb[idx]);
        end

        end

        // CSR Registers (Only print if written back)
        $display("      csr (written back):");
        for (idx = 0; idx < 4096; idx++) begin
            if (data.csr_wb[idx]) begin
                $display("        csr[%0d] = 0x%0h", idx, data.csr[idx]);
            end
        end

        $display("      lrsc_cancel  = %0b", data.lrsc_cancel);
        $display("      hart         = %0d", data.hart);
        $display("      issue        = %0d", data.issue);
        $display("      disass       = %0s", data.disass);
        $display("      inst_name    = %0s", data.inst_name);
        $display("      inst_category= %0d", data.inst_category);

        // Operand flags
        $display("      has_rd       = %0b", data.has_rd);
        $display("      has_rs1      = %0b", data.has_rs1);
        $display("      has_rs2      = %0b", data.has_rs2);
        $display("      has_rs3      = %0b", data.has_rs3);
        $display("      has_fd       = %0b", data.has_fd);
        $display("      has_fs1      = %0b", data.has_fs1);
        $display("      has_fs2      = %0b", data.has_fs2);
        $display("      has_fs3      = %0b", data.has_fs3);
        $display("      has_vd       = %0b", data.has_vd);
        $display("      has_vs1      = %0b", data.has_vs1);
        $display("      has_vs2      = %0b", data.has_vs2);
        $display("      has_vs3      = %0b", data.has_vs3);
        $display("      has_vm       = %0b", data.has_vm);

        // Operand names
        $display("      rd           = %0s", data.rd);
        $display("      rs1          = %0s", data.rs1);
        $display("      rs2          = %0s", data.rs2);
        $display("      rs3          = %0s", data.rs3);
        $display("      fd           = %0s", data.fd);
        $display("      fs1          = %0s", data.fs1);
        $display("      fs2          = %0s", data.fs2);
        $display("      fs3          = %0s", data.fs3);
        $display("      vd           = %0s", data.vd);
        $display("      vs1          = %0s", data.vs1);
        $display("      vs2          = %0s", data.vs2);
        $display("      vs3          = %0s", data.vs3);
        $display("      vm           = %0s", data.vm);

        // Operand values
        $display("      rd_val       = 0x%0h", data.rd_val);
        $display("      rd_val_pre   = 0x%0h", data.rd_val_pre);
        $display("      rs1_val      = 0x%0h", data.rs1_val);
        $display("      rs2_val      = 0x%0h", data.rs2_val);
        $display("      rs3_val      = 0x%0h", data.rs3_val);
        $display("      fd_val       = 0x%0h", data.fd_val);
        $display("      fd_val_pre   = 0x%0h", data.fd_val_pre);
        $display("      fs1_val      = 0x%0h", data.fs1_val);
        $display("      fs2_val      = 0x%0h", data.fs2_val);
        $display("      fs3_val      = 0x%0h", data.fs3_val);
        $display("      vd_val       = 0x%0h", data.vd_val);
        $display("      vd_val_pre   = 0x%0h", data.vd_val_pre);
        $display("      vs1_val      = 0x%0h", data.vs1_val);
        $display("      vs2_val      = 0x%0h", data.vs2_val);
        $display("      vs3_val      = 0x%0h", data.vs3_val);
        $display("      vm_val       = 0x%0h", data.vm_val);

        // Immediate values
        $display("      imm          = 0x%0h", data.imm);
        $display("      imm2         = 0x%0h", data.imm2);
        $display("      imm3         = 0x%0h", data.imm3);
        $display("      mem_addr     = 0x%0h", data.mem_addr);
    endfunction


endclass

