// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Andrew Dickson <andrew.dickson@axelera.ai>
//
// tms_register parallel access test
// jtag and apb accesses in paramer


task tms_register_parll_access_test();
  `uvm_info("REG_ACCESS_TEST", $sformatf("REGISTER_ACCESS_TEST Start"), UVM_NONE)
  //============================================================================
  // parallel accesses
  fork
    begin : fork_apb
      regs_ctrl  regs_txn                   ;

      regs_txn = new();

      for (int i=0; i<333e3; i++) begin
        if (!regs_txn.randomize()) begin
          `uvm_error(" Parallel REGISTER_ACCESS_TEST", "Randomize failed")
          fail_cnt++;
        end

        case(regs_txn.dir)
          READ  : begin
            apb_read (regs_txn.addr, prdata);
            check_reg_write_and_read_data("APB_PARL", get_reg_name(regs_txn.addr), regs_txn.addr, regs_wdata[regs_txn.addr>>2], prdata);
          end
          WRITE : begin
            apb_write(regs_txn.addr, regs_txn.wdata);
          end
        endcase
      end
    end
    begin : fork_jtag
      regs_ctrl  regs_txn       ;
      tms_pdata_t jtag_rdata_exp;

      regs_txn = new();

      for (int i=0; i<1e3; i++) begin
        if (!regs_txn.randomize()) begin
          `uvm_error("Parallel REGISTER_ACCESS_TEST", "Randomize failed")
          fail_cnt++;
        end

        case(regs_txn.dir)
          READ  : begin
            fork
              begin
                // send read request
                jtag_read_data(regs_txn.addr, prdata);
              end
              begin
                // store current read data. may be changed by apb during jtag
                // txn
                wait(`DUT.u_tms_jtag_to_apb.u_apb_manager.i_apb_m_pready);
                @(posedge tb_clk) jtag_rdata_exp = `DUT.u_tms_jtag_to_apb.u_apb_manager.i_apb_m_prdata;
              end
            join
            check_reg_write_and_read_data("JTAG_PARL", get_reg_name(regs_txn.addr), regs_txn.addr, jtag_rdata_exp, prdata);
          end
          WRITE : begin
            jtag_write_data(regs_txn.addr, regs_txn.wdata);
          end
        endcase
      end
    end
  join

endtask
