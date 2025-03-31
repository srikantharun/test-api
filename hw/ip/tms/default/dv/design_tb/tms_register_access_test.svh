// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Andrew Dickson <andrew.dickson@axelera.ai>
//
// tms_register access test
//==============================================================================
// Register access testing
// Write all registers then read all registers
// Read write in random order
// Check with APB and JTAG
task register_access_test();
  int         i      ;
  int         ptr    ;
  tms_pdata_t prdata ;

  `uvm_info("REG_ACCESS_TEST", $sformatf("REGISTER_ACCESS_TEST Start"), UVM_NONE)

  //============================================================================
  // APB write/read check
  i   = 0;
  ptr = 0;
  // write then read all registers.
  while (i<=LAST_REG_ADDR) begin
    if (!regs_txn.randomize()) begin
      `uvm_error("APB_REGISTER_ACCESS_TEST", "Randomize failed")
      fail_cnt++;
    end
    apb_write(i, regs_txn.wdata);
    `uvm_info("APB_REGISTER_ACCESS_TEST", $sformatf("APB Write Reg: %0s Addr: %0x Data: %0x", get_reg_name(i), i, regs_txn.wdata), UVM_HIGH)

    apb_read(i, prdata);
    `uvm_info("APB_REGISTER_ACCESS_TEST", $sformatf("DEBUG100 %0s,%0x,%0x,%0x,%0s", get_reg_name(i), i, regs_txn.wdata,prdata,regs_txn.wdata==prdata ? "OK" : "KO"), UVM_HIGH)
    check_reg_write_and_read_data("APB", get_reg_name(i), i, regs_txn.wdata, prdata);
    i+=4;
    ptr++;
  end

  //============================================================================
  // JTAG write/read check
  i   = 0;
  ptr = 0;
  // write then read all registers.
  while (i<=LAST_REG_ADDR) begin
    if (!regs_txn.randomize()) begin
      `uvm_error("JTAG REGISTER_ACCESS_TEST", "Randomize failed")
      fail_cnt++;
    end

    jtag_write_data(i, regs_txn.wdata);
    `uvm_info("JTAG_REGISTER_ACCESS_TEST", $sformatf("JTAG Write Reg: %0s Addr: %0x Data: %0x", get_reg_name(i), i, regs_txn.wdata), UVM_HIGH)

    jtag_read_data(i, prdata);
    `uvm_info("JTAG_REGISTER_ACCESS_TEST", $sformatf("DEBUG100 %0s,%0x,%0x,%0x,%0s", get_reg_name(i), i, regs_txn.wdata,prdata,regs_txn.wdata==prdata ? "OK" : "KO"), UVM_HIGH)
    check_reg_write_and_read_data("JTAG", get_reg_name(i), i, regs_txn.wdata, prdata);

    i+=4;
    ptr++;
  end

  //============================================================================
  // random accesses
  // APB
  for (int i=0; i<10e3; i++) begin
    if (!regs_txn.randomize()) begin
      `uvm_error("APB REGISTER_ACCESS_TEST", "Randomize failed")
      fail_cnt++;
    end

    case(regs_txn.dir)
      READ  : begin
        apb_read (regs_txn.addr, prdata);
        check_reg_write_and_read_data("APB", get_reg_name(regs_txn.addr), regs_txn.addr, regs_wdata[regs_txn.addr>>2], prdata);
      end
      WRITE : begin
        apb_write(regs_txn.addr, regs_txn.wdata);
      end
    endcase
  end

  // JTAG
  for (int i=0; i<10e3; i++) begin
    if (!regs_txn.randomize()) begin
      `uvm_error(" JTAGREGISTER_ACCESS_TEST", "Randomize failed")
      fail_cnt++;
    end

    case(regs_txn.dir)
      READ  : begin
        jtag_read_data(regs_txn.addr, prdata);
        check_reg_write_and_read_data("JTAG_RAND", get_reg_name(regs_txn.addr), regs_txn.addr, regs_wdata[regs_txn.addr>>2], prdata);
      end
      WRITE : begin
        jtag_write_data(regs_txn.addr, regs_txn.wdata);
      end
    endcase
  end

  //============================================================================
  // random accesses
  for (int i=0; i<10e3; i++) begin
    if (!regs_txn.randomize()) begin
      `uvm_error(" JTAGREGISTER_ACCESS_TEST", "Randomize failed")
      fail_cnt++;
    end

    case(regs_txn.regs_access)
      APB : begin
        case(regs_txn.dir)
          READ  : begin
            apb_read (regs_txn.addr, prdata);
            check_reg_write_and_read_data("APB", get_reg_name(regs_txn.addr), regs_txn.addr, regs_wdata[regs_txn.addr>>2], prdata);
          end
          WRITE : begin
            apb_write(regs_txn.addr, regs_txn.wdata);
          end
    endcase
      end
      JTAG : begin
        case(regs_txn.dir)
          READ  : begin
            jtag_read_data(regs_txn.addr, prdata);
            check_reg_write_and_read_data("JTAG_RAND", get_reg_name(regs_txn.addr), regs_txn.addr, regs_wdata[regs_txn.addr>>2], prdata);
          end
          WRITE : begin
            jtag_write_data(regs_txn.addr, regs_txn.wdata);
          end
        endcase
      end
    endcase

  end

endtask


