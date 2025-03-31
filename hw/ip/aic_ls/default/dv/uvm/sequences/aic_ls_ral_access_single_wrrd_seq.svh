// (C) Copyright Axelera AI 2023
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Sequence inherited from Alpha. Accesses
//   one register per LS device. Could be improved in
//   the future when time allows
// Owner: Rafael Frangulian <rafael.frangulian@axelera.ai>

// ==========================================================================================================
// RAL single write/read test-case
// ==========================================================================================================
class aic_ls_ral_access_single_wrrd_seq extends uvm_sequence;

    `uvm_object_utils(aic_ls_ral_access_single_wrrd_seq)

   // Declare p sequencer
   int loop_count = 1;
   `uvm_declare_p_sequencer(axi_virtual_sequencer)

   function new(string name="aic_ls_ral_access_single_wrrd_seq");
     super.new(name);
   endfunction : new

   virtual task body();
      //aic_ls_subsys_reg_block ls_regmodel;
      uvm_status_e  status;
      bit [63:0]    rand_wrdata;
      bit [63:0]    rd_data;
      bit [63:0]    exp_data;
      bit [63:0]    mask_val;

      `uvm_info("aic_ls_ral_access_single_wrrd_seq","Write and read", UVM_LOW);

      // RAL model reset and update through p_sequencer
      //p_sequencer.regmodel.reset("HARD");
      //p_sequencer.regmodel.update(status, .parent(this));
      // Check status
      if (status == UVM_NOT_OK)
        uvm_report_error("LSRALSEQ", $psprintf("LS RAL model could not be updated"), UVM_LOW);
      else
        uvm_report_info("LSRALSEQ", $psprintf("LS RAL model updated"));

      // Write/read back from one register of all CSR blocks
      for (int ii = 0; ii < loop_count; ii++)
      begin

        // 1. M_IFD0 dbg_scratch register
        mask_val    = 64'hFFFF_FFFF_FFFF_FFFF;
        rand_wrdata = {$urandom, $urandom};
        exp_data    = rand_wrdata & mask_val;

        `uvm_info("M_IFD0", $sformatf("Loop Number = %0d Random Write Data = 64'h%0h, Random Exp Data = 64'h%0h", ii, rand_wrdata, exp_data), UVM_LOW)
        // Perform writes and reads
        p_sequencer.regmodel.m_ifd0_regmod.dbg_scratch.write(status, rand_wrdata);
        p_sequencer.regmodel.m_ifd0_regmod.dbg_scratch.read (status, rd_data);

        // Comparison between the expected and the actual value
        if(exp_data != rd_data)
          `uvm_error("M_IFD0:SINGLE_WRRD: FAILED", $sformatf("Read Value 64'h%0h does not match the expected value 64'h%0h", rd_data, exp_data))
        else
          `uvm_info("M_IFD0:SINGLE_WRRD: PASSED", $sformatf("Read Value 64'h%0h matches the expected value 64'h%0h", rd_data, exp_data), UVM_LOW)

        #20ns;

        // 2. M_IFD1 dbg_scratch register
        mask_val    = 64'hFFFF_FFFF_FFFF_FFFF;
        rand_wrdata = {$urandom, $urandom};
        exp_data    = rand_wrdata & mask_val;

        `uvm_info("M_IFD0", $sformatf("Loop Number = %0d Random Write Data = 64'h%0h, Random Exp Data = 64'h%0h", ii, rand_wrdata, exp_data), UVM_LOW)
        // Perform writes and reads
        p_sequencer.regmodel.m_ifd1_regmod.dbg_scratch.write(status, rand_wrdata);
        p_sequencer.regmodel.m_ifd1_regmod.dbg_scratch.read (status, rd_data);

        // Comparison between the expected and the actual value
        if(exp_data != rd_data)
          `uvm_error("M_IFD1:SINGLE_WRRD: FAILED", $sformatf("Read Value 64'h%0h does not match the expected value 64'h%0h", rd_data, exp_data))
        else
          `uvm_info("M_IFD1:SINGLE_WRRD: PASSED", $sformatf("Read Value 64'h%0h matches the expected value 64'h%0h", rd_data, exp_data), UVM_LOW)

        #20ns;

        // 3. M_IFDW dbg_scratch register
        mask_val    = 64'hFFFF_FFFF_FFFF_FFFF;
        rand_wrdata = {$urandom, $urandom};
        exp_data    = rand_wrdata & mask_val;

        `uvm_info("M_IFDW", $sformatf("Loop Number = %0d Random Write Data = 64'h%0h, Random Exp Data = 64'h%0h", ii, rand_wrdata, exp_data), UVM_LOW)
        // Perform writes and reads
        p_sequencer.regmodel.m_ifdw_regmod.dbg_scratch.write(status, rand_wrdata);
        p_sequencer.regmodel.m_ifdw_regmod.dbg_scratch.read (status, rd_data);

        // Comparison between the expected and the actual value
        if(exp_data != rd_data)
          `uvm_error("M_IFDW:SINGLE_WRRD: FAILED", $sformatf("Read Value 64'h%0h does not match the expected value 64'h%0h", rd_data, exp_data))
        else
          `uvm_info("M_IFDW:SINGLE_WRRD: PASSED", $sformatf("Read Value 64'h%0h matches the expected value 64'h%0h", rd_data, exp_data), UVM_LOW)

        #20ns;

        // 4. D_IFD0 dbg_scratch register
        mask_val    = 64'hFFFF_FFFF_FFFF_FFFF;
        rand_wrdata = {$urandom, $urandom};
        exp_data    = rand_wrdata & mask_val;

        `uvm_info("M_IFD0", $sformatf("Loop Number = %0d Random Write Data = 64'h%0h, Random Exp Data = 64'h%0h", ii, rand_wrdata, exp_data), UVM_LOW)
        // Perform writes and reads
        p_sequencer.regmodel.d_ifd0_regmod.dbg_scratch.write(status, rand_wrdata);
        p_sequencer.regmodel.d_ifd0_regmod.dbg_scratch.read (status, rd_data);

        // Comparison between the expected and the actual value
        if(exp_data != rd_data)
          `uvm_error("D_IFD0:SINGLE_WRRD: FAILED", $sformatf("Read Value 64'h%0h does not match the expected value 64'h%0h", rd_data, exp_data))
        else
          `uvm_info("D_IFD0:SINGLE_WRRD: PASSED", $sformatf("Read Value 64'h%0h matches the expected value 64'h%0h", rd_data, exp_data), UVM_LOW)

        #20ns;

        // 5. D_IFD1 dbg_scratch register
        mask_val    = 64'hFFFF_FFFF_FFFF_FFFF;
        rand_wrdata = {$urandom, $urandom};
        exp_data    = rand_wrdata & mask_val;

        `uvm_info("D_IFD1", $sformatf("Loop Number = %0d Random Write Data = 64'h%0h, Random Exp Data = 64'h%0h", ii, rand_wrdata, exp_data), UVM_LOW)
        // Perform writes and reads
        p_sequencer.regmodel.d_ifd1_regmod.dbg_scratch.write(status, rand_wrdata);
        p_sequencer.regmodel.d_ifd1_regmod.dbg_scratch.read (status, rd_data);

        // Comparison between the expected and the actual value
        if(exp_data != rd_data)
          `uvm_error("D_IFD1:SINGLE_WRRD: FAILED", $sformatf("Read Value 64'h%0h does not match the expected value 64'h%0h", rd_data, exp_data))
        else
          `uvm_info("D_IFD1:SINGLE_WRRD: PASSED", $sformatf("Read Value 64'h%0h matches the expected value 64'h%0h", rd_data, exp_data), UVM_LOW)

        #20ns;

        // 6. M_ODR dbg_scratch register
        mask_val    = 64'hFFFF_FFFF_FFFF_FFFF;
        rand_wrdata = {$urandom, $urandom};
        exp_data    = rand_wrdata & mask_val;

        `uvm_info("M_ODR", $sformatf("Loop Number = %0d Random Write Data = 64'h%0h, Random Exp Data = 64'h%0h", ii, rand_wrdata, exp_data), UVM_LOW)
        // Perform writes and reads
        p_sequencer.regmodel.m_odr_regmod.dbg_scratch.write(status, rand_wrdata);
        p_sequencer.regmodel.m_odr_regmod.dbg_scratch.read (status, rd_data);

        // Comparison between the expected and the actual value
        if(exp_data != rd_data)
          `uvm_error("M_ODR:SINGLE_WRRD: FAILED", $sformatf("Read Value 64'h%0h does not match the expected value 64'h%0h", rd_data, exp_data))
        else
          `uvm_info("M_ODR:SINGLE_WRRD: PASSED", $sformatf("Read Value 64'h%0h matches the expected value 64'h%0h", rd_data, exp_data), UVM_LOW)

        #20ns;

        // 7. D_ODR dbg_scratch register
        mask_val    = 64'hFFFF_FFFF_FFFF_FFFF;
        rand_wrdata = {$urandom, $urandom};
        exp_data    = rand_wrdata & mask_val;

        `uvm_info("D_ODR", $sformatf("Loop Number = %0d Random Write Data = 64'h%0h, Random Exp Data = 64'h%0h", ii, rand_wrdata, exp_data), UVM_LOW)
        // Perform writes and reads
        p_sequencer.regmodel.d_odr_regmod.dbg_scratch.write(status, rand_wrdata);
        p_sequencer.regmodel.d_odr_regmod.dbg_scratch.read (status, rd_data);

        // Comparison between the expected and the actual value
        if(exp_data != rd_data)
          `uvm_error("D_ODR:SINGLE_WRRD: FAILED", $sformatf("Read Value 64'h%0h does not match the expected value 64'h%0h", rd_data, exp_data))
        else
          `uvm_info("D_ODR:SINGLE_WRRD: PASSED", $sformatf("Read Value 64'h%0h matches the expected value 64'h%0h", rd_data, exp_data), UVM_LOW)

        #20ns;
      end // for

      #100ns;
   endtask : body
endclass : aic_ls_ral_access_single_wrrd_seq
