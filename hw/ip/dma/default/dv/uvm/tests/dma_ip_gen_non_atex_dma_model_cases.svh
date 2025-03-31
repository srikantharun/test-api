/// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
//   Quick means to Generate simple NON-ATEX DMA MODEL 1D cases (for manual incorporation into the DMA model)
//   Scenarios extracted from the sim.log file, and then pasted into the non-ATEX DMA model before the model is run
//   NOTE : There is no simulation taking place. Just the generation of various scenarios 
// Owner: Sultan Khan

`ifndef GUARD_DMA_IP_GEN_NON_ATEX_DMA_MODEL_CASES_SV
`define GUARD_DMA_IP_GEN_NON_ATEX_DMA_MODEL_CASES_SV


class dma_ip_gen_non_atex_dma_model_cases extends dma_ip_base_test;

  // ------------------------------------------------------------

  /** UVM Component Utility macro */
  `uvm_component_utils(dma_ip_gen_non_atex_dma_model_cases)

  // Members which need to be exercised (taken from NON-ATEX DMA Model)
  // # test_num, src_address, dst_address, tran_size, xtype, src_xbytesize, dst_xbytesize, xaddrinc, ytype, src_yrowsize, dst_yrowsize, yaddrstride, src_burst_len , dst_burst_len, fillval

  // Members which need to be assigned values
  bit [39:0]  src_addr;
  bit [39:0]  dst_addr;

  bit [15:0]  xaddrinc;
  bit [31:0]  src_xbytesize, src_xbytesize_assigned;
  bit [31:0]  dst_xbytesize, dst_xbytesize_assigned;
  bit [3:0]   transize;
  bit [3:0]   xtype;

  int ytype = 0;
  int src_yrowsize = 0;
  int dst_yrowsize = 0;
  int yaddrstride  = 0;

  int src_burst_len = 64;
  int dst_burst_len = 64;
  int fillval = 5;

  // QUEUEs containing fixed values, which we use per value-chaning iteration
  int src_addr_q[$];
  int dst_addr_q[$];

  int xaddrinc_q[$];
  int src_xbytesize_q[$];
  int dst_xbytesize_q[$];
  int transize_q[$];
  int xtype_q[$];

  int ytype_q[$];
  int src_yrowsize_q[$];
  int dst_yrowsize_q[$];
  int yaddrstride_q[$];
  int src_burst_len_q[$];
  int dst_burst_len_q[$];
  int fillval_q[$];

  // Defines the start of iteration count (The DMA Model test-number)
  int testcase_cnt;
  
  // Genral Purpose
  int rand_xbytesize_lwr;
  int rand_xbytesize_upr;
  int xbytesize;
  int transfer_size_bytes;
  
  

  // Class constructor
  function new (string name="dma_ip_gen_non_atex_dma_model_cases", uvm_component parent);
    super.new (name, parent);
  endfunction : new

  // Build phase
  virtual function void build_phase(uvm_phase phase);
    `uvm_info ("dma_ip_gen_non_atex_dma_model_cases", "Build phase entered", UVM_HIGH)
    super.build_phase(phase);
  endfunction

  // ------------------------------------------------------------

  // Start of simulation phase 
  function void start_of_simulation_phase (uvm_phase phase);
    super.start_of_simulation_phase(phase);
  endfunction: start_of_simulation_phase;

  // ------------------------------------------------------------

  virtual task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    super.run_phase(phase);

    // -----------------------------------------------------------------------------------------------------------------------------------------
    // Highly Focused 1D cases. 1 Dependancy altered at a time
    
    testcase_cnt = 200;

    // Fixed values to be applied to eam Member    
    src_addr_q      = {0, 1, 2, 3, 4096, 4097, 4098, 4099};    // Aligned and Unaligned
    dst_addr_q      = {0, 1, 2, 3, 4096, 4097, 4098, 4099};    // Aligned and Unaligned
    xaddrinc_q      = {0, 1, 2, 128, 256, 4096, 32767};
    src_xbytesize_q = {0, 1, 2, 3, 64, 256, 4096, 65535, 'hffff_ffff};
    dst_xbytesize_q = {0, 1, 2, 3, 64, 256, 4096, 65535, 'hffff_ffff};
    transize_q      = {0, 1, 2, 3, 4, 5, 6};
    xtype_q         = {0, 1, 2, 3};
    src_burst_len_q = {0, 1, 2, 3, 64, 128, 255};
    dst_burst_len_q = {0, 1, 2, 3, 64, 128, 255};
    fillval_q       = {0, 5, 10, 'haaaa, 'h5555};

    ytype_q         = {0, 1, 2, 3};
    src_yrowsize_q  = {0, 1, 2, 3, 64, 256, 4096, 65535, 'hffff_ffff};
    dst_yrowsize_q  = {0, 1, 2, 3, 64, 256, 4096, 65535, 'hffff_ffff};
    yaddrstride_q   = {0, 1, 2, 3, 64, 256, 4096, 'hffff};

    // For 1D - There are 10 Members to exercise one at a time. 
    // For 2D - There are 4  Members to exercise one at a time.
    //        - Total Members 14
    for (int i=0;  i < 14; i++ ) begin
      int general_q[$];
      
      // Default values which are always applicable, when exercsiing members 1 at a time
      src_addr       = 0;
      dst_addr       = 4096;
      transize       = 0;
      xtype          = 1;
      src_xbytesize  = 2048;  // Figure is always a multiple of transizes (from 0 to 6)
      dst_xbytesize  = 2048;  // Figure is always a multiple of transizes (from 0 to 6)
      xaddrinc       = 1;
      src_burst_len  = 64;
      dst_burst_len  = 64;
      fillval        = 5;

      // Keep log of member values, which can be temporailty overwritten
      src_xbytesize_assigned = src_xbytesize;
      dst_xbytesize_assigned = dst_xbytesize;


      // If dealing with 1st 10 Members (1D) then 2D operation is disabled
      // If dealing with members after the 1st 10, then enable 2D operation as changing 2D members
      ytype          = (i<10) ? 0 : 1;
      
      src_yrowsize   = 0;
      dst_yrowsize   = 0;
      yaddrstride    = 0;

      // Determine Which Member we are exercising, by loading the corresponding QUEUE contents into a general Queue
      case (i)
        // 1D
        0  : general_q = src_addr_q;     
        1  : general_q = dst_addr_q;     
        2  : general_q = xaddrinc_q;     
        3  : general_q = src_xbytesize_q;
        4  : general_q = dst_xbytesize_q;
        5  : general_q = transize_q;     
        6  : general_q = xtype_q;        
        7  : general_q = src_burst_len_q;
        8  : general_q = dst_burst_len_q;
        9  : general_q = fillval_q; 
        
        // 2D - If iterations permit them     
        10 : general_q = ytype_q;       
        11 : general_q = src_yrowsize_q;
        12 : general_q = dst_yrowsize_q;
        13 : general_q = yaddrstride_q; 
      endcase

      // For the given Member, POP the value from the general QUEUE in turn
      for (int idx=0; idx < general_q.size(); idx++) begin
        int  q_value;
        
        q_value = general_q[idx];
        
        // Assign the Q Value to the member in question
        case (i)
        // 1D
          0  : src_addr      = q_value;     
          1  : dst_addr      = q_value;     
          2  : xaddrinc      = q_value;     
          3  : src_xbytesize = q_value;
          4  : dst_xbytesize = q_value;
          5  : transize      = q_value;     
          6  : xtype         = q_value;        
          7  : src_burst_len = q_value;
          8  : dst_burst_len = q_value;
          9  : fillval       = q_value; 
        
          // 2D - If iterations permit them     
          10 : ytype         = q_value;       
          11 : src_yrowsize  = q_value;
          12 : dst_yrowsize  = q_value;
          13 : yaddrstride   = q_value; 
        endcase

        // ------------------------------------------------------------------------------------------------
        // SOME POST PROCESSING - to cope with values which are dependant upon others t
        
        // AssertionError: DMA: src_xbytesize and dst_xbytesize must be equal to 0 when xtype is DISABLED
        src_xbytesize = (xtype == 0) ? 0 : src_xbytesize_assigned;
        dst_xbytesize = (xtype == 0) ? 0 : dst_xbytesize_assigned;
        
        
        // ------------------------------------------------------------------------------------------------


        `uvm_info("DMA_MODEL_CASES", $sformatf("*(%0d, %0d, %0d, %0d, %0d, %0d, %0d, %0d, %0d, %0d, %0d, %0d, %0d, %0d, %0d),", 
                                                  testcase_cnt, src_addr, dst_addr, transize, xtype, src_xbytesize, dst_xbytesize, xaddrinc,
                                                  ytype, src_yrowsize, dst_yrowsize, yaddrstride, src_burst_len , dst_burst_len, fillval
                                               ), UVM_LOW)

        testcase_cnt++;
      end
    end

    `uvm_fatal("DMA_MODEL_CASES", $sformatf("DELIBERATE STOP - NO NEED for other SCERNARIOs"))
    // -----------------------------------------------------------------------------------------------------------------------------------------

    // -----------------------------------------------------------------------------------------------------------------------------------------
    // 1D Cases - Some Random Values - create 50 cases 
    testcase_cnt = 600;

    // NO 2D at all
    ytype = 0;
    src_yrowsize = 0;
    dst_yrowsize = 0;
    yaddrstride  = 0;

    src_burst_len = 64;
    dst_burst_len = 64;
    fillval = 5;

    // Have Random cases for 4 types of ADDR_ALIGNMENTs
    for (int align_case=0; align_case<4; align_case++) begin
     
      // All other 1D cases to be random
      for (int rand_cases=0; rand_cases <10; rand_cases++) begin

        src_addr = 64;     // TBD - FIXED for now
        dst_addr = 4096;   // TBD - FIXED for now
        
        // each iteration, we assign src/dst addr based on ALIGNED/UNALIGNED cases
        // 1st N will be BOTH ALIGNED, next n SRC is UNALIGNED, etc
        case (align_case)
          0  : begin                 // SRC DST BOTH Aligned
                src_addr[1:0]= 0;  
                dst_addr[1:0]= 0;  
              end
          1  : begin                 // SRC UNALIGNED Only  
                src_addr[1:0]= $urandom_range(1,3);  
                dst_addr[1:0]= 0;  
              end  // Aligned
          2 : begin                 // DST UNALIGNED Only  
                src_addr[1:0]= 0;
                dst_addr[1:0]= $urandom_range(1,3);   
              end  // Aligned
          3 : begin                 // SRC DST BOTH UNALIGNED  
                src_addr[1:0]= $urandom_range(1,3); 
                dst_addr[1:0]= $urandom_range(1,3);   
              end  
        endcase
      
        transize = $urandom_range(0,6);
        
        // XTYPE
        randcase
          90 : xtype = $urandom_range(1,3);
          10 : xtype = 0;
        endcase
      
        // DMA Model expects src/dst xbytessize to be a multiple of transfer size (Else it Errors out)
        case (transize)
          0 : begin  transfer_size_bytes = 1;   rand_xbytesize_lwr = 62;  rand_xbytesize_upr = 66;  end
          1 : begin  transfer_size_bytes = 2;   rand_xbytesize_lwr = 62;  rand_xbytesize_upr = 66;  end
          2 : begin  transfer_size_bytes = 4;   rand_xbytesize_lwr = 60;  rand_xbytesize_upr = 68;  end
          3 : begin  transfer_size_bytes = 8;   rand_xbytesize_lwr = 56;  rand_xbytesize_upr = 72;  end
          4 : begin  transfer_size_bytes = 16;  rand_xbytesize_lwr = 48;  rand_xbytesize_upr = 80;  end
          5 : begin  transfer_size_bytes = 32;  rand_xbytesize_lwr = 32;  rand_xbytesize_upr = 96;  end
          6 : begin  transfer_size_bytes = 64;  rand_xbytesize_lwr = 64;  rand_xbytesize_upr = 192; end
        endcase

        // Randomize xbytesize, to be within the given ranges and also amultiple of transfer_size (in bytes)
        if (!randomize(xbytesize)  with {xbytesize inside {[rand_xbytesize_lwr:rand_xbytesize_upr]};
                                                xbytesize %transfer_size_bytes == 0;  // But, value must be a multiple of transfer size too
                                               })
       	  `uvm_fatal(get_full_name(),$sformatf("TestRun Setup : Failed to Randomize  xbytesize"));

        randcase
          10 : begin   // srcx == dstx
                src_xbytesize = xbytesize;
                dst_xbytesize = src_xbytesize;
              end
          10: begin   // srcx <dstx, 
                dst_xbytesize = xbytesize;
                src_xbytesize = dst_xbytesize - transfer_size_bytes;
              end
          10: begin   // srcx > dstx, 
                dst_xbytesize = xbytesize;
                src_xbytesize = dst_xbytesize + transfer_size_bytes;
              end
          10: begin   // srcx==0
                src_xbytesize = 0;
                dst_xbytesize = xbytesize;
              end
          10: begin   // dstx==0
                src_xbytesize = xbytesize;
                dst_xbytesize = 0;
              end
        endcase
        
        // NOTE DMA MODEL has an assertion which states that if XTYPE=DISABLED then src and dst xbtessize must be 0 too
        if (xtype == 4'b0000) begin
          src_xbytesize = 0;
          dst_xbytesize = 0;
        end
        
        randcase
          50 : xaddrinc = 1;
          30 : xaddrinc = $urandom_range (2,4);
          20 : xaddrinc = $urandom_range (5,16);
          10 : xaddrinc = 0;
        endcase
      

        `uvm_info("DMA_MODEL_CASES", $sformatf("*(%0d, %0d, %0d, %0d, %0d, %0d, %0d, %0d, %0d, %0d, %0d, %0d, %0d, %0d, %0d),", 
                                                  testcase_cnt, src_addr, dst_addr, transize, xtype, src_xbytesize, dst_xbytesize, xaddrinc,
                                                  ytype, src_yrowsize, dst_yrowsize, yaddrstride, src_burst_len , dst_burst_len, fillval
                                                  ), UVM_LOW)
                                             
        
        testcase_cnt++;

      end
    end



    `uvm_fatal("DMA_MODEL_CASES", $sformatf("DELIBERATE STOP - NO NEED for other SCERNARIOs"))
    // -----------------------------------------------------------------------------------------------------------------------------------------






    // Embedded series of for-loops to yield all combinations of key values (so all crosses)
    testcase_cnt = 700;   // Start from 600
    for (int scenarios=0; scenarios <=0; scenarios++) begin
      for (int addr=0; addr < 4; addr++) begin
        
        src_addr = 0;      // TBD - FIXED for now
        dst_addr = 4096;   // TBD - FIXED for now
        
        case (addr)
          0 : begin                 // SRC DST BOTH Aligned
                src_addr[1:0]= 0;  
                dst_addr[1:0]= 0;  
              end
          1 : begin                 // SRC UNALIGNED Only  
                src_addr[1:0]= $urandom_range(1,3);  
                dst_addr[1:0]= 0;  
              end  // Aligned
          2 : begin                 // DST UNALIGNED Only  
                src_addr[1:0]= 0;
                dst_addr[1:0]= $urandom_range(1,3);   
              end  // Aligned
          3 : begin                 // SRC DST BOTH UNALIGNED  
                src_addr[1:0]= 0;
                dst_addr[1:0]= $urandom_range(1,3);   
              end  // Aligned
        endcase
        
        // -----------------------------------------------------
        for (int i_transize=0; i_transize <=6; i_transize++) begin
          transize = i_transize;

          for (int i_xtype=0; i_xtype <=3; i_xtype++) begin
            case (i_xtype)
              0 : xtype = 4'b0011;   // FILL
              1 : xtype = 4'b0010;   // WRAP
              2 : xtype = 4'b0001;   // CONTINUE
              3 : xtype = 4'b0000;   // DISABLE
            endcase
            
            for (int src_dst_case=0; src_dst_case<=4; src_dst_case++) begin
              case (src_dst_case)
                0 : begin   // srcx == dstx
                      src_xbytesize = $urandom_range(63, 65);
                      dst_xbytesize = src_xbytesize;
                    end
                1 : begin   // srcx <dstx, 
                      dst_xbytesize = $urandom_range(63, 65);
                      src_xbytesize = dst_xbytesize - 4;
                    end
                2 : begin   // srcx > dstx, 
                      dst_xbytesize = $urandom_range(63, 65);
                      src_xbytesize = dst_xbytesize + 4;
                    end
                3 : begin   // srcx==0
                      src_xbytesize = 0;
                      dst_xbytesize = $urandom_range(63, 65);
                    end
                4 : begin   // dstx==0
                      src_xbytesize = $urandom_range(63, 65);
                      dst_xbytesize = 0;
                    end
              endcase
              
              // NOTE DMA MODEL has an assertion which states that if XTYPE=DISABLED then src and dst xbtessize must be 0 too
              if (xtype == 4'b0000) begin
                src_xbytesize = 0;
                dst_xbytesize = 0;
              end
              
              // XINC values apply to BOTH SRC/DST
              for (int i_xaddrinc_case=0; i_xaddrinc_case <=3; i_xaddrinc_case++) begin
                case (i_xaddrinc_case)
                  0 : xaddrinc = 1;
                  1 : xaddrinc = $urandom_range (2,4);
                  2 : xaddrinc = $urandom_range (5,16);
                  3 : xaddrinc = 0;
                endcase
                
                // Output values in format we can cut/paste into NON-ATEX DMA model
                // We search logfile for DMA_MODEL_CASES, strip out all strings except for the bits we need. 
                // There is a deliberate * char in the uvm_info, to assist in stripping out everything except what we need 
                //
                // format DMA model expects is 
                //   (525, 3, 4099, 0, 1, 65, 65, 1, 0, 0, 0, 0, 64, 64, 5),
                
                `uvm_info("DMA_MODEL_CASES", $sformatf("*(%0d, %0d, %0d, %0d, %0d, %0d, %0d, %0d, %0d, %0d, %0d, %0d, %0d, %0d, %0d),", 
                                                          testcase_cnt, src_addr, dst_addr, transize, xtype, src_xbytesize, dst_xbytesize, xaddrinc,
                                                          ytype, src_yrowsize, dst_yrowsize, yaddrstride, src_burst_len , dst_burst_len, fillval
                                                          ), UVM_LOW)
                                                     
              
                testcase_cnt++;
              end
              
            end
          end
        end
        // -----------------------------------------------------
        
      end
    end

    phase.drop_objection(this);
  endtask

  // ------------------------------------------------------------

endclass:dma_ip_gen_non_atex_dma_model_cases



`endif // GUARD_DMA_IP_GEN_NON_ATEX_DMA_MODEL_CASES_SV
