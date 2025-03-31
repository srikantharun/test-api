//------------------------------------------------------------------------------
// Project     : Axelera LPDDR Subsystem
// File Name   : lpddr_subsystem_axi_scheduler_seq.sv
// Unit Name   : lpddr_subsystem_axi_scheduler_seq.sv
//------------------------------------------------------------------------------
// Description : This scheduler keep transmitting AXI write and read data
//transactions to DUT.
//------------------------------------------------------------------------------


//--------------------------------------------------------------------------------------
// Class name : lpddr_subsystem_axi_scheduler_seq
//--------------------------------------------------------------------------------------
class lpddr_subsystem_axi_scheduler_seq extends lpddr_subsystem_base_virtual_seq;
  
	`uvm_object_utils(lpddr_subsystem_axi_scheduler_seq)
	axi_trans_t trans_axi_rd;
	axi_trans_t trans_axi_wr;
  axi_trans_t read_req_trans[$];
  axi_trans_t write_req_trans[$];
 


		// new function
	function new(string name = "lpddr_subsystem_axi_scheduler_seq");
    super.new(name);
	endfunction : new

	static bit disable_scheduler = 0;
  static bit user_rd_data = 0;
  static bit user_wr_data = 0;

  rand bit [3:0] qos_rd;
  rand bit [3:0] qos_wr;
  rand bit [32:0] addr_local;
  rand bit [7:0] burst_length_local;
	rand axi4_size_e size_local; 
	rand axi4_burst_e burst_local;
  rand bit lock_local;
  rand bit [2:0] prot_local;

  
 /* constraint qos_rd_c {
    if((m_io_vif.hpr_credit_cnt > 0) || (m_io_vif.lpr_credit_cnt > 0))
      qos_rd < 4'd16;
    else if ((m_io_vif.hpr_credit_cnt > 0) && (m_io_vif.lpr_credit_cnt == 0))
      qos_rd > 4'd11;
    else if ((m_io_vif.hpr_credit_cnt == 0) && (m_io_vif.lpr_credit_cnt > 0))
      qos_rd < 4'd12;
  }  */

 /* constraint size_local_c {
    size_local inside {[0:8]};
  } */




	//----------------------------------------------------------------------------
  // Function Name : build_phase
  // Arguments     : uvm_phase phase
  //----------------------------------------------------------------------------
  virtual function void build_phase (uvm_phase phase);
    //super.build_phase(phase);
    trans_axi_wr  = axi_trans_t::type_id::create("trans_axi_wr");
    trans_axi_rd  = axi_trans_t::type_id::create("trans_axi_rd");
	endfunction: build_phase

  //--------------------------------------------------------------------------------------
  // Task        : body
  // Description : This task executes AXI write and read transaction
  //--------------------------------------------------------------------------------------
  virtual task body ();
	  //assert (this.randomize());
	  wait(m_env_cfg.init_seq_done == 1'b1);
	 `uvm_info(get_type_name(),"Started schedular after init seq done ", UVM_LOW)
    fork
      forever begin
        axi_trans_t rd_trans;
        if(user_rd_data == 1) begin
          wait(read_req_trans.size() > 0);
          rd_trans = read_req_trans.pop_front();
          `uvm_do(rd_trans);
        end
		    else if(disable_scheduler == 0) begin
          //#1;  //TODO : need to check timing
          $display("value of gpt credit = %0d", m_io_vif.hpr_credit_cnt);
          wait (m_io_vif.hpr_credit_cnt > 0 || m_io_vif.lpr_credit_cnt > 0);
          `uvm_do_on_with(trans_axi_rd, p_sequencer.axi_sqr, {read_or_write == AXI4_TRANS_READ; 
                                                           //addr == addr_local; 
                                                           burst_length inside {[8'd5:8'd8]}; 
                                                           burst inside {[AXI4_INCR:AXI4_WRAP]}; 
                                                           lock == 0; 
                                                           cache == 0; 
                                                           prot == 0;
																													 foreach(write_strobes[i]) write_strobes[i] == '1; 
                                                           //qos == qos_wr;
																													 region == 0;
                                                           //wdata_words == $urandom(); 
                                                           //write_strobes == 32'hffffffff; 
                                                         })
		      `uvm_info("AXI_SCHEDULAR",$sformatf("AXI WRITE TRANSACTION\n",trans_axi_rd.sprint()), UVM_HIGH)
		    #100ns;
        end
				else begin
				    wait((disable_scheduler == 0) || (user_wr_data == 1));
				end
      end

      forever begin
        axi_trans_t wr_trans;
        if(user_wr_data == 1) begin
          wait(write_req_trans.size() > 0);
          wr_trans = write_req_trans.pop_front();
          `uvm_do(wr_trans);
        end 
        else if(disable_scheduler == 0) begin
          wait (m_io_vif.wr_credit_cnt > 0);
          `uvm_do_on_with(trans_axi_wr, p_sequencer.axi_sqr, {read_or_write == AXI4_TRANS_WRITE; 
                                                           //addr == addr_local; 
                                                           burst_length inside {[8'd5:8'd8]}; 
                                                           size == AXI4_BYTES_1; 
                                                           burst inside {[AXI4_INCR:AXI4_WRAP]}; 
                                                           lock == 0; 
                                                           cache == 0; 
                                                           prot == 0; 
																													 foreach(write_strobes[i]) write_strobes[i] == '1; 
                                                           //qos == qos_wr;
																													 region == 0;
                                                           //wdata_words == $urandom(); 
                                                           //write_strobes == 32'hffffffff; 
                                                         }) 
		   		`uvm_info("AXI_SCHEDULAR",$sformatf("AXI READ TRANSACTION\n",trans_axi_wr.sprint()), UVM_HIGH)
				  #100ns;
        end
				else begin
				    wait((disable_scheduler == 0) || (user_wr_data == 1));
				end
      end

      
    join
  endtask : body

  //--------------------------------------------------------------------------------------
  // Method        : disable_axi_scheduler 
  // Description   : This method will disable the axi scheduler.
  //--------------------------------------------------------------------------------------
 task disable_axi_scheduler();
    disable_scheduler = 1;
		`uvm_info(get_type_name(),"axi scheduler is disabled", UVM_LOW)
	endtask : disable_axi_scheduler

  //--------------------------------------------------------------------------------------
  // Method        : enable_axi_scheduler
  // Description   : This method will enable the axi scheduler.
  //--------------------------------------------------------------------------------------
  task enable_axi_scheduler();
    disable_scheduler = 0;
		`uvm_info(get_type_name(),"axi scheduler is enabled", UVM_LOW)
	endtask : enable_axi_scheduler

  //--------------------------------------------------------------------------------------
  // Method        : read_data_in
  // Description   :
  //--------------------------------------------------------------------------------------
  task read_data_in (axi_trans_t read_axi_trans);
    axi_trans_t tmp_read_trans;
    if(read_axi_trans != null) begin
      assert($cast(tmp_read_trans, read_axi_trans.clone));
      read_req_trans.push_back(tmp_read_trans);
    end
  endtask

  //--------------------------------------------------------------------------------------
  // Method        : write_data_in
  // Description   :
  //--------------------------------------------------------------------------------------
  task write_data_in (axi_trans_t write_axi_trans);
    axi_trans_t tmp_write_trans;
    if(write_axi_trans != null) begin
      assert($cast(tmp_write_trans, write_axi_trans.clone));
      write_req_trans.push_back(tmp_write_trans);
    end
  endtask

  //--------------------------------------------------------------------------------------
  // Method        : user_rd_data user_wr_data
  // Description   :
  //--------------------------------------------------------------------------------------
  virtual function void enable_user_rd_data();
    user_rd_data = 1;
		`uvm_info(get_type_name(),"axi scheduler is sending user READ data", UVM_LOW)
  endfunction : enable_user_rd_data

   //--------------------------------------------------------------------------------------
  // Method        : user_rd_data user_wr_data
  // Description   :
  //--------------------------------------------------------------------------------------
  virtual function void disable_user_rd_data();
    user_rd_data = 0;
		`uvm_info(get_type_name(),"axi scheduler is sending random read data", UVM_LOW)
  endfunction : disable_user_rd_data

  //--------------------------------------------------------------------------------------
  // Method        :
  // Description   :
  //--------------------------------------------------------------------------------------
  virtual function void enable_user_wr_data();
    user_wr_data = 1;
		`uvm_info(get_type_name(),"axi scheduler is sending user WRITE data", UVM_LOW)
  endfunction : enable_user_wr_data

   //--------------------------------------------------------------------------------------
  // Method        :
  // Description   :
  //--------------------------------------------------------------------------------------
  virtual function void disable_user_wr_data();
    user_wr_data = 0;
		`uvm_info(get_type_name(),"axi scheduler is sending random write data", UVM_LOW)
  endfunction : disable_user_wr_data



  

endclass : lpddr_subsystem_axi_scheduler_seq

 // read transaction
		  	 /* begin : read_trans
							`uvm_info(get_type_name(),"write start - 1j ", UVM_LOW)
		  		  if (m_io_vif.hpr_credit_cnt > 0) begin
							`uvm_info(get_type_name(),"write start - 1", UVM_LOW)

              //`uvm_do_on_with(trans_axi, p_sequencer.axi_sqr, {read_or_write ==0; addr == $urandom_range(0, 33'h1_ffff_ffff);})
              //`uvm_do_on_with(trans_axi, p_sequencer.axi_sqr, {read_or_write ==0; addr == $urandom_range(0, 33'h1_ffff_ffff); burst_length == 1; size == 4'b0010; burst == 2'h1; lock == 1'h0; cache == 4'h0; cache == 4'h0; prot == 4'h0; qos == 4'h0; wdata_words == $urandom(); write_strobes == 32'hffffffff;})

              //`uvm_do_on_with(req, {req.read_or_write ==0; req.adrr == $urandom_range(0, 33'h1_ffff_ffff); req.burst_length == 1; req.size == 4'b0010; req.burst == 2'h1; req.lock == 1'h0; req.cache == 4'h0; req.cache == 4'h0; req.port == 4'h0; req.qos == 4'h0; req.wdata_words == $urandom(); req.write_strobes == 32'hffffffff; })
		  		  end
		  			else if (m_io_vif.lpr_credit_cnt > 0) begin
              // `uvm_do_on_with(req, {req.read_or_write ==0; req.adrr == $urandom_range(0, 33'h1_ffff_ffff); req.burst_length == 1; req.size == 4'b0010; req.burst == 2'h1; req.lock == 1'h0; req.cache == 4'h0; req.cache == 4'h0; req.port == 4'h0; req.qos == 4'h0; req.wdata_words == $urandom(); req.write_strobes == 32'hffffffff; })
		  			end
		  			else if (m_io_vif.hpr_credit_cnt == 0) begin
		  				`uvm_info(get_type_name(), "hpr_credit_cnt is not available", UVM_DEBUG);
		  			end
		  			else if (m_io_vif.lpr_credit_cnt == 0) begin
		  				`uvm_info(get_type_name(), "lpr_credit_cnt is not available", UVM_DEBUG);
		  			end
		  		end
          // write transaction
		  		begin : write_trans
		  		  if(m_io_vif.wrecc_credit_cnt > 0) begin
							`uvm_info(get_type_name(),"write start", UVM_LOW)
              `uvm_do_on_with(trans_axi, p_sequencer.axi_sqr, {read_or_write ==1; addr == $urandom_range(0, 33'h1_ffff_ffff);})
							`uvm_info(get_type_name(),"write start - 2", UVM_LOW)
              //`uvm_do_on_with(req, {req.read_or_write ==1; req.adrr == $urandom_range(0, 33'h1_ffff_ffff); req.burst_length == 1; req.size == 4'b0010; req.burst == 2'h1; req.lock == 1'h0; req.cache == 4'h0; req.cache == 4'h0; req.port == 4'h0; req.qos == 4'h0; req.wdata_words == $urandom(); req.write_strobes == 32'hffffffff; })
		  			end
		  			else if (m_io_vif.wr_credit_cnt > 0) begin
              //`uvm_do_on_with(req, {req.read_or_write ==1; req.adrr == $urandom_range(0, 33'h1_ffff_ffff); req.burst_length == 1; req.size == 4'b0010; req.burst == 2'h1; req.lock == 1'h0; req.cache == 4'h0; req.cache == 4'h0; req.port == 4'h0; req.qos == 4'h0; req.wdata_words == $urandom(); req.write_strobes == 32'hffffffff; })
		  			end 
		  			else if(m_io_vif.wrecc_credit_cnt == 0) begin
              `uvm_info(get_type_name(), "hpr_credit_cnt is not available", UVM_DEBUG);
		  			end
		  			else if(m_io_vif.wr_credit_cnt == 0) begin 
		  				`uvm_info(get_type_name(), "hpr_credit_cnt is not available", UVM_DEBUG);
		  			end
		  		end  */

