// (C) Copyright Axelera AI 2023
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: AI Core LS Function Coverage
//
// Owner: Rafael Frangulian <rafael.frangulian@axelera.ai>
// -------------------------------------------------

`ifndef AIC_DMC_FUNC_COVERAGE_SV
`define AIC_DMC_FUNC_COVERAGE_SV

//========================================================================================================================
/** Coverage component **/
//========================================================================================================================

class aic_ls_coverage extends uvm_component;
  `uvm_component_utils(aic_ls_coverage)
  int write_cnt;
  uvm_tlm_analysis_fifo#(dmc_addr_gen_seq_item) taf_mon_dmc_ag[AIC_DMC_COV_DMC_NUM_DEVICE];
  uvm_tlm_analysis_fifo#(dmc_addr_gen_seq_item) taf_mon_dmc_dpc[AIC_DMC_COV_DMC_NUM_DEVICE];
  uvm_tlm_analysis_fifo#(mmio_item#(MMIO_DMC_DATA_WIDTH, MMIO_DMC_ADDR_WIDTH))                 taf_mon_dmc_mmio[AIC_DMC_COV_DMC_NUM_DEVICE];
  uvm_tlm_analysis_fifo#(mmio_item#(MMIO_DMC_DATA_WIDTH, MMIO_DMC_ADDR_WIDTH))                 taf_mon_dmc_axi2mmio[AIC_DMC_COV_AXI2MMIO_NUM_DEVICE];
  uvm_tlm_analysis_fifo#(mmio_item#(MMIO_RVV_DATA_WIDTH, MMIO_RVV_ADDR_WIDTH))                 taf_mon_rvv_mmio[AIC_DMC_COV_RVV_NUM_PORTS];
  uvm_tlm_analysis_fifo#(aic_ls_seq_item)       taf_mon_aic_ls;
  uvm_tlm_analysis_fifo#(svt_axi_transaction)       taf_mon_axi_hp_slv;
  uvm_tlm_analysis_fifo#(svt_axi_transaction)       taf_mon_axi_hp_mst;
  uvm_tlm_analysis_fifo#(svt_axi_transaction)       taf_mon_axi_cfg;

  dmc_addr_gen_seq_item ag_item[AIC_DMC_COV_DMC_NUM_DEVICE];
  dmc_addr_gen_seq_item dpc_item[AIC_DMC_COV_DMC_NUM_DEVICE];
  mmio_item#(MMIO_DMC_DATA_WIDTH, MMIO_DMC_ADDR_WIDTH)                 dmc_mmio_item[AIC_DMC_COV_DMC_NUM_DEVICE];
  mmio_item#(MMIO_DMC_DATA_WIDTH, MMIO_DMC_ADDR_WIDTH)                 dmc_axi2mmio_item[AIC_DMC_COV_AXI2MMIO_NUM_DEVICE];
  mmio_item#(MMIO_RVV_DATA_WIDTH, MMIO_RVV_ADDR_WIDTH)                 rvv_mmio_item[AIC_DMC_COV_RVV_NUM_PORTS];
  uvm_event                 m_reg_access_evt[AIC_DMC_COV_DMC_NUM_DEVICE];
  uvm_object                m_uvm_obj[AIC_DMC_COV_DMC_NUM_DEVICE];
  v_object                  m_v_obj[AIC_DMC_COV_DMC_NUM_DEVICE];
  aic_ls_seq_item       aic_ls_item;
  svt_axi_transaction       axi_hp_slv_item;
  svt_axi_transaction       axi_hp_mst_item;
  svt_axi_transaction       axi_cfg_item;

  bit[AIC_DMC_COV_AXI_NUM_DEVICE-1:0]     m_l1_mmio_ongoing_txn; // IFD/ODR + 2 AXItoMMIO
  bit[AIC_DMC_COV_RVV_NUM_PORTS-1:0]      m_l1_rvv_mmio_ongoing_txn;

  int unsigned m_l1_mmio_ongoing_txn_count[AIC_DMC_COV_AXI_NUM_DEVICE];
  int unsigned m_l1_rvv_mmio_ongoing_txn_count[AIC_DMC_COV_RVV_NUM_PORTS];

//========================================================================================================================
/** Covergroups **/
//========================================================================================================================
  /** L1 Memory Tightly Coupled Access. Done via IFD and ODR accesses. */
  /** Access L1 via MMIO aside from the AXI HP Slave Access and make sure min max and in between ranges are covered */
  l1_dmc_mmio_cg l1_dmc_cg;
  l1_rvv_mmio_cg l1_rvv_cg;

  /** L1 Memory Tightly Coupled AXI2MMIO Access. Done via IFD and ODR accesses. */
  l1_dmc_mmio_cg l1_axi2mmio_cg[AIC_DMC_COV_AXI2MMIO_NUM_DEVICE];

  dmc_ag_cg      dmc_ag_dev_cg[AIC_DMC_COV_DMC_NUM_DEVICE];
  dmc_dpc_cg     dmc_dpc_dev_cg[AIC_DMC_COV_DMC_NUM_DEVICE];
  ifd_reg_cg         ifd_reg_dev_cg[AIC_DMC_COV_IFD_NUM_DEVICE];
  odr_reg_cg         odr_reg_dev_cg[AIC_DMC_COV_ODR_NUM_DEVICE];
  compression_cg     ifdw_compression_cg;

  `include "aic_ls_l1_coverage.svh"
  `include "aic_ls_sideband_and_irq_coverage.svh"

//========================================================================================================================
/** Methods **/
//========================================================================================================================

  function new(string name, uvm_component parent);
    super.new(name,parent);
    aic_ls_irq_cg         = new();
    aic_ls_sideband_cg    = new();
    l1_axi_slv_cg             = new();
    l1_mmio_concurrency_cg = new();

    l1_dmc_cg = new ( "l1_dmc_cg" );
    l1_rvv_cg = new ("l1_rvv_cg");
    foreach ( l1_axi2mmio_cg[i]      ) l1_axi2mmio_cg[i]      = new ( $sformatf ( "l1_axi2mmio_cg_%s", AIC_DMC_COV_AXI2MMIO_DEVICE_NAME[i]  ));
    foreach ( dmc_ag_dev_cg[i]      ) dmc_ag_dev_cg[i]      = new ( $sformatf ( "dmc_ag_dev_cg_%s", AIC_DMC_COV_DEVICE_NAME[i]           ));
    foreach ( dmc_dpc_dev_cg[i]     ) dmc_dpc_dev_cg[i]     = new ( $sformatf ( "dmc_dpc_dev_cg_%s", AIC_DMC_COV_DEVICE_NAME[i]          ));
    foreach ( ifd_reg_dev_cg[i]         ) ifd_reg_dev_cg[i]         = new ( $sformatf ( "ifd_reg_dev_cg_%s", AIC_DMC_COV_DEVICE_NAME[i]              ));
    foreach ( odr_reg_dev_cg[i]         ) odr_reg_dev_cg[i]         = new ( $sformatf ( "odr_reg_dev_cg_%s", AIC_DMC_COV_DEVICE_NAME[i+AIC_DMC_COV_IFD_NUM_DEVICE]));
    ifdw_compression_cg                                             = new ( "ifdw_compression_cg");
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    foreach (taf_mon_dmc_ag[i]) begin
      taf_mon_dmc_ag[i]      = new($sformatf("taf_mon_ag_%s", AIC_DMC_COV_DEVICE_NAME[i]), this);
      taf_mon_dmc_dpc[i] = new($sformatf("taf_mon_dpc_%s", AIC_DMC_COV_DEVICE_NAME[i]), this);
      ag_item[i]        = dmc_addr_gen_seq_item::type_id::create($sformatf("ag_item_%s",AIC_DMC_COV_DEVICE_NAME[i]));
      dpc_item[i]       = dmc_addr_gen_seq_item::type_id::create($sformatf("dpc_item_%s",AIC_DMC_COV_DEVICE_NAME[i]));
    end

    foreach (taf_mon_dmc_mmio[i]) begin
      taf_mon_dmc_mmio[i] = new($sformatf("taf_mon_dmc_mmio_%s", AIC_DMC_COV_DEVICE_NAME[i]), this);
      dmc_mmio_item[i]         = mmio_item#(MMIO_DMC_DATA_WIDTH, MMIO_DMC_ADDR_WIDTH)::type_id::create($sformatf("dmc_mmio_item_%s",AIC_DMC_COV_DEVICE_NAME[i]));
    end
    foreach (taf_mon_dmc_axi2mmio[i]) begin
      taf_mon_dmc_axi2mmio[i] = new($sformatf("taf_mon_dmc_axi2mmio_%s", AIC_DMC_COV_AXI2MMIO_DEVICE_NAME[i]), this);
      dmc_axi2mmio_item[i]    = mmio_item#(MMIO_DMC_DATA_WIDTH, MMIO_DMC_ADDR_WIDTH)::type_id::create($sformatf("dmc_axi2mmio_item_%s",AIC_DMC_COV_AXI2MMIO_DEVICE_NAME[i]));
    end
    foreach (taf_mon_rvv_mmio[i]) begin
      taf_mon_rvv_mmio[i] = new($sformatf("taf_mon_rvv_mmio_%0d", i), this);
      rvv_mmio_item[i]         = mmio_item#(MMIO_RVV_DATA_WIDTH, MMIO_RVV_ADDR_WIDTH)::type_id::create($sformatf("rvv_mmio_item_%0d",i));
    end
    taf_mon_aic_ls = new("taf_mon_aic_ls", this);
    taf_mon_axi_hp_slv = new("taf_mon_axi_hp_slv", this);
    taf_mon_axi_hp_mst = new("taf_mon_axi_hp_mst", this);
    taf_mon_axi_cfg    = new("taf_mon_axi_cfg", this);

    axi_hp_slv_item  = new();
    axi_hp_mst_item  = new();
    axi_cfg_item     = new();

    foreach (m_reg_access_evt[i]) begin
      m_reg_access_evt[i] =  uvm_event_pool::get_global($sformatf("%s_reg_evt", AIC_DMC_COV_DEVICE_NAME[i]));
    end
  endfunction : build_phase


  virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);

    fork
      begin : dmc_ag_cmd_proc
        foreach (taf_mon_dmc_ag[k]) begin
          automatic int i = k;
          fork
            forever begin
              taf_mon_dmc_ag[i].get(ag_item[i]);
              dmc_ag_dev_cg[i].sample(ag_item[i], AIC_DMC_COV_DEVICE_NAME[i], aic_ls_item);
              `uvm_info(get_name(), $sformatf("Got AG func_cov item: %s", ag_item[i].convert2string()), UVM_HIGH)
            end
          join_none
        end
      end : dmc_ag_cmd_proc

      begin : dmc_dpc_cmd_proc
        foreach (taf_mon_dmc_dpc[j]) begin
          automatic int i = j;
          fork
            forever begin
              taf_mon_dmc_dpc[i].get(dpc_item[i]);
              dmc_dpc_dev_cg[i].sample(dpc_item[i]);
            end
          join_none
       end
      end : dmc_dpc_cmd_proc

      begin : dmc_mmio_proc
        foreach (taf_mon_dmc_mmio[j]) begin
          automatic int i = j;
          automatic bit[2:0] concurrent_devices;
          fork
            forever begin
              taf_mon_dmc_mmio[i].get(dmc_mmio_item[i]);
              if (dmc_mmio_item[i].m_type == MMIO_REQ) begin
                m_l1_mmio_ongoing_txn_count[i] += 1;
                m_l1_mmio_ongoing_txn[i] = 1; // ongoing txn
                l1_dmc_cg.sample(dmc_mmio_item[i].m_addr, dmc_mmio_item[i].m_error, $countones(m_l1_mmio_ongoing_txn));
                concurrent_devices[0] = (m_l1_mmio_ongoing_txn[AIC_DMC_COV_DMC_NUM_DEVICE-1:0]>0);
                concurrent_devices[1] = (m_l1_mmio_ongoing_txn[AIC_DMC_COV_AXI_NUM_DEVICE-1:AIC_DMC_COV_DMC_NUM_DEVICE]>0);
                concurrent_devices[2] = (m_l1_rvv_mmio_ongoing_txn>0);
                l1_mmio_concurrency_cg.sample($countones({m_l1_rvv_mmio_ongoing_txn,m_l1_mmio_ongoing_txn}), concurrent_devices, i);
              end else if (dmc_mmio_item[i].m_type == MMIO_TXN) begin
                m_l1_mmio_ongoing_txn_count[i] -= 1;
                if (m_l1_mmio_ongoing_txn_count[i] == 0) begin
                  m_l1_mmio_ongoing_txn[i] = 0; // reset txn
                end
              end
            end
          join_none
        end
      end : dmc_mmio_proc

      begin : dmc_axi2mmio_proc
        foreach (taf_mon_dmc_axi2mmio[j]) begin
          automatic int i = j;
          automatic bit[2:0] concurrent_devices;
          fork
            forever begin
              taf_mon_dmc_axi2mmio[i].get(dmc_axi2mmio_item[i]);
              if (dmc_axi2mmio_item[i].m_type == MMIO_REQ) begin
                m_l1_mmio_ongoing_txn_count[i+AIC_DMC_COV_DMC_NUM_DEVICE] += 1;
                m_l1_mmio_ongoing_txn[i+AIC_DMC_COV_DMC_NUM_DEVICE] = 1; // ongoing txn
                l1_axi2mmio_cg[i].sample(dmc_axi2mmio_item[i].m_addr, dmc_axi2mmio_item[i].m_error, $countones(m_l1_mmio_ongoing_txn));
                concurrent_devices[0] = (m_l1_mmio_ongoing_txn[AIC_DMC_COV_DMC_NUM_DEVICE-1:0]>0);
                concurrent_devices[1] = (m_l1_mmio_ongoing_txn[AIC_DMC_COV_AXI_NUM_DEVICE-1:AIC_DMC_COV_DMC_NUM_DEVICE]>0);
                concurrent_devices[2] = (m_l1_rvv_mmio_ongoing_txn>0);
                l1_mmio_concurrency_cg.sample($countones({m_l1_rvv_mmio_ongoing_txn,m_l1_mmio_ongoing_txn}), concurrent_devices, i+AIC_DMC_COV_DMC_NUM_DEVICE);
              end else if (dmc_axi2mmio_item[i].m_type == MMIO_TXN) begin
                m_l1_mmio_ongoing_txn_count[i+AIC_DMC_COV_DMC_NUM_DEVICE] -= 1;
                if (m_l1_mmio_ongoing_txn_count[i+AIC_DMC_COV_DMC_NUM_DEVICE] == 0) begin
                  m_l1_mmio_ongoing_txn[i+7] = 0; // reset txn
                end
              end
            end
          join_none
        end
      end : dmc_axi2mmio_proc

      begin : dmc_rvv_proc
        foreach (taf_mon_rvv_mmio[j]) begin
          automatic int i = j;
          automatic bit[2:0] concurrent_devices;
          fork
            forever begin
              taf_mon_rvv_mmio[i].get(rvv_mmio_item[i]);
              if (rvv_mmio_item[i].m_type == MMIO_REQ) begin  //the type we get when the transaction has started (request)
                m_l1_rvv_mmio_ongoing_txn_count[i] += 1;
                m_l1_rvv_mmio_ongoing_txn[i] = 1; // ongoing txn
                l1_rvv_cg.sample(rvv_mmio_item[i].m_addr, rvv_mmio_item[i].m_we, $countones(m_l1_rvv_mmio_ongoing_txn));
                concurrent_devices[0] = (m_l1_mmio_ongoing_txn[AIC_DMC_COV_DMC_NUM_DEVICE-1:0]>0);
                concurrent_devices[1] = (m_l1_mmio_ongoing_txn[AIC_DMC_COV_AXI_NUM_DEVICE-1:AIC_DMC_COV_DMC_NUM_DEVICE]>0);
                concurrent_devices[2] = (m_l1_rvv_mmio_ongoing_txn>0);
                l1_mmio_concurrency_cg.sample($countones({m_l1_rvv_mmio_ongoing_txn,m_l1_mmio_ongoing_txn}), concurrent_devices, AIC_DMC_COV_AXI_NUM_DEVICE);
              end else if (rvv_mmio_item[i].m_type == MMIO_TXN) begin  //the type we get when the transaction is over
                m_l1_rvv_mmio_ongoing_txn_count[i] -= 1;
                if (m_l1_rvv_mmio_ongoing_txn_count[i] == 0) begin
                  m_l1_rvv_mmio_ongoing_txn[i] = 0; // reset txn
                end
              end
            end
          join_none
        end
      end : dmc_rvv_proc

      forever begin : axi_slave_data
        taf_mon_axi_hp_slv.get(axi_hp_slv_item);
        l1_axi_slv_cg.sample(axi_hp_slv_item, $countones(m_l1_mmio_ongoing_txn));
      end : axi_slave_data

      forever begin : axi_master_data
        taf_mon_axi_hp_mst.get(axi_hp_mst_item);
      end : axi_master_data

      forever begin : aic_ls_proc
        taf_mon_aic_ls.get(aic_ls_item);
        aic_ls_sideband_cg.sample(aic_ls_item);
        aic_ls_irq_cg.sample(aic_ls_item);
      end : aic_ls_proc

      begin : aic_ls_reg_proc
        foreach (m_reg_access_evt[j]) begin
          automatic int i = j;
          fork
            forever begin
              m_reg_access_evt[i].wait_trigger_data(m_uvm_obj[i]);
              if (!$cast(m_v_obj[i], m_uvm_obj[i])) begin
                `uvm_fatal(get_type_name(), "Cast failed!")
              end
              if (i < AIC_DMC_COV_IFD_NUM_DEVICE) begin
                ifd_reg_dev_cg[i].sample(m_v_obj[i]);
                `uvm_info(get_name(), $sformatf("ifd_reg_dev_cg[%0d] func_cov sampled! v_obj.m_string: %s", i, m_v_obj[i].m_string), UVM_HIGH)
              end else if (i < AIC_DMC_COV_IFD_NUM_DEVICE + AIC_DMC_COV_ODR_NUM_DEVICE) begin
                odr_reg_dev_cg[i-AIC_DMC_COV_IFD_NUM_DEVICE].sample(m_v_obj[i]);
                `uvm_info(get_name(), $sformatf("odr_reg_dev_cg[%0d] func_cov sampled! v_obj.m_string: %s", i, m_v_obj[i].m_string), UVM_HIGH)
              end
            end
          join_none
       end
      end : aic_ls_reg_proc

    join
  endtask : run_phase
endclass

`endif
