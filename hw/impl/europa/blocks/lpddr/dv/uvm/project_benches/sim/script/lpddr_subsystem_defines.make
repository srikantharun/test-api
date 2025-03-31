HVL_SV_SOURCE = ../../verification_ip/top_env_pkg/lpddr_subsystem_hvl_top.sv
HDL_SV_SOURCE = ../../verification_ip/top_env_pkg/lpddr_subsystem_hdl_top.sv

METH_HOME = $(QUESTA_HOME)/uvm-1.2

# Dependent Packages
MVC_PKG = $(QUESTA_MVC_HOME)/include/questa_mvc_svapi.sv +incdir+$(QUESTA_MVC_HOME)/questa_mvc_src/sv +define+MAP_PROT_ATTR $(QUESTA_MVC_HOME)/questa_mvc_src/sv/mvc_pkg.sv
UVM_PKG = +incdir+$(QUESTA_HOME)/verilog_src/uvm-1.2/src $(QUESTA_HOME)/verilog_src/uvm-1.2/src/uvm_macros.svh $(QUESTA_HOME)/verilog_src/uvm-1.2/src/uvm_pkg.sv
UVMF_PKG = +incdir+$(UVMF_HOME)/common/fli_pkg $(UVMF_HOME)/common/fli_pkg/fli_pkg.sv +incdir+$(UVMF_HOME)/uvmf_base_pkg $(UVMF_HOME)/uvmf_base_pkg/uvmf_base_pkg_hdl.sv $(UVMF_HOME)/uvmf_base_pkg/uvmf_base_pkg.sv
AMBA_VIP_PKGS = +incdir+$(QUESTA_MVC_HOME)/questa_mvc_src/sv/apb3 $(QUESTA_MVC_HOME)/questa_mvc_src/sv/apb3/mgc_apb3_v1_0_pkg.sv +incdir+$(QUESTA_MVC_HOME)/questa_mvc_src/sv/axi4 $(QUESTA_MVC_HOME)/questa_mvc_src/sv/axi4/mgc_axi4_v1_0_pkg.sv +incdir+$(QUESTA_MVC_HOME)/questa_mvc_src/sv/apb3/modules $(QUESTA_MVC_HOME)/questa_mvc_src/sv/apb3/modules/apb_master.sv +incdir+$QUESTA_MVC_HOME/questa_mvc_src/sv/axi4/modules $(QUESTA_MVC_HOME)/questa_mvc_src/sv/axi4/modules/axi4_master.sv $(QUESTA_MVC_HOME)/questa_mvc_src/sv/apb3/modules/apb_monitor.sv $(QUESTA_MVC_HOME)/questa_mvc_src/sv/apb3/modules/apb5_monitor.sv $(QUESTA_MVC_HOME)/questa_mvc_src/sv/axi4/modules/axi4_monitor.sv
LPDDR_VIP_PKG = +incdir+$(AVERY_SIM)/src.IEEE +incdir+$(AVERY_SIM)/src +incdir+$(AVERY_DDR)/src.uvm +incdir+$(AVERY_DDR)/src +incdir+$(AVERY_DDR)/src.MTI $(AVERY_SIM)/src/avery_pkg.sv $(AVERY_DDR)/src/amem_pkg.sv $(AVERY_DDR)/src/amem_pkg_test.sv $(AVERY_SIM)/../ddrxactor/src/addr_intf.sv

AVERY_DEFINES = +define+AVERY_LPDDR2 +define+AVERY_LPDDR5 +define+AMEM_UVM +define+ADDR_INTF +define+AVERY_MTI +define+AVERY_UVM+UVM_REPORT_DISABLE_FILE_LINE
BASE_DEPENDENTS = $(UVM_PKG) $(UVMF_PKG) $(MVC_PKG) $(AMBA_VIP_PKGS) $(LPDDR_VIP_PKG)

INCDIRS = +incdir+$(TOP_DIR) +incdir+$(TOP_DIR)/../environment_packages/avery_vip/  +incdir+$(TOP_DIR) +incdir+$(TOP_DIR)/../environment_packages/apb_vip/config_policies/ +incdir+$(TOP_DIR)/../environment_packages/axi_vip/config_policies/ +incdir+$(BASE_DIR)/project_benches/tb/sequences/ +incdir+$(BASE_DIR)/project_benches/tb/tests/ +incdir+$(BASE_DIR)/project_benches/rtl/lpddr5x/v_roel/20240916_snps_ss2/ctrl/src +incdir+$(BASE_DIR)/project_benches/rtl/vendor/lowrisc/prim_subreg/default/rtl/include +incdir+$(BASE_DIR)/project_benches/tb/testbench/ +incdir+$(BASE_DIR)/project_benches/tb/functional_coverage/ 


# LPDDR Subsystem related defines

# Compile Options
VLOG_OPTIONS += -incr -64
COMPILE_DEFINES += +define+UVM_NO_DEPRECATED  $(AVERY_DEFINES)

# Optimization Options
OS = linux
VOPT_ARGS += -opt=-specialize -coverdeglitch 0
VOPT_OPTIONS += -incr -L mtiUvm +delay_mode_zero

# Simulation related options
SIM_MODE = c
VSIM_OPTIONS = -L mtiUvm -mvchome $(QUESTA_MVC_HOME) -t 1fs -$(SIM_MODE) -pli $(AVERY_PLI)/lib.$(OS)/libtb_ms64.so
VSIM_COV_CMD = coverage clear; coverage save -onexit $(LOG_FILE_DIR)/$(LOG_NAME).ucdb;
VSIM_DUMP_CMD = log -r /*;
VSIM_WAVE_CMD = -wlf "$(LOG_FILE_DIR)/$(LOG_NAME).wlf"
VSIM_RUN_CMD =  run -all; quit
VSIM_DO_CMD = -do '$(VSIM_COV_CMD) $(VSIM_DUMP_CMD) $(VSIM_RUN_CMD)'
VSIM_LOG_CMD = -l $(LOG_FILE_DIR)/$(LOG_NAME).log
TEST=lpddr_subsystem_sanity_test
LOG_NAME=$(TEST)_debug
LOG_FILE_DIR = $(SIM_DIR)/log
UVM_OPTIONS =  +UVM_TESTNAME=$(TEST)
VISUALIZER = 1
VSIM_PLUS_ARGS =
VERBOSITY="UVM_MEDIUM"
# Additional Defines
PI_DETAILS_PATH = $(SIM_DIR)/../tb/sequences/phy_init_details/
