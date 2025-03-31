# Configuration for the IP
IP_NAME            = otp_design_tb_compile
TOP_LEVEL_MODULES  = otp_design_tb

BENDER_MANI_LOC    = $(MAKEFILE_DIR)/../dv/design_tb

BENDER_TARGETS_EXT  = asic
BENDER_TARGETS_EXT += sf5a

# Custom compile configuration

override GLOBAL_DEFINES += +define+ASSERTIONS_ON
override GLOBAL_DEFINES += +define+SOTP_SET_PWR_ON=1
override GLOBAL_DEFINES += +define+LOADMEM

# VSIM_VLOG_OPTS  =
# VSIM_VCOM_OPTS  =
# OTP memory model initialization file
OTP_WRAPPER_MEMFILE_PATH = $(MAKEFILE_DIR)/../dv/memfiles/otp_lcs_chip_perso.bin
VSIM_VOPT_OPTS  = -G otp_design_tb/u_otp_wrapper/u_otp_wrapper/u_sf_otp16kb_cp_a100_ln05lpe_4006000/MEM_FILE1=$(OTP_WRAPPER_MEMFILE_PATH)
VSIM_VOPT_OPTS += -G otp_design_tb/u_otp_wrapper/u_otp_wrapper/u_sf_otp16kb_cp_a100_ln05lpe_4006000/MEM_FILE2=$(OTP_WRAPPER_MEMFILE_PATH)
VSIM_VOPT_OPTS += -G otp_design_tb/u_otp_wrapper/u_otp_wrapper/u_sf_otp16kb_cp_a100_ln05lpe_4006000/TMEM_FILE1=$(OTP_WRAPPER_MEMFILE_PATH)
VSIM_VOPT_OPTS += -G otp_design_tb/u_otp_wrapper/u_otp_wrapper/u_sf_otp16kb_cp_a100_ln05lpe_4006000/TMEM_FILE2=$(OTP_WRAPPER_MEMFILE_PATH)

# VSIM_ELAB_OPTS  =
# VSIM run configuration
# VSIM_RUN_OPTS  =

# VSIM usage configuration
