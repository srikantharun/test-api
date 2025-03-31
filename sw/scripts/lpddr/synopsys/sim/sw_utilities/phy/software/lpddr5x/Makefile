# Makefile to create a sample initialization sequence based on customer input.
# Please refer to the Phyinit App Note for details on how to compile and run
# Phyinit software.

#
# Sample make commands to create initialization output for executing firmware
# training:
#    make FIRMWARE_PATH=/exmpale/fimrware/rel_0.75a
PROTOCOL  = lpddr5x
# Please specify FIRMWARE_PATH=<Absolute path to firmware release>.
# PhyInit looks for the firmware message block definition in
# $(FIRMWARE_PATH)/$(PROTOCOL)/mnPmuSramMsgBlock_$(PROTOCOL).h
# Ensure this path is provided correctly in order to compile PhyInit.
FIRMWARE_PATH ?=

FW_PROTOCOL ?= $(PROTOCOL)
# extract the 1st message block header only, but suppress error message just makefile wildcard
MSG_BLOCK_HEADER = $(shell ls $(FIRMWARE_PATH)/$(FW_PROTOCOL)/mnPmuSramMsgBlock_$(PROTOCOL)*.h 2>/dev/null | head -n 1)

# Location of the SR FW files
SR_FW_FILES_LOC ?=$(FIRMWARE_PATH)/save_restore
DEBUG   ?= 1
# Location of pll settings file
PLL_SETTINGS_FILE  ?=
CmntStr ?= //
ApbStr  ?=
gcov    ?= 0
NUM_PHY ?= 1
RET_EN  ?= 0
PUB_REV ?= 0
APB_WR_CHK ?= 1

ifeq (,$(findstring dimm,$(PROTOCOL)))
UnderScore =_
else
endif

SCRDIR   = ../scripts
OUTDIR   = output
OBJDIR   = obj
SRCDIR   = src
CUSTDIR  = userCustom
IDIR2    = -I$(FIRMWARE_PATH)/$(FW_PROTOCOL)
IFDEF    = -DFW_FILES_LOC=\"$(FIRMWARE_PATH)\"
IFDEF   += -DSR_FW_FILES_LOC=\"$(SR_FW_FILES_LOC)\"
IFDEF   += -DDWC_DDRPHY_NUM_PHY=$(NUM_PHY)
IFDEF   += -DRET_EN=$(RET_EN)
IFDEF   += -DPUB_REV=$(PUB_REV)
CC       = gcc
LIBS     = -lm
CFLAGS   = -Wall -m64 -fPIC -std=gnu99 -fPIC -I$(SRCDIR) -I$(CUSTDIR) $(IDIR2) $(IFDEF) -g



CFLAGS   += -D_BUILD_LPDDR5X

CFLAGS   += -D_BUILD_LPDDR5





ifneq ($(PROTOCOL), $(FW_PROTOCOL))
CFLAGS += \
    -DIMEM_INCV_FILENAME=\"$(wildcard $(FIRMWARE_PATH)/$(FW_PROTOCOL)/$(FW_PROTOCOL)*_imem.incv)\" \
    -DDMEM_INCV_FILENAME=\"$(wildcard $(FIRMWARE_PATH)/$(FW_PROTOCOL)/$(FW_PROTOCOL)*_dmem.incv)\" \
    -DMSG_BLOCK_H=\"$(notdir $(MSG_BLOCK_HEADER))\"
endif # ($(PROTOCOL), $(FW_PROTOCOL))

LDFLAGS  =
ifeq ($(gcov),1)
CFLAGS  += -fprofile-arcs -ftest-coverage
LDFLAGS += -lgcov
endif


HDR  = dwc_ddrphy_phyinit.h
HDR += dwc_ddrphy_phyinit_protocols.h
HDR += dwc_ddrphy_phyinit_struct.h
HDR += dwc_ddrphy_csr_ALL_cdefines.h
ALLHDR = $(patsubst %,$(SRCDIR)/%,$(HDR))

FUNC  = dwc_ddrphy_phyinit_main
FUNC += dwc_ddrphy_phyinit_globals
FUNC += dwc_ddrphy_phyinit_sequence
FUNC += dwc_ddrphy_phyinit_restore_sequence
FUNC += dwc_ddrphy_phyinit_C_initPhyConfig
FUNC += dwc_ddrphy_phyinit_I_loadPIEImage
FUNC += dwc_ddrphy_phyinit_progCsrSkipTrain
FUNC += dwc_ddrphy_phyinit_setUserInput
FUNC += dwc_ddrphy_phyinit_getUserInput
FUNC += dwc_ddrphy_phyinit_cmnt
FUNC += dwc_ddrphy_phyinit_print
FUNC += dwc_ddrphy_phyinit_assert
FUNC += dwc_ddrphy_phyinit_print_dat
FUNC += dwc_ddrphy_phyinit_setMb
FUNC += dwc_ddrphy_phyinit_softSetMb
FUNC += dwc_ddrphy_phyinit_getMb
FUNC += dwc_ddrphy_phyinit_LoadPieProdCode
FUNC += dwc_ddrphy_phyinit_calcMb
FUNC += dwc_ddrphy_phyinit_G_execFW
FUNC += dwc_ddrphy_phyinit_H_readMsgBlock
FUNC += dwc_ddrphy_phyinit_D_loadIMEM
FUNC += dwc_ddrphy_phyinit_F_loadDMEM
FUNC += dwc_ddrphy_phyinit_storeIncvFile
FUNC += dwc_ddrphy_phyinit_storeMsgBlk
FUNC += dwc_ddrphy_phyinit_WriteOutMem
FUNC += dwc_ddrphy_phyinit_IsDbyteDisabled
FUNC += dwc_ddrphy_phyinit_initStruct
FUNC += dwc_ddrphy_phyinit_regInterface
FUNC += dwc_ddrphy_phyinit_setStruct
FUNC += dwc_ddrphy_phyinit_chkInputs

CUSTFUNC  = dwc_ddrphy_phyinit_setDefault
CUSTFUNC += dwc_ddrphy_phyinit_log
CUSTFUNC += dwc_ddrphy_phyinit_userCustom_overrideUserInput
CUSTFUNC += dwc_ddrphy_phyinit_userCustom_A_bringupPower
CUSTFUNC += dwc_ddrphy_phyinit_userCustom_B_startClockResetPhy
CUSTFUNC += dwc_ddrphy_phyinit_userCustom_customPreTrain
CUSTFUNC += dwc_ddrphy_phyinit_userCustom_customPostTrain
CUSTFUNC += dwc_ddrphy_phyinit_userCustom_E_setDfiClk
CUSTFUNC += dwc_ddrphy_phyinit_userCustom_G_waitFwDone
CUSTFUNC += dwc_ddrphy_phyinit_userCustom_H_readMsgBlock
CUSTFUNC += dwc_ddrphy_phyinit_userCustom_J_enterMissionMode
CUSTFUNC += dwc_ddrphy_phyinit_userCustom_io_write16
CUSTFUNC += dwc_ddrphy_phyinit_userCustom_io_write32
CUSTFUNC += dwc_ddrphy_phyinit_userCustom_io_read16
CUSTFUNC += dwc_ddrphy_phyinit_userCustom_io_read32
CUSTFUNC += dwc_ddrphy_phyinit_userCustom_wait
CUSTFUNC += dwc_ddrphy_phyinit_userCustom_waitTime
CUSTFUNC += dwc_ddrphy_phyinit_userCustom_saveRetRegs
CUSTFUNC += dwc_ddrphy_phyinit_userCustom_RCDMessage
CUSTFUNC += dwc_ddrphy_phyinit_userCustom_majorMailboxMessage
CUSTFUNC += dwc_ddrphy_phyinit_userCustom_streamingMailboxMessage

OBJ     = $(patsubst %,$(OBJDIR)/%.o,$(FUNC))
CUSTOBJ = $(patsubst %,$(OBJDIR)/%.o,$(CUSTFUNC))
ALLOBJ  = $(OBJ) $(CUSTOBJ)

.SUFFIXES: .c .h .o

.DEFAULT: run
.PHONY: run compile link clean print_obj print_hdr print_func print_custfunc

OPTS = -debug $(DEBUG) -comment_string "$(CmntStr)" -apb_string "$(ApbStr)"
ifeq ($(RET_EN),1)
OPTS += -retention_exit 1
endif
ifneq ($(PLL_SETTINGS_FILE),)
OPTS += -pll_settings_file "$(PLL_SETTINGS_FILE)"
endif
ifneq ($(PUB_REV),)
OPTS += -pub_rev $(PUB_REV)
endif
default : run

$(OUTDIR):
	mkdir -p $(OUTDIR)

TMP_FILE_PRE      = $(OUTDIR)/tmp.dwc_ddrphy_phyinit_out_$(PROTOCOL)
OUT_FILE_PRE      = $(OUTDIR)/dwc_ddrphy_phyinit_out_$(PROTOCOL)

tmp_skiptrain     = $(TMP_FILE_PRE)_skiptrain
files_skiptrain   = $(OUT_FILE_PRE)_skiptrain.txt
vg_skiptrain      = $(OUT_FILE_PRE)_skiptrain.vglog
tmp_devinit       = $(TMP_FILE_PRE)_devinit_skiptrain
files_devinit     = $(OUT_FILE_PRE)_devinit_skiptrain.txt
vg_devinit        = $(OUT_FILE_PRE)_devinit_skiptrain.vglog
tmp_train1d2d     = $(TMP_FILE_PRE)_train
files_train1d2d   = $(OUT_FILE_PRE)_train.txt
vg_train1d2d      = $(OUT_FILE_PRE)_train.vglog

tmp_ret_skiptrain = $(TMP_FILE_PRE)_skiptrain_retention_exit
ret_skiptrain     = $(OUT_FILE_PRE)_skiptrain_retention_exit.txt
tmp_ret_devinit   = $(TMP_FILE_PRE)_devinit_skiptrain_retention_exit
ret_devinit       = $(OUT_FILE_PRE)_devinit_skiptrain_retention_exit.txt
tmp_ret_train1d2d = $(TMP_FILE_PRE)_train_retention_exit
ret_train1d2d     = $(OUT_FILE_PRE)_train_retention_exit.txt



ifeq ($(NUM_PHY),0)
$(error NUM_PHY cannot be 0)
endif

files     = $(files_skiptrain)
files    += $(files_devinit)
files    += $(files_train1d2d)

ret_files  = $(ret_skiptrain)
ret_files += $(ret_devinit)
ret_files += $(ret_train1d2d)


VGCMD = valgrind --leak-check=yes --track-origins=yes
vglogs    = $(vg_skiptrain) $(vg_devinit) $(vg_train1d2d)
valgrind: CFLAGS += -g -O0
valgrind: DEBUG = 2
valgrind: compile $(OUTDIR) $(vglogs)


ifeq (2,$(DEBUG))
CFLAGS += -g -O0
endif

ifeq ($(RET_EN),1)
  files += $(ret_files)
endif

$(vg_skiptrain) : $(OBJDIR)/phyinit
	$(VGCMD) $(OBJDIR)/phyinit -skip_train 1 $(OPTS) -output $(tmp_skiptrain) >& $@

$(vg_devinit) : $(OBJDIR)/phyinit
	$(VGCMD) $(OBJDIR)/phyinit -skip_train 2 $(OPTS) -output $(tmp_devinit)   >& $@

$(vg_train1d2d) : $(OBJDIR)/phyinit
	$(VGCMD) $(OBJDIR)/phyinit -skip_train 0 $(OPTS) -output $(tmp_train1d2d) >& $@

$(tmp_ret_skiptrain) $(tmp_skiptrain): $(OBJDIR)/phyinit
	$(VGOPTS) $(OBJDIR)/phyinit -skip_train 1 $(OPTS) -output $(tmp_skiptrain)

$(tmp_ret_devinit) $(tmp_devinit): $(OBJDIR)/phyinit
	$(VGOPTS) $(OBJDIR)/phyinit -skip_train 2 $(OPTS) -output $(tmp_devinit)

$(tmp_ret_train1d2d) $(tmp_train1d2d): $(OBJDIR)/phyinit
	$(VGOPTS) $(OBJDIR)/phyinit -skip_train 0 $(OPTS) -output $(tmp_train1d2d)



$(OUT_FILE_PRE)_%.txt: $(TMP_FILE_PRE)_%
	perl $(SCRDIR)/comment_csr_addr_name.pl -reg $(SCRDIR)/reg_names_hash -init=$< -o=$@

run: link $(OBJ) $(CUSTOBJ)
run2: compile $(OUTDIR) $(files) apb_wr_check
	rm -rf $(OUTDIR)/tmp.*
	@echo ------------------
	@echo PhyInit Successful
	@echo ------------------

compile: clean link $(OBJDIR)/phyinit
incremental_compile: link $(OBJDIR)/phyinit

$(OBJDIR)/phyinit: $(OBJ) $(CUSTOBJ)
	$(CC) -o $@ $^ $(CFLAGS) $(LDFLAGS) $(LIBS)

$(OBJ): $(OBJDIR)/%.o: $(SRCDIR)/%.c $(ALLHDR)
	@echo $@
	$(CC) -c -o $@ $< $(CFLAGS) $(LDFLAGS)

$(CUSTOBJ): $(OBJDIR)/%.o: $(CUSTDIR)/%.c $(ALLHDR)
	@echo $@
	$(CC) -c -o $@ $< $(CFLAGS) $(LDFLAGS)

link:
	@if [ ! -d $(ODIR) ]; then mkdir -p $(ODIR); fi
	@if [ ! -d $(OBJDIR) ]; then mkdir -p $(OBJDIR); fi
ifneq ($(MSG_BLOCK_HEADER),)
	@echo "found Message Block Header $(MSG_BLOCK_HEADER)"
else
	@printf "ERROR: could not find Message Block Header.\nFIRMWARE_PATH= \"$(FIRMWARE_PATH)\". Please specify FIRMWARE_PATH=<Absolute path to firmware release>.\nPhyInit looks for the firmware message block definition in <FIRMWARE_PATH>/$(FW_PROTOCOL)/mnPmuSramMsgBlock_$(PROTOCOL).h\nEnsure this path is provided correctly in order to compile PhyInit.\n"
	@false;
endif


clean:
	rm -rf $(OBJDIR) $(OUTDIR)

print_obj:
	@echo $(ALLOBJ)

print_custobj:
	@echo $(CUSTOBJ)

print_hdr:
	@echo $(HDR)

print_func:
	@echo $(FUNC)

print_custfunc:
	@echo $(CUSTFUNC)

apb_wr_check: $(files)
ifeq ($(APB_WR_CHK),1)
	$(eval APB_WR_CHK_RESULTS=$(shell grep -E '^\/\/.*dwc_ddrphy_apb_wr' $(OUTDIR)/*.txt > /dev/null 2>&1; echo $$?))
	$(eval APB_WR_CHK_STATUS=$(if $(filter $(APB_WR_CHK_RESULTS),0), "FAIL", "PASS"))
	$(if $(filter $(APB_WR_CHK_RESULTS),0), $(call apb_wr_check_error, $(APB_WR_CHK_STATUS)), true)
	@echo "APB_WR_CHK_RESULTS=$(APB_WR_CHK_RESULTS)"
	@echo "APB_WR_CHK_STATUS=$(APB_WR_CHK_STATUS)"
endif

define apb_wr_check_error
	@printf "ERROR: Found dwc_ddrphy_apb_wr() on commented line\n"
	grep -E '^\/\/.*dwc_ddrphy_apb_wr' $(OUTDIR)/*.txt
	@echo "ABP_WR_CHECK $(1)"
	@false
endef

