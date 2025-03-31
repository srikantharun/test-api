#!/bin/bash


##  To achieve this, you need to create an ATPG model of the SERDES macro block with the necessary pad attributes defined to use the BSCAN flow. 
##   Typically you would use libcomp to create ATPG library file and you would manually add I/O definitions like so:

#cp /data/foundry/LIB/synopsys/lpddr5x/v_roel/Europa_lpddr_phy_config/src/dwc_lpddr5xphy_top.v ./
#edit the file to remove contents


phy_path=./

find $phy_path -name "dwc_lpddr5xphy_top.v" -print0 | while read -d $'\0' file
do
    filename=$(basename -- "$file")
    extension="${filename##*.}"
    filename="${filename%.*}"

    rm -f ./${filename}.libcomp.do
    cat > ./${filename}.libcomp.do <<EOF
set verification off
add models -all
set system mode translation
run
write library ./${filename}.atpglib -replace
exit
EOF
    libcomp $file \
    +define+DWC_LPDDR5XPHY__LPDDR5_ENABLE=1 \
    +define+DWC_LPDDR5XPHY_NUM_DBYTES_PER_CHANNEL=1 \
    +define+DWC_LPDDR5XPHY_NUM_RANKS=2 \
    +define+DWC_LPDDR5XPHY_NUM_TOP_SCAN_CHAINS=1368 \
    +define+DWC_LPDDR5XPHY_NUM_CHANNELS=2 \
    +define+DWC_LPDDR5XPHY_LPDDR5_ENABLED=1 \
    +define+DWC_LPDDR5XPHY_PMU_DCCM_ADDR_RANGE=12:0 \
    +define+DWC_LPDDR5XPHY_PMU_DBL_DCCM_BE_RANGE=9:0 \
    +define+DWC_LPDDR5XPHY_PMU_DBL_DCCM_RANGE=77:0 \
    +define+DWC_LPDDR5XPHY_PMU_ICCM0_BANK_WIDTH=78 \
    +define+DWC_LPDDR5XPHY_PMU_ICCM0_ADR_RANGE=16:4 \
    +define+DWC_LPDDR5XPHY_PMU_ICCM0_BANK_BYTE_SIZE=10 \
    +define+DWC_LPDDR5XPHY_PMU_BR_BC_DATA_RANGE=63:0 \
    +define+DWC_LPDDR5XPHY_PMU_BR_BC_IDX_RANGE=11:4 \
    +define+DWC_LPDDR5XPHY_PMU_BR_PT_DATA_RANGE=7:0 \
    +define+DWC_LPDDR5XPHY_PMU_BR_PT_RANGE=13:4 \
    +define+DWC_LPDDR5XPHY_PMU_DBL_DCCM_BE_SIZE=10 \
    +define+DWC_LPDDR5XPHY_NUM_DBYTES=4 \
    +define+DWC_LPDDR5XPHY_EXISTS_DB0=1 \
    +define+DWC_LPDDR5XPHY_EXISTS_AC0=1 \
    +define+DWC_LPDDR5XPHY_EXISTS_DB1=1 \
    +define+DWC_LPDDR5XPHY_DBYTE_DMI_ENABLED=1 \
    +define+DWC_LPDDR5XPHY_NUM_CHANNELS_2=1 \
    +define+DWC_LPDDR5XPHY_EXISTS_AC1=1 \
    +define+DWC_LPDDR5XPHY_EXISTS_DB3=1 \
    +define+DWC_LPDDR5XPHY_NUM_DBYTES_4=1 \
    +define+DWC_LPDDR5XPHY_EXISTS_DB2=1 \
    +define+DWC_LPDDR5XPHY_TECH__CDCBUF__DISABLE_BEHAVIORAL_VERILOG=1 \
    +define+DWC_LPDDR5XPHY_CDCBUF_MODE01_SUPPORT=1 \
    -dofile  ${filename}.libcomp.do \
    -logfile ${filename}.libcomp.log \
    -replace
done

##  The above creates the basic IO outline of the ATPG model. Unfortunately, you then need to add in the necessary pad attributes 
##  manually e.g. pad_pad_io, pad_from_pad, pad_tp_pad, pad_enable_high etc. and I am not aware of a way to automate this as it 
##  requires additional information from the Synopsys spec which Tessent can't determine itself e.g.:
##  
##  mode(
##    inout (BP_D[1]) (pad_pad_io; )
##    output (BypassInDataDAT[1]) (pad_from_pad; )
##    input  (BypassOutDataDAT[1]) (pad_to_pad; )
##    input  (BypassOutEnDAT[1]) (pad_enable_high; )
##  )
##  
##  This essentially creates the pad model for the SERDES IP block, and you can now use to run the BSCAN flow normally. The pad 
##  attributes identify the necessary ports and pad types BSCAN should consider. You would also specify the pad order based on 
##  the port orders of the macro to enforce a sensible BSCAN cell ordering.
##  
##  
