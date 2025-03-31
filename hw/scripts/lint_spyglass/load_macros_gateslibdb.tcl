#
# Load the macros DBs
# Handle all the quirks for the DBs based on the macro name
#

foreach tech_lib "${MEM_LIBS} ${REG_FILES} ${STD_CELL_NDM_LIBS}" {
    puts "Reading: ${tech_lib}"
    if {
        ([string first "_vromp_hd_lvt_" $tech_lib] != -1) ||
        ([string first "tu_pll0519a01"  $tech_lib] != -1) ||
        ([string first "tu_pvt0501a01"  $tech_lib] != -1)
    } {
        read_file -type gateslibdb ${tech_lib}/*sspg_sigrcmax_0p7650v_125c*.db
    } elseif {[string first "tu_tem0501ar01" $tech_lib] != -1} {
        read_file -type gateslibdb ${tech_lib}/*_sspg_sigcmax_0p7100v_125c.db
    } elseif {[string first "ln05lpe_gpio_lib_" $tech_lib] != -1} {
        read_file -type gateslibdb ${tech_lib}/*_sigcmax_0p7650v_1p6200v_125c_*.db
    } elseif {[string first "_c54l08_" $tech_lib] != -1} {
        read_file -type gateslibdb ${tech_lib}/*_min_0p6050v_125c.db_ccs_tn_lvf
    } elseif {[string first "_efuse" $tech_lib] != -1} {
        read_file -type gateslibdb ${tech_lib}/*_sspg_sigcmax_0p6750v_125c.db
    } elseif {[string first "_otp" $tech_lib] != -1} {
        read_file -type gateslibdb ${tech_lib}/*_sspg_sigcmax_0p7650v_125c.db
    } elseif {
        ([string first "_monitor" $tech_lib] != -1) ||
        ([string first "imc_bank" $tech_lib] != -1)
    } {
        read_file -type gateslibdb ${tech_lib}/*_ssgnp0p77v125c*.db
    } else {
        read_file -type gateslibdb ${tech_lib}/*sspg_sigrcmax_0p7650v_0p7650v_125c*.db
    }
}
