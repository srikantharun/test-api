#! /usr/bin/perl

use strict;
#use warnings;

##########################################
### Arguments                         
##########################################
my $arg;
my $grd                   = 0;                                         ## grid mode
my $lsf                   = 0;                                         ## LSF mode
my $seed                  = "";
my $machine               = 0;                                         ## Dedicated machine 
my $scratch               = 0;                                         ## scratch disk
my $dumpvpd               = 0;                                         ## dump waveform in VPD format
my $dumpfsdb              = 0;                                         ## dump wavefomr in FSDB format
my $nosva                 = 1;                                         ## no SVA 
my $nocmp                 = 0;                                         ## no compile
my $noxprop               = 0;                                         ## no xpropagation
my $nocov                 = 0;                                         ## no coverage collection
my $nodbg                 = 0;                                         ## no debug accsss
my $fast_cmpl_opt         = "";                                        ## Fast compilation 
my $rptonly               = 0;                                         ## report only
my $cmponly               = 0;                                         ## compile only
my $printcmd              = 0;                                         ## print command
my $upfsim                = 0;                                         ## UPF simulation
my $GLB_TARGET_LINK_SPEED = "GEN4";                                    ## target link speed
my $GLB_AXI_MSTR_CLK_PER  = 1667;                                      ## AXI master clock period in ps
my $GLB_AXI_SLV_CLK_PER   = 1667;                                      ## AXI slave clock periold in ps
my $GLB_AXI_DBI_CLK_PER   = 10000;                                      ## AXI DBI clock periold in ps
my $GLB_CXS_CLK_PER       = 1000;                                      ## CXS clock periold in ps  #mmah: FIXME: which clk frq to be taken here?
my $GLB_AUX_CLK_PER       = 10000;                                      ## auxilary clock period in ps
my $GLB_APB_CLK_PER       = 10000;                                      ## APB clock periold in ps
my $SVT_AXI_MAX_ADDR_USER_WIDTH = 200;
my $SVT_AXI_MAX_DATA_USER_WIDTH = 200;
my $SVT_AXI_MAX_BRESP_USER_WIDTH= 200;                                    #mmah: FIXME: added from sm. default is 4. how do we set this? any std way?
my $LINKUP_TIMEOUT_VAL    = 10000000;                                  ## link up timeout value in ps #mmah: FIXME: how to set?  
my $STARTUP_DELAY         = 0;                                         ## simulation delay in ns to start up env #mmah: FIXME: how to set?   
my $testlistfile          = "./tests/DS_SS_pcie_subsystem.test_list";  ## test list
my $testgroup             = "";                                        ## test group
my $logfile               = "./runtest.log";                           ## log file of regression status 
my $output_path           = "TESTS_COMPILE_DIR";                       ## output path
my $simulator             = "vcs";                                     ## simulator. Limited support of NC.
my $sva_option            = "+define+SVA_PHY_RXEQEVAL_TIMEOUT_NS=5000000 +define+SVA_POSTED_WR_TO_RX_CONTROL3_TOL_NS=100000000"; 
my $batch_job;
my $job_kill;
my $job_enviornment;
my $current_wdir;
my $login_shell;
my $jobname;
my $binorscript;
my $seperator;
my $job_depend;
my $os_version;
my $virtualmem;
my $singlejobstatus;
my $jobstatus;
my $multithreadjobs;

while($arg = shift @ARGV) {
  if($arg=~m/^-grd$/i) {
    $grd     = 1;
  }elsif($arg=~m/^-lsf$/i) {
    $lsf = 1;
  } elsif($arg =~ /^-seed$/i) {
    $seed    = shift @ARGV;
  }elsif($arg=~m/^-nomachine$/i) {
    $machine = 0;
  } elsif($arg =~ /^-nogrd$/i) {
    $grd = 0;
  }elsif($arg=~m/^-scratch$/i) {
    $scratch = 1;
  } elsif($arg=~m/^-localdisk$/i) {
    $scratch = 0;
  } elsif($arg=~m/^-dumpvpd$/i) {
    $dumpvpd = 1;
  } elsif($arg=~m/^-dumpfsdb$/i) {
    $dumpfsdb= 1;
  } elsif($arg=~m/^-nosva$/i) {
    $nosva   = 1;
  } elsif($arg=~m/^-nocmp$/i) {
    $nocmp   = 1;
  } elsif($arg=~m/^-noxprop$/i) {
    $noxprop = 1;
  } elsif($arg=~m/^-nocov$/i) {
    $nocov   = 1;
  } elsif($arg=~m/^-nodbg$/i) {
    $nodbg   = 1;
  }elsif($arg =~ /^-fst_cmpl$/i) {
    #$qsub_multicore_opt  = " -pe mt 4 ";
    $fast_cmpl_opt       = " -partcomp -fastpartcomp=j4 -pcmakeprof ";
    #$fast_cmpl_opt       = " ";
  } elsif($arg=~m/^-rptonly$/i || $arg=~m/^-rpt_ponly$/i || $arg=~m/^-rpt$/i) {
    $rptonly = 1;
    $printcmd= 1;
  } elsif($arg=~m/^-cmponly$/i || $arg=~m/^-componly$/i || $arg=~m/^-comp_only$/i || $arg=~m/^-cmp/i) {
    $cmponly = 1;
  } elsif($arg=~m/^-printcmd$/i) {
    $printcmd= 1;
  } elsif($arg=~m/^-upfsim$/i) {
    $upfsim  = 1;
  } elsif($arg=~m/^-speed$/i || $arg=~m/^-sim_speed$/i) {
    $GLB_TARGET_LINK_SPEED = shift @ARGV;
    $GLB_TARGET_LINK_SPEED = uc($GLB_TARGET_LINK_SPEED);
  } elsif($arg=~m/^-cxs_clk_per$/i) {
    $GLB_CXS_CLK_PER       = shift @ARGV;
  } elsif($arg=~m/^-aux_clk_per$/i) { 
    $GLB_AUX_CLK_PER       = shift @ARGV;
  } elsif($arg=~m/^-apb_clk_per$/i) { 
    $GLB_APB_CLK_PER       = shift @ARGV;
  } elsif($arg=~m/^-linkup_timeout_val$/i) { 
    $LINKUP_TIMEOUT_VAL    = shift @ARGV;
  } elsif($arg =~ /^-SVT_AXI_MAX_ADDR_USER_WIDTH$/i) { 
    $SVT_AXI_MAX_ADDR_USER_WIDTH= shift @ARGV;
  } elsif($arg =~ /^-SVT_AXI_MAX_DATA_USER_WIDTH$/i) { 
    $SVT_AXI_MAX_DATA_USER_WIDTH= shift @ARGV;
  } elsif($arg =~ /^-SVT_AXI_MAX_BRESP_USER_WIDTH$/i) { 
    $SVT_AXI_MAX_BRESP_USER_WIDTH= shift @ARGV;
  } elsif($arg=~m/^-startup_delay$/i) { 
    $STARTUP_DELAY         = shift @ARGV;
  } elsif($arg=~m/^-testlist$/i || $arg=~m/^-testfile$/i) {
    $testlistfile= shift @ARGV;
  } elsif($arg=~m/^-group$/i) {
    $testgroup   = shift @ARGV;
  } elsif($arg=~m/^-logfile$/i) {
    $logfile     = shift @ARGV;
  } elsif($arg=~m/^-output_path$/i || $arg=~m/^-o$/i) {
    $output_path = shift @ARGV;
  } elsif($arg=~m/^-nc[\w-]*$/i) {
    $simulator   = "nc";
  } elsif($arg=~m/^(-help|--help|-h|--h|-usage|--usage|-u|--u)$/i) {
    system("perldoc $0");
    exit(0);
  } else {
    print "Unkown options: $arg\n";
    system("perldoc $0");
    exit(0);
  }
}

if($GLB_TARGET_LINK_SPEED!~/^GEN[1-4]$/i && ($GLB_TARGET_LINK_SPEED ne "")) {
  print "Unkown target link speed: $GLB_TARGET_LINK_SPEED! Target link speed must be GEN1, GEN2, GEN3, GEN4.\n";
  exit(0);
}

$output_path =~ s/\/$//;
if($output_path eq ''){
  print "Invalid output path. Please provide output path through <-output_path <mypath>>\n";
  exit(0);
}
if($simulator=~m/nc/i) {
  $output_path = "${output_path}_NC";
  $upfsim      = 0;
}

my @abbr = qw(Jan Feb Mar Apr May Jun Jul Aug Sep Oct Nov Dec);
my ($sec, $min, $hour ,$mday, $mon, $year, $wday, $yday, $isdst) = localtime(time);
my $timestr = sprintf("%d%s%d_%02dh_%02dm_%02ds",$year+1900,$abbr[$mon],$mday,$hour,$min,$sec);


##########################################
### Compile Path
##########################################

my $pwddir = `pwd`;
chomp $pwddir;
my $myname = `whoami`;
chomp $myname;
my $glb_cmpdir = "$pwddir/$output_path/all";
my $output_basename = $output_path;

if(($rptonly==0) && ($nocmp==0)) {
  if($output_path=~m/^\//) {
    print("The output path is :$output_path. Scratch cannot be used!\n");
    $scratch = 0;
    $output_basename = `basename $output_path`;
    $glb_cmpdir = "$output_path/all";
    chomp $output_basename;
  }
  if($scratch==1) {
    print "Hello $myname! Allocating scratch disk ...\n";
    my @tmp_scratch = qx(/global/cust_apps_sgip001/dw_tools/bin/nfsScratch);
    chomp @tmp_scratch[0];
    system_or_report("mkdir -p @tmp_scratch[0]/$myname/${output_path}_$timestr");
    if(-l "$output_path") {
      system_or_report("\\rm -rf ./$output_path");
    }
    system_or_report("\\ln -sf @tmp_scratch[0]/$myname/${output_path}_$timestr ./$output_path");
    system_or_report("\\echo $pwddir/$output_path @tmp_scratch[0]/$myname/${output_path}_$timestr >> ~$myname/tmp_scratch");

    print "Using @tmp_scratch[0] scratch disk.\n";
  } else {
    system_or_report("\\mkdir -p $output_path");
  }
}

##########################################
### Compile VIP                          #
##########################################
if(-d "$pwddir/models") {
} else {
  print "Compile VIP\n";
  system "./compile_vip.sh >> $logfile";
}


##########################################
### Test Group
##########################################
my @test_all_group;
my @test_run_group;
my @test_exc_group;

if($testgroup=~m/,/) {
  @test_all_group = split(/,/, $testgroup);
} elsif($testgroup ne "") {
  push @test_all_group, $testgroup;
}

foreach my $tmp_name (@test_all_group){
  if($tmp_name =~ /^no(\w+)/){
    push @test_exc_group, $1;
  } else {
    push @test_run_group, $tmp_name;
  }
}

##########################################
### Variables
##########################################
my $rom_ext_binfile         = "$ENV{PCIE_PHY_PATH}/phy/firmware/dwc_c20pcie4_phy_x4_ns_pcs_raw_ref_100m_ext_rom.bin";
my $rom_ext_cntx_binfile    = "$ENV{PCIE_PHY_PATH}/phy/firmware/dwc_c20pcie4_phy_x4_ns_pcs_raw_ref_100m_ext_rom.bin";
my $rom_ext_fast_sim_binfile= "$ENV{PCIE_PHY_PATH}/phy/firmware/dwc_c20pcie4_phy_x4_ns_pcs_raw_ref_100m_ext_rom.fastsim";
my $sram_fast_sim_fw        = "$ENV{PCIE_PHY_PATH}/phy/firmware/dwc_c20pcie4_phy_x4_ns_pcs_raw_sram_ref_100m_fastsim.fw";
my $default_uvm_verbosity   = "UVM_LOW"; 
my $uvm_time_out_val        = "2000000";
my $uvm_quit_count          = "100";
my $dbgfile                 = "./runtest.dbg";
my $top_files               = "top_files";

##########################################
### Platform Variables
##########################################
my $vcs64bit;
my $nc64bit;
my $ccflags_dyn;
my $ldflags_dyn;
my $verdi_platform;
my $disable_verdi = 0;
&set_os_version_bit();

###########################################
#GRID settings
###########################################
if($lsf==0){
$batch_job = 'qsub -P bnormal -A long';
$job_kill  = 'qdel';
$job_enviornment = '-V'; ##By default UGE does not pass current shell environment.
$current_wdir = '-cwd';
$login_shell= '-S /bin/sh';
$jobname   = '-N';
$binorscript = '-b y';
$seperator  = '';
$job_depend ='-hold_jid';
$os_version = '-l os_version=CS7.0';
$virtualmem = '-l h_vmem=';
$singlejobstatus = 'qstat -j';
$jobstatus  = 'qstat';
$multithreadjobs = '-pe mt 2';
}else{
  if ($machine==1){
    $batch_job = 'bsub -app normal -U FRS_370';
  }else {
    $batch_job = 'bsub -app normal ';
  }
$job_kill  = 'bkill';
$job_enviornment = ''; ##By default LSF passes all current shell environment variables.
$current_wdir = ''; ##No need to specify for the current working directory in LSF, however if specified it means to change to another path
#$login_shell= '-L /bin/sh';
$login_shell= ''; #seems if add -L , there be an error on founding cmd
$jobname   = '-J';
$binorscript = '';
$seperator  = '\"';
$job_depend ='-w';
$os_version = '-R \"select[os_version=CS7.0]\"';
$virtualmem = '-v ';
$singlejobstatus = 'bjobs'; #here, no use bjobs -l
$jobstatus = 'bjobs';
$multithreadjobs = '-R \"span[hosts=1]\" -n 2';
#$multithreadjobs = '';
}

##########################################
### Compile and Run options
##########################################
###-----------------
### Assertion Options
###-----------------
my $sva_cmpopt = "";
if($nosva==0) {
#  $sva_cmpopt  = "-assert enable_diag -assert svaext ";
#  $sva_cmpopt .= ' -f ./assertion/common/compile.f ';  #to be updated with SVA
#  $sva_cmpopt .= '+define+UPCS_PIPE_ASSERTIONS_EXCEPTIONS=\'\"upcs_pipe_assertions_exceptions.v\"\' -f ./assertion/compile.f -f ./assertion/customer_sva_clk_rst/compile.f'; 
}

###-----------------
### Coverage Options
###-----------------
my $cov_cmpopt = "";
my $cov_simopt = "";
my $tmp_cov_simopt = "";
if($nocov==0) {
  $cov_cmpopt = "-cm line+cond+tgl+fsm+branch+assert -cm_noconst -cm_hier ./cov_config.vcs -cm_dir ./simv.vdb -cm_tgl portsonly -assert enable_diag -assert dve ";
  $tmp_cov_simopt = "-cm line+cond+tgl+fsm+branch+assert -cm_dir ./sub_simv.vdb -assert nopostproc -assert maxfail=10 -assert no_default_msg ";
}

###-----------------
### Coverage Options
###-----------------
my $dbg_cmpopt = "";
$dbg_cmpopt = "+lint=PCWM -debug_access+all -debug_region=cell+encrypt" if($nodbg==0);
$dbg_cmpopt = "-debug_access+r+f " if($nodbg==1);
###-----------------
### incdir Options
###-----------------
my $incdir_cmpopt = "+error+100 +incdir+$ENV{VCS_HOME}/include +incdir+$pwddir/models/vip/src/sverilog/vcs +incdir+$pwddir/models/vip/include/sverilog +incdir+$pwddir/models/vip/src/verilog/$simulator +incdir+$pwddir/models/vip/include/verilog +incdir+$pwddir/{.,env,env/strap_pin_uvc,env/agents/DwDutCxsAgent,env/agents/dti_ats_vip,env/agents/DwDutInterface,env/agents/utbBaseLib,env/agents/ss_jtag_vip,ral,wrapper,include,tests}";

###-----------------
### Warning Options
###-----------------
my $warn_cmpopt = "";
$warn_cmpopt .= "+warn=noSVA-LDRF "; #Warning-[SVA-LDRF] Large delay or repetition found.
$warn_cmpopt .= "+warn=noDRTZ ";     #Warning-[DRTZ] Detect delay value roundoff to 0
$warn_cmpopt .= "+warn=noTMR ";      #Warning-[TMR] Text macro redefined
$warn_cmpopt .= "+warn=noTMBIN ";    #Warning-[TMBIN] Too many bits in Based Number
$warn_cmpopt .= "+warn=noRVOSFD ";   #Warning-[RVOSFD] Return value discarded

###-----------------
### UPF Options
###-----------------
my $upf_cmpopt = "";
my $upf_simopt = "";
if($upfsim==1) {
  $upf_cmpopt  = "-upf $pwddir/../upf/DS_SS_PCIE_subsystem.upf -power_top DS_SS_PCIE_subsystem -power=attributes_on ";
  $upf_cmpopt .= "-power=coverage -power=dump_hvp " if($nocov==0);
  $upf_simopt  = "-power $pwddir/../upf/vcs_power_config.tcl " if($simulator=~m/vcs/i);
  $upf_simopt  = "-power $pwddir/../upf/nc_power_config.tcl " if($simulator=~m/nc/i);
}else{
  $upf_cmpopt  = " +define+DWC_PCIE5_X4NS_TOP_PG_PINS";
  $upf_simopt  = "-power $pwddir/../upf/vcs_power_config.tcl " if($simulator=~m/vcs/i);
}

###-----------------
### Reserved Options
###-----------------
my $rsv_cmpopt = "";
$rsv_cmpopt='-P ./models/obj/amd64/vcs/pli.tab ./models/obj/amd64/vcs/msglog.o ' if($simulator=~m/vcs/i);
$rsv_cmpopt='-P ./models/obj/amd64/ncv/pli.tab ./models/obj/amd64/ncv/msglog.o ' if($simulator=~m/nc/i);

##########################################
### SDF Options
##########################################
my $sdf_cmpopt = "";
#$sdf_cmpopt = "+nospecify +notimingcheck -hsopt=gates +no_notifier "; #-j4 +nocelldefinepli+2
$sdf_cmpopt = " +notimingcheck ";

###-----------------
### Testbench Options
###-----------------
my $tb_cmpopt = "";
#$tb_cmpopt = " +define+CXS_CLK_PER=$GLB_CXS_CLK_PER +define+AUX_CLK_PER=$GLB_AUX_CLK_PER +define+APB_CLK_PER=$GLB_APB_CLK_PER +define+LINKUP_TIMEOUT_VAL=$LINKUP_TIMEOUT_VAL +define+STARTUP_DELAY=$STARTUP_DELAY -top test_top";
$tb_cmpopt = " +define+UVM_OBJECT_MUST_HAVE_CONSTRUCTOR +define+UVM_NO_DEPRECATED +define+CXS_CLK_PER=$GLB_CXS_CLK_PER +define+AUX_CLK_PER=$GLB_AUX_CLK_PER +define+APB_CLK_PER=$GLB_APB_CLK_PER +define+LINKUP_TIMEOUT_VAL=$LINKUP_TIMEOUT_VAL +define+STARTUP_DELAY=$STARTUP_DELAY +define+AXI_MSTR_CLK_PER=$GLB_AXI_MSTR_CLK_PER +define+AXI_DBI_CLK_PER=$GLB_AXI_DBI_CLK_PER +define+SVT_AXI_MAX_ADDR_USER_WIDTH=$SVT_AXI_MAX_ADDR_USER_WIDTH +define+SVT_AXI_MAX_DATA_USER_WIDTH=$SVT_AXI_MAX_DATA_USER_WIDTH +define+SVT_AXI_MAX_BRESP_USER_WIDTH=$SVT_AXI_MAX_BRESP_USER_WIDTH   -top test_top"; #FIXME: added SVT_AXI_MAX_ADDR_USER_WIDTH, SVT_AXI_MAX_DATA_USER_WIDTH, SVT_AXI_MAX_BRESP_USER_WIDTH from sm. how do we set these?
#$tb_cmpopt = " +define+CXS_CLK_PER=$GLB_CXS_CLK_PER +define+AUX_CLK_PER=$GLB_AUX_CLK_PER +define+APB_CLK_PER=$GLB_APB_CLK_PER +define+LINKUP_TIMEOUT_VAL=$LINKUP_TIMEOUT_VAL +define+STARTUP_DELAY=$STARTUP_DELAY +define+SVT_AMBA_APB5_ENABLE -top test_top";
my $tb_simopt = "";

###-----------------
### UVM Options
###-----------------
my $uvm_cmpopt = "";
$uvm_cmpopt  = "-ntb_opts uvm-1.2 +define+SVT_UVM_TECHNOLOGY +define+SYNOPSYS_SV +define+UVM_HDL_MAX_WIDTH=1000 +define+UVM_REG_FIELD_LEVEL_ATTRIBUTE +define+DWC_PCIE6_UPCS_NS_L0P_SUPPORT +define+DWC_PCIE6_UPCS_NS_AGGREGATION_EN  +libext+.v+.V+.sv+.SV+ +librescan +libverbose -diskopt -check_all +error+1000 -Mupdate +define+ASSERT_ON+COVER_ON ";
$uvm_cmpopt .= qx(head -1 ./sim_build_options);
chomp $uvm_cmpopt;
$uvm_cmpopt .= " ".qx(cat vcs_build_options | tr '\n' ' ') if($simulator=~m/vcs/i);
chomp $uvm_cmpopt;
$uvm_cmpopt =~ s/`design_dir/$pwddir\/models\/vip/g;
$uvm_cmpopt =~ s/`SYNOPSYS/\${SYNOPSYS}/g;

my $uvm_simopt = "";
#$uvm_simopt = "+svt_pcie_enable_enumeration +svt_pcie_enable_transaction_logging +svt_debug_opts ";
$uvm_simopt = "+svt_pcie_enable_enumeration +svt_pcie_enable_transaction_logging";

####------------------ #mmah: FIXME: removing completely. check this 1s
#####CSL Options 
####------------------
#my $csl_opt  ="";
#$csl_opt = ' -CFLAGS \"'."-g -I $ENV{PCIE_X16_IDE_PATH}/sim/bin/csl -I$ENV{PCIE_WORKSPACE}/sim_uvm/models/vip/src/C".'\"'." $ENV{PCIE_WORKSPACE}/sim_uvm/models/vip/src/C/svt_security_aes_gcm_dpi.cpp $ENV{PCIE_X16_IDE_PATH}/sim/bin/csl/csl.a ";
#

###-----------------
### Wave Options
###-----------------
my $wave_cmpopt = "";
$wave_cmpopt = "+define+SVT_VIP_WRITER_NEW_HIER+VERDI_EXISTS -P $ENV{VERDI_HOME}/share/PLI/VCS/${verdi_platform}/novas.tab $ENV{VERDI_HOME}/share/PLI/VCS/${verdi_platform}/pli.a" if($disable_verdi==0);
my $wave_simopt = "";
$wave_simopt = "+WAVES_VPD "  if($dumpvpd==1);
#$wave_simopt = "+fsdb+functions +WAVES_FSDB " if($dumpfsdb==1);
$wave_simopt = " +WAVES_FSDB " if($dumpfsdb==1);

###-----------------
### Xprop Options
###-----------------
my $xprop_cmpopt = "";
my $xprop_cmpopt = "-xprop=./xprop.cfg -xprop=unifiedInference" if($noxprop==0);


##########################################
### Generate Run script and report                        
##########################################
my @testlist;
my %cmplist;
my $testidx = 0;
my %cmp_id_q;
my %cmp_path;
  
&gen_sim_script;

my $testsch  = $#testlist + 1;
my $testcpl  = 0;
my $testpass = 0;
my $testSkip = 0;
my $testhang = 0;
my $testfail = 0;
my $testleft = 0;

system("echo \"+---------------------------+------+\"   >  $logfile");
system("echo \"  Number of Tests Scheduled | $testsch\" >> $logfile");
system("echo \"+---------------------------+------+\"   >> $logfile");
system("echo \"  Number of Tests Completed | $testcpl\" >> $logfile");
system("echo \"+---------------------------+------+\"   >> $logfile");

system("echo \"+---------------------------+------+\"   >  $dbgfile");
system("echo \"  Number of Tests Scheduled | $testsch\" >> $dbgfile");
system("echo \"  Run Regression with GRD   | $grd\"     >> $dbgfile");
system("echo \"  Only Generate Report ?    | $rptonly\" >> $dbgfile");
system("echo \"+---------------------------+------+\"   >> $dbgfile");

if($cmponly==1) {
  while (scalar(keys %cmp_id_q)) {
    foreach my $cmpile_id (keys %cmp_id_q) {
      sleep(10);
      my @lines=qx($singlejobstatus $cmpile_id 2>/dev/null);
      if(scalar(@lines)==0) {
        delete $cmp_id_q{$cmpile_id};
        if(!-e "$cmp_path{$cmpile_id}/simv") {
          foreach my $cmp_id (keys %cmp_id_q) {
            `$job_kill $cmp_id`;
          } ## foreach 
          print "PWD dir : $pwddir\n";
          print "\033[0;31mCompile ERROR\033[0;0m, please check $cmp_path{$cmpile_id}/cmp_*.o$cmpile_id\n or wait a few moment of server sync to check $cmp_path{$cmpile_id}/test.cmp.log \n";
          exit(0);
        } ## if
      } ## if
    } ## foreach
  } ## while
  exit;
}

if($rptonly==1) {
  &gen_sim_report;
} else {
  &run_sim;
  &gen_sim_report;
}


sub gen_sim_script {
  my $src_line;

  open(SRCFILE, "$testlistfile") || die("ERROR! $testlistfile can't be found\n");
  while($src_line=<SRCFILE>) {
    my $local_target_link_speed = $GLB_TARGET_LINK_SPEED;
    my $local_axi_mstr_clk_per  = $GLB_AXI_MSTR_CLK_PER;
    my $local_upfsim = $upfsim;
    my $simdir;
    my $m_h_vmem = '32G';
    my $cmpdir = $glb_cmpdir;
    my $uvmtestname;
    my $testname;
    my $postfix;
    my $rootdir = `pwd`;
    #my $SEED;
    my $repeat_num;
    my $dwcpcie_type = "ctl";
    my $test_simopt = "";
    my $test_cmpopt = "";
    chomp $src_line;
    next if($src_line=~m/^\s*#/);
    next if($src_line=~m/^\s*\/\//);

    chomp $rootdir;
    $rootdir = $rootdir."/../..";

    if($testgroup ne "") {
      my $skip_test = 1;
      foreach my $tmp_run_group(@test_run_group) {
        if($src_line=~m/GROUP=$tmp_run_group/) {
          $skip_test = 0;
          last;
        };
      }
      foreach my $tmp_run_group(@test_exc_group) {
        if($src_line=~m/GROUP=$tmp_run_group/) {
          $skip_test = 1;
          last;
        };
      }
      if($skip_test==1){
        next;
      }
    }

    $tb_simopt = "";
    $local_target_link_speed = $GLB_TARGET_LINK_SPEED;
    $repeat_num = 1;

    if($src_line=~m/^\s*([\w\d\_]+)\s*-uid\s*_([\w\d\_]+)\s*--/) {
      $testname = $1;
      $postfix  = $2;
      my $tmp_postfix = $postfix;

      if($postfix=~m/mode(\d)/i) {
        $tb_simopt .= "+ss_mode_$1 ";
      }

      my $portidx = 0;
      my $cnt = 0;
      while($tmp_postfix=~s/^(\w+?)_//) {  #in thisprject only one controller
       my $porttype = $1;
       $porttype  = lc($porttype);
	   if($porttype eq "ep" || $porttype eq "rc") {
             $tb_simopt .= "+iip${cnt}_is_${porttype} +pcie${cnt}_seq=$testname ";
	   } elsif ($porttype ne "na") {
             print "Unknown PCIe type: current \$_ is $_\n";
             exit;
	   }
       $cnt++;
      }

      if($src_line=~m/REPEAT\s*=\s*(\d+)/i) {
        $repeat_num = $1;
      }
      if($src_line=~m/mem\s*=\s*(\w+)/i) { #need how much mem for a specified test
        $m_h_vmem = $1;
      }
      if($src_line=~m/NO_UPF/i){
        $local_upfsim = 0;
      }
      if($local_upfsim==1) {
        $simdir = "${testname}_${postfix}_upf";
      } else {
        $simdir = "${testname}_${postfix}";
        $upf_simopt = "";
      }
      if($simulator=~m/nc/i) {
        $simdir .= "_NC";
      }
      if($src_line=~m/\W(SIM_SPEED|SPEED)\s*=\s*(GEN1|GEN2|GEN3|GEN4)/i) {
        $local_target_link_speed = $2;
        $simdir .= "_$1";
      }
      if($src_line=~m/AXI_MSTR_CLK_PER\s*=\s*(\w+)/i) {
        $local_axi_mstr_clk_per = $1;
        $simdir .= "_axi_clk_$1";
      }
      if($src_line=~m/tl_performance_mode\s*=\s*(\w+)/i) {
        $simdir .= "_$1";
      }
      if($testname eq "tl_linkup"                   or
        $testname eq "tl_enumeration"               or 
        $testname eq "ss_phy_bypass_sram_bootload"  or 
        $testname =~ /tl_performance/               or 
        $testname =~ /pl_lane_reversal/             or 
        $testname eq "pl_width_change"              or 
        $testname eq "ss_pipe_loopback"             or 
        $testname eq "ss_pipe_phy_loopback"         or 
        $testname eq "ss_phy_internal_loopback"     or 
        $testname eq "ss_phy_sim"                   or 
        $testname eq "ss_reg_bit_bash"              or 
        $testname eq "ss_reg_hw_reset"              or 
        $testname eq "reg_wr_rd_using_RAL"          or 
        $testname eq "ss_reg_missed_check"          or 
        $testname eq "ss_ram_connect"               or 
        $testname eq "ss_fsm_track"                 or 
        $testname eq "ss_apb_timeout"               or 
        $testname eq "ss_pcie_int_with_st"          or 
        $testname eq "ss_apb_strobe_test"           or 
        $testname eq "reg_pcie_bit_bash"            or 
        $testname eq "reg_pcie_hw_reset"            or 
        $testname eq "ss_debug_signals"             or 
        $testname eq "pl_polarity_reverse"          or 
        $testname eq "pl_lane_flip"                 or 
        $testname eq "pl_lane_flip_linkwidth_down"  or 
        $testname eq "pl_compliance"                or 
        $testname eq "tl_mem_connect"               or 
        $testname eq "scan_test"                    or 
        $testname eq "ss_connectivity"              or 
        $testname eq "tl_linkup_no_srambypass"      or
        $testname eq "tl_linkup_repeat_clk"         or
        $testname eq "tl_linkup_perst"              or
        $testname eq "tl_sris_mode"                 or
        #$testname =~ /^reg_access_d/                or
        $testname eq "reg_access_invalid_reg"       or
        $testname =~ /ss_reg_phy_access/            or 
        $testname eq "dma_read_linked_list"         or 
        $testname eq "dma_read_local"               or 
        $testname eq "dma_write_linked_list"        or 
        $testname eq "dma_write_local"              or 
        $testname eq "dma_read_linked_list_vf"      or 
        $testname eq "dma_write_linked_list_vf"     or 
        $testname =~ /cxs/                          or 
        $testname =~ /_dti_/                        or 
        $testname =~ /direct/                       or 
        $testname =~ /jtag/
        ) {
        $uvmtestname = $testname;
      } else {
        $uvmtestname = 'lib_test';
      }

      $uvm_time_out_val = "2500000";
      $uvm_time_out_val = "100000000" if($src_line=~m/LONG_SIM/i);
      $uvm_time_out_val = "0"       if($src_line=~m/NO_TIMEOUT/i);

      my $tempstr = $src_line;
      $test_cmpopt = "";
      $test_simopt = "";
      while($tempstr=~s/\+define\+([\w\d\=\_]+)\s*//) {
        my $mydef = $1;
        $test_cmpopt .= "+define+$mydef ";
        $mydef =~ s/=/_/;
        $cmpdir .= "_$mydef";
      }
      if($tempstr=~m/BYPASS_SRAM\s*=\s*(\w+)/i) {
        $simdir .= "_bypass_sram_$1";
        $test_simopt .= " +bypass_sram=$1 +sram_bootload_bypass=1 ";
      }
      while($tempstr=~s/\s*(\+[\w\d\=\_]*)\s*//) {
        $test_simopt .= "$1 ";
      }

      if(-e $cmpdir) {
      } else {
        system_or_report("\\mkdir -p $cmpdir");
        system_or_report("\\cd $cmpdir;\\ln -s $pwddir/* . 2> /dev/null;\\rm -rf $output_basename; \\cd $pwddir");
        system_or_report("\\rm -rf $cmpdir/*.svi");
        system_or_report("\\cd $cmpdir;\\ln -s test_top_serdes.sv top_test.sv;\\cd $pwddir");
      }
      $simdir="$cmpdir/$simdir";

      if($seed == "") {
        $seed = int(rand(1)*1000000);
	    #  print ("Randomizing seed to value $seed\n");
      }
      print("seed = $seed\n");
      if(! -e "$cmpdir/test.startcmp") {
        system_or_report("echo -e \"DWCPCIE_TYPE=$dwcpcie_type ; export DWCPCIE_TYPE\nCX_SIM=vcs ; export CX_SIM\nMTI_VCO_MODE=32 ; export MTI_VCO_MODE\nenv > env.info\nwstestdir=`pwd`\nlocal=.\" > $cmpdir/test.startcmp");
        system_or_report("echo -e \"rm -rf ./csrc ./simv\" > $cmpdir/test.startcmp");
        system_or_report("echo -e \"vcs -lca -l test.cmp.log +error+1000 -timescale=1ns/1fs -picarchive +vpi -sverilog -gen_obj -kdb $vcs64bit $cov_cmpopt $dbg_cmpopt $incdir_cmpopt $rsv_cmpopt $sdf_cmpopt $tb_cmpopt $upf_cmpopt $uvm_cmpopt $warn_cmpopt $wave_cmpopt $xprop_cmpopt $test_cmpopt -o ./simv -f hdl_files -f $top_files $sva_cmpopt $sva_option $fast_cmpl_opt \n\" >> $cmpdir/test.startcmp");
      }

      if($rptonly!=1) {
        for(my $i=0; $i<$repeat_num; $i=$i+1) {
          print("seed = $seed\n");
          if (! -d "${simdir}_$i") {
            system_or_report("\\mkdir ${simdir}_$i") ;
          }

          if($nocov==0) {
            $cov_simopt = "$tmp_cov_simopt -cm_test $testname";
          }
          my $simcmd = "$cmpdir/simv +svt_pcie_link_speed=$local_target_link_speed +UVM_TESTNAME=$uvmtestname +UVM_MAX_QUIT_COUNT=$uvm_quit_count +UVM_TIMEOUT=$uvm_time_out_val +UVM_NO_RELNOTES +UVM_VERBOSITY=$default_uvm_verbosity +ntb_random_seed=$seed $test_simopt $cov_simopt $tb_simopt $upf_simopt $uvm_simopt $wave_simopt +rom_ext_cntx_binfile=$rom_ext_cntx_binfile +rom_ext_binfile=$rom_ext_binfile +rom_ext_fast_sim_binfile=$rom_ext_fast_sim_binfile +sram_fast_sim_fw=$sram_fast_sim_fw -l test.log ";
          $simcmd .= "+axi_mstr_clk_per_int=$local_axi_mstr_clk_per ";

          if( $testname =~ /jtag/){
            if( ! -f "${simdir}_$i/simv_jtag_send_data"){
              system_or_report("echo \"31 70000\n31 20000\" > ${simdir}_$i/simv_jtag_send_data");
            }
          }

          system_or_report("rm -rf ${simdir}_$i/test.startsim");
          system_or_report("echo -e \"ln -s $cmpdir/cov_config.vcs .\" > ${simdir}_$i/test.startsim");
          system_or_report("echo -e \"$simcmd \" >> ${simdir}_$i/test.startsim");
          system_or_report("chmod +x ${simdir}_$i/test.startsim");

          system_or_report("rm -rf ${simdir}_$i/dumpfsdb");                                                                         
          system_or_report("echo -e \"$simcmd +power +WAVES_FSDB -l test.log \" > ${simdir}_$i/dumpfsdb");
          system_or_report("chmod +x ${simdir}_$i/dumpfsdb");

          system_or_report("rm -rf ${simdir}_$i/dumpvcd");                                                                          
          system_or_report("echo -e \"$simcmd +WAVES_VCD -l test.log \" > ${simdir}_$i/dumpvcd");
          system_or_report("chmod +x ${simdir}_$i/dumpvcd");

          system_or_report("rm -rf ${simdir}_$i/dumpvpd");                                                                          
          system_or_report("echo -e \"$simcmd +WAVES_VPD -l test.log \" > ${simdir}_$i/dumpvpd");
          system_or_report("chmod +x ${simdir}_$i/dumpvpd");
          $seed = int(rand(1)*1000000);
        }
      }# if($rptonly!=1)

      system_or_report("chmod +x $cmpdir/test.startcmp");
      my $bsub_name = `basename $cmpdir`;
      chomp $bsub_name;
      $bsub_name .=  "_";
      $bsub_name .=  $timestr;
      for(my $i=0; $i<$repeat_num; $i=$i+1) {
        if($nocmp == 0){
          system_or_report("echo $batch_job $job_enviornment  $current_wdir $login_shell $binorscript $jobname ${seperator}sim_${testname}_$i${seperator} $job_depend ${seperator}cmp_${bsub_name}${seperator} $os_version ${virtualmem}$m_h_vmem $multithreadjobs test.startsim > ${simdir}_$i/test.grd" );
        }else{
          system_or_report("echo $batch_job $job_enviornment  $current_wdir $login_shell $binorscript $jobname ${seperator}sim_${testname}_$i${seperator} $os_version ${virtualmem}$m_h_vmem $multithreadjobs test.startsim > ${simdir}_$i/test.grd" );
        }
          system_or_report("chmod +x ${simdir}_$i/test.grd");
          $testlist[$testidx] = "${simdir}_$i";
          $testidx++;
      }
      system_or_report("echo $batch_job $job_enviornment  $current_wdir $login_shell $binorscript $jobname ${seperator}cmp_${bsub_name}${seperator} $os_version ${virtualmem}$m_h_vmem test.startcmp > $cmpdir/test.cmp.grd" );
      system_or_report("chmod +x $cmpdir/test.cmp.grd");

      if(! defined $cmplist{$cmpdir}) {
        if($rptonly==1) {
        } else{
          sleep(1);
          run_compile($cmpdir);
        }
      }
      $cmplist{$cmpdir}=1;
    }## if($src_line=~ /^\s*([\w\d\_]+)\s*-uid\s*_([\w\d\_]+)\s*--/) 
  } #PARSINGFILE
  close(SRCFILE);
}


sub run_compile {
  my $cmpdir = shift;
  if($grd==1) {
    if($simulator=~m/vcs/i && ($nocmp==0)) {
      chdir "$cmpdir";
      my $my_job_id;
      my $qsub_to_queue_already = 0;
      while($qsub_to_queue_already==0) {
        my @lines = qx("./test.cmp.grd");
        foreach my $myline (@lines) {
          print $myline;
          chomp($myline);
          if($lsf == 1  and  $myline=~m/Job <(\d+)> is submitted to queue/) {
            $my_job_id = $1;
            $cmp_id_q{$my_job_id} = 1;
            $cmp_path{$my_job_id} = $cmpdir;
            $qsub_to_queue_already = 1;
            last;
          }
          if($lsf == 0  and  $myline=~m/Your job (\d+) \("(.*)"\) has been submitted/) {
            $my_job_id = $1;
            $cmp_id_q{$my_job_id} = 1;
            $cmp_path{$my_job_id} = $cmpdir;
            $qsub_to_queue_already = 1;
            last;
          }
        }
      #	sleep(10);
      }
      chdir "$pwddir";
    } ## if($simulator=~m/vcs/i && ($nocmp==0))
  } ## $grid==1
}


sub run_sim {
  my $simdir;
  my $second;
  my $minute;
  my $hour;
  my %job_id_q;
  my %job_path;

  if($grd==1) {
    if($simulator=~m/vcs/i){
      if($nocmp==0) {
        my $do_not_submit_simv = 0;
        while (scalar(keys %cmp_id_q)) {
          foreach my $cmpile_id (keys %cmp_id_q){
            sleep(10);
            my @lines=qx($singlejobstatus $cmpile_id 2>/dev/null);
            my $push_out_cmp_id = 0;
            if(scalar(@lines)==0 and $lsf == 0){
              $push_out_cmp_id = 1;
            }elsif($lsf == 1){
              my $tmp = @lines[1];
              my @wds=split /\s+/, $tmp;
              if($wds[4] =~ /EXIT/ or $wds[4] =~ /DONE/){
              $push_out_cmp_id = 1;
              }
            }
            if($push_out_cmp_id==1){
              delete $cmp_id_q{$cmpile_id};
              if (!-e "$cmp_path{$cmpile_id}/simv"){
                $do_not_submit_simv = 1;
              }
            }
            if($do_not_submit_simv==1){
              foreach my $cmp_id (keys %cmp_id_q){
                `$job_kill $cmp_id`;
              }
              print "PWD dir : $pwddir\n";
              print "\033[0;31mCompile ERROR\033[0;0m, please check $cmp_path{$cmpile_id}/cmp_*.o$cmpile_id\n or wait a moment to check $cmp_path{$cmpile_id}/test.cmp.log \n";
              exit(0);
            }
          }
        }
      } #noCMP == 0
    }else{ #$simulator
    }

    for($testidx=0; $testidx<=$#testlist; $testidx++) {
      $simdir = $testlist[$testidx];
      chdir "$simdir";
      my $my_job_id;
      my $qsub_to_queue_already = 0;
      while($qsub_to_queue_already==0){
        my @lines=qx("./test.grd");
        foreach my $myline(@lines) {
          print $myline;
          chomp($myline);
          if($lsf == 1 and $myline=~m/Job <(\d+)> is submitted to queue/) {
            $my_job_id = $1;
            $job_id_q{$my_job_id}  = 1;
            $job_path{$my_job_id}  = $simdir;
            $qsub_to_queue_already = 1;
            last;
          }
          if($lsf == 0 and $myline=~m/Your job (\d+) \("(.*)"\) has been submitted/) {
            $my_job_id = $1;
            $job_id_q{$my_job_id}  = 1;
            $job_path{$my_job_id}  = $simdir;
            $qsub_to_queue_already = 1;
            last;
          }
        }
      }
      chdir "..";
      system("echo \"$hour:$minute:$second submit test $simdir to lsf/grid\" >> $pwddir/$logfile");
    }

    if($rptonly==0) {
      my $stor_job_id_when_quit;
      print "\033[0;34mJobs are all submited~~~\nYou can kill all the jobs with:\033[0m $job_kill ";
      foreach my $myjobid (keys %job_id_q) {
        print $myjobid." ";
        $stor_job_id_when_quit .= $myjobid." ";
      }
      print "\n";
      if(-e "$pwddir/qdel_all_job"){
        `rm -rf $pwddir/qdel_all_job`;
      }
      `echo "$job_kill $stor_job_id_when_quit" > $pwddir/qdel_all_job`; ##this is for run.sh use;
      my %running_jb;
      my %last_log;
      my $start_sim_time = time();
      my $cnt_hour = 0;
      my $report_hour = 0;
      my $report_step = 3600; #one hour
      my %remember_log_tail = {};
      my %need_kill_jb_cnt;
      chdir "$pwddir";
      while (scalar(keys %job_id_q)) {
        sleep(60);
        my @lines=qx($jobstatus); #qx(qstat | grep -E "$jobid_str");
        $report_hour = 0;
        %running_jb = {};
        $cnt_hour = time() - $start_sim_time;
        if($cnt_hour>=$report_step){
          $report_hour = 1;
          $report_step += 1800; #30 min
          print "\n";
        }
        foreach my $line (@lines){
          if($line=~m/^\s*(\d+)\s+\S+\s+/) {
            $running_jb{$1} = 1;
          }
        }
        foreach my $chk_run_id (keys %job_id_q){
          my $test_case_passed;
          if($running_jb{$chk_run_id}==1) {
            if($report_hour!=0) {
              printf "\033[0;35mTEST RUNNING OVER %d Hour %d Min:\033[0m $job_path{$chk_run_id}",$cnt_hour/3600, ($cnt_hour/60)%60;
              my @tail_lines=qx(tail $job_path{$chk_run_id}/test.log -n 3);
              if(! defined $remember_log_tail{$chk_run_id}){
                print"\n";
                $remember_log_tail{$chk_run_id} = @tail_lines[0];
                $need_kill_jb_cnt{$chk_run_id} = 0;
              } else {
                if($remember_log_tail{$chk_run_id} eq @tail_lines[0]){
                  print "\033[0;35m ==> The test log didn't updat. The test might hang!\033[0m\n";
                  $need_kill_jb_cnt{$chk_run_id} = $need_kill_jb_cnt{$chk_run_id} + 1;
                  if($need_kill_jb_cnt{$chk_run_id} >111) {#About 3days
                    print "deleting job : $chk_run_id for test: $job_path{$chk_run_id}. The test log has not updated for a long time.\n";
                    `$job_kill $chk_run_id`;
                  }
                } else {
                  $remember_log_tail{$chk_run_id} = @tail_lines[0];
                  $need_kill_jb_cnt{$chk_run_id} = 0;
                  print "\033[1;35m ==> The test is still running!\033[0m\n";
                }
              }
            }
          } else {
            delete $job_id_q{$chk_run_id};
            #TODO://project different
            tar_log_file("$job_path{$chk_run_id}");
            my $testlog_exists = 1;
            open (GRDLOG,"$job_path{$chk_run_id}/test.log") or $testlog_exists = 0;
            if($testlog_exists==0) {
              $test_case_passed = 3;
            } else {
              my @all_lines=<GRDLOG>;
              close(GRDLOG);
              $test_case_passed = &check_log(\@all_lines);
            }
            if($test_case_passed==1) {
              print "\033[93;42m PASS \033[0m PATH: ".$job_path{$chk_run_id}."\n";
            } elsif ($test_case_passed==2) {
              print "\033[93;40m FAIL \033[0m \033[0;31mPATH:\033[0m ".$job_path{$chk_run_id}." \033[0;31mAbnormal Finished\033[0m.\n";
            #}elsif($test_case_passed == 3){
            #  print "\033[93;48m FAIL \033[0m PATH: ".$job_path{$chk_run_id}." \033[0;31mCannot find test.log\033[0m, need check the log.\n";
            } elsif($test_case_passed==0) {
              print "\033[93;41m FAIL \033[0m \033[0;31mPATH:\033[0m ".$job_path{$chk_run_id}."\n";
            } else {
              print "Strange \$test_case_passed value : $test_case_passed";
            }
          }
        }# $chk_run_id (keys %job_id_q
      }#while (scalar(keys %job_id_q
      `rm -rf $pwddir/qdel_all_job`;
    } else {#if($disable_auto_chk == 0){ #now is 1
      system("sleep 1h");
    }

  } else {#if($grd==1)
    if($simulator=~m/vcs/i) {
      if($nocmp==0) {
        foreach my $cmp_dir (keys %cmplist){
          chdir "$cmp_dir";
          system("./test.startcmp");
          chdir "../..";
        } 
      }#if($nocmp==0)
    } else { #$simulator
    }

    if($cmponly==0) {
      for($testidx=0; $testidx<=$#testlist; $testidx++) {
        $simdir = $testlist[$testidx];
        ($second, $minute, $hour) = localtime(time);
        system("echo \"$hour:$minute:$second  Test $simdir is running ...\" >> $logfile");
        chdir "$simdir";
        system("./test.startsim");
        chdir "..";
        ($second, $minute, $hour) = localtime(time);
        system("echo \"$hour:$minute:$second  Test $simdir is completed.\" >> $logfile");
      }
    }# if($cmponly==0) 
  }#end of grd==1
}


sub gen_sim_report {
  my $simdir;
  my $errflag;
  my $skpflag;
  my $hngflag;
  my $errcnt;
  my $simflag;
  my $errline;
  my $second;
  my $minute;
  my $hour;

  chdir "$pwddir";

  for($testidx=0; $testidx<=$#testlist; $testidx++) {
    $simdir = $testlist[$testidx];

    $errflag = 0;
    $skpflag = 0;
    $hngflag = 0;
    $errcnt  = 0;
    $simflag = 0;

    open (MYLOG, "$simdir/test.log");
    tar_log_file("$simdir");
    while($errline = <MYLOG>) {
      chomp $errline;
      if($errline=~m/SvtTestEpilog: Passed/) {
        $simflag = 1;
        $testcpl++;
        last;
      } elsif($errline=~m/\bERROR\b/ && $errline!~m/\(ERROR\)/) { #in upf simulation Invalid(ERROR) is a state
        $simflag = 1;
        $testcpl++;
        $errflag = 1;
        last;
      } elsif($errline=~m/SvtTestEpilog: Failed/) {
        $simflag = 1;
        $testcpl++;
        $errflag = 1;
        last;
      }elsif($errline=~m/SNPS SVA checker/) {
        $simflag = 1;
        $testcpl++;
        $errflag = 1;
        last;
      }elsif($errline=~m/IO BAR is NOT SUPPORTED by DUT :: Test is not applicable/) {
        $simflag = 1;
        $testcpl++;
        $skpflag = 1;
        last;
      }elsif($errline=~m/DUT does not support L1 PM extended capability with extended/) {
        $simflag = 1;
        $testcpl++;
        $skpflag = 1;
        last;
      }elsif($errline=~m/UVM_FATAL \@.*UVM_TESTNAME=.* not found./) {
        $simflag = 1;
        $testcpl++;
        $skpflag = 1;
        last;
      }elsif($errline=~m/OptionalFeatureNotSupportedBy\w+/) {
        $simflag = 1;
        $testcpl++;
        $skpflag = 1;
        last;
      }elsif($errline=~m/did not implement ARI Extended Capabilit/) {
        $simflag = 1;
        $testcpl++;
        $skpflag = 1;
        last;
      }elsif($errline=~m/Neither MFVC Capability nor VC Capability Register Supported by device/) {
        $simflag = 1;
        $testcpl++;
        $skpflag = 1;
        last;
      }elsif($errline=~m/^UVM_ERROR\s*\//) {
        $simflag = 1;
        $testcpl++;
        $errflag = 1;
        last;
      }elsif($errline=~m/Offending /) {
        $simflag = 1;
        $testcpl++;
        $errflag = 1;
        last;
      }
    }
    close (MYLOG);

    my $log_simdir = $simdir;
    if($log_simdir=~m/\/([^\/]+)$/) {
      $log_simdir = $1;
    }
    system("echo \"simflag=$simflag, skpflag=$skpflag, hngflag=$hngflag, errflag=$errflag, Test is $simdir\" >> $dbgfile");
    if($errflag!=0 && $simflag==1) {
      system("echo \"Result:  *** Test: $simdir => FAILED\" >> $logfile");
      system("touch failed/$log_simdir");
      system("touch $simdir/failed");
      $testfail++;
    } elsif($skpflag!=0) {
      system("echo \"Result:  *** Test: $simdir => SKIPPED\" >> $logfile");
      system("touch skipped/$log_simdir");
      system("touch $simdir/skipped");
      $testSkip++;
    } elsif($hngflag!=0) {
      system("echo \"Result:  *** Test: $simdir => HANG\" >> $logfile");
      system("touch failed/$log_simdir");
      system("touch $simdir/failed");
      $testhang++;
    } elsif($simflag!=0) {
      system("echo \"Result:  *** Test: $simdir => PASSED\" >> $logfile");
      system("touch passed/$log_simdir");
      system("touch $simdir/passed");
      #system("rm -rf $simdir/csrc $simdir/simv.daidir $simdir/simv");
      $testpass++;
    } else {
      system("echo \"Result:  *** Test: $simdir => RUNNING\" >> $logfile");
      $testleft++;
    }
  } # end of for

  system("mv $logfile $logfile.temp");
  system("echo \"+------------------------+\" >> $logfile");
  system("echo \"| Summary of all Results |\" >> $logfile");
  system("echo \"+------------------------+\" >> $logfile");
  system("echo \"\" >> $logfile");
  system("echo \"+---------------------------+------+\"   >> $logfile");
  system("echo \"  Number of Tests Scheduled | $testsch\" >> $logfile");
  system("echo \"+---------------------------+------+\"   >> $logfile");
  system("echo \"  Number of Tests Completed | $testcpl\" >> $logfile");
  system("echo \"+---------------------------+------+\"   >> $logfile");
  system("echo \" ________________________\"   >> $logfile");
  system("echo \"|                                   \"   >> $logfile");
  system("echo \"|  $testhang tests HANG!\" >> $logfile");
  system("echo \"|  $testfail tests FAILED!\" >> $logfile");
  system("echo \"|  $testSkip tests SKIPPED!\" >> $logfile");
  system("echo \"|  $testpass tests PASSED!\" >> $logfile");
  system("echo \"|  $testleft tests Running!\" >> $logfile");
  system("echo \"|________________________\"   >> $logfile");
  system("echo \"\" >> $logfile");
  if($testhang!=0) {
    system("echo \"$testhang tests HANG!\" >> $logfile");
    system("grep \"Result.*HANG\" $logfile.temp >> $logfile");
    system("echo \"\" >> $logfile");
  }
  if($testfail!=0) {
    system("echo \"$testfail tests FAILED!\" >> $logfile");
    system("grep \"Result.*FAILED\" $logfile.temp >> $logfile");
    system("echo \"\" >> $logfile");
  }
  if($testSkip!=0) {
    system("echo \"$testSkip tests SKIPPED!\" >> $logfile");
    system("grep \"Result.*SKIPPED\" $logfile.temp >> $logfile");
    system("echo \"\" >> $logfile");
  }
  if($testpass!=0){
    system("echo \"$testpass tests PASSED!\" >> $logfile");
    system("grep \"Result.*PASSED\" $logfile.temp >> $logfile");
    system("echo \"\" >> $logfile");
  }
  if($testleft!=0){
    system("echo \"$testleft tests Running!\" >> $logfile");
    system("grep \"Result.*RUNNING\" $logfile.temp >> $logfile");
    system("rm $logfile.temp");
  }
}


sub check_log{  #1 passed ; 0 failed; 2 running
  my $p = shift;
  foreach (@$p){
    return 0 if($_=~m/Simulation\s+TIMEOUT\s+ERROR/ || $_=~m/ERROR[\s-]*Simulation\s+Timeout/);
    if($_=~m/INFO.*WARNING.*ERROR\s+=\s+(\d*).*FATAL\s+=\s+(\d*)/) {
      return 0 if(($1!=0) || ($2!=0));
    } 
    return 0 if($_=~m/^Error-\[/);  #compile error
    return 0 if($_=~m/SNPS SVA checker/); #assertion error
    return 0 if($_=~m/\bERROR\b/ && $_!~m/\(ERROR\)/);  #in upf simulation Invalid(ERROR) is a state
    return 0 if($_=~m/\WFATAL\W/ || $_=~m/^ERROR\W/ || $_=~m/^FATAL\W/ || $_=~/\WFAILED\W/); #in upf simulation Invalid(ERROR) is a state
    if($_=~m/^\s*UVM_ERROR\s*:\s*(\d+)/) {
      return 0 if($1!=0);
    } 
    return 0 if($_=~m/^\s*UVM_ERROR\s+\D+/);
    return 1 if($_=~m/Simulation\s+Finished/ || $_=~m/TEST\s+SUITE\s+Finished/);
    return 1 if($_=~m/Simulation\s+Finished\s*\(\s*Skipped\s*\)/ || $_=~m/SKIPPED\s+-\s+TEST\s+SUITE\s+not\s+executed/);
    return 1 if($_=~m/SvtTestEpilog: Passed/);
    return 0 if($_=~/SvtTestEpilog: Failed/);
    return 0 if($_=~/Offending /);
  }
  return 2;
}


sub set_os_version_bit{
  my $os_uname;
  my $mach_uname;
  my $bitarch;
  my $platform;

  $os_uname = qx(/bin/uname -s);
  $mach_uname = qx(/bin/uname -m);

  if($os_uname =~ m/SunOS/) {
    if($mach_uname =~ m/i86pc/) {
      $bitarch = qx(isainfo -b);
      if($bitarch =~ m/64/) {
       $platform         = "x86sol64";
       $vcs64bit         = "-full64";
       $nc64bit          = "+nc64bit";
       $ccflags_dyn      = "-Kpic -m64";
       $ldflags_dyn      = "-G";
      } else {
       $platform         = "x86sol32";
       $vcs64bit         = "";
       $nc64bit          = "";
       $ccflags_dyn      = "-Kpic -m32";
       $ldflags_dyn      = "-G";
      }
    } else {
      $bitarch  = qx(isainfo -b);
      if($bitarch =~ m/64/ ){
       $platform         = "sparc64";
       $vcs64bit         = "-full64";
       $nc64bit          = "+nc64bit";
       $ccflags_dyn      = "-Kpic -m64";
       $ldflags_dyn      = "-G";
      }else{
       $platform         = "sparcOS5";
       $vcs64bit         = "";
       $nc64bit          = "";
       $ccflags_dyn      = "-Kpic -m32";
       $ldflags_dyn      = "-G";
      }
    }
  } elsif($os_uname =~ m/Linux/) {
      $bitarch  = qx(uname -i);
      if($bitarch =~ m/_64/) {
        if(qx(lsb_release) =~ m/amd64/) {
          $platform      = "amd64";
        }else{
          $platform      = "suse64";
        }
        $verdi_platform  = "LINUX64";
        $nc64bit         = "+nc64bit";
        $vcs64bit        = "-full64";
        $ccflags_dyn     = "-fPIC";
        $ldflags_dyn     = "-shared";
      } else {
        if(qx(lsb_release) =~ m/linux/) {
         $platform       = "linux";
        }else{
         $platform       = "suse32";
        }
       $verdi_platform   = "LINUX";
       $nc64bit          = "";
       $vcs64bit         = "";
       $ccflags_dyn      = "-m32 -fPIC";
       $ldflags_dyn      = "-m32 -shared";
      }
  } else {
    print "Unsupported platform! Exiting...\n";
    exit(0);
  }

  if(defined $ENV{VERDI_HOME}) {
  } elsif(defined $ENV{NOVAS_HOME}) {
    $ENV{VERDI_HOME}=$ENV{NOVAS_HOME};
  } else{
    $disable_verdi = 1;
  }
}


sub system_or_report {
  my $my_args = shift;
  if($printcmd==1) {
    print "\n$my_args\n";
  } else {
    system($my_args);
  }
}


sub tar_log_file {
  my $path = shift;
  my @logfiles;
  my $name;
  @logfiles = `find $path | grep 'xact_log\\|sym_log\\|cm.log'`;
  foreach my $log (@logfiles){
    chomp $log;
    next if($log =~ m/\.tar\.gz/);
    if($log =~ /\/(\w+\.[^\/]*log)/) {
      $name = $1;
    }
    system_or_report("tar zcf ${log}.tar.gz -C $path $name");
    system_or_report("rm -rf $log");
  }
}

##########################################
###                POD                 ###
##########################################
=pod

=head1 NAME

runtest.pl - Run test regression of PCIe subsystem

=head1 SYNOPSIS

runtest.pl   
[-grd]
[-scratch]
[-localdisk]
[-dumpvpd]
[-dumpfsdb]
[-nosva]
[-nocmp]
[-noxprop]
[-nocov]
[-nodbg]
[-rptonly|-rpt|-rpt_only]
[-cmponly|-cmp|-comp_only|componly]
[-printcmd]
[-upfsim]
[-speed|-sim_speed <GEN1|GEN2|GEN3|GEN4>]
`ifdef AXI_POPULATED
[-axi_mstr_clk_per_0 <axi master clock period in ps>]
[-axi_mstr_clk_per_1 <axi master clock period in ps>]
[-axi_slv_clk_per <axi slave clock period in ps>]
[-axi_dbi_clk_per <axi dbi clock period in ps>]
`endif //AXI_POPULATED
[-cxl_clk_per <cxl clock period in ps>]
[-aux_clk_per <auxiliary clock period in ps>]
[-apb_clk_per <apb clock period in ps>]
[-linkup_timeout_val <link timeout threshold in ps>]
[-startup_delay <environment start-up delay>]
[-testfile|-testlist <test list file>]
[-group <test group>]
[-logfile <regression status log file>]
[-output_path|-o <compile output directory>] 
[-help|--help|-h|--h|-usage|--usage|-u|--u]

=head1 DESCRIPTION

This PERL script is to help you run test regression of the PCIe Subsystem.

=head1 EXAMPLE

   runtest.pl -nosva
   runtest.pl -rpt
   runtest.pl -grd

=cut


