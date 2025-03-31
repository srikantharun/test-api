#! /bin/bash

auditScript=`git rev-parse --show-toplevel`"/scripts/audit/audit.py"
milestoneList=("skeleton" "prebronze" "bronze" "silver" "gold")

getMaturityLevel() {
  idx=0
  for item in ${milestoneList[@]}
  do
    if [ $item == $1 ]; then
      return $idx
    else
      let "idx+=1"
    fi
  done
  return -1
}
signoffs=""
while getopts m:r:e:b:R:t: flag
do
    case "${flag}" in
        m) milestone=${OPTARG};;
        r) rtlDir=${OPTARG};;
        e) extTrgt=${OPTARG};;
        b) blk=${OPTARG};;
        t) tlm=${OPTARG};;
        R) releaseDir=${OPTARG};;
    esac
done
shift $((OPTIND -1))
so_filelist=$@
echo $so_filelist
for so in $so_filelist
do
  signoffs="${signoffs} -s ${so}"
done

getMaturityLevel $milestone
CertMilestoneIdx=$?

if [[ ${milestoneList[@]} =~ $milestone ]]; then
  echo "Certificate for ${milestone^^} maturity"
  echo ""
else
  echo "Unsupported milestone ${milestone}";
  exit
fi

function audit_log()
{
  tms=$1
  log=$2
  getMaturityLevel ${tms}
  MS=$?
  if [ $CertMilestoneIdx -ge $MS ]; then
    mkdir -p audit_reports/${tool}
    cp ${log} audit_reports/${tool} 2>/dev/null
    ${auditScript} -r ${rtlDir} -e "${extTrgt}" -m ${milestone} -q -t ${tool} -l ${log} -o audit_reports/${tool}/${log##*/} ${signoffs}
    let "STATUS+=$?"
    cp ${log} audit_reports/${tool} 2>/dev/null
  fi
}

STATUS=0
rm -f audit_run.log
rm -f certificate.txt


echo "====================================================" > certificate.log
echo "==               EUROPA CERTIFICATE               ==" >> certificate.log
echo "====================================================" >> certificate.log
echo "" >> certificate.log
echo "  MILESTONE :  ${milestone^^}" >> certificate.log
echo "  BLOCK     :  ${blk^^}" >> certificate.log
echo "  USER      : " `whoami` >> certificate.log
echo "  DATE      : " `date` >> certificate.log
echo "  WORKSPACE : " `pwd` >> certificate.log
echo "" >> certificate.log
echo "====================================================" >> certificate.log
echo "==                  SIGNOFF FILES                 ==" >> certificate.log
echo "====================================================" >> certificate.log
echo "" >> certificate.log
if [ ${#so_filelist[@]} -eq 0 ]; then
echo "  < None >                                          " >> certificate.log
else
mkdir -p audit_signoffs
for so in $so_filelist
do
echo "  SIGNOFF   : ${so}" >> certificate.log
cp ${so} audit_signoffs
done
fi
echo "" >> certificate.log
echo "====================================================" >> certificate.log
echo "==                    GIT LOG                     ==" >> certificate.log
echo "====================================================" >> certificate.log
echo "" >> certificate.log
git log -n 1 >> certificate.log
echo "" >> certificate.log
echo "====================================================" >> certificate.log
echo "==                 AUDIT RESULTS                  ==" >> certificate.log
echo "====================================================" >> certificate.log
echo "" >> certificate.log




###########################################
#### GIT CHECKS
###########################################

mkdir -p audit_reports/git/
git status --porcelain | grep "^ [AM]" > audit_reports/git/dirty_file_list.rpt
if [ `git status --porcelain | grep "^ [AM]" | wc -l` -gt 0 ]; then
echo "INFO: [FAIL] GIT      : ${milestone^^} : git checkout DIRTY" >> certificate.log
STATUS=1
else
echo "INFO: [PASS] GIT      : ${milestone^^} : git checkout CLEAN" >> certificate.log
fi

###########################################
#### RTL CHECKS
###########################################

tool="code_grep"
audit_log "skeleton"   "audit_todo/audit_todo.log"
tool="code_grep"
audit_log "silver"   "audit_waive/audit_waive.log"

###########################################
#### QUESTA ELABORATION CHECKS
###########################################

tool="questa"
audit_log "skeleton"   "../sim-questa/build_vsim_${blk}/compile_vsim/${blk}.analyze_vsim.log"
audit_log "skeleton"   "../sim-questa/build_vsim_${blk}/compile_vsim/${tlm}.vopt.log"
audit_log "skeleton"   "../sim-questa/build_vsim_${blk}/compile_vsim/${tlm}_vsim_elab.log"

###########################################
#### RTLA ELABORATION CHECKS
###########################################

tool="rtla"
LATEST=`ls --sort time ../synth-rtla/build_rtl_architect | awk 'BEGIN {L=0} { if (L==0) {print $1}; L=1}'`
audit_log "skeleton"   "../synth-rtla/build_rtl_architect/${LATEST}/${blk}_synthesis/logs/setup_lib.log"
audit_log "skeleton"   "../synth-rtla/build_rtl_architect/${LATEST}/${blk}_synthesis/logs/analyze.log"
audit_log "skeleton"   "../synth-rtla/build_rtl_architect/${LATEST}/${blk}_synthesis/logs/elaborate.log"
audit_log "bronze"     "../synth-rtla/build_rtl_architect/${LATEST}/${blk}_synthesis/logs/conditioning.log"

###########################################
#### SPYGLASS CHECKS
###########################################

tool="spyglass"
audit_log "bronze"   "../lint-spyglass_vc/build_spyglass/sg_proj/consolidated_reports/${blk}_lint_lint_rtl/moresimple.rpt"

###########################################
#### SUMMARY
###########################################

cat audit_run.log >> certificate.log
rm -f audit_run.log

echo "" >> certificate.log
echo "====================================================" >> certificate.log
echo "==              CERTIFICATION RESULT              ==" >> certificate.log
echo "====================================================" >> certificate.log
echo "" >> certificate.log


echo ""
if [ $STATUS -gt 0 ]; then
  echo "      Certificate: FAILED"
  echo "      Certificate: FAILED" >> certificate.log
else
  echo "      Certificate: PASSED"
  echo "      Certificate: PASSED" >> certificate.log
fi

echo "" >> certificate.log
echo "====================================================" >> certificate.log
echo "==            END OF EUROPA CERTIFICATE           ==" >> certificate.log
echo "====================================================" >> certificate.log

if [ $STATUS -eq 0 ]; then
  mv certificate.log certificate.txt
  cp certificate.txt certificate.${milestone}
fi

exit $STATUS
