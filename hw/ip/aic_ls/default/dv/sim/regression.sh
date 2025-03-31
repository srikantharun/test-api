#!/bin/bash
umask 002
top=ai_core_ls
if [ "$1" == "-f" ]
then
python3 ../../../../../../../scripts/triton_rms/regression.py -f Testlist.pass.hjson -m $top -r 1 -cover 1 -p 1 -copy 1 -test 0
else
python3 ../../../../../../../scripts/triton_rms/regression.py -f Testlist.pass.hjson -m $top -r 1 -cover 1 -p 1 -copy 1 -test 1
fi
