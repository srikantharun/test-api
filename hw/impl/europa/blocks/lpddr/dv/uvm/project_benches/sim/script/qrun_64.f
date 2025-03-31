export TOP_DIR_NAME=$(pwd)/../uvmf

qrun -f top_test_filelist.f \
../uvmf/hdl_top.sv \
../uvmf/hvl_top.sv \
-64 \
-debug \
-designfile design.bin \
-c \
-mvchome ${QUESTA_MVC_HOME} \
+nowarnTSCALE -t 1ps \
-do "run -all; quit" \
+UVM_TESTNAME=top_test_base \
+SEQ=top_example_vseq \
-qwavedb=+signal+transaction+class+uvm_schematic
