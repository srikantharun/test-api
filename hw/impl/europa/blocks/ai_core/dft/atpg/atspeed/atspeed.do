global ft block pat_ids mode fault_id sdc_mode sdc_corner

set block      ai_core_p
set mode       "int_mode"
set ft         transition
set pat_id     atpg_atspeed
set sdc_mode   scanAtspeed
set sdc_corner max_SSPG.0P72V.125C_RCWorstT_125ss

cd ..
dofile atpg.do
