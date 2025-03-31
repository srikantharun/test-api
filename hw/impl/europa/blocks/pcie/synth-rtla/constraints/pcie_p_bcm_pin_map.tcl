# Set up pin names for the various hand-instantiated cells used within
# the design


# Pin mapping for sync_2_stage_src
set sync_2_stage_src_inst_name          "U_SAMPLE_META_2"
set sync_2_stage_src_data_s_pin         "D"
set sync_2_stage_src_clk_d_pin          "CK"
set sync_2_stage_src_rst_d_n_pin        "R"
set sync_2_stage_src_data_d_pin         "Q"

# Pin mapping for sync_3_stage_src
set sync_3_stage_src_inst_name          "U_SAMPLE_META_3"
set sync_3_stage_src_data_s_pin         "D"
set sync_3_stage_src_clk_d_pin          "CK"
set sync_3_stage_src_rst_d_n_pin        "R"
set sync_3_stage_src_data_d_pin         "Q"

# Pin mapping for sync_4_stage_src
set sync_4_stage_src_inst_name          "U_SAMPLE_META_4"
set sync_4_stage_src_data_s_pin         ""
set sync_4_stage_src_clk_d_pin          ""
set sync_4_stage_src_rst_d_n_pin        ""
set sync_4_stage_src_data_d_pin         ""

# Pin mapping for ck_gt_lat_src
set ck_gt_lat_src_inst_name             "I_hand_bcm_ck_gt_lat"
set ck_gt_lat_src_clk_in_pin            "CK"
set ck_gt_lat_src_en_pin                "E"
set ck_gt_lat_src_test_pin              "SE"
set ck_gt_lat_src_clk_out_pin           "ECK"

# Pin mapping for ck_buf_src
set ck_buf_src_inst_name                "I_hand_bcm_ck_buf"
set ck_buf_src_clk_in_pin               "A"
set ck_buf_src_clk_out_pin              "Y"

# Pin mapping for and_src
set and_src_inst_name                   "I_hand_bcm_and"
set and_src_a_pin                       "A"
set and_src_b_pin                       "B"
set and_src_z_pin                       "Y"

# Pin mapping for or_src
set or_src_inst_name                    "I_hand_bcm_or"
set or_src_a_pin                        "A"
set or_src_b_pin                        "B"
set or_src_z_pin                        "Y"

# Pin mapping for mx_src
set mx_src_inst_name                    "I_hand_bcm_mx"
set mx_src_a0_pin                       "A"
set mx_src_a1_pin                       "B"
set mx_src_s_pin                        "S"
set mx_src_z_pin                        "Y"

# Pin mapping for ck_and_src
set ck_and_src_inst_name                "I_hand_bcm_ck_and"
set ck_and_src_clk_a_pin                "A"
set ck_and_src_clk_b_pin                "B"
set ck_and_src_clk_z_pin                "Y"

# Pin mapping for ck_or_src
set ck_or_src_inst_name                 "I_hand_bcm_ck_or"
set ck_or_src_clk_a_pin                 "A"
set ck_or_src_clk_b_pin                 "B"
set ck_or_src_clk_z_pin                 "Y"

# Pin mapping for ck_mx_src
set ck_mx_src_inst_name                 "I_hand_bcm_ck_mx"
set ck_mx_src_clk0_pin                  "A"
set ck_mx_src_clk1_pin                  "B"
set ck_mx_src_s_pin                     "S0"
set ck_mx_src_clk_out_pin               "Y"

# Pin mapping for ck_dff_clrn_src
set ck_dff_clrn_src_inst_name             "I_hand_bcm_ck_dff_clrn"
set ck_dff_clrn_src_d_pin                 "D"
set ck_dff_clrn_src_clk_pin               "CK"
set ck_dff_clrn_src_rst_n_pin             "R"
set ck_dff_clrn_src_q_pin                 "Q"

# Pin mapping for ck_dff_prstn_src
set ck_dff_prstn_src_inst_name             "I_hand_bcm_ck_dff_prstn"
set ck_dff_prstn_src_d_pin                 "D"
set ck_dff_prstn_src_clk_pin               "CK"
#set ck_dff_prstn_src_prst_n_pin            "SD"
set ck_dff_prstn_src_prst_n_pin            "R"
set ck_dff_prstn_src_q_pin                 "Q"

# Pin mapping for dff_clrn_src
set dff_clrn_src_inst_name             "I_hand_bcm_dff_clrn"
set dff_clrn_src_d_pin                 "D"
set dff_clrn_src_clk_pin               "CK"
set dff_clrn_src_rst_n_pin             "R"
set dff_clrn_src_q_pin                 "Q"

# Pin mapping for dff_prstn_src
set dff_prstn_src_inst_name             "I_hand_bcm_dff_prstn"
set dff_prstn_src_d_pin                 "D"
set dff_prstn_src_clk_pin               "CK"
#set dff_prstn_src_prst_n_pin            "SD"
set dff_prstn_src_prst_n_pin            "R"
set dff_prstn_src_q_pin                 "Q"

# Pin mapping for clk_dflop_src
set clk_dflop_src_inst_name             "I_hand_bcm_clk_dflop"
set clk_dflop_src_d_pin                 ""
set clk_dflop_src_clk_pin               ""
set clk_dflop_src_rst_pin               ""
set clk_dflop_src_q_pin                 ""

# Pin mapping for buf_src
set buf_src_inst_name                 "I_hand_bcm_buf"
set buf_src_a_pin                    "A"
set buf_src_z_pin                    "Y"

# Pin mapping for dflop_src
set dflop_src_inst_name                 "I_hand_bcm_dflop"
set dflop_src_d_pin                     ""
set dflop_src_clk_pin                   ""
set dflop_src_clr_n_pin                 ""
set dflop_src_q_pin                     ""

