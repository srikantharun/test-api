
# Extracted placement bounds for noc_h_west_p. Extracted from europa/flex-out-part/placement_guidance.tcl

create_bound -boundary { {2226.520 43.680} {2226.520 123.680} {2331.520 123.680} {2331.520 43.680} {2226.520 43.680} } -name reg_lnk_dist_center_to_west_32_req_1 -type soft [get_cells "u_noc_h_west/u_noc_art_h_west/m_reg_lnk_dist_center_to_west_32_req_1"]
create_bound -boundary { {676.520 157.680} {676.520 448.680} {790.520 448.680} {790.520 157.680} {676.520 157.680} } -name reg_lnk_dist_center_to_west_req -type soft [get_cells "u_noc_h_west/u_noc_art_h_west/m_reg_lnk_dist_center_to_west_req"]
create_bound -boundary { {1.520 78.680} {1.520 447.680} {50.520 447.680} {50.520 78.680} {1.520 78.680} } -name reg_lnk_west_cross_west_to_ddrw -type soft [get_cells "u_noc_h_west/u_noc_art_h_west/m_reg_lnk_west_cross_west_to_ddrw"]
create_bound -boundary { {2339.520 47.680} {2339.520 491.680} {2605.520 491.680} {2605.520 47.680} {2339.520 47.680} } -name reg_lnk_buff_west_to_ddr_req -type soft [get_cells "u_noc_h_west/u_noc_art_h_west/m_reg_lnk_buff_west_to_ddr_req"]
create_bound -boundary { {3802.520 11.680} {3802.520 526.680} {3946.520 526.680} {3946.520 11.680} {3802.520 11.680} } -name rgn_west_cross_to_center_top -type soft [get_cells "u_noc_h_west/u_noc_art_h_west/m_reg_lnk_west_cross_center_to_west"]
create_bound -boundary { {676.520 87.680} {676.520 152.680} {790.520 152.680} {790.520 87.680} {676.520 87.680} } -name reg_lnk_dist_center_to_west_32_0 -type soft [get_cells "u_noc_h_west/u_noc_art_h_west/m_reg_lnk_dist_center_to_west_32_0"]
create_bound -boundary { {2227.520 129.680} {2227.520 524.680} {2332.520 524.680} {2332.520 129.680} {2227.520 129.680} } -name reg_lnk_dist_center_to_west_req_resp -type soft [get_cells "u_noc_h_west/u_noc_art_h_west/m_reg_lnk_dist_center_to_west_req_resp"]
create_bound -boundary { {801.520 93.680} {801.520 446.680} {1126.520 446.680} {1126.520 93.680} {801.520 93.680} } -name reg_lnk_buff_west_to_ddr_req_resp -type soft [get_cells "u_noc_h_west/u_noc_art_h_west/m_reg_lnk_buff_west_to_ddr_req_resp"]
