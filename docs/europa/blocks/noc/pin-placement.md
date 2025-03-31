---
title: Pin Placement
doc:
  status: draft
  version: [0, 0, 1]
  confidentiality: internal
---

# Pin Placement

This section documents the relative placement of the _inter-partition_ NoC Link pins.

## NoC Link Bundle Pin Structure


Note that, assuming a Sender (TX) and a Receiver (RX) partition each NoC Link Bundle consists of the following signals (note the "Driver" column that indicates _direction_ from Sending to Receiving partition):

| Driver | width | name
|--------|------:|----------------
| TX     | Bus   | `[io]_dp_<name>_data`
| TX     | 1     | `[io]_dp_<name>_vld`
| TX     | 1     | `[io]_dp_<name>_head`
| TX     | 1     | `[io]_dp_<name>_tail`
| RX     | 1     | `[io]_dp_<name>_rdy`

<!-- TODO(psarras; a figure would be nice-to-have here -->

## DDR-West <--> West


| Placed | Pin Bundle                                                                       | TX       | RX
|--------|----------------------------------------------------------------------------------|----------|----------
| top    | `lnk_cross_west_to_ddrw_256_3_egr_to_lnk_cross_west_to_ddrw_256_3_ingr`          | West     | DDR-West
|        | `lnk_cross_west_to_ddrw_256_3_ingr_resp_to_lnk_cross_west_to_ddrw_256_3_egr_resp`| DDR-West | West
|        | `lnk_cross_west_to_ddrw_256_2_egr_to_lnk_cross_west_to_ddrw_256_2_ingr`          | West     | DDR-West
|        | `lnk_cross_west_to_ddrw_256_2_ingr_resp_to_lnk_cross_west_to_ddrw_256_2_egr_resp`| DDR-West | West
|        | `lnk_cross_west_to_ddrw_256_1_egr_to_lnk_cross_west_to_ddrw_256_1_ingr`          | West     | DDR-West
|        | `lnk_cross_west_to_ddrw_256_1_ingr_resp_to_lnk_cross_west_to_ddrw_256_1_egr_resp`| DDR-West | West
|        | `lnk_cross_west_to_ddrw_256_0_egr_to_lnk_cross_west_to_ddrw_256_0_ingr`          | West     | DDR-West
|        | `lnk_cross_west_to_ddrw_256_0_ingr_resp_to_lnk_cross_west_to_ddrw_256_0_egr_resp`| DDR-West | West
|        | `lnk_cross_west_to_ddrw_32_egr_to_lnk_cross_west_to_ddrw_32_ingr`                | West     | DDR-West
| bottom | `lnk_cross_west_to_ddrw_32_ingr_resp_to_lnk_cross_west_to_ddrw_32_egr_resp`      | DDR-West | West


## West <--> Center


| Placed | Pin Bundle                                                                            | TX      | RX
|--------|---------------------------------------------------------------------------------------|---------|----------
| top    | `lnk_cross_center_to_west_512_3_egr_to_lnk_cross_center_to_west_512_3_ingr`           | Center  | West
|        | `lnk_cross_center_to_west_512_3_ingr_resp_to_lnk_cross_center_to_west_512_3_egr_resp` | West    | Center
|        | `lnk_cross_center_to_west_512_2_egr_to_lnk_cross_center_to_west_512_2_ingr`           | Center  | West
|        | `lnk_cross_center_to_west_512_2_ingr_resp_to_lnk_cross_center_to_west_512_2_egr_resp` | West    | Center
|        | `lnk_cross_center_to_west_512_1_egr_to_lnk_cross_center_to_west_512_1_ingr`           | Center  | West
|        | `lnk_cross_center_to_west_512_1_ingr_resp_to_lnk_cross_center_to_west_512_1_egr_resp` | West    | Center
|        | `lnk_cross_center_to_west_512_0_egr_to_lnk_cross_center_to_west_512_0_ingr`           | Center  | West
|        | `lnk_cross_center_to_west_512_0_ingr_resp_to_lnk_cross_center_to_west_512_0_egr_resp` | West    | Center
|        | `lnk_cross_center_to_west_64_egr_to_lnk_cross_center_to_west_32_ingr`                 | Center  | West
| bottom | `lnk_cross_center_to_west_32_ingr_resp_to_lnk_cross_center_to_west_64_egr_resp`       | West    | Center


## North <--> Center


| Placed | Pin Bundle                                                                                            | TX      | RX
|--------|-------------------------------------------------------------------------------------------------------|---------|----------
| Left   | `lnk_cross_center_to_north_512_6_egr_wr_req_to_lnk_cross_center_to_north_512_6_ingr_wr_req`           | Center  | North
|        | `lnk_cross_center_to_north_512_0_egr_wr_req_to_lnk_cross_center_to_north_512_0_ingr_wr_req`           | Center  | North
|        | `lnk_cross_center_to_north_512_0_ingr_wr_req_resp_to_lnk_cross_center_to_north_512_0_egr_wr_req_resp` | North   | Center
|        | `lnk_cross_center_to_north_512_2_egr_rd_req_to_lnk_cross_center_to_north_512_2_ingr_rd_req`           | North   | Center
|        | `lnk_cross_center_to_north_512_2_ingr_rd_req_resp_to_lnk_cross_center_to_north_512_2_egr_rd_req_resp` | Center  | North
|        | `lnk_cross_center_to_north_512_3_egr_rd_req_to_lnk_cross_center_to_north_512_3_ingr_rd_req`           | Center  | North
|        | `lnk_cross_center_to_north_512_3_ingr_rd_req_resp_to_lnk_cross_center_to_north_512_3_egr_rd_req_resp` | North   | Center
|        | `lnk_cross_north_to_center_512_2_ingr_rd_req_resp_to_lnk_cross_north_to_center_512_2_egr_rd_req_resp` | Center  | North
|        | `lnk_cross_north_to_center_512_2_egr_rd_req_to_lnk_cross_north_to_center_512_2_ingr_rd_req`           | North   | Center
|        | `lnk_cross_north_to_center_512_3_egr_rd_req_to_lnk_cross_north_to_center_512_3_ingr_rd_req`           | North   | Center
|        | `lnk_cross_north_to_center_512_4_egr_rd_req_to_lnk_cross_north_to_center_512_4_ingr_rd_req`           | North   | Center
|        | `lnk_cross_north_to_center_512_3_ingr_rd_req_resp_to_lnk_cross_north_to_center_512_3_egr_rd_req_resp` | Center  | North
|        | `lnk_cross_north_to_center_512_5_egr_rd_req_to_lnk_cross_north_to_center_512_5_ingr_rd_req`           | North   | Center
|        | `lnk_cross_north_to_center_512_a_egr_wr_req_to_lnk_cross_north_to_center_512_a_ingr_wr_req`           | North   | Center
|        | `lnk_cross_north_to_center_512_0_ingr_wr_req_resp_to_lnk_cross_north_to_center_512_0_egr_wr_req_resp` | Center  | North
|        | `lnk_cross_north_to_center_64_egr_req_to_lnk_cross_north_to_center_64_ingr_req`                       | North   | Center
|        | `lnk_cross_north_to_center_512_a_ingr_wr_req_resp_to_lnk_cross_north_to_center_512_a_egr_wr_req_resp` | Center  | North
|        | `lnk_cross_center_to_north_64_egr_req_to_lnk_cross_center_to_north_64_ingr_req`                       | Center  | North
|        | `lnk_cross_north_to_center_512_4_ingr_rd_req_resp_to_lnk_cross_north_to_center_512_4_egr_rd_req_resp` | Center  | North
|        | `lnk_cross_center_to_north_512_b_egr_rd_req_to_lnk_cross_center_to_north_512_b_ingr_rd_req`           | Center  | North
|        | `lnk_cross_center_to_north_64_ingr_req_resp_to_lnk_cross_center_to_north_64_egr_req_resp`             | North   | Center
|        | `lnk_cross_north_to_center_512_0_egr_wr_req_to_lnk_cross_north_to_center_512_0_ingr_wr_req`           | North   | Center
|        | `lnk_cross_north_to_center_512_1_egr_rd_req_to_lnk_cross_north_to_center_512_1_ingr_rd_req`           | North   | Center
|        | `lnk_cross_north_to_center_512_5_ingr_rd_req_resp_to_lnk_cross_north_to_center_512_5_egr_rd_req_resp` | Center  | North
|        | `lnk_cross_north_to_center_64_ingr_req_resp_to_lnk_cross_north_to_center_64_egr_req_resp`             | Center  | North
|        | `lnk_cross_north_to_center_512_b_egr_rd_req_to_lnk_cross_north_to_center_512_b_ingr_rd_req`           | North   | Center
|        | `lnk_cross_center_to_north_512_6_ingr_wr_req_resp_to_lnk_cross_center_to_north_512_6_egr_wr_req_resp` | North   | Center
|        | `lnk_cross_center_to_north_512_a_egr_wr_req_to_lnk_cross_center_to_north_512_a_ingr_wr_req`           | Center  | North
|        | `lnk_cross_north_to_center_512_1_ingr_rd_req_resp_to_lnk_cross_north_to_center_512_1_egr_rd_req_resp` | Center  | North
|        | `lnk_cross_north_to_center_512_b_ingr_rd_req_resp_to_lnk_cross_north_to_center_512_b_egr_rd_req_resp` | Center  | North
|        | `lnk_cross_north_to_center_512_6_ingr_wr_req_resp_to_lnk_cross_north_to_center_512_6_egr_wr_req_resp` | Center  | North
|        | `lnk_cross_north_to_center_512_8_egr_wr_req_to_lnk_cross_north_to_center_512_8_ingr_wr_req`           | North   | Center
|        | `lnk_cross_center_to_north_512_b_ingr_rd_req_resp_to_lnk_cross_center_to_north_512_b_egr_rd_req_resp` | North   | Center
|        | `lnk_cross_north_to_center_512_6_egr_wr_req_to_lnk_cross_north_to_center_512_6_ingr_wr_req`           | North   | Center
|        | `lnk_cross_north_to_center_512_7_ingr_wr_req_resp_to_lnk_cross_north_to_center_512_7_egr_wr_req_resp` | Center  | North
|        | `lnk_cross_center_to_north_512_9_ingr_rd_req_resp_to_lnk_cross_center_to_north_512_9_egr_rd_req_resp` | North   | Center
|        | `lnk_cross_north_to_center_512_7_egr_wr_req_to_lnk_cross_north_to_center_512_7_ingr_wr_req`           | North   | Center
|        | `lnk_cross_center_to_north_512_8_ingr_wr_req_resp_to_lnk_cross_center_to_north_512_8_egr_wr_req_resp` | North   | Center
|        | `lnk_cross_north_to_center_512_9_egr_wr_req_to_lnk_cross_north_to_center_512_9_ingr_wr_req`           | North   | Center
|        | `lnk_cross_center_to_north_512_a_ingr_wr_req_resp_to_lnk_cross_center_to_north_512_a_egr_wr_req_resp` | North   | Center
|        | `lnk_cross_center_to_north_512_9_egr_rd_req_to_lnk_cross_center_to_north_512_9_ingr_rd_req`           | Center  | North
|        | `lnk_cross_center_to_north_512_8_egr_wr_req_to_lnk_cross_center_to_north_512_8_ingr_wr_req`           | Center  | North
|        | `lnk_cross_north_to_center_512_8_ingr_wr_req_resp_to_lnk_cross_north_to_center_512_8_egr_wr_req_resp` | Center  | North
|        | `lnk_cross_center_to_north_512_5_egr_rd_req_to_lnk_cross_center_to_north_512_5_ingr_rd_req`           | North   | Center
|        | `lnk_cross_north_to_center_512_9_ingr_wr_req_resp_to_lnk_cross_north_to_center_512_9_egr_wr_req_resp` | Center  | North
|        | `lnk_cross_center_to_north_512_4_ingr_rd_req_resp_to_lnk_cross_center_to_north_512_4_egr_rd_req_resp` | North   | Center
|        | `lnk_cross_center_to_north_512_5_ingr_rd_req_resp_to_lnk_cross_center_to_north_512_5_egr_rd_req_resp` | North   | Center
|        | `lnk_cross_center_to_north_512_7_egr_wr_req_to_lnk_cross_center_to_north_512_7_ingr_wr_req`           | Center  | North
|        | `lnk_cross_center_to_north_512_7_ingr_wr_req_resp_to_lnk_cross_center_to_north_512_7_egr_wr_req_resp` | North   | Center
|        | `lnk_cross_center_to_north_512_1_egr_wr_req_to_lnk_cross_center_to_north_512_1_ingr_wr_req`           | Center  | North
|        | `lnk_cross_center_to_north_512_4_egr_rd_req_to_lnk_cross_center_to_north_512_4_ingr_rd_req`           | Center  | North
| Right  | `lnk_cross_center_to_north_512_1_ingr_wr_req_resp_to_lnk_cross_center_to_north_512_1_egr_wr_req_resp` | North   | Center


## South <--> Center

| Placed | Pin Bundle                                                                                            | TX     | RX
|--------|-------------------------------------------------------------------------------------------------------|--------|----------
| Left   | `lnk_cross_center_to_south_512_8_egr_wr_req_to_lnk_cross_center_to_south_512_8_ingr_wr_req`           | Center | South
|        | `lnk_cross_center_to_south_512_8_ingr_wr_req_resp_to_lnk_cross_center_to_south_512_8_egr_wr_req_resp` | South  | Center
|        | `lnk_cross_center_to_south_512_9_egr_rd_req_to_lnk_cross_center_to_south_512_9_ingr_rd_req`           | Center | South
|        | `lnk_cross_center_to_south_512_9_ingr_rd_req_resp_to_lnk_cross_center_to_south_512_9_egr_rd_req_resp` | South  | Center
|        | `lnk_cross_center_to_south_512_b_egr_rd_req_to_lnk_cross_center_to_south_512_b_ingr_rd_req`           | Center | South
|        | `lnk_cross_center_to_south_512_a_egr_wr_req_to_lnk_cross_center_to_south_512_a_ingr_wr_req`           | Center | South
|        | `lnk_cross_center_to_south_512_a_ingr_wr_req_resp_to_lnk_cross_center_to_south_512_a_egr_wr_req_resp` | South  | Center
|        | `lnk_cross_center_to_south_512_b_ingr_rd_req_resp_to_lnk_cross_center_to_south_512_b_egr_rd_req_resp` | South  | Center
|        | `lnk_cross_south_to_center_512_b_ingr_rd_req_resp_to_lnk_cross_south_to_center_512_b_egr_rd_req_resp` | Center | South
|        | `lnk_cross_south_to_center_512_4_ingr_rd_req_resp_to_lnk_cross_south_to_center_512_4_egr_rd_req_resp` | Center | South
|        | `lnk_cross_south_to_center_512_7_ingr_wr_req_resp_to_lnk_cross_south_to_center_512_7_egr_wr_req_resp` | Center | South
|        | `lnk_cross_south_to_center_512_9_egr_rd_req_to_lnk_cross_south_to_center_512_9_ingr_rd_req`           | South  | Center
|        | `lnk_cross_center_to_south_512_2_ingr_rd_req_resp_to_lnk_cross_center_to_south_512_2_egr_rd_req_resp` | South  | Center
|        | `lnk_cross_south_to_center_512_0_egr_rd_req_to_lnk_cross_south_to_center_512_0_ingr_rd_req`           | South  | Center
|        | `lnk_cross_south_to_center_512_3_egr_rd_req_to_lnk_cross_south_to_center_512_3_ingr_rd_req`           | South  | Center
|        | `lnk_cross_south_to_center_512_8_egr_rd_req_to_lnk_cross_south_to_center_512_8_ingr_rd_req`           | South  | Center
|        | `lnk_cross_center_to_south_512_2_egr_rd_req_to_lnk_cross_center_to_south_512_2_ingr_rd_req`           | South  | Center
|        | `lnk_cross_center_to_south_512_4_ingr_rd_req_resp_to_lnk_cross_center_to_south_512_4_egr_rd_req_resp` | South  | Center
|        | `lnk_cross_south_to_center_512_2_ingr_wr_req_resp_to_lnk_cross_south_to_center_512_2_egr_wr_req_resp` | Center | South
|        | `lnk_cross_south_to_center_512_1_ingr_wr_req_resp_to_lnk_cross_south_to_center_512_1_egr_wr_req_resp` | Center | South
|        | `lnk_cross_south_to_center_512_6_ingr_wr_req_resp_to_lnk_cross_south_to_center_512_6_egr_wr_req_resp` | Center | South
|        | `lnk_cross_south_to_center_512_5_ingr_wr_req_resp_to_lnk_cross_south_to_center_512_5_egr_wr_req_resp` | Center | South
|        | `lnk_cross_center_to_south_64_egr_req_to_lnk_cross_center_to_south_64_ingr_req`                       | Center | South
|        | `lnk_cross_center_to_south_64_ingr_req_resp_to_lnk_cross_center_to_south_64_egr_req_resp`             | South  | Center
|        | `lnk_cross_center_to_south_512_4_egr_rd_req_to_lnk_cross_center_to_south_512_4_ingr_rd_req`           | Center | South
|        | `lnk_cross_south_to_center_512_8_ingr_rd_req_resp_to_lnk_cross_south_to_center_512_8_egr_rd_req_resp` | Center | South
|        | `lnk_cross_south_to_center_512_9_ingr_rd_req_resp_to_lnk_cross_south_to_center_512_9_egr_rd_req_resp` | Center | South
|        | `lnk_cross_south_to_center_512_0_ingr_rd_req_resp_to_lnk_cross_south_to_center_512_0_egr_rd_req_resp` | Center | South
|        | `lnk_cross_south_to_center_512_3_ingr_rd_req_resp_to_lnk_cross_south_to_center_512_3_egr_rd_req_resp` | Center | South
|        | `lnk_cross_south_to_center_64_egr_req_to_lnk_cross_south_to_center_64_ingr_req`                       | South  | Center
|        | `lnk_cross_south_to_center_64_ingr_req_resp_to_lnk_cross_south_to_center_64_egr_req_resp`             | Center | South
|        | `lnk_cross_center_to_south_512_1_ingr_wr_req_resp_to_lnk_cross_center_to_south_512_1_egr_wr_req_resp` | South  | Center
|        | `lnk_cross_center_to_south_512_1_egr_wr_req_to_lnk_cross_center_to_south_512_1_ingr_wr_req`           | Center | South
|        | `lnk_cross_center_to_south_512_0_egr_wr_req_to_lnk_cross_center_to_south_512_0_ingr_wr_req`           | Center | South
|        | `lnk_cross_south_to_center_512_b_egr_rd_req_to_lnk_cross_south_to_center_512_b_ingr_rd_req`           | South  | Center
|        | `lnk_cross_south_to_center_512_4_egr_rd_req_to_lnk_cross_south_to_center_512_4_ingr_rd_req`           | South  | Center
|        | `lnk_cross_south_to_center_512_5_egr_wr_req_to_lnk_cross_south_to_center_512_5_ingr_wr_req`           | South  | Center
|        | `lnk_cross_south_to_center_512_6_egr_wr_req_to_lnk_cross_south_to_center_512_6_ingr_wr_req`           | South  | Center
|        | `lnk_cross_south_to_center_512_1_egr_wr_req_to_lnk_cross_south_to_center_512_1_ingr_wr_req`           | South  | Center
|        | `lnk_cross_south_to_center_512_2_egr_wr_req_to_lnk_cross_south_to_center_512_2_ingr_wr_req`           | South  | Center
|        | `lnk_cross_south_to_center_512_a_egr_wr_req_to_lnk_cross_south_to_center_512_a_ingr_wr_req`           | South  | Center
|        | `lnk_cross_south_to_center_512_7_egr_wr_req_to_lnk_cross_south_to_center_512_7_ingr_wr_req`           | South  | Center
|        | `lnk_cross_south_to_center_512_a_ingr_wr_req_resp_to_lnk_cross_south_to_center_512_a_egr_wr_req_resp` | Center | South
|        | `lnk_cross_center_to_south_512_0_ingr_wr_req_resp_to_lnk_cross_center_to_south_512_0_egr_wr_req_resp` | South  | Center
|        | `lnk_cross_center_to_south_512_5_egr_wr_req_to_lnk_cross_center_to_south_512_5_ingr_wr_req`           | Center | South
|        | `lnk_cross_center_to_south_512_7_egr_rd_req_to_lnk_cross_center_to_south_512_7_ingr_rd_req`           | Center | South
|        | `lnk_cross_center_to_south_512_6_egr_rd_req_to_lnk_cross_center_to_south_512_6_ingr_rd_req`           | Center | South
|        | `lnk_cross_center_to_south_512_6_ingr_rd_req_resp_to_lnk_cross_center_to_south_512_6_egr_rd_req_resp` | South  | Center
|        | `lnk_cross_center_to_south_512_5_ingr_wr_req_resp_to_lnk_cross_center_to_south_512_5_egr_wr_req_resp` | South  | Center
|        | `lnk_cross_center_to_south_512_7_ingr_rd_req_resp_to_lnk_cross_center_to_south_512_7_egr_rd_req_resp` | South  | Center
|        | `lnk_cross_center_to_south_512_3_egr_wr_req_to_lnk_cross_center_to_south_512_3_ingr_wr_req`           | Center | South
| Right  | `lnk_cross_center_to_south_512_3_ingr_wr_req_resp_to_lnk_cross_center_to_south_512_3_egr_wr_req_resp` | South  | Center



## Center <--> East

| Placed | Pin Bundle                                                                                               | TX      | RX
|--------|----------------------------------------------------------------------------------------------------------|---------|----------
| Top    | `lnk_cross_center_to_east_512_0_ingr_wr_req_resp_to_lnk_cross_center_to_east_512_0_egr_wr_req_resp_data` | East    | Center
|        | `lnk_cross_center_to_east_512_0_egr_wr_req_to_lnk_cross_center_to_east_512_0_ingr_wr_req_data`           | Center  | East
|        | `lnk_cross_center_to_east_512_1_egr_wr_req_to_lnk_cross_center_to_east_512_1_ingr_wr_req_data`           | Center  | East
|        | `lnk_cross_center_to_east_512_1_ingr_wr_req_resp_to_lnk_cross_center_to_east_512_1_egr_wr_req_resp_data` | East    | Center
|        | `lnk_cross_center_to_east_512_2_ingr_rd_req_resp_to_lnk_cross_center_to_east_512_2_egr_rd_req_resp_data` | East    | Center
|        | `lnk_cross_center_to_east_512_2_egr_rd_req_to_lnk_cross_center_to_east_512_2_ingr_rd_req_data`           | Center  | East
|        | `lnk_cross_center_to_east_512_3_ingr_rd_req_resp_to_lnk_cross_center_to_east_512_3_egr_rd_req_resp_data` | East    | Center
|        | `lnk_cross_center_to_east_512_3_egr_rd_req_to_lnk_cross_center_to_east_512_3_ingr_rd_req_data`           | Center  | East
|        | `lnk_cross_east_to_center_512_0_egr_wr_req_to_lnk_cross_east_to_center_512_0_ingr_wr_req_data`           | East    | Center
|        | `lnk_cross_east_to_center_512_0_ingr_wr_req_resp_to_lnk_cross_east_to_center_512_0_egr_wr_req_resp_data` | Center  | East
|        | `lnk_cross_east_to_center_512_1_egr_rd_req_to_lnk_cross_east_to_center_512_1_ingr_rd_req_data`           | East    | Center
|        | `lnk_cross_east_to_center_512_1_ingr_rd_req_resp_to_lnk_cross_east_to_center_512_1_egr_rd_req_resp_data` | Center  | East
|        | `lnk_cross_center_to_east_64_ingr_req_resp_to_lnk_cross_center_to_east_64_egr_req_resp_data`             | East    | Center
|        | `lnk_cross_center_to_east_64_egr_req_to_lnk_cross_center_to_east_64_ingr_req_data`                       | Center  | East
|        | `lnk_cross_east_to_center_64_ingr_req_resp_to_lnk_cross_east_to_center_64_egr_req_resp_data`             | Center  | East
| Bottom | `lnk_cross_east_to_center_64_egr_req_to_lnk_cross_east_to_center_64_ingr_req_data`                       | East    | Center

## East <--> SoC

| Placed | Pin Bundle                                                                                    | TX      | RX
|--------|-----------------------------------------------------------------------------------------------|---------|----------
| Top    | `lnk_cross_east_to_soc_512_0_ingr_wr_req_resp_to_lnk_cross_east_to_soc_512_0_egr_wr_req_resp` | SoC     | East
|        | `lnk_cross_east_to_soc_512_0_egr_wr_req_to_lnk_cross_east_to_soc_512_0_ingr_wr_req`           | East    | SoC
|        | `lnk_cross_east_to_soc_512_1_ingr_wr_req_resp_to_lnk_cross_east_to_soc_512_1_egr_wr_req_resp` | SoC     | East
|        | `lnk_cross_east_to_soc_512_1_egr_wr_req_to_lnk_cross_east_to_soc_512_1_ingr_wr_req`           | East    | SoC
|        | `lnk_cross_east_to_soc_512_2_ingr_rd_req_resp_to_lnk_cross_east_to_soc_512_2_egr_rd_req_resp` | SoC     | East
|        | `lnk_cross_east_to_soc_512_2_egr_rd_req_to_lnk_cross_east_to_soc_512_2_ingr_rd_req`           | East    | SoC
|        | `lnk_cross_east_to_soc_512_3_ingr_rd_req_resp_to_lnk_cross_east_to_soc_512_3_egr_rd_req_resp` | SoC     | East
|        | `lnk_cross_east_to_soc_512_3_egr_rd_req_to_lnk_cross_east_to_soc_512_3_ingr_rd_req`           | East    | SoC
|        | `lnk_cross_soc_to_east_512_0_egr_wr_req_to_lnk_cross_soc_to_east_512_0_ingr_wr_req`           | SoC     | East
|        | `lnk_cross_soc_to_east_512_0_ingr_wr_req_resp_to_lnk_cross_soc_to_east_512_0_egr_wr_req_resp` | East    | SoC
|        | `lnk_cross_soc_to_east_512_1_ingr_rd_req_resp_to_lnk_cross_soc_to_east_512_1_egr_rd_req_resp` | East    | SoC
| Bottom | `lnk_cross_east_to_soc_64_ingr_req_resp_to_lnk_cross_east_to_soc_64_egr_req_resp`             | SoC     | East



## SoC <--> DDR-East

| Placed | Pin Bundle                                                                                 | TX        | RX
|--------|--------------------------------------------------------------------------------------------|-----------|----------
| Top    | `lnk_cross_soc_to_ddr_e_256_3_ingr_req_resp_to_lnk_cross_soc_to_ddr_e_256_3_egr_req_resp`  | DDR-East  | East
|        | `lnk_cross_soc_to_ddr_e_256_3_egr_req_to_lnk_cross_soc_to_ddr_e_256_3_ingr_req`            | East      | DDR-East
|        | `lnk_cross_soc_to_ddr_e_256_2_ingr_req_resp_to_lnk_cross_soc_to_ddr_e_256_2_egr_req_resp`  | DDR-East  | East
|        | `lnk_cross_soc_to_ddr_e_256_2_egr_req_to_lnk_cross_soc_to_ddr_e_256_2_ingr_req`            | East      | DDR-East
|        | `lnk_cross_soc_to_ddr_e_64_ingr_req_resp_to_lnk_cross_soc_to_ddr_e_64_egr_req_resp`        | DDR-East  | East
|        | `lnk_cross_soc_to_ddr_e_64_egr_req_to_lnk_cross_soc_to_ddr_e_64_ingr_req`                  | East      | DDR-East
|        | `lnk_cross_soc_to_ddr_e_256_1_ingr_req_resp_to_lnk_cross_soc_to_ddr_e_256_1_egr_req_resp`  | DDR-East  | East
|        | `lnk_cross_soc_to_ddr_e_256_1_egr_req_to_lnk_cross_soc_to_ddr_e_256_1_ingr_req`            | East      | DDR-East
|        | `lnk_cross_soc_to_ddr_e_256_0_ingr_req_resp_to_lnk_cross_soc_to_ddr_e_256_0_egr_req_resp`  | DDR-East  | East
|        | `lnk_cross_soc_to_ddr_e_256_0_egr_req_to_lnk_cross_soc_to_ddr_e_256_0_ingr_req`            | East      | DDR-East
|        | `lnk_cross_soc_periph_to_soc_64_egr_to_lnk_cross_soc_periph_to_soc_64_ingr_req`            | DDR-East  | East
| Bottom | `lnk_cross_soc_periph_to_soc_64_ingr_req_resp_to_lnk_cross_soc_periph_to_soc_64_egr_resp`  | East      | DDR-East
