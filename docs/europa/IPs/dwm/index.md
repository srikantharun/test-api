---
title: DWM - Dynamic Workload Management
doc:
  status: draft
  version: [0, 0, 0]
  confidentiality: internal
---

This is the library of all IPs used for the `Dynamic Workload Management - DWM`.

## Basic DWM units

| Name                            | Module                                                              | Description                                                                    |
|:------------------------------- |:------------------------------------------------------------------- |:------------------------------------------------------------------------------ |
| `Observation Reader`            | [dwm_observatio_reader](dwm_observation_reader.md)                  | Generate throttle indication based on the observation of the input data stream |
| `Boost Requester`               | [dwm_boost_requester](dwm_boost_requester.md)                       | Generate boost request and manage the utilisation limit                        |
| `Throttle Control Unit`         | [dwm_throttle_ctrl_unit](dwm_throttle_ctrl_unit.md)                 | Control the throttle behavior                                                  |
| `Dynamic Throttle Control Unit` | [dwm_dynamic_throttle_ctrl_unit](dwm_dynamic_throttle_ctrl_unit.md) | Combines multiple throttle units                                               |
