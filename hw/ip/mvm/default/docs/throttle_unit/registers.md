---
title: MVM Throttle unit registers
doc:
  status: draft
  version: [0, 0, 0]
  confidentiality: internal
rtl:
  registers:
    ai_core_csr: subip/ai_core/subip/ai_core_csr/data/ai_core_csr.hjson
---

# Throttle unit registers

## Register descriptions

These are the `ai_core_csr` registers that directly control the `mvm_throttle_unit`:

<!--
%% field_table( "ai_core_csr", ["MVM_THROTTLE_UNIT_CFG", "MVM_THROTTLE_SIGNAL_CFG", "MVM_THROTTLE_SW_CTRL", "MONITOR_MIN_MAX_VALUE"]) %%
-->

## Related registers

These registers indirectly affect the `mvm_throttle_unit` by controlling the voltage monitor and MVM utilization limiter:
<!--
%% field_table( "ai_core_csr", ["MVM_VOLT_MONITOR_CFG", "MVM_AVG_UTIL_CFG"]) %%
-->
