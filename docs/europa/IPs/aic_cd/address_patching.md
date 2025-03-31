---
title: "Address Patching"
doc:
  status: draft
  version: [0, 0, 0]
  confidentiality: internal
---


Address fields in the copied `commands` of AI-Core datapath blocks can be patched using the `patch_mode` and `patch_id_x`
fields of the Control Dispatcher [cmd instruction](./instructions.md#copy-instruction-cmd).  The fields act as a lookup
ID for configurations stored in the CSR. Below diagram depicts the mechanism.

![AIC_CD: Address Patching](./figures/aic_cd_address_patching.drawio.svg)

!!! note "Patch Mode Indexing"

    The patch mode IDs start from `1`! Hence `patch_mode == 0` disables the feature.

    In addition, it is required that the `word_index_0` is strictly smaller than `word_index_1` ensuring a strict
    ordering of patch application.  This also means that only one address per command payload word may be patched.


The address patching feature allows us to generate binaries which contain all the necessary control data for the
`AI-Core` datapath blocks without yet worrying about memory allocation.  Instead of storing the final address in the
address fields, an address offset relative to a memory pool is stored.  The memory pools can then be allocated during
runtime and their base addresses patched on top of the offsets within the Control Dispatcher.
