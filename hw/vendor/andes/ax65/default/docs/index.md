---
title: Andes AX65
doc:
  status: draft
  version: [0, 0, 0]
  confidentiality: internal
---

Contains the RAM and DFT overrides, tech cell mapping and the Bender file.

Documentation regarding AX65 is provided at `/home/projects/andes/`.

# RAM override

Bind the sf5a macros instead of the generic ones provided by Andes.

# DFT override

As how the parameter propagation is done in Andes codebase, we have to ensure these files are kept in sync with the original file on new AX65 releases.

## Wrong syncs

Andes instantiated some non DFT friendly sync without a `test_mode` input, these files contain the override using `axe_ccl_rst_n_sync`.
The override is located between a `//// AXELERA OVERRIDE START` and `//// AXELERA OVERRIDE END` anchors.

## Routing of test_mode

The routing of the `test_mode` is also done though the Andes hierarchy (saving the DFT team to do it at insertion).
`test_mode` is simply broadcasted to all modules.
These IO changes are located between a `//// AXELERA OVERRIDE START` and `//// AXELERA OVERRIDE END` anchors.


# Tech cell mapping

Make sure to use our standard cells for PD.
