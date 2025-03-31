# Architectural Requirements 

Architectural requirements are part of the Architectural definition of a product.
The requirements are derived from the product specifications and aim to provide a concrete list of features that the product need to be able to support and their technical implications.

Documenting architectural requirements for the design is crucial because:
* it provides a clear blueprint that guides the development process
* ensures that all stakeholders have a common understanding of the goals and specifications
* it helps in identifying and addressing potential issues early in the design phase
* facilitates better communication among cross-functional teams
* supports the validation and verification process
* ensures that the final product meets the desired performance, functionality, and quality standards.


## Architectural requirements owner
The owner of the architectural requirements is always the architect of the specific block of the full chip.  
Architects need to provide the architectural requirements in the format described below as part of their Architecture specification documentation. 

## Architectural requirements consumer
The consumer of the requirements are:
* the block designer engineer: in order to implement the architecture into digital design. Designers use the Architectural requirements in conjunction with the rest of the documentation in order to derive efficient implementations of the Architecture. 
* the block verification engineer: in order to verify and validate the features of the architecture into the design. The verification plan and the verification testlist will need to be linked with the associated architectural requirements. 
* the top level verification engineer: in order to cover the full system features at a system level. The verification plan and the verification testlist will need to be linked with the associated architectural requirements. 
* SW team and other interested parties that need an understanding of the system and product requirements and functionality. 
* DFT engineers, package and board designers and any other stakeholders


## Architectural requirement format

* each BLOCK will have a dedicated architectural requirement YAML
* each yaml file will have the following fields:

```yaml
requirements:
  -
    block: L2 
    category: FEAT
    index: 3
    description: "The L2 subsystem memory shall have defined size of 128MiB."
    criticality: bronze
    owner: Spyridoula Koumousi
```

Additionally all TOP requirements receive an additional prefix `TOP` to indicate the top-level.

```yaml
requirements:
  -
    prefix: TOP
    block: L2 
    category: FEAT
    index: 3
    description: "The L2 subsystem memory shall have defined size of 128MiB."
    criticality: bronze
    owner: Spyridoula Koumousi
```

This allows us to reuse any test on the top level by appending the `TOP` prefix when the same feature needs to be validated in the block and top level.

Another example of top level requirement:

```yaml
requirements:
-
  prefix: TOP
  block: AICORE
  category: NET
  optional_description: YOLO
  index: 0
  description: "Run YOLO5s on the top level test bench."
  criticality: bronze
  owner: Gua Hao Khov 
```

## Agreed convention for the requirement naming 

### Block level

The requirement identification is composed by the following fields:

`<block_name>_<category>_<optional_description>_<index>`

**Block name from list:**
- AICORE
- APU
- PVE
- DECODER
- L2
- SYS_SPM
- SDMA
- SOC_MNGT
- SOC_PERIPH
- PCIE
- LPDDR 
- NOC
- ... 


**Category from list:**
| Category abbreviation | Meaning |
| --------------------- | ------ |
|  CONN                 | indicates a connectivity requirement       |
|  CLK                  | indicates a clocking requirement           |
|  RST                  | indicates a reset requirement              |
|  FEAT                 | indicates a requirement related to a specific block feature (ex interleaving mode in NOC)  |
|  BOOT                 | indicates a requirement related to the BOOT sequence  |
|  SEC                  | indicates a requirement related to security  |
|  MBIST                | indicates a requirement related to MBIST  |
|  DFT                  | indicates a requirement related to DFT ( scan, stuck-at etc)  |
|  PERF                 | indicates a requirement related to performance metrics  |
|  PWR                  | indicates a requirement related to power metrics  |
|  DBG                  | indicates a requirement related to debug functionality  |
|  NET                  | indicates a requirement related to a specific network (see YOLO etc). Please provide optional_description  |
|  APP                  | indicates a requirement related to a specific application (specific kernel  etc). Please provide optional_description  |
|  E2E                  | indicates a requirement related to E2E chip functionality - only used at TOP |

The above categories can be extended by any user as long as this has been communicated with the flow owners @antoine.madec and @spyridoula.koumousi and this table has been updated.

**Optional description:**

At the block level it will be possible to add more suffixes into the name to indicate a specific feature.

For example `AICORE_FEAT_THROTTLE_0` or `AICORE_FEAT_STRESS_0`: in this requirement the feature that checks the throttle functionality or a bus stress functionality is specified in the naming convention.
_It is not mandatory to have this description._


**Criticality description:**
| Criticality| Meaning  |
| --------------------- | ------ |
|  bronze               | indicates this requirement needs to be verified by bronze DV milestone       |
|  silver               | indicates this requirement needs to be verified by silver DV milestone       |
|  gold                 | indicates this requirement needs to be verified by gold DV milestone         |

The choice of the criticality should be done based on whether the requirement needs to be covered by a certain RTL/DV maturity level. 
There is no strict rule on how to choose the criticality-it should be reviewed as part of the verif plan and arch. requirements review.

### Top level

`TOP_<block_name>_<category>_<optional_description>_<index>` or 

`TOP_<category>_<optional_description>_<index>`


If a block requirement can be ported 1-2-1 or with small updates to the top level then it should keep the same naming convention by just adding the `TOP` prefix and updating the index to the right number at the top. 

Example: 

`AICORE_CLK_0` could potentially become `TOP_AICORE_CLK_5`
 * the index changes due to the fact that there might be already other requirements with `TOP_AICORE_CLK0-4` 

However the top level might have requirements that do not touch upon only one IP.
example `TOP_CLK_0`: could be a requirement that checks all the clock generation from the top level to all IPs.

_so if the requirement touches multiple IPs there is no need to add a block prefix._


## Requirements for an IP

All Axelera owned IPs need to have a dedicated architectural requirements document. This document will be located in the `/docs` folder of the IP but it will be linked
in the project documentation folder see relevant [paragraph](#location-of-the-requirements-list)


## Rules for requirement writing
- The blocks need to define requirements for all the functionality of the block (legacy and new)
- The block architect is responsible for delivering the requirement list in the proposed format by the verif team. 
- Once the requirement name has been given it cannot change as it will mess with the testlist linking
- The requirements should contain info on what the system `shall/should` be able to do and it should contain any conditions with the wording `unless/when`. The requirements should be short and concise.
- The resulting ID should be unique.

## Location of the requirements list
Block architects should write the requirements in a yaml file as above and place it in the 
arch documentation directory

example 
* block-level, e.g. PVE: `docs/europa_architecture/blocks/pve/architectural_requirements.yaml`
* top-level, (not sure): `docs/europa_architecture/architectural_requirements.yaml`
* ip level, e.g SPM: `hw/ip/spm/default/docs/architectural_requirements.yaml` and needs to be linked to `docs/europa/IPs/`folder.
