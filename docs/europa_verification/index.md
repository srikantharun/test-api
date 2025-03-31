# Europa Verification

This documentation aims to be the first point of reference for all things verification for the Europa project.

## Planning

2 styles of planning are used for the Europa verification project:

| Plan | Description | Link |
| ---- | ----------- | ---- |
| Top-Down | excel spreadsheet owned by @andrew.bond. This plan is generated with a month granularity based on high-level dependencies and estimates pre-final architecture.| [Top Down Plan](https://axeleraai.sharepoint.com/::x::/r/sites/AXELERAAI-ResearchandDevelopment/Gedeelde%20documenten/Research%20and%20Development/hw/projects/europa/verification/planning/Europa%20Verif%20Plan.xlsx?d=w42c7decdaba64a8097d2ad14d2e84189&csf=1&web=1&e=OQfC7O) |
| Bottom-Up | gitLab projects updated by individual owners. This plan is generated with a week granularity based on known work-packages based on knwon specifications. | [Bottom Up Plan](https://git.axelera.ai/ai-dv-team/dv-europa-planning) |

Both plans are living documents and will be updated regularily throughout the project.

The bottom up plans are also used for tracking progress. A report will be generated weekly and is available [here](https://git.axelera.ai/ai-dv-team/dv-europa-planning/reports/-/blob/main/report.md?ref_type=heads).

## Owners

Each verification work-package has a dedicated owner. Where additional resource is required multiple people will be assigned to a project. However, a single owner is still responsible for the overall project.

These owners are part of the defined working groups. Details of which can be found [here](https://axeleraai-my.sharepoint.com/:x:/g/personal/jonathan_ferguson_axelera_ai/EW4vctIZVrZGjvLqKaYzYskBB8NiyfiwEXEeB8mNXmrc-A?e=Dca1vy&wdLOR=cF583FD92-4A29-0548-A6DC-34536EB4993A).

## Workpackages

All verification work-packages must be documented following [this template](./work_package_template.md).

As documents are produced they must be added to the following table.

| Workpackage | Link |
| ----------- | ---- |
| Security Verification Plan   | [Security Verification plan](security_verif_plan.md) |
| Example     | [Verification Template](work_package_template.md) |

# New Joiners

When new team member joins the team it is their responsibility to update the [new joiners guide](./new_joiners_guide.md).

# Directory Structure and Simulation Flow

- The Europa [verification directory structure](dv_directory_structure.md) is documented. The purpose of this is to allow the team to be consistent without being overly strict.
- When writing RTL, although DV doesn't have a requirement to be as strict with coding style as the design team, it is highly recommmended that the [RTL coding guide](../flow_docs/guides/europa_rtl_style_guide.md) is followed.
- All simulation environments should be configured in the same way and unless **absolutely necessary** support both Questa and VCS. Documentation can be found [here](../flow_docs/flows/simulation.md).

# Useful Common Simulation packages
- [axe_csv](./axe_csv.md) Useful CSV generation and analysis tools from simulation

# Frequently Asked Questions

| Question | Answer |
| -------- | ------ |
| Who is working on my block? | Refer to the [workgroups](https://axeleraai-my.sharepoint.com/:x:/g/personal/jonathan_ferguson_axelera_ai/EW4vctIZVrZGjvLqKaYzYskBB8NiyfiwEXEeB8mNXmrc-A?e=Dca1vy&wdLOR=cF583FD92-4A29-0548-A6DC-34536EB4993A). Or contact @andrew.bond |
| How do a run the testbench? | Please refer to the "Compile" and "Run" sections of the [simulation guide](../flow_docs/flows/simulation.md) |
| What is UVM? | [wikipedia](https://en.wikipedia.org/wiki/Universal_Verification_Methodology) |
| Which simulators do we support? | [Questa](https://eda.sw.siemens.com/en-US/ic/questa/simulation/advanced-simulator/) and [VCS](https://www.synopsys.com/verification/simulation/vcs.html) (all testbenches should run on both) |
| Which emulator do we support? | [Veloce](https://eda.sw.siemens.com/en-US/ic/veloce/) ask @antoine.madec for details) |
| What are the stages of a verification project? | Bronze, Silver, Gold. The details are defined in the issues for each [project](https://git.axelera.ai/ai-dv-team/dv-europa-planning) |


