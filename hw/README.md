# HARDWARE

This directory contains everything that is needed to build a hardware design. This includes all of the flow related
scripts and configurations. This directory setup is intended to support multiple chip tapeouts. For each concrete
IP, IMPL, and VENDOR the directory structure should follow the one described for an IP directory.

The structure of where to put source code is as follows:

```
hw/                       (Hardware sources)
├── impl/                 (Concrete Implementations / Chip Architectures)
│   └── europa/           (The Concrete Chip Europa)
│       ├── asic/         (Chip top-level and Testbench)
│       ├── fpga/         (FPGA top-level and Infrastructure)
│       └── blocks/       (Physical Partition Blocks)
│           ├── block_0/  (Concrete Block)
│           └── block_1/  (Concrete Block)
│
├── ip/                   (Internal developed IP)
│   ├── ip_0/             (Concrete Internal IP)
│   └── ip_1/             (Concrete Internal IP)
│
├── scripts/              (Common scripts / flows applicable for IP AND IPML)
│   ├── flow_makefiles/   (Entry points for common flows)
│   └── gen_script/       (Example where to put more complex scripts)
│
└── vendor/               (Integration fir external IP)
    ├── ip_0/             (Concrete External IP)
    └── ip_1/             (Concrete External IP)
```
