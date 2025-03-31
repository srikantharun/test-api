# IP

This is the directory to keep IP that has been developed in house. An IP directory should follow the following structure:

```
<ip_name>/default/                                     (Name of the IP ( & variant))
├── docs/                                              (directory for mkdocs)
├── dv/                                                (Ip specific design verification modules and testbenches)
│   ├── sim/
│   └──
├── lint/                                              (Linting jobs)
│   ├── Makefile -> hw/scripts/flow_makefiles/lint.mk  (Entry points for common flows)
│   └── lint_config.mk                                 (Default flow configuration for lint)
│
└── rtl/                           (Synthesizable Sources)
    ├── include/<ip_name>/         (Concrete External IP)
    │           └── defines.svh    (This should be used like: `ìnclude"<ip_name>/defines.svh"`)
    ├── pkg/                       (Concrete External IP)
    │   ├── ip_pkg.sv              (Packages for this IP)
    │   └── Bender.yml             (Separate Bender manifest for IP packages (no target))
    ├── ip_0.sv                    (IP source file)
    ├── ip_1.sv                    (IP source file)
    └── Bender.yml                 (RTL sources for this IP, plus eventual added include)
```
