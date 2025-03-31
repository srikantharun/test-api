# Europa

This repository features most of the sources for the `EUROPA` architecture. `EUROPA` is an evolution of the
[`TRITON`](https://git.axelera.ai/ai-hw-team/triton) architecture.

[Europa documentation server](https://doc.axelera.ai/prod/europa/) has how-to documents, architecture, microarchitecture and verification plans.

## Description

> TODO: Add a fitting description and link to documentation

## Environment Setup

This repository relies on the [Environment Modules](https://modules.readthedocs.io/en/latest/) utility to switch
between certain programs / tools. It provides a unified way to manage a shell environment like `$PATH` and custom
environment variables.

**TL;DR**: To turn on the environment with the default set of modules:

```shell
# In the repository root:
source .env-default-modules
```

With the `module` command it is also possible to customize the environment. However the default modules are designed
to not clash with each other.

To get a list of available modules use:

```shell
# 'module' has a help and a manual page
module help
man module

# This will print the list of all available modules on the system
module avail

# Show information about what the command will set up in the shell environment
module show tool_name/version
```

To enable one of the modules use:

```shell
# To load a module if none is loaded
module load tool_name/version

# To load or switch between modules with the same name
module switch tool_name/version
```

And to return the shell to the previous state:

```shell
module purge
```


## License

>  (C) Copyright Axelera AI 2024
>  All Rights Reserved
>  *** Axelera AI Confidential ***
