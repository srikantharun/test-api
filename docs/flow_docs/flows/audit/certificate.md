# Cerification Flow
This document presents the steps to populate the structure required to run certification.

## Required tools

Load environment defaults:
```shell
source .env-default-modules
module load cookiecutter
```

## Generate the structure

Similarly to IP generation, a `cookiecutter` setup is available for generating the certification directory.

If you want to run at IP level:
```shell
cd hw/ip/<ip>/default
cookiecutter ../../../scripts/cookiecutter/certificate_directory
```

Or alternatively at block level:
```shell
cd hw/impl/europa/blocks/<blk>
cookiecutter ../../../../scripts/cookiecutter/certificate_directory
```

## Running the tool

```shell
cd certificate
make certificate.txt
```

This will run certification, by default at gold milstone.

There are 4 certification levels:

- skeleton
- bronze
- silver
- gold

To run at bronze level, add the milestone to the command as follows:

```shell
make certificate.txt MILESTONE=bronze
```

## Releases

This isn't available jsut yet(!) but when you're ready to release an IP or block at a milestone, this will run certification and copy logs, signoffs and certificate to the release area.

```shell
cd certificate
make release
```
