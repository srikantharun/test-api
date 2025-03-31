# Europa Verification Linker Script Generator

This Python-based script generates a linker script for the Europa verification process using a Jinja template and a YAML configuration. The generated linker script is saved in the `$REPO_ROOT/sw/src/lib/common` directory and can be customized by specifying AI cores (`aicores`) and PVEs (`pves`).

<br/>

## Files
1) **ld_generator.py**: The main script that generates the linker script using the verifsdk YAML and Jinja template.
2) **ld_generator_template.jinja**: The Jinja template that defines the structure of the linker script.
3) **verifsdk.yaml**: The YAML configuration file that specifies the processors (APU, AI cores, PVEs).

## Command-Line Options
- `-F` or `--file`: (Required) Path to the YAML file.
- `--aicores`: (Optional) Comma-separated list of AI core IDs to include in the linker script (e.g., 0,1,2).
- `--pves`: (Optional) Comma-separated list of PVE IDs to include in the linker script (e.g., 0,1).

## Usage

### Basic Usage
To generate the linker script from the verifsdk YAML, simply run:
```
$ ld_generator -F verifsdk.yaml
```

This will generate the linker script based on the contents of the verifsdk.yaml file and will create the file `link.ld` in the `$REPO_ROOT/sw/src/lib/common` directory.


### Customizing AI Cores and PVEs
You can specify which AI cores and PVEs to include in the generated linker script by using the `--aicores` and `--pves` flags. For example, to generate the linker script for AI cores 0 and 4 and PVE 0, use:
```
$ ld_generator -F verifsdk.yaml --aicores 0,4 --pves 0
```

## Output

The generated linker script will be saved in:
```
$REPO_ROOT/sw/src/lib/common/link.ld
```

## Script Details

### ld_generator.py
- Loads the YAML configuration from the file specified with the `-F` option.
- Parses the AI cores and PVEs using helper functions that generate lists from the processors section of the YAML configuration.
- If `--aicores` or `--pves` options are provided, it filters the corresponding list to include only the specified cores.
- Uses the Jinja template to generate the linker script, inserting the current time, AI cores, and PVEs into the template.
- Outputs the generated linker script to `$REPO_ROOT/sw/src/lib/common/link.ld`.

### ld_generator_template.jinja
This template defines the structure of the generated linker script. It uses the variables `aicores`, `pves`, and `current_time` to insert relevant sections based on the AI cores and PVEs provided.

The template contains placeholders such as:
- `aicores`: AI cores.
- `pves`: PVEs.
- `current_time`: The timestamp when the linker script was generated.
