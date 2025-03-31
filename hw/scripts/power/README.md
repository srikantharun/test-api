### User Guide for Ungated Flip-Flops Report Script

---

## Overview
This script analyzes synthesis reports to identify **ungated flip-flops** in a design block, filtering results based on a user-defined threshold. Filtered data is logged and saved to a report file.

---

## Prerequisites
1. **PrimeTime (pt_shell)**: Ensure `pt_shell` is installed and available.
2. **Script Directory**: Include `pt_clock_savings_rep.tcl` in the script directory.
3. **Report Path**:
   ```
   /path/to/europa/hw/impl/europa/blocks/<block_name>/pt_reports/
   ```

---

## Usage

### Command Syntax
```bash
./gen_clock_savings_report.py [OPTIONS]
```

### Command-Line Arguments

| Argument                | Description                                           | Default Value      |
|-------------------------|-------------------------------------------------------|--------------------|
| `-v`, `--verbose`       | Enable detailed logging.                              | `False`            |
| `-b`, `--block`         | Specify block name for analysis.                      | `'aic_did'`        |
| `-n`, `--netlist`       | Specify the location of the netlist                   |                    |
| `-d`, `--dry_run`       | Simulate execution without running commands.          | `False`            |
| `-t`, `--threshold`     | Minimum count for flip-flops to be reported.          | `2`                |
| `-s`, `--spef_condition`| SPEF condition for analysis (e.g., `'rcworst_125c'`). | `'rcworst_125c'`   |
| `--dft`                 | Enable Design for Test mode.                          | `False`            |

---

## Output

1. **Console Logs**:
   - Example:
     ```
     INFO: Writing report to /path/to/block/pt_reports/ungated_flops.block_1.rpt
     ```

2. **Generated Report**:
   - Location: `<block_directory>/pt_reports/`
   - File Name: `ungated_flops.<block_identifier>.rpt`
   - Example Content:
     ```
     Ungated flip-flops (threshold: 2):
      - flop_1: 3 bits
      - flop_2: 5 bits
     ```

---

## Examples

- **Basic Execution**:
  ```bash
  ./gen_clock_savings_report.py
  ```

- **Verbose Mode**:
  ```bash
  ./gen_clock_savings_report.py -v
  ```

- **Specify Block**:
  ```bash
  ./gen_clock_savings_report.py -b my_block -n netlist_path
  ```

- **Latest Netlist**:
  ```bash
  ./gen_clock_savings_report.py -b my_block
  ```
If no netlist is provided, the script will search for the latest netlist in /data.

- **Dry Run**:
  ```bash
  ./gen_clock_savings_report.py -d
  ```

- **Custom Threshold**:
  ```bash
  ./gen_clock_savings_report.py -t 3
  ```

---

## Error Handling

- **Missing Reports**:
  ```
  ERROR: No report files found in <block_directory>/pt_reports/
  ```
- **File Access Issues**:
  ```
  ERROR: Unable to open <filename>, skipping. Error: <error_message>
  ```
