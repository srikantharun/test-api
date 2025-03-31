---
title: AXE CSV
doc:
  status: draft
  version: [0, 0, 0]
  confidentiality: internal
---

# AXE CSV

## Introduction

AXE CSV is a simple set of utilities for working for generating csv files from SystemVerilog and analysing in Python.

## Generating CSVs

A systemverilog package is provided in the hw/dv/common directory.
- [$(REPO_ROOT)/hw/dv/common/rtl/axe_csv_pkg.sv](../../hw/dv/common/rtl/axe_csv_pkg.sv)

This provides the basic function to open, close and write to a csv file.

### Opening a File
To open a file you must provide:
- The Filename
- The header as a comma separated string of column names

e.g.
```
    initial begin
        automatic chandle h;
        h = open_csv("test_data.csv", "column1,column2,column3");
    end
```

The function returns a handle that is used to update the file in subsequent function calls.

The underlying DPI function takes care of re-using the filename. Should you attempt to open a file with an already used filename the library shared the file handle.

Each sim will override existing csv files. However, if it is closed and re-openned in a single simulation the file will be appended.

This is useful for creating a single csv updated from multiple sources.

It is the users responsibility to ensure the sources all share the same column definitions.

### Writing to a File
To write data you must provide:
- The handle returned by open_csv()
- A comma separated string of values for each column in the order they were defined when opening the file.

```
write_csv(h, '{$psprintf("%0d", i), "HELLO WORLD", $psprintf("%0.2f", (real'(i)/100.00))});
```

All arguments are strings, allowing the user to format the string in any way they wish.

### Closing a File
To close a file you must provide:
- The handle returned by open_csv()
- If null all open files are closed

```
    final close_csv(null);
```

It is recommended to call in a final statement to ensure all file handles are closed when the simulaton exits.

## Analyzing CSVs

A python package is provided in the hw/dv/common directory.
- [$(REPO_ROOT)/hw/dv/common/scripts/axe_csv/axe_csv.py](../../hw/dv/common/scripts/axe_csv/axe_csv.py)

This is wrapped in a venv
- [$(REPO_ROOT)/bin/axe_csv](../../bin/axe_csv)

This provides a class to read and analyse csv files.

The underlying analysis is done using [pandas](https://pandas.pydata.org/).

```
usage: axe_csv.py [-h] [--icsv ICSV] [--ocsv OCSV] [--otxt OTXT] [--verbose] [--nostdout] [--delimiter DELIMITER] [--sort SORT] [--query QUERY] [--width WIDTH] [--max_rows MAX_ROWS]

Analyze AXE CSV Files

options:
  -h, --help            show this help message and exit
  --icsv ICSV           Input global to find src csvs (default="*.csv")
  --ocsv OCSV           Output CSV file
  --otxt OTXT           Output TXT file
  --verbose             Verbose output
  --nostdout            Suppress standard output
  --delimiter DELIMITER
                        CSV delimiter (default:,)
  --sort SORT           Sort / order by
  --query QUERY         Query to apply to data
  --width WIDTH         Display width
  --max_rows MAX_ROWS   Maxium number of rows to display (default=all)

```

### Reading CSVs
Files are located by providing the [python glob](https://pynative.com/python-glob/) pattern on the commandline

e.g.
```
axe_csv --icsv="./build_vsim_aic_dp_cmd_gen/run_vsim_ai_core_dp_cmd_gen_m1n0_test_1/*.csv"
```

All files matching the pattern will be read and combined into a single dataframe containing a superset of all columns.

### Sorting
All numerical values are automatically converted to their native data type (int, float) from the string in the csv in order to allow sorting.

The data can be sorted using the --sort comamnd line option.

```
axe_csv --icsv="./build_vsim_aic_dp_cmd_gen/run_vsim_ai_core_dp_cmd_gen_m1n0_test_1/*.csv" --sort=time
```

### Queries
The data can be filtered using the --query comamnd line option.

The query syntax is standard in [pandas](https://pandas.pydata.org/docs/reference/api/pandas.DataFrame.query.html)

```
axe_csv --icsv="./build_vsim_aic_dp_cmd_gen/run_vsim_ai_core_dp_cmd_gen_m1n0_test_1/*.csv" --sort=time --query='(time>8000)&(time<8100)'
```

If no query is provided all data is returned.

### Output
The combined query can be outputs as
- CSV file (--ocsv)
- TXT file (--otxt)

By default the query response is displayed as text on standard out. This can be disabled using --nostdout.

e.g.
```
[abond@htz1-login06 sim-aic-dp-cmd-gen]$ axe_csv --icsv="./build_vsim_aic_dp_cmd_gen/run_vsim_ai_core_dp_cmd_gen_m1n0_test_1/*.csv" --sort=time --query='(time>8000)&(time<8100)'
         time port phase   awid     awaddr awburst awsize awcache awlen awprot awlock awqos rid rdata rresp rlast arid araddr arburst arsize arcache arlen arprot arlock arqos    bid bresp               wdata wstrb wlast
1001  8003.05    m    AW  0x15d  0x0001f48     0.0    3.0     1.0   0.0    2.0    1.0   0.0
1001  8004.71    m     W                                                                                                                                                                     0x00000000000003e9  0xff   1.0
1000  8004.71    m     B                                                                                                                                                        0x15d   0.0
1001  8011.38    m     B                                                                                                                                                        0x15d   0.0
1002  8015.54    m    AW  0x15d  0x0001f50     0.0    3.0     1.0   0.0    2.0    1.0   0.0
1002  8017.21    m     W                                                                                                                                                                     0x00000000000003ea  0xff   1.0
1002  8023.87    m     B                                                                                                                                                        0x15d   0.0
1003  8027.20    m    AW  0x15d  0x0001f58     0.0    3.0     1.0   0.0    2.0    1.0   0.0
1003  8028.87    m     W                                                                                                                                                                     0x00000000000003eb  0xff   1.0
1004  8036.37    m    AW  0x15d  0x0001f60     0.0    3.0     1.0   0.0    2.0    1.0   0.0
1004  8038.03    m     W                                                                                                                                                                     0x00000000000003ec  0xff   1.0
1003  8038.03    m     B                                                                                                                                                        0x15d   0.0
1004  8040.53    m     B                                                                                                                                                        0x15d   0.0
1005  8045.53    m    AW  0x15d  0x0001f68     0.0    3.0     1.0   0.0    2.0    1.0   0.0
1005  8047.20    m     W                                                                                                                                                                     0x00000000000003ed  0xff   1.0
1006  8048.86    m    AW  0x15d  0x0001f70     0.0    3.0     1.0   0.0    2.0    1.0   0.0
1005  8049.70    m     B                                                                                                                                                        0x15d   0.0
1006  8050.53    m     W                                                                                                                                                                     0x00000000000003ee  0xff   1.0
1006  8056.36    m     B                                                                                                                                                        0x15d   0.0
1007  8058.03    m    AW  0x15d  0x0001f78     0.0    3.0     1.0   0.0    2.0    1.0   0.0
1008  8058.86    m    AW  0x15d  0x0001f80     0.0    3.0     1.0   0.0    2.0    1.0   0.0
1007  8059.69    m     W                                                                                                                                                                     0x00000000000003ef  0xff   1.0
1008  8060.52    m     W                                                                                                                                                                     0x00000000000003f0  0xff   1.0
1009  8063.02    m    AW  0x15d  0x0001f88     0.0    3.0     1.0   0.0    2.0    1.0   0.0
1007  8063.02    m     B                                                                                                                                                        0x15d   0.0
1009  8064.69    m     W                                                                                                                                                                     0x00000000000003f1  0xff   1.0
1008  8072.19    m     B                                                                                                                                                        0x15d   0.0
1010  8075.52    m    AW  0x15d  0x0001f90     0.0    3.0     1.0   0.0    2.0    1.0   0.0
1009  8077.19    m     B                                                                                                                                                        0x15d   0.0
1010  8077.19    m     W                                                                                                                                                                     0x00000000000003f2  0xff   1.0
1011  8081.35    m    AW  0x15d  0x0001f98     0.0    3.0     1.0   0.0    2.0    1.0   0.0
1010  8082.18    m     B                                                                                                                                                        0x15d   0.0
1011  8083.02    m     W                                                                                                                                                                     0x00000000000003f3  0xff   1.0
1011  8087.18    m     B                                                                                                                                                        0x15d   0.0
1012  8088.01    m    AW  0x15d  0x0001fa0     0.0    3.0     1.0   0.0    2.0    1.0   0.0
1012  8089.68    m     W                                                                                                                                                                     0x00000000000003f4  0xff   1.0
1012  8096.34    m     B                                                                                                                                                        0x15d   0.0

```
