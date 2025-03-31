# Docstring Extraction from RTL

We have a system in place where we can automatically extract specially marked comments in RTL code and add them
to the documentation here.  We use for this a plugin for [mkdocstrings](https://mkdocstrings.github.io/) called
[mkdocstrings-systemverilog](https://git.axelera.ai/tools/py/dev/mkdocstrings-systemverilog).

It is currently possible to inject for the following constructs:

- module
- package
- class
- function
- typedef

!!! note "Syntax for Calling the Extraction"

    ```
    ::: relative-path-to-file{:systemverilog-namespace-path{:special-template}}
    ```

!!! note "Docstring in RTL"

    A Docstring in RTL for this extraction is marked via:

    ```verilog
    /// <my_docstring>
    ```


## Example from the Common Cell Library

The [common cell library (axe_ccl)](../../../documentation/ip/axe_ccl/index.md) has been set up to use the automatic extraction.
If we look at the sourcecode of [cc_stream_join]( {{link_repo_file("hw/ip/common_cell_library/default/rtl/cc_stream_join.sv") }}),
we see that the parameters and port comments start with `///`. This demotes for the extraction that there is a docstring
to be extracted. The docstrings can be placed in the line above the respective constructs to be extracted.
The resulting extracted documentation would look like [this](../../../documentation/ip/axe_ccl/stream/join.md).


So summarizing to be able to print the full rendered parameter and port table in the markdown file we can use:

```markdown
::: hw/ip/common_cell_library/default/rtl/cc_stream_join.sv:cc_stream_join
```


!!! tip

    It is possible to only render the list of parameters or ports seperately.
    For this extend the Syntax with the `special-template`:

    - `:parameter_table`
    - `:port_table`


## Examples of Docstrings

!!! tip "Adding a description to a `module`, `class` or `function`"

    ```verilog
    /// This module does awesome stuff.
    ///
    /// And can even be multi-line!
    ///
    module my_module;
    ```


!!! tip "Adding a description to a `parameter`"

    ```verilog
    /// All data flops in the module will be implemented without reset.
    parameter bit NoDataReset = 1'b1,
    ```


!!! tip "Adding a description to a `port`"

    ```verilog
    /// This port inidcates that something went wrong in my module!
    output logic o_error,
    ```
