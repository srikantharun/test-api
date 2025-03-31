# Markdown Tricks

As we use for the documentation [Material for MkDocs](https://squidfunk.github.io/mkdocs-material/), we have access to a bunch of neat features to make the documentation prettier.

!!! tip "Material Features"

    [Have a look at the reference!](https://squidfunk.github.io/mkdocs-material/reference/)


## WaveDrom

[WaveDrom](https://wavedrom.com/) is a syntax which makes it possible to render waveforms.

As example the following signal definition:

```markdown
<script type="WaveDrom">
{ signal: [{ name: "Alfa", wave: "01.zx=ud.23.456789" }] }
</script>
```

Gives the rendered picture:

<script type="WaveDrom">
    { signal: [{ name: "Alfa", wave: "01.zx=ud.23.456789" }] }
</script>

It is also possible to specify [bit-fields](https://observablehq.com/collection/@drom/bitfield):

```markdown
<script type="WaveDrom">
{reg: [
        {bits: 7,  name: 'opcode',    attr: 'OP-IMM'},
        {bits: 5,  name: 'rd',        attr: 'dest'},
        {bits: 3,  name: 'func3',     attr: ['ADDI', 'SLTI', 'SLTIU', 'ANDI', 'ORI', 'XORI'], type: 4},
        {bits: 5,  name: 'rs1',       attr: 'src'},
        {bits: 12, name: 'imm[11:0]', attr: 'I-immediate[11:0]', type: 3}
    ],
    config: {
        hspace: 1200,
    }
}
</script>
```

<script type="WaveDrom">
{reg: [
        {bits: 7,  name: 'opcode',    attr: 'OP-IMM'},
        {bits: 5,  name: 'rd',        attr: 'dest'},
        {bits: 3,  name: 'func3',     attr: ['ADDI', 'SLTI', 'SLTIU', 'ANDI', 'ORI', 'XORI'], type: 4},
        {bits: 5,  name: 'rs1',       attr: 'src'},
        {bits: 12, name: 'imm[11:0]', attr: 'I-immediate[11:0]', type: 3}
    ],
    config: {
        hspace: 1200,
    }
}
</script>


## Math Equations

We also support [Mathjax](https://squidfunk.github.io/mkdocs-material/reference/math/) which makes it possible to render equations.

```markdown
$$x = {-b \pm \sqrt{b^2-4ac} \over 2a}.$$
```

$$x = {-b \pm \sqrt{b^2-4ac} \over 2a}.$$


## Local Defined Macros

We also have the ability to define [local macros]({{link_repo_file("scripts/mkdocs-macros-local/axelera/miraculix_plugins/europa_docs_api")}}) which will expand dunring rendering to add additional functionality to the documentation. There we use the [miraculix](https://git.axelera.ai/tools/py/miraculix/miraculix-lib) utility which is
a wrapper around [jinja2](https://jinja.palletsprojects.com/en/stable/). In essence with the local defined macros it
is possible to also write jinja enabled documentation which then can be dynamically expandet.

For example we can directly link to a file in the Europa Repository by `link_repo_file("path/from/repo_root/to/file")` and surround the expression with doubble `{` and `}`.
