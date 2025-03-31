
# Europa Specification

## Asic Specs

  [Europa Asic](asic/index.md)

## Example Block

This containt the following IP:

| IP Name | Block Spec Link                                   |
| ------- | ------------------------------------------------- |
| Example | [Example Functional Spec](block_spec_template.md) |


## Block Specs

| IP Name    | Block Spec Link                                                          |
| ---------- | ------------------------------------------------------------------------ |
| DCD        | [CODEC Subsystem Spec](blocks/dcd/index.md)                              |
| L2         | [L2 Functional Spec](blocks/l2/l2_block_spec.md)                         |
| SOC_MGMT   | [SOC_MGMT Functional Spec](blocks/soc_mgmt/soc_mgmt_block_spec.md)       |
| SOC_PERIPH | [SOC_PERIPH Functional Spec](blocks/soc_periph/soc_periph_block_spec.md) |


## Architectural Requirements

| Requirement ID        | Criticality | Owner | Description |
|-----------------------|-------------|-------|-------------|
{% for requirement in load_data('docs/europa_architecture/architectural_requirements.yaml').requirements -%}
{% set prefix = requirement.get('prefix', '') -%}
{% set optional_description = requirement.get('optional_description', '') -%}
{% set id = (prefix ~ "_" if prefix else "") ~ requirement.block ~ "_" ~ requirement.category ~ "_" ~ (optional_description ~ "_" if optional_description else "") ~ requirement.index -%}
{% set criticality_color = {
    'gold': '#D4AF37',
    'silver': '#c0c0c0',
    'bronze': '#cd7f32'
} -%}
{% set criticality_style = '<span style="color: ' + criticality_color[requirement.criticality] + '">' + requirement.criticality + '</span>' if requirement.criticality in criticality_color else requirement.criticality -%}
| {{ id }} | {{ criticality_style }} | {{ requirement.owner }} | {{ requirement.description }} |
{% endfor %}
