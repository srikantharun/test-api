# --------------------------------------------------------------------------------------------------
# (C) Copyright 2024 Axelera AI B.V.
# All rights reserved.
# *** Axelera AI Confidential ***
# --------------------------------------------------------------------------------------------------

"""Describe a module port
"""

# --------------------------------------------------------------------------------------------------
# Imports
# --------------------------------------------------------------------------------------------------

import logging
import dataclasses

import jinja2

import impl

# --------------------------------------------------------------------------------------------------
# Exports
# --------------------------------------------------------------------------------------------------

__all__ = [
    "Port",
    "PortGroup",
]

# --------------------------------------------------------------------------------------------------
# Module Variables
# --------------------------------------------------------------------------------------------------

_logger = logging.getLogger(__name__)

# --------------------------------------------------------------------------------------------------
# Implementation
# --------------------------------------------------------------------------------------------------

@dataclasses.dataclass(kw_only=True)
class Port:
    name: str
    direction: impl.DirectionEnum
    signal_type: str = "logic"
    is_duplicate: bool = False

    def __post_init__(self) -> None:
        if "'" in self.name:
            raise ValueError

    def __eq__(self, other) -> bool:
        if isinstance(other, Port):
            return self.name == other.name and self.direction == other.direction and self.signal_type == other.signal_type
        return False

    def __hash__(self) -> int:
        return hash((self.name, self.direction, self.signal_type))


@dataclasses.dataclass(kw_only=True)
class PortGroup:
    name: str
    ports: list[Port] = dataclasses.field(default_factory=list)
    direction: impl.DirectionEnum

    @property
    def render(self) -> str:
        template_string = """

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // {{ port_group.name }} ({{ port_group.direction.name }})
  //////////////////////////////////////////////////////////////////////////////////////////////////
  {%- set max_direction_length = port_group.ports|map(attribute='direction.value')|map('length')|max %}
  {%- set max_type_length = port_group.ports|map(attribute='signal_type')|map('length')|max %}
  {%- for port in port_group.ports %}
  {%- if port.is_duplicate %}
  /* Port already declared:
  {%- endif %}
  {{ ("%-"+max_direction_length|string+"s")|format(port.direction.value) }} {{ ("%-"+max_type_length|string+"s")|format(port.signal_type) }} {{ port.name }},
  {%- if port.is_duplicate %} */{% endif -%}
  {%- endfor %}
"""
        template = jinja2.Environment(loader=jinja2.BaseLoader).from_string(template_string)
        return template.render(port_group=self)

    def add_port(
        self,
        port: Port,
    ) -> "PortGroup":
        self.ports.append(port)
        _logger.debug("Added port %s to group %s", port.name, self.name)
        return self
