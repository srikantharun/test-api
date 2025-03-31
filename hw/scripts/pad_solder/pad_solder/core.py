# --------------------------------------------------------------------------------------------------
# (C) Copyright 2024 Axelera AI B.V.
# All rights reserved.
# *** Axelera AI Confidential ***
# --------------------------------------------------------------------------------------------------

"""Core utilities to transform a pad soldering configuration into a pad module.
"""

# --------------------------------------------------------------------------------------------------
# Imports
# --------------------------------------------------------------------------------------------------

import logging
import collections

import package_lib.exceptions

import pad
import port
import impl
import pad_config

# --------------------------------------------------------------------------------------------------
# Exports
# --------------------------------------------------------------------------------------------------

__all__ = [
    "pads_from_config",
    "extract_portgroups",
]

# --------------------------------------------------------------------------------------------------
# Module Variables
# --------------------------------------------------------------------------------------------------

_logger = logging.getLogger(__name__)

class CoreError(package_lib.exceptions.HandledException):
    """Errors Caused by functional Errors of the core logic."""

# --------------------------------------------------------------------------------------------------
# Implemenation
# --------------------------------------------------------------------------------------------------

def pads_from_config(
    config: pad_config.PadConfigModel
) -> list[pad.FunctionalPad]:
    """Extracts the pads from the configuration.

    TODO: Make this less coupled in the future
    """
    _logger.debug("Extracting pads from configuration")
    ret_list = list()

    for data in config.pads:
        if data.padtype in [impl.PadTypeEnum.OSCILLATOR_FAST, impl.PadTypeEnum.OSCILLATOR_SLOW]:
            ret_list.append(
                pad.OscillatorPad(
                    name=data.cell_name,
                    direction=impl.DirectionEnum(data.direction),
                    padtype=impl.PadTypeEnum(data.padtype),
                    orientation=impl.OrientationEnum(data.orientation),
                    core_signal_input=data.core_side_output,
                    core_signal_output_enable=data.output_enable,
                    core_signal_oe_active_low=data.oe_active_low,
                    core_signal_ie_active_low=data.ie_active_low,
                    core_signal_drive=data.drive_strength,
                    row_index=int(data.row_index),
                    dft=False,
                )
            )
        else:
            ret_list.append(
                pad.FunctionalPad(
                    name=data.cell_name,
                    direction=impl.DirectionEnum(data.direction),
                    padtype=impl.PadTypeEnum(data.padtype),
                    orientation=impl.OrientationEnum(data.orientation),
                    core_signal_output=data.core_side_input,
                    core_signal_output_enable=data.output_enable,
                    core_signal_oe_active_low=data.oe_active_low,
                    core_signal_ie_active_low=data.ie_active_low,
                    core_signal_input=data.core_side_output,
                    core_signal_input_enable=data.input_enable,
                    core_signal_pull_type=data.pull_type,
                    core_signal_pull_enable=data.pull_enable,
                    core_signal_drive=data.drive_strength,
                    core_signal_schmitt=data.schmitt_trigger,
                    row_index=int(data.row_index),
                    dft=data.dft_mux,
                )
            )
    _logger.debug("Functional: Extracted %d pads", len(ret_list))
    _logger.debug("Functional: Pads: %s", ret_list)

    return ret_list

def _get_bus_ports(
    pad_list: list[pad.FunctionalPad],
) -> dict[str, int]:
    """Retrieves the list of bus ports.
        Key is the name, value the data width.
    """
    ret = collections.defaultdict(int)
    for pad_instance in pad_list:
        if pad_instance.is_bus:
            ret[pad_instance.busname] += 1

    return dict(ret)


def _form_sideband_signal_type(
    signal_name: str,
    bus_width: int = 1
) -> str:
    """Return the signal type for a sideband signal

    This checks if a '[' character is present in the sidband signal
    then makes an unpacked array out of it of 'bus_width'.
    """

    signal_type = "logic"
    if "[" in signal_name and bus_width > 1:
        signal_type += f" [{bus_width-1}:0]"
    return signal_type


def _add_sidebands(
    pad_instance: pad.FunctionalPad,
    port_group: port.PortGroup,
    bus_width: int = 1,
) -> None:

        # Add the sidebands if needed:
    if "'" not in pad_instance.core_signal_pull_enable:
        port_group.add_port(
            port.Port(
                name=f"{pad_instance.core_signal_pull_enable.split('[')[0]}",
                direction=impl.DirectionEnum.INPUT,
                signal_type=_form_sideband_signal_type(
                    signal_name=pad_instance.core_signal_pull_enable,
                    bus_width=bus_width,
                ),
            )
        )
    if "'" not in pad_instance.core_signal_pull_type:
        port_group.add_port(
            port.Port(
                name=f"{pad_instance.core_signal_pull_type.split('[')[0]}",
                direction=impl.DirectionEnum.INPUT,
                signal_type=_form_sideband_signal_type(
                    signal_name=pad_instance.core_signal_pull_type,
                    bus_width=bus_width,
                ),
            )
        )
    if "'" not in pad_instance.core_signal_drive:
        drive_str = "logic"
        if pad_instance.padtype == impl.PadTypeEnum.FAST:
            drive_str = "logic [2:0]"
        if pad_instance.padtype == impl.PadTypeEnum.SLOW:
            drive_str = "logic [1:0]"

        port_group.add_port(
            port.Port(
                name=f"{pad_instance.core_signal_drive}",
                direction=impl.DirectionEnum.INPUT,
                signal_type=drive_str
            )
        )
    if "'" not in pad_instance.core_signal_schmitt:
        port_group.add_port(
            port.Port(
                name=f"{pad_instance.core_signal_schmitt.split('[')[0]}",
                direction=impl.DirectionEnum.INPUT,
                signal_type=_form_sideband_signal_type(
                    signal_name=pad_instance.core_signal_schmitt,
                    bus_width=bus_width,
                ),
            )
        )

def _add_dft_sidebands(
    pad_instance: pad.FunctionalPad,
    port_group: port.PortGroup,
) -> None:
    port_group.add_port(
        port.Port(
            name=f"{pad_instance.dft_signal_pull_type}",
            direction=impl.DirectionEnum.INPUT,
            signal_type="logic"
        )
    )
    port_group.add_port(
        port.Port(
            name=f"{pad_instance.dft_signal_pull_enable}",
            direction=impl.DirectionEnum.INPUT,
            signal_type="logic"
        )
    )
    port_group.add_port(
        port.Port(
            name=f"{pad_instance.dft_signal_schmitt}",
            direction=impl.DirectionEnum.INPUT,
            signal_type="logic"
        )
    )
    drive_str = "logic"
    if pad_instance.padtype == impl.PadTypeEnum.FAST:
        drive_str = "logic [2:0]"
    if pad_instance.padtype == impl.PadTypeEnum.SLOW:
        drive_str = "logic [1:0]"
    port_group.add_port(
        port.Port(
            name=f"{pad_instance.dft_signal_drive}",
            direction=impl.DirectionEnum.INPUT,
            signal_type=drive_str
        )
    )


def _create_oscillatorgroup(
    pad_instance: pad.OscillatorPad
) -> port.PortGroup:
    """Creates a group for an Oscillator pad
    """

    port_group = port.PortGroup(name=pad_instance.name, direction=pad_instance.direction)

    # Add the clock to the system
    port_group.add_port(
        port.Port(
            name=f"{pad_instance.core_signal_input}",
            direction=impl.DirectionEnum.OUTPUT,
            signal_type=f"logic"
        )
    )

    # Add the oscillator pad output enable
    if "'" not in pad_instance.core_signal_output_enable:
        port_group.add_port(
            port.Port(
                name=f"{pad_instance.core_signal_output_enable}",
                direction=impl.DirectionEnum.INPUT,
                signal_type="logic"
            )
        )

    # If a fast pad add the drive strength
    if "'" not in pad_instance.core_signal_drive:
        if (pad_instance.padtype is impl.PadTypeEnum.OSCILLATOR_FAST):
            port_group.add_port(
                port.Port(
                    name=f"{pad_instance.core_signal_drive}",
                    direction=impl.DirectionEnum.INPUT,
                    signal_type="logic [1:0]"
                )
            )

    # Add the pad wires
    port_group.add_port(
        port.Port(
            name=f"{pad_instance.pad_signal_oup}",
            direction=impl.DirectionEnum.OUTPUT,
            signal_type="wire"
        )
    )

    port_group.add_port(
        port.Port(
            name=f"{pad_instance.pad_signal_inp}",
            direction=impl.DirectionEnum.INPUT,
            signal_type="wire"
        )
    )

    port_group.add_port(
        port.Port(
            name=f"{pad_instance.pad_signal_inp}_bypass",
            direction=impl.DirectionEnum.INPUT,
            signal_type="wire"
        )
    )

    return port_group



def _create_busportgroup(
    pad_instance: pad.FunctionalPad,
    bus_width: int,
) -> port.PortGroup:
    """Creates a bus port.
    """
    port_group = port.PortGroup(name=pad_instance.busname, direction=pad_instance.direction)

    # Sanitize also the core side signals
    if pad_instance.direction in [impl.DirectionEnum.OUTPUT, impl.DirectionEnum.INOUT]:
        port_group.add_port(
            port.Port(
                name=f"{pad_instance.core_signal_output.split('[')[0]}",
                direction=impl.DirectionEnum.INPUT,
                signal_type=f"logic [{bus_width-1}:0]"
            )
        )
        if "'" not in pad_instance.core_signal_output_enable != "1'b0":
            port_group.add_port(
                port.Port(
                    name=f"{pad_instance.core_signal_output_enable.split('[')[0]}",
                    direction=impl.DirectionEnum.INPUT,
                    signal_type=f"logic [{bus_width-1}:0]"
                )
            )

    if pad_instance.direction in [impl.DirectionEnum.INPUT, impl.DirectionEnum.INOUT]:
        port_group.add_port(
            port.Port(
                name=f"{pad_instance.core_signal_input.split('[')[0]}",
                direction=impl.DirectionEnum.OUTPUT,
                signal_type=f"logic [{bus_width-1}:0]"
            )
        )
        if "'" not in pad_instance.core_signal_input_enable:
            port_group.add_port(
                port.Port(
                    name=f"{pad_instance.core_signal_input_enable.split('[')[0]}",
                    direction=impl.DirectionEnum.INPUT,
                    signal_type=f"logic [{bus_width-1}:0]"
                )
            )

    # Add the sidebands if needed:
    _add_sidebands(pad_instance, port_group, bus_width)

    # Add dft signals
    if pad_instance.dft:
        if pad_instance.direction in [impl.DirectionEnum.OUTPUT, impl.DirectionEnum.INOUT]:
            port_group.add_port(
                port.Port(
                    name=f"{pad_instance.dft_signal_output.split('[')[0]}",
                    direction=impl.DirectionEnum.INPUT,
                    signal_type=f"logic [{bus_width-1}:0]"
                )
            )
            port_group.add_port(
                port.Port(
                    name=f"{pad_instance.dft_signal_output_enable.split('[')[0]}",
                    direction=impl.DirectionEnum.INPUT,
                    signal_type=f"logic [{bus_width-1}:0]"
                )
            )

        if pad_instance.direction in [impl.DirectionEnum.INPUT, impl.DirectionEnum.INOUT]:
            port_group.add_port(
                port.Port(
                    name=f"{pad_instance.dft_signal_input.split('[')[0]}",
                    direction=impl.DirectionEnum.OUTPUT,
                    signal_type=f"logic [{bus_width-1}:0]"
                )
            )
            port_group.add_port(
                port.Port(
                    name=f"{pad_instance.dft_signal_input_enable.split('[')[0]}",
                    direction=impl.DirectionEnum.INPUT,
                    signal_type=f"logic [{bus_width-1}:0]"
                )
            )

        _add_dft_sidebands(pad_instance, port_group)

    # Add the pad wires:
    port_group.add_port(
        port.Port(
            name=f"{pad_instance.pad_signal.split('[')[0]}",
            direction=pad_instance.direction,
            signal_type=f"wire  [{bus_width-1}:0]"
        )
    )

    return port_group


def _create_portgroup(
    pad_instance: pad.FunctionalPad,
) -> port.PortGroup:
    """Creates a port group.
    """

    port_group = port.PortGroup(name=pad_instance.name, direction=pad_instance.direction)
    # Add the core side signals
    if pad_instance.direction in [impl.DirectionEnum.OUTPUT, impl.DirectionEnum.INOUT]:
        if "'" not in pad_instance.core_signal_output:
            port_group.add_port(
                port.Port(
                    name=f"{pad_instance.core_signal_output}",
                    direction=impl.DirectionEnum.INPUT,
                    signal_type=f"logic"
                )
            )
        if "'" not in pad_instance.core_signal_output_enable:
            port_group.add_port(
                port.Port(
                    name=f"{pad_instance.core_signal_output_enable}",
                    direction=impl.DirectionEnum.INPUT,
                    signal_type=f"logic"
                )
            )

    if pad_instance.direction in [impl.DirectionEnum.INPUT, impl.DirectionEnum.INOUT]:
        if ("'" not in pad_instance.core_signal_input) and (("/*" not in pad_instance.core_signal_input)):
            port_group.add_port(
                port.Port(
                    name=f"{pad_instance.core_signal_input}",
                    direction=impl.DirectionEnum.OUTPUT,
                    signal_type=f"logic"
                )
            )
        if "'" not in pad_instance.core_signal_input_enable:
            port_group.add_port(
                port.Port(
                    name=f"{pad_instance.core_signal_input_enable}",
                    direction=impl.DirectionEnum.INPUT,
                    signal_type=f"logic"
                )
            )


    # Add the sidebands if needed:
    _add_sidebands(pad_instance, port_group)

    # Add dft signals
    if pad_instance.dft:
        if pad_instance.direction in [impl.DirectionEnum.OUTPUT, impl.DirectionEnum.INOUT]:
            port_group.add_port(
                port.Port(
                    name=f"{pad_instance.dft_signal_output}",
                    direction=impl.DirectionEnum.INPUT,
                    signal_type=f"logic"
                )
            )
            port_group.add_port(
                port.Port(
                    name=f"{pad_instance.dft_signal_output_enable}",
                    direction=impl.DirectionEnum.INPUT,
                    signal_type=f"logic"
                )
            )

        if pad_instance.direction in [impl.DirectionEnum.INPUT, impl.DirectionEnum.INOUT]:
            port_group.add_port(
                port.Port(
                    name=f"{pad_instance.dft_signal_input}",
                    direction=impl.DirectionEnum.OUTPUT,
                    signal_type=f"logic"
                )
            )
            port_group.add_port(
                port.Port(
                    name=f"{pad_instance.dft_signal_input_enable}",
                    direction=impl.DirectionEnum.INPUT,
                    signal_type=f"logic"
                )
            )

        _add_dft_sidebands(pad_instance, port_group)


    # Add the pad wire:
    port_group.add_port(
        port.Port(
            name=f"{pad_instance.pad_signal}",
            direction=pad_instance.direction,
            signal_type="wire"
        )
    )

    return port_group


def _remove_duplicate_ports(
    port_groups: list[port.PortGroup],
) -> list[port.PortGroup]:
    seen_ports = set()
    for port_group in port_groups:
        for port in port_group.ports:
            port_tuple = (port.name, port.direction, port.signal_type)
            if port_tuple not in seen_ports:
                seen_ports.add(port_tuple)
            else:
                port.is_duplicate = True
    return port_groups


def extract_portgroups(
    pads: list[pad.FunctionalPad]
) -> list[port.PortGroup]:
    bus_ports = _get_bus_ports(pads)

    port_groups = dict()
    for pad_instance in pads:
        if pad_instance.is_oscillator_pad:
            port_groups[pad_instance.name] = _create_oscillatorgroup(pad_instance) # This is ok as we did create a oscillator pad
        elif pad_instance.is_bus:
            if pad_instance.busname not in bus_ports:
                raise CoreError(f"Bus {pad_instance.busname} not found in extracted busses")

            if pad_instance.busname not in port_groups:
                port_groups[pad_instance.busname] = _create_busportgroup(pad_instance, bus_ports[pad_instance.busname])
        else:
            port_groups[pad_instance.name] = _create_portgroup(pad_instance)

    return _remove_duplicate_ports([port_group for port_group in port_groups.values()])


def split_functional_and_oscillator(
    pads: list[pad.FunctionalPad | pad.OscillatorPad],
) -> tuple[list[pad.FunctionalPad], list[pad.OscillatorPad]]:
    functional_list = list()
    oscillator_list = list()

    for pad_istance in pads:
        oscillator_list.append(pad_istance) if pad_istance.is_oscillator_pad else functional_list.append(pad_istance)

    return functional_list, oscillator_list

def number_of_pad_rows(
    pads: list[pad.FunctionalPad | pad.OscillatorPad],
) -> int:
    return max(pad_instance.row_index for pad_instance in pads) + 1
