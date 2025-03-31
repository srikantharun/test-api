#!/usr/bin/env python3

import argparse
import collections
import jinja2
import logging
import math
import os
import pathlib
import pydantic
import subprocess
import typing
import yaml


class InterruptEntry(pydantic.BaseModel):
    name: str
    source: str
    prio_group: str
    trigger_on: typing.Literal['edge', 'level']
    invert_sync_behavior: bool = pydantic.Field(default=False)


class SortedInterruptMap():
    interrupt_map: typing.Dict[int, InterruptEntry]

    def __init__(self):
        self.interrupt_map = {}

    def get_all_interrupt(self) -> typing.List[InterruptEntry]:
        irqs = []

        for entry in self.interrupt_map.values():
            irqs.append(entry)

        return irqs

    def get_external_interrupt(self, block: str) -> typing.List[InterruptEntry]:
        irqs = []

        for entry in self.interrupt_map.values():
            if entry.source != block:
                irqs.append(entry)

        return irqs

    def get_internal_interrupt(self, block: str) -> typing.List[InterruptEntry]:
        irqs = []

        for entry in self.interrupt_map.values():
            if entry.source == block:
                irqs.append(entry)

        return irqs

    def get_edge_trigger_as_hex_param(self) -> str:
        trigger: int = 0

        for (idx, entry) in self.interrupt_map.items():
            if entry.trigger_on == "edge":
                trigger |= (1 << idx)

        return f"'h{trigger:x}"

    def get_async_as_hex_param(self, block: str) -> str:
        async_int: int = 0

        for (idx, entry) in self.interrupt_map.items():
            if entry.invert_sync_behavior:
                if entry.source == block:
                    async_int |= (1 << idx)
            else:
                if entry.source != block:
                    async_int |= (1 << idx)

        return f"'h{async_int:x}"

    def pretty_print(self):
        idx_max_width = math.floor(math.log10(len(self.interrupt_map.keys())+1)+1)
        prio_max_width = max(map(lambda kv: len(kv[1].prio_group), self.interrupt_map.items()))
        source_max_width = max(map(lambda kv: len(kv[1].source), self.interrupt_map.items()))
        name_max_width = max(map(lambda kv: len(kv[1].name), self.interrupt_map.items()))

        for (idx, entry) in self.interrupt_map.items():
            print(f"{idx:{idx_max_width}} {entry.prio_group:{prio_max_width}} {entry.source:{source_max_width}} {entry.name:{name_max_width}}")


class InterruptMap(pydantic.BaseModel):
    platform_irqs_header_path: pathlib.Path
    priority_groups: typing.List[str]
    interrupt_map: typing.List[InterruptEntry]

    def generate_sorted_interrupt_map(self) -> SortedInterruptMap:
        group_by_prio: typing.Dict[str, typing.List[InterruptEntry]] = collections.defaultdict(list)

        logging.debug("grouping entries by priority")
        for entry in self.interrupt_map:
            group_by_prio[entry.prio_group].append(entry)

        logging.debug("sorting entries following alphabetical order")
        for grouped_entries in group_by_prio.values():
            grouped_entries = sorted(grouped_entries, key=lambda e: f"{e.source}__{e.name}")

        logging.debug("filling entries into sorted interrupt map")
        sorted_map: typing.List[InterruptEntry] = []
        for group in self.priority_groups:
            if group in group_by_prio.keys():
                for entry in group_by_prio[group]:
                    sorted_map.append(entry)

        sorted_interrupt_map = SortedInterruptMap()
        for (idx, entry) in enumerate(sorted_map):
            sorted_interrupt_map.interrupt_map[idx + 1] = entry

        return sorted_interrupt_map

    @pydantic.model_validator(mode='after')
    def check_unique_name_per_source(cls, values):
        name_per_source: typing.Dict[str, typing.Set[str]] = collections.defaultdict(set)

        logging.debug("checking for duplicate names")
        for entry in values.interrupt_map:
            if entry.name in name_per_source[entry.source]:
                raise ValueError(f'duplicate {entry.name} for source {entry.source}')
            else:
                name_per_source[entry.source].add(entry.name)

        return values

    @pydantic.model_validator(mode='after')
    def check_unique_priority_group(cls, values):
        priority_set: typing.Set[str] = set()

        logging.debug("checking for duplicate priority_group")
        for prio in values.priority_groups:
            if prio in priority_set:
                raise ValueError(f'duplicate priority_group {prio}')
            else:
                priority_set.add(prio)

        return values

    @pydantic.model_validator(mode='after')
    def check_matching_priority_group(cls, values):
        logging.debug("checking for matching priority_group")
        for entry in values.interrupt_map:
            if entry.prio_group not in values.priority_groups:
                raise ValueError(f'non-existing prio_group {entry.prio_group} for {entry.name} of {entry.source}')

        return values


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Render the interrupt map generated files")
    parser.add_argument(
        "-d", "--debug",
        help="set logging at debug level",
        action="store_const", dest="log_level", const=logging.DEBUG, default=logging.WARNING)
    parser.add_argument(
        "-v", "--verbose",
        help="set logging at info level",
        action="store_const", dest="log_level", const=logging.INFO)

    parser.add_argument(
        "-b", "--block", type=str,
        required=True,
        help="block to generate")
    parser.add_argument(
        "-l", "--list-irqs",
        help="list IRQs in order",
        action="store_const", const=True, default=False)
    parser.add_argument(
        "-p", "--print-io",
        help="print the io",
        action="store_const", const=True, default=False)
    parser.add_argument(
        "-r", "--render-files",
        help="render the block pkg, and connectivity module(s)",
        action="store_const", const=True, default=False)

    args = parser.parse_args()
    logging.basicConfig(
        format="%(asctime)s %(levelname)s: (%(filename)s:%(lineno)s): %(message)s",
        datefmt="%Y-%m-%dT%H:%M:%S%z",
        level=args.log_level)

    logging.info("interrupt map script starting...")
    REPO_ROOT = pathlib.Path(os.environ.get("REPO_ROOT"))
    block_path = REPO_ROOT / "hw/impl/europa/blocks" / args.block
    cfg_path = block_path / "data/interrupt_map.yaml"

    logging.debug(f"reading {cfg_path}...")
    with cfg_path.open("r") as file:
        config = yaml.safe_load(file)
    logging.info(f"read {cfg_path}")

    logging.debug(f"validating {cfg_path}...")
    valid_cfg = InterruptMap.model_validate(config)
    sorted_cfg = valid_cfg.generate_sorted_interrupt_map()
    logging.info(f"validated {cfg_path}")

    all_irqs = sorted_cfg.get_all_interrupt()
    external_irqs = sorted_cfg.get_external_interrupt(args.block)
    internal_irqs = sorted_cfg.get_internal_interrupt(args.block)

    if args.print_io or args.render_files:
        logging.debug(f"loading jinja2 templates...")
        templates_path = REPO_ROOT / "hw/scripts/interrupt_map/templates"
        jinja_env = jinja2.Environment(
            loader=jinja2.FileSystemLoader(templates_path),
            autoescape=jinja2.select_autoescape())
        logging.info(f"loaded jinja2 templates")

    if args.list_irqs:
        logging.info("listing IRQs...")
        sorted_cfg.pretty_print()
        logging.debug("listed IRQs")

    if args.print_io:
        logging.info("printing IOs...")

        template = jinja_env.get_template("io_macros.jinja2")
        rendered = template.render(irqs=external_irqs)
        print(rendered)

        logging.info(f"printed {len(external_irqs)} IOs")

    if args.render_files:
        logging.info("rendering files...")

        logging.debug(f"rendering interrupt connectivity external...")
        template = jinja_env.get_template("axe_block_interrupt_connectivity_external.sv.jinja2")
        output_path = block_path / "rtl" / f"{args.block}_interrupt_connectivity_external.sv"

        rendered = template.render(
            block=args.block,
            external_irqs=external_irqs)

        with output_path.open("w") as file:
            file.write(rendered)
        subprocess.call(["verible-verilog-format", "--inplace", output_path])
        logging.info(f"wrote {output_path}")

        logging.debug(f"rendering interrupt connectivity internal...")
        template = jinja_env.get_template("axe_block_interrupt_connectivity_internal.sv.jinja2")
        output_path = block_path / "rtl" / f"{args.block}_interrupt_connectivity_internal.sv"

        rendered = template.render(
            block=args.block,
            external_irqs=external_irqs,
            internal_irqs=internal_irqs)

        with output_path.open("w") as file:
            file.write(rendered)
        subprocess.call(["verible-verilog-format", "--inplace", output_path])
        logging.info(f"wrote {output_path}")

        logging.debug(f"rendering interrupt map...")
        template = jinja_env.get_template("axe_block_interrupt_map_pkg.sv.jinja2")
        output_path = block_path / "rtl/pkg" / f"{args.block}_interrupt_map_pkg.sv"

        rendered = template.render(
            block=args.block,
            async_hex=sorted_cfg.get_async_as_hex_param(args.block),
            edge_trigger_hex=sorted_cfg.get_edge_trigger_as_hex_param(),
            external_irqs=external_irqs,
            all_irqs=all_irqs)

        with output_path.open("w") as file:
            file.write(rendered)
        subprocess.call(["verible-verilog-format", "--inplace", output_path])
        logging.info(f"wrote {output_path}")

        logging.debug(f"rendering platform irqs header...")
        template = jinja_env.get_template("platform_irqs.h.jinja2")
        output_path = pathlib.Path(os.path.expandvars(valid_cfg.platform_irqs_header_path))

        rendered = template.render(
            block=args.block,
            irqs=all_irqs)

        with output_path.open("w") as file:
            file.write(rendered)
        logging.info(f"wrote {output_path}")

        logging.info("rendered files")

    logging.info("interrupt map script done")
