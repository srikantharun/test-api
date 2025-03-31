# (C) Copyright Axelera AI 2024
# All Rights Reserved
# *** Axelera AI Confidential ***
#
# Owner: Jovin Langenegger <jovin.langenegger@axelera.ai>

import random
import re
from collections import defaultdict
from pydantic import (
    BaseModel,
    create_model,
    Field,
    field_validator,
    PrivateAttr,
    ValidationInfo,
)
from typing_extensions import Annotated
from typing import Dict, List, Optional, Union

from settings import Settings


def _validate_return_list(cls, value) -> List:
    return value if isinstance(value, list) else [value]


def group_by_prefix(flavors: List[str]) -> Dict[str, List[str]]:
    grouped = defaultdict(lambda: [])
    for flavor in flavors:
        prefix = flavor.split(".", 1)[0]
        grouped[prefix].append(flavor)
    return dict(grouped)


class Attributes(BaseModel, extra="forbid"):
    name: str = Field(...)
    master: Union[str, List[str]] = []
    flags: Union[str, List[str]] = []
    pre_hook: str = ""

    @field_validator("master", "flags")
    def return_list(cls, value):
        return _validate_return_list(cls, value)


class BaseLabelAttributes(Attributes, extra="forbid"):
    repeat_count_multiplier: int = 1

    @field_validator("repeat_count_multiplier")
    def _validate_repeat_count(cls, repeat_count_multiplier: int, info: ValidationInfo) -> int:
        assert (
            repeat_count_multiplier > 0
        ), f"Invalid repeat_count_multiplier: {repeat_count_multiplier}. Value must be > 0."
        return repeat_count_multiplier


class BaseFlavorAttributes(Attributes, extra="forbid"):
    # We keep the convention of Baseclasses inheriting form Attributes
    pass

class BasePlatformAttributes(Attributes, extra="forbid"):
    owner: Union[str, List[str]] = Field(...)
    run_script: str = Field(...)
    processors: List[str] = []
    default_flavors: Union[str, List[str]] = []

    @field_validator("owner", "default_flavors")
    def return_list_2(cls, value):
        return _validate_return_list(cls, value)

    @field_validator("name")
    def check_name(cls, value: str, info: ValidationInfo):
        parts = value.split(".")
        systems = info.context["settings"].systems
        assert len(parts) == 2, "Platform names need to be of format 'foo.BAR'."
        assert parts[0] in systems, f"Platform prefix must be in {systems}."
        return value

    @field_validator("run_script")
    def check_run_script(cls, value: str, info: ValidationInfo):
        assert value.startswith(
            "./"
        ), f"Attribute {info.field_name} '{value}' must start with './' ."
        return value

    @field_validator("default_flavors")
    def check_flavors_exist(cls, values: List[str], info: ValidationInfo):
        for flavor in values:
            assert (
                flavor in info.context["attrs"]["flavors"]
            ), f"specified non-existing default flavor {flavor} for platform {info.data['name']}"
        return values

    @field_validator("default_flavors")
    def check_flavors_unique_per_tag(cls, value: List[str], info: ValidationInfo):
        flavors_by_prefix = group_by_prefix(value)
        for prefix, flavors in flavors_by_prefix.items():
            if len(flavors) > 1:
                flavors_str = ", ".join(flavors)
                assert (
                    False
                ), f"specified multiple default flavors for tag {prefix}.* ({flavors_str}) in YAML file, at most one allowed"
        return value

    @field_validator("processors")
    def check_processors_exist(cls, processors: List[str], info: ValidationInfo):
        all_processors = list(info.context["settings"].firmware.processors.keys())
        for processor in processors:
            assert (
                processor in all_processors
            ), f"specified non-existing processor {processor} for platform {info.data['name']}"
        return processors


class BaseTestInstance(BaseModel, extra="forbid"):
    name: str = Field(...)
    owner: Union[str, List[str]] = Field(...)
    description: str = Field(...)
    requirement_ids: Union[str, List[str]] = Field(...)
    labels: Union[str, List[str]] = []
    platforms: Union[str, List[str]] = Field(...)
    flavors: Union[str, List[str]] = []
    flags: Union[str, List[str]] = []
    repeat_count: int = None
    seeds: Annotated[List[int], Field(validate_default=True)] = []
    pre_compilation: str = ""
    # fields for firmware sources are added dynamically

    _context: Dict = PrivateAttr()

    def filter(self, args, context_filtered):
        self._context = context_filtered

        valid = args.platform in self.platforms or len(self.platforms) == 0
        valid = valid and (args.label in self.labels or args.label is None)

        # Ensure all flavors in self.flavors exist in context_flavors
        valid = valid and all(flavor in context_filtered["attrs"]["flavors"].keys() for flavor in self.flavors)

        self.platforms = (
            args.platform
            if (args.platform in self.platforms or len(self.platforms) == 0)
            else None
        )
        self.labels = args.label if (args.label in self.labels) else None
        self.flavors = list(context_filtered["attrs"]["flavors"].keys())

        return valid

    def toCmake(self) -> Dict[str, str]:
        # static fields
        cmake = {}
        cmake["NAME"] = self.name
        cmake["PRE_COMPILATION"] = self.pre_compilation
        cmake["RUN_SCRIPT"] = f"${{run_script}}"
        cmake["SEEDS"] = " ".join(str(s) for s in self.seeds)
        attr_flags = []
        for attr, _ in self._context.get("attrs").items():
            values = getattr(self, attr)
            if values != [] and values is not None:
                values = values if isinstance(values, list) else [values]
                for value in values:
                    value_sanitized = value.replace(".", "_")
                    attr_flags.append(f"${{{attr}_{value_sanitized}_flags}}")
        cmake["FLAGS"] = " ".join(self.flags + attr_flags)
        cmake["ATTRIBUTE_SRCS"] = "${src_attr_default}"

        # test sources (dynamic)
        platforms = self._context["attrs"]["platforms"]
        assert len(platforms) == 1, "not exactly one platform selected"
        platform = list(platforms.values())[0]
        for name in platform.processors:
            metadata = self._context["settings"].firmware.processors[name]
            libs = [f"${{src_lib_{lib}}}" for lib in metadata.lib]
            attrs = [f"${{src_attr_{name}}}"]
            key = f"SRC_TEST_{name.upper()}"
            sources = getattr(self, name)
            if not sources:
                continue
            cmake[key] = " ".join(libs + attrs + sources)

        return cmake

    @field_validator(
        "owner", "requirement_ids", "labels", "platforms", "flavors", "flags"
    )
    def _validate_return_list(cls, value) -> List[str]:
        return _validate_return_list(cls, value)

    # field_validator for dynamically added fields only
    def _validate_file_path(cls, values, info: ValidationInfo):
        settings = info.context["settings"]
        for i, value in enumerate(values):
            file = settings.directories.tests / value
            values[i] = str(file.relative_to(settings.directories.sw))
        return values

    @field_validator("platforms")
    def _validate_platforms(cls, values: List[str], info: ValidationInfo) -> List[str]:
        candidates = info.context["attrs"][info.field_name]
        expanded_values = []
        for value in values:
            if value in candidates:
                # Explicitly specified.
                expanded_values.append(value)
            elif (
                value.endswith(".*") and value[:-2] in info.context["settings"].systems
            ):
                # Specified as glob, e.g., 'top.*'.
                prefix = value[:-1]
                expanded = [c for c in candidates if c.startswith(prefix)]
                assert (
                    len(expanded) > 0
                ), f"Specified platform {value} is invalid, should expand to at least one concrete flavor."
                expanded_values.extend(expanded)
            elif value == "TODO":
                expanded = f"todo.{value}"
                expanded_values.append(expanded)
            else:
                assert (
                    False
                ), f"Platform '{value}' is invalid, specify either full platform (foo.BAR) or glob (foo.*)."
        assert len(expanded_values) >= 1, f"At least one platform has to be specified."
        return expanded_values

    @field_validator("flavors")
    def _validate_flavors(cls, values: List[str], info: ValidationInfo) -> List[str]:
        candidates = info.context["attrs"][info.field_name]
        expanded_values = []
        for value in values:
            if value in candidates:
                # Explicitly specified.
                expanded_values.append(value)
            elif value.endswith(".*"):
                # Specified as glob, e.g., 'default.*'.
                prefix = value[:-1]
                expanded = [c for c in candidates if c.startswith(prefix)]
                assert (
                    len(expanded) > 0
                ), f"Specified flavor {value} is invalid, should expand to at least one concrete flavor."
                expanded_values.extend(expanded)
            else:
                assert (
                    False
                ), f"Platform '{value}' is invalid, specify either full platform (foo.BAR) or glob (foo.*)."
        assert len(expanded_values) >= 1, f"At least one platform has to be specified."
        return expanded_values

    @field_validator("labels")
    def _validate_labels(cls, values: List[str], info: ValidationInfo) -> List[str]:
        for value in values:
            assert value in info.context.get("attrs").get(
                info.field_name
            ), f"Attribute {info.field_name} '{value}' is not defined in list of attributes: {list(info.context.get('attrs').get(info.field_name).keys())}."
        return values

    @field_validator("repeat_count")
    def _validate_repeat_count(cls, repeat_count: int, info: ValidationInfo) -> int:
        assert (
            repeat_count > 0
        ), f"Invalid repeat_count: {repeat_count}. Value must be > 0."
        return repeat_count

    @field_validator("seeds")
    def _validate_seeds(cls, values: List[int], info: ValidationInfo) -> List[int]:
        num_seeds = len(values)

        if info.data["repeat_count"] is None:
            info.data["repeat_count"] = num_seeds

        assert info.data["repeat_count"] >= num_seeds, f"Seeds exceed repeat_count! Number of seeds:{num_seeds}, repeat_count: {info.data['repeat_count']}."

        return values

def get_all_possible_cores(settings):
    processors = list(settings.firmware.processors.keys())
    processors.append('coreX')

    for name in settings.firmware.processors:
        # match a positive number at the end of a processor name
        match = re.match(r'^(.*?)(\d+)$', name)
        if match and not f'{match.group(1)}X' in processors:
            processors.append(f'{match.group(1)}X')
    return processors

def create_test_instance_model(baseInstance: BaseModel, settings: Settings, isTestModel=False) -> any:
    fields = {}
    processors = get_all_possible_cores(settings)
    for name in processors:
        fields[name] = (Union[str, List[str]], [])

    # field validators
    # WARNING: The keys of this dictionary must not overlap with the field
    # names. Otherwise, the validators will be silently ignored.
    validators = {
        "validate_return_list": field_validator(*fields)(
            BaseTestInstance._validate_return_list
        ),
    }

    if isTestModel:
        validators["validate_file_path"] = field_validator(*fields)(
            BaseTestInstance._validate_file_path
        )

    model = create_model(
        "TestInstance", **fields, __base__=baseInstance, __validators__=validators
    )
    return model
