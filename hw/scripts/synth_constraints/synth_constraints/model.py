# --------------------------------------------------------------------------------------------------
# (C) Copyright 2024 Axelera AI B.V.
# All rights reserved.
# *** Axelera AI Confidential ***
# --------------------------------------------------------------------------------------------------

"""TODO:__one_line_summary_of_mondel.py__

TODO:__multiline_description_of_mondel.py__
"""

# --------------------------------------------------------------------------------------------------
# Imports
# --------------------------------------------------------------------------------------------------

import logging
import pydantic
import enum
import typing

# --------------------------------------------------------------------------------------------------
# Exports
# --------------------------------------------------------------------------------------------------

__all__ = [
    "ConstraintModel",
]

# --------------------------------------------------------------------------------------------------
# Module Variables
# --------------------------------------------------------------------------------------------------

_logger = logging.getLogger(__name__)

# --------------------------------------------------------------------------------------------------
# Enumerations
# --------------------------------------------------------------------------------------------------

class ModeEnum(str, enum.Enum):
    func = "func"
    atspeed = "atspeed"
    shift = "shift"


class ObjectEnum(str, enum.Enum):
    pin = "pin"
    port = "port"
    net = "net"
    cell = "cell"
    expr = "expr"


class TimingTypeEnum(str, enum.Enum):
    setup = "setup"
    hold = "hold"
    both = "both"


class MinMaxEnum(str, enum.Enum):
    min = "min"
    max = "max"


class PropagationTypeEnum(str, enum.Enum):
    clock = "clock"
    data = "data"


class EdgeEnum(str, enum.Enum):
    positive = "positive"
    negative = "negative"


class ClockExclusiveEnum(str, enum.Enum):
    asynchronous = "asynchronous"
    physically_exclusive = "physically_exclusive"
    logically_exclusive = "logically_exclusive"


# --------------------------------------------------------------------------------------------------
# Model
# --------------------------------------------------------------------------------------------------

class PackageModel(pydantic.BaseModel):
    name: str
    description: str
    authors: list[str]


class ConstraintModel(pydantic.BaseModel):
    mode: ModeEnum = ModeEnum.func


class ObjectModel(pydantic.BaseModel):
    name: str
    type: ObjectEnum

    @pydantic.field_validator("name")
    @classmethod
    def brackets_must_close(cls, v: str) -> str:
        open_brackets = tuple("([{")
        close_brackets = tuple(")]}")
        mapping = dict(zip(open_brackets, close_brackets))
        queue = []

        for index, letter in enumerate(v):
            if letter in open_brackets:
                queue.append(mapping[letter])
            elif letter in close_brackets:
                if not queue or letter != queue.pop():
                    raise ValueError(f"In '{v}', letter {index}, expected {queue}, but got '{letter}'")

        if queue:
            raise ValueError(f"Parenthesis not closed, expected {queue}, but got noting")

        return v

    @pydantic.model_validator(mode="after")
    def expr_must_be_get_object_expression(self) -> "ObjectModel":
        if self.type is ObjectEnum.expr:
            if "[" not in self.name:
                raise ValueError("Must contain '['")
            if "]" not in self.name:
                raise ValueError("Must contain ']'")
            if "get_" not in self.name:
                raise ValueError("Must contain a 'get_*' expression")

        return self


class MasterClockModel(ConstraintModel):
    clock_type: typing.Literal["master"]
    name: str
    freq_mhz: int
    dc: pydantic.conint(ge=1, le=100) = 50
    source: ObjectModel
    sync_in: list[ObjectModel] = pydantic.Field(default_factory=list)
    sync_out: list[ObjectModel] = pydantic.Field(default_factory=list)


class GeneratedClockModel(ConstraintModel):
    clock_type: typing.Literal["generated"]
    name: str
    divisor: pydantic.conint(ge=1)
    source: ObjectModel
    master_name: str
    master_source: ObjectModel
    sync_in: list[ObjectModel] = pydantic.Field(default_factory=list)
    sync_out: list[ObjectModel] = pydantic.Field(default_factory=list)

    @pydantic.field_validator("sync_in", "sync_out")
    @classmethod
    def no_inputs_allowed(cls, v: list[str]) -> list[str]:
        if v:
            raise ValueError("No inputs or atouts allowed for generated clocks!")
        return v


ClockModel = typing.Annotated[
                typing.Union[MasterClockModel, GeneratedClockModel],
                pydantic.Field(discriminator='clock_type'),
            ]


class ClockGroupModel(ConstraintModel):
    name: str
    exclusive: ClockExclusiveEnum = ClockExclusiveEnum.asynchronous
    groups: dict[pydantic.constr(pattern=r"group_\d+"), list[str]]
    allow_path: bool = False

class CaseAnalysisModel(ConstraintModel):
    object: ObjectModel
    value: pydantic.conint(ge=0, le=1)


class TimingPathModel(ConstraintModel):
    from_object: ObjectModel | None = None
    to_object: ObjectModel | None = None
    through_object: ObjectModel | None = None

    @pydantic.model_validator(mode="after")
    def at_least_one_object_defined(self) -> "TimingPathModel":
        if not any([self.from_object, self.to_object, self.through_object]):
            raise ValueError("At least one '[from|to|thourgh]_object' expression must be defiend!")

        return self


class FalsePathModel(TimingPathModel):
    type: TimingTypeEnum


class MultiCyclePathModel(TimingPathModel):
    type: TimingTypeEnum
    multiplier: pydantic.conint(ge=1)
    relative_to: str


class IoDelayModel(ConstraintModel):
    type: MinMaxEnum
    clock: str
    object: ObjectModel
    delay_ns: float


class DelayModel(TimingPathModel):
    delay_ns: float


class DataCheckModel(TimingPathModel):
    clock: str
    delay_ns: float
    type: TimingTypeEnum = TimingTypeEnum.both

    @pydantic.model_validator(mode="after")
    def no_through_allowed(self) -> "DisableTimingModel":
        if self.through_object:
            raise ValueError("'through_object' is not allowed in disable_timing")

        return self


class StopPropagationModel(ConstraintModel):
    type: PropagationTypeEnum
    edge: EdgeEnum
    object: ObjectModel
    clock: str


class DisableTimingModel(TimingPathModel):
    object: ObjectModel

    @pydantic.model_validator(mode="after")
    def no_through_allowed(self) -> "DisableTimingModel":
        if self.through_object:
            raise ValueError("'through_object' is not allowed in disable_timing")

        return self


class ConfigModel(pydantic.BaseModel):
    package: PackageModel
    clocks: list[ClockModel]
    clock_groups: list[ClockGroupModel] = pydantic.Field(default_factory=list)
    resets: list[ObjectModel]
    case_analysis: list[CaseAnalysisModel] | None = pydantic.Field(default_factory=list)
    false_path: list[FalsePathModel] | None = pydantic.Field(default_factory=list)
    mcp_path: list[MultiCyclePathModel] | None = pydantic.Field(default_factory=list)
    io_delay: list[IoDelayModel] | None = pydantic.Field(default_factory=list)
    max_delay: list[DelayModel] | None = pydantic.Field(default_factory=list)
    min_delay: list[DelayModel] | None = pydantic.Field(default_factory=list)
    data_check: list[DataCheckModel] | None = pydantic.Field(default_factory=list)
    stop_propagation: list[StopPropagationModel] | None = pydantic.Field(default_factory=list)
    disable_timing: list[DisableTimingModel] | None = pydantic.Field(default_factory=list)
    retiming: list[ObjectModel] | None = pydantic.Field(default_factory=list)

    @pydantic.validator(
        "case_analysis",
        "false_path",
        "mcp_path",
        "io_delay",
        "max_delay",
        "min_delay",
        "data_check",
        "stop_propagation",
        "disable_timing",
        pre=True,
        each_item=False,
    )
    def set_list_to_default(cls, v):
        return v or []
