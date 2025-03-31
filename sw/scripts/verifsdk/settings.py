# (C) Copyright Axelera AI 2024
# All Rights Reserved
# *** Axelera AI Confidential ***
#
# Owner: Jovin Langenegger <jovin.langenegger@axelera.ai>

import os
import sys
import yaml
from pathlib import Path
from pydantic import BaseModel, computed_field, field_validator, ValidationInfo
from typing import Dict, List, Optional


VERIFSDK_SETTINGS_FILENAME = "verifsdk.yaml"


# used by _get_repo_root()
_repo_root_cache: Optional[Path] = None


def _get_repo_root() -> Path:
    global _repo_root_cache
    if _repo_root_cache is None:
        repo_root = os.environ.get("REPO_ROOT", "")
        if not repo_root:
            print("VerifSDK: Variable $REPO_ROOT required but not set.")
            sys.exit(1)
        _repo_root_cache = Path(repo_root)
    return _repo_root_cache


def _prepend_root_dir(value: Path, info: ValidationInfo):
    assert not value.is_absolute(), f"{info.field_name} is not a relative path."
    return _get_repo_root() / value


class DirectoriesSettings(BaseModel, extra="forbid"):
    config: Path
    sw: Path

    @computed_field
    @property
    def root(self) -> Path:
        return _get_repo_root()

    @field_validator("config", "sw")
    def prepend_root_dir(cls, value: Path, info: ValidationInfo):
        return _prepend_root_dir(value, info)

    @computed_field
    @property
    def tests(self) -> Path:
        return self.sw / "src/tests"


class ProcessorSettings(BaseModel, extra="forbid"):
    lib: List[str]


class FirmwareSettings(BaseModel, extra="forbid"):
    processors: Dict[str, ProcessorSettings]


class CmakeSettings(BaseModel, extra="forbid"):
    includes: List[Path]
    callable: str

    @field_validator("includes")
    def prepend_root_dir_list(cls, value: List[Path], info: ValidationInfo):
        return [_prepend_root_dir(include, info) for include in value]


class Settings(BaseModel, extra="forbid"):
    project_name: str
    directories: DirectoriesSettings
    systems: List[str]
    firmware: FirmwareSettings
    cmake: CmakeSettings


def load_verifsdk_settings() -> Settings:
    settings_path = _get_repo_root() / VERIFSDK_SETTINGS_FILENAME
    if not settings_path.is_file():
        print(
            f"VerifSDK error: settings file $REPO_ROOT/{VERIFSDK_SETTINGS_FILENAME} does not exist."
        )
        sys.exit(1)

    with settings_path.open("r") as f:
        data = yaml.load(f, Loader=yaml.CSafeLoader)
    settings = Settings.model_validate(data["verifsdk"])

    return settings
