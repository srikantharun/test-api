#!/usr/bin/env python3

import yaml
import argparse
import os
from pathlib import Path
from typing import List
from pydantic import BaseModel, field_validator

COVERAGE_EDIT_TEMPLATE = """
# Auto-generated section for {location}
vsim -c -do <(cat << EOF
coverage open {location}
{coverage_edit}
coverage save {output_location}
exit
EOF
)
"""

COV_SCRIPT_TEMPLATE_PATH = (
    f"{os.environ['REPO_ROOT']}/hw/impl/europa/blocks/soc_periph/dv/coverage/coverage_script_template.sh"
)


class DataBaseInfo(BaseModel, extra="forbid"):
    name: str
    location: str
    inst_path: str
    rename: str | None = None
    delete: List[str] | None = None
    move_inside: str | None = None

    @field_validator("location")
    def validate_location(cls, location: str) -> str:
        loc_path = Path(os.environ["REPO_ROOT"]) / location
        if loc_path.exists():
            assert loc_path.is_file(), f"{loc_path} is not a file!"
        else:
            print(f"Warning: {loc_path} does not exists!")
        return str(loc_path)

    def gen_config(self) -> str:
        lines = []
        lines.append(f"coverage edit -keeponly -path {self.inst_path}")
        if self.rename:
            lines.append(f"coverage edit -path {self.inst_path} -rename {self.rename}")
        if self.move_inside:
            inst = Path(self.inst_path)
            if self.rename:
                # Use pathlib to edit instance path
                inst = inst.parent / self.rename
            lines.append(f"coverage edit -movedesign {inst} {self.move_inside}")
        if self.delete:
            for scope in self.delete:
                lines.append(f"coverage edit -delete -path {scope}")

        return COVERAGE_EDIT_TEMPLATE.format(
            coverage_edit="\n".join(lines), location=self.location, output_location=self.output_location
        )

    @property
    def output_location(self) -> str:
        return f"input/{self.name}.ucdb"

    @property
    def is_valid(self) -> bool:
        return Path(self.location).exists()

class CoverageExclude(BaseModel, extra="forbid"):
    scope: str
    signals: List[str]
    comment: str

    @property
    def exclude_command(self) -> str:
        return f'coverage exclude -scope {self.scope} -togglenode {" ".join(self.signals)} -comment "{self.comment}"'


def main():
    parser = argparse.ArgumentParser("Generate coverage merge script from YAML config")
    parser.add_argument("-f", "--file", required=True, help="YAML config")
    parser.add_argument("-o", "--output", help="Coverage output directory path", default="output_coverage")

    args = parser.parse_args()

    with open(args.file, "r") as f:
        cov_data = yaml.safe_load(f)

    db_infos = [DataBaseInfo.model_validate(db) for db in cov_data["databases"]]
    excludes = []
    if "excludes" in cov_data:
        excludes = [CoverageExclude.model_validate(exclude) for exclude in cov_data["excludes"]]

    with open(COV_SCRIPT_TEMPLATE_PATH, "r") as f:
        template = f.read()

    output_file = "coverage_script.sh"
    with open(output_file, "w+") as f:
        coverage_edit = []
        ucdb_list = []
        for db in db_infos:
            if db.is_valid:
                coverage_edit.append(db.gen_config())
                ucdb_list.append(db.output_location)
        exclude_list = [exclude.exclude_command for exclude in excludes]
        f.write(template.format(coverage_edit="\n".join(coverage_edit), ucdb_list=" ".join(ucdb_list), exclude_list="\n".join(exclude_list), output_dir=args.output))
    os.chmod(output_file, 0o777)


if __name__ == "__main__":
    main()
