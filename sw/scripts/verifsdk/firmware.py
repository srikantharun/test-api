# (C) Copyright Axelera AI 2024
# All Rights Reserved
# *** Axelera AI Confidential ***
#
# Owner: Jovin Langenegger <jovin.langenegger@axelera.ai>


def get_builtin_compile_flags(context: dict) -> list[str]:
    platforms = context["attrs"]["platforms"]
    assert len(platforms) == 1, "not exactly one platform specified"
    platform = list(platforms.values())[0]

    # flag: -DSYSTEM_*
    system = platform.name.split(".")[0]
    flags = [f"-DSYSTEM_{system.upper()}"]

    # flags: -DPROCESSOR_*
    for processor in platform.processors:
        flags += [f"-DPROCESSOR_{processor.upper()}"]

    return flags
