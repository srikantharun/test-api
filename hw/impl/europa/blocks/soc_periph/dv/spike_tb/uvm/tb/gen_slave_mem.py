#!/usr/bin/env python3
from dataclasses import dataclass
from typing import Tuple
from pathlib import Path
import random

MEM_SIZE = 4  # MB
DATA_WIDTH = 8  # BYTES


@dataclass
class Buffer:
    start: int
    size_bytes: int

    @property
    def end(self) -> int:
        return self.start + self.size_bytes - 1

    def __repr__(self) -> str:
        return f"start: 0x{self.start:x}, end: 0x{self.end:x}, size: 0x{self.size_bytes:x}"


class Memory:
    def __init__(self, name: str, size_mb: int, data_width_bytes: int) -> None:
        self.name = name
        self.data_width_bytes = data_width_bytes
        self.size_mb = size_mb
        self._buffers = []

    @property
    def end(self) -> int:
        return 1024 * 1024 * self.size_mb

    def add_buffer(self, buffer: Buffer):
        if buffer.start > self.end:
            raise ValueError(f"Buffer address {buffer.start} is outside of the memory")

        if len(self._buffers) == 0:
            self._buffers.append(buffer)
            return

        if buffer.start > self._buffers[-1].end:
            self._buffers.append(buffer)
            return

        if buffer.end < self._buffers[0].base_address:
            self._buffers.insert(0, buffer)
            return

        for i in range(1, len(self._buffers)):
            prev_buffer = self._buffers[i - 1]
            next_buffer = self._buffers[i]
            if prev_buffer.end < buffer.start and buffer.end < next_buffer.base_address:
                self._buffers.insert(i, buffer)
                return

        raise ValueError(f"Unable to enqueue buffer {buffer}")

    def addr_inside_buff(self, addr: int, start_idx: int = 0) -> Tuple[bool, int]:
        if len(self._buffers) == 0 or start_idx >= len(self._buffers):
            return (False, 0)

        for i in range(start_idx, len(self._buffers)):
            buff = self._buffers[i]
            if addr < buff.start:
                return (False, 0)
            elif addr >= buff.start and addr <= buff.end:
                return (True, i)

        return (False, 0)

    def gen_memfile(self):
        buff_idx = 0
        dir_path = Path(__file__).parent
        with open(f"{dir_path}/{self.name}.hex", "w+") as f:
            data = "0x"
            for i in range(self.end):
                res, idx = self.addr_inside_buff(i, start_idx=buff_idx)
                if res:
                    buff_idx = idx
                    data += f"{random.randint(0, 255):02x}"
                else:
                    data += "00"

                if (i + 1) % self.data_width_bytes == 0:
                    f.write(data + "\n")
                    data = "0x"


if __name__ == "__main__":
    mem = Memory("emmc_slave_mem", 1, DATA_WIDTH)
    buff_in = Buffer(0x1000, 512)
    mem.add_buffer(buff_in)
    mem.gen_memfile()
