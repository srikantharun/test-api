---
title: NoC: Token Network
doc:
  status: draft
  version: [0, 0, 1]
  confidentiality: internal
---

# Token Network

The Token Network is an entirely separate network to the main NoC. It's accessible by 11 partitions:

* AI Cores 0-7
* SDMA 0-1
* APU

The Token Network has its own [memory map](#memory-map) on an entirely separate address space and uses light-weight, write-only interfaces. The Token Network has no responses and no Error Logging.

## Interfaces

For every Token-enabled partition, there exists a pair of Initiator and Target OCP-Lite ports. The OCP-Lite protocol is a massively simplified version of OCP with the following attributes/signals:

| Signal       | Width | Description      | Driver
| ------------ | -----:| ---------------- | --------
| `maddr`      | 8     | Transfer Address | Manager
| `mcmd`       | 1*    | Transfer Command | Manager
| `mdata`      | 8     | Write Data       | Manager
| `scmdaccept` | 1     | Back-pressure    | Subordinate

\* Note that the original OCP `mcmd` signal consists of 3 bits to encode 8 different commands (`Idle`, `Write`, `Read`, etc). We only use the 1 LSB of that encoding, tieing 2 MSBs to `0`. Therefore, there are only 2 Transfer Commands that can be encoded:

* `Idle` when `mcmd[0] = 0`, implying `mcmd[2:0] = 3b'000`
* `Write` when `mcmd[0] = 1`, implying `mcmd[2:0] = 3b'001`

Keep in mind that a `Write` implies a Posted Write (hence, the missing response signals). For more information, read the OCP specification from [Accellera](https://www.accellera.org/downloads/standards/ocp).

## Clocks, Resets, Fences

* The Clock used by the Token interfaces is the main NIU clock for that block (see [Baseband Interfaces](./baseband_interfaces.md) page).
* The Reset used by the Token interfaces is the main NIU reset for that block (see [Baseband Interfaces](./baseband_interfaces.md) page).
* A separate Fence is implemented to control the Power state of these interfaces' NIUs (see [Clock, Reset & Fences](./clocks-resets-fences.md) page).


## Memory Map

The Token Network has its own memory map that's completely independent to the memory of the main NoC.

| Low  | High | Size | W/R | Target
| ----:| ----:| ----:| --- | ----
|  0x0 | 0x3  | 0x4  |  W  | AI Core 0 Token Target
|  0x4 | 0x7  | 0x4  |  W  | AI Core 1 Token Target
|  0x8 | 0xB  | 0x4  |  W  | AI Core 2 Token Target
|  0xC | 0xF  | 0x4  |  W  | AI Core 3 Token Target
| 0x10 | 0x13 | 0x4  |  W  | AI Core 4 Token Target
| 0x14 | 0x17 | 0x4  |  W  | AI Core 5 Token Target
| 0x18 | 0x1B | 0x4  |  W  | AI Core 6 Token Target
| 0x1C | 0x1F | 0x4  |  W  | AI Core 7 Token Target
| 0x20 | 0x23 | 0x4  |  W  | SDMA 0 Token Target
| 0x24 | 0x27 | 0x4  |  W  | SDMA 1 Token Target
| 0x28 | 0x2B | 0x4  |  W  | APU Token Target

## Connectivity

All Initiators can access all Targets, except of its own IP's Token Target (i.e. loopbacks not allowed). The connectivity matrix looks like this:

|        |AIC 0|AIC 1|AIC 2|AIC 3|AIC 4| AIC 5|AIC 6|AIC 7|APU|SDMA 0|SDMA 1
|:-------|-----|-----|-----|-----|-----|-----|-----|-----|-----|-----|-----
| AIC 0  | -|X|X|X|X|X|X|X|X|X|X
| AIC 1  | X|-|X|X|X|X|X|X|X|X|X
| AIC 2  | X|X|-|X|X|X|X|X|X|X|X
| AIC 3  | X|X|X|-|X|X|X|X|X|X|X
| AIC 4  | X|X|X|X|-|X|X|X|X|X|X
| AIC 5  | X|X|X|X|X|-|X|X|X|X|X
| AIC 6  | X|X|X|X|X|X|-|X|X|X|X
| AIC 7  | X|X|X|X|X|X|X|-|X|X|X
| APU    | X|X|X|X|X|X|X|X|-|X|X
| sdma_0 | X|X|X|X|X|X|X|X|X|-|X
| sdma_1 | X|X|X|X|X|X|X|X|X|X|-
