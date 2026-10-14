# Accurate Models toolbox v0.1: H100 and H200 FP8 outputs

Unmodified copies from [MATLAB-tensor-core](https://github.com/north-numerical-computing/MATLAB-tensor-core)
at release v0.1 (commit `109e412`, 2025-11-29; v0.2 holds the same files), under the toolbox's
BSD 2-Clause licence (`LICENCE`): the binary32 outputs of H100 and H200 for E4M3 and E5M2 inputs.
The inputs are the a, b and c files of commit `79143bd` (`../matlab-tensor-core-79143bd`), which
later releases did not change; from v0.3 on, the toolbox holds other output files for these
inputs, which agree with the Hopper block FMA from a zero accumulator. `SOURCES.json` pins the commit and the SHA-256 of every
file.

Why they are here: these are the only recorded H100 and H200 FP8 outputs in which `c` is
accumulated. `scripts/check_device_replay.py` replays them through the FP8 `mma.sync` model (two
interleaved FP16 block FMAs, then `c` added in binary32), which they match bit for bit.
