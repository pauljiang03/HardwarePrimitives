# Work in progress

These projects build on the hardware models of this repository but are not part of the documented
development: the [website](https://pauljiang03.github.io/HardwarePrimitives/) does not cover them,
and the root checks do not build them. Each is a standalone Lake project that requires the root
library `TensorCore` and the AMD library [`MatrixCore`](../amd/README.md) by relative path.

| Folder | What it holds |
| --- | --- |
| [`ozaki/`](ozaki/README.md) | The Ozaki schemes (Ozaki-I, Ozaki-II, and ADP/ESC) on the Tensor Core and matrix core models, with correctly rounded versions of all three |
| [`mmalgebra/`](mmalgebra/README.md) | The reduction algebra of schedules: when two GEMM schedules give bitwise identical results on the Tensor Core and matrix core models, and how far apart they can be, with a Python prototype; it also requires `ozaki/` |
| [`site-pages/`](site-pages/) | The website pages of both projects, kept here while they are off the site; their links use the website's paths |

Build and check each project from its own folder:

```sh
cd wip/ozaki && lake build && python3 -B scripts/check.py
cd wip/mmalgebra && lake build && python3 -B scripts/check.py --prototype --port
```
