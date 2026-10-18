# Work in progress

Work in progress and archived documentation. Nothing here is part of the
libraries: the [website](https://pauljiang03.github.io/HardwarePrimitives/)
does not cover it, and the root checks do not build it.

| Folder | Contents |
| --- | --- |
| [`ozaki/`](ozaki/README.md) | The Ozaki schemes (Ozaki-I, Ozaki-II, ADP/ESC) on the Tensor Core and matrix core models, with correctly rounded versions |
| [`mmalgebra/`](mmalgebra/README.md) | The reduction algebra of schedules: when two GEMM schedules give identical bits, and how far apart they can be; requires `ozaki/` |
| [`site-pages/`](site-pages/) | The website pages of both projects, kept while they are off the site |
| [`docs/`](docs/) | Earlier guides, the reviewer guide, the status file, the theorem indexes and the test walkthrough; not maintained |

`ozaki/` and `mmalgebra/` are standalone Lake projects that require
[`TensorCore`](../tensor-core/README.md) and [`MatrixCore`](../matrix-core/README.md) by relative path:

```sh
cd wip/ozaki && lake build && python3 -B scripts/check.py
cd wip/mmalgebra && lake build && python3 -B scripts/check.py --prototype --port
```
