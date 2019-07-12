These are verifications by [Andrew Appel](https://www.cs.princeton.edu/~appel/) of programs from the [cbench](https://github.com/cverified/cbench) benchmark
using [VST](https://vst.cs.princeton.edu).

BUILD INSTRUCTIONS:  see in each subdirectory.

POINTS CLAIMED:

|            | [VST](https://vst.cs.princeton.edu) |
|------------|----:|
| **Total**  |  28 |
| `fac1.c`   |   4 |
| `fac2.c`   |   4 |
| `fac3.c`   |   4 |
| `fac4.c`   |   4 |
| `fac6.c`   |   4 |
| `qsort1.c` |   4 |
| `qsort3.c` |   4 |

Note 1: qsort1.c contains a main() with calls to printf().  At the moment, VST cannot do printf.  However, the chart in the [paper](https://arxiv.org/abs/1904.01009) lists qsort1.c as "not containing standard library calls, not containing I/O", so I assume that main() is not part of the task in qsort1.c.