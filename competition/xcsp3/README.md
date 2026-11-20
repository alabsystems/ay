# XCSP3 entry for AY

`ay-xcsp3 <instance.xml> [-l SECONDS] [-c CORES] [-s SEED] [-m MiB]`

AY has no XCSP3 reader of its own yet. The entry reads the instance with
CPMpy's XCSP3 front end and solves it with AY as a FlatZinc solver behind
MiniZinc, with AY's own MiniZinc library and `fzn-exec`
(`../minizinc`). It prints what the competition reads: the status line
(`s SATISFIABLE`, `s OPTIMUM FOUND`, `s UNSATISFIABLE`, `s UNKNOWN`) and the
`v <instantiation>` of every variable, with its cost on optimisation
instances.

## What it needs

| What | Version measured with | How the entry finds it |
|---|---|---|
| Python with `cpmpy` (and the `pycsp3` parser it uses) | cpmpy 1.1.1, Python 3.12 | `AY_XCSP3_PYTHON`, default `python3` |
| the `minizinc` Python package | 0.10.0 | importable by that Python |
| MiniZinc | 2.9.7 | `minizinc` on `PATH` |
| the ay binary | this repository's | beside `../minizinc/fzn-exec`, or on `PATH`, or `AY=/path/to/ay` |

CPMpy 1.1.1 does not check the sub-solver name against its list of known
MiniZinc solvers; a later CPMpy may, so the version is part of the entry.

## What it does not do

- No intermediate `o` lines: CPMpy's MiniZinc back end reports the final
  solution only. An optimisation job that is stopped before AY ends has no
  answer, where a native entry would hold its best solution.
- CPMpy's native circuit constraints are used for the solver named exactly
  `minizinc`; with AY they are decomposed. Correct, slower.
- Constraints CPMpy's reader does not support end with its own
  `s UNSUPPORTED`.
- Every limit of `ay flatzinc solve` carries over. Two that MiniZinc Challenge
  instances hit (measured 2026-11-13 on `268ebff6e252`): the CP back end
  preallocates at most 2^20 order literals over the declared integer domains
  (`MAX_PREALLOCATED_ORDER_LITERALS`, `crates/ay-cp/src/encoder.rs`) and
  answers UNKNOWN beyond that, and a variable-by-variable `int_times` or
  `int_div` is supported only as a table of at most 10,000 values, beyond which
  `ay flatzinc solve` falls back to the SMT translation without a message.

## Measured

All-comp scoreboard (`sb`), run `base-20261114`, 18 November 2026, ay
`268ebff6e252`, the six XCSP3 tracks, 20 instances each, 60 s (180 s in the
fast track): 43 answers on 120 jobs, every one accepted by the organizers'
solution checker, none wrong. Places among the entrants run there: 5th of 5
in CSP, COP, Fast COP and Parallel COP, 4th of 6 in Mini CSP, 6th of 6 in
Mini COP. Parallel COP has no answer: `-c 8` reaches `ay flatzinc solve -p 8`.

## What should replace it

A reader inside AY (`ay xcsp3 solve FILE`): an XCSP3-core parser that lowers
to the FlatZinc model types or straight to the CP engine, prints `o` on
every improvement and the last solution on SIGTERM.
