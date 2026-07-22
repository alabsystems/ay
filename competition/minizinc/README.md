# MiniZinc integration for AY

`fzn-exec` is a FlatZinc wrapper around `ay flatzinc solve`; `../../ay.msc`
is the MiniZinc solver descriptor that points at it.

## Installation

The descriptor is not installed
by any packaging step, so MiniZinc cannot discover AY until you register it
manually. Either:

1. Add this repository root to the MiniZinc solver search path:

   ```sh
   export MZN_SOLVER_PATH="/path/to/ay:${MZN_SOLVER_PATH:-}"
   ```

   (MiniZinc scans `MZN_SOLVER_PATH` directories for `*.msc` files; `ay.msc`
   lives at the repo root and references `competition/minizinc/fzn-exec` by
   relative path, so the repo root must be the registered directory.)

2. Or copy `ay.msc` into a user solver directory MiniZinc already scans
   (e.g. `~/.minizinc/solvers/`) after editing its `"executable"` field to an
   absolute path to `fzn-exec`.

The wrapper prefers an `ay` binary sitting next to it (packaged-bundle
layout) and falls back to `ay` on PATH — build one with
`cargo build -p ay --features cli --release` and either copy
`target/release/ay` next to `fzn-exec` or put it on PATH.

Verify registration with:

```sh
minizinc --solvers          # AY (org.ay.ay) should be listed
minizinc --solver org.ay.ay model.mzn data.dzn
```

This integration currently requires that manual solver registration.
