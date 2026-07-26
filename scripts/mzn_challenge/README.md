# MiniZinc Challenge 2025 — retroactive scoring harness

Goal: **retroactively win the [MiniZinc Challenge 2025](https://www.minizinc.org/challenge/2025/)**
by improving AY's CP engine. This directory measures where AY stands against the
real 2025 field, using the official pairwise-Borda scoring.

## What's here
- `score.py` — the pairwise scorer. **Validated to 0 mismatches** against the
  official precomputed 42×42×100 score tensor in `results-2025.json`
  (`python3 score.py <results.json>` re-runs the validation).
- `score_ay.py` — appends AY as a solver, prints its total score and rank in a
  category (`fd`/`free`/`par`). Reports both the OFFICIAL score (time-split
  ties) and a QUALITY-ONLY score (ties→0.5) — the latter removes the
  hardware-relative time confound because competitor and AY timings come from
  different hardware.
- `run.py` — drives `minizinc --solver org.ay.ay --output-objective -s -t <ms>`
  over all 100 instances; emits a run vector `{status, objective, time_ms}`.
- `setup.sh` — builds the Rust CLI and reconstitutes the toolchain + corpus on
  a fresh machine through the size/SHA-pinned `ay corpus` manifest entries.

## The field & scoring
42 solver-configs, 20 problems, 100 instances (5 each). Categories: **Fixed**
(respect the model's search annotation), **Free** (`-f`), **Parallel** (`-p 8`),
Local Search. OR-Tools CP-SAT swept all four in 2025. Chuffed (LCG, AY's
architectural sibling) and Gecode are organizer reference solvers.

Per instance, each ordered solver pair scores 0/0.5/1: a feasible solution beats
none; for optimisation a strictly better objective wins (loser 0.0 if the winner
proved optimality, else 0.5); equal quality splits by whole-second time
(satisfaction problems ignore the completeness distinction). See `score.py`.

## Usage
```sh
bash scripts/mzn_challenge/setup.sh                       # one-time
cargo build --release -p ay --features cli --bin ay
python3 scripts/mzn_challenge/run.py 1200000 free 6       # full 1200s budget
python3 scripts/mzn_challenge/score_ay.py \
    benchmarks/minizinc/challenge-2025/runs/ay-free-1200s.json free
```
Short budgets (e.g. `60000`) give fast iteration signal; the official challenge
budget is **1200000 ms**. Corpus + runs live in
`benchmarks/minizinc/challenge-2025/` (gitignored); models and instances are in
`mznc2025_probs/`, and the immutable official field snapshot is
`results-2025.json`.

## Key finding (baseline)
Because AY ships no MiniZinc globals library, every model flattens with the
`std` library, which **decomposes all global constraints** into primitives —
so AY's native propagators (alldifferent-AC, cumulative, disjunctive, table,
circuit) are never exercised, and large instances explode (ihtc-kletzander:
5.3M reified constraints). Closing this is the #1 lever. See
the development design notes.
