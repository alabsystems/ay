# Proof-Complexity Hard-Family Corpus Slice

This directory records the small tracked SAT hard-family slice for issue #8890.
It does not duplicate benchmark inputs. `manifest.csv` points at existing
tracked DIMACS files and records the provenance and run-output contract needed
by ProofReplay/Omega proof-complexity dashboards.

## Scope

The initial slice covers these required families:

- PHP: `benchmarks/sat/unsat/php_4_3.cnf`
- Tseitin: `benchmarks/sat/unsat/tseitin_grid_3x3.cnf`
- parity/XOR: `benchmarks/sat/unsat/parity_6.cnf`
- random k-CNF: `benchmarks/sat/unsat/random_3sat_50_213_s12345.cnf`
- crypto/XOR: the SAT-COMP 2024 Ascon hash UNSAT sample recorded in
  `benchmarks/sat/satcomp2024-sample/manifest.csv`

The slice is a readiness artifact, not a score-bearing SAT-COMP result. Any
run that claims proof-complexity evidence from this corpus must record the
metrics below for every selected row.

## Run Output Contract

Dashboard-ready run rows must include:

- `case_id`
- `git_commit`
- `command`
- `solver_status`
- `expected_result`
- `solver_time_ms`
- `proof_size_bytes`
- `feature_usage_json`
- `certificate_replay_status`

UNSAT rows require `certificate_replay_status=passed` when a proof is emitted.
If a run mode cannot emit or replay a certificate, the row must record an
explicit non-score-bearing status and a reason in the run artifact.

## Files

- `manifest.csv` - corpus metadata, file hashes, expected results, and required
  measurements.
- `benchmarks.txt` - explicit benchmark list consumable as a `ay-bench`
  `list_file`.

## Acceptance Gates

Before moving issue #8890 forward, run:

```bash
python3 -m pytest -q tests/test_proof_complexity_hard_corpus.py
git diff --check
```
