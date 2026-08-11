# SAT Competition 2026 — Main track benchmarks

This directory holds **two different 400-instance sets**. Only one of them is the
set the competition actually scored. Read this before scoring anything.

## `official/` + `SC2026.official.csv` — USE THIS

The 400 instances the competition scored, taken from the `instanceid` column of
the organizers' per-instance results export:

    https://satcompetition.github.io/2026/downloads/scores.csv

That export has 12,400 rows = 31 sequential solvers x 400 instances, covering
the `main`, `main-ai`, `exp`, and `exp-ai` tracks. It is also the ground-truth
source: an instance's truth is the `vresult` agreed by the competition's own
verified solvers (191 sat / 166 unsat / 43 unresolved, **zero disagreements**
across all 31 solvers).

Provision with:

    python scripts/sat_bench/fetch_satcomp2026_official.py \
        --scores <path to scores.csv> --jobs 6

Every payload is verified by recomputing GBD's identity hash and requiring it to
equal the official `instanceid`. That hash is md5 over the CNF with comment
(`c`) and header (`p`) lines removed and all whitespace runs collapsed to single
spaces. This binds each file to the exact formula the competition scored,
independently of transport.

## `instances/` + `SC2026.pinned.csv` + `selected_benchmarks.csv` — NOT THE SCORED SET

These come from the organizers' `benchmark-compilation-script/selected_benchmarks.csv`
pinned at commit `6aed7e2d` (see `benchmarks/corpora.toml`, corpus
`satcomp-2026-main-selection`). Despite the official-looking provenance, this is
a *pre-final selection*, not the set that was scored.

Measured 2026-07-28, comparing the two manifests:

| check | result |
| --- | --- |
| `SC2026.pinned.csv` rows | 400 (only **391 distinct** hashes — 9 duplicates) |
| pinned hashes present in official `scores.csv` | **20 / 400** |
| `isohash2` values present in `scores.csv` | 0 / 400 |
| **shared files by sha256 content hash** | **20** |
| files only in pinned / only in official | 371 / 380 |
| total download size | 5.17 GB vs 2.24 GB |

So it is not an id-space mismatch — the two sets are genuinely different
collections of formulas.

**Scoring AY against `instances/` while comparing to published winner scores
would compare AY on one set of formulas to the winners on another.** The
resulting number would look well-formed and mean nothing.

`instances/` is retained because it is a legitimately pinned, hash-verified
corpus that is useful as an extra regression set. It is simply not SAT-COMP
2026 Main, and no competition claim may be based on it.

## 2025

`../satcomp2025-main/` **is** correct: its 400 pinned URIs match GBD's official
`track=main_2025` query exactly (400/400, verified 2026-07-29). Ground truth for
2025 is in `SC2025.groundtruth.json` (172 sat / 170 unsat / 58 unresolved),
queried from GBD's `result` attribute, because SAT-COMP 2025 published no
per-instance results export — only aggregate slides.
