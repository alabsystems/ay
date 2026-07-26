# SMT-COMP 2025 benchmark selections (beachhead divisions)

Per-division selection manifests for an SMT-COMP 2025 evaluation. One JSON object per line:
`{relpath, logic, family, name, expected}`. `relpath` follows the
`Smt2File.path()` convention of `smtcomp/defs.py`
(`(non-incremental|incremental)/<LOGIC>/<family...>/<name>`) and resolves
relative to `benchmarks/smtlib-2025/`.

## Provenance

- **Selection source:** the unique benchmark file sets appearing in the official
  results data of github.com/SMT-COMP/smt-comp.github.io at tag **`smtcomp25`**
  (commit `b0faba0`): `data/results-{sq,mv,uc,inc}-2025.json.gz`, restricted to
  each division's logics. Track names as in the data: `SingleQuery`,
  `ModelValidation`, `UnsatCore`, `Incremental`. This is the as-run selection
  (drawn by the competition with seed **757067271**, the published 2025
  competition seed: NYSE Composite 2025-06-30 open 20338.41 → 2033841 +
  755033430); we take the file sets from the results rather than re-running the
  sampler, avoiding a second implementation of the selection procedure.
- **Benchmark statuses:** `data/benchmarks-2025.json.gz` (same tag).
- **Corpora:** SMT-LIB release 2025 (version 2025.05.22), Zenodo record
  **15493090** (non-incremental: `QF_DT`, `QF_UFDT`, `QF_LRA`, `QF_RDL`) and
  **15493096** (incremental: `QF_LRA`), per-logic `.tar.zst` archives, md5
  verified against the Zenodo file listing, extracted 2026-07-08 into
  `benchmarks/smtlib-2025/` (trees gitignored via the local `.gitignore`).
- The selections are re-derivable from the repo tag + records above.

## Divisions present

| Track | Division | Rows | Derived |
|---|---|---|---|
| UnsatCore | QF_Datatypes | 400 | earlier session |
| UnsatCore | **QF_LinearIntArith** | **1069** | **2026-07-26 (this file's provenance rules, re-derived from the pinned tag)** |
| SingleQuery / ModelValidation / Incremental | see files | — | earlier sessions |

`UnsatCore/QF_LinearIntArith.jsonl` was derived 2026-07-26 by exactly the
procedure documented above, and the derivation was VALIDATED by re-deriving
`UnsatCore/QF_Datatypes.jsonl` with the same code first and reproducing its 400
rows (QF_DT 300 + QF_UFDT 100). The division spans three logics —
**QF_LIA 964 + QF_IDL 100 + QF_LIRA 5 = 1069**, matching the official division
size on smt-comp.github.io/2025/results/qf_linearintarith-unsat-core. Expected
provenance: 1035 `known` (official status), 33 `sound-consensus`, 1 `unknown`;
distribution 1068 `unsat` + 1 `unknown`. All 7 UnsatCore-track solvers are
0-error by the rule below (none contradicted a known status anywhere in the
track), so rule 2 had a 7-solver quorum available.

Official 2025 bar for this division (sequential): Yices2 **3,580,653** (968/1069
solved), SMTInterpol 3,234,355, cvc5 2,189,130; OpenSMT scored 3,539,809 but
recorded **36 errors** and OpenSMT (min-ucore) 32 — the 0-error discipline is
itself worth points here, and AY's UC path cannot emit an invalid core by
construction.

## `expected` field

1. `status` from `benchmarks-2025.json.gz` when it is `sat`/`unsat`;
2. else the **sound status**: the unanimous `sat`/`unsat` answer among 0-error
   solvers of that track, where a solver is 0-error iff it never contradicted a
   known benchmark status anywhere in that track's 2025 results (excluded on
   that basis: SQ track — Amaya, COLIBRI, SMTInterpol, 1 error each; the
   SMTInterpol error is in UFDTLIRA, outside these divisions);
3. else `"unknown"`.

No conflicting definitive answers exist between any two solvers (0-error or
not) inside any of these divisions, so rule 2 never had to arbitrate a
disagreement. Exactly 3 unknown-status SQ `QF_Datatypes` benchmarks were
answered only by SMTInterpol; per the conservative rule they remain
`"unknown"` (conflict-free, so treat SMTInterpol-vs-AY disagreement there as a
red flag anyway). Incremental files carry no single status (many `check-sat`s),
hence `"unknown"`.

## Verification (2026-07-08)

Every manifest line resolves to an extracted file (`resolved == lines`), and
every count matches the official 2025 division size:

| Manifest | lines | resolved | logic split | expected split |
|---|---|---|---|---|
| `SingleQuery/QF_Datatypes.jsonl` | 552 | 552 | QF_DT 352, QF_UFDT 200 | sat 161, unsat 285, unknown 106 |
| `ModelValidation/QF_Datatypes.jsonl` | 1943 | 1943 | QF_DT 1840, QF_UFDT 103 | sat 1943 |
| `UnsatCore/QF_Datatypes.jsonl` | 400 | 400 | QF_DT 300, QF_UFDT 100 | unsat 400 |
| `SingleQuery/QF_LinearRealArith.jsonl` | 842 | 842 | QF_LRA 595, QF_RDL 247 | sat 441, unsat 364, unknown 37 |
| `ModelValidation/QF_LinearRealArith.jsonl` | 606 | 606 | QF_LRA 497, QF_RDL 109 | sat 606 |
| `Incremental/QF_LinearRealArith.jsonl` | 10 | 10 | QF_LRA 10 | unknown 10 |

Notes: MV manifests are all-`sat` (586/606 LRA and all 1943 DT from benchmark
status; the remainder from validated-model unanimity — an MV result of `sat`
in the results data means the model passed validation). UC is all-`unsat` by
construction. The competition run protocol strips `(set-info :status)` before
solving; the extracted files here are the pristine SMT-LIB release, so strip at
harness time, not on disk.
