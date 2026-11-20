# Third-Party Notices

This document records the outside projects that AY borrows ideas from, vendors
as external tools, compares against, or keeps around as reference material. It
is an attribution aid, not a full software bill of materials and not a license
grant. Checkout metadata for anything cloned under `reference/` lives in
`reference/SOURCES.md`.

## Algorithms And Interfaces Referenced In Tracked Code

The crates below study these upstream projects at the algorithm or
interface level. Within the `crates/` tree, no upstream code is copied
wholesale; the relation is one of reference and (in the Z3 case) wire
compatibility. Vendored components are recorded in the sections below.

- **Z3** (MIT) — consulted for EUF explanation/proof structures, PDR pieces in
  the spirit of Spacer, arithmetic compatibility behavior, and a Z3-compatible
  FFI surface.
- **Golem** (MIT) — consulted for the CHC DAR, IMC, LAWI, and MBP routines and
  related portfolio and termination handling.
- **CaDiCaL** (MIT) — consulted for SAT inprocessing, proof-checking parity, and
  covered-clause coverage routines.
- **Bitwuzla** (MIT) — consulted for bit-vector preprocessing and normalization.
- **Choco-solver** (BSD-4-Clause) — the CP alldifferent bounds-consistency
  propagators (`crates/ay-cp/src/propagators/alldifferent.rs` and
  `shifted_alldifferent.rs`) port the union-find structure of Choco's
  `AlgoAllDiffBC.java` (IMT Atlantique) and carry its BSD-4-Clause
  attribution in their file headers.
- **CVC5** (BSD-3-Clause) — consulted for string solving and quantifier
  strategy.
- **Kissat** (MIT) — the hash-cons term-store mark-compact collector
  (`crates/ay-core/src/term/compact.rs`) ports Kissat's arena-compaction
  strategy from `compact.c`, and dense occurrence-list propagation for
  inprocessing (`crates/ay-sat/src/solver/propagation_dense.rs`) is a port of
  `propdense.c`. Both carry the attribution in their file headers.
- **CryptoMiniSat** (MIT) — intree probing
  (`crates/ay-sat/src/solver/inprocessing/intree.rs`) is ported from
  CryptoMiniSat's `intree.cpp` and carries the attribution in its file header.
- **Pumpkin** (MIT) — the disjunctive (unary resource) edge-finding propagator
  and its Theta-Lambda tree
  (`crates/ay-cp/src/propagators/disjunctive/mod.rs` and
  `theta_lambda_tree.rs`) are ported from Pumpkin's propagators of the same
  names, with the attribution in their file headers.
- **OpenSMT** (MIT) — decomposed Farkas interpolation
  (`crates/ay-chc/src/farkas_decomposition/mod.rs`) is ported from OpenSMT's
  `FarkasInterpolator.cc` and carries the attribution in its file header.
- **Eldarica** (BSD-3-Clause) — forward/backward interval propagation over
  integer CHC systems
  (`crates/ay-chc/src/transform/interval_propagation.rs`) ports the idea of
  Eldarica's `IntervalPropagator`, with the attribution in its file header.

## Vendored Components (`third_party/`)

Unlike the references above, these are wholesale copies of upstream tools.
Each keeps its upstream license (see the LICENSE file in its directory); none
is relicensed by AY, and none is part of any published Cargo package. They are
built and run as external checker binaries.

- **cake_lpr** under `third_party/cake_lpr/` — the formally verified LPR/LRAT
  proof checker produced with the CakeML toolchain, used by `ay check` as an
  optional external trust anchor. Covered by the CakeML BSD-style license
  reproduced in `third_party/cake_lpr/LICENSE` (Heule, Myreen, Tan, and the
  CakeML contributors). The vendored copy includes the prebuilt verified
  ARMv8 assembly blob `cake_lpr_arm8.S` emitted by the CakeML compiler; the
  x64 `cake_lpr.S` is not vendored (see `third_party/cake_lpr/README.md`).
- **dpr-trim** under `third_party/dpr-trim/` — Marijn Heule's DPR proof
  trimmer and companion tools (`dpr-trim`, `lpr-check`, `compress`,
  `decompress`), an optional external checker. MIT: each source file carries
  the license header, and `third_party/dpr-trim/LICENSE` reproduces it.
- **dsr-trim** under `third_party/dsr-trim/` — substitution-redundancy (SR)
  proof checking and trimming tools, an optional external checker.
  Apache-2.0 (`third_party/dsr-trim/LICENSE`).

## Reference And Comparison Material In The Tree

- **LoAT CHC-COMP wrapper** under `reference/loat-chc-comp-2025/` — a snapshot
  kept only for comparison. Upstream LoAT licensing governs it; see the local
  README and the upstream distribution. It is not relicensed by AY and is not
  part of any published Cargo package.
- **Verus** (MIT, "Copyright (c) 2021 The Verus Contributors") — SMT-LIB
  queries that Verus generated, and reductions of them, embed Verus's AIR
  prelude text. Verus's MIT notice below covers every such query in the tree.
  Those present are test and regression inputs:
  - the regression `benchmarks/smt/wrong-verdict/sat_verus_zero_divisor_after_int_const_subst.smt2`
    and its twin `unsat_verus_zero_divisor_after_int_const_subst_twin.smt2`,
    with Verus's push/pop, get-info and rlimit commands removed (not part of
    any Cargo package);
  - the ay-dpll test fixtures `crates/ay-dpll/tests/fixtures/verus_demand_flush_closure.smt2`
    and `verus_demand_flush_closure_sat.smt2`;
  - the delta-debugged reductions inlined in
    `crates/ay-dpll/tests/group_quantifiers/fuel_guard_verus_reductions.rs` and
    `fuel_guarded_definitions.rs`.

  Verus's MIT notice:

  > MIT License
  >
  > Copyright (c) 2021 The Verus Contributors
  >
  > Permission is hereby granted, free of charge, to any person obtaining a copy
  > of this software and associated documentation files (the "Software"), to deal
  > in the Software without restriction, including without limitation the rights
  > to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
  > copies of the Software, and to permit persons to whom the Software is
  > furnished to do so, subject to the following conditions:
  >
  > The above copyright notice and this permission notice shall be included in all
  > copies or substantial portions of the Software.
  >
  > THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
  > IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
  > FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
  > AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
  > LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
  > OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
  > SOFTWARE.
- **TLA+ / TLC** (`tla2tools.jar`) — an optional external tool. Supply it
  through `TLC_BIN` or `TLA2TOOLS_JAR`; it is not vendored here.
- **DRAT/LRAT proof checkers** — used externally to cross-check emitted proofs
  during testing. They are not part of the published Cargo packages.

## Test Material Copied From Upstream

- **VeriPB** (MIT OR Apache-2.0, at the recipient's option; used here under
  MIT) — the checker-soundness fixtures in `ci/veripb-soundness/` are AY's own,
  but a few of their files come from VeriPB's test suite
  (`tests/instances/`) at the commit pinned in `ci/veripb.pin`. The three
  positive controls the fixture README names are VeriPB's own tests:
  `20-output-guarantee-solx-unguarded/variants/redundance-export-valid/`
  (`decision_output`),
  `21-sol-then-obji-evades-equienum/variants/equioptimal-with-soli/`
  (`optimization_output_opposing_lits_objective`), and
  `15-order-aux-var-not-private/variants/aux-vars-in-scope-valid/valid.pbp`,
  which is `dominance_with_aux_vars.pbp` with a header comment and one `rup`
  step added and its `conclusion NONE` changed to `conclusion UNSAT`. Some
  one- to three-line OPB formulas elsewhere in that directory are also
  byte-identical to upstream instances. VeriPB's MIT notice, which covers them:

  > MIT License
  >
  > Copyright (c) 2022-2025 Andy Oertel
  >
  > Permission is hereby granted, free of charge, to any person obtaining a copy
  > of this software and associated documentation files (the "Software"), to deal
  > in the Software without restriction, including without limitation the rights
  > to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
  > copies of the Software, and to permit persons to whom the Software is
  > furnished to do so, subject to the following conditions:
  >
  > The above copyright notice and this permission notice shall be included in all
  > copies or substantial portions of the Software.
  >
  > THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
  > IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
  > FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
  > AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
  > LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
  > OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
  > SOFTWARE.

  The VeriPB checker itself is not vendored: it is built from upstream at the
  pinned commit, and the reviewed patch applied on top of it is kept in the
  development tree only.

## Where The References Live In Source

The clearest in-source pointers, for anyone tracing a reference back to its
origin:

- `crates/ay-chc/src/dar/mod.rs`, `imc/mod.rs`, `lawi/solver.rs`, and
  `mbp/mod.rs` — Golem DAR/IMC/LAWI/MBP.
- `crates/ay-sat/src/cce/cover.rs` and `crates/ay-sat/src/solver/reap.rs` —
  CaDiCaL covered-clause and reap routines.
- `crates/ay-dpll/src/preprocess/normalize_eq_bv_concat/mod.rs` — Bitwuzla.
- `crates/ay-cp/src/propagators/alldifferent.rs` and
  `crates/ay-cp/src/propagators/shifted_alldifferent.rs` — Choco-solver.
- `crates/ay-theories/euf/src/explain.rs` and
  `crates/ay-theories/lia/src/gcd_tableau.rs` — Z3 EUF and arithmetic.
- `crates/ay-core/src/term/compact.rs` and
  `crates/ay-sat/src/solver/propagation_dense.rs` — Kissat arena compaction
  and dense propagation.
- `crates/ay-sat/src/solver/inprocessing/intree.rs` — CryptoMiniSat intree
  probing.
- `crates/ay-cp/src/propagators/disjunctive/mod.rs` and
  `crates/ay-cp/src/propagators/disjunctive/theta_lambda_tree.rs` — Pumpkin
  disjunctive edge-finding.
- `crates/ay-chc/src/farkas_decomposition/mod.rs` — OpenSMT Farkas
  interpolation.
- `crates/ay-chc/src/transform/interval_propagation.rs` — Eldarica interval
  propagation.

## A Note On GPL-Sensitive Material

LoAT material is treated strictly as reference. AY source may cite LoAT for
algorithm behavior or for its papers, but does not claim Apache relicensing of
any LoAT code.


## Integrated VeriPB checker

`vendor/veripb` contains the VeriPB checking libraries by Andy Oertel and
contributors, plus maintained ALab fixes. It is licensed under MIT OR
Apache-2.0; both original license texts are retained in that directory.
The upstream is <https://gitlab.com/MIAOresearch/software/VeriPB>. AY maintains
this cohort as integrated functionality; it is not a separate ALab product.
