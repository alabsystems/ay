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
compatibility. Wholesale copies of upstream tools live only under
`third_party/` (next section).

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
- **TLA+ / TLC** (`tla2tools.jar`) — an optional external tool. Supply it
  through `TLC_BIN` or `TLA2TOOLS_JAR`; it is not vendored here.
- **DRAT/LRAT proof checkers** — used externally to cross-check emitted proofs
  during testing. They are not part of the published Cargo packages.

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

## A Note On GPL-Sensitive Material

LoAT material is treated strictly as reference. AY source may cite LoAT for
algorithm behavior or for its papers, but does not claim Apache relicensing of
any LoAT code.
