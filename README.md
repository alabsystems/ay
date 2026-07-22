<div align="center">
  <h1>AY</h1>
  <p><strong>Solve constraints. Inspect models. Check certificates.</strong></p>
  <p>A proof-oriented SAT, SMT, and CHC solver in Rust for Z3-compatible workflows,
  with companion PB, MaxSAT, QBF, CP, and LP/MILP engines.</p>
  <p>
    <a href="#quick-start">Quick start</a> ·
    <a href="#check-ays-answers-without-trusting-ay">Check the answers</a> ·
    <a href="#use-ay">Use AY</a> ·
    <a href="#capability-grid">Capabilities</a> ·
    <a href="LIMITATIONS.md">Limitations</a> ·
    <a href="#similar-programs">Similar programs</a> ·
    <a href="#benchmarks">Benchmarks</a> ·
    <a href="#roadmap">Roadmap</a> ·
    <a href="https://github.com/alabsystems/ay/issues">Issues</a>
  </p>
</div>

## What is AY?

AY turns formal constraints into models, counterexamples, optima, and
checkable certificates. It combines SAT, SMT, and constrained Horn clause
(CHC) solving with pseudo-Boolean optimization, MaxSAT, QBF, LP/MILP,
FlatZinc, AllSAT, and exact model counting in one Rust workspace.

A solver answers questions of the form "can all of these requirements hold at
once?" You state the constraints; the solver returns:

| Answer | Meaning | Artifact |
| --- | --- | --- |
| `sat` | The constraints can all hold. | A model, such as `x = 7, y = 0`. |
| `unsat` | No assignment satisfies them all. | A proof you can check independently. |
| `unknown` | AY could not justify either answer within its supported methods or limits. | The reason. |

Optimization adds "among the satisfying models, which is best?" — and AY can
prove the optimum is the optimum. Solvers sit underneath program verification,
scheduling, symbolic execution, theorem proving, circuit design, test
generation, configuration, planning, and optimization.

AY is inspired by Z3 and is being built as a drop-in replacement, with a
growing compatible command-line, C, and language-binding surface. Existing
tools can adopt AY one workflow at a time; new tools can embed its native
Rust APIs directly.

> **Status:** AY 0.x is under active development. Its tested Z3-compatible
> subset is useful today, with logic, API, and performance coverage expanding
> toward full parity.

## Quick start

Build AY from source with a current stable Rust toolchain:

```bash
git clone https://github.com/alabsystems/ay.git
cd ay
cargo build --release --locked -p ay --features cli --bin ay
export PATH="$PWD/target/release:$PATH"
```

> AY builds with stock stable Rust. The ALab
> [Trust](development-only integration) compiler — a
> verification-oriented Rust toolchain — will become the recommended way to
> build AY when it is published.

Solve a small integer problem from stdin:

```bash
ay --z3-mode -in <<'SMT'
(set-logic QF_LIA)
(set-option :produce-models true)
(declare-const x Int)
(declare-const y Int)
(assert (= (+ x y) 7))
(assert (> x 2))
(assert (< y 4))
(check-sat)
(get-model)
SMT
```

AY returns `sat` and a model, for example `x = 7, y = 0`.

Unsat answers carry proof. Solve the included unsatisfiable example and
re-check the emitted certificate with
[Carcara](https://github.com/ufmg-smite/carcara), the SMT community's
independent Alethe proof checker
(`cargo install --git https://github.com/ufmg-smite/carcara.git`):

```bash
ay examples/quickstart_unsat.smt2                 # prints: unsat
carcara check examples/quickstart_unsat.smt2.alethe examples/quickstart_unsat.smt2
```

The solver writes the `.alethe` proof next to the input, and Carcara replays
it independently of AY.

New to constraint solving? The interactive tutorial teaches it hands-on with
the real engine — five short levels from a first model to a first `unsat`:

```bash
ay tutorial --interactive
ay tutorial --challenge easy   # standalone puzzles: easy, medium, hard
```

## Check AY's answers without trusting AY

`sat` answers are easy to verify: substitute the model into your own
constraints with your own tools. The hard claims are `unsat` and *optimal* —
for those, AY emits the community-standard proof format wherever one exists,
and reduces its evidence to things you can already check where none does:

| AY's claim | Evidence AY emits | Check it with |
| --- | --- | --- |
| SAT `unsat` | DRAT/LRAT proof | [drat-trim](https://github.com/marijnheule/drat-trim), the SAT community's reference proof checker (`ay tool install drat-trim` builds it from source), plus standard LRAT checkers |
| SMT `unsat` | Alethe proof | [Carcara](https://github.com/ufmg-smite/carcara), the SMT community's independent Alethe checker |
| PB `unsat` **and optimality** | VeriPB proof, including `BOUNDS optimum optimum` | [VeriPB](https://gitlab.com/MIAOresearch/software/VeriPB), the PB Competition's own proof system |
| CHC SAFE | Invariant certificate | `scripts/chc_cert_check.py`, which discharges the obligations to an external SMT solver of your choice |
| CHC UNSAFE | Concrete counterexample over the *original* clauses, plus standalone SMT-LIB replay obligations | Any SMT-LIB solver, including Z3 |
| LP/MILP infeasible, LRA optimum | Exact rational Farkas certificates; MILP infeasibility as an integer split tree with Farkas leaves | Recombine the inequalities — elementary arithmetic, checkable with anything |
| Enumeration / counting / CP solutions | The models themselves | Substitution into your own model |

MaxSAT and QBF certificates are roadmap items; those paths return verdicts
and statistics today.

**Proofs are on by default.** Solve a file, get `unsat`, and AY writes the
proof next to the input (`problem.cnf.drat`, `problem.smt2.alethe`,
`problem.smt2.chccert`). If a proof cannot be produced, the verdict is still
reported — AY says the proof is missing rather than silently changing the
answer. Choose how strict to be:

| Mode | What you get |
| --- | --- |
| default | verdict + proof file when possible; a missing proof never changes the verdict |
| `--proof FILE` | verdict + proof at FILE — or the run **fails**; never an answer without the artifact |
| `--self-check` | `sat`/`unsat` only when AY has verified its own evidence (model re-evaluated, refutation proved); anything else becomes `unknown` |
| `--strict-proofs` | any path that would trust an unproven step returns `unknown` instead |
| `--no-proof` | verdict only, no proof files (benchmarking) |
| `--competition` | raw-speed mode: no default proofs or re-checks; core soundness gates stay on |

Beyond external checkers, the shipped
[`verification/lean`](verification/lean) project states soundness theorems for
selected solver kernels in Lean 4, and the ALab
[Clean](development-only integration) proof kernel reconstructs
supported SAT, SMT, arithmetic, and Farkas evidence inside a minimal,
auditable kernel. `ay check` validates SAT proof artifacts in-tree.

## Use AY

### Command line

AY auto-detects its primary input formats and exposes dedicated commands for
the other solver families:

```bash
ay problem.smt2                       # SMT-LIB 2.6
ay problem.cnf                        # DIMACS SAT
ay horn-clauses.smt2                  # HORN logic selects CHC
ay pb solve optimization.opb          # pseudo-Boolean decision or optimization
ay maxsat solve weighted.wcnf         # weighted MaxSAT
ay qbf solve quantified.qdimacs       # quantified Boolean formulas
ay lp solve model.mps                 # LP / MILP
ay flatzinc solve model.fzn           # constraint programming / MiniZinc output
ay allsat formula.cnf                 # enumerate satisfying assignments
ay model-count formula.cnf            # exact model count
ay tool <list|install|which|verify>   # external checkers/reference solvers (reference/tools.toml)
ay scripts <list|show|run|check>      # the maintained-script index (scripts/index.toml)
ay bench compare <list|show|check>    # competition registry + host preflight (needs --features bench)
```

Use `ay --help`, `ay <command> --help`, and `ay --features` to inspect the
commands, build metadata, accepted SMT logics, and proof coverage in the
binary you actually built.

### In place of Z3

AY speaks Z3's language: SMT-LIB 2 input, `z3py`-style Python, and the
`(check-sat)` / `(get-model)` / `(get-proof)` workflow all behave the way a
Z3 user expects.

| Z3 | AY |
| --- | --- |
| `z3 -smt2 file.smt2` | `ay --z3-mode file.smt2` |
| `z3 file.smt2` | `ay file.smt2` |
| `z3 -in` (stdin, incremental) | `ay -in` |
| `import z3` | `import ayz3 as z3` |
| `Solver()`, `Optimize()`, `s.add(...)`, `s.check()`, `s.model()` | identical |
| `(get-unsat-core)`, `(get-objectives)`, `(check-sat-assuming …)` | identical |

#### Replacing the z3 CLI

Point your workflow at the AY binary. Named `z3` (a symlink is enough), AY
selects its Z3-shaped transcript automatically; `--z3-mode` does the same
under any name. Z3's common flags (`-in`, `-t:`, `-model`, `key=value`) are
accepted, and unsupported options are rejected explicitly rather than
ignored, so a staged migration is easy to test:

```bash
mkdir -p target/ay-z3-shim
ln -sf "$PWD/target/release/ay" target/ay-z3-shim/z3
PATH="$PWD/target/ay-z3-shim:$PATH" z3 -smt2 examples/quickstart.smt2
```

#### Python

[`ayz3`](bindings/python/README.md) implements a growing core slice of z3py
over AY's C ABI. A typical migration changes the import and keeps the
constraint-building code:

```bash
python3 -m pip install ./bindings/python
```

```python
# import z3
import ayz3 as z3

x = z3.Int("x")
s = z3.Solver()
s.add(x > 2, x < 7)
assert s.check() == z3.sat
```

#### Compiled library

For programs linked against Z3's C API, AY ships a native C ABI and a
Z3-shaped C header ([`crates/ay-ffi/include/`](crates/ay-ffi/include/)), plus
C++, Java, JavaScript/WASM, and OCaml bindings built on it
([`bindings/`](bindings/)). Each surface exposes its tested subset and
reports unsupported calls explicitly; `ay z3-audit` and the capability grid
say exactly what is covered.

AY ships the same differential harness used in development, so you can
measure parity on your own problems against your own Z3:

```bash
# per-file: AY vs a reference Z3, with a verdict diff
ay diagnose --reference z3 problem.smt2

# the Python differential fuzzer (ayz3 vs real z3py), soundness oracle
python3 -m ayz3_fuzz --fragment qf_lia --count 500 --seed 1
```

### Embed in Rust

The native API constructs terms and solves in-process, without serializing
SMT-LIB or crossing a C boundary:

```toml
[dependencies]
ay-dpll = { git = "https://github.com/alabsystems/ay.git" }
```

```rust
use ay_dpll::api::{Logic, SolveResult, Solver, Sort};

let mut solver = Solver::try_new(Logic::QfLia).expect("QF_LIA");
let x = solver.declare_const("x", Sort::Int);
let zero = solver.int_const(0);
let positive = solver.try_gt(x, zero).expect("integer comparison");
solver.try_assert_term(positive).expect("Boolean assertion");

let details = solver.check_sat_with_details();
assert!(matches!(details.accept_for_consumer(), Ok(SolveResult::Sat)));
println!("x = {:?}", solver.value(x));
```

Pin a commit in production. A complete runnable version is
[`crates/ay-dpll/examples/native_api.rs`](crates/ay-dpll/examples/native_api.rs):

```bash
cargo run -p ay-dpll --example native_api
```

The in-tree interfaces also include a native C API, a Z3-shaped C header, a
header-only C++ wrapper, Java FFM bindings, JavaScript native/WASM bindings,
and OCaml bindings. Each binding exposes its tested subset and reports
unsupported calls explicitly.

## Why AY?

AY's contribution is the combination of capabilities that normally require
several separate integrations:

| Design choice | What it gives you |
| --- | --- |
| Z3-shaped adoption | Point a supported CLI workflow at AY, or migrate a z3py-style program to `ayz3`, before changing the rest of your application. |
| Checkable evidence | Proof, certificate, and validation artifacts alongside satisfiability, safety, `unsat`, and optimality results — replayable with independent tools. |
| One solver toolkit | One Rust workspace and CLI, with shared resource controls and evaluation conventions, across SAT, SMT, CHC, optimization, and counting. |
| Native Rust embedding | Construct and solve constraints in-process without a parser, subprocess protocol, or C boundary. |
| Sound by construction | An answer is emitted only when AY can stand behind it: `sat` models re-evaluate, `unsat` carries proof on supported paths, and anything unproven is `unknown`. |

This matters when a compiler needs both SMT queries and optimization, a model
checker moves between BMC and invariant synthesis, a theorem prover wants to
reconstruct a certificate, or an AI agent needs a deterministic checker for
several kinds of formal task: an LLM can propose, and AY can check.

## Capability grid

Coverage is fragment-specific. The grid names implemented paths and the
evidence they expose.

| Problem family | Entry point | Implemented surface | Evidence |
| --- | --- | --- | --- |
| SAT | DIMACS `.cnf` / `.dimacs` | CDCL, preprocessing/inprocessing, portfolios | Models, DRAT, LRAT |
| SMT | SMT-LIB 2.6 / native API | Arithmetic, UF, BV, arrays, FP, strings/sequences, datatypes, quantifiers; coverage varies by logic | Models, cores, Alethe, self-check |
| CHC / Horn | SMT-LIB `HORN` | Adaptive PDR/IC3, BMC, k-induction, CEGAR, IMC, DAR, and related engines | Invariants, traces, CHC certificates |
| Incremental SMT | `push` / `pop`, assumptions | Repeated checks on supported theory/API surfaces | Per-check models, cores, proof metadata |
| OMT | `minimize`, `maximize` | Linear arithmetic is the strongest path | Models, objective values, LRA Farkas certificates |
| MaxSMT | `assert-soft` | Weighted soft constraints on a dedicated path | Models and objective values |
| Pseudo-Boolean | `ay pb`, OPB / WBO | Decision and optimization | VeriPB proofs for `unsat` and optimality (opt-in) |
| MaxSAT | `ay maxsat`, WCNF | Weighted and unweighted instances | Models and objective values |
| QBF | `ay qbf`, QDIMACS | Quantified Boolean formulas | Verdict and statistics |
| LP / MILP | `ay lp`, MPS / CPLEX LP | Continuous and mixed-integer models | Primal solutions, bounds, Farkas certificates |
| Constraint programming | `ay flatzinc solve` | FlatZinc / MiniZinc adapter and developing global constraints | Solutions and objective values |
| Enumeration / counting | `ay allsat`, `ay model-count` | Full/projected AllSAT and exact/projected counting | Enumerated models or exact count |
| Embedding | Rust, C, Python, C++, Java, JavaScript/WASM, OCaml | In-tree bindings over shared solver cores | Binding and differential test suites |
| Z3 compatibility | Z3-style CLI, C header, `ayz3`, shaped bindings | Tested subset with explicit gap reporting | CLI smoke gate, differential tests, parity audit |

For the authoritative build-specific list of accepted SMT-LIB logics, proof
formats, proof theories, and compiled features, run `ay --features`.

## Novel improvements in AY

The foundations of AY — CDCL, DPLL(T), PDR/IC3, Farkas duality, branch and
bound — come from decades of solver research. AY's distinctive contribution is
how it composes them: recognize useful structure, select a suitable proof
method, and validate the result in the original problem's frame. The entries
below are concrete AY implementation contributions, not claims that their
underlying techniques began here.

### Theory and algorithms

- **Original-clause CHC replay.** AY backtranslates concrete counterexamples
  through datatype, array, bit-vector, ITE, and equality transformations, then
  checks a ground derivation over the original Horn clauses. Search can operate
  on a transformed problem while the final evidence speaks about the problem
  the user supplied. See the
  [ground-derivation checker](crates/ay-chc/src/ground_derivation/mod.rs).
- **Fail-closed partition rescue.** When an unsupported mixed-theory
  conjunction separates into symbol-disjoint components, AY can solve the
  components with established single-theory paths. UNSAT follows from a
  component; SAT is admitted only after model merging and full-formula checks.
  See [`partition_rescue.rs`](crates/ay-dpll/src/executor/partition_rescue.rs).
- **Exact optimization evidence.** AY can represent a MILP infeasibility proof
  as an integer split tree with exact rational Farkas leaves, independently
  checkable against the caller's model. Certificate-required mode returns a
  definite answer only when the bounded proof capture succeeds. See
  [`tree_cert.rs`](crates/ay-milp/src/tree_cert.rs).
- **Structure-directed exact solving.** Dedicated paths recognize algebraic
  forms such as market-split 0/1 equalities and switch to meet-in-the-middle
  or lattice methods, with candidate witnesses rechecked before admission. See
  [`market_split.rs`](crates/ay-pb/src/optimize/market_split.rs) and
  [`lattice.rs`](crates/ay-milp/src/lattice.rs).

### Engineering

- **Proof production off the hot loop.** The pseudo-Boolean decision solver
  streams cutting-planes events through a bounded ring to an asynchronous
  VeriPB serializer. Backpressure, serializer failure, or incomplete draining
  voids the certificate rather than committing partial evidence. See the
  [proof tap](crates/ay-pb/src/proof/tap/mod.rs).
- **A cooperative CHC portfolio.** Formula and graph features choose an engine
  order; later engines can reuse lemmas and hints through a shared blackboard;
  every accepted candidate crosses an original-problem validation firewall.
  See the [selector](crates/ay-chc/src/portfolio/selector.rs) and
  [acceptance gate](crates/ay-chc/src/portfolio/accept.rs).
- **Checked code without a shadow implementation.** The
  [Trust](development-only integration) toolchain machine-checks
  selected bounded kernels over the same source bytes compiled by Rust; this
  repository includes the corresponding source and exhaustive tests. This
  reduces drift between an executable function and a proof model. One example
  is [`ay-sat-congruence-core`](crates/ay-sat-congruence-core/src/lib.rs).
- **Compatibility as executable evidence.** The parity tooling loads AY and Z3
  independently, inventories symbols, isolates each corpus case in a child
  process, and records versions, hashes, timeouts, disagreements, unknowns,
  and crashes. It measures a named surface rather than turning one passing
  corpus into a universal claim. See
  [`ay-z3-parity`](crates/ay-z3-parity/src/main.rs).

## AY in ALab Systems

AY is exercised as infrastructure by the other ALab Systems projects:

| Project | How it uses AY |
| --- | --- |
| [Trust VC](development-only integration) / [Trust WP](development-only integration) | Lower Rust contracts and verification conditions to SMT, then retain AY's solve evidence for proof reconstruction. |
| [Trust MC](development-only integration) / [Ty](development-only integration) | Power bounded and symbolic model checking with SAT, CHC/PDR, k-induction, counterexample validation, and LRAT-backed hardware checks. |
| [Clean](development-only integration) | Discharge theorem goals with AY-backed tactics and reconstruct supported SAT, SMT, arithmetic, and Farkas evidence in the proof kernel. |
| [NN](development-only integration) / [NY](development-only integration) | NN exposes partial NY/AY verification hooks; NY uses AY's in-process MILP and SMT escalation paths for network properties, returning validated counterexamples and supported certificates. |
| [Trust IR](development-only integration) | Supply the typed compiler facts from which downstream verification conditions and solver artifacts are built. |

## Similar programs

People evaluating AY will often also consider Z3, cvc5, propositional SAT
solvers such as Kissat or CaDiCaL, CHC solvers such as Spacer, Golem, or
Eldarica, and optimization systems such as SCIP, HiGHS, or OR-Tools. Each has
a different center of gravity:

| Program | Primary focus | AY's focus |
| --- | --- | --- |
| [Z3](https://github.com/Z3Prover/z3) | General SMT, optimization, fixed points, tactics, and widely used APIs | A Z3-shaped adoption path backed by a Rust-native, proof-oriented multi-solver workspace |
| [cvc5](https://cvc5.github.io/) | Standards-oriented SMT, broad theories, proofs, and synthesis | SMT plus dedicated SAT, CHC, PB, MaxSAT, QBF, counting, and LP/MILP commands in one project |
| [Kissat](https://github.com/arminbiere/kissat) / [CaDiCaL](https://github.com/arminbiere/cadical) | Highly tuned propositional SAT | An integrated SAT core that also feeds theories, CHC, proofs, and higher-level tools |
| [Spacer](https://microsoft.github.io/z3guide/docs/fixedpoints/engineforpdr/) / [Golem](https://github.com/usi-verification-and-security/golem) / [Eldarica](https://github.com/uuverifiers/eldarica) | Constrained Horn clauses and invariant synthesis | An adaptive multi-engine CHC portfolio with original-problem validation before a result is published |
| [SCIP](https://github.com/scipopt/scip) / [HiGHS](https://highs.dev/) / [OR-Tools](https://developers.google.com/optimization) | Mathematical optimization and constraint programming | Dedicated optimization engines shipped beside logical solving in the same Rust workspace and CLI |

These programs are complementary reference points. AY is most distinctive
when Z3-shaped integration, native Rust embedding, several formal problem
families, and checkable result artifacts are useful in the same system.

## Benchmarks and competition readiness

AY distinguishes an **official competition result** from a **replay on
matched hardware** from a **laptop run** — a number never travels without its
class. The registry of official machine specs, budgets, scoring rules, and
recent winners for every competition lives in
[`benchmarks/comparisons.toml`](benchmarks/comparisons.toml) (researched from
the official sites, with citations) and is first-class in the CLI:
`ay bench compare list` shows it, and `ay bench compare check <id>` verifies
the current host against the cited official specs — run it on the benchmark
machine to learn whether a run there earns the `replay` class or is
`laptop-only`. Competitions AY would enter but cannot yet (XCSP³, CASC,
SyGuS) are recorded with `status = "unsupported"`, and every *not yet* across
this document is consolidated in the readiness file's
**Future functionality** table.

### Head to head with Z3

Every cell was verified by executing both solvers on concrete instances
against **Z3 5.0.0** (the latest release; commands in
[`benchmarks/COMPETITIONS.md`](benchmarks/COMPETITIONS.md)):

| Capability | Z3 | AY |
| --- | --- | --- |
| SMT-LIB 2.6, incremental, models, unsat cores | ✓ | ✓ |
| OMT (`minimize`/`maximize`) and MaxSMT (`assert-soft`) | ✓ incl. joint use | ◐ each alone; the joint combination deliberately returns `unknown` rather than a half-optimized answer |
| CHC / fixedpoint (HORN) | ✓ | ✓ plus an inductive-invariant certificate and replay obligations |
| Z3 tactic surface (`apply`, `check-sat-using`) | ✓ native engine | ◐ all 118 Z3 5.0.0 tactic + 42 probe names accepted with z3-style errors; `apply` runs real transforms, `check-sat-using` validates then solves with AY's engine |
| `unsat` proofs | ◐ own format, no independent checker | ✓ Alethe + DRAT/LRAT, replayed by Carcara / drat-trim |
| PB **certified** optimality | ✗ solves OPB, emits no certificate | ✓ VeriPB proof, verified by the official checker incl. `BOUNDS optimum optimum` |
| QDIMACS QBF / MPS LP / FlatZinc / AllSAT / model counting | ✗ | ✓ dedicated commands |
| DIMACS SAT | ✓ | ✓ (+ DRAT/LRAT proofs) |
| In-process Rust API | ◐ community FFI wrappers | ✓ native |
| Formally verified validators | ✗ | ✓ 11 theory validators + combination firewall in Lean 4, zero `sorry` |

Per-track readiness — what works today, verified by execution
(the full 77-row table with evidence and paste-able commands is
[`benchmarks/COMPETITIONS.md`](benchmarks/COMPETITIONS.md)):

| Competition | Ready today | Partial / not yet |
| --- | --- | --- |
| [SAT Competition](https://satcompetition.github.io/) | main (DRAT/LRAT verified by drat-trim), parallel (`--parallel N`), experimental | cloud (no distributed engine) |
| [SMT-COMP](https://smt-comp.github.io/) | single-query in the entered divisions (QF_LIA/IDL, QF_LRA, QF_BV, QF_UF/AX, QF_DT, QF_ABV/AUFBV/UFBV, QF_AUFLIA); incremental, unsat-core, model-validation conventions | quantified divisions, FP/strings combos, nonlinear (solve but not entered); QF_UFLIA withdrawn 2026-06-15 over a confirmed false-SAT — re-entry after the fix is proven |
| [CHC-COMP](https://chc-comp.github.io/) | LIA lin/nonlin (± arrays), ADT-LIA (± arrays), LRA-Lin, BV-Lin — with certificates | BV-Nonlin (honest `unknown` on a hard case) |
| [PB Competition](https://www.cril.univ-artois.fr/PB26/) | DEC/OPT linear **and nonlinear**, WBO, **certified tracks** (VeriPB-verified incl. optimality) | certified WBO (refused honestly) |
| [MaxSAT Evaluation](https://maxsat-evaluations.github.io/2024/) | exact weighted + unweighted, both wcnf formats; anytime via `--timeout` | certified, IPAMIR incremental |
| [QBF Gallery](https://qbf.pages.sai.jku.at/gallery/) | PCNF, 2QBF (QDIMACS, right exit codes) | QCIR, DQBF, certificates |
| [Model Counting Comp.](https://mccompetition.org/) | mc, wmc, pmc, pwmc — exact, competition output conventions | — |
| [MiniZinc Challenge](https://www.minizinc.org/challenge/) | fixed, free, open class (CP+SMT portfolio) | parallel (CP-sat only), local search, float variables |
| [MIPLIB](https://miplib.zib.de/) | plain `.mps` LP/MIP to proven OPTIMAL | `.mps.gz` |

AY has not yet entered these competitions; official scorecards will be linked
here as result packets exist. Each packet identifies the AY commit and binary,
reference-solver version, corpus revision, host and run class, budgets, proof
mode, checker verdicts, solved counts, wrong/invalid counts, and scoring rule.

### Generate the stats yourself

Every number AY states about itself is reproducible from the shipped tree
(each command below is tested; `ay bench` needs a `--features bench` build):

```bash
ay --features                     # 54 SMT logics, 4 proof formats, 12 proof theories, build provenance
ay z3-audit --scope cli-subset --inventory-only --summary-json audit.json
ay verifier-audit --consumer all --json surfaces.json   # 13 surfaces: 11 READY, 2 tracked gaps
ay diagnose --reference z3 examples/quickstart_unsat.smt2
ay corpus list                    # 27 corpora with pinned provenance
ay tool list                      # external checkers/solvers registry + install state
ay scripts list                   # every maintained script, indexed and grouped
ay bench compare list             # the competition registry: specs, budgets, winners
ay bench compare check <id>       # preflight a comparison on THIS host: replay-eligible or laptop-only
cd bindings/python && python3 -m ayz3_fuzz --fragment qf_lia --count 500 --seed 1
cd verification/lean && lake build   # the verified validators: 43 jobs, zero sorry
```

Reproduce a comparison locally (requires Z3 plus `curl`, `tar`, and `zstd`):

```bash
cargo build --release --locked -p ay --features bench --bin ay
./target/release/ay bench list
./target/release/ay corpus list

# Start with the small suite shipped in the checkout.
./target/release/ay bench run smt-local-suite \
  --ay ./target/release/ay \
  --reference-solver "$(command -v z3)" \
  --timeout 30 --runs 3 \
  --output ay-vs-z3-local.json

# Example: fetch one official SMT-LIB snapshot and compare AY with Z3.
scripts/download_smtcomp_benchmarks.sh --logic QF_BV
./target/release/ay bench run smt-smtcomp-qf-bv \
  --ay ./target/release/ay \
  --reference-solver "$(command -v z3)" \
  --output ay-vs-z3-qf-bv.json
```

The scorecard reports solved, unknown, timeout, mismatch, and timing data, so
a wrong answer remains visible instead of being averaged into a speed number.
See [`benchmarks/README.md`](benchmarks/README.md) for the corpus manager and
evaluation workflow.

## Roadmap

AY's roadmap is ordered by evidence:

1. **Publish a dependable 0.x distribution.** Reproducible source builds,
   multi-platform CI, signed release artifacts, package-manager installation,
   and public benchmark packets.
2. **Reach Z3 parity.** Close the remaining SMT-LIB, CLI, tactic, C API,
   binding, incremental, model, proof, and CHC gaps until the
   full-replacement gate passes.
3. **Deepen completeness and performance.** Current frontiers include arrays
   combined with arithmetic, strings and sequences, nonlinear and mixed
   arithmetic, quantifiers, large-theory combination, CHC invariant
   synthesis, and specialist-grade SAT/optimization performance.
4. **Expand independently checkable evidence.** Broaden end-to-end Alethe and
   certificate replay, reduce residual trusted steps, and add proof formats
   for MaxSAT and QBF.
5. **Compete in public.** Turn local replays into reproducible official
   SAT/SMT/CHC/PB/MaxSAT/counting/MiniZinc submissions and publish every
   result, including losses and invalid outputs.
6. **Improve the embedding story.** Stabilize the Rust API, finish the
   Z3-compatible surfaces, broaden language bindings, and ship native and
   WASM packages that work without a source checkout.

The 1.0 bar is a stable, distributable solver whose compatibility,
correctness, and performance claims survive its own audits and independent
checkers.

<details>
<summary><strong>Repository layout and corpus management</strong></summary>

## Repository layout

AY is a Cargo workspace. The main boundaries are:

| Path | Purpose |
| --- | --- |
| `crates/ay` | Unified command-line solver. |
| `crates/ay-sat` | CDCL SAT engine and proof generation. |
| `crates/ay-dpll` | DPLL(T) execution and SMT orchestration. |
| `crates/ay-theories/` | Arithmetic, UF, BV, arrays, strings, FP, datatype, and related theory solvers. |
| `crates/ay-chc` | CHC portfolio and certificate surfaces. |
| `crates/ay-pb`, `ay-maxsat`, `ay-qbf`, `ay-count` | Discrete optimization and counting engines. |
| `crates/ay-lp`, `ay-milp`, `ay-cp` | LP/MILP and constraint-programming paths. |
| `crates/ay-bindings`, `crates/ay-ffi` | Typed Rust API and native/Z3-shaped interfaces. |
| `bindings/` | Python, C++, Java, JavaScript/WASM, and OCaml adapters. |
| `benchmarks/`, `evals/` | Small fixtures, corpus metadata, and reproducible evaluation definitions. |
| `proofs/` | Proof fixtures and recorded proof artifacts. |
| `verification/` | Formal verification material, including the Lean 4 `AySoundness` project under `verification/lean`. |

Large competition corpora are fetched on demand rather than committed in
full. `ay corpus list` prints the catalog, defined in
[`benchmarks/corpora.toml`](benchmarks/corpora.toml):

```bash
ay corpus list
ay corpus download satcomp2024-sample
ay corpus download chc-comp-2025-benchmarks
ay corpus verify --all
```

</details>

## Developing and contributing

Start with the narrowest check that covers a change, then broaden it:

```bash
cargo check --workspace --all-targets
cargo test -p ay-sat
cargo test -p ay-dpll
cargo check -p ay --features cli
```

Solver changes should be checked against a reference solver and, where
possible, a proof or model checker. Benchmark evidence should always include
provenance and wrong/invalid counts, not only speed.

Contribution basics (build, test, licensing, reporting) are in
[`CONTRIBUTING.md`](CONTRIBUTING.md). See [`LIMITATIONS.md`](LIMITATIONS.md)
for known boundaries and caveats, [`SUPPORT.md`](SUPPORT.md) for help and
issue-reporting guidance, [`SECURITY.md`](SECURITY.md) for private
vulnerability reports, and [`CODE_OF_CONDUCT.md`](CODE_OF_CONDUCT.md) for
community expectations.

## Maintainer commands

AY ships the machinery that gates its own releases — the same commands the
project runs in CI. They are part of every build but kept out of the default
`ay --help` so the everyday verb set stays small; anyone can inspect and run
what a release must pass:

| Command | What it does |
| --- | --- |
| `ay gate` | Run the checked-in CI/release gates |
| `ay launch-gate` | Run the release-readiness gate |
| `ay release` | Generate and verify release evidence |
| `ay launch-packet` | Generate launch benchmark-packet metadata |
| `ay verifier-audit` | Audit AY as the SMT backend for Creusot / Why3 / Verus |
| `ay submission` | Generate competition submission skeletons |
| `ay competition-jit` | Competition matrix, gate, and ROI tooling |
| `ay bisect` | Localize a soundness bug by bisecting feature flags |

Run `ay <command> --help` for any of them.

## License

Apache License 2.0. See [`LICENSE`](LICENSE). AY was created by Andrew Yates.

Vendored tools under `third_party/` and reference material under `reference/`
keep their own licenses, recorded in [`THIRD_PARTY.md`](THIRD_PARTY.md).
Benchmark instance files under `benchmarks/` are third-party data distributed
under their own terms.
