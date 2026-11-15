# AY

A constraint solver in Rust. You give it a logical problem; it tells you whether
the problem has a solution, shows you one if it does, and can hand you a
machine-checkable proof when it says there is none.

AY covers SAT, SMT, Horn clauses, pseudo-Boolean, MaxSAT, QBF, LP/MILP,
FlatZinc, and model counting in one binary.

## The idea

A solver answers one question: *can all of these requirements hold at once?*

| Answer | Meaning | What you get |
| --- | --- | --- |
| `sat` | Yes | A solution, e.g. `x = 7, y = 0` |
| `unsat` | No | A proof, which you can check with a tool that isn't AY |
| `unknown` | AY couldn't decide | The reason |

The `unsat` row is the point of the project. Every solver can claim "no
solution exists" — a wrong claim there is silent and expensive. AY writes a
proof of that claim to a file, and ships checkers that replay it
independently. You do not have to trust the search to trust the answer.

## Build

AY builds with ALab's Trust compiler, which `rust-toolchain.toml` pins. Install
[aterm](https://github.com/alabsystems/aterm#install); atpkg installs Trust
(`aterm pkg install trust` does it by hand; atpkg ships it for Apple-silicon
macOS today).

```bash
git clone https://github.com/alabsystems/ay.git
cd ay
targo --unverified build --release -p ay --features cli --bin ay
export PATH="$PWD/target/release:$PATH"
```

**The `--features cli` is not optional.** Without it Cargo builds the library
and produces no executable, with no error explaining why.

A **public snapshot's** `.cargo/config.toml` carries no verification policy.
This **development** repo's requires `certify` policy on every unit, with no
dependency or build-script exemptions. Name a lane:

```bash
targo --unverified test -p ay-sat            # everyday: proof pipeline off,
                                             # no proof claim
offline deductive checker check -p ay-sat                  # fail-closed, per-unit proof report
offline deductive checker test --allow-l0-gaps -p ay-sat   # advisory: run tests while the
                                             # proof ratchet is still open
```

The required posture is not a claim that the workspace currently discharges
it — `ay-sat` alone still reports thousands of Level-0 gaps, mostly in derived
`Clone`/`Default`/`thiserror` impls. See [CONTRIBUTING.md](CONTRIBUTING.md).

## Try it

Give `ay` a file. It works out the format from the contents.

```bash
$ ay examples/quickstart.smt2
c ay.session.start build.version=0.27.0 build.commit=…
c writing Alethe proof to examples/quickstart.smt2.alethe on unsat
sat
(model
  (define-fun y () Int 0)
  (define-fun x () Int 7)
)
c ay.session.end exit.code=0 wall_time_ms=2
```

Lines starting with `c` are comments recording which build ran and where a
proof would go. `--z3-mode` suppresses them if you want bare Z3-shaped output.

An unsatisfiable problem writes a proof next to the input, then re-checks it:

```bash
$ ay problem.cnf              # DIMACS CNF
unsat                         # also writes problem.cnf.drat

$ ay check drat problem.cnf problem.cnf.drat
s VERIFIED
```

For SMT-LIB input the proof is [Alethe](https://verit.loria.fr/documentation/alethe-spec.pdf),
which the external checker `carcara` reads:

```bash
$ ay problem.smt2             # writes problem.smt2.alethe on unsat
$ carcara check problem.smt2.alethe problem.smt2
valid
```

Be aware that AY still emits some theory steps as opaque `trust` holes that
carcara cannot expand. Fully hole-free proofs are demonstrated today only on
small hand-written formulas, not across the board.

Pinned carcara also parses neither AY's `Seq`, `FloatingPoint` and `Char`
sorts nor symbols spelled with the AY/Z3 `\|` escape extension, nor a problem
written with constructs AY accepts and its parser refuses: a qualified
`(as C S)` on a constructor of a non-parametric datatype, Z3 names such as
`bv2nat`, `is-C` or `iff`, an implicit Int/Real coercion, or a use of a
`define-const` symbol. AY still writes the certificate its own strict checker
accepted for those problems and says so on the `c ay.proof.certificate` line
as `carcara_surface=unsupported`
(the reason follows on a `c warning:` line; a library consumer reads
`UnsatProofArtifact::carcara_surface`, or takes the problem-scoped document and
its verdict from one rendering with
`Executor::try_export_last_proof_alethe_for_problem_scope_with_carcara_surface`).
Such a verdict stands on AY's strict checker alone: `--rigor strict` and
`--rigor certified` (legacy spellings `--strict-proofs` / `--self-check`)
refuse it with that reason.

Pinned carcara and Clean's vendored carcara (which external-codegen replays with) also
disagree on three spellings: the `bitblast_ashr` overshift layer,
`zero_extend`, and the `bitblast_udiv`/`bitblast_urem` divider. They also
disagree on one rule, `dt_project`, which checks a datatype selector over a
constructor (`(= (fst (mk a b)) a)`): pinned carcara has no datatype rule and
answers `unknown rule`, which rejects the whole document. By default AY
prints Clean's (each names the Clean rule that admits it,
`CleanOnlySpelling::consumer_rule`), and a certificate that keeps one says
`carcara_surface=clean-dialect` (`CarcaraSurface::CleanDialect` on a library
`UnsatProofArtifact`): pinned carcara refuses it. A problem pinned carcara
cannot parse is `unsupported` in either dialect. `--alethe-dialect
pinned-carcara` (`Executor::set_alethe_dialect`, `Solver::set_alethe_dialect`)
prints the pinned spelling where one exists and is true, and prints the
`dt_project` step as a `hole`. To check a QF_DT certificate with pinned
carcara, write it with `--alethe-dialect pinned-carcara`. See LIMITATIONS.md.

Check a certificate as `carcara check -- PROOF PROBLEM`. A `let` the problem
writes is eliminated with `:rule let`, which pinned carcara checks only in
that invocation, never under `--expand-let-bindings`; such a certificate says
`carcara_surface=without-let-expansion`.

`ay tutorial` is an interactive walkthrough if you'd rather start there.

## Commands

```
ay solve FILE      SMT-LIB 2.6, DIMACS CNF, or Horn clauses (the default)
ay allsat          enumerate every solution of a CNF
ay model-count     exact model counting
ay simplify        rewrite an SMT-LIB formula
ay check           replay a DRAT / LRAT / DPR / SR / VeriPB proof, or validate a model
ay diagnose        investigate a suspected wrong answer
ay maxsat          WCNF
ay pb              pseudo-Boolean, OPB / WBO
ay qbf             QDIMACS
ay lp              MPS / LP
ay flatzinc        FlatZinc / MiniZinc
ay tutorial        interactive lessons
ay commands        this list, grouped, from the binary itself
ay options         AY_* environment options and their defaults
ay help            topic pages: z3, formats, exit-codes, output
```

`ay commands` prints the live list, `ay help` the topic pages, and
`ay <command> --help` the flags. About fifteen more maintainer commands
(benchmarks, corpora, gates, release and audit tooling) are hidden from that
list but ship in the binary, and each answers to `ay <name> --help`. In AY's
development tree, the development design notes maps every command, hidden ones
included, to the crates behind it.

`ay check veripb FORMULA PROOF` checks pseudo-Boolean certificates using AY's
integrated checker. Incomplete conclusions, unproved assertions and weakened
guarantees fail. A supplied output formula must be checked by an output FILE
rule. No separate VeriPB installation is needed.

`ay` also accepts Z3's command-line spellings (`-t:`, `-T:`, `-in`, `-model`,
`-st`, …), so it can stand in for `z3` in an existing script. Symlinking the
binary to `z3` turns that mode on automatically. Compatibility is partial —
see [LIMITATIONS.md](LIMITATIONS.md).

## What actually works

Solid, with real algorithms and heavy test coverage:

- **SAT** — a CDCL solver following CaDiCaL's design: two-watched-literal
  propagation, 1UIP clause learning, EVSIDS/VMTF/CHB branching, Luby and
  glue-based restarts, three-tier clause deletion, and a full preprocessing
  suite (variable elimination, vivification, subsumption, probing, blocked
  clause elimination, hyper-binary resolution).
- **SMT** — DPLL(T): the SAT search above runs in lockstep with theory
  solvers. Equality is congruence closure with proof-producing explanations;
  linear real arithmetic is dual simplex with Farkas certificates; integers
  add branch-and-bound with Gomory and Hermite-normal-form cuts; bitvectors
  and floating point are bit-blasted. Arrays, datatypes and difference logic
  are there too. Quantifiers go through E-matching, CEGQI and MBQI.
- **MILP** — branch-and-cut. A floating-point simplex proposes a basis and an
  exact-rational simplex re-verifies it, so floating point can cost search
  time but cannot corrupt the answer. Sparse LU with Forrest-Tomlin updates;
  cover, Gomory, MIR, flow-cover and clique cuts, each re-checked in exact
  arithmetic before use.
- **Pseudo-Boolean** — a native PB conflict-driven solver in the RoundingSat
  style, four PB-to-CNF encodings, and VeriPB proof output.
- **MaxSAT** — core-guided OLL/RC2 on one incremental SAT instance.
- **Proof checking** — the DRAT and LRAT checkers are independently written,
  not wrappers: two-watched-literal propagation, RUP and full RAT, forward and
  backward modes, text and binary formats. (The repo does not currently ship a
  cross-check against drat-trim — the fixtures for that live in a `reference/`
  checkout you'd have to clone yourself, and the tests skip without it.)

Known to be incomplete — these are design limits, not bugs:

- **Nonlinear arithmetic** returns `unknown` on problems it can't linearize.
  CAD projection exists but is not wired into the search.
- **Strings** deliberately latch to `unknown` rather than risk a wrong `sat`.
- **`ay lp`** uses a small dense simplex capped at 4096 search nodes. It is
  sized for test fixtures. The serious MILP engine has no `ay` subcommand
  yet; it is reached through `ay solve`'s MILP fast path, inside `ay maxsat`
  and `ay pb`, and through the separate `ay-milp` binary
  (`targo --unverified run -p ay-milp -- solve FILE.mps`; with stock Rust,
  `cargo run -p ay-milp -- solve FILE.mps`).
- **Certificates are uneven.** CNF and SMT `unsat` produce externally
  checkable proofs. `sat` answers get model validation only. MILP emits exact
  Farkas certificates that only AY can read, because no external checker
  format exists. Model counting, QBF and AllSAT have no certificates at all.

[LIMITATIONS.md](LIMITATIONS.md) has the details.

## Layout

```
crates/          the workspace crates: ay-sat, ay-dpll, ay-theories/*, ay-milp,
                 ay-pb-core, ay-proof, ay-chc, and the ay binary
benchmarks/      test corpora
examples/        small inputs to start from
proofs/          Lean proof sources and certificate fixtures
specs/           TLA+ models of the CDCL and PDR algorithms
scripts/         maintainer tooling
```

## Status

AY is 0.x and under active development. The API is not stable and there is no
release cadence yet. The two sections above are meant to be read together: the
first lists what has been checked against the source, the second lists what is
known not to work. If something is in neither list, assume it is untested.

## Contributing

See [CONTRIBUTING.md](CONTRIBUTING.md).

## License

Apache-2.0. See [LICENSE](LICENSE) and [THIRD_PARTY.md](THIRD_PARTY.md).
