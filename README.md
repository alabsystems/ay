# ay

The solver that shows its work.

When ay finds no solution to a CNF or SMT-LIB problem, by default it writes a proof another program checks.

One Rust binary covers SAT, SMT, Horn clauses, pseudo-Boolean, MaxSAT, QBF, LP/MILP, FlatZinc, and model counting. Run `ay FILE` on SMT-LIB 2.6, CNF, or Horn inputs for `sat` with a model, `unsat` with a proof artifact on supported paths, or `unknown` with the reason. Pass `--rigor certified` for fail-closed workflows, or `--z3-mode` for Z3-shaped CLI output.

Part of [ALab](https://alab.systems): superhuman software for AIs. On Apple-silicon macOS, install [aterm](https://github.com/alabsystems/aterm#install) and run `aterm pkg install ay`.

## Build

ay builds with ALab's trust compiler, pinned by `rust-toolchain.toml`. Install [aterm](https://github.com/alabsystems/aterm#install) and its trust package (`aterm pkg install trust`; atpkg ships it for Apple-silicon macOS today).

```bash
git clone https://github.com/alabsystems/ay.git
cd ay
targo --unverified build --release --locked -p ay --features cli --bin ay
export PATH="$PWD/target/release:$PATH"
```

The `ay` executable requires `--features cli`; without it, `targo` builds no `ay` binary. Run tests without a proof claim:

```bash
targo --unverified test -p ay-sat
```

The development checkout requires level 2 `certify` with `unix_hardened`, strict frontend lowering, authenticated dependency MIR for host and target, and rustdoc verification, including dependencies and build scripts. A full workspace proof requires a verified build of every unit; `targo --unverified` makes no proof claim.

[Development configuration](.cargo/config.toml) · [Tests and landing checks](CONTRIBUTING.md)

## Try it

ay detects the input format. This SMT-LIB example prints a model to stdout:

```console
$ ay examples/quickstart.smt2
sat
(model
  (define-fun y () Int 0)
  (define-fun x () Int 7)
)
```

Session and proof diagnostics go to stderr. Add `--rigor strict` to answer `unknown` instead of an `unsat` whose proof has a `trust` step or an unproved step.

An unsatisfiable DIMACS input exits with code 20. Declare a DRAT checker so the proof written beside the CNF uses only steps that `ay check drat` accepts:

```console
$ ay --proof-checker drat-trim problem.cnf
s UNSATISFIABLE

$ ay check drat problem.cnf problem.cnf.drat
s VERIFIED
```

Replay the bundled SMT-LIB example's Alethe proof with the pinned Carcara checker:

```bash
ay --alethe-dialect pinned-carcara examples/quickstart_unsat.smt2
carcara check -- examples/quickstart_unsat.smt2.alethe examples/quickstart_unsat.smt2
```

Read `unproved_steps` and `carcara_surface` on the `c ay.proof.certificate` line to see remaining proof holes and checker compatibility. By default, ay emits the Alethe dialect used by clean; pass `--alethe-dialect pinned-carcara` for the pinned Carcara checker's spellings. [Certificate coverage and checker compatibility](LIMITATIONS.md#certificate-coverage-is-uneven)

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
ay lp solve FILE   solve an MPS or CPLEX LP model
ay flatzinc solve FILE    solve a FlatZinc model with the CP or SMT backend
ay tutorial        interactive lessons
ay commands        this list, grouped, from the binary itself
ay options         AY_* environment options and their defaults
ay help            topic pages: z3, formats, exit-codes, output
```

Use `ay <command> --help` for flags. Hidden maintainer tools and their implementing crates are listed in the CLI reference.

`ay check veripb FORMULA PROOF` checks pseudo-Boolean certificates using ay's integrated checker. Incomplete conclusions, unproved assertions, and weakened guarantees fail, and a supplied output formula must be checked by an output FILE rule. No separate VeriPB installation is needed.

`ay` accepts Z3's command-line spellings (`-t:`, `-T:`, `-in`, `-model`, `-st`, …), and symlinking the binary to `z3` turns `--z3-mode` on automatically. In Python, `ayz3` mirrors a documented subset of `z3py`, so matching scripts generally need only an import change. Compatibility is partial: see [LIMITATIONS.md](LIMITATIONS.md).

## Engines and proof checkers

- **SAT**: a CDCL solver following CaDiCaL's design with two-watched-literal propagation, 1UIP clause learning, EVSIDS/VMTF/CHB branching, Luby and glue-based restarts, three-tier clause deletion, and preprocessing (variable elimination, vivification, subsumption, probing, blocked clause elimination, hyper-binary resolution).
- **SMT**: DPLL(T) combining the SAT core with congruence closure (proof-producing explanations), dual simplex for linear real arithmetic (Farkas certificates), integer branch-and-bound with Gomory and Hermite-normal-form cuts, bit-blasted bitvectors and floating point, arrays, datatypes, difference logic, and E-matching/CEGQI/MBQI quantifiers.
- **MILP**: branch-and-cut where a floating-point simplex proposes a basis and an exact-rational simplex re-verifies it, so floating point cannot corrupt the answer. Sparse LU with Forrest-Tomlin updates; cover, Gomory, MIR, flow-cover, and clique cuts re-checked in exact arithmetic before use.
- **Pseudo-Boolean**: a native PB conflict-driven solver in the RoundingSat style, four PB-to-CNF encodings, and VeriPB proof output.
- **MaxSAT**: core-guided OLL/RC2 on one incremental SAT instance.
- **Proof checking**: independently written DRAT and LRAT checkers (two-watched-literal propagation, RUP and full RAT, forward and backward modes, text and binary formats), plus the integrated VeriPB checker. The `ay-pb` tests and the PB certified gate require the pinned VeriPB checker to reject [22 regression fixtures](ci/veripb-soundness/README.md) for 21 wrong-verdict defects found in published VeriPB 3.0.2.
- **Measured proof validation**: on 2026-09-30, all 97 of 97 certificates marked `carcara_surface=supported` (out of a 128-query consumer corpus) checked `valid` under pinned Carcara 1.1.0 ([LIMITATIONS.md](LIMITATIONS.md)).
- **Lean LRAT theorem**: `lratCheck_sound` in `verification/lean` proves in Lean 4 that when its checker `lratCheck` accepts a well-formed LRAT proof for a well-formed formula, the formula is unsatisfiable. It uses only the axioms `propext` and `Quot.sound`, and that Lean project has no external dependencies.

### Limits

- **Nonlinear arithmetic**: returns `unknown` on problems it cannot linearize. CAD projection exists but is not wired into the search.
- **Strings**: unresolved word equations can yield `unknown`. An inferred equality can resolve the remaining equation and allow `sat`.
- **`ay lp solve`**: reads MPS coefficients exactly and uses the sparse MILP engine. CPLEX LP files use a dense binary64 simplex with a 4,096-node branch-and-bound limit.
- **Certificates**: a CNF or SMT proof is independently verified when the intended checker accepts it. Default proof emission can fail while ay still reports `unsat`. ay validates `sat` models. MILP emits exact Farkas certificates that only ay can read, because no external checker format exists. Model counting, QBF, and AllSAT have no certificates at all.
- **DRAT/LRAT cross-check**: the repo does not currently ship a cross-check against `drat-trim` (the fixtures live in a `reference/` checkout you have to clone yourself, and the tests skip without it).

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

ay is in active 0.x development. Its API and release schedule can change.

## Contributing

See [CONTRIBUTING.md](CONTRIBUTING.md).

## License

Apache-2.0. See [LICENSE](LICENSE) and [THIRD_PARTY.md](THIRD_PARTY.md).
