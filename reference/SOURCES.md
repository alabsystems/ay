# Reference Solver Sources

Clone these into `reference/` to set up the reference implementations.

```bash
cd reference/

# SMT solvers
git clone --depth 1 https://github.com/Z3Prover/z3
git clone --depth 1 https://github.com/cvc5/cvc5
git clone --depth 1 https://github.com/usi-verification-and-security/opensmt
git clone --depth 1 https://github.com/smtrat/smtrat
git clone --depth 1 https://github.com/ultimate-pa/smtinterpol

# SAT solvers
git clone --depth 1 https://github.com/arminbiere/cadical
git clone --depth 1 https://github.com/arminbiere/kissat
git clone --depth 1 https://github.com/msoos/cryptominisat
git clone --depth 1 https://github.com/muhos/ParaFROST parafrost
git clone --depth 1 https://github.com/sarsko/CreuSAT creusat

# CHC solvers
git clone --depth 1 https://github.com/usi-verification-and-security/golem
git clone --depth 1 https://github.com/uuverifiers/eldarica

# CP-SAT solvers (for ay-cp / MiniZinc)
git clone --depth 1 https://github.com/ConSol-Lab/Pumpkin pumpkin

# String solvers
git clone --depth 1 https://github.com/VeriFIT/z3-noodler
git clone --depth 1 https://github.com/VeriFIT/mata

# Proof checking
git clone --depth 1 https://github.com/ufmg-smite/carcara
```

## Directory Index

| Directory | Repository | Domain | License |
|-----------|-----------|--------|---------|
| `z3/` | [Z3Prover/z3](https://github.com/Z3Prover/z3) | SMT/CHC | MIT |
| `cvc5/` | [cvc5/cvc5](https://github.com/cvc5/cvc5) | SMT | BSD-3 |
| `opensmt/` | [opensmt](https://github.com/usi-verification-and-security/opensmt) | SMT (interpolation) | MIT |
| `smtrat/` | [smtrat/smtrat](https://github.com/smtrat/smtrat) | SMT (NRA) | MIT |
| `smtinterpol/` | [smtinterpol](https://github.com/ultimate-pa/smtinterpol) | SMT (interpolation) | LGPL-3 |
| `cadical/` | [arminbiere/cadical](https://github.com/arminbiere/cadical) | SAT | MIT |
| `kissat/` | [arminbiere/kissat](https://github.com/arminbiere/kissat) | SAT | MIT |
| `cryptominisat/` | [msoos/cryptominisat](https://github.com/msoos/cryptominisat) | SAT (XOR) | MIT |
| `parafrost/` | [muhos/ParaFROST](https://github.com/muhos/ParaFROST) | SAT (GPU) | MIT |
| `creusat/` | [sarsko/CreuSAT](https://github.com/sarsko/CreuSAT) | SAT (verified) | MIT |
| `golem/` | [golem](https://github.com/usi-verification-and-security/golem) | CHC | MIT |
| `eldarica/` | [uuverifiers/eldarica](https://github.com/uuverifiers/eldarica) | CHC | BSD-3 |
| `z3-noodler/` | [VeriFIT/z3-noodler](https://github.com/VeriFIT/z3-noodler) | Strings | MIT |
| `mata/` | [VeriFIT/mata](https://github.com/VeriFIT/mata) | Automata | MIT |
| `carcara/` | [ufmg-smite/carcara](https://github.com/ufmg-smite/carcara) | Proof checking | Apache-2 |
| `pumpkin/` | [ConSol-Lab/Pumpkin](https://github.com/ConSol-Lab/Pumpkin) | CP-SAT (LCG, Rust) | MIT |

## Non-Git Entries

| Path | Description |
|------|-------------|
| `drat-trim/` | Vendored DRAT/LRAT reference checker sources used by tests and comparisons; see file headers for license text |
| TLA+ TLC | External TLA+ TLC model checker; provide with `TLC_BIN` or `TLA2TOOLS_JAR` when needed |
| `chc-solvers/` | Dockerfile for LoAT + UltimateTreeAutomizer |
| `loat-chc-comp-2025/` | Reference-only LoAT CHC-COMP 2025 portfolio wrapper |
| `isafol/` | Optional local Isabelle/AFP checkout; expected to stay untracked/ignored in normal repo work |
