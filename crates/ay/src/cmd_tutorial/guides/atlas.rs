// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use anyhow::Result;

use super::FeatureSection;

pub(super) fn run(selected: Option<FeatureSection>, interactive: bool) -> Result<()> {
    println!();
    println!("=== AY Feature Atlas ===");
    println!("A map of the public solver, evidence, integration, and evaluation surfaces.");
    println!("Run `ay tutorial features SECTION` to revisit one section.");
    println!();

    let sections: Vec<_> = FeatureSection::ALL
        .into_iter()
        .filter(|section| selected.is_none_or(|wanted| wanted == *section))
        .collect();
    for (index, section) in sections.iter().copied().enumerate() {
        println!("--- {} ---", section.title());
        println!();
        match section {
            FeatureSection::Solving => solving(),
            FeatureSection::Proofs => proofs(),
            FeatureSection::Optimization => optimization(),
            FeatureSection::Exploration => exploration(),
            FeatureSection::Integration => integration(),
            FeatureSection::Tooling => tooling(),
        }
        if interactive && index + 1 < sections.len() && !super::super::prompt_continue()? {
            println!("Atlas paused. Select a section by name whenever you return.");
            break;
        }
    }

    println!("Feature availability is build- and fragment-specific.");
    println!("Inspect this binary with `ay --features` and read LIMITATIONS.md before relying on a path.");
    println!();
    Ok(())
}

fn solving() {
    println!(
        "{}",
        r#"Primary entry point: ay solve FILE  (or simply: ay FILE)

  SMT-LIB 2.6   Arithmetic, UF, bit-vectors, arrays, floating point,
                strings/sequences, datatypes, and quantified fragments.
  DIMACS CNF    CDCL SAT with preprocessing, inprocessing, portfolios,
                models, and propositional proof output.
  CHC / HORN    Program-safety solving with an adaptive PDR/IC3-centered
                portfolio, invariants for SAFE, and concrete traces for UNSAFE.

AY auto-detects these three families. Dedicated solver frontends cover:

  ay flatzinc solve MODEL.fzn     MiniZinc/FlatZinc; CP first, SMT fallback
  ay pb solve INSTANCE.opb       Pseudo-Boolean decision and optimization
  ay maxsat solve INSTANCE.wcnf  Weighted and unweighted MaxSAT
  ay qbf solve INSTANCE.qdimacs  Quantified Boolean formulas
  ay lp solve MODEL.mps          LP/MILP in MPS or CPLEX LP syntax

The answer is three-valued where the format permits it: SAT/UNSAT/UNKNOWN,
SAFE/UNSAFE/UNKNOWN, or an optimization result that distinguishes a proved
optimum from a best incumbent. UNKNOWN is information, never “probably false.”
"#,
    );
}

fn proofs() {
    println!(
        "{}",
        r#"AY is proof-oriented: search and acceptance are separate questions.

  SMT UNSAT       Alethe on supported paths; replay with Carcara
  DIMACS UNSAT    DRAT or LRAT; replay with `ay check` and an independent checker
  PB UNSAT/OPT    VeriPB proof with `ay pb solve --proof ...`
  CHC SAFE        Invariant certificate plus independently solvable obligations
  CHC UNSAFE      Original-clause counterexample and replay obligations
  BV              Versioned bit-blast export and Lean rendering on named paths

Worked commands:

  ay solve --proof out.alethe problem.smt2
  carcara check out.alethe problem.smt2

  ay solve --proof out.lrat problem.cnf
  ay check lrat problem.cnf out.lrat

Trust modes have different jobs:

  --strict-proofs  screens terminal Trust/Hole fallbacks inside AY
  --self-check     emits a definite answer only after AY's fail-closed checks
  external replay crosses AY's implementation trust boundary

Successful proof emission alone is not certification. Name the checker and
record its acceptance verdict before calling an artifact certified.
"#,
    );
}

fn optimization() {
    println!(
        "{}",
        r#"There are several optimization layers because their proof methods differ.

  SMT OMT          (minimize ...), (maximize ...), (get-objectives)
  MaxSMT           weighted (assert-soft ...)
  LRA evidence     exact Farkas optimality certificates on supported Real objectives
  Pseudo-Boolean   OPB/WBO, engine selection, optional VeriPB certification
  MaxSAT           WCNF with core-guided search and competition output
  LP / MILP        MPS and CPLEX LP; exact checked values in native ay-milp
  FlatZinc / CP    finite-domain search, globals, enumeration, and objectives

  ay pb solve routing.opb --proof routing.veripb
  ay maxsat solve preferences.wcnf
  ay lp solve schedule.lp
  ay flatzinc solve schedule.fzn

Linear Real optimization is the strongest SMT certificate path today. Integer,
bit-vector, MaxSAT, and QBF evidence differs; do not generalize one format's
certificate claim to another solver family.
"#,
    );
}

fn exploration() {
    println!(
        "{}",
        r#"A solver is useful after the first model too.

  ay allsat FORMULA.cnf
      Enumerate every DIMACS model, cap with --max-models, or project onto
      selected variables with --projected-vars.

  ay model-count INSTANCE.cnf
      Exact and projected model counting, including weighted and algebraic
      competition inputs supported by the counting frontend.

  ay simplify INPUT.smt2 --tactic ctx-simplify --check-sat
      Apply AST-level, equivalence-preserving simplification and emit SMT-LIB.

  ay solve --explain INPUT.smt2
      Explain a model or classify an UNSAT reason. Use --explain-format json
      for reason metadata consumed by programs.

  ay solve --visualize=ascii puzzle.smt2
  ay solve --visualize=svg puzzle.smt2
      Render recognized N-Queens and Sudoku models. Visualization is
      presentation, not independent validation.

The tutorial-specific `ay tutorial solve FILE.smt2` back-substitutes a model,
and `ay tutorial play sudoku` exposes a live solver-backed model.
"#,
    );
}

fn integration() {
    println!(
        "{}",
        r#"Choose the narrowest integration boundary that fits the application.

  Process / SMT-LIB   Stable, inspectable, language-neutral
  Z3-shaped CLI       `ay --z3-mode`, `-in`, and a project-local `z3` shim
  Native Rust         `ay::api` typed terms, scopes, details, and model values
  AY Search           finite-domain model API for search-shaped applications
  Python              `ayz3` for Z3-shaped code; `aysearch` for model specs
  JavaScript/TS       `ayz3` plus the typed `ayz3/search` entry point
  C / C++             C ABI and header-only z3++-shaped wrapper
  Java / OCaml        in-tree bindings with documented, tested subsets
  WASM                source-checkout Node harness for its supported surface

Z3 transcript mode changes the visible protocol, not AY's reasoning, and each
binding documents its implemented subset. Differentially test the exact
operations your program uses.

Start with:
  cargo run -p ay-dpll --example native_api
  python3 -m pip install ./bindings/python
  cd bindings/js && npm install && npm test
"#,
    );
}

fn tooling() {
    println!(
        "{}",
        r#"AY ships tools that turn one solve into reproducible evidence.

  ay bench list / run / score / diff
      Registered evaluations, references, raw per-file rows, provenance,
      resource envelopes, and competition-style scoring.

  ay corpus list / download / verify
      Manifest-backed benchmark acquisition and hash verification.

  ay diagnose --reference z3 --json failing.smt2
      Re-run a disputed input, validate models, compare a reference verdict,
      surface an explanation, and preserve binary provenance.

  ay check drat|lrat ...
      Explicit proof replay with the in-tree checkers.

  ay --features
      Machine-readable build features, accepted logics, and renderer inventory.

  ay solve --stats-json --progress-json progress.jsonl problem.smt2
      Machine-readable statistics and streaming progress evidence.

Benchmark-only functionality may require `cargo build -p ay --features bench`.
Parallel benchmark runs must use the repository OOM planner and persist the
enforced per-child memory envelope; timings without it are not comparable.
"#,
    );
}
