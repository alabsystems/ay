// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use anyhow::Result;

use super::ExpertChapter;

pub(super) fn run(selected: Option<ExpertChapter>, interactive: bool) -> Result<()> {
    println!();
    println!("=== AY for Experts ===");
    println!("Worked examples for readers fluent in SAT/SMT, Z3, and solver literature.");
    println!("Select a chapter with `ay tutorial experts CHAPTER`.");
    println!();

    let chapters: Vec<_> = ExpertChapter::ALL
        .into_iter()
        .filter(|chapter| selected.is_none_or(|wanted| wanted == *chapter))
        .collect();
    for (index, chapter) in chapters.iter().copied().enumerate() {
        println!("--- Chapter: {} ---", chapter.title());
        println!();
        match chapter {
            ExpertChapter::Proofs => proofs(),
            ExpertChapter::Incremental => incremental(),
            ExpertChapter::Optimization => optimization(),
            ExpertChapter::Theories => theories(),
            ExpertChapter::Research => research(),
        }
        if interactive && index + 1 < chapters.len() && !super::super::prompt_continue()? {
            println!("Course paused. Resume by selecting any chapter by name.");
            break;
        }
    }
    println!("Inspect the build you are using with `ay --features`.");
    println!();
    Ok(())
}

fn proofs() {
    println!(
        "{}",
        r#"Worked example A: theory UNSAT -> Alethe -> independent replay

  (set-logic QF_LIA)
  (declare-const x Int)
  (assert (>= x 1))
  (assert (<= x 0))
  (check-sat)

  ay solve --proof contradiction.alethe contradiction.smt2
  carcara check contradiction.alethe contradiction.smt2

The first command asks AY to serialize a refutation. The second command is the
acceptance boundary. Only successful Carcara replay justifies calling that
particular Alethe artifact independently checked. Renderer inventory in
`ay --features` is not an acceptance claim.

Worked example B: propositional LRAT and explicit replay

  p cnf 1 2
  1 0
  -1 0

  ay solve --proof contradiction.lrat contradiction.cnf
  ay check lrat contradiction.cnf contradiction.lrat

DRAT is available too (`--proof out.drat`, `ay check drat ...`). For a trust
boundary independent of AY, replay with a separate standard checker and record
its identity.

Worked example C: choose the fail-closed posture deliberately

  ay solve --strict-proofs problem.smt2
  ay solve --self-check problem.smt2

`--strict-proofs` screens a terminal derivation for load-bearing Trust/Hole
steps. `--self-check` gates definite answers on AY's stricter in-tree checks.
They serve different roles, and both remain inside AY's implementation boundary.

Evidence matrix:

  SAT model          independent evaluation in the original formula
  SMT UNSAT          Alethe -> Carcara on supported paths
  SAT UNSAT          DRAT/LRAT -> standard checker
  PB UNSAT/OPT       VeriPB (proof mode is opt-in and changes strategy)
  CHC SAFE           invariant + initiation/consecution/safety obligations
  CHC UNSAFE         original-clause concrete counterexample obligations

MaxSAT and QBF currently return verdicts/statistics without a shipped
certificate format. Keep proof-carrying claims format- and path-specific.
"#,
    );
}

fn incremental() {
    println!(
        "{}",
        r#"Worked example: named cores, scopes, and assumptions in one warm process

Run `ay --z3-mode -in`, then send:

  (set-logic QF_LIA)
  (set-option :produce-unsat-cores true)
  (set-option :produce-unsat-assumptions true)
  (declare-const x Int)
  (declare-const hi Bool)
  (assert (! (>= x 0) :named nonnegative))

  (check-sat)                         ; sat
  (push 1)
  (assert (! (< x 0) :named negative))
  (check-sat)                         ; unsat
  (get-unsat-core)                    ; (nonnegative negative)
  (pop 1)

  (assert (=> hi (< x 0)))
  (check-sat-assuming (hi))           ; unsat
  (get-unsat-assumptions)             ; (hi)
  (check-sat-assuming ((not hi)))     ; sat

Use either `-in` or `--incremental`, not both: `-in` already selects the
incremental, line-flushed stdin path.

The implementation can retain learned clauses, activity, phase state, existing
Tseitin encodings, and replayable theory lemmas across checks while respecting
push/pop scopes. The native API adds RAII `SolverScope`, structured assumption
details, annotated cores, interrupts, and resource controls.

For a lazy cutting-plane or CEGIS driver, keep a base context resident:

  assert base constraints
  check-sat -> inspect model
  assert one violated cut
  check-sat -> inspect the next model
  ...

Always handle UNKNOWN per iteration. A bounded search that times out has not
proved the scoped formula satisfiable or unsatisfiable.
"#,
    );
}

fn optimization() {
    println!(
        "{}",
        r#"Worked example: exact LRA optimality evidence

  (set-logic QF_LRA)
  (declare-const x Real)
  (declare-const y Real)
  (assert (>= x 1))
  (assert (>= (- y x) 3))
  (minimize y)
  (check-sat)
  (get-objectives)
  (get-objective-certificates)

The optimum is y = 4. On the supported path AY emits positive Farkas
multipliers whose linear combination is the exact identity proving `y >= 4`.
The model attains 4; primal attainment plus the dual bound brackets the optimum.
The executor rechecks the solve and certificate before publishing it.

This path fails closed: a certificate can be absent for equality/derived bound
reasons, nonlinear or non-Real objectives, unbounded optima, or fallback search.
Integer and bit-vector objectives do not inherit the LRA certificate claim.

Other worked surfaces:

  ; lexicographic by default; :opt.priority also has box/pareto paths
  (minimize latency)
  (minimize cost)
  (check-sat)
  (get-objectives)

  ay pb solve allocation.opb --proof allocation.veripb
  veripb allocation.opb allocation.veripb

  ay maxsat solve preferences.wcnf
  ay lp solve model.mps
  ay flatzinc solve schedule.fzn

Pseudo-Boolean proof mode is opt-in because it selects a certifying strategy.
MaxSAT uses a dedicated core-guided path; its `--milp` lane is experimental.
The native ay-milp API exposes exact rational checks and split-tree/Farkas
evidence on supported outcomes. Preserve Optimal, Feasible/incumbent,
Unbounded, Infeasible, and Unknown as distinct results.
"#,
    );
}

fn theories() {
    println!(
        "{}",
        r#"AY's DPLL(T) surface spans UF, LIA/LRA/LIRA, bit-vector, arrays,
floating point, strings/sequences, datatypes, nonlinear fragments, quantifiers,
and combinations. `ay --features` reports routes and proof renderers; it is not
a blanket completeness or checker-acceptance theorem.

Worked example A: Farkas-annotated arithmetic core

  (set-logic QF_LRA)
  (set-option :produce-proofs true)
  (set-option :produce-unsat-cores true)
  (declare-const x Real)
  (assert (! (<= x 0.0) :named upper))
  (assert (! (>= x 1.0) :named lower))
  (check-sat)
  (get-unsat-core :farkas)

Worked example B: validated Craig interpolation

  (set-logic QF_LIA)
  (declare-const x Int)
  (get-interpolant (<= x 0) (>= x 1))

For the supported LIA/LRA path, AY validates A => I, I & B => false, and the
shared-symbol condition. Do not infer general Z3 tactic/interpolation parity.

Worked example C: validated abduction

  (set-logic QF_LIA)
  (declare-const x Int)
  (assert (>= x 10))
  (get-abduct enough (> x 5))

Candidates come from a bounded grammar and are checked for consistency and
entailment before publication; failure returns none rather than a guess.

CHC is a first-class search family rather than a thin SMT alias. Its adaptive
portfolio includes PDR/IC3, BMC, k-induction/PDKind, TPA, TRL, decomposition,
LAWI, IMC, DAR, and CEGAR-style routes. SAFE carries an invariant; UNSAFE carries
a trace translated back to original clauses. Bounded BMC exhaustion remains
UNKNOWN. In Z3 fixedpoint `(query ...)` syntax, sat means the bad state is reachable.

SAT specialists can inspect two-watched CDCL, 1-UIP, VSIDS/VMTF, LBD tiers,
chronological backtracking, Luby/EMA restarts, vivification, BVE/BCE, HTR, gate
extraction, sweeping, congruence, local search, portfolio solving, and
cube-and-conquer. Technique disables are for controlled experiments; the
correct default is the complete configured solver.
"#,
    );
}

fn research() {
    println!(
        "{}",
        r#"Worked workflow: turn a surprising answer into a reproducible experiment

  cargo build -p ay --features bench

  ay diagnose --reference z3 --json candidate.smt2 > diagnosis.json

  ay solve --stats-json \
    --diagnostic-file dpll.jsonl \
    --decision-trace decisions.jsonl \
    --clause-provenance \
    candidate.smt2

  ay bench run MY-EVAL --reference-solver "$(command -v z3)" \
    --output scorecard.json

Bind every claim to AY/reference provenance, corpus hash/manifest, timeout,
enforced memory per child, proof mode, checker verdicts, wrong/invalid counts,
solved counts, and raw per-instance rows. Do not publish an aggregate speedup
without the evidence needed to audit it.

Research surfaces include:

  --stats-json / --progress-json       counters and streaming progress
  --decision-trace / --replay          deterministic decision experiments
  --diagnostic-file                    JSONL solver diagnostics
  --dump-encoding                      annotated pre-solve DIMACS
  --dump-bv-cnf                        complete QF_BV Boolean export
  --dump-conflicts / --iuc-trace       theory conflict/interpolation study
  --disable ...                        one-technique ablations from full help
  ay bench features FORMULA.cnf        proof-complexity features
  ay allsat --projected-vars ...       projected model enumeration

Distinctive AY work worth inspecting in source and artifacts:

  - original-clause CHC replay after transformed search;
  - fail-closed partition rescue for symbol-disjoint theory components;
  - exact Farkas and MILP split-tree evidence;
  - structure-directed specialization with final witness rechecks;
  - typed `check_sat_with_details()` plus `accept_for_consumer()`;
  - native replay artifacts carrying terms, scopes, limits, models, and proofs.

Never run a full corpus sweep beside a Cargo/LTO build. Size parallel jobs with
`scripts/_oom_guard.py`, enforce the correct child-specific memory knob or RSS
watchdog, and persist that envelope. Solver defaults are sibling-blind; N
children each believing they own the machine is not an experiment.
"#,
    );
}
