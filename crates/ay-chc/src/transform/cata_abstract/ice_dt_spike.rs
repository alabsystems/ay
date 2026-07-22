// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! SPIKE harness (make-or-break gate) for the Horn-ICE decision-tree learner.
//!
//! Loads a real ADT-LIA sortedness benchmark, builds its SORTED-level cata
//! abstraction exactly as the route does, discharges the per-clause obligations
//! with a generous budget, then runs BOTH the exact-fixpoint DNF learner
//! ([`super::disj_abstract::solve_abstract_disjunctive`]) and the new
//! generalizing DT learner ([`super::ice_dt::solve_abstract_ice_dt`]) on the
//! same abstract problem, re-certifying each candidate with the SAME fail-closed
//! gate the route uses ([`crate::engines::validate_external_invariant_model`]).
//!
//! `#[ignore]` — reads the CHC-COMP-25 tip-adt-lia corpus (not vendored). Point
//! `AY_SPIKE_CORPUS` at the directory holding the `.smt2` files and run:
//! `AY_SPIKE_CORPUS=<dir> cargo test -p ay-chc ice_dt_spike -- --ignored --nocapture`.

use std::time::Duration;

use ay_core::time::Instant;

use super::{build_cata_ladder, CataAbstraction, CataKind, ColumnTag};
use crate::{
    ChcExpr, ChcParser, ChcProblem, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause,
    InvariantModel, PdrConfig, PredicateId,
};

/// A two-flag predicate `P(a, b)` whose safety invariant is the DISJUNCTION
/// `(a=0 ∧ b=0) ∨ (a=1 ∧ b=1)`. Facts pin `(0,0)` and `(1,1)`; the extra
/// clauses (below) decide whether it is SAFE or a false-Safe trap.
fn two_flag_problem() -> (ChcProblem, PredicateId) {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int, ChcSort::Int]);
    let a = ChcVar::new("a", ChcSort::Int);
    let b = ChcVar::new("b", ChcSort::Int);
    let va = || ChcExpr::var(a.clone());
    let vb = || ChcExpr::var(b.clone());
    let eq0 = |v: ChcExpr| ChcExpr::eq(v, ChcExpr::int(0));
    let eq1 = |v: ChcExpr| ChcExpr::eq(v, ChcExpr::int(1));
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::and(eq0(va()), eq0(vb()))),
        ClauseHead::Predicate(p, vec![va(), vb()]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::and(eq1(va()), eq1(vb()))),
        ClauseHead::Predicate(p, vec![va(), vb()]),
    ));
    (problem, p)
}

fn flag_tags(p: PredicateId) -> ay_core::kani_compat::DetHashMap<PredicateId, Vec<ColumnTag>> {
    [(
        p,
        vec![
            ColumnTag {
                kind: Some(CataKind::RootDisc),
                group: 0,
                scalar_int: false,
            },
            ColumnTag {
                kind: Some(CataKind::RootDisc),
                group: 1,
                scalar_int: false,
            },
        ],
    )]
    .into_iter()
    .collect()
}

fn recert_orig(problem: &ChcProblem, model: &InvariantModel) -> bool {
    let cfg = PdrConfig {
        strict_proofs: true,
        solve_timeout: Some(Duration::from_secs(10)),
        ..PdrConfig::default()
    };
    matches!(
        crate::engines::validate_external_invariant_model(problem, model, &cfg),
        Ok(true)
    )
}

/// The Horn-ICE DT learner finds the genuinely DISJUNCTIVE two-minterm
/// invariant and it re-certifies — the corpus-free positive pin.
#[test]
fn ice_dt_solves_two_minterm_invariant() {
    let (mut problem, p) = two_flag_problem();
    let va = || ChcExpr::var(ChcVar::new("a", ChcSort::Int));
    let vb = || ChcExpr::var(ChcVar::new("b", ChcSort::Int));
    let eq0 = |v: ChcExpr| ChcExpr::eq(v, ChcExpr::int(0));
    let eq1 = |v: ChcExpr| ChcExpr::eq(v, ChcExpr::int(1));
    // Errors on the "mixed" corners ⇒ the only safety invariant is the
    // disjunction of the two pinned corners.
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![va(), vb()])],
            Some(ChcExpr::and(eq0(va()), eq1(vb()))),
        ),
        ClauseHead::False,
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![va(), vb()])],
            Some(ChcExpr::and(eq1(va()), eq0(vb()))),
        ),
        ClauseHead::False,
    ));

    let model = super::ice_dt::solve_abstract_ice_dt(
        &problem,
        &flag_tags(p),
        Instant::now() + Duration::from_secs(10),
    )
    .expect("DT learner must find the two-minterm invariant");
    assert!(
        recert_orig(&problem, &model),
        "learned invariant must re-certify"
    );
}

/// ADVERSARIAL no-false-Safe: the query is genuinely REACHABLE (`(0,0)` is a
/// fact AND an error). The DT learner must NEVER return a re-certifying model —
/// it either returns `None` (query reachable in its closure) or a candidate
/// that fails the re-cert gate. A false Safe here would be a soundness bug.
#[test]
fn ice_dt_never_false_safe_on_reachable_query() {
    let (mut problem, p) = two_flag_problem();
    let va = || ChcExpr::var(ChcVar::new("a", ChcSort::Int));
    let vb = || ChcExpr::var(ChcVar::new("b", ChcSort::Int));
    let eq0 = |v: ChcExpr| ChcExpr::eq(v, ChcExpr::int(0));
    // `P ∧ a=0 ∧ b=0 ⇒ false` — but `(0,0) ∈ P` by the first fact ⇒ UNSAFE.
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![va(), vb()])],
            Some(ChcExpr::and(eq0(va()), eq0(vb()))),
        ),
        ClauseHead::False,
    ));

    let outcome = super::ice_dt::solve_abstract_ice_dt(
        &problem,
        &flag_tags(p),
        Instant::now() + Duration::from_secs(10),
    );
    if let Some(model) = outcome {
        assert!(
            !recert_orig(&problem, &model),
            "DT learner produced a FALSE Safe on a reachable-query (unsafe) problem"
        );
    }
}

/// ADVERSARIAL no-false-Safe for the FLAGS-ONLY entry: the query is genuinely
/// REACHABLE (`(0,0)` is a fact AND an error). The flag-only DT learner must
/// NEVER return a re-certifying model — the compact vocabulary widens the region
/// but the fail-closed re-cert gate still rejects any candidate on a reachable
/// query. A false Safe here would be a soundness bug in the wide-family lane.
#[test]
fn ice_dt_flags_only_never_false_safe_on_reachable_query() {
    let (mut problem, p) = two_flag_problem();
    let va = || ChcExpr::var(ChcVar::new("a", ChcSort::Int));
    let vb = || ChcExpr::var(ChcVar::new("b", ChcSort::Int));
    let eq0 = |v: ChcExpr| ChcExpr::eq(v, ChcExpr::int(0));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![va(), vb()])],
            Some(ChcExpr::and(eq0(va()), eq0(vb()))),
        ),
        ClauseHead::False,
    ));
    let outcome = super::ice_dt::solve_abstract_ice_dt_flags_only(
        &problem,
        &flag_tags(p),
        Instant::now() + Duration::from_secs(10),
    );
    if let Some(model) = outcome {
        assert!(
            !recert_orig(&problem, &model),
            "flag-only DT learner produced a FALSE Safe on a reachable-query (unsafe) problem"
        );
    }
}

/// Outcome of running one learner on one abstraction.
struct LearnRun {
    solved: bool,
    recertified: bool,
    wall: Duration,
}

fn recert(problem: &crate::ChcProblem, model: &crate::InvariantModel) -> bool {
    let cfg = crate::PdrConfig {
        strict_proofs: true,
        solve_timeout: Some(Duration::from_secs(30)),
        ..crate::PdrConfig::default()
    };
    matches!(
        crate::engines::validate_external_invariant_model(problem, model, &cfg),
        Ok(true)
    )
}

/// Build the sorted-level abstraction and run one learner; `None` if the
/// benchmark cannot be prepared (missing corpus, no sorted level, obligations
/// undischarged).
fn prepare_sorted_abstraction(smt: &str) -> Option<CataAbstraction> {
    let problem = ChcParser::parse(smt).expect("benchmark CHC should parse");
    let ladder = build_cata_ladder(&problem, true);
    let pool = ladder
        .iter()
        .find(|p| p.contains(&CataKind::Sorted))?
        .clone();
    let abstraction = CataAbstraction::build(&problem, &pool).ok()?;
    // Generous obligation budget (the spike is offline, not competition-timed).
    if !abstraction.discharge_obligations(
        Duration::from_secs(5),
        Some(Instant::now() + Duration::from_secs(120)),
    ) {
        return None;
    }
    Some(abstraction)
}

fn ice_tags(
    abstraction: &CataAbstraction,
) -> ay_core::kani_compat::DetHashMap<PredicateId, Vec<ColumnTag>> {
    abstraction
        .abstract_problem
        .predicates()
        .iter()
        .map(|p| (p.id, abstraction.column_tags(p.id)))
        .collect()
}

fn run_dnf(abstraction: &CataAbstraction, budget: Duration) -> LearnRun {
    let tags = ice_tags(abstraction);
    let start = Instant::now();
    let model = super::disj_abstract::solve_abstract_disjunctive(
        &abstraction.abstract_problem,
        &tags,
        start + budget,
    );
    let wall = start.elapsed();
    match model {
        Some(m) => LearnRun {
            solved: true,
            recertified: recert(&abstraction.abstract_problem, &m),
            wall,
        },
        None => LearnRun {
            solved: false,
            recertified: false,
            wall,
        },
    }
}

fn run_dt(abstraction: &CataAbstraction, budget: Duration) -> LearnRun {
    let tags = ice_tags(abstraction);
    let start = Instant::now();
    let model =
        super::ice_dt::solve_abstract_ice_dt(&abstraction.abstract_problem, &tags, start + budget);
    let wall = start.elapsed();
    match model {
        Some(m) => LearnRun {
            solved: true,
            recertified: recert(&abstraction.abstract_problem, &m),
            wall,
        },
        None => LearnRun {
            solved: false,
            recertified: false,
            wall,
        },
    }
}

/// The three spike targets: ISortSorts (must keep working) + the two Blocker-A
/// instances (z3 SAT, DNF fixpoint times out).
const TARGETS: &[(&str, &str)] = &[
    ("ISortSorts", "tip2015_sort_ISortSorts_000.smt2"),
    ("NMSortTDSorts", "tip2015_sort_NMSortTDSorts_000.smt2"),
    ("nat_ISortSorts", "tip2015_sort_nat_ISortSorts_000.smt2"),
];

#[test]
#[ignore]
fn ice_dt_dump_abstract() {
    let corpus = match std::env::var("AY_SPIKE_CORPUS") {
        Ok(d) => std::path::PathBuf::from(d),
        Err(_) => {
            eprintln!("SKIP: set AY_SPIKE_CORPUS");
            return;
        }
    };
    let which = std::env::var("AY_DUMP_BENCH").unwrap_or_else(|_| "ISortSorts".to_string());
    let file = WIDE_TARGETS
        .iter()
        .find(|(l, _)| *l == which)
        .map(|(_, f)| *f)
        .unwrap();
    let smt = std::fs::read_to_string(corpus.join(file)).expect("read");
    let problem = ChcParser::parse(&smt).expect("parse");
    let ladder = build_cata_ladder(&problem, true);
    let pool = ladder
        .iter()
        .find(|p| p.contains(&CataKind::Sorted))
        .unwrap()
        .clone();
    let abstraction = CataAbstraction::build(&problem, &pool).unwrap();
    let dump = super::dump_abstract_lia_problem(&abstraction.abstract_problem);
    eprintln!("=== SORTED-LEVEL ABSTRACT [{which}] ===\n{dump}");
}

#[test]
#[ignore]
fn ice_dt_spike_gate() {
    let corpus = match std::env::var("AY_SPIKE_CORPUS") {
        Ok(d) => std::path::PathBuf::from(d),
        Err(_) => {
            eprintln!("SKIP: set AY_SPIKE_CORPUS to the tip-adt-lia directory");
            return;
        }
    };

    // Generous per-learner budget so the DNF learner has every chance to
    // converge (the point is to reproduce its blow-up, not starve it).
    let dnf_budget = Duration::from_secs(
        std::env::var("AY_SPIKE_DNF_SECS")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(150),
    );
    let dt_budget = Duration::from_secs(
        std::env::var("AY_SPIKE_DT_SECS")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(60),
    );

    let mut dt_isort_ok = false;
    let mut dt_blocker_ok = 0usize;

    eprintln!("\n=== ICE-DT SPIKE GATE ===");
    eprintln!("corpus: {}", corpus.display());
    eprintln!("dnf_budget={:?} dt_budget={:?}\n", dnf_budget, dt_budget);

    for (label, file) in TARGETS {
        let path = corpus.join(file);
        let smt = match std::fs::read_to_string(&path) {
            Ok(s) => s,
            Err(e) => {
                eprintln!("[{label}] MISSING {}: {e}", path.display());
                continue;
            }
        };
        let Some(abstraction) = prepare_sorted_abstraction(&smt) else {
            eprintln!("[{label}] could not build/discharge sorted-level abstraction");
            continue;
        };
        let n_preds = abstraction.abstract_problem.predicates().len();
        let n_clauses = abstraction.abstract_problem.clauses().len();
        eprintln!("[{label}] sorted-level abstract: {n_preds} preds, {n_clauses} clauses");

        let dt = run_dt(&abstraction, dt_budget);
        eprintln!(
            "[{label}]   DT : solved={} recert={} wall={:?}",
            dt.solved, dt.recertified, dt.wall
        );
        let dnf = run_dnf(&abstraction, dnf_budget);
        eprintln!(
            "[{label}]   DNF: solved={} recert={} wall={:?}",
            dnf.solved, dnf.recertified, dnf.wall
        );

        if *label == "ISortSorts" && dt.solved && dt.recertified {
            dt_isort_ok = true;
        }
        if (*label == "NMSortTDSorts" || *label == "nat_ISortSorts") && dt.solved && dt.recertified
        {
            dt_blocker_ok += 1;
        }
    }

    eprintln!(
        "\n=== SPIKE RESULT: ISortSorts(DT)={} BlockerA(DT)={}/2 ===\n",
        dt_isort_ok, dt_blocker_ok
    );

    assert!(
        dt_isort_ok,
        "SPIKE FAIL: DT learner must still solve+recertify ISortSorts (no regression)"
    );
    assert!(
        dt_blocker_ok >= 1,
        "SPIKE FAIL: DT learner solved neither Blocker-A instance (need >=1)"
    );
}

/// The WIDE sortedness targets for the flag-projection scaling spike (task #28):
/// the 9+-pred abstracts that the full vocabulary times out / hits ay-dpll
/// `Unknown` on, plus the narrow ISortSorts family (the no-regression pins).
const WIDE_TARGETS: &[(&str, &str)] = &[
    ("ISortSorts", "tip2015_sort_ISortSorts_000.smt2"),
    ("nat_ISortSorts", "tip2015_sort_nat_ISortSorts_000.smt2"),
    ("NMSortTDSorts", "tip2015_sort_NMSortTDSorts_000.smt2"),
    ("BSortSorts", "tip2015_sort_BSortSorts_000.smt2"),
    ("HSortSorts", "tip2015_sort_HSortSorts_000.smt2"),
    ("BSortIsSort", "tip2015_sort_BSortIsSort_000.smt2"),
    ("BubSortSorts", "tip2015_sort_BubSortSorts_000.smt2"),
    ("BubSortIsSort", "tip2015_sort_BubSortIsSort_000.smt2"),
];

/// Run the flag-only-vocabulary DT learner (the additive wide-family lane).
fn run_dt_flags(abstraction: &CataAbstraction, budget: Duration) -> LearnRun {
    let tags = ice_tags(abstraction);
    let start = Instant::now();
    let model = super::ice_dt::solve_abstract_ice_dt_flags_only(
        &abstraction.abstract_problem,
        &tags,
        start + budget,
    );
    let wall = start.elapsed();
    match model {
        Some(m) => LearnRun {
            solved: true,
            recertified: recert(&abstraction.abstract_problem, &m),
            wall,
        },
        None => LearnRun {
            solved: false,
            recertified: false,
            wall,
        },
    }
}

/// SWEEP: measure each learner lane on the sortedness abstracts. Reports the
/// abstract size (preds/clauses/atoms) and, per lane, solved/recert/wall.
/// Non-asserting (measurement only) — read the table. The landed route tries
/// DT-full, then the exact DNF fixpoint, then DT-flags (the wide-family lane).
///
/// `AY_SPIKE_CORPUS=<tip-adt-lia dir> AY_SWEEP_SECS=40 cargo test -p ay-chc \
///   disj_cube_sweep -- --ignored --nocapture`
#[test]
#[ignore]
fn disj_cube_sweep() {
    let corpus = match std::env::var("AY_SPIKE_CORPUS") {
        Ok(d) => std::path::PathBuf::from(d),
        Err(_) => {
            eprintln!("SKIP: set AY_SPIKE_CORPUS to the tip-adt-lia directory");
            return;
        }
    };
    let budget = Duration::from_secs(
        std::env::var("AY_SWEEP_SECS")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(60),
    );
    let only: Option<String> = std::env::var("AY_SWEEP_ONLY").ok();

    eprintln!("\n=== SORTEDNESS ATOM-PROFILE SWEEP (budget={budget:?}) ===");
    eprintln!(
        "{:<15} {:>4} {:>4} {:>5} {:>4} {:>5} | {:<22} {:<22} {:<22}",
        "target", "prd", "cls", "atomF", "maxF", "atomL", "DNF-full", "DT-full", "DT-flagsOnly"
    );

    for (label, file) in WIDE_TARGETS {
        if let Some(o) = &only {
            if o != label {
                continue;
            }
        }
        let path = corpus.join(file);
        let smt = match std::fs::read_to_string(&path) {
            Ok(s) => s,
            Err(e) => {
                eprintln!("[{label}] MISSING {}: {e}", path.display());
                continue;
            }
        };
        let Some(abstraction) = prepare_sorted_abstraction(&smt) else {
            eprintln!("[{label:<13}] could not build/discharge sorted-level abstraction");
            continue;
        };
        let n_preds = abstraction.abstract_problem.predicates().len();
        let n_clauses = abstraction.abstract_problem.clauses().len();
        let tags = ice_tags(&abstraction);
        let (mut atoms_full, mut max_full, mut atoms_flags) = (0usize, 0usize, 0usize);
        for p in abstraction.abstract_problem.predicates() {
            let pt = tags.get(&p.id).map(Vec::as_slice).unwrap_or(&[]);
            let af = super::disj_abstract::build_atoms(p.id, &p.arg_sorts, pt);
            let al = super::disj_abstract::build_atoms_profiled(
                p.id,
                &p.arg_sorts,
                pt,
                super::disj_abstract::AtomProfile::FlagsOnly,
            );
            atoms_full += af.len();
            max_full = max_full.max(af.len());
            atoms_flags += al.len();
        }

        let fmt = |r: &LearnRun| -> String {
            format!(
                "s={} c={} {:>6}ms",
                if r.solved { "Y" } else { "n" },
                if r.recertified { "Y" } else { "n" },
                r.wall.as_millis()
            )
        };

        let dt_only = std::env::var_os("AY_SWEEP_DT_ONLY").is_some();
        let skip = || LearnRun {
            solved: false,
            recertified: false,
            wall: Duration::ZERO,
        };
        let dnf_full = if dt_only {
            skip()
        } else {
            run_dnf(&abstraction, budget)
        };
        let dt_full = run_dt(&abstraction, budget);
        let dt_flags = run_dt_flags(&abstraction, budget);

        eprintln!(
            "{:<15} {:>4} {:>4} {:>5} {:>4} {:>5} | {:<22} {:<22} {:<22}",
            label,
            n_preds,
            n_clauses,
            atoms_full,
            max_full,
            atoms_flags,
            fmt(&dnf_full),
            fmt(&dt_full),
            fmt(&dt_flags),
        );
    }
    eprintln!("=== END SWEEP ===\n");
}

fn run_dt_nat(abstraction: &CataAbstraction, budget: Duration) -> LearnRun {
    let tags = ice_tags(abstraction);
    let start = Instant::now();
    let model = super::ice_dt::solve_abstract_ice_dt_nat(
        &abstraction.abstract_problem,
        &tags,
        start + budget,
    );
    let wall = start.elapsed();
    match model {
        Some(m) => LearnRun {
            solved: true,
            recertified: recert(&abstraction.abstract_problem, &m),
            wall,
        },
        None => LearnRun {
            solved: false,
            recertified: false,
            wall,
        },
    }
}

fn run_affine(abstraction: &CataAbstraction, budget: Duration) -> LearnRun {
    let tags = ice_tags(abstraction);
    let start = Instant::now();
    let model = super::affine_houdini::solve_abstract_affine(
        &abstraction.abstract_problem,
        &tags,
        start + budget,
    );
    let wall = start.elapsed();
    match model {
        Some(m) => LearnRun {
            solved: true,
            recertified: recert(&abstraction.abstract_problem, &m),
            wall,
        },
        None => LearnRun {
            solved: false,
            recertified: false,
            wall,
        },
    }
}

/// NAT-PEANO SPIKE: for ONE benchmark file (absolute path in `AY_NAT_SPIKE_FILE`)
/// walk EVERY cata ladder level (not just Sorted). At each level: build the
/// abstraction, discharge obligations, dump the abstract LIA, then run the
/// CONJUNCTIVE affine-Houdini vs the DISJUNCTIVE ice-dt / ice-dt-flags / DNF
/// learners, re-certifying each candidate. This proves whether the disjunctive
/// learner converts where the conjunctive one returns unknown, on the nat size
/// abstracts (which have NO Sorted level so the wired route never tries a
/// disjunctive learner today).
///
/// `AY_NAT_SPIKE_FILE=<abs.smt2> AY_NAT_SPIKE_SECS=30 cargo test -p ay-chc \
///   nat_peano_spike -- --ignored --nocapture`
#[test]
#[ignore]
fn nat_peano_spike() {
    let file = match std::env::var("AY_NAT_SPIKE_FILE") {
        Ok(f) => std::path::PathBuf::from(f),
        Err(_) => {
            eprintln!("SKIP: set AY_NAT_SPIKE_FILE to an absolute .smt2 path");
            return;
        }
    };
    let budget = Duration::from_secs(
        std::env::var("AY_NAT_SPIKE_SECS")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(30),
    );
    let dump = std::env::var_os("AY_NAT_SPIKE_DUMP").is_some();
    let smt = std::fs::read_to_string(&file).expect("read benchmark");
    let problem = ChcParser::parse(&smt).expect("parse");
    let ladder = build_cata_ladder(&problem, true);
    eprintln!(
        "\n=== NAT-PEANO SPIKE [{}] : {} ladder levels ===",
        file.display(),
        ladder.len()
    );
    eprintln!(
        "{:<3} {:<28} {:>4} {:>4} {:>5} | {:<20} {:<20} {:<20} {:<20}",
        "L",
        "pool",
        "prd",
        "cls",
        "atom",
        "affine(conj)",
        "ice-dt(disj)",
        "ice-dt-NAT-leq",
        "dnf(disj)",
    );
    let fmt = |r: &LearnRun| -> String {
        format!(
            "s={} c={} {:>6}ms",
            if r.solved { "Y" } else { "n" },
            if r.recertified { "Y" } else { "n" },
            r.wall.as_millis()
        )
    };
    for (level, pool) in ladder.iter().enumerate() {
        let pool_str: String = pool
            .iter()
            .map(|k| format!("{k:?}"))
            .collect::<Vec<_>>()
            .join("+");
        let pool_str = if pool_str.len() > 27 {
            pool_str[..27].to_string()
        } else {
            pool_str
        };
        let abstraction = match CataAbstraction::build(&problem, pool) {
            Ok(a) => a,
            Err(e) => {
                eprintln!("{level:<3} {pool_str:<28} BUILD-SKIP {e:?}");
                continue;
            }
        };
        let discharged = abstraction.discharge_obligations(
            Duration::from_secs(5),
            Some(Instant::now() + Duration::from_secs(60)),
        );
        if !discharged {
            eprintln!("{level:<3} {pool_str:<28} OBLIGATIONS-UNDISCHARGED (fail-closed)");
            continue;
        }
        let n_preds = abstraction.abstract_problem.predicates().len();
        let n_clauses = abstraction.abstract_problem.clauses().len();
        let tags = ice_tags(&abstraction);
        let mut atoms_full = 0usize;
        for p in abstraction.abstract_problem.predicates() {
            let pt = tags.get(&p.id).map(Vec::as_slice).unwrap_or(&[]);
            atoms_full += super::disj_abstract::build_atoms(p.id, &p.arg_sorts, pt).len();
        }
        if dump {
            let script = super::dump_abstract_lia_problem(&abstraction.abstract_problem);
            let out = file.with_extension(format!("abstract_L{level}.smt2"));
            std::fs::write(&out, &script).expect("write dump");
            eprintln!("   dumped {} ({} bytes)", out.display(), script.len());
        }
        let affine = run_affine(&abstraction, budget);
        let dt = run_dt(&abstraction, budget);
        let dt_nat = run_dt_nat(&abstraction, budget);
        let dnf = run_dnf(&abstraction, budget);
        eprintln!(
            "{:<3} {:<28} {:>4} {:>4} {:>5} | {:<20} {:<20} {:<20} {:<20}",
            level,
            pool_str,
            n_preds,
            n_clauses,
            atoms_full,
            fmt(&affine),
            fmt(&dt),
            fmt(&dt_nat),
            fmt(&dnf),
        );
    }
    eprintln!("=== END NAT-PEANO SPIKE ===\n");
}
