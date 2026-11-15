// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The forged-UNSAT guard re-decides the authored problem over a rebuilt
//! arena, returns the same verdicts, and returns at its budget.

use std::time::Duration;

use ay_core::time::Instant;
use ay_core::{Sort, Symbol, TermData, TermId};
use ay_frontend::Command;

use crate::executor::Executor;
use crate::executor_types::SolveResult;

const NESTED_ROW: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../benchmarks/smt/model_checker_consumer_quantified_counterexample/nested_query_false_unsat.smt2"
));
const IOS_ROW: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../benchmarks/smt/QF_ALIA/smtlib_regression/ios_t1_ios_bia_np_sf_ai_00005_001.cvc.smt2"
));

/// The differential gate's uf-arith `g6_100000/g6_100167` (QF_UFLIA, unsat).
const G6_100167: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../benchmarks/smt/abort/unsat_uflia_div0_forged_guard_g6_100167.smt2"
));

/// Solve `script` the way `ay solve` does by default (best-effort proof
/// collection with the CLI's reconstruction budget), so the arena carries the
/// outer solve's proof-planning scratch when certification runs. Returns the
/// executor, the authored assertions, and the verdict.
fn solve_like_the_cli(script: &str) -> (Executor, Vec<TermId>, SolveResult) {
    let mut exec = Executor::new();
    exec.set_best_effort_produce_proofs(1_000_000);
    for command in &ay_frontend::parse(script).expect("parse the fixture") {
        if matches!(command, Command::CheckSat) {
            break;
        }
        exec.execute(command).expect("execute the fixture");
    }
    let authored = exec.ctx.assertions.clone();
    let solved = exec.check_sat().expect("the fixture solves");
    (exec, authored, solved)
}

/// [`solve_like_the_cli`] on a fixture AY refutes.
fn solved_like_the_cli(script: &str) -> (Executor, Vec<TermId>) {
    let (exec, authored, solved) = solve_like_the_cli(script);
    assert!(
        solved.is_unsat(),
        "the fixture is unsatisfiable: {solved:?}"
    );
    (exec, authored)
}

/// Intern unasserted proof-planning scaffolding over `subject` (the
/// reflexive-equality fold bridge's residue that d9ccc7a45 measured): no
/// assertion names it. Returns how many fresh terms it interned.
fn scaffolding(exec: &mut Executor, subject: TermId) -> usize {
    let before = exec.ctx.terms.len();
    let terms = &mut exec.ctx.terms;
    let reflexive = terms.mk_app(Symbol::named("="), [subject, subject], Sort::Bool);
    assert!(
        matches!(terms.get(reflexive), TermData::App(..)),
        "un-folded reflexive node"
    );
    let _negated = terms.mk_not_raw(reflexive);
    let true_term = terms.true_term();
    let _lifted = terms.mk_app(Symbol::named("="), [reflexive, true_term], Sort::Bool);
    exec.ctx.terms.len() - before
}

#[test]
fn the_rebuild_reclaims_what_the_authored_roots_never_name() {
    let mut exec = Executor::new();
    let p = exec.ctx.terms.mk_var("guard_arena_p", Sort::Bool);
    let not_p = exec.ctx.terms.mk_not_raw(p);
    let interned = scaffolding(&mut exec, p);
    assert!(interned >= 3, "fixture: scaffolding was interned");
    let caller_arena = exec.ctx.terms.len();

    let mut derived = exec.new_derived_query_executor();
    derived.ctx.assertions = vec![not_p];
    assert_eq!(
        derived.ctx.terms.len(),
        caller_arena,
        "the clone copies it all"
    );
    assert!(exec.rebuild_forged_guard_arena(&mut derived));
    assert!(
        derived.ctx.terms.len() + interned <= caller_arena,
        "the rebuilt arena drops the {interned} unnamed scaffolding terms: {} of {caller_arena}",
        derived.ctx.terms.len()
    );
    let root = derived.ctx.assertions[0];
    assert!(
        matches!(derived.ctx.terms.get(root), TermData::Not(_)),
        "the authored root survives, relabelled, as the same term"
    );
    assert_eq!(
        exec.ctx.terms.len(),
        caller_arena,
        "the caller's arena is untouched"
    );

    // No room beside the clone for the compacted copy: the guard re-decides
    // over the clone as it stands, as before the rebuild -- it never abstains.
    let mut tight = exec.new_derived_query_executor();
    tight.ctx.assertions = vec![not_p];
    exec.set_memory_limit(Some(1));
    assert!(exec.rebuild_forged_guard_arena(&mut tight));
    assert_eq!(
        tight.ctx.terms.len(),
        caller_arena,
        "the clone is kept whole"
    );
}

/// A-UFA-g6-div0, the forged-guard leg (differential gate uf-arith
/// `g6_100167`). `mod_div_elim` spells a dividend's `TermId` INTO the name
/// `__ay_zerodiv_{op}_{index}` and parses it back; relabelling cannot reach
/// those digits. Scratch interned BELOW the dividend makes a compaction move
/// it, so a rebuilt guard arena would decode the name to some other term (in
/// b288f5e6f5's CLI run: index 80 in a 77-term arena, a panic in the nested
/// solve). The guard must re-decide over an arena whose spelled ids still name
/// what they were minted for: the clone, untouched.
#[test]
fn the_rebuild_keeps_an_arena_whose_names_spell_term_ids() {
    let mut exec = Executor::new();
    let p = exec.ctx.terms.mk_var("guard_names_p", Sort::Bool);
    let interned = scaffolding(&mut exec, p);
    assert!(
        interned >= 3,
        "fixture: reclaimable scratch below the dividend"
    );
    let dividend = exec.ctx.terms.mk_var("guard_names_x", Sort::Int);
    let spelled = format!("__ay_zerodiv_div_{}", dividend.index());
    let _zero_divisor = exec.ctx.terms.mk_var(spelled.clone(), Sort::Int);
    let not_p = exec.ctx.terms.mk_not_raw(p);
    let caller_arena = exec.ctx.terms.len();

    let mut derived = exec.new_derived_query_executor();
    derived.ctx.assertions = vec![not_p];
    assert!(
        exec.rebuild_forged_guard_arena(&mut derived),
        "a name-spelled id is no reason to abstain: the clone is re-decided as it stands"
    );
    assert_eq!(
        derived.ctx.terms.len(),
        caller_arena,
        "`{spelled}` spells an id, so the guard's arena is the untouched clone"
    );
    let decoded = TermId::new(u32::try_from(dividend.index()).expect("fixture index fits u32"));
    assert!(
        derived.ctx.terms.entry_stamp(decoded).is_some()
            && matches!(
                derived.ctx.terms.get(decoded),
                TermData::Var(name, _) if name == "guard_names_x"
            ),
        "`{spelled}` must still decode to its dividend in the guard's arena"
    );
    assert_eq!(derived.ctx.assertions, vec![not_p], "the root keeps its id");
}

/// The same leg end to end: the forged-guard re-solve of g6_100167's authored
/// problem, after the outer solve minted `__ay_zerodiv_*` names into the
/// arena. On b288f5e6f5 the nested solve decoded a stale spelled id and
/// panicked (`index out of bounds`) inside `eliminate_int_mod_div`.
#[test]
fn forged_guard_resolves_a_zero_divisor_query_without_decoding_a_stale_id() {
    let (exec, authored) = solved_like_the_cli(G6_100167);
    assert!(
        (0..exec.ctx.terms.len()).any(|index| matches!(
            exec.ctx.terms.get(TermId::new(u32::try_from(index).expect("index fits u32"))),
            TermData::Var(name, _) if name.starts_with("__ay_zerodiv_")
        )),
        "fixture: the outer solve minted a zero-divisor name"
    );
    assert!(
        !exec.redecides_definitive_sat_within(&authored, &guard_controls(&exec, None)),
        "g6_100167 is unsatisfiable (z3 5.1.0: unsat); it is never re-decided SAT"
    );
}

#[test]
fn forged_guard_verdicts_are_unchanged_over_a_rebuilt_arena() {
    let mut sat = Executor::new();
    let p = sat.ctx.terms.mk_var("guard_rebuild_p", Sort::Bool);
    let q = sat.ctx.terms.mk_var("guard_rebuild_q", Sort::Bool);
    let not_q = sat.ctx.terms.mk_not_raw(q);
    sat.ctx.assertions = vec![p, not_q];
    scaffolding(&mut sat, p);
    let caller_arena = sat.ctx.terms.len();
    assert!(
        sat.redecides_definitive_sat_within(&[p, not_q], &guard_controls(&sat, None)),
        "a satisfiable authored problem is still re-decided SAT"
    );
    assert_eq!(
        sat.ctx.terms.len(),
        caller_arena,
        "only the nested copy is rebuilt"
    );

    let mut unsat = Executor::new();
    let p = unsat
        .ctx
        .terms
        .mk_var("guard_rebuild_contradiction", Sort::Bool);
    let not_p = unsat.ctx.terms.mk_not_raw(p);
    unsat.ctx.assertions = vec![p, not_p];
    scaffolding(&mut unsat, p);
    let caller_arena = unsat.ctx.terms.len();
    assert!(
        !unsat.redecides_definitive_sat_within(&[p, not_p], &guard_controls(&unsat, None)),
        "a contradiction is never re-decided SAT"
    );
    assert_eq!(
        unsat.ctx.terms.len(),
        caller_arena,
        "only the nested copy is rebuilt"
    );
}

/// The model-checker-consumer nested row: after the outer solve the arena holds ~25,800
/// terms, almost all proof-planning scratch. Over that whole arena the
/// guard's re-solve ran to (and past) its 250 ms budget undecided (313-1087
/// ms in the CLI, 430 ms here, at ad60a0707). The guard's copy keeps only what
/// the authored roots name, and over it the guard's question is DECIDED: the
/// re-solve reaches the ground refutation, not a deadline.
///
/// #nested-array-quarantine-datatype-fields RE-PIN. The row keeps arrays in
/// the datatype fields of an outer array's elements, so its trust-only ground
/// refutation is now withheld by the nested-array quarantine: the outer solve
/// answers `unknown` (the arena still holds 25,821 terms), and the rebuilt
/// re-solve reaches the refutation and reports that gate (`incomplete`)
/// where it used to answer `unsat`. That stays separable from the deadline
/// bug: over the WHOLE arena the same re-solve under the guard's 250 ms budget
/// ends `unknown` with reason `timeout` (phase `ground-result-mapping`, after
/// 430-470 ms, measured with this re-pin).
#[test]
fn forged_guard_decides_the_nested_row_over_the_terms_it_names() {
    let (exec, authored, solved) = solve_like_the_cli(NESTED_ROW);
    assert!(
        matches!(solved, SolveResult::Unknown),
        "the nested row's trust-only refutation is withheld, never sat: {solved:?}"
    );
    let outer_arena = exec.ctx.terms.len();
    let mut derived = exec.new_derived_query_executor();
    derived.ctx.assertions = authored.clone();
    assert!(exec.rebuild_forged_guard_arena(&mut derived));
    assert!(
        derived.ctx.terms.len() * 4 < outer_arena,
        "the guard's arena keeps only what the authored roots name \
         ({} rebuilt of {outer_arena})",
        derived.ctx.terms.len()
    );
    derived.set_solve_controls(None, Instant::now().checked_add(Duration::from_secs(60)));
    let decided = derived.check_sat();
    assert!(
        matches!(decided, Ok(SolveResult::Unknown)),
        "the rebuilt arena asks the same question: {decided:?}"
    );
    assert_eq!(
        (
            derived.statistics().get_string("unknown.reason"),
            derived.statistics().get_string("unknown.phase")
        ),
        (Some("incomplete"), Some("array-combination-quarantine")),
        "it reaches the ground refutation, which the nested-array quarantine \
         withholds, rather than a deadline"
    );
    assert!(
        !exec.redecides_definitive_sat_within(&authored, &guard_controls(&exec, Some(250))),
        "a refutation is never re-decided SAT"
    );
}

/// The ios row, undecided at a 250 ms budget. The lazy split loop's
/// model-to-theory sync asserts every active atom, and on this array model
/// each assertion re-scans the array equalities; the sync polled nothing, so
/// a 250 ms re-solve of the authored problem ran seconds past its deadline
/// (6.4 s here at ad60a0707) and so did the guard (6.4 s here, 5.2 s in the
/// CLI). Each sync assertion now polls the deadline the iteration head polls:
/// the re-solve over the whole outer arena (no rebuild) and the guard both
/// return at their deadline.
#[test]
fn the_lazy_split_resolve_and_the_guard_return_at_their_deadline_on_the_ios_row() {
    let (exec, authored) = solved_like_the_cli(IOS_ROW);
    let mut derived = exec.new_derived_query_executor();
    derived.ctx.assertions = authored.clone();
    derived.set_ground_budget_enabled(false);
    derived.set_solve_controls(None, Instant::now().checked_add(Duration::from_millis(250)));
    let started = Instant::now();
    let result = derived.check_sat();
    let elapsed = started.elapsed();
    assert!(
        !matches!(result, Ok(ref verdict) if verdict.is_sat()),
        "the authored problem is unsatisfiable: {result:?}"
    );
    assert!(
        elapsed < Duration::from_millis(2_500),
        "the 250 ms re-solve returned after {elapsed:?}"
    );

    let started = Instant::now();
    assert!(!exec.redecides_definitive_sat_within(&authored, &guard_controls(&exec, Some(250))));
    let elapsed = started.elapsed();
    assert!(
        elapsed < Duration::from_millis(2_500),
        "the guard's 250 ms re-solve returned after {elapsed:?}"
    );
}

/// The guard's envelope over `exec`'s own count, with an optional backstop
/// `backstop_ms` from now (the guard's only remaining clock is a backstop).
fn guard_controls(
    exec: &Executor,
    backstop_ms: Option<u64>,
) -> crate::api::proofs::TrustClauseDischargeControls {
    crate::api::proofs::TrustClauseDischargeControls::new(
        None,
        backstop_ms.and_then(|ms| Instant::now().checked_add(Duration::from_millis(ms))),
        exec.memory_limit(),
        exec.term_memory_limit(),
        crate::api::proofs::CertificationEffort::for_query(exec),
    )
}
