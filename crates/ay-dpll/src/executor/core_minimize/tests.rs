// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_core::Sort;

use super::*;
use crate::executor_types::UnknownOrigin;

#[test]
fn minimizer_envelope_restores_completed_sidecar_and_array_markers() {
    let mut executor = Executor::new();
    let proposition = executor
        .ctx
        .terms
        .mk_fresh_var("core_envelope_sidecar_p", Sort::Bool);
    let not_proposition = executor.ctx.terms.mk_not_raw(proposition);
    executor.ctx.assertions = vec![proposition, not_proposition];
    executor.begin_public_solve(false);
    executor.bind_unsat_query_assumptions(&[]);
    let proposed = executor
        .check_sat()
        .expect("contradictory units must solve");
    assert!(proposed.is_unsat());
    assert!(executor.last_checked_sat_refutation.is_some());

    executor.nested_array_row_reduction_unsat = true;
    executor.ho_seq_unfold_array_free_unsat = true;
    let result = executor
        .minimize_assumption_core(&[], Ok(proposed), None, Duration::ZERO)
        .expect("empty-core envelope must not fail");

    assert!(result.is_unsat());
    assert!(executor.last_checked_sat_refutation.is_some());
    assert!(executor.nested_array_row_reduction_unsat);
    assert!(executor.ho_seq_unfold_array_free_unsat);
    assert!(executor.pending_nested_array_bool_bv_unsat.is_none());
}

/// Two named assumptions that contradict each other; the base is stripped
/// (empty), exactly the named-core redirect's precondition.
fn contradictory_named_pair(executor: &mut Executor) -> Vec<TermId> {
    let proposition = executor
        .ctx
        .terms
        .mk_fresh_var("core_envelope_attempt_p", Sort::Bool);
    let not_proposition = executor.ctx.terms.mk_not_raw(proposition);
    executor.ctx.assertions = Vec::new();
    executor.begin_public_solve(false);
    executor.begin_external_decision_query(false);
    vec![proposition, not_proposition]
}

/// Control for the attempt parking (the regression itself lives in
/// `model::evaluation_control::tests`, which can install the evaluator-only
/// stop channel): a stop the ENTRY decision itself recorded is still there
/// after the envelope, and the entry attempt is the one live afterwards —
/// parking discards subset stops, never the decision's own.
#[test]
fn minimizer_keeps_the_stop_the_entry_decision_itself_recorded() {
    let mut executor = Executor::new();
    let named = contradictory_named_pair(&mut executor);
    let entry = executor
        .check_sat_assuming(&named)
        .expect("contradictory assumptions must solve");
    executor.record_evaluation_stop(UnknownOrigin::SolveDeadline);
    let outer = executor.evaluation_attempt();
    let result = executor
        .minimize_assumption_core(&named, Ok(entry), None, Duration::ZERO)
        .expect("minimizer never alters the verdict");
    assert!(result.is_unsat());
    assert!(executor.evaluation_attempt().is_same_attempt(&outer));
    assert_eq!(
        executor.evaluation_stop_origin(),
        Some(UnknownOrigin::SolveDeadline)
    );
    assert!(matches!(executor.last_result, Some(SolveResult::Unsat(_))));
}

/// Parse a named-core script (no `check-sat`) and put the executor exactly
/// where the named-core redirect calls the minimizer: base stripped to the
/// unnamed assertions, named assertions returned as the assumption set.
fn named_core_redirect_setup(script: &str) -> (Executor, Vec<TermId>) {
    let commands = ay_frontend::parse(script).expect("fixture parses");
    let mut executor = Executor::new();
    executor
        .execute_all(&commands)
        .expect("declarations and asserts execute");
    let named: HashSet<TermId> = executor.ctx.named_terms_iter().map(|(_, t)| t).collect();
    let (named_assertions, unnamed): (Vec<TermId>, Vec<TermId>) = executor
        .ctx
        .assertions
        .iter()
        .copied()
        .partition(|t| named.contains(t));
    executor.ctx.assertions = unnamed;
    executor.begin_public_solve(false);
    executor.begin_external_decision_query(false);
    (executor, named_assertions)
}

/// The named-core redirect's ENTRY, exactly as `check_sat.rs` and
/// `check_sat_assuming.rs` run it before calling the minimizer: the deferred
/// plain solve over the named assumptions plus the harvest recheck — and
/// nothing after it. The public `check_sat_assuming` is the wrong entry for
/// a test that then calls `minimize_assumption_core` by hand: its own
/// redirect already runs the pass, so the hand call starts from an
/// already-shrunk core (`start=3` on the five-member transitivity fixture)
/// and every `start` expectation is off.
fn redirect_entry(executor: &mut Executor, named: &[TermId]) -> SolveResult {
    let result = executor.check_sat_assuming_deferred_to_plain_check_sat(named);
    executor
        .certify_assumption_core(named, result)
        .expect("the redirect entry solves")
}

/// `start=.. final=.. attempts=..` from the pass's own statistic.
fn uc_minimize_stat(executor: &Executor) -> Option<(usize, usize, u64)> {
    let stat = executor.statistics().get_string("solver.uc_minimize")?;
    let field = |key: &str| -> Option<u64> {
        stat.split_whitespace()
            .find_map(|kv| kv.strip_prefix(key))
            .and_then(|v| v.parse().ok())
    };
    Some((
        usize::try_from(field("start=")?).ok()?,
        usize::try_from(field("final=")?).ok()?,
        field("attempts=")?,
    ))
}

/// An EUF transitivity refutation plus two irrelevant named asserts. The
/// redirect entry already harvests the three transitivity members on this
/// shape (so `start` reads 3, not 5); what the pass is asked to show is that
/// it RAN and left exactly that three-member core — never a larger one.
const EUF_TRANSITIVITY_WITH_IRRELEVANT: &str = r#"
    (set-option :produce-unsat-cores true)
    (set-logic QF_UF)
    (declare-sort U 0)
    (declare-const a U) (declare-const b U) (declare-const c U)
    (declare-const d U) (declare-const e U) (declare-const f U)
    (assert (! (= a b) :named h1))
    (assert (! (= b c) :named h2))
    (assert (! (not (= a c)) :named h3))
    (assert (! (= d e) :named irr1))
    (assert (! (= e f) :named irr2))
"#;

/// Control for the entry-cost gate: with a free entry (`Duration::ZERO`) the
/// pass runs and shrinks the core.
#[test]
fn free_entry_cost_lets_the_pass_shrink_the_core() {
    let (mut executor, named) = named_core_redirect_setup(EUF_TRANSITIVITY_WITH_IRRELEVANT);
    let entry = redirect_entry(&mut executor, &named);
    assert!(entry.is_unsat());
    let result = executor
        .minimize_assumption_core(&named, Ok(entry), None, Duration::ZERO)
        .expect("minimizer never alters the verdict");
    assert!(result.is_unsat());
    let (start, final_len, _) = uc_minimize_stat(&executor).expect("the pass ran");
    assert!(
        final_len <= start,
        "the pass never grows a core: {start} -> {final_len}"
    );
    assert_eq!(
        final_len, 3,
        "the two irrelevant members are never in the core"
    );
}

/// #uc-minimize-entry-cost: when the shrink budget cannot cover
/// `ENTRY_COST_AFFORDABILITY` entry-sized solves the pass declines before
/// its first attempt, leaving the entry's core bookkeeping untouched. With
/// no deadline installed the budget is `NO_DEADLINE_BUDGET` minus its
/// margin, so an entry cost of a hundred seconds is unaffordable.
#[test]
fn unaffordable_entry_cost_declines_the_pass_before_the_first_attempt() {
    let (mut executor, named) = named_core_redirect_setup(EUF_TRANSITIVITY_WITH_IRRELEVANT);
    let entry = redirect_entry(&mut executor, &named);
    assert!(entry.is_unsat());
    let entry_core = executor.last_assumption_core.clone();
    let entry_assumptions = executor.last_assumptions.clone();
    let unaffordable = Duration::from_secs(100);
    assert!(
        NO_DEADLINE_BUDGET < unaffordable.saturating_mul(ENTRY_COST_AFFORDABILITY),
        "the fixture entry cost must exceed what the no-deadline budget affords"
    );
    let result = executor
        .minimize_assumption_core(&named, Ok(entry), None, unaffordable)
        .expect("minimizer never alters the verdict");
    assert!(result.is_unsat());
    assert_eq!(
        uc_minimize_stat(&executor),
        None,
        "a declined pass records no attempt statistic"
    );
    assert_eq!(executor.last_assumption_core, entry_core);
    assert_eq!(executor.last_assumptions, entry_assumptions);
    assert!(matches!(executor.last_result, Some(SolveResult::Unsat(_))));
}

/// The boundary of the gate: an entry cost the budget affords exactly
/// (`shrink_budget == ENTRY_COST_AFFORDABILITY x entry`) still runs.
#[test]
fn affordable_entry_cost_at_the_boundary_runs_the_pass() {
    let (mut executor, named) = named_core_redirect_setup(EUF_TRANSITIVITY_WITH_IRRELEVANT);
    let entry = redirect_entry(&mut executor, &named);
    // No deadline: remaining = NO_DEADLINE_BUDGET, margin = clamp(remaining/8,
    // 3s, 10s), shrink = remaining - margin.
    let margin = (NO_DEADLINE_BUDGET / 8).clamp(Duration::from_secs(3), Duration::from_secs(10));
    let shrink_budget = NO_DEADLINE_BUDGET
        .checked_sub(margin)
        .expect("the clamped margin fits the no-deadline budget");
    let boundary = shrink_budget / ENTRY_COST_AFFORDABILITY;
    let result = executor
        .minimize_assumption_core(&named, Ok(entry), None, boundary)
        .expect("minimizer never alters the verdict");
    assert!(result.is_unsat());
    let (start, final_len, _) = uc_minimize_stat(&executor).expect("the pass ran at the boundary");
    assert!(
        final_len <= start,
        "the pass never grows a core: {start} -> {final_len}"
    );
    assert_eq!(final_len, 3);
}

/// Clears the test-only probe budget override on every exit path.
struct ProbeBudgetOverride;

impl ProbeBudgetOverride {
    fn install(budget: Duration) -> Self {
        set_probe_budget_override_for_test(Some(budget));
        Self
    }
}

impl Drop for ProbeBudgetOverride {
    fn drop(&mut self) {
        set_probe_budget_override_for_test(None);
    }
}

/// deductive-checks's 64-bit `bvmul` overflow obligation (`return_position_overflow`
/// harness): a five-member named core over a bit-blasted multiplier. Every
/// subset attempt re-bit-blasts and re-solves; an adoption also pays the
/// strict re-verification. z3: unsat.
const QFBV_RETURN_POSITION_OVERFLOW: &str = include_str!(
    "../../../tests/fixtures/deductive_checks_qfbv_return_position_overflow_named_core.smt2"
);

fn without_check_sat(script: &str) -> String {
    script.replace("(check-sat)", "")
}

/// #uc-minimize-entry-cost, probe-undecided stop: when the FIRST attempt of
/// non-array content runs its whole budget without deciding its subset, the
/// pass stops after that one attempt and restores the entry's core
/// bookkeeping. The test-only override installs an already-expired first
/// probe deadline, so the stop and restoration assertions do not race the
/// subset solver against the machine's speed.
#[test]
fn undecided_probe_stops_the_pass_after_one_attempt() {
    let (mut executor, named) =
        named_core_redirect_setup(&without_check_sat(QFBV_RETURN_POSITION_OVERFLOW));
    let entry = redirect_entry(&mut executor, &named);
    assert!(entry.is_unsat());
    let entry_core = executor.last_assumption_core.clone();
    let entry_assumptions = executor.last_assumptions.clone();
    let _override = ProbeBudgetOverride::install(Duration::ZERO);
    let result = executor
        .minimize_assumption_core(&named, Ok(entry), None, Duration::ZERO)
        .expect("minimizer never alters the verdict");
    assert!(result.is_unsat());
    let (start, final_len, attempts) = uc_minimize_stat(&executor).expect("the pass ran");
    assert_eq!(start, named.len());
    assert_eq!(final_len, start, "an undecided probe adopts nothing");
    assert_eq!(attempts, 1, "the pass stops at the undecided probe");
    assert_eq!(executor.last_assumption_core, entry_core);
    assert_eq!(executor.last_assumptions, entry_assumptions);
    assert!(matches!(executor.last_result, Some(SolveResult::Unsat(_))));
}

/// Control for the probe-undecided stop: the same fixture with the ordinary
/// probe budget decides its subsets and the scan proceeds past attempt one.
/// (The pass may or may not adopt on this machine — that depends on whether
/// an adoption's strict re-verification fits the per-attempt cap — but an
/// EUF-cheap instance is the wrong control for a stop keyed on the probe
/// running its budget out, so the assertion is only that the probe rule did
/// not fire: more than one attempt was made.)
#[test]
fn decided_probe_lets_the_scan_continue() {
    let (mut executor, named) = named_core_redirect_setup(EUF_TRANSITIVITY_WITH_IRRELEVANT);
    let entry = redirect_entry(&mut executor, &named);
    let result = executor
        .minimize_assumption_core(&named, Ok(entry), None, Duration::ZERO)
        .expect("minimizer never alters the verdict");
    assert!(result.is_unsat());
    let (_, _, attempts) = uc_minimize_stat(&executor).expect("the pass ran");
    assert!(
        attempts > 1,
        "a decided probe never stops the scan: {attempts}"
    );
}

#[test]
fn core_subset_nomination_scope_restores_nested_and_ordinary_postures() {
    let mut executor = Executor::new();
    assert!(!executor.core_subset_nomination);
    executor.with_core_subset_nomination(|executor| {
        assert!(executor.core_subset_nomination);
        assert!(!executor.certification_resolve);
        executor.with_core_subset_nomination(|executor| {
            assert!(executor.core_subset_nomination);
        });
        assert!(executor.core_subset_nomination);
        let derived = executor.new_derived_query_executor();
        assert!(derived.core_shrinking_suppressed);
        assert!(!derived.core_subset_nomination);
    });
    assert!(!executor.core_subset_nomination);
    assert!(!executor.certification_resolve);
    assert!(!executor.core_shrinking_suppressed);
}

#[test]
fn core_subset_nomination_scope_restores_after_unwind() {
    let mut executor = Executor::new();
    let panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        executor.with_core_subset_nomination(|executor| {
            assert!(executor.core_subset_nomination);
            panic!("test unwind from a private subset nomination");
        });
    }));
    assert!(panic.is_err());
    assert!(!executor.core_subset_nomination);
    assert!(!executor.certification_resolve);
}

/// SMT-COMP 2026 uc-qf-linearintarith, QF_LIA/d2c76902 (scrambled): 39 named
/// assertions, of which the redirect harvests 19. opensmt publishes 9.
const QF_LIA_UC_D2C76902: &str =
    include_str!("../../../tests/fixtures/smtcomp2026_uc_qf_lia_d2c76902.smt2");

/// The named assertions of `script` whose labels are in `labels`, as a fresh
/// script: the reduced benchmark SMT-COMP's validators re-solve.
fn reduced_script(script: &str, labels: &[String]) -> String {
    script
        .lines()
        .filter(|line| {
            if !line.starts_with("(assert") {
                return !line.starts_with("(get-unsat-core") && !line.starts_with("(exit");
            }
            labels
                .iter()
                .any(|label| line.ends_with(&format!(":named {label}))")))
        })
        .collect::<Vec<_>>()
        .join("\n")
}

/// AY-SMT-4: the general minimizer's cap bounds the deletion scan, so it is
/// measured on the scan's start set (the certified harvest), not on the named
/// count. With the cap on the named count this 39-named instance declined at
/// the gate and kept its 19-member harvest. The reduced core must be a real
/// core: a fresh executor re-solves exactly its members and answers unsat.
#[test]
fn harvest_below_the_cap_is_minimized_when_the_named_set_is_above_it() {
    let script = QF_LIA_UC_D2C76902
        .replace("(check-sat)", "")
        .replace("(get-unsat-core)", "")
        .replace("(exit)", "");
    let (mut executor, named) = named_core_redirect_setup(&script);
    assert_eq!(named.len(), 39);
    let entry = redirect_entry(&mut executor, &named);
    assert!(entry.is_unsat());
    let harvest = executor
        .last_assumption_core
        .clone()
        .expect("the redirect certifies its harvest");
    assert!(harvest.len() <= GENERAL_MINIMIZE_CAP && harvest.len() < named.len());
    let result = executor
        .minimize_assumption_core(&named, Ok(entry), None, Duration::ZERO)
        .expect("minimizer never alters the verdict");
    assert!(result.is_unsat());
    let (start, final_len, _) = uc_minimize_stat(&executor).expect("the pass ran");
    assert_eq!(start, harvest.len());
    assert!(
        final_len < start,
        "the scan shrinks the harvest: {start} -> {final_len}"
    );
    let core = executor
        .last_assumption_core
        .clone()
        .expect("an adopted core is pinned");
    assert_eq!(core.len(), final_len);
    let labels: Vec<String> = executor
        .ctx
        .named_terms_iter()
        .filter(|(_, term)| core.contains(term))
        .map(|(name, _)| name.to_string())
        .collect();
    assert_eq!(labels.len(), core.len());

    let reduced = reduced_script(QF_LIA_UC_D2C76902, &labels);
    let commands = ay_frontend::parse(&reduced).expect("the reduced benchmark parses");
    let mut fresh = Executor::new();
    let outputs = fresh
        .execute_all(&commands)
        .expect("the reduced benchmark runs");
    assert_eq!(
        outputs.first().map(String::as_str),
        Some("unsat"),
        "the reduced core must be unsatisfiable on its own"
    );
}
