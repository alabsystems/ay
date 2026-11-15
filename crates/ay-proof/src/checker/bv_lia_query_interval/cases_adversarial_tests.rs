// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Additional refusal-boundary controls; no solver or proof-policy overrides.

use ay_core::TermStore;

use super::super::super::authenticate_bv_lia_unsat_query;
use super::*;

fn false_constant_clause() -> Vec<Vec<ClauseLiteral>> {
    vec![vec![ClauseLiteral::Arithmetic {
        form: LinearForm::constant(BigInt::one()),
        relation: Relation::LessOrEqual,
    }]]
}

fn unbounded_atom(atom: LinearAtom) -> IntervalState {
    IntervalState {
        bounds: HashMap::from([(atom, Interval::default())]),
        ..IntervalState::default()
    }
}

#[test]
fn literal_share_exhaustion_precedes_a_would_be_conflict() {
    let terms = TermStore::new();
    let clauses = false_constant_clause(); // 1 <= 0.
    let mut positive = QueryChecker::new(&terms, None);
    assert!(matches!(
        positive
            .propagate_interval_clauses(&clauses, &mut IntervalState::default(), 0)
            .unwrap(),
        AssumeOutcome::Conflict
    ));

    let mut checked = QueryChecker::new(&terms, None);
    checked.meter.work = MAX_INTERVAL_WORK - 2;
    assert!(matches!(
        checked
            .propagate_interval_clauses(&clauses, &mut IntervalState::default(), 0)
            .unwrap(),
        AssumeOutcome::Decline
    ));
    // Clause entry costs one; literal_truth plus its empty form cost two.
    // Refusal must occur before confirm_interval_conflict adds another unit.
    assert_eq!(checked.meter.work, MAX_INTERVAL_WORK + 1);
}

#[test]
fn assumption_share_exhaustion_precedes_a_would_be_conflict() {
    let mut terms = TermStore::new();
    let atom = LinearAtom::Int(terms.mk_var("indivisible_x", Sort::Int));
    let clauses = vec![vec![ClauseLiteral::Arithmetic {
        form: LinearForm {
            constant: BigInt::from(-1),
            atoms: BTreeMap::from([(atom, BigInt::from(2))]),
        },
        relation: Relation::Equal,
    }]]; // 2*x = 1: initially unknown, then integer tightening conflicts.
    let mut positive = QueryChecker::new(&terms, None);
    assert!(matches!(
        positive
            .propagate_interval_clauses(&clauses, &mut unbounded_atom(atom), 0)
            .unwrap(),
        AssumeOutcome::Conflict
    ));

    // Measure only the two existing primitive operations, not a replacement
    // implementation of propagation. Both must exercise their stated path.
    let mut primitive = QueryChecker::new(&terms, None);
    let mut state = unbounded_atom(atom);
    assert_eq!(
        primitive.literal_truth(&clauses[0][0], &state).unwrap(),
        None
    );
    let truth_work = primitive.meter.work;
    assert!(matches!(
        primitive
            .assume_literal(&clauses[0][0], &mut state)
            .unwrap(),
        AssumeOutcome::Conflict
    ));
    let assumption_work = primitive.meter.work - truth_work;
    assert!(truth_work > 0 && assumption_work > 0);
    assert_eq!(state.bounds[&atom].upper, Some(BigInt::zero()));

    let mut checked = QueryChecker::new(&terms, None);
    checked.meter.work = MAX_INTERVAL_WORK - 1 - truth_work;
    let mut state = unbounded_atom(atom);
    assert!(matches!(
        checked
            .propagate_interval_clauses(&clauses, &mut state, 0)
            .unwrap(),
        AssumeOutcome::Decline
    ));
    assert_eq!(state.bounds[&atom].upper, Some(BigInt::zero()));
    assert_eq!(checked.meter.work, MAX_INTERVAL_WORK + assumption_work);
}

#[test]
fn final_conflict_checks_an_expired_deadline_below_a_sampling_bucket() {
    let terms = TermStore::new();
    let clauses = false_constant_clause();
    let mut positive = QueryChecker::new(&terms, None);
    assert!(matches!(
        positive
            .propagate_interval_clauses(&clauses, &mut IntervalState::default(), 0)
            .unwrap(),
        AssumeOutcome::Conflict
    ));

    // The direct helper has no entry check. These few charges cannot cross
    // the meter's 2^14 sampling boundary; acceptance needs the fresh check.
    let mut checked = QueryChecker::new(&terms, Some(ay_core::time::Instant::now()));
    assert!(matches!(
        checked.propagate_interval_clauses(&clauses, &mut IntervalState::default(), 0),
        Err(BvLiaUnsatAuthenticationError::ResourceLimit {
            resource: "caller deadline"
        })
    ));
    assert!(checked.meter.work > 0 && checked.meter.work < (1 << 14));
}

#[test]
fn ordinary_case_copy_bytes_refuse_before_charging_or_cloning() {
    // A real, finite table just beyond the existing 512-byte-per-bound
    // conservative allowance; no forged limb counter or arithmetic overflow.
    let count = MAX_CASE_COPY_BYTES / 512;
    let mut terms = TermStore::new();
    let mut source = IntervalState::default();
    for i in 0..count {
        let atom = LinearAtom::Int(terms.mk_var(format!("copy_boundary_{i}"), Sort::Int));
        source.bounds.insert(atom, Interval::default());
    }
    let extra = LinearAtom::Int(terms.mk_var("copy_boundary_extra", Sort::Int));
    source.bounds.insert(extra, Interval::default());
    assert_eq!(source.bounds.len(), count + 1);
    assert_eq!(source.bound_limbs, 0);
    let mut checked = QueryChecker::new(&terms, None);
    assert!(checked
        .copy_interval_case_state(&source, 0)
        .unwrap()
        .is_none());
    assert_eq!(
        checked.meter.work, 0,
        "byte refusal precedes copy precharge"
    );

    source.bounds.remove(&extra).unwrap();
    let mut copy = checked
        .copy_interval_case_state(&source, 0)
        .unwrap()
        .expect("the exact byte-boundary table fits");
    assert_eq!(copy.bounds.len(), count);
    let atom = *copy.bounds.keys().next().unwrap();
    copy.bounds.get_mut(&atom).unwrap().upper = Some(BigInt::zero());
    copy.bound_limbs = 1;
    assert_eq!(source.bounds[&atom].upper, None, "the copy owns its bounds");
    assert_eq!(source.bound_limbs, 0);
}

fn reachable_nodes(terms: &TermStore, root: TermId) -> usize {
    let mut pending = vec![root];
    let mut seen = BTreeSet::new();
    while let Some(term) = pending.pop() {
        if seen.insert(term) {
            pending.extend(terms.children(term));
        }
    }
    seen.len()
}

fn padded_raw_ite(terms: &mut TermStore, padding: usize) -> TermId {
    let guard = terms.mk_var("node_guard", Sort::Bool);
    let zero = terms.mk_int(0.into());
    let one = terms.mk_int(1.into());
    let value = terms.mk_ite_raw(guard, zero, one);
    let equality = terms.mk_app(Symbol::named("="), [value, zero], Sort::Bool);
    let mut conjuncts = vec![equality];
    for i in 0..padding {
        conjuncts.push(terms.mk_var(format!("node_padding_{i}"), Sort::Bool));
    }
    terms.mk_app(Symbol::named("and"), conjuncts, Sort::Bool)
}

#[test]
fn source_node_boundary_keeps_the_raw_ite_and_refuses_the_whole_walk() {
    // Six shared core nodes plus padding: guard, 0, 1, ITE, equality, and.
    // These pin the reviewed 4096-node admission policy without exporting it.
    for (padding, expected) in [(4090, Some(2)), (4091, None)] {
        let mut terms = TermStore::new();
        let root = padded_raw_ite(&mut terms, padding);
        assert_eq!(reachable_nodes(&terms, root), padding + 6);
        let mut checked = QueryChecker::new(&terms, None);
        let mut clauses = Vec::new();
        let mut nodes = MAX_FORM_NODES;
        assert_eq!(
            checked
                .append_source_ite_clauses(&[root], &mut clauses, &mut nodes, 0)
                .unwrap(),
            expected
        );
        assert_eq!(clauses.len(), expected.unwrap_or(0));
    }
}

fn many_raw_ites(terms: &mut TermStore, count: usize) -> TermId {
    let zero = terms.mk_int(0.into());
    let one = terms.mk_int(1.into());
    let mut conjuncts = Vec::new();
    for i in 0..count {
        let guard = terms.mk_var(format!("ite_limit_guard_{i}"), Sort::Bool);
        let value = terms.mk_ite_raw(guard, zero, one);
        conjuncts.push(terms.mk_app(Symbol::named("="), [value, zero], Sort::Bool));
    }
    terms.mk_app(Symbol::named("and"), conjuncts, Sort::Bool)
}

#[test]
fn ite_count_boundary_is_complete_or_retains_no_projection_prefix() {
    for (count, expected) in [(32, Some(64)), (33, None)] {
        let mut terms = TermStore::new();
        let root = many_raw_ites(&mut terms, count);
        assert_eq!(reachable_nodes(&terms, root), 3 * count + 3);
        let mut checked = QueryChecker::new(&terms, None);
        let mut clauses = Vec::new();
        let mut nodes = MAX_FORM_NODES;
        assert_eq!(
            checked
                .append_source_ite_clauses(&[root], &mut clauses, &mut nodes, 0)
                .unwrap(),
            expected
        );
        assert_eq!(clauses.len(), expected.unwrap_or(0));
    }
}

fn pinned_remainder_witness(
    terms: &mut TermStore,
    dividend: i64,
    divisor: i64,
    witness: i64,
    variable_divisor: bool,
) -> Vec<TermId> {
    assert!(divisor > 0);
    assert_eq!(dividend.rem_euclid(divisor), witness);
    let x = terms.mk_var("witness_dividend", Sort::Int);
    let d = terms.mk_int(divisor.into());
    let mut roots = Vec::new();
    let denominator = if variable_divisor {
        let variable = terms.mk_var("witness_divisor", Sort::Int);
        roots.push(terms.mk_app(Symbol::named("="), [variable, d], Sort::Bool));
        variable
    } else {
        d
    };
    let value = terms.mk_int(dividend.into());
    roots.push(terms.mk_app(Symbol::named("="), [x, value], Sort::Bool));
    let remainder = terms.mk_app(Symbol::named("mod"), [x, denominator], Sort::Int);
    // Exclude EVERY other residue. Dropping the actual witness case would
    // manufacture UNSAT, including at the upper endpoint beyond divisor16.
    for residue in 0..divisor {
        if residue != witness {
            let value = terms.mk_int(residue.into());
            let equality = terms.mk_app(Symbol::named("="), [remainder, value], Sort::Bool);
            roots.push(terms.mk_not_raw(equality));
        }
    }
    roots
}

#[test]
fn variable_divisors_keep_their_pinned_actual_sat_witnesses() {
    for (divisor, dividend, witness) in [(2, 1, 1), (3, 2, 2), (17, 16, 16)] {
        let mut terms = TermStore::new();
        let roots = pinned_remainder_witness(&mut terms, dividend, divisor, witness, true);
        assert!(matches!(
            authenticate_bv_lia_unsat_query(&terms, &roots, None),
            Err(BvLiaUnsatAuthenticationError::Satisfiable)
        ));
    }
}

#[test]
fn negative_dividends_keep_their_euclidean_actual_sat_witnesses() {
    for (dividend, divisor, witness) in [(-1, 2, 1), (-2, 3, 1), (-4, 3, 2), (-17, 16, 15)] {
        let mut terms = TermStore::new();
        let roots = pinned_remainder_witness(&mut terms, dividend, divisor, witness, false);
        assert!(matches!(
            authenticate_bv_lia_unsat_query(&terms, &roots, None),
            Err(BvLiaUnsatAuthenticationError::Satisfiable)
        ));
    }
}
