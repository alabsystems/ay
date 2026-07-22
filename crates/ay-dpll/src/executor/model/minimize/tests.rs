// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_int_candidates_zero_returns_zero() {
    let candidates = int_candidates(&BigInt::zero());
    assert_eq!(candidates, vec![BigInt::zero()]);
}

#[test]
fn test_int_candidates_large_positive() {
    let candidates = int_candidates(&BigInt::from(100));
    assert!(candidates[0].is_zero());
    assert_eq!(candidates[1], BigInt::one());
    assert!(candidates.len() > 2);
}

#[test]
fn test_int_candidates_one_includes_neg_one() {
    let candidates = int_candidates(&BigInt::one());
    // 0, 1, -1 all have magnitude <= 1
    assert_eq!(
        candidates,
        vec![BigInt::zero(), BigInt::one(), BigInt::from(-1)]
    );
}

#[test]
fn test_bv_candidates_zero_returns_zero() {
    let candidates = bv_candidates(&BigInt::zero(), 8);
    assert_eq!(candidates, vec![BigInt::zero()]);
}

#[test]
fn test_bv_candidates_has_expected_values() {
    let candidates = bv_candidates(&BigInt::from(255), 8);
    assert!(candidates.contains(&BigInt::zero()));
    assert!(candidates.contains(&BigInt::one()));
    assert!(candidates.contains(&BigInt::from(255))); // max unsigned
}

#[test]
fn test_rational_candidates_zero_returns_zero() {
    let candidates = rational_candidates(&BigRational::zero());
    assert_eq!(candidates, vec![BigRational::zero()]);
}

#[test]
fn test_int_candidates_large_includes_powers_of_10() {
    // For a large value like 1000, candidates should include powers of 10
    let candidates = int_candidates(&BigInt::from(1000));
    assert!(candidates.contains(&BigInt::zero()));
    assert!(candidates.contains(&BigInt::one()));
    assert!(
        candidates.contains(&BigInt::from(10)),
        "should include 10 for large positive values"
    );
    assert!(
        candidates.contains(&BigInt::from(100)),
        "should include 100 for large positive values"
    );
}

#[test]
fn test_int_candidates_negative_large_includes_negative_powers_of_10() {
    let candidates = int_candidates(&BigInt::from(-500));
    assert!(candidates.contains(&BigInt::zero()));
    assert!(
        candidates.contains(&BigInt::from(-10)),
        "should include -10 for large negative values"
    );
    assert!(
        candidates.contains(&BigInt::from(-100)),
        "should include -100 for large negative values"
    );
}

#[test]
fn test_int_candidates_respects_max_count() {
    // Even for very large values, should not exceed MAX_CANDIDATES_PER_VAR
    let candidates = int_candidates(&BigInt::from(1_000_000_000i64));
    assert!(candidates.len() <= MAX_CANDIDATES_PER_VAR);
}

#[test]
fn test_array_minimize_empty_stores_noop() {
    let mut interp = ArrayInterpretation {
        default: Some("#x00".to_owned()),
        stores: vec![],
        index_sort: None,
        element_sort: None,
    };
    minimize_array_interpretation(&mut interp, false);
    assert_eq!(interp.default.as_deref(), Some("#x00"));
    assert!(interp.stores.is_empty());
}

#[test]
fn test_array_minimize_removes_default_matching_stores() {
    let mut interp = ArrayInterpretation {
        default: Some("#x00".to_owned()),
        stores: vec![
            ("#x01".to_owned(), "#xFF".to_owned()),
            ("#x02".to_owned(), "#x00".to_owned()), // matches default
            ("#x03".to_owned(), "#x00".to_owned()), // matches default
        ],
        index_sort: Some(Sort::bitvec(8)),
        element_sort: Some(Sort::bitvec(8)),
    };
    minimize_array_interpretation(&mut interp, false);
    assert_eq!(interp.default.as_deref(), Some("#x00"));
    assert_eq!(interp.stores.len(), 1);
    assert_eq!(interp.stores[0], ("#x01".to_owned(), "#xFF".to_owned()));
}

#[test]
fn test_array_minimize_keeps_mixed_duplicate_index_chain() {
    // ArrayInterpretation entries are authoritative first. Removing the first
    // `0` store would expose the older non-default value at the same index.
    let mut interp = ArrayInterpretation {
        default: Some("0".to_owned()),
        stores: vec![
            ("7".to_owned(), "0".to_owned()),
            ("7".to_owned(), "5".to_owned()),
        ],
        index_sort: None,
        element_sort: None,
    };
    let original = interp.stores.clone();
    minimize_array_interpretation(&mut interp, false);
    assert_eq!(interp.default.as_deref(), Some("0"));
    assert_eq!(interp.stores, original);
}

#[test]
fn test_array_minimize_keeps_semantically_aliased_bv_duplicate_chain() {
    // The first entry is authoritative and returns the default.  Its index is
    // the same BV value as the differently formatted, older non-default entry;
    // comparing raw strings would remove it and change the array at index 1.
    let mut interp = ArrayInterpretation {
        default: Some("0".to_owned()),
        stores: vec![
            ("#x01".to_owned(), "0".to_owned()),
            ("#b00000001".to_owned(), "5".to_owned()),
        ],
        index_sort: Some(Sort::bitvec(8)),
        element_sort: Some(Sort::Int),
    };
    let original = interp.stores.clone();
    minimize_array_interpretation(&mut interp, false);
    assert_eq!(interp.stores, original);
}

#[test]
fn test_array_minimize_removes_default_store_at_provably_distinct_bv_index() {
    let mut interp = ArrayInterpretation {
        default: Some("0".to_owned()),
        stores: vec![
            ("#x01".to_owned(), "0".to_owned()),
            ("#b00000010".to_owned(), "5".to_owned()),
        ],
        index_sort: Some(Sort::bitvec(8)),
        element_sort: Some(Sort::Int),
    };
    minimize_array_interpretation(&mut interp, false);
    assert_eq!(
        interp.stores,
        vec![("#b00000010".to_owned(), "5".to_owned())]
    );
}

#[test]
fn test_array_minimize_unknown_index_sort_fails_closed_on_alias() {
    let mut interp = ArrayInterpretation {
        default: Some("0".to_owned()),
        stores: vec![
            ("#x01".to_owned(), "0".to_owned()),
            ("#b00000001".to_owned(), "5".to_owned()),
        ],
        index_sort: None,
        element_sort: Some(Sort::Int),
    };
    let original = interp.stores.clone();
    minimize_array_interpretation(&mut interp, false);
    assert_eq!(interp.stores, original);
}

#[test]
fn test_array_minimize_removes_all_default_duplicate_entries() {
    let mut interp = ArrayInterpretation {
        default: Some("0".to_owned()),
        stores: vec![
            ("7".to_owned(), "0".to_owned()),
            ("7".to_owned(), "0".to_owned()),
        ],
        index_sort: None,
        element_sort: None,
    };
    minimize_array_interpretation(&mut interp, false);
    assert!(interp.stores.is_empty());
}

#[test]
fn test_array_minimize_never_changes_existing_default() {
    // Store frequency is not evidence about unlisted indices. Promoting #xFF
    // would change every such index from #x00 to #xFF.
    let mut interp = ArrayInterpretation {
        default: Some("#x00".to_owned()),
        stores: vec![
            ("#x01".to_owned(), "#xFF".to_owned()),
            ("#x02".to_owned(), "#xFF".to_owned()),
            ("#x03".to_owned(), "#xFF".to_owned()),
            ("#x04".to_owned(), "#x01".to_owned()),
        ],
        index_sort: None,
        element_sort: None,
    };
    minimize_array_interpretation(&mut interp, false);
    assert_eq!(interp.default.as_deref(), Some("#x00"));
    assert_eq!(interp.stores.len(), 4);
}

#[test]
fn test_array_minimize_never_invents_missing_default() {
    // A partial interpretation has no value for unlisted indices. Picking 42
    // would complete, not minimize, the model.
    let mut interp = ArrayInterpretation {
        default: None,
        stores: vec![
            ("0".to_owned(), "42".to_owned()),
            ("1".to_owned(), "42".to_owned()),
            ("2".to_owned(), "42".to_owned()),
            ("3".to_owned(), "7".to_owned()),
        ],
        index_sort: None,
        element_sort: None,
    };
    minimize_array_interpretation(&mut interp, false);
    assert_eq!(interp.default, None);
    assert_eq!(interp.stores.len(), 4);
}

#[test]
fn test_array_minimize_partial_interpretation_stays_untouched() {
    let mut interp = ArrayInterpretation {
        default: None,
        stores: vec![
            ("0".to_owned(), "#xFF".to_owned()),
            ("1".to_owned(), "#x00".to_owned()),
            ("2".to_owned(), "#xFF".to_owned()),
            ("3".to_owned(), "#x00".to_owned()),
        ],
        index_sort: None,
        element_sort: None,
    };
    minimize_array_interpretation(&mut interp, false);
    assert_eq!(interp.default, None);
    assert_eq!(interp.stores.len(), 4);
}

#[test]
fn test_array_minimize_read_conflicted_interp_stays_untouched() {
    // FAIL-CLOSED REGRESSION (#select-read-conflict-fail-closed): an interp
    // whose extraction dropped a cell on a committed-read conflict is
    // deliberately PARTIAL there. Preserve it byte-for-byte so no cleanup can
    // obscure the contested witness shape from downstream validation.
    let mut interp = ArrayInterpretation {
        default: None,
        stores: vec![
            ("2".to_owned(), "20".to_owned()),
            ("3".to_owned(), "0".to_owned()),
            ("4".to_owned(), "0".to_owned()),
        ],
        index_sort: None,
        element_sort: None,
    };
    minimize_array_interpretation(&mut interp, true);
    assert_eq!(
        interp.default, None,
        "a read-conflicted interpretation must never gain an invented default"
    );
    assert_eq!(
        interp.stores.len(),
        3,
        "no store of a read-conflicted interp may be dropped"
    );
}

#[test]
fn test_array_minimize_read_conflicted_keeps_existing_default_and_stores() {
    // The read-conflicted skip applies to defaulted interps too: the flag
    // marks the whole interpretation as contested, so even store-dropping
    // against an existing default is skipped (fail closed, no reshaping).
    let mut interp = ArrayInterpretation {
        default: Some("0".to_owned()),
        stores: vec![
            ("1".to_owned(), "0".to_owned()),
            ("2".to_owned(), "20".to_owned()),
        ],
        index_sort: None,
        element_sort: None,
    };
    minimize_array_interpretation(&mut interp, true);
    assert_eq!(interp.default.as_deref(), Some("0"));
    assert_eq!(interp.stores.len(), 2);
}

#[test]
fn test_array_minimize_removes_store_equal_to_existing_default() {
    // The existing default is immutable; its matching point is redundant.
    let mut interp = ArrayInterpretation {
        default: Some("#x00".to_owned()),
        stores: vec![
            ("0".to_owned(), "#xFF".to_owned()),
            ("1".to_owned(), "#x00".to_owned()),
        ],
        index_sort: Some(Sort::bitvec(8)),
        element_sort: Some(Sort::bitvec(8)),
    };
    minimize_array_interpretation(&mut interp, false);
    assert_eq!(interp.default.as_deref(), Some("#x00"));
    assert_eq!(interp.stores.len(), 1);
    assert_eq!(interp.stores[0], ("0".to_owned(), "#xFF".to_owned()));
}

#[test]
fn test_array_minimize_frequent_nondefault_value_stays_explicit() {
    let mut interp = ArrayInterpretation {
        default: Some("#x00".to_owned()),
        stores: vec![
            ("0".to_owned(), "#x42".to_owned()),
            ("1".to_owned(), "#x42".to_owned()),
            ("2".to_owned(), "#x42".to_owned()),
        ],
        index_sort: None,
        element_sort: None,
    };
    minimize_array_interpretation(&mut interp, false);
    assert_eq!(interp.default.as_deref(), Some("#x00"));
    assert_eq!(interp.stores.len(), 3);
}

/// #42 (model-checker-consumer #39): an expired solve deadline makes minimization bail
/// immediately, keeping the current (valid) model — same sat verdict, no
/// candidate re-solves. Control: with the deadline cleared, the same inflated
/// value DOES shrink, proving the bail (not convergence) kept it.
#[test]
fn minimize_bails_on_expired_deadline_and_keeps_model() {
    let commands = ay_frontend::parse(
        "(set-option :produce-models true)(declare-const x Int)(assert (> x 90))(check-sat)",
    )
    .expect("valid SMT-LIB");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute succeeds");
    assert_eq!(outputs[0], "sat");

    // Inflate x's model value to something obviously shrinkable (x > 90 still
    // holds), so a RUN of the minimizer would provably change it.
    let term_id = {
        let lia = exec
            .last_model
            .as_ref()
            .and_then(|m| m.lia_model.as_ref())
            .expect("lia model present");
        *lia.values.keys().next().expect("x present in lia model")
    };
    let inflated = BigInt::from(1_000_000);
    if let Some(lia) = exec.last_model.as_mut().and_then(|m| m.lia_model.as_mut()) {
        lia.values.insert(term_id, inflated.clone());
    }

    // Expired deadline: bail immediately, value untouched.
    exec.solve_deadline.set(Some(ay_core::time::Instant::now()));
    exec.minimize_model_sat_preserving();
    let after_bail = exec
        .last_model
        .as_ref()
        .and_then(|m| m.lia_model.as_ref())
        .and_then(|lia| lia.values.get(&term_id))
        .cloned()
        .expect("model preserved");
    assert_eq!(
        after_bail, inflated,
        "expired deadline must leave the model untouched"
    );

    // Control: with no deadline the minimizer shrinks the inflated value.
    exec.solve_deadline.set(None);
    exec.minimize_model_sat_preserving();
    let after_run = exec
        .last_model
        .as_ref()
        .and_then(|m| m.lia_model.as_ref())
        .and_then(|lia| lia.values.get(&term_id))
        .cloned()
        .expect("model preserved");
    assert!(
        after_run < inflated,
        "control run must shrink the inflated value, got {after_run}"
    );
}
