// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::ModelView;
use ay_core::TermStore;

struct EmptyModel;

impl ModelView for EmptyModel {
    fn leaf_value(&self, _: TermId) -> Option<ModelValue> {
        None
    }
}

fn boolean_app(terms: &mut TermStore, operator: &str, args: &[TermId]) -> TermId {
    terms.mk_app(Symbol::named(operator), args, Sort::Bool)
}

/// Force support derivation directly, even when normal full-carrier evaluation
/// would fit. Compare its theorem with independent existing term evaluation.
fn assert_bv3_support_contains_every_decisive_value(
    terms: &TermStore,
    variable: TermId,
    body: TermId,
    kind: QuantifierKind,
) -> usize {
    let model = EmptyModel;
    let evaluator = Evaluator::new(terms, &model);
    evaluator.quantifier_state.nesting.set(1);
    let _guard = super::super::QuantifierDepthGuard(&evaluator.quantifier_state.nesting);
    let sort = Sort::bitvec(3);
    let domain = GuardedDomain::derive(
        &evaluator,
        kind,
        &[("i".to_string(), sort.clone())],
        body,
        0,
        65_536,
    )
    .expect("small support analysis fits its budgets")
    .expect("every fixture carries an interpreted bound comparison");
    let mut included = [false; 8];
    for ordinal in 0..domain.count {
        let ModelValue::BitVec { value, width: 3 } = domain
            .value_at(&evaluator, &sort, ordinal)
            .expect("valid support ordinal")
        else {
            panic!("support must preserve the BV3 carrier");
        };
        let index = value.to_usize().expect("small nonnegative index");
        assert!(index < included.len());
        assert!(!included[index], "support must not enumerate a value twice");
        included[index] = true;
    }
    for (ordinal, &in_support) in included.iter().enumerate() {
        let actual = evaluator
            .eval_with_binding(
                variable,
                ModelValue::bitvec(BigInt::from(ordinal), 3),
                body,
                0,
            )
            .expect("the full source body is evaluable at every BV3 value");
        let ModelValue::Bool(value) = actual else {
            panic!("Boolean source body");
        };
        assert!(
            value != kind.decisive_value() || in_support,
            "support dropped decisive source value {ordinal} for {body:?}"
        );
    }
    domain.count
}

#[test]
fn guarded_quantifier_support_differential_checks_comparisons_and_polarity() {
    let mut terms = TermStore::new();
    let variable = terms.mk_var("i", Sort::bitvec(3));
    let mut formulas = Vec::new();
    for operator in ["bvult", "bvule", "bvugt", "bvuge", "=", "distinct"] {
        for value in [0u8, 1, 7] {
            let endpoint = terms.mk_bitvec(BigInt::from(value), 3);
            for args in [[variable, endpoint], [endpoint, variable]] {
                let atom = boolean_app(&mut terms, operator, &args);
                formulas.push(atom);
                formulas.push(terms.mk_not_raw(atom));
                formulas.push(boolean_app(&mut terms, "not", &[atom]));
            }
        }
    }
    let atoms = formulas.clone();
    for pair in atoms.chunks_exact(2) {
        for operator in ["and", "or", "=>"] {
            formulas.push(boolean_app(&mut terms, operator, pair));
        }
    }
    let mut saw_nonempty_narrowing = false;
    let mut saw_empty_support = false;
    for body in formulas {
        for kind in [QuantifierKind::Forall, QuantifierKind::Exists] {
            let count =
                assert_bv3_support_contains_every_decisive_value(&terms, variable, body, kind);
            saw_nonempty_narrowing |= (1..8).contains(&count);
            saw_empty_support |= count == 0;
        }
    }
    assert!(
        saw_nonempty_narrowing,
        "whole-support-only analysis is insufficient"
    );
    assert!(
        saw_empty_support,
        "exact vacuity controls must actually narrow to empty"
    );
}

#[test]
fn guarded_quantifier_support_differential_preserves_disjoint_branches() {
    let mut terms = TermStore::new();
    let variable = terms.mk_var("i", Sort::bitvec(3));
    let first = terms.mk_bitvec(BigInt::from(1u8), 3);
    let last = terms.mk_bitvec(BigInt::from(7u8), 3);
    let first_eq = boolean_app(&mut terms, "=", &[variable, first]);
    let last_eq = boolean_app(&mut terms, "=", &[variable, last]);
    let no = terms.mk_bool(false);
    let first_implication = boolean_app(&mut terms, "=>", &[first_eq, no]);
    let last_implication = boolean_app(&mut terms, "=>", &[last_eq, no]);
    let forall_body = boolean_app(&mut terms, "and", &[first_implication, last_implication]);
    let exists_body = boolean_app(&mut terms, "or", &[first_eq, last_eq]);
    assert_eq!(
        assert_bv3_support_contains_every_decisive_value(
            &terms,
            variable,
            forall_body,
            QuantifierKind::Forall
        ),
        2
    );
    assert_eq!(
        assert_bv3_support_contains_every_decisive_value(
            &terms,
            variable,
            exists_body,
            QuantifierKind::Exists
        ),
        2
    );
}
