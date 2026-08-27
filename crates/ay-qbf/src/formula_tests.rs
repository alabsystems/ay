// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_sat::Variable;

#[test]
fn test_qbf_formula_var_info() {
    // ∃x₁∀x₂∃x₃. (x₁ ∨ x₂ ∨ x₃)
    let prefix = vec![
        QuantifierBlock::exists(vec![1]),
        QuantifierBlock::forall(vec![2]),
        QuantifierBlock::exists(vec![3]),
    ];
    let clauses = vec![vec![
        Literal::positive(Variable::new(1)),
        Literal::positive(Variable::new(2)),
        Literal::positive(Variable::new(3)),
    ]];

    let formula = QbfFormula::new(3, prefix, clauses);

    // Check levels
    assert_eq!(formula.var_level(1), 0); // Outermost
    assert_eq!(formula.var_level(2), 1);
    assert_eq!(formula.var_level(3), 2); // Innermost

    // Check quantifiers
    assert!(formula.is_existential(1));
    assert!(formula.is_universal(2));
    assert!(formula.is_existential(3));
}

#[test]
fn accessors_and_prefix_cache_share_canonical_state() {
    let x1 = Literal::positive(Variable::new(1));
    let x2 = Literal::positive(Variable::new(2));
    let not_x2 = Literal::negative(Variable::new(2));
    let formula = QbfFormula::new(
        3,
        vec![
            QuantifierBlock::exists(vec![0, 2, 4]),
            QuantifierBlock::forall(vec![2, 1]),
            QuantifierBlock::exists(vec![0, 4]),
        ],
        vec![vec![x1, x1], vec![x2, not_x2], Vec::new()],
    );

    assert_eq!(formula.num_vars(), 3);
    assert_eq!(
        formula.prefix(),
        &[
            QuantifierBlock::exists(vec![2]),
            QuantifierBlock::forall(vec![1]),
        ]
    );
    assert_eq!(formula.clauses(), &[vec![x1], Vec::new()]);
    assert_eq!(formula.var_level(2), 0);
    assert!(formula.is_existential(2));
    assert_eq!(formula.var_level(1), 1);
    assert!(formula.is_universal(1));
    assert_eq!(formula.var_level(3), 0);
    assert!(formula.is_existential(3));

    let debug = format!("{formula:?}");
    assert!(!debug.contains("var_levels"));
    assert!(!debug.contains("var_quantifiers"));

    let prefix_ptr = formula.prefix().as_ptr();
    let clauses_ptr = formula.clauses().as_ptr();
    let (num_vars, prefix, clauses) = formula.into_parts();
    assert_eq!(num_vars, 3);
    assert!(std::ptr::eq(prefix.as_ptr(), prefix_ptr));
    assert!(std::ptr::eq(clauses.as_ptr(), clauses_ptr));
}

#[test]
fn oversized_formula_looks_up_explicit_prefix_metadata_without_dense_caches() {
    let formula = QbfFormula::new(
        MAX_QBF_VARS + 1,
        vec![
            QuantifierBlock::exists(vec![1]),
            QuantifierBlock::forall(vec![2]),
        ],
        Vec::new(),
    );

    assert_eq!(formula.var_level(2), 1);
    assert_eq!(formula.var_quantifier(2), Quantifier::Forall);
    assert!(formula.is_universal(2));
}

#[test]
fn test_universal_reduction() {
    // ∃x₁∀x₂∃x₃. (x₁ ∨ x₂ ∨ x₃)
    // Universal reduction leaves the clause unchanged because x₂ is at level
    // 1, which is below the maximum existential level 2.
    let prefix = vec![
        QuantifierBlock::exists(vec![1]),
        QuantifierBlock::forall(vec![2]),
        QuantifierBlock::exists(vec![3]),
    ];
    let formula = QbfFormula::new(3, prefix, vec![]);

    let clause = vec![
        Literal::positive(Variable::new(1)),
        Literal::positive(Variable::new(2)),
        Literal::positive(Variable::new(3)),
    ];
    let reduced = formula.universal_reduce(&clause);

    // x₂ at level 1 < max_exist_level=2, so it stays
    assert_eq!(reduced.len(), 3);

    // Test case where universal is removed
    // ∃x₁∀x₂. (x₁ ∨ x₂)
    // x₂ at level 1 >= max_exist_level=0, so x₂ removed
    let prefix2 = vec![
        QuantifierBlock::exists(vec![1]),
        QuantifierBlock::forall(vec![2]),
    ];
    let formula2 = QbfFormula::new(2, prefix2, vec![]);

    let clause2 = vec![
        Literal::positive(Variable::new(1)),
        Literal::positive(Variable::new(2)),
    ];
    let reduced2 = formula2.universal_reduce(&clause2);

    // x₂ is deeper than the only existential literal and is removed.
    assert_eq!(reduced2.len(), 1);
    assert_eq!(reduced2[0], Literal::positive(Variable::new(1)));
}

#[test]
fn test_universal_reduction_of_universal_only_clause_is_empty() {
    let formula = QbfFormula::new(2, vec![QuantifierBlock::forall(vec![1, 2])], vec![]);
    let clause = vec![
        Literal::positive(Variable::new(1)),
        Literal::negative(Variable::new(2)),
    ];

    assert!(formula.universal_reduce(&clause).is_empty());
}

#[test]
fn test_universal_reduction_preserves_tautology() {
    let formula = QbfFormula::new(1, vec![QuantifierBlock::forall(vec![1])], vec![]);
    let clause = vec![
        Literal::positive(Variable::new(1)),
        Literal::negative(Variable::new(1)),
    ];

    assert_eq!(formula.universal_reduce(&clause), clause);
}
