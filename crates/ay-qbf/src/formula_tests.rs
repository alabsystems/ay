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
fn test_universal_reduction() {
    // ∃x₁∀x₂∃x₃. (x₁ ∨ x₂ ∨ x₃)
    // After universal reduction: (x₁ ∨ x₃) because x₂ is at level 1,
    // which is < max existential level 2, so x₂ stays
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

    // x₂ at level 1 >= max_exist_level=0, so x₂ removed? No wait...
    // max_exist_level for x₁ is 0, x₂ is at level 1
    // We remove universal literals with level >= max_exist_level
    // So x₂ (level 1) >= 0 should be removed
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
