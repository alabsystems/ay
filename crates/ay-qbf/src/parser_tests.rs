// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn test_parse_simple_qdimacs() -> Result<(), Box<dyn std::error::Error>> {
    let input = r#"
c Simple QBF example
p cnf 3 2
e 1 3 0
a 2 0
1 2 0
-1 -2 3 0
"#;

    let formula = parse_qdimacs(input)?;
    assert_eq!(formula.num_vars(), 3);
    assert_eq!(formula.prefix().len(), 2);
    assert_eq!(formula.clauses().len(), 2);

    // Check prefix
    let first = formula.prefix().first().ok_or("missing first block")?;
    let second = formula.prefix().get(1).ok_or("missing second block")?;
    assert_eq!(first.quantifier, Quantifier::Exists);
    assert_eq!(first.variables, vec![1, 3]);
    assert_eq!(second.quantifier, Quantifier::Forall);
    assert_eq!(second.variables, vec![2]);

    // Check quantifier info
    assert!(formula.is_existential(1));
    assert!(formula.is_universal(2));
    assert!(formula.is_existential(3));
    Ok(())
}

#[test]
fn test_parse_minimal_qdimacs() {
    let input = "p cnf 2 1\ne 1 2 0\n1 2 0\n";
    let formula = parse_qdimacs(input).unwrap();
    assert_eq!(formula.num_vars(), 2);
    assert_eq!(formula.prefix().len(), 1);
    assert_eq!(formula.clauses().len(), 1);
}

#[test]
fn test_parse_alternating_quantifiers() -> Result<(), Box<dyn std::error::Error>> {
    let input = r#"
p cnf 4 1
e 1 0
a 2 0
e 3 0
a 4 0
1 -2 3 -4 0
"#;

    let formula = parse_qdimacs(input)?;
    assert_eq!(formula.prefix().len(), 4);

    // Check alternation
    let quantifiers: Vec<Quantifier> = formula
        .prefix()
        .iter()
        .map(|block| block.quantifier)
        .collect();
    assert_eq!(
        quantifiers,
        [
            Quantifier::Exists,
            Quantifier::Forall,
            Quantifier::Exists,
            Quantifier::Forall
        ]
    );

    // Check levels
    assert_eq!(formula.var_level(1), 0);
    assert_eq!(formula.var_level(2), 1);
    assert_eq!(formula.var_level(3), 2);
    assert_eq!(formula.var_level(4), 3);
    Ok(())
}

#[test]
fn test_parse_error_missing_problem() {
    let input = "e 1 2 0\n1 2 0\n";
    // Core parser returns MissingHeader when data appears before p cnf
    assert!(matches!(
        parse_qdimacs(input),
        Err(QdimacsError::MissingProblemLine)
    ));
}

#[test]
fn test_parse_error_var_out_of_range() {
    let input = "p cnf 2 1\ne 1 3 0\n1 2 0\n";
    assert!(matches!(
        parse_qdimacs(input),
        Err(QdimacsError::VariableOutOfRange(3, 2))
    ));
}

#[test]
fn test_parse_error_clause_var_above_header() {
    // A clause variable above the declared count is refused (by
    // `dimacs_core`) like a prefix one, so the header bounds the dense state
    // that `formula.rs` describes.
    assert!(matches!(
        parse_qdimacs("p cnf 2 1\ne 1 2 0\n1 -3 0\n"),
        Err(QdimacsError::VariableOutOfRange(3, 2))
    ));
    assert!(matches!(
        parse_qdimacs("p cnf 1 1\n67000000 0\n"),
        Err(QdimacsError::VariableOutOfRange(67_000_000, 1))
    ));
}

#[test]
fn test_parse_preserves_empty_clause() {
    let formula = parse_qdimacs("p cnf 0 1\n0\n").unwrap();

    assert_eq!(formula.clauses(), &[Vec::new()]);
}

#[test]
fn test_parse_rejects_duplicate_quantification() {
    let error = parse_qdimacs("p cnf 1 1\ne 1 0\na 1 0\n1 0\n").unwrap_err();

    assert!(matches!(error, QdimacsError::InvalidQuantifierLine(_)));
}

#[test]
fn test_parse_rejects_quantifier_after_matrix() {
    let error = parse_qdimacs("p cnf 2 1\ne 1 0\n1 0\na 2 0\n").unwrap_err();

    assert!(matches!(error, QdimacsError::InvalidQuantifierLine(_)));
}

#[test]
fn test_parse_rejects_unencodable_clause_literal_without_panicking() {
    let error = parse_qdimacs("p cnf 2147483648 1\n-2147483648 0\n").unwrap_err();

    assert!(matches!(error, QdimacsError::InvalidClause(_)));
    assert!(error.to_string().contains("maximum supported"), "{error}");
}

#[test]
fn test_parse_rejects_variable_above_dense_solver_cap() {
    let over = MAX_QBF_VARS + 1;
    let input = format!("p cnf {over} 1\n{over} 0\n");
    let error = parse_qdimacs(&input).expect_err("dense-state cap must fail closed");

    assert!(matches!(error, QdimacsError::InvalidClause(_)));
    assert!(error.to_string().contains("maximum supported"), "{error}");
}

#[test]
fn test_parse_accepts_gallery_sized_variable_indices() {
    // c1_BMC_p1_k2048 (QBF Gallery 2023) declares 2,202,779 variables; the
    // old dense cap of 2^20 refused it at parse time.
    let input = "p cnf 2202779 3\ne 7 0\na 1100000 0\ne 2200000 0\n\
                 7 1100000 2200000 0\n-2200000 -1100000 0\n-7 2200000 0\n";
    let formula = parse_qdimacs(input).expect("a declared 2.2M-variable formula parses");
    assert_eq!(formula.num_vars(), 2_200_000);
    assert!(formula.is_universal(1_100_000));
    // ∃x ∀u ∃y. (x ∨ u ∨ y)(¬y ∨ ¬u)(¬x ∨ y) is true: x = false, y = ¬u.
    // Both engines agree on it.
    assert!(matches!(
        crate::QbfSolver::new(formula.clone()).solve_until(None),
        crate::QbfResult::Sat(_)
    ));
    assert!(matches!(
        crate::QbfSolver::new(formula).solve(),
        crate::QbfResult::Sat(_)
    ));
}
