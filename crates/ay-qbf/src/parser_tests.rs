// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn test_parse_simple_qdimacs() {
    let input = r#"
c Simple QBF example
p cnf 3 2
e 1 3 0
a 2 0
1 2 0
-1 -2 3 0
"#;

    let formula = parse_qdimacs(input).unwrap();
    assert_eq!(formula.num_vars, 3);
    assert_eq!(formula.prefix.len(), 2);
    assert_eq!(formula.clauses.len(), 2);

    // Check prefix
    assert_eq!(formula.prefix[0].quantifier, Quantifier::Exists);
    assert_eq!(formula.prefix[0].variables, vec![1, 3]);
    assert_eq!(formula.prefix[1].quantifier, Quantifier::Forall);
    assert_eq!(formula.prefix[1].variables, vec![2]);

    // Check quantifier info
    assert!(formula.is_existential(1));
    assert!(formula.is_universal(2));
    assert!(formula.is_existential(3));
}

#[test]
fn test_parse_minimal_qdimacs() {
    let input = "p cnf 2 1\ne 1 2 0\n1 2 0\n";
    let formula = parse_qdimacs(input).unwrap();
    assert_eq!(formula.num_vars, 2);
    assert_eq!(formula.prefix.len(), 1);
    assert_eq!(formula.clauses.len(), 1);
}

#[test]
fn test_parse_alternating_quantifiers() {
    let input = r#"
p cnf 4 1
e 1 0
a 2 0
e 3 0
a 4 0
1 -2 3 -4 0
"#;

    let formula = parse_qdimacs(input).unwrap();
    assert_eq!(formula.prefix.len(), 4);

    // Check alternation
    assert_eq!(formula.prefix[0].quantifier, Quantifier::Exists);
    assert_eq!(formula.prefix[1].quantifier, Quantifier::Forall);
    assert_eq!(formula.prefix[2].quantifier, Quantifier::Exists);
    assert_eq!(formula.prefix[3].quantifier, Quantifier::Forall);

    // Check levels
    assert_eq!(formula.var_level(1), 0);
    assert_eq!(formula.var_level(2), 1);
    assert_eq!(formula.var_level(3), 2);
    assert_eq!(formula.var_level(4), 3);
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
fn test_parse_preserves_empty_clause() {
    let formula = parse_qdimacs("p cnf 0 1\n0\n").unwrap();

    assert_eq!(formula.clauses, vec![Vec::new()]);
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
