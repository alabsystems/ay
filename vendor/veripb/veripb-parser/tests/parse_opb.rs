use std::str::FromStr;

use logos::Logos;
use malachite_bigint::BigInt;
use veripb_formula::prelude::*;
use veripb_parser::{
    error::ParserError,
    opb_parser::{parse_opb_from_file, parse_opb_objective, parse_single_constraint},
    opb_token::OPBToken,
};

/// Check that a formula file is rejected with the token error that says `expected`, so that a test
/// for a rejection does not pass on an unrelated error.
fn assert_rejected_expecting(instance: &str, expected: &str, message: &str) {
    let path = format!("./tests/instances/{instance}.opb");
    match parse_opb_from_file(&path) {
        Ok(_) => panic!("{message} `{instance}` was accepted."),
        Err(ParserError::TokenErrorFile {
            expected: actual, ..
        }) => assert_eq!(actual, expected, "{message}"),
        Err(error) => panic!("{message} `{instance}` was rejected with {error:?}."),
    }
}

#[test]
fn parse_general_opb_i64() {
    let (formula, var_names, _, _) = match parse_opb_from_file("./tests/instances/general_i64.opb")
    {
        Ok(formula) => formula,
        Err(e) => {
            eprintln!("Parsing error: {e:?}");
            panic!();
        }
    };

    assert_eq!(formula.len(), 2, "Should parse 2 constraint.");
    assert_eq!(var_names.len(), 4, "Formula should contain 4 variables.")
}

#[test]
fn parse_general_opb_i64_with_equal() {
    let (formula, var_names, _, _) =
        match parse_opb_from_file("./tests/instances/general_i64_equal.opb") {
            Ok(formula) => formula,
            Err(e) => {
                eprintln!("Parsing error: {e:?}");
                panic!();
            }
        };

    assert_eq!(formula.len(), 3, "Should parse 3 constraint.");
    assert_eq!(var_names.len(), 4, "Formula should contain 4 variables.")
}

#[test]
fn parse_mixed_opb_i64() {
    let (formula, var_names, _, _) = match parse_opb_from_file("./tests/instances/mixed_i64.opb") {
        Ok(formula) => formula,
        Err(e) => {
            eprintln!("Parsing error: {e:?}");
            panic!();
        }
    };

    assert_eq!(formula.len(), 3, "Should parse 3 constraint.");
    assert_eq!(var_names.len(), 4, "Formula should contain 4 variables.");
    assert!(
        matches!(formula.constraints[0], PBConstraintEnum::GeneralPBI64(..)),
        "The first constraint should be a general arbitrary size PB constraint."
    );
    assert!(
        matches!(formula.constraints[1], PBConstraintEnum::Cardinality(..)),
        "The third constraint should be a cardinality constraint."
    );
    assert!(
        matches!(formula.constraints[2], PBConstraintEnum::Clause(..)),
        "The fourth constraint should be a clause."
    );
}

#[test]
fn parse_general_opb_arbitrary() {
    let (formula, var_names, _, _) =
        match parse_opb_from_file("./tests/instances/general_arbitrary.opb") {
            Ok(formula) => formula,
            Err(e) => {
                eprintln!("Parsing error: {e:?}");
                panic!();
            }
        };

    assert_eq!(formula.len(), 2, "Should parse 2 constraint.");
    assert_eq!(var_names.len(), 4, "Formula should contain 4 variables.")
}

#[test]
fn parse_mixed_opb_arbitrary() {
    let (formula, var_names, _, _) =
        match parse_opb_from_file("./tests/instances/mixed_arbitrary.opb") {
            Ok(formula) => formula,
            Err(e) => {
                eprintln!("Parsing error: {e:?}");
                panic!();
            }
        };

    assert_eq!(formula.len(), 7, "Should parse 7 constraint.");
    assert_eq!(var_names.len(), 4, "Formula should contain 4 variables.");
    assert!(
        matches!(
            formula.constraints[0],
            PBConstraintEnum::GeneralPBBigInt(..)
        ),
        "The first constraint should be a general arbitrary size PB constraint."
    );
    assert!(
        matches!(formula.constraints[1], PBConstraintEnum::GeneralPBI128(..)),
        "The second constraint should be a general 128 bit PB constraint."
    );
    assert!(
        matches!(formula.constraints[2], PBConstraintEnum::Cardinality(..)),
        "The third constraint should be a cardinality constraint."
    );
    assert!(
        matches!(formula.constraints[3], PBConstraintEnum::Clause(..)),
        "The fourth constraint should be a clause."
    );
    assert!(
        matches!(
            formula.constraints[4],
            PBConstraintEnum::GeneralPBBigInt(..)
        ),
        "The fifth constraint should be a general arbitrary size PB constraint."
    );
    assert!(
        matches!(
            formula.constraints[5],
            PBConstraintEnum::GeneralPBBigInt(..)
        ),
        "The sixth constraint should be a general arbitrary size PB constraint."
    );
    assert!(
        matches!(formula.constraints[6], PBConstraintEnum::GeneralPBI128(..)),
        "The seventh constraint should be a general 128 bit PB constraint."
    );
}

#[test]
fn parse_no_terms() {
    let (formula, var_names, _, _) = match parse_opb_from_file("./tests/instances/no_terms.opb") {
        Ok(formula) => formula,
        Err(e) => {
            eprintln!("Parsing error: {e:?}");
            panic!();
        }
    };

    assert_eq!(formula.len(), 5, "Should parse 5 constraint.");
    assert_eq!(var_names.len(), 0, "Formula should contain 0 variables.");

    assert!(matches!(
        formula.constraints[0],
        PBConstraintEnum::Cardinality(..)
    ));
    assert!(matches!(
        formula.constraints[1],
        PBConstraintEnum::GeneralPBI128(..)
    ));
    assert!(matches!(
        formula.constraints[2],
        PBConstraintEnum::GeneralPBBigInt(..)
    ));
    assert!(matches!(
        formula.constraints[3],
        PBConstraintEnum::Clause(..)
    ));
    assert!(matches!(
        formula.constraints[4],
        PBConstraintEnum::Cardinality(..)
    ));
}

#[test]
fn parse_implication() {
    let (formula, var_names, labels, _) =
        match parse_opb_from_file("./tests/instances/implication.opb") {
            Ok(formula) => formula,
            Err(e) => {
                eprintln!("Parsing error: {e:?}");
                panic!();
            }
        };

    // The reified equality on the sixth line counts as two constraints.
    assert_eq!(formula.len(), 8, "Should parse 8 constraints.");
    assert_eq!(var_names.len(), 8, "Formula should contain 8 variables.");
    assert_eq!(
        labels.get("@lab"),
        Some(&5),
        "The label should map to the fifth constraint."
    );
}

#[test]
fn parse_implication_large_coefficients() {
    let (formula, var_names, _, _) =
        match parse_opb_from_file("./tests/instances/implication_large_coefficients.opb") {
            Ok(formula) => formula,
            Err(e) => {
                eprintln!("Parsing error: {e:?}");
                panic!();
            }
        };

    assert_eq!(formula.len(), 3, "Should parse 3 constraints.");
    assert_eq!(var_names.len(), 5, "Formula should contain 5 variables.");

    let PBConstraintEnum::GeneralPBI128(first) = &formula.constraints[0] else {
        panic!(
            "The degree of the first constraint fits into an i64, but carrying it on both literals of the antecedent does not."
        );
    };
    // `z1 z2 ==> 4611686018427387904 x1 >= 4611686018427387904`, where the degree is 2^62.
    assert_eq!(
        *first.get_degree(),
        4_611_686_018_427_387_904,
        "Reifying does not change the degree."
    );
    assert_eq!(
        first
            .get_terms()
            .iter()
            .map(|term| term.coeff)
            .collect::<Vec<_>>(),
        vec![4_611_686_018_427_387_904; 3],
        "Each literal of the antecedent is added with the degree as coefficient, which is what needs the wider type: three times 2^62 does not fit into an i64."
    );

    let PBConstraintEnum::GeneralPBBigInt(second) = &formula.constraints[1] else {
        panic!("The second constraint should be a general arbitrary size PB constraint.");
    };
    // `z3 ==> 17014118346046923173168730371588410572800000000000 x1 3 x2 >= 4`.
    assert_eq!(
        *second.get_degree(),
        BigInt::from(4),
        "Reifying does not change the degree."
    );
    assert_eq!(
        second
            .get_terms()
            .iter()
            .map(|term| term.coeff.clone())
            .collect::<Vec<_>>(),
        vec![
            BigInt::from_str("17014118346046923173168730371588410572800000000000").unwrap(),
            BigInt::from(4),
            BigInt::from(3)
        ],
        "A coefficient is stored as it is written, and the antecedent's literal is added with the degree as coefficient."
    );

    assert!(
        matches!(formula.constraints[2], PBConstraintEnum::Clause(..)),
        "The third constraint should be a clause."
    );
}

#[test]
fn parse_implication_equivalence() {
    let (formula, _, _, _) =
        match parse_opb_from_file("./tests/instances/implication_equivalence.opb") {
            Ok(formula) => formula,
            Err(e) => {
                eprintln!("Parsing error: {e:?}");
                panic!();
            }
        };

    // Each equivalence stands for the two directions of the same constraint.
    assert_eq!(formula.len(), 6, "Should parse 6 constraints.");
    assert!(
        matches!(formula.constraints[2], PBConstraintEnum::Clause(..))
            && matches!(formula.constraints[3], PBConstraintEnum::Clause(..)),
        "The constraint is normalized to `1 x1 >= 1` before it is reified in either direction."
    );
    assert!(
        !formula.constraints[4].is_trivial() && formula.constraints[5].is_trivial(),
        "A contradicting constraint forces the literal to be false, and is implied by nothing."
    );
}

#[test]
fn parse_equivalence_of_equality_fails() {
    assert_rejected_expecting(
        "implication_equivalence_equality",
        "'>=', '<=', or integer",
        "An equivalence of an equality would be implied by a tautology.",
    );
}

#[test]
fn parse_equivalence_with_multiple_literals_fails() {
    assert_rejected_expecting(
        "implication_equivalence_two_literals",
        "'==>', since '<==>' reifies a single literal",
        "An equivalence reifies a single literal.",
    );
}

#[test]
fn parse_left_implication_with_multiple_literals_fails() {
    assert_rejected_expecting(
        "implication_two_left_literals",
        "'==>', since '<==' reifies a single literal",
        "A left implication reifies a single literal.",
    );
}

#[test]
fn parse_labelled_reified_equality_with_one_label_fails() {
    assert_rejected_expecting(
        "implication_labelled_equality",
        "one label for each of the 2 constraints this line stands for, but found 1",
        "A reified equality is split into two constraints, so one label does not name all of them.",
    );
}

#[test]
fn parse_labelled_equality() {
    let (formula, _, labels, _) =
        match parse_opb_from_file("./tests/instances/labelled_equality.opb") {
            Ok(formula) => formula,
            Err(e) => {
                eprintln!("Parsing error: {e:?}");
                panic!();
            }
        };

    assert_eq!(formula.len(), 5, "Should parse 5 constraints.");
    for (label, id) in [
        ("@sum_lo", 1),
        ("@sum_hi", 2),
        ("@reif_lo", 3),
        ("@reif_hi", 4),
        ("@plain", 5),
    ] {
        assert_eq!(
            labels.get(label),
            Some(&id),
            "The i-th label should name the i-th constraint the line stands for."
        );
    }
}

#[test]
fn parse_labelled_equivalence() {
    let (formula, _, labels, _) =
        match parse_opb_from_file("./tests/instances/labelled_equivalence.opb") {
            Ok(formula) => formula,
            Err(e) => {
                eprintln!("Parsing error: {e:?}");
                panic!();
            }
        };

    assert_eq!(
        formula.len(),
        2,
        "An equivalence stands for two constraints."
    );
    assert_eq!(
        (labels.get("@right"), labels.get("@left")),
        (Some(&1), Some(&2)),
        "An equivalence is loaded as its `==>` direction followed by its `<==` direction, and the i-th label names the i-th of them."
    );
}

#[test]
fn parse_labelled_equality_with_too_few_labels_fails() {
    assert_rejected_expecting(
        "labelled_equality_too_few",
        "one label for each of the 2 constraints this line stands for, but found 1",
        "An equality stands for two constraints and needs a label for each of them.",
    );
}

#[test]
fn parse_labelled_inequality_with_too_many_labels_fails() {
    assert_rejected_expecting(
        "labelled_inequality_too_many",
        "a single label, since this line stands for one constraint, but found 2",
        "An inequality stands for one constraint and can not carry two labels.",
    );
}

#[test]
fn parse_left_implication_of_equality_fails() {
    assert_rejected_expecting(
        "implication_left_equality",
        "'>=', '<=', or integer",
        "A left implication of an equality would be implied by a tautology.",
    );
}

#[test]
fn parse_implication_normalization() {
    let (formula, _, _, _) =
        match parse_opb_from_file("./tests/instances/implication_normalization.opb") {
            Ok(formula) => formula,
            Err(e) => {
                eprintln!("Parsing error: {e:?}");
                panic!();
            }
        };

    assert_eq!(formula.len(), 4, "Should parse 4 constraints.");
    assert!(
        matches!(formula.constraints[0], PBConstraintEnum::Clause(..)),
        "The constraint is normalized to `1 x1 >= 1` before the antecedent is added, so the reified constraint is the clause `1 ~z1 1 x1 >= 1`."
    );
    assert!(
        formula.constraints[1].is_trivial(),
        "A trivially satisfied constraint stays trivially satisfied when it is reified."
    );
    assert!(
        formula.constraints[2].is_trivial(),
        "The antecedent cancels against the term of the constraint, leaving a trivially satisfied constraint."
    );
    assert!(
        formula.constraints[3].is_trivial() && formula.constraints[3].len() == 1,
        "The constraint is normalized to the contradicting `1 x1 >= 3`, which implies the literal of the left implication, so only its trivially satisfied negation `1 ~x1 >= -1` is left."
    );
}

#[test]
fn parse_objective() {
    let (formula, var_names, _, _) = match parse_opb_from_file("./tests/instances/objective.opb") {
        Ok(formula) => formula,
        Err(e) => {
            eprintln!("Parsing error: {e:?}");
            panic!();
        }
    };

    assert_eq!(formula.len(), 0, "Should parse 0 constraint.");
    assert_eq!(var_names.len(), 3, "Formula should contain 3 variables.");
    assert_eq!(
        formula.objective.as_ref().unwrap().len(),
        3,
        "Objective should have 3 terms."
    );

    assert_eq!(formula.objective.unwrap().constant, 4.into());
}

#[test]
fn parse_only_constraint() {
    let mut lex = OPBToken::lexer("1 z1 2414213213 ~fddsewr >= 20431412 ;");
    let mut var_names = VarNameManager::default();

    let (geq, leq) =
        parse_single_constraint(&mut lex, &mut var_names).expect("Constraint should be parsed");

    assert!(matches!(geq, PBConstraintEnum::GeneralPBI64(..)));
    assert!(leq.is_none());
}

#[test]
fn parse_only_constraint_equality() {
    let mut lex = OPBToken::lexer("1 z1 2414213213 ~fddsewr = 20431412 ;");
    let mut var_names = VarNameManager::default();

    let (geq, leq) =
        parse_single_constraint(&mut lex, &mut var_names).expect("Constraint should be parsed");

    assert!(matches!(geq, PBConstraintEnum::GeneralPBI64(..)));
    assert!(leq.is_some());
    let leq = leq.unwrap();
    assert!(matches!(leq, PBConstraintEnum::GeneralPBI64(..)));
}

#[test]
fn parse_only_constraint_without_terms() {
    for comparator in [">=", "<=", "="] {
        let source = format!("{comparator} 0 ;");
        let mut lex = OPBToken::lexer(&source);
        let mut var_names = VarNameManager::default();

        parse_single_constraint(&mut lex, &mut var_names).unwrap_or_else(|error| {
            panic!("A constraint without terms written with `{comparator}` should be parsed, but got {error:?}.")
        });
    }
}

#[test]
fn parse_only_objective() {
    let mut lex = OPBToken::lexer("1 x1 2 ~x2 3 x3 4 ;");
    let mut var_names = VarNameManager::default();

    let objective =
        parse_opb_objective(&mut lex, &mut var_names, false).expect("Objective should be parsed.");

    assert_eq!(objective.len(), 3);
    assert_eq!(objective.constant, 4.into());
}

#[test]
fn parse_only_objective_negative() {
    let mut lex = OPBToken::lexer("-1 x1 -2 ~x2 -3 x3 4 ;");
    let mut var_names = VarNameManager::default();

    let objective =
        parse_opb_objective(&mut lex, &mut var_names, false).expect("Objective should be parsed.");

    assert_eq!(objective.len(), 3);
    assert_eq!(objective.constant, (-2).into());
}

/// Regression test: `<=` (and the `<=` half of `=`) is turned into `>=` by negating
/// the terms and the degree. That negation used to be a plain unary minus in the
/// constraint's own integer width, so a degree of `i64::MIN` wrapped back to itself
/// and the infeasible `1 x1 <= -9223372036854775808` was stored as the trivially true
/// `1 ~x1 >= -9223372036854775807`. The release profile had overflow checks disabled,
/// so this wrapped silently rather than panicking.
#[test]
fn parse_leq_with_minimal_degree_does_not_wrap() {
    let mut lex = OPBToken::lexer("1 x1 <= -9223372036854775808 ;");
    let mut var_names = VarNameManager::default();

    let (geq, leq) =
        parse_single_constraint(&mut lex, &mut var_names).expect("Constraint should be parsed");

    assert!(leq.is_none());
    // `1 x1 <= -2^63` is `1 ~x1 >= 2^63 + 1` after normalization, which no assignment
    // can satisfy: the constraint must be contradicting.
    assert!(
        geq.is_contradicting(),
        "`1 x1 <= i64::MIN` is infeasible and must not be stored as a trivially true constraint"
    );
    assert!(!geq.is_trivial());
}

/// The same for the `<=` half of an equality constraint.
#[test]
fn parse_equality_with_minimal_degree_does_not_wrap() {
    let mut lex = OPBToken::lexer("1 x1 = -9223372036854775808 ;");
    let mut var_names = VarNameManager::default();

    let (geq, leq) =
        parse_single_constraint(&mut lex, &mut var_names).expect("Constraint should be parsed");

    assert!(geq.is_trivial(), "`1 x1 >= i64::MIN` is trivially true");
    let leq = leq.expect("an equality constraint yields both directions");
    assert!(
        leq.is_contradicting(),
        "`1 x1 <= i64::MIN` is infeasible and must not be stored as a trivially true constraint"
    );
}

/// A coefficient of `i64::MIN` must escalate as well: negating it is not representable
/// either. `parse_opb_terms` already bails out to the wider type for the coefficient
/// sum, so this is a guard against regressions in that interaction.
#[test]
fn parse_leq_with_minimal_coefficient_does_not_wrap() {
    let mut lex = OPBToken::lexer("-9223372036854775808 x1 <= -9223372036854775808 ;");
    let mut var_names = VarNameManager::default();

    let (geq, leq) =
        parse_single_constraint(&mut lex, &mut var_names).expect("Constraint should be parsed");

    assert!(leq.is_none());
    // `-2^63 x1 <= -2^63` is `2^63 x1 >= 2^63`, i.e. `x1` must be true: satisfiable,
    // so neither trivial nor contradicting.
    assert!(!geq.is_trivial());
    assert!(!geq.is_contradicting());
}

/// What [`parse_opb_from_file`] returns on success: the formula, the variable
/// names, the constraint labels, and the preserved set if the file names one.
type ParsedOpb = (
    Formula,
    VarNameManager,
    ahash::AHashMap<String, isize>,
    Option<ahash::AHashSet<VarIdx>>,
);

/// Write `text` to a temporary `.opb` file and parse it.
fn parse_opb_text(text: &str) -> Result<ParsedOpb, veripb_parser::error::ParserError> {
    use std::io::Write;
    let dir = tempfile::tempdir().expect("failed to create temporary directory");
    let path = dir.path().join("f.opb");
    let mut file = std::fs::File::create(&path).expect("failed to create temporary formula");
    file.write_all(text.as_bytes())
        .expect("failed to write temporary formula");
    file.flush().expect("failed to flush temporary formula");
    parse_opb_from_file(&path)
}

/// the development design notes §XPB Grammar:
///
///     xpb ::= {xpb_skip}, [xpb_objective], {xpb_skip | xpb_constraint}
///
/// — at most one objective, and it precedes every constraint. The reader used
/// to assign on `min:`/`max:` wherever it appeared, so a second objective
/// silently replaced the first and an objective after the constraints was
/// accepted as if it led the file: the same "data silently dropped" shape as
/// wrong verdicts 25/26, though on a file the grammar calls malformed rather
/// than on one with a correct reading.
#[test]
fn parse_refuses_a_second_or_misplaced_objective() {
    for text in [
        // A second objective would silently replace the first.
        "min: 1 x1 ;\nmin: 2 x2 ;\n1 x1 >= 1 ;\n",
        "min: 1 x1 ;\nmax: 2 x2 ;\n1 x1 >= 1 ;\n",
        // An objective after a constraint did not lead the file.
        "1 x1 >= 1 ;\nmin: 1 x1 ;\n",
        // Repeated *and* misplaced.
        "min: 1 x1 ;\n1 x1 >= 1 ;\nmin: 2 x2 ;\n",
    ] {
        assert!(
            parse_opb_text(text).is_err(),
            "an objective the XPB grammar rules out was accepted, silently \
             dropping data: {text:?}"
        );
    }
    // The grammar's own shape still parses: one objective, then constraints.
    let (formula, ..) = parse_opb_text("min: 1 x1 ;\n1 x1 >= 1 ;\n")
        .expect("a well-placed objective must still parse");
    assert_eq!(formula.len(), 1);
    assert!(formula.objective.is_some());
}

/// A second `preserved:` list would silently replace the first, so it is
/// refused; but `preserved:` is not in the XPB grammar at all — it is an
/// extension this checker reads — so its *placement* is free and must stay
/// free rather than creep toward the objective's rule.
#[test]
fn parse_refuses_a_second_preserved_list_but_not_a_late_one() {
    assert!(
        parse_opb_text("preserved: x1 ;\npreserved: x2 ;\n1 x1 >= 1 ;\n").is_err(),
        "a second `preserved:` list was accepted, silently dropping the first"
    );
    let (formula, _, _, preserved) = parse_opb_text("1 x1 >= 1 ;\npreserved: x1 ;\n")
        .expect("a `preserved:` list after the constraints must still parse");
    assert_eq!(formula.len(), 1);
    assert_eq!(preserved.expect("the list was read").len(), 1);
}
