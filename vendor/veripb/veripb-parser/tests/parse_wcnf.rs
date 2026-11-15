use malachite_bigint::BigInt;
use num_traits::{One, Zero};
use veripb_parser::wcnf_parser::parse_wcnf_from_file;

#[test]
fn parse_wcnf_empty() {
    let (formula, var_names) = match parse_wcnf_from_file("./tests/instances/empty.wcnf") {
        Ok(formula) => formula,
        Err(e) => {
            eprintln!("Parsing error: {e:?}");
            panic!();
        }
    };

    assert_eq!(formula.len(), 0, "Formula should contain 0 clauses.");
    assert_eq!(
        formula.objective.as_ref().unwrap().len(),
        0,
        "Objective should contain 0 terms."
    );
    assert!(
        formula.objective.as_ref().unwrap().constant.is_zero(),
        "Objective constant should be 0."
    );
    assert_eq!(var_names.len(), 0, "Formula should contain 0 variables.");
}

#[test]
fn parse_wcnf_empty_soft() {
    let (formula, var_names) =
        match parse_wcnf_from_file("./tests/instances/empty_soft_clause.wcnf") {
            Ok(formula) => formula,
            Err(e) => {
                eprintln!("Parsing error: {e:?}");
                panic!();
            }
        };

    assert_eq!(formula.len(), 0, "Formula should contain 0 clauses.");
    assert_eq!(
        formula.objective.as_ref().unwrap().len(),
        0,
        "Objective should contain 0 terms."
    );
    assert_eq!(
        formula.objective.as_ref().unwrap().constant,
        BigInt::one(),
        "Objective constant should be 1."
    );
    assert_eq!(var_names.len(), 0, "Formula should contain 0 variables.");
}

#[test]
fn parse_maxsat_1() {
    let (formula, var_names) = match parse_wcnf_from_file("./tests/instances/maxsat_mix.wcnf") {
        Ok(formula) => formula,
        Err(e) => {
            eprintln!("Parsing error: {e:?}");
            panic!();
        }
    };

    assert_eq!(formula.len(), 3, "Formula should contain 3 clauses.");
    assert_eq!(
        formula.objective.as_ref().unwrap().len(),
        1,
        "Objective should contain 1 terms."
    );
    assert_eq!(
        formula.objective.as_ref().unwrap().constant,
        BigInt::zero(),
        "Objective constant should be 0."
    );
    assert_eq!(var_names.len(), 5, "Formula should contain 5 variables.");
}

#[test]
fn parse_maxsat_2() {
    let (formula, var_names) =
        match parse_wcnf_from_file("./tests/instances/maxsat_new_format.wcnf") {
            Ok(formula) => formula,
            Err(e) => {
                eprintln!("Parsing error: {e:?}");
                panic!();
            }
        };

    assert_eq!(formula.len(), 7, "Formula should contain 7 clauses.");
    assert_eq!(
        formula.objective.as_ref().unwrap().len(),
        4,
        "Objective should contain 4 terms."
    );
    assert_eq!(
        formula.objective.as_ref().unwrap().constant,
        BigInt::zero(),
        "Objective constant should be 0."
    );
    assert_eq!(var_names.len(), 8, "Formula should contain 8 variables.");
}

#[test]
fn parse_maxsat_cancelling_objective_lits() {
    let (formula, var_names) =
        match parse_wcnf_from_file("./tests/instances/maxsat_cancelling_objective_lits.wcnf") {
            Ok(formula) => formula,
            Err(e) => {
                eprintln!("Parsing error: {e:?}");
                panic!();
            }
        };

    assert_eq!(formula.len(), 0, "Formula should contain 0 clauses.");
    assert_eq!(
        formula.objective.as_ref().unwrap().len(),
        1,
        "Objective should contain 1 terms."
    );
    assert_eq!(
        formula.objective.as_ref().unwrap().constant,
        1038862559.into(),
        "Objective constant should be 1038862559."
    );
    assert_eq!(var_names.len(), 1, "Formula should contain 1 variables.");
}
