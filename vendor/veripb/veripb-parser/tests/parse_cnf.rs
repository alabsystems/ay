use veripb_formula::prelude::PBConstraint;
use veripb_parser::cnf_parser::parse_cnf_from_file;

#[test]
fn parse_cnf_normal() {
    let (formula, num_vars) = match parse_cnf_from_file("./tests/instances/cnf_normal.cnf") {
        Ok(formula) => formula,
        Err(e) => {
            eprintln!("Parsing error: {e:?}");
            panic!();
        }
    };

    assert_eq!(formula.len(), 2, "Formula should contain 2 clauses.");
    assert_eq!(num_vars, 3, "Formula should contain 3 variables.");
}

#[test]
fn parse_cnf_header_init() {
    let (formula, num_vars) = match parse_cnf_from_file("./tests/instances/cnf_header_init.cnf") {
        Ok(formula) => formula,
        Err(e) => {
            eprintln!("Parsing error: {e:?}");
            panic!();
        }
    };

    assert_eq!(
        formula.capacity(),
        732,
        "Formula should have capacity for 732 clauses."
    );
    assert_eq!(
        num_vars, 42,
        "Formula should have capacity for 42 variables."
    );
}

#[test]
fn parse_cnf_duplicate_lit() {
    let (formula, num_vars) = match parse_cnf_from_file("./tests/instances/cnf_duplicate_lit.cnf") {
        Ok(formula) => formula,
        Err(e) => {
            eprintln!("Parsing error: {e:?}");
            panic!();
        }
    };

    assert_eq!(formula.len(), 2, "Formula should contain 2 clauses.");
    assert_eq!(num_vars, 3, "Formula should contain 3 variables.");
    assert_eq!(formula.constraints[0].len(), 3);
    assert_eq!(formula.constraints[1].len(), 2);
}

#[test]
fn parse_cnf_opposing_literals() {
    let (formula, num_vars) =
        match parse_cnf_from_file("./tests/instances/cnf_opposing_literals.cnf") {
            Ok(formula) => formula,
            Err(e) => {
                eprintln!("Parsing error: {e:?}");
                panic!();
            }
        };

    assert_eq!(formula.len(), 2, "Formula should contain 2 clauses.");
    assert_eq!(num_vars, 3, "Formula should contain 3 variables.");
    assert_eq!(formula.constraints[0].len(), 2);
    assert_eq!(formula.constraints[1].len(), 0);
}
