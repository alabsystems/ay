use veripb_parser::{
    cnf_parser::parse_cnf_from_file, opb_parser::parse_opb_from_file,
    wcnf_parser::parse_wcnf_from_file,
};

#[test]
fn parse_opb_zst() {
    let (formula, var_names, _, _) =
        match parse_opb_from_file("./tests/instances/general_i64.opb.zst") {
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
fn parse_cnf_zst() {
    let (formula, num_vars) = match parse_cnf_from_file("./tests/instances/cnf_normal.cnf.zst") {
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
fn parse_wcnf_zst() {
    let (formula, _var_names) = match parse_wcnf_from_file("./tests/instances/maxsat_mix.wcnf.zst")
    {
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
}

#[test]
fn parse_opb_gz() {
    let (formula, var_names, _, _) =
        match parse_opb_from_file("./tests/instances/general_i64.opb.gz") {
            Ok(formula) => formula,
            Err(e) => {
                eprintln!("Parsing error: {e:?}");
                panic!();
            }
        };

    assert_eq!(formula.len(), 2, "Should parse 2 constraints.");
    assert_eq!(var_names.len(), 4, "Formula should contain 4 variables.")
}

#[test]
fn parse_cnf_gz() {
    let (formula, num_vars) = match parse_cnf_from_file("./tests/instances/cnf_normal.cnf.gz") {
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
fn parse_wcnf_gz() {
    let (formula, _var_names) = match parse_wcnf_from_file("./tests/instances/maxsat_mix.wcnf.gz") {
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
        "Objective should contain 1 term."
    );
}

#[test]
fn parse_opb_xz() {
    let (formula, var_names, _, _) =
        match parse_opb_from_file("./tests/instances/general_i64.opb.xz") {
            Ok(formula) => formula,
            Err(e) => {
                eprintln!("Parsing error: {e:?}");
                panic!();
            }
        };

    assert_eq!(formula.len(), 2, "Should parse 2 constraints.");
    assert_eq!(var_names.len(), 4, "Formula should contain 4 variables.")
}

#[test]
fn parse_cnf_xz() {
    let (formula, num_vars) = match parse_cnf_from_file("./tests/instances/cnf_normal.cnf.xz") {
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
fn parse_wcnf_xz() {
    let (formula, _var_names) = match parse_wcnf_from_file("./tests/instances/maxsat_mix.wcnf.xz") {
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
        "Objective should contain 1 term."
    );
}

#[test]
fn parse_opb_uncompressed_path_without_zst_extension_still_works() {
    // Sanity check: a plain (non-.zst) path must still be read as plain text,
    // not mistakenly run through the zstd decoder.
    let result = parse_opb_from_file("./tests/instances/general_i64.opb");
    assert!(result.is_ok(), "Uncompressed .opb should still parse fine.");
}
