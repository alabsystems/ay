use logos::Logos;
use veripb_formula::prelude::*;
use veripb_parser::pbp_parser::legacy_v2::{
    parser::parse_bool_assignment_to_raw_vec, tokens::AssignmentToken,
};

#[test]
fn read_assignment_without_resize() {
    let mut var_names = VarNameManager::default();
    let x1 = var_names.add_by_name("x1");
    let _x2 = var_names.add_by_name("x83e42");
    let x3 = var_names.add_by_name("s452345llkj4dse435");
    let _x4 = var_names.add_by_name("rs3s322ed3e3d");
    let x5 = var_names.add_by_name("x8fewsafssfwsa3w82");

    let mut lex = AssignmentToken::lexer("x1 ~s452345llkj4dse435 x8fewsafssfwsa3w82");
    let assignment_vec =
        parse_bool_assignment_to_raw_vec(&mut lex, &mut var_names).expect("Parsing error!");

    assert!(!assignment_vec[0].is_negated());
    assert!(assignment_vec[1].is_negated());
    assert!(!assignment_vec[2].is_negated());
    assert_eq!(assignment_vec[0].get_var(), x1);
    assert_eq!(assignment_vec[1].get_var(), x3);
    assert_eq!(assignment_vec[2].get_var(), x5);
}
