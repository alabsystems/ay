use logos::Logos;
use veripb_formula::prelude::*;
use veripb_parser::{
    opb_token::OPBToken,
    pbp_parser::legacy_v2::{parser::parse_substitution, tokens::SubstitutionToken},
};

#[test]
fn parse_substitution_from_scratch() {
    let mut var_names = VarNameManager::default();
    let x1 = var_names.add_by_name("x1");
    let x2 = var_names.add_by_name("x2");
    let x3 = var_names.add_by_name("x3");
    let x4 = var_names.add_by_name("x4");

    let mut lex = SubstitutionToken::lexer("x1 0 x2 1 x3 x1 x4 ~x1");

    let sub = parse_substitution(&mut lex, &mut var_names).expect("Parsing error!");

    assert_eq!(sub.get(x1), Some(SubstitutionValue::FALSE));
    assert_eq!(sub.get(x2), Some(SubstitutionValue::TRUE));
    assert_eq!(
        sub.get(x3),
        Some(SubstitutionValue::lit(Lit::from_var(x1, false)))
    );
    assert_eq!(
        sub.get(x4),
        Some(SubstitutionValue::lit(Lit::from_var(x1, true)))
    );
    assert_eq!(sub.get(4), None);
}

#[test]
fn parse_substitution_var_twice_in_domain() {
    let mut var_names = VarNameManager::default();

    let mut lex = SubstitutionToken::lexer("x1 0 x1 1 x3 x1 x4 ~x1");

    let sub = parse_substitution(&mut lex, &mut var_names);

    assert!(sub.is_err());
}

#[test]
fn parse_substitution_change_lexer() {
    let mut var_names = VarNameManager::default();
    let x1 = var_names.add_by_name("x1");
    let x2 = var_names.add_by_name("x2");
    let x3 = var_names.add_by_name("x3");
    let x4 = var_names.add_by_name("x4");

    let lex = OPBToken::lexer("x1 0 x2 1 x3 x1 x4 ~x1");

    let sub = parse_substitution(&mut lex.morph(), &mut var_names).expect("Parsing error!");

    assert_eq!(sub.get(x1), Some(SubstitutionValue::FALSE));
    assert_eq!(sub.get(x2), Some(SubstitutionValue::TRUE));
    assert_eq!(
        sub.get(x3),
        Some(SubstitutionValue::lit(Lit::from_var(x1, false)))
    );
    assert_eq!(
        sub.get(x4),
        Some(SubstitutionValue::lit(Lit::from_var(x1, true)))
    );
    assert_eq!(sub.get(4), None);
}

#[test]
fn parse_substitution_with_map_symbol() {
    let mut var_names = VarNameManager::default();
    let x1 = var_names.add_by_name("x1");
    let x2 = var_names.add_by_name("x2");
    let x3 = var_names.add_by_name("x3");
    let x4 = var_names.add_by_name("x4");

    let mut lex = SubstitutionToken::lexer("x1 -> 0 x2 1 x3 → x1 x4 -> ~x1");

    let sub = parse_substitution(&mut lex, &mut var_names).expect("Parsing error!");

    assert_eq!(sub.get(x1), Some(SubstitutionValue::FALSE));
    assert_eq!(sub.get(x2), Some(SubstitutionValue::TRUE));
    assert_eq!(
        sub.get(x3),
        Some(SubstitutionValue::lit(Lit::from_var(x1, false)))
    );
    assert_eq!(
        sub.get(x4),
        Some(SubstitutionValue::lit(Lit::from_var(x1, true)))
    );
    assert_eq!(sub.get(4), None);
}
