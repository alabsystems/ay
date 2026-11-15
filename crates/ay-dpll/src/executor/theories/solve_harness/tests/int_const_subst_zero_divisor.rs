// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The int-constant substitution shared by the UFNIA and AUFLIA
//! preprocessors, on `div` and `mod` whose divisor it substitutes.

use super::super::substitute_int_constants_preserving_definitions;
use ay_core::term::{Constant, TermData};
use ay_core::{Sort, TermId, TermStore};
use num_traits::Zero;

/// True if `term` has a `div`/`mod` application (named `op`) whose divisor is
/// the literal 0 somewhere below it.
fn has_zero_divisor_app(terms: &TermStore, term: TermId, op: &str) -> bool {
    match terms.get(term) {
        TermData::App(sym, args) => {
            let zero_divisor = args.len() == 2
                && matches!(terms.get(args[1]), TermData::Const(Constant::Int(v)) if v.is_zero());
            (sym.name() == op && zero_divisor)
                || args.iter().any(|&arg| has_zero_divisor_app(terms, arg, op))
        }
        TermData::Not(inner) => has_zero_divisor_app(terms, *inner, op),
        _ => false,
    }
}

/// A divisor that an asserted `(= y 0)` substitutes to 0 keeps its `div` and
/// `mod`: SMT-LIB leaves `(div t 0)` and `(mod t 0)` unspecified, so they may
/// not be rewritten to `0` and `t`.
#[test]
fn int_const_substitution_keeps_zero_divisor_div_and_mod() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("div0_subst_x", Sort::Int);
    let y = terms.mk_var("div0_subst_y", Sort::Int);
    let zero = terms.mk_int(num_bigint::BigInt::from(0));
    let seven = terms.mk_int(num_bigint::BigInt::from(7));
    let definition = terms.mk_eq(y, zero);
    let div = terms.mk_intdiv(x, y);
    let div_is_seven = terms.mk_eq(div, seven);
    let modulo = terms.mk_mod(x, y);
    let mod_is_not_x = {
        let eq = terms.mk_eq(modulo, x);
        terms.mk_not(eq)
    };
    let mut assertions = vec![definition, div_is_seven, mod_is_not_x];
    let mut source_sets = vec![None, None, None];

    assert!(substitute_int_constants_preserving_definitions(
        &mut terms,
        &mut assertions,
        &mut source_sets,
    ));
    assert!(
        has_zero_divisor_app(&terms, assertions[1], "div"),
        "(= (div x y) 7) with y = 0 must become (= (div x 0) 7), not (= 0 7)"
    );
    assert!(
        has_zero_divisor_app(&terms, assertions[2], "mod"),
        "(not (= (mod x y) x)) with y = 0 must keep (mod x 0), not fold to x"
    );
    assert_ne!(assertions[1], terms.false_term());
    assert_ne!(assertions[2], terms.false_term());
}

/// Twin of the test above: with a nonzero divisor and a constant dividend the
/// substitution still folds `div` and `mod` to their Euclidean values.
#[test]
fn int_const_substitution_folds_nonzero_divisor_div_and_mod() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("div3_subst_x", Sort::Int);
    let y = terms.mk_var("div3_subst_y", Sort::Int);
    let three = terms.mk_int(num_bigint::BigInt::from(3));
    let minus_seven = terms.mk_int(num_bigint::BigInt::from(-7));
    let seven = terms.mk_int(num_bigint::BigInt::from(7));
    let def_x = terms.mk_eq(x, minus_seven);
    let def_y = terms.mk_eq(y, three);
    let div = terms.mk_intdiv(x, y);
    let div_is_seven = terms.mk_eq(div, seven);
    let modulo = terms.mk_mod(x, y);
    let two = terms.mk_int(num_bigint::BigInt::from(2));
    let mod_is_two = terms.mk_eq(modulo, two);
    let mut assertions = vec![def_x, def_y, div_is_seven, mod_is_two];
    let mut source_sets = vec![None, None, None, None];

    assert!(substitute_int_constants_preserving_definitions(
        &mut terms,
        &mut assertions,
        &mut source_sets,
    ));
    assert_eq!(
        assertions[2],
        terms.false_term(),
        "(div -7 3) is -3, so (= (div x y) 7) folds to false"
    );
    assert_eq!(
        assertions[3],
        terms.true_term(),
        "(mod -7 3) is 2, so (= (mod x y) 2) folds to true"
    );
}
