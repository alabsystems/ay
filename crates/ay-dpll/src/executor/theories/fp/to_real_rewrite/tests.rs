// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The Real constants the FP-to-Real rewrites intern by name are spelled in a
//! namespace source text cannot declare, so a user Real constant is never
//! returned in their place.

use super::*;
use crate::Executor;
use ay_core::term::Symbol;
use ay_fp::FpModelValue;
use ay_frontend::{is_reserved_symbol, is_source_reserved_symbol, parse};
use ntest::timeout;

#[test]
fn undefined_fp_to_real_is_not_a_user_constant_spelled_like_the_witness() {
    let mut terms = TermStore::new();
    let fp_sort = Sort::FloatingPoint(8, 24);
    let x = terms.mk_var("x", fp_sort);
    // The spelling this witness had before it moved to the `!ay.` namespace.
    let user = terms.mk_var("__fp_undef_(__NaN_8_24)", Sort::Real);
    let to_real = terms.mk_app(Symbol::named("fp.to_real"), [x], Sort::Real);
    let mut model = FpModel::default();
    model.values.insert(x, FpModelValue::NaN { eb: 8, sb: 24 });
    let mut undefined = HashMap::default();

    let witness = rewrite_fp_to_real_for_model(
        &mut terms,
        to_real,
        &model,
        &mut HashMap::default(),
        &mut undefined,
    );

    assert_ne!(witness, user);
    let TermData::Var(name, _) = terms.get(witness) else {
        panic!("the NaN witness is a variable: {:?}", terms.get(witness));
    };
    assert_eq!(name, &fp_to_real_undefined_name("(_ NaN 8 24)"));
    // Source text cannot declare it; it is not an `__ay_` name, whose
    // assertions model validation would skip.
    assert!(is_source_reserved_symbol(name), "{name}");
    assert!(!is_reserved_symbol(name), "{name}");
}

#[test]
fn every_fp_to_real_witness_spelling_is_source_reserved_outside_the_ay_prefix() {
    for name in [
        fp_to_real_undefined_name("(_ NaN 5 11)"),
        fp_to_real_undefined_name("(_ +oo 8 24)"),
        fp_to_real_target_name(0),
        fp_to_real_target_name(17),
    ] {
        assert!(is_source_reserved_symbol(&name), "{name}");
        assert!(!name.starts_with("__ay_"), "{name}");
    }
}

#[test]
#[timeout(60_000)]
fn a_user_real_spelled_like_the_old_nan_witness_keeps_the_query_sat() {
    let script = r#"
(set-logic QF_FPLRA)
(declare-const x (_ FloatingPoint 8 24))
(declare-const |__fp_undef_(__NaN_8_24)| Real)
(assert (fp.isNaN x))
(assert (= |__fp_undef_(__NaN_8_24)| 5.0))
(assert (= (fp.to_real x) 7.0))
(check-sat)
"#;
    let commands = parse(script).expect("the script parses");
    let mut exec = Executor::new();
    let output = exec.execute_all(&commands).expect("the script executes");
    assert_eq!(output, vec!["sat".to_string()]);
}
