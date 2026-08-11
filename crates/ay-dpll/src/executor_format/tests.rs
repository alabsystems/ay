// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::term::Symbol;
use num_bigint::BigInt;
use num_rational::BigRational;

#[test]
fn format_sort_handles_core_sorts_and_quoting() {
    assert_eq!(format_sort(&Sort::Bool), "Bool");
    assert_eq!(format_sort(&Sort::RegLan), "RegLan");
    assert_eq!(format_sort(&Sort::bitvec(8)), "(_ BitVec 8)");
    assert_eq!(
        format_sort(&Sort::array(Sort::Int, Sort::Bool)),
        "(Array Int Bool)"
    );
    assert_eq!(
        format_sort(&Sort::Uninterpreted("let".to_string())),
        "|let|"
    );
}

#[test]
fn format_symbol_quotes_reserved_words_and_formats_indices() {
    assert_eq!(format_symbol(&Symbol::named("x")), "x");
    assert_eq!(format_symbol(&Symbol::named("let")), "|let|");
    assert_eq!(
        format_symbol(&Symbol::indexed("extract", vec![7, 4])),
        "(_ extract 7 4)"
    );
}

#[test]
fn format_rational_prints_integer_and_fractional_values() {
    assert_eq!(
        format_rational(&BigRational::from_integer(BigInt::from(5))),
        "5.0"
    );
    assert_eq!(
        format_rational(&BigRational::from_integer(BigInt::from(-5))),
        "(- 5.0)"
    );
    assert_eq!(
        format_rational(&BigRational::new(BigInt::from(3), BigInt::from(2))),
        "(/ 3 2)"
    );
    assert_eq!(
        format_rational(&BigRational::new(BigInt::from(-3), BigInt::from(2))),
        "(- (/ 3 2))"
    );
}

#[test]
fn format_real_prints_z3_exact_user_facing_values() {
    // Integer arm: identical to format_rational.
    assert_eq!(
        format_real(&BigRational::from_integer(BigInt::from(5))),
        "5.0"
    );
    assert_eq!(
        format_real(&BigRational::from_integer(BigInt::from(-5))),
        "(- 5.0)"
    );
    assert_eq!(
        format_real(&BigRational::from_integer(BigInt::from(0))),
        "0.0"
    );
    // Fraction arm: z3-exact decimal components (#real-fmt).
    assert_eq!(
        format_real(&BigRational::new(BigInt::from(7), BigInt::from(2))),
        "(/ 7.0 2.0)"
    );
    assert_eq!(
        format_real(&BigRational::new(BigInt::from(-7), BigInt::from(2))),
        "(- (/ 7.0 2.0))"
    );
}

#[test]
fn format_bigint_uses_unary_minus_form() {
    assert_eq!(format_bigint(&BigInt::from(0)), "0");
    assert_eq!(format_bigint(&BigInt::from(7)), "7");
    assert_eq!(format_bigint(&BigInt::from(-7)), "(- 7)");
}

#[test]
fn format_bitvec_masks_and_pads() {
    // Width 4: divisible by 4, uses hex
    assert_eq!(format_bitvec(&BigInt::from(3), 4), "#x3");
    // Width 8: divisible by 4, uses hex
    assert_eq!(format_bitvec(&BigInt::from(0xA_u32), 8), "#x0a");
    assert_eq!(format_bitvec(&BigInt::from(-1), 8), "#xff");
    // Width 1: not divisible by 4, uses binary (#1793)
    assert_eq!(format_bitvec(&BigInt::from(0), 1), "#b0");
    assert_eq!(format_bitvec(&BigInt::from(1), 1), "#b1");
    // Width 49: not divisible by 4, uses binary (#1793)
    assert_eq!(
        format_bitvec(&BigInt::from(1), 49),
        "#b0000000000000000000000000000000000000000000000001"
    );
    // Width 64: boundary case, divisible by 4, uses hex (#1793)
    assert_eq!(format_bitvec(&BigInt::from(1), 64), "#x0000000000000001");
    // Width 65: > 64 and not divisible by 4 -> still binary, zero-padded to the
    // full width. This case previously printed the indexed form `(_ bv1 65)`;
    // that is legal SMT-LIB but z3 5.0.0 never emits it (measured: z3 prints
    // `#b0…01`), so the pin was corrected to match z3.
    assert_eq!(
        format_bitvec(&BigInt::from(1), 65),
        "#b00000000000000000000000000000000000000000000000000000000000000001"
    );
    // Width 68: > 64, divisible by 4, still uses hex (#1793)
    assert_eq!(format_bitvec(&BigInt::from(1), 68), "#x00000000000000001");
    // Negative inputs print their two's-complement pattern at both a hex and a
    // binary width (the modular reduction, not a sign-magnitude mask).
    assert_eq!(format_bitvec(&BigInt::from(-1), 5), "#b11111");
    assert_eq!(format_bitvec(&BigInt::from(-2), 65), {
        let mut s = String::from("#b");
        s.push_str(&"1".repeat(64));
        s.push('0');
        s
    });
}

#[test]
fn format_model_atom_quotes_uninterpreted_values() {
    // Non-uninterpreted sorts return value as-is
    assert_eq!(format_model_atom(&Sort::Int, "42"), "42");
    assert_eq!(format_model_atom(&Sort::Bool, "true"), "true");
    assert_eq!(format_model_atom(&Sort::Real, "3.14"), "3.14");
    assert_eq!(format_model_atom(&Sort::bitvec(8), "#xff"), "#xff");

    // ABSTRACT values (`@Sort!n` internal representatives) of an
    // uninterpreted/datatype sort are sort-ascribed: the bare token is an
    // unbound identifier to a model validator; `(as @U!0 U)` is the standard
    // abstract-value syntax and validates (#mv-abstract-value-ascription).
    assert_eq!(
        format_model_atom(&Sort::Uninterpreted("U".to_string()), "@U!0"),
        "(as @U!0 U)"
    );
    assert_eq!(
        format_model_atom(
            &Sort::Datatype(ay_core::DatatypeSort::new("Pair", vec![])),
            "@Pair!1"
        ),
        "(as @Pair!1 Pair)"
    );

    // Simple identifiers don't need quoting
    assert_eq!(
        format_model_atom(&Sort::Uninterpreted("U".to_string()), "elem0"),
        "elem0"
    );

    // Values with spaces or reserved words need quoting
    assert_eq!(
        format_model_atom(&Sort::Uninterpreted("U".to_string()), "foo bar"),
        "|foo bar|"
    );
    // Reserved word 'true' needs quoting (even as uninterpreted value)
    assert_eq!(
        format_model_atom(&Sort::Uninterpreted("U".to_string()), "true"),
        "|true|"
    );
}

#[test]
fn format_default_value_produces_smt_lib_defaults() {
    let context = ay_frontend::Context::new();
    let format = |sort: &Sort| format_default_value_surface(&context, sort);
    assert_eq!(format(&Sort::Bool), "false");
    assert_eq!(format(&Sort::Int), "0");
    assert_eq!(format(&Sort::Real), "0.0");
    assert_eq!(format(&Sort::String), "\"\"");
    assert_eq!(format(&Sort::RegLan), "re.none");
    // width%4==0 uses hex (#1793)
    assert_eq!(format(&Sort::bitvec(8)), "#x00");
    assert_eq!(format(&Sort::bitvec(4)), "#x0");
    assert_eq!(format(&Sort::bitvec(16)), "#x0000");
    // width%4!=0 uses binary (#1793)
    assert_eq!(format(&Sort::bitvec(1)), "#b0");
    assert_eq!(format(&Sort::bitvec(7)), "#b0000000");
    assert_eq!(format(&Sort::FloatingPoint(8, 24)), "(_ +zero 8 24)");
    // Abstract `@Sort!n` defaults are sort-ascribed so they validate as model
    // values (#mv-abstract-value-ascription).
    assert_eq!(format(&Sort::Uninterpreted("U".to_string())), "(as @U!0 U)");
    assert_eq!(
        format(&Sort::Datatype(ay_core::DatatypeSort::new("List", vec![]))),
        "(as @List!0 List)"
    );
    // Nested array sort
    assert_eq!(
        format(&Sort::array(Sort::Int, Sort::Bool)),
        "((as const (Array Int Bool)) false)"
    );
}

// NOTE: the former `format_value(sort, Option<bool>, ..)` — which fabricated a
// sort default into user-visible model output whenever the evaluator returned
// Unknown — is REMOVED (#no-fabricated-model-values). Unconstrained variables
// are now completed in the model itself before validation (model/completion.rs),
// and a print-time miss is an explicit error, never a fabricated value.

/// #closure-capture-uninterp-range: canonicalization must invert BOTH printed
/// spellings of an abstract atom — the plain `(as @S!n S)` AND the
/// pipe-quoted `(as |@S!n| |S|)` the printer emits when the sort name needs
/// quoting (e.g. the verification-consumer carrier sort `__verification_consumer_mutref::int`). The
/// quoted spelling previously escaped the strip, so one element masqueraded
/// as two and the independent gate falsely refuted a valid model.
#[test]
fn strip_abstract_atom_ascription_handles_quoted_and_bare_spellings() {
    // Plain spelling (unchanged behavior).
    assert_eq!(strip_abstract_atom_ascription("(as @U!0 U)"), Some("@U!0"));
    // Pipe-quoted atom and sort (the verification-consumer mut-ref carrier shape).
    assert_eq!(
        strip_abstract_atom_ascription(
            "(as |@__verification_consumer_mutref::int!0| |__verification_consumer_mutref::int|)"
        ),
        Some("@__verification_consumer_mutref::int!0")
    );
    // Quoted atom with an unquoted sort.
    assert_eq!(
        strip_abstract_atom_ascription("(as |@S!1| S)"),
        Some("@S!1")
    );
    // A datatype-constructor ascription is NOT an abstract atom.
    assert_eq!(strip_abstract_atom_ascription("(as nil (List Int))"), None);
    assert_eq!(
        strip_abstract_atom_ascription("(as |nil| (List Int))"),
        None
    );
    // No sort part -> not an as-cast shape.
    assert_eq!(strip_abstract_atom_ascription("(as @U!0)"), None);
    // Bare atoms are left to the caller (canonical_internal_atom identity).
    assert_eq!(strip_abstract_atom_ascription("@U!0"), None);
    assert_eq!(canonical_internal_atom("@U!0"), "@U!0");
    assert_eq!(
        canonical_internal_atom(
            "(as |@__verification_consumer_mutref::int!0| |__verification_consumer_mutref::int|)"
        ),
        "@__verification_consumer_mutref::int!0"
    );
}

/// Round-trip: `format_model_atom` -> `canonical_internal_atom` must be the
/// identity on the internal bare dialect for quoting-required sort names.
#[test]
fn format_model_atom_round_trips_through_canonicalization() {
    let sort = Sort::Uninterpreted("__verification_consumer_mutref::int".to_string());
    let printed = format_model_atom(&sort, "@__verification_consumer_mutref::int!0");
    assert_eq!(
        printed,
        "(as |@__verification_consumer_mutref::int!0| |__verification_consumer_mutref::int|)"
    );
    assert_eq!(
        canonical_internal_atom(&printed),
        "@__verification_consumer_mutref::int!0"
    );
    // Simple sort names keep the historical unquoted spelling.
    let simple = Sort::Uninterpreted("U".to_string());
    let printed_simple = format_model_atom(&simple, "@U!0");
    assert_eq!(printed_simple, "(as @U!0 U)");
    assert_eq!(canonical_internal_atom(&printed_simple), "@U!0");
}
