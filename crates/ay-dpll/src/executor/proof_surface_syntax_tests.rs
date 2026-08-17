// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn indexed_literal_and_same_spelled_symbol_format_distinctly() {
    let parsed = FrontendTerm::App(
        "distinct".to_string(),
        vec![
            FrontendTerm::Symbol("(_ bv0 8)".to_string()),
            FrontendTerm::IndexedApp(
                "bv0".to_string(),
                vec![FrontendIndex::Numeral("8".to_string())],
                Vec::new(),
            ),
        ],
    );
    assert_eq!(
        format_frontend_term(&parsed),
        "(distinct |(_ bv0 8)| (_ bv0 8))"
    );
}

#[test]
fn indexed_token_kinds_remain_distinct_when_formatted() {
    for (index, expected) in [
        (FrontendIndex::Numeral("8".to_string()), "8"),
        (FrontendIndex::Decimal("0.5".to_string()), "0.5"),
        (FrontendIndex::Symbol("8".to_string()), "|8|"),
        (FrontendIndex::Hexadecimal("#x41".to_string()), "#x41"),
        (FrontendIndex::Symbol("#x41".to_string()), "|#x41|"),
    ] {
        let term = FrontendTerm::IndexedApp("f".to_string(), vec![index], Vec::new());
        assert_eq!(format_frontend_term(&term), format!("(_ f {expected})"));
    }
}

#[test]
fn authored_formatter_preserves_pattern_annotations() {
    let commands =
        ay_frontend::parse("(assert (forall ((x X)) (! (= x x) :pattern ((as c X)) :qid q)))")
            .expect("fixture parses");
    let ay_frontend::Command::Assert(term) = &commands[0] else {
        panic!("fixture must be an assertion")
    };
    assert_eq!(
        format_authored_frontend_term(term),
        "(forall ((x X)) (! (= x x) :pattern ((as c X)) :qid q))"
    );
}

#[test]
fn frontend_string_constants_use_round_trip_safe_smtlib_escaping() {
    assert_eq!(
        format_frontend_constant(&FrontendConstant::String(r"\u{61}".to_string())),
        r#""\u{5c}u{61}""#,
    );
    assert_eq!(
        format_frontend_constant(&FrontendConstant::String("\0".to_string())),
        r#""\u{0}""#,
    );
}

#[test]
fn bound_collector_skips_identity_constant_spellings() {
    for constant in [
        FrontendConstant::Numeral("7".to_string()),
        FrontendConstant::Binary("#b0011".to_string()),
        FrontendConstant::String("quoted \" text".to_string()),
        FrontendConstant::String(r"\u{61}".to_string()),
        FrontendConstant::String("control\0\n\t".to_string()),
    ] {
        let mut ctx = Context::new();
        let parsed = FrontendTerm::Const(constant);
        let canonical = ctx
            .elaborate_surface_subterm(&parsed)
            .expect("constant fixture elaborates");
        assert_eq!(
            format_frontend_term(&parsed),
            ay_proof::format_term_alethe(&ctx.terms, canonical),
            "fixture must use the canonical Alethe spelling"
        );

        let mut overrides = HashMap::default();
        collect_bound_surface_overrides(&mut ctx, &parsed, &[], &mut overrides);
        assert!(!overrides.contains_key(&canonical));
    }
}

#[test]
fn bound_collector_retains_nonidentity_constant_spellings() {
    for constant in [
        FrontendConstant::Decimal("1.00".to_string()),
        FrontendConstant::Hexadecimal("#x0f".to_string()),
    ] {
        let mut ctx = Context::new();
        let parsed = FrontendTerm::Const(constant);
        let canonical = ctx
            .elaborate_surface_subterm(&parsed)
            .expect("constant fixture elaborates");
        let authored = format_frontend_term(&parsed);
        assert_ne!(
            authored,
            ay_proof::format_term_alethe(&ctx.terms, canonical),
            "fixture must exercise a non-canonical surface spelling"
        );

        let mut overrides = HashMap::default();
        collect_bound_surface_overrides(&mut ctx, &parsed, &[], &mut overrides);
        assert_eq!(overrides.get(&canonical), Some(&authored));
    }
}

/// A surface override inside a binder may re-spell a term, never re-write it.
///
/// Elaboration folds `(+ x 0)` and `(* 1 x)` to the bare bound variable `x`.
/// Attaching either composite spelling to that leaf would rename every `x` in
/// an exported proof and can give one Skolem witness incompatible choice
/// renderings.  The comparison itself is different: canonical `(<= x y)`
/// strictly contains both operands, so retaining its authored spelling is a
/// genuine re-spelling.  Pin both sides so the containment guard cannot pass
/// merely by dropping every override.
#[test]
fn bound_collector_respells_comparisons_without_rewriting_folded_leaves() {
    for (operator, identity) in [("+", "0"), ("*", "1")] {
        let mut ctx = Context::new();
        for (name, sort) in [("y", "Int"), ("p", "Bool")] {
            ctx.process_command(&ay_frontend::Command::DeclareConst(
                name.to_string(),
                FrontendSort::Simple(sort.to_string()),
            ))
            .expect("fixture declaration succeeds");
        }

        let folded_lhs = FrontendTerm::App(
            operator.to_string(),
            vec![
                FrontendTerm::Symbol("x".to_string()),
                FrontendTerm::Const(FrontendConstant::Numeral(identity.to_string())),
            ],
        );
        let comparison = FrontendTerm::App(
            "<=".to_string(),
            vec![folded_lhs.clone(), FrontendTerm::Symbol("y".to_string())],
        );
        let quantified = FrontendTerm::Forall(
            vec![("x".to_string(), FrontendSort::Simple("Int".to_string()))],
            Box::new(FrontendTerm::App(
                "or".to_string(),
                vec![comparison.clone(), FrontendTerm::Symbol("p".to_string())],
            )),
        );
        let canonical = ctx
            .elaborate_surface_subterm(&quantified)
            .expect("quantified fixture elaborates");
        let mut overrides = HashMap::default();
        assert!(collect_surface_term_overrides(
            &mut ctx,
            canonical,
            &quantified,
            &mut overrides,
        ));

        for (&term, spelling) in &overrides {
            let is_leaf = matches!(ctx.terms.get(term), TermData::Var(..) | TermData::Const(..));
            assert!(
                !(is_leaf && spelling.starts_with('(')),
                "({operator} x {identity}): a surface override rewrote leaf {term:?} \
                 ({:?}) as composite `{spelling}`",
                ctx.terms.get(term),
            );
        }

        let authored_comparison = format_frontend_term(&comparison);
        assert_eq!(
            authored_comparison,
            format!("(<= ({operator} x {identity}) y)"),
            "fixture must retain the intended authored spelling",
        );
        assert!(
            overrides
                .values()
                .any(|spelling| spelling == &authored_comparison),
            "the genuine comparison re-spelling must survive; collected {overrides:?}",
        );
    }
}
