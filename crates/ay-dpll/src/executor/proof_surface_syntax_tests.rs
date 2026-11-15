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

/// A positive authored `exists` is descended exactly like a `forall`.
///
/// The eighth false green's `sko_ex` sibling: elaboration renames the binder
/// (`z` to `z_N`) and canonicalizes `(>= z 0)` to `(<= 0 z_N)`, so without the
/// descent the body's atoms had no authored spelling and the certified
/// `sko_ex` printer carried nothing across `binder := choice` — the instance
/// and its projections printed the canonical atoms under an anchored `refl`
/// over the authored body, and pinned carcara refused the step. Pinned on
/// both quantifiers so the two descents cannot drift apart.
#[test]
fn bound_collector_descends_a_positive_exists_body_like_a_forall() {
    type Build = fn(Vec<(String, FrontendSort)>, Box<FrontendTerm>) -> FrontendTerm;
    let quantifiers: [(&str, Build); 2] = [
        ("exists", |bindings, body| {
            FrontendTerm::Exists(bindings, body)
        }),
        ("forall", |bindings, body| {
            FrontendTerm::Forall(bindings, body)
        }),
    ];
    for (quantifier, build) in quantifiers {
        let mut ctx = Context::new();
        ctx.process_command(&ay_frontend::Command::DeclareFun(
            "g".to_string(),
            vec![FrontendSort::Simple("Int".to_string())],
            FrontendSort::Simple("Int".to_string()),
        ))
        .expect("fixture declaration succeeds");
        let z = || FrontendTerm::Symbol("z".to_string());
        let zero = || FrontendTerm::Const(FrontendConstant::Numeral("0".to_string()));
        let nonnegative = FrontendTerm::App(">=".to_string(), vec![z(), zero()]);
        let below_g = FrontendTerm::App(
            "<".to_string(),
            vec![FrontendTerm::App("g".to_string(), vec![z()]), z()],
        );
        let quantified = build(
            vec![("z".to_string(), FrontendSort::Simple("Int".to_string()))],
            Box::new(FrontendTerm::App(
                "and".to_string(),
                vec![nonnegative.clone(), below_g],
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

        let authored_atom = format_frontend_term(&nonnegative);
        assert_eq!(authored_atom, "(>= z 0)");
        let respelled: Vec<TermId> = overrides
            .iter()
            .filter(|(_, spelling)| *spelling == &authored_atom)
            .map(|(term, _)| *term)
            .collect();
        assert_eq!(
            respelled.len(),
            1,
            "{quantifier}: the canonicalized body atom must carry its authored \
             spelling exactly once; collected {overrides:?}",
        );
        let atom = respelled[0];
        assert!(
            matches!(
                ctx.terms.get(atom),
                TermData::App(symbol, operands) if symbol.name() == "<=" && operands.len() == 2
            ),
            "{quantifier}: the authored `(>= z 0)` is keyed on the store's `(<= 0 z_N)`, \
             got {:?}",
            ctx.terms.get(atom),
        );
        let (bindings, body) = match ctx.terms.get(canonical) {
            TermData::Forall(bindings, body, _) | TermData::Exists(bindings, body, _) => {
                (bindings.clone(), *body)
            }
            other => panic!("{quantifier}: fixture must elaborate to a quantifier, got {other:?}"),
        };
        assert_eq!(bindings.len(), 1);
        assert!(
            ctx.terms.children(body).contains(&atom),
            "{quantifier}: the respelled atom must be a conjunct of the canonical body",
        );
    }
}

/// Collect the overrides of one authored assertion over `script`.
fn collected_overrides(script: &str, assertion: &str) -> (TermId, HashMap<TermId, String>) {
    let mut ctx = Context::new();
    for command in ay_frontend::parse(script).expect("parse") {
        ctx.process_command(&command).expect("declare");
    }
    let commands = ay_frontend::parse(&format!("(assert {assertion})")).expect("parse");
    let [ay_frontend::Command::Assert(authored)] = commands.as_slice() else {
        panic!("one assertion expected");
    };
    let canonical = ctx
        .elaborate_surface_subterm(authored)
        .expect("assertion elaborates");
    let mut overrides = HashMap::default();
    assert!(collect_surface_term_overrides(
        &mut ctx,
        canonical,
        authored,
        &mut overrides
    ));
    (canonical, overrides)
}

fn names(spelling: &str, symbol: &str) -> bool {
    spelling
        .split(|c: char| c == '(' || c == ')' || c.is_whitespace())
        .any(|token| token == symbol)
}

/// A descendant spelling that names a nullary `define-fun` is never recorded:
/// it would re-spell its `TermId` document-wide as a symbol pinned carcara
/// reads as an opaque constant. The assertion's own root spelling, which the
/// printer bridges through the definition premise, still is.
#[test]
fn a_descendant_spelling_that_names_a_nullary_macro_is_never_recorded() {
    let (root, overrides) = collected_overrides(
        "(declare-const x Int)(declare-const r Bool)(define-fun m () Bool (< x 3))",
        "(or r (not m))",
    );
    assert_eq!(
        overrides.get(&root).map(String::as_str),
        Some("(or r (not m))")
    );
    for (term, spelling) in &overrides {
        assert!(
            *term == root || !names(spelling, "m"),
            "descendant spelling `{spelling}` names the macro: {overrides:?}"
        );
    }
}

/// Negative twin: without a macro the same descendant keeps its spelling.
#[test]
fn a_descendant_spelling_without_a_macro_is_still_recorded() {
    let (_, overrides) = collected_overrides(
        "(declare-const x Int)(declare-const r Bool)",
        "(or r (not (>= x 3)))",
    );
    assert!(
        overrides
            .values()
            .any(|spelling| spelling == "(not (>= x 3))"),
        "{overrides:?}"
    );
}

/// A descendant that folded onto ONE OF ITS OWN OPERANDS records no spelling.
/// `(and true (not (<= a b)))` interns as `(not (<= a b))`; an entry keyed on
/// that term re-spelled every occurrence of it — including the one inside the
/// recorded spelling — so the raw re-interned root of
/// `(and (<= a b) (and true (not (<= a b))))` printed as
/// `(and (<= a b) (and true (and true (not (<= a b)))))`, the complement
/// rescue refused its own candidate, and a correct `unsat` was withheld as
/// `unknown (incomplete self-check-rejected)` (Trust, 2026-10-06).
#[test]
fn a_descendant_folded_onto_its_own_operand_records_no_spelling() {
    let script = "(declare-const a Int)(declare-const b Int)(declare-const p Bool)";
    for assertion in [
        "(and (<= a b) (and true (not (<= a b))))",
        "(and (<= a b) (and true (and true (not (<= a b)))))",
        "(or p (and true (not (<= a b))))",
        "(or p (or false (not (<= a b))))",
        "(or p (and (not (<= a b)) (not (<= a b))))",
    ] {
        let (_, overrides) = collected_overrides(script, assertion);
        for spelling in overrides.values() {
            assert!(
                !spelling.starts_with("(and true") && !spelling.starts_with("(or false"),
                "{assertion}: a fold onto an operand recorded `{spelling}`: {overrides:?}"
            );
            assert_ne!(
                spelling, "(and (not (<= a b)) (not (<= a b)))",
                "{assertion}: an idempotent fold recorded its spelling: {overrides:?}"
            );
        }
    }
}

/// Negative twin: a genuine re-spelling — no operand elaborates to the whole
/// canonical term — keeps its entry, exactly as before.
#[test]
fn a_descendant_respelled_without_folding_keeps_its_spelling() {
    let (_, overrides) = collected_overrides(
        "(declare-const x Int)(declare-const r Bool)",
        "(or r (and true (>= x 3)))",
    );
    assert!(
        overrides.values().any(|spelling| spelling == "(>= x 3)"),
        "{overrides:?}"
    );
    assert!(
        !overrides
            .values()
            .any(|spelling| spelling == "(and true (>= x 3))"),
        "{overrides:?}"
    );
}

/// The single-buffer renderer spells every constructor exactly as the
/// recursive `format!` renderer it replaced did.
#[test]
fn buffered_renderer_spells_every_constructor_as_authored() {
    let cases = [
        "(and p (not q) (=> p q))",
        "(= ((_ extract 7 0) x) ((_ zero_extend 4) ((_ extract 3 0) x)))",
        "(= ((as const (Array Int Int)) 0) a)",
        "(let ((a (+ x 1)) (b 2)) (> a b))",
        "(forall ((x Int) (y Real)) (exists ((z Int)) (< x z)))",
        "(match l ((nil false) ((cons h t) true) (w true)))",
        "(! (> x 0) :named n)",
        "(distinct |a b| \"s\" #x0f #b01 1.5)",
    ];
    for source in cases {
        let commands = ay_frontend::parse(&format!("(assert {source})")).expect("fixture parses");
        let ay_frontend::Command::Assert(term) = &commands[0] else {
            panic!("fixture must be an assertion")
        };
        assert_eq!(format_authored_frontend_term(term), source);
    }
    // Stripping annotations drops the `!` wrapper, at any depth.
    let commands =
        ay_frontend::parse("(assert (and (! p :named a) (not (! q :named b))))").expect("parses");
    let ay_frontend::Command::Assert(term) = &commands[0] else {
        panic!("fixture must be an assertion")
    };
    assert_eq!(format_frontend_term(term), "(and p (not q))");
    assert_eq!(
        format_authored_frontend_term(term),
        "(and (! p :named a) (not (! q :named b)))"
    );
}

// Keep these tests in this namespace while bounding the physical source file.
include!("proof_surface_syntax_quantifier_tests.rs");
