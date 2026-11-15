// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::{
    try_export_alethe_with_problem_scope_and_overrides,
    try_export_alethe_with_problem_scope_overrides_and_budget_to, AletheStreamError,
};
use ay_core::kani_compat::DetHashMap;
use ay_core::{DatatypeConstructor, DatatypeField, DatatypeSort};

fn bv4_bool_array() -> Sort {
    Sort::array(Sort::bitvec(4), Sort::Bool)
}

/// A one-step proof: a theory lemma (printed `hole`) whose single literal is
/// `literal`, exported against `problem`.
fn export_lemma(
    terms: &TermStore,
    literal: TermId,
    problem: &[TermId],
    overrides: Option<&DetHashMap<TermId, String>>,
) -> Result<String, AlethePrintError> {
    let mut proof = Proof::new();
    proof.add_theory_lemma("ARRAYS", vec![literal]);
    try_export_alethe_with_problem_scope_and_overrides(&proof, terms, problem, overrides)
}

fn assert_declines_naming(result: Result<String, AlethePrintError>, name: &str) {
    match result {
        Err(AlethePrintError::UndeclarableProofSymbols { count, names }) => {
            assert_eq!(count, 1, "{names}");
            assert_eq!(names, name);
        }
        Err(other) => panic!("expected UndeclarableProofSymbols naming {name}, got {other}"),
        Ok(document) => panic!("a document spelling `{name}` was written:\n{document}"),
    }
}

/// The reproducer's shape: the array-default axiom
/// `(not (default (store ((as const ..) false) #x1 true)))` printed as a
/// `hole`. Before the fix the export wrote it and pinned Carcara answered
/// `invalid` (`identifier 'default' is not defined`).
#[test]
fn array_default_head_declines_the_export() {
    let mut terms = TermStore::new();
    let ff = terms.mk_bool(false);
    let tt = terms.mk_bool(true);
    let base = terms.mk_const_array(Sort::bitvec(4), ff);
    let one = terms.mk_bitvec(1u8.into(), 4);
    let stored = terms.mk_store(base, one, tt);
    let default = terms.mk_array_default(stored);
    assert_eq!(terms.get_array_default(default), Some(stored));
    let not_default = terms.mk_not(default);
    let c = terms.mk_var("c", bv4_bool_array());
    let problem = terms.mk_eq(c, stored);

    assert_declines_naming(
        export_lemma(&terms, not_default, &[problem], None),
        "default",
    );
}

/// Negative twin over the class, not the one symbol: every AY-internal head
/// the problem cannot declare declines, whatever minted it.
#[test]
fn every_internal_application_head_declines_the_export() {
    for head in [
        "__ay_array_default_diag!7",
        "!ay.array-ext!0",
        "map[f]",
        "lambda-array",
        "as-array",
        "bv2nat",
        "rem",
    ] {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::bitvec(4));
        let y = terms.mk_var("y", Sort::bitvec(4));
        let applied = terms.mk_app(Symbol::named(head), vec![x], Sort::bitvec(4));
        let literal = terms.mk_eq(applied, x);
        let problem = terms.mk_eq(x, y);
        assert_declines_naming(export_lemma(&terms, literal, &[problem], None), head);
    }
    // An indexed head outside pinned Carcara's indexed operators, too.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let applied = terms.mk_app(Symbol::indexed("int2bv", vec![4]), vec![x], Sort::bitvec(4));
    let y = terms.mk_var("y", Sort::bitvec(4));
    let literal = terms.mk_eq(applied, y);
    let z = terms.mk_var("z", Sort::bitvec(4));
    let w = terms.mk_var("w", Sort::Int);
    let problem = [terms.mk_eq(y, z), terms.mk_eq(x, w)];
    assert_declines_naming(export_lemma(&terms, literal, &problem, None), "int2bv");
}

/// An internal namespace is refused even when the problem's own assertions
/// apply it: `__ay_overload_N` stands in AY's terms for a selector the problem
/// file spells differently, so the checker cannot resolve it either.
#[test]
fn internal_namespace_head_declines_even_when_the_problem_applies_it() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let applied = terms.mk_app(Symbol::named("__ay_overload_1"), vec![x], Sort::Int);
    let literal = terms.mk_eq(applied, x);
    let problem = terms.mk_eq(applied, x);
    assert_declines_naming(
        export_lemma(&terms, literal, &[problem], None),
        "__ay_overload_1",
    );

    // A NULLARY member identity is a zero-argument application, printed
    // bare: a datatype declared again after a `pop` gives its constructors
    // such identities, and the problem's assertions mention them.
    let mut terms = TermStore::new();
    let v = terms.mk_var("v", Sort::Int);
    let constant = terms.mk_app(Symbol::named("__ay_overload_0"), vec![], Sort::Int);
    let literal = terms.mk_eq(v, constant);
    let problem = terms.mk_not(literal);
    assert_declines_naming(
        export_lemma(&terms, literal, &[problem], None),
        "__ay_overload_0",
    );
}

/// Positive twins: heads the checker resolves are not candidates.
#[test]
fn resolvable_heads_export() {
    let mut terms = TermStore::new();
    // A function the problem applies (its `declare-fun` is what the checker
    // reads), a pinned-Carcara operator, and a printable constant array.
    let x = terms.mk_var("x", Sort::bitvec(4));
    let f_x = terms.mk_app(Symbol::named("f"), vec![x], Sort::bitvec(4));
    let arr = terms.mk_var("arr", bv4_bool_array());
    let brr = terms.mk_var("brr", bv4_bool_array());
    let problem = [terms.mk_eq(f_x, x), terms.mk_eq(arr, brr)];
    let sum = terms.mk_app(Symbol::named("bvadd"), vec![f_x, x], Sort::bitvec(4));
    let sum_eq = terms.mk_eq(sum, x);
    let ff = terms.mk_bool(false);
    let base = terms.mk_const_array(Sort::bitvec(4), ff);
    let constant = terms.mk_eq(arr, base);
    let literal = terms.mk_or(vec![constant, sum_eq]);
    let document = export_lemma(&terms, literal, &problem, None).expect("resolvable heads");
    assert!(document.contains("(as const"), "{document}");
    assert!(!document.contains("const-array"), "{document}");

    // A selector and a constructor the problem's datatype declares, though
    // no assertion applies them.
    let pair = Sort::Datatype(DatatypeSort::new(
        "Pair",
        vec![DatatypeConstructor::new(
            "mk",
            vec![
                DatatypeField::new("fst", Sort::Int),
                DatatypeField::new("snd", Sort::Int),
            ],
        )],
    ));
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", pair.clone());
    let a = terms.mk_var("a", Sort::Int);
    let fst = terms.mk_app(Symbol::named("fst"), vec![p], Sort::Int);
    let built = terms.mk_app(Symbol::named("mk"), vec![a, a], pair.clone());
    let fst_eq = terms.mk_eq(fst, a);
    let built_eq = terms.mk_eq(built, p);
    let literal = terms.mk_or(vec![fst_eq, built_eq]);
    let q = terms.mk_var("q", pair);
    let b = terms.mk_var("b", Sort::Int);
    let problem = [terms.mk_eq(p, q), terms.mk_eq(a, b)];
    let document = export_lemma(&terms, literal, &problem, None).expect("datatype members");
    assert!(document.contains("(fst p)"), "{document}");
}

/// The guard reads the SHIPPED bytes: an internal head every occurrence of
/// which a rendering channel re-spells never reaches the document, so it
/// refuses nothing.
#[test]
fn internal_head_hidden_by_a_rendering_channel_exports() {
    let mut terms = TermStore::new();
    let ff = terms.mk_bool(false);
    let base = terms.mk_const_array(Sort::bitvec(4), ff);
    let default = terms.mk_array_default(base);
    // `mk_array_default` folds a constant array's default to its value.
    assert_eq!(default, ff);
    let a = terms.mk_var("a", bv4_bool_array());
    let default_a = terms.mk_array_default(a);
    let p = terms.mk_var("p", Sort::Bool);
    let literal = terms.mk_eq(default_a, p);
    let b = terms.mk_var("b", bv4_bool_array());
    let problem = [terms.mk_eq(a, b), p];
    let mut overrides = DetHashMap::default();
    overrides.insert(default_a, "p".to_string());
    let document = export_lemma(&terms, literal, &problem, Some(&overrides))
        .expect("the internal head never ships");
    assert!(!document.contains("default"), "{document}");

    // Without the channel it ships, and the export declines.
    assert_declines_naming(export_lemma(&terms, literal, &problem, None), "default");
}

/// The streaming export the CLI writes `<input>.alethe` through declines the
/// same way, so its caller discards the temporary file.
#[test]
fn streaming_export_declines_on_an_internal_head() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", bv4_bool_array());
    let default_a = terms.mk_array_default(a);
    let b = terms.mk_var("b", bv4_bool_array());
    let problem = terms.mk_eq(a, b);
    let mut proof = Proof::new();
    proof.add_theory_lemma("ARRAYS", vec![default_a]);
    let mut sink: Vec<u8> = Vec::new();
    let error = try_export_alethe_with_problem_scope_overrides_and_budget_to(
        &mut sink,
        &proof,
        &terms,
        &[problem],
        None,
        None,
    )
    .expect_err("`default` has no declaration the checker can read");
    assert!(
        matches!(
            error,
            AletheStreamError::Print(AlethePrintError::UndeclarableProofSymbols { .. })
        ),
        "{error}"
    );
}

/// The frontend's identity of a parametric-instance member (`member@D!{T}`,
/// `mangle_member`) is AY's own: no problem file declares it, even when the
/// problem's assertions apply it, so a step that prints it raw declines.
/// MEASURED before this rule: `(|val@Opt!{Int}| x)` in a `hole` step,
/// `carcara_surface=supported`, pinned Carcara `invalid`.
#[test]
fn parametric_instance_member_declines_even_when_the_problem_applies_it() {
    let opt = Sort::Datatype(DatatypeSort::new(
        "Opt!{Int}",
        vec![
            DatatypeConstructor::new("none@Opt!{Int}", vec![]),
            DatatypeConstructor::new(
                "some@Opt!{Int}",
                vec![DatatypeField::new("val@Opt!{Int}", Sort::Int)],
            ),
        ],
    ));
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", opt.clone());
    let a = terms.mk_var("a", Sort::Int);
    let val_x = terms.mk_app(Symbol::named("val@Opt!{Int}"), vec![x], Sort::Int);
    let selected = terms.mk_eq(a, val_x);
    let is_some = terms.mk_app(Symbol::named("is-some@Opt!{Int}"), vec![x], Sort::Bool);
    let none = terms.mk_var("none@Opt!{Int}", opt);
    let is_none = terms.mk_eq(x, none);
    // The problem applies the selector and the tester and mentions the
    // nullary constructor, in AY's spelling.
    let problem = [selected, is_some, is_none];
    assert_declines_naming(
        export_lemma(&terms, selected, &problem, None),
        "val@Opt!{Int}",
    );
    assert_declines_naming(
        export_lemma(&terms, is_some, &problem, None),
        "some@Opt!{Int}",
    );
    assert_declines_naming(
        export_lemma(&terms, is_none, &problem, None),
        "none@Opt!{Int}",
    );

    // Positive twin: a surface channel that respells every occurrence ships
    // no mangled identity, and the export goes through.
    let mut overrides = DetHashMap::default();
    overrides.insert(val_x, "(val x)".to_string());
    let document = export_lemma(&terms, selected, &problem, Some(&overrides))
        .expect("the mangled identity never ships");
    assert!(!document.contains('@'), "{document}");
}

/// A SORT identity of AY's own declines too: the printer writes a binder's
/// sort by its name. MEASURED before this rule: an inline Skolem
/// `(choice ((x |Opt!{Int}|)) ..)` and `(choice ((x __ay_datatype_sort_0))
/// ..)`, each disclosed `carcara_surface=supported` and `invalid` to pinned
/// Carcara (`sort '..' is not defined`).
#[test]
fn internal_sort_identity_declines_the_export() {
    let opt = Sort::Datatype(DatatypeSort::new(
        "Opt!{Int}",
        vec![
            DatatypeConstructor::new("none@Opt!{Int}", vec![]),
            DatatypeConstructor::new(
                "some@Opt!{Int}",
                vec![DatatypeField::new("val@Opt!{Int}", Sort::Int)],
            ),
        ],
    ));
    let redeclared = |name: &str| Sort::Uninterpreted(name.to_string());
    for (sort, name) in [
        (opt.clone(), "Opt!{Int}"),
        (redeclared("__ay_datatype_sort_0"), "__ay_datatype_sort_0"),
        (
            Sort::array(Sort::Int, redeclared("__ay_datatype_sort_1")),
            "__ay_datatype_sort_1",
        ),
    ] {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", sort.clone());
        let p_x = terms.mk_app(Symbol::named("P"), vec![x], Sort::Bool);
        let forall = terms.mk_forall(vec![("x".to_string(), sort)], p_x);
        let literal = terms.mk_not(forall);
        assert_declines_naming(export_lemma(&terms, literal, &[forall], None), name);
    }

    // Positive twins: a sort the problem declares exports, and so does an
    // internal one every occurrence of which a surface channel re-spells.
    let mut terms = TermStore::new();
    let user = redeclared("U");
    let x = terms.mk_var("x", user.clone());
    let p_x = terms.mk_app(Symbol::named("P"), vec![x], Sort::Bool);
    let forall = terms.mk_forall(vec![("x".to_string(), user)], p_x);
    let literal = terms.mk_not(forall);
    let document = export_lemma(&terms, literal, &[forall], None).expect("a declared sort");
    assert!(document.contains("((x U))"), "{document}");

    let mut terms = TermStore::new();
    let x = terms.mk_var("x", opt.clone());
    let p_x = terms.mk_app(Symbol::named("P"), vec![x], Sort::Bool);
    let forall = terms.mk_forall(vec![("x".to_string(), opt)], p_x);
    let literal = terms.mk_not(forall);
    let mut overrides = DetHashMap::default();
    overrides.insert(forall, "(forall ((x (Opt Int))) (P x))".to_string());
    let document = export_lemma(&terms, literal, &[forall], Some(&overrides))
        .expect("the internal sort never ships");
    assert!(!document.contains("!{"), "{document}");
}

/// This crate restates AY's internal namespaces; they must not drift from
/// the frontend's single source of truth.
#[test]
fn internal_namespaces_agree_with_the_frontend() {
    for name in [
        "__ay_overload_1",
        "__ay_",
        "!ay.array-ext!0",
        "map[f]",
        "map[]",
        "map[f",
        "mapf]",
        "default",
        "f",
        "_ay_x",
        "ay.x",
    ] {
        assert_eq!(
            is_internal_namespace_name(name),
            ay_frontend::is_internal_namespace_name(name),
            "{name}"
        );
    }
    for namespace in ay_frontend::INTERNAL_NAMESPACES {
        let sample = format!("{}x{}", namespace.prefix, namespace.suffix);
        assert!(is_internal_namespace_name(&sample), "{sample}");
    }
}

fn float64() -> Sort {
    Sort::FloatingPoint(11, 53)
}

/// The FloatingPoint theory declares its own symbols, so a proof over FP
/// sorts that applies one exports, and the surface verdict discloses it
/// `unsupported`. MEASURED before this rule: the refutation of
/// `(forall ((q (_ FloatingPoint 11 53))) (fp.isNaN q))` instantiates the
/// quantifier at `(_ +zero 11 53)` and was declined as free in `+zero`,
/// though AY's strict checker accepted it (owner decision D7: export it,
/// disclosed `carcara_surface=unsupported`).
#[test]
fn floating_point_theory_heads_export_over_floating_point_sorts() {
    let mut terms = TermStore::new();
    let q = terms.mk_var("q", float64());
    let is_nan_q = terms.mk_app(Symbol::named("fp.isNaN"), vec![q], Sort::Bool);
    let forall = terms.mk_forall(vec![("q".to_string(), float64())], is_nan_q);
    let zero = terms.mk_app(Symbol::indexed("+zero", vec![11, 53]), vec![], float64());
    let is_nan_zero = terms.mk_app(Symbol::named("fp.isNaN"), vec![zero], Sort::Bool);
    let literal = terms.mk_not(is_nan_zero);
    let document = export_lemma(&terms, literal, &[forall], None).expect("theory heads resolve");
    assert!(
        document.contains("(fp.isNaN (_ +zero 11 53))"),
        "{document}"
    );
    let mut proof = Proof::new();
    proof.add_theory_lemma("ARRAYS", vec![literal]);
    assert!(
        !crate::carcara_proof_surface(&proof, &terms, None).is_supported(),
        "a FloatingPoint document is disclosed unsupported"
    );

    // The theory's heads the problem never applies: a rounding mode and an
    // operator over it, and an indexed conversion.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", float64());
    let y = terms.mk_var("y", float64());
    let r = terms.mk_var("r", Sort::Real);
    let s = terms.mk_var("s", Sort::Real);
    let problem = [
        terms.mk_app(Symbol::named("fp.lt"), vec![x, y], Sort::Bool),
        terms.mk_eq(r, s),
    ];
    let rne = terms.mk_app(
        Symbol::named("RNE"),
        vec![],
        Sort::Uninterpreted("RoundingMode".to_string()),
    );
    let sum = terms.mk_app(Symbol::named("fp.add"), vec![rne, x, y], float64());
    let converted = terms.mk_app(
        Symbol::indexed("to_fp", vec![11, 53]),
        vec![rne, r],
        float64(),
    );
    let literal = terms.mk_app(Symbol::named("fp.eq"), vec![sum, converted], Sort::Bool);
    let document = export_lemma(&terms, literal, &problem, None).expect("theory heads resolve");
    assert!(document.contains("(fp.add RNE x y)"), "{document}");
    assert!(document.contains("((_ to_fp 11 53) RNE r)"), "{document}");
}

/// Negative twins: the FloatingPoint rule is the theory's vocabulary in an FP
/// proof, nothing wider. A rounding-mode constant in a proof with no
/// FloatingPoint-sorted term still declines (its `RoundingMode` sort is not
/// one the surface verdict flags, so accepting it could put `supported`
/// beside a document pinned Carcara cannot parse), and so does a head of
/// AY's own, or a z3 extension, in an FP proof.
#[test]
fn floating_point_rule_is_the_theory_in_a_floating_point_proof() {
    let rounding_mode = Sort::Uninterpreted("RoundingMode".to_string());
    let mut terms = TermStore::new();
    let rm = terms.mk_var("rm", rounding_mode.clone());
    let other = terms.mk_var("other", rounding_mode.clone());
    let rtz = terms.mk_app(Symbol::named("RTZ"), vec![], rounding_mode);
    let literal = terms.mk_eq(rm, rtz);
    let problem = terms.mk_eq(rm, other);
    assert_declines_naming(export_lemma(&terms, literal, &[problem], None), "RTZ");

    for head in ["__ay_fp_unpack!3", "fp.to_ieee_bv"] {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", float64());
        let b = terms.mk_var("b", Sort::bitvec(64));
        let c = terms.mk_var("c", Sort::bitvec(64));
        let applied = terms.mk_app(Symbol::named(head), vec![x], Sort::bitvec(64));
        let literal = terms.mk_eq(applied, b);
        let is_nan = terms.mk_app(Symbol::named("fp.isNaN"), vec![x], Sort::Bool);
        let problem = [is_nan, terms.mk_eq(b, c)];
        assert_declines_naming(export_lemma(&terms, literal, &problem, None), head);
    }
}

/// Every symbol the FloatingPoint rule accepts is one the frontend reserves
/// for the theory (so no problem declares it as its own), or one of the five
/// indexed constants, which no declaration can spell.
#[test]
fn floating_point_theory_heads_are_the_frontends_reserved_names() {
    for name in FLOATING_POINT_THEORY_OPERATORS {
        assert!(ay_frontend::is_reserved_op_name(name), "{name}");
    }
    for name in FLOATING_POINT_THEORY_INDEXED {
        assert!(
            ay_frontend::is_reserved_op_name(name)
                || ["+zero", "-zero", "+oo", "-oo", "NaN"].contains(name),
            "{name}"
        );
    }
}

#[path = "application_heads_tests/complex.rs"]
mod complex;
