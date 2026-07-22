// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model-Validation printer package tests (#mv-abstract-value-ascription,
//! #mv-defined-fun-emit, #mv-total-selectors, #mv-internal-symbol-suppression).
//!
//! The SMT-COMP Model-Validation track feeds `(get-model)` output to a strict
//! validator (Dolmen). These tests pin the printer properties that validator
//! requires: the legacy `(model ...)` wrapper, sort-ascribed abstract values,
//! no re-emission of problem-defined symbols, no leakage of solver-internal
//! symbols, and total selector interpretations for datatype models.

use crate::Executor;
use ay_frontend::parse;

fn run(input: &str) -> Vec<String> {
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    exec.execute_all(&commands).unwrap()
}

/// Every `@`-prefixed abstract value in the model must be sort-ascribed:
/// a bare `@U!N` is an unbound identifier to a model validator.
fn assert_abstract_values_ascribed(model: &str) {
    let bytes = model.as_bytes();
    for (i, _) in model.match_indices('@') {
        // `@p0` selector-parameter tokens are definition binders, not values.
        if model[i..].starts_with("@p0") {
            continue;
        }
        assert!(
            i >= 4 && &bytes[i - 4..i] == b"(as ",
            "bare abstract value at byte {i} in model:\n{model}"
        );
    }
}

#[test]
fn mv_abstract_values_sort_ascribed() {
    let outputs = run(r#"
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-const a U)
        (declare-const b U)
        (declare-fun f (U) U)
        (assert (distinct a b))
        (assert (= (f a) b))
        (check-sat)
        (get-model)
    "#);
    assert_eq!(outputs[0], "sat");
    let model = &outputs[1];
    // Legacy `(model ...)` wrapper (accepted by the 2025 validator grammar).
    assert!(model.starts_with("(model"), "wrapper missing:\n{model}");
    assert!(
        model.trim_end().ends_with(')'),
        "wrapper unclosed:\n{model}"
    );
    // The constants have abstract values; every one must be `(as @… U)`.
    assert!(
        model.contains("(as @"),
        "expected sort-ascribed abstract values:\n{model}"
    );
    assert_abstract_values_ascribed(model);
    // The get-model response grammar (Dolmen: `SAT OPEN MODEL? definition*
    // CLOSE`) admits ONLY define-fun forms: a `(declare-fun @U!n () U)`
    // universe header makes the whole model unparseable (E:parsing-error —
    // the QF_UFDT stream_processor ModelParsingError class). Abstract values
    // are self-contained per SMT-LIB 2.7 and need no declaration.
    assert!(
        !model.contains("(declare-fun"),
        "declare-fun in a get-model response is unparseable:\n{model}"
    );
}

#[test]
fn mv_no_problem_defined_symbol_reemission() {
    // QF_LRA blending/12.smt2 shape: problem-defined min/max drew a definition
    // conflict AND printed WRONG bodies (0.0) fabricated by the
    // unconstrained-function completion sweep (#mv-defined-fun-emit).
    let outputs = run(r#"
        (set-logic QF_LRA)
        (define-fun min ((x Real) (y Real)) Real (ite (<= x y) x y))
        (define-fun max ((x Real) (y Real)) Real (ite (<= x y) y x))
        (define-fun half () Real 0.5)
        (declare-const p Real)
        (declare-const q Real)
        (assert (= (min p q) 1.0))
        (assert (>= (max p q) 2.0))
        (assert (> p half))
        (check-sat)
        (get-model)
    "#);
    assert_eq!(outputs[0], "sat");
    let model = &outputs[1];
    assert!(model.starts_with("(model"));
    assert!(
        !model.contains("define-fun min") && !model.contains("define-fun max"),
        "problem-defined function re-emitted:\n{model}"
    );
    assert!(
        !model.contains("define-fun half"),
        "problem-defined constant re-emitted:\n{model}"
    );
    // User-DECLARED symbols must still be emitted.
    assert!(
        model.contains("define-fun p () Real"),
        "p missing:\n{model}"
    );
    assert!(
        model.contains("define-fun q () Real"),
        "q missing:\n{model}"
    );
}

#[test]
fn mv_total_selector_definitions() {
    let outputs = run(r#"
        (set-logic QF_DT)
        (declare-datatypes ((nat 0) (list 0))
          (((succ (pred nat)) (zero))
           ((cons (car nat) (cdr list)) (null))))
        (declare-const x nat)
        (declare-const l list)
        (assert (= x (succ zero)))
        (assert ((_ is cons) l))
        (check-sat)
        (get-model)
    "#);
    assert_eq!(outputs[0], "sat");
    let model = &outputs[1];
    // Every selector of every datatype gets a TOTAL definition whose
    // right-constructor arm defers to the builtin selector.
    assert!(
        model.contains("(define-fun pred ((@p0 nat)) nat (ite ((_ is succ) @p0) (pred @p0)"),
        "pred totalization missing:\n{model}"
    );
    assert!(
        model.contains("(define-fun car ((@p0 list)) nat (ite ((_ is cons) @p0) (car @p0)"),
        "car totalization missing:\n{model}"
    );
    assert!(
        model.contains("(define-fun cdr ((@p0 list)) list (ite ((_ is cons) @p0) (cdr @p0)"),
        "cdr totalization missing:\n{model}"
    );
    // User constants still print as constructor values.
    assert!(model.contains("define-fun x () nat"), "x missing:\n{model}");
    assert!(
        model.contains("define-fun l () list"),
        "l missing:\n{model}"
    );
    assert_abstract_values_ascribed(model);
}

#[test]
fn mv_total_selector_committed_wrong_ctor_case() {
    // The internal model commits `(pred zero) = succ zero` (the gate checked
    // that value); the printed totalization must reproduce it on the
    // wrong-constructor arm, not paper over it with the canonical default.
    let outputs = run(r#"
        (set-logic QF_DT)
        (declare-datatypes ((nat 0))
          (((succ (pred nat)) (zero))))
        (declare-const x nat)
        (assert (= x (pred zero)))
        (assert (= x (succ zero)))
        (check-sat)
        (get-model)
    "#);
    assert_eq!(outputs[0], "sat");
    let model = &outputs[1];
    let pred_def = model
        .lines()
        .find(|l| l.contains("(define-fun pred "))
        .unwrap_or_else(|| panic!("pred totalization missing:\n{model}"));
    assert!(
        pred_def.contains("(ite (= @p0 zero) (succ zero)"),
        "committed wrong-constructor case missing from pred:\n{pred_def}"
    );
}

#[test]
fn mv_internal_field_vars_suppressed_user_bang_symbols_kept() {
    // Single-constructor elimination introduces internal `r!fst`/`r!snd`
    // field constants: they must NOT print (the validator stops reading the
    // model at the first undeclared name). A user-DECLARED symbol whose name
    // contains `!` must still print (#mv-internal-symbol-suppression).
    let outputs = run(r#"
        (set-logic QF_DT)
        (declare-datatypes ((Rec 0)) (((mk (fst Int) (snd Int)))))
        (declare-const r Rec)
        (declare-const c!0 Int)
        (assert (= (fst r) 3))
        (assert (= c!0 5))
        (check-sat)
        (get-model)
    "#);
    assert_eq!(outputs[0], "sat");
    let model = &outputs[1];
    assert!(
        !model.contains("r!fst") && !model.contains("r!snd"),
        "solver-internal field constant leaked:\n{model}"
    );
    assert!(
        model.contains("define-fun r () Rec (mk 3"),
        "eliminated constant not reassembled:\n{model}"
    );
    assert!(
        model.contains("define-fun c!0 () Int 5"),
        "user-declared bang symbol suppressed:\n{model}"
    );
}

/// Extract the committed wrong-constructor case value for `(sel key)` from a
/// printed totalization line, e.g. `(ite (= @p0 zero) (succ zero) …)` -> the
/// `(succ zero)`.
fn committed_case_value<'m>(model: &'m str, sel: &str, key: &str) -> Option<&'m str> {
    let line = model
        .lines()
        .find(|l| l.contains(&format!("(define-fun {sel} ")))?;
    let marker = format!("(ite (= @p0 {key}) ");
    let start = line.find(&marker)? + marker.len();
    let rest = &line[start..];
    // The value is one balanced s-expression (or a bare symbol).
    let mut depth = 0i32;
    for (i, c) in rest.char_indices() {
        match c {
            '(' => depth += 1,
            ')' if depth > 0 => {
                depth -= 1;
                if depth == 0 {
                    return Some(&rest[..=i]);
                }
            }
            ' ' | ')' if depth == 0 => return Some(&rest[..i]),
            _ => {}
        }
    }
    None
}

/// INVARIANT (#mv-dt-single-source): a committed wrong-constructor case in a
/// printed total selector definition must be exactly what `(get-value)`
/// answers for the same application — one value engine, no divergence.
#[test]
fn mv_total_selector_committed_case_matches_get_value() {
    let outputs = run(r#"
        (set-logic QF_DT)
        (declare-datatypes ((nat 0))
          (((succ (pred nat)) (zero))))
        (declare-const x nat)
        (assert (= x (pred zero)))
        (assert (= x (succ zero)))
        (check-sat)
        (get-model)
        (get-value ((pred zero)))
    "#);
    assert_eq!(outputs[0], "sat");
    let model = &outputs[1];
    let case = committed_case_value(model, "pred", "zero")
        .unwrap_or_else(|| panic!("committed case for (pred zero) missing:\n{model}"));
    let gv = &outputs[2];
    assert!(
        gv.contains(case),
        "get-value diverged from the printed committed case: case={case} get-value={gv}"
    );
}

/// Stale same-point pin convergence (#dt-egraph-stale-point-repin, the
/// ModelPartialFunctionMissing class: v1l20077/v1l40058/v1l50075/v1l90007/
/// v2l90086/v3l80079). A wrong-constructor selector CHAIN — `(car null)` vs
/// `(car (cdr (cdr null)))` — can leave the inner application's class pinned
/// to a value from an earlier repair round (its argument first rendered as a
/// `cons`, then settled to `null`), producing two committed values for one
/// `(car null)` key. The repair loop must re-pin the stale same-point pin to
/// the canonical value instead of leaving the clash for the totalization
/// scan to drop `car`'s whole definition (a partial model to the validator).
#[test]
fn mv_stale_pin_chain_keeps_selector_definition() {
    let outputs = run(r#"
        (set-logic QF_DT)
        (declare-datatypes ((nat 0) (list 0) (tree 0))
          (((succ (pred nat)) (zero))
           ((cons (car tree) (cdr list)) (null))
           ((node (children list)) (leaf (data nat)))))
        (declare-fun x1 () nat)
        (declare-fun x2 () list)
        (declare-fun x3 () tree)
        (assert (and (= (data (car null)) x1)
                     (not (= (car (cons x3 (children (car (cdr (cdr null))))))
                             (leaf (pred (succ (succ (succ zero)))))))))
        (check-sat)
        (get-model)
        (get-value ((car null) (car (cdr (cdr null))) (cdr (cdr null))))
    "#);
    assert_eq!(outputs[0], "sat");
    let model = &outputs[1];
    // The `car` totalization must survive (it was dropped fail-closed on the
    // conflicting committed values before the stale-pin repair).
    let case = committed_case_value(model, "car", "null")
        .unwrap_or_else(|| panic!("car totalization missing or has no null case:\n{model}"));
    // Value-level selector congruence: when `(cdr (cdr null))` renders `null`
    // (today's assignment — a repair that SEPARATES the arguments instead
    // would also be a valid model), `(get-value)` must answer the SAME value
    // for both `car` applications, and it must be the printed committed case.
    let gv = &outputs[2];
    if gv.contains("((cdr (cdr null)) null)") {
        let occurrences = gv.matches(case).count();
        assert!(
            occurrences >= 2,
            "selector congruence broken: committed case {case} not shared by \
             both applications in get-value answer:\n{gv}"
        );
    }
}

/// Disequality collapse regression (M4 F1 / v1l40058 shape): an asserted
/// datatype disequality between a constant and a wrong-constructor selector
/// chain must NOT print both sides to the same fabricated default.
#[test]
fn mv_disequality_not_collapsed_by_defaults() {
    let outputs = run(r#"
        (set-logic QF_DT)
        (declare-datatypes ((nat 0) (list 0) (tree 0))
          (((succ (pred nat)) (zero))
           ((cons (car tree) (cdr list)) (null))
           ((node (children list)) (leaf (data nat)))))
        (declare-const x3 tree)
        (assert (not (= x3 (car (cdr null)))))
        (check-sat)
        (get-value (x3 (car (cdr null))))
    "#);
    assert_eq!(outputs[0], "sat");
    let gv = &outputs[1];
    // `(get-value)` answers `((term value) (term value))`; the two values must
    // differ or the asserted disequality is violated by the exhibited model.
    let inner = gv
        .trim()
        .strip_prefix('(')
        .and_then(|s| s.strip_suffix(')'))
        .unwrap_or(gv);
    let x3_val = inner
        .split("(car (cdr null))")
        .next()
        .map(str::trim)
        .unwrap_or("");
    assert!(!x3_val.is_empty(), "unexpected get-value shape: {gv}");
    let sel_val = inner
        .rsplit("(car (cdr null))")
        .next()
        .map(str::trim)
        .unwrap_or("");
    let x3_val = x3_val
        .trim_start_matches("(x3")
        .trim()
        .trim_end_matches(')')
        .trim();
    let sel_val = sel_val.trim().trim_end_matches(')').trim();
    assert!(
        x3_val != sel_val,
        "asserted-disequal terms print the same value {x3_val:?}:\n{gv}"
    );
}

/// Merged classes print identical values: an asserted equality between two
/// constants must yield byte-identical printed model values.
#[test]
fn mv_equal_classes_print_identical_values() {
    let outputs = run(r#"
        (set-logic QF_DT)
        (declare-datatypes ((nat 0))
          (((succ (pred nat)) (zero))))
        (declare-const a nat)
        (declare-const b nat)
        (assert (= a b))
        (assert (= a (succ zero)))
        (check-sat)
        (get-model)
    "#);
    assert_eq!(outputs[0], "sat");
    let model = &outputs[1];
    let val_of = |name: &str| {
        model
            .lines()
            .find(|l| l.contains(&format!("(define-fun {name} () nat ")))
            .map(|l| {
                l.trim()
                    .trim_start_matches(&format!("(define-fun {name} () nat "))
                    .trim_end_matches(')')
                    .trim()
                    .to_string()
            })
            .unwrap_or_else(|| panic!("{name} missing:\n{model}"))
    };
    assert_eq!(
        val_of("a"),
        val_of("b"),
        "merged constants diverge:\n{model}"
    );
}

/// M4 F2 fail-closed: a committed wrong-constructor case whose branch KEY
/// would contain an abstract `@` value cannot be represented — the selector's
/// total definition must be OMITTED (a partial model is at worst 0 points to
/// a validator), never emitted with the default arm silently overriding the
/// committed point (a voiding wrong model).
#[test]
fn mv_abstract_key_committed_case_drops_definition() {
    let outputs = run(r#"
        (set-logic QF_UFDT)
        (declare-sort U 0)
        (declare-datatypes ((T 0)) (((mkA (fa U)) (mkB (fb U)))))
        (declare-const t T)
        (declare-const u0 U)
        (declare-const u1 U)
        (assert (distinct u0 u1))
        (assert ((_ is mkB) t))
        (assert (= (fa t) u1))
        (check-sat)
        (get-model)
    "#);
    assert_eq!(outputs[0], "sat");
    let model = &outputs[1];
    if let Some(fa_def) = model.lines().find(|l| l.contains("(define-fun fa ")) {
        // If a total definition IS emitted, its committed case must be intact:
        // the branch key must not have been silently skipped into the default
        // arm. `t`'s printed value must appear as a branch key.
        let t_val = model
            .lines()
            .find(|l| l.contains("(define-fun t () T "))
            .map(|l| {
                l.trim()
                    .trim_start_matches("(define-fun t () T ")
                    .trim_end_matches(')')
                    .trim()
                    .to_string()
            })
            .unwrap_or_default();
        assert!(
            !t_val.is_empty() && fa_def.contains(&format!("(= @p0 {t_val})")),
            "fa emitted without the committed case for t={t_val}:\n{fa_def}\n{model}"
        );
    }
    // Otherwise: definition omitted — the fail-closed outcome (E:partial-dstr).
}

/// Stage-4 review F2 fail-closed: when the structural self-check fails and a
/// class pair still violates an asserted disequality, the poisoned classes'
/// constant `define-fun`s must be OMITTED — never delegated to the legacy
/// emitter, which re-derives the SAME collision (`c8-tester-distinct`:
/// `b = c = (s (s (s (s z))))` under `(distinct a b c)` → E:bad-model,
/// division-voiding). Whatever subset of constants prints must be pairwise
/// distinct; omission (a 0-point partial model) is the acceptable outcome.
#[test]
fn mv_poisoned_constant_collision_omitted_not_refabricated() {
    let outputs = run(r#"
        (set-logic QF_DT)
        (declare-datatypes ((N 0)) (((s (p N)) (z))))
        (declare-const a N)
        (declare-const b N)
        (declare-const c N)
        (assert ((_ is s) a))
        (assert ((_ is s) b))
        (assert ((_ is s) c))
        (assert (distinct a b c))
        (check-sat)
        (get-model)
    "#);
    assert_eq!(outputs[0], "sat");
    let model = &outputs[1];
    let val_of = |name: &str| {
        model
            .lines()
            .find(|l| l.contains(&format!("(define-fun {name} () N ")))
            .map(|l| {
                l.trim()
                    .trim_start_matches(&format!("(define-fun {name} () N "))
                    .trim_end_matches(')')
                    .trim()
                    .to_string()
            })
    };
    let printed: Vec<(&str, String)> = ["a", "b", "c"]
        .iter()
        .filter_map(|n| val_of(n).map(|v| (*n, v)))
        .collect();
    for i in 0..printed.len() {
        for j in (i + 1)..printed.len() {
            assert_ne!(
                printed[i].1, printed[j].1,
                "asserted-distinct constants {} and {} print the same value \
                 (the F2 voiding collision):\n{model}",
                printed[i].0, printed[j].0
            );
        }
    }
}

/// Stage-4 review F3: a UF function table over a selector-bearing datatype
/// must key its branches on the SAME single-source values the constants
/// print — abstract-element keys (`(as @N!k N)`) can never match the printed
/// constants under a validator, so every application falls to the default arm
/// and a satisfied disequality evaluates false (`c1-ufdt-f`: E:bad-model,
/// division-voiding). Either the table prints fully concrete (branch keys =
/// the printed constant values) or the definition is omitted (fail-closed
/// partial) — no abstract datatype element may survive in the model.
#[test]
fn mv_ufdt_table_keys_single_sourced_or_dropped() {
    let outputs = run(r#"
        (set-logic QF_UFDT)
        (declare-datatypes ((N 0)) (((s (p N)) (z))))
        (declare-fun f (N) N)
        (declare-const a N)
        (declare-const b N)
        (assert (not (= (f a) (f b))))
        (check-sat)
        (get-model)
    "#);
    assert_eq!(outputs[0], "sat");
    let model = &outputs[1];
    // No abstract datatype element and no unresolved placeholder anywhere:
    // the datatype sort N is selector-bearing, so every printed datatype
    // value must be a concrete constructor tree (`@p0` totalization binders
    // are definition parameters, not values, and remain legal).
    assert!(
        !model.contains("@N!") && !model.contains("@?"),
        "abstract datatype element survives in the printed model (F3):\n{model}"
    );
    // If the table printed, its branch keys must be the printed constants'
    // values, so the validator's lookup reproduces the internal model.
    if model.contains("(define-fun f ") {
        let val_of = |name: &str| {
            model
                .lines()
                .find(|l| l.contains(&format!("(define-fun {name} () N ")))
                .map(|l| {
                    l.trim()
                        .trim_start_matches(&format!("(define-fun {name} () N "))
                        .trim_end_matches(')')
                        .trim()
                        .to_string()
                })
        };
        if let (Some(a_val), Some(b_val)) = (val_of("a"), val_of("b")) {
            assert_ne!(
                a_val, b_val,
                "f(a) != f(b) forces distinct printed a, b:\n{model}"
            );
        }
    }
}

#[test]
fn mv_get_value_unaffected_by_internal_suppression() {
    // Suppression is print-only: `(get-value ...)` over eliminated-constant
    // selectors must still resolve.
    let outputs = run(r#"
        (set-logic QF_DT)
        (declare-datatypes ((Rec 0)) (((mk (fst Int) (snd Int)))))
        (declare-const r Rec)
        (assert (= (fst r) 3))
        (check-sat)
        (get-value ((fst r)))
    "#);
    assert_eq!(outputs[0], "sat");
    assert!(
        outputs[1].contains("3"),
        "get-value lost the field value: {}",
        outputs[1]
    );
}
