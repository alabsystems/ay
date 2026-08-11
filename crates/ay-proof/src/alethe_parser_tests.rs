// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the Alethe document parser and round-trip self-check.
//!
//! Two obligations, matching the two ways the gate can fail:
//!
//! * POSITIVE — every construct in the emission inventory (the 30 rules, the
//!   four commands, `let` / `choice` / quantifiers / testers / rationals, the
//!   real skolem symbol names, deep nesting, subproofs) must be ACCEPTED, or
//!   the gate is a false-reject machine and will be turned off.
//! * NEGATIVE — every parse-level rejection carcara makes must be REPRODUCED,
//!   or the gate is the false-accept machine we already have.

use super::*;

/// The problem the small fixtures are checked against.
const PROBLEM: &str = r"
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun p () Bool)
(declare-fun q () Bool)
(declare-fun a () U)
(declare-fun b () U)
(declare-fun P (U) Bool)
(declare-fun l () Int)
(declare-fun u () Int)
(assert p)
(assert (not p))
(check-sat)
";

fn scope() -> ProblemScope {
    ProblemScope::from_smtlib_source(PROBLEM)
}

fn accept(text: &str) -> AletheDocumentReport {
    match check_alethe_document(text, &scope()) {
        Ok(report) => report,
        Err(defect) => panic!("expected ACCEPT, got {defect}\n---\n{text}"),
    }
}

fn reject(text: &str) -> AletheDefect {
    match check_alethe_document(text, &scope()) {
        Ok(report) => panic!("expected REJECT, got ACCEPT {report:?}\n---\n{text}"),
        Err(defect) => defect,
    }
}

// -------------------------------------------------------------------------
// Problem scanner
// -------------------------------------------------------------------------

#[test]
fn problem_scanner_finds_declarations() {
    let scope = scope();
    assert!(scope.contains_symbol("p"));
    assert!(scope.contains_symbol("P"));
    assert!(scope.contains_sort("U"));
    assert!(!scope.contains_symbol("nosuchsym"));
}

#[test]
fn problem_scanner_finds_datatype_constructors_and_selectors() {
    let scope = ProblemScope::from_smtlib_source(
        "(declare-datatypes ((Lst 0)) (((nil) (cons (head Int) (tail Lst)))))\n\
         (declare-fun l () Lst)",
    );
    for name in ["nil", "cons", "head", "tail", "l"] {
        assert!(scope.contains_symbol(name), "missing {name}");
    }
    assert!(scope.contains_sort("Lst"));
}

#[test]
fn problem_scanner_handles_single_datatype_and_quoted_names() {
    let scope = ProblemScope::from_smtlib_source(
        "(declare-datatype Colour ((red) (green)))\n(declare-fun |weird sym| () Int)",
    );
    assert!(scope.contains_sort("Colour"));
    assert!(scope.contains_symbol("red"));
    assert!(scope.contains_symbol("weird sym"));
}

// -------------------------------------------------------------------------
// POSITIVE: everything the inventory says AY emits
// -------------------------------------------------------------------------

#[test]
fn accepts_minimal_resolution_proof() {
    let report = accept(
        "(assume a0 p)\n\
         (assume a1 (not p))\n\
         (step t0 (cl) :rule resolution :premises (a0 a1))\n",
    );
    assert_eq!(report.commands, 3);
    assert_eq!(report.steps, 1);
    assert_eq!(report.assumes, 2);
}

#[test]
fn accepts_proof_with_no_assumes() {
    // 15 of the 150 inventoried proofs contain no `assume` at all.
    accept("(step t0 (cl p) :rule hole)\n(step t1 (cl) :rule hole :premises (t0))\n");
}

#[test]
fn accepts_all_four_attribute_keywords_in_order() {
    accept(
        "(assume a0 p)\n\
         (anchor :step t5)\n\
         (assume t5.h1 p)\n\
         (step t5.t2 (cl p) :rule hole :premises (t5.h1))\n\
         (step t5 (cl (not p) p) :rule subproof :discharge (t5.h1))\n\
         (step t9 (cl) :rule hole :premises (a0 t5))\n",
    );
}

#[test]
fn accepts_la_generic_numeric_args() {
    // The single most common `:args` shape: 45,724 occurrences.
    accept(
        "(step t0 (cl (<= u (+ l (- 1)))) :rule hole)\n\
         (step t3 (cl (not (<= u (+ l (- 1))))) :rule la_generic :args (1 1 1))\n\
         (step t6 (cl) :rule th_resolution :premises (t0 t3))\n",
    );
}

#[test]
fn accepts_rational_and_decimal_args() {
    accept(
        "(step t0 (cl p) :rule hole)\n\
         (step t1 (cl (not p)) :rule la_generic :args (1 (/ 1.0 4.0) (/ 1.0 4.0)))\n\
         (step t2 (cl) :rule resolution :premises (t0 t1))\n",
    );
}

#[test]
fn accepts_bare_negative_numerals() {
    // carcara lexes `-3` and `-3.5` as literals (probes tm_bareneg,
    // tm_baregnegdec); a parser that lexed them as symbols would reject.
    accept(
        "(step t0 (cl p) :rule hole :args (-3 -3.5))\n\
         (step t1 (cl) :rule hole :premises (t0))\n",
    );
}

#[test]
fn accepts_let_choice_and_quantifiers() {
    accept(
        "(step t0 (cl (let ((v (+ l 1))) (<= v u))) :rule hole)\n\
         (step t1 (cl (forall ((x Int)) (<= x x))) :rule hole)\n\
         (step t2 (cl (exists ((x Int)) (<= x x))) :rule hole)\n\
         (step t3 (cl (P (choice ((x U)) (P x)))) :rule hole)\n\
         (step t4 (cl) :rule hole :premises (t0 t1 t2 t3))\n",
    );
}

#[test]
fn accepts_nested_let_bindings() {
    accept(
        "(step t0 (cl (let ((v1 l)) (let ((v2 (+ v1 1))) (<= v1 v2)))) :rule hole)\n\
         (step t1 (cl) :rule hole :premises (t0))\n",
    );
}

#[test]
fn accepts_datatype_tester_the_only_indexed_identifier_ay_emits() {
    let dt = ProblemScope::from_smtlib_source(
        "(declare-datatypes ((Lst 0)) (((nil) (cons (head Int) (tail Lst)))))\n\
         (declare-fun z () Lst)",
    );
    let text = "(step t0 (cl ((_ is cons) z)) :rule hole)\n\
                (step t1 (cl) :rule hole :premises (t0))\n";
    check_alethe_document(text, &dt).expect("tester must parse");
}

#[test]
fn accepts_ay_real_skolem_symbol_names_via_define_fun() {
    // `sk!?V_8_2_6`, `__ay_sk_x171_205!278`, `__ay_ext_diff!69` must lex.
    accept(
        "(define-fun sk!?V_8_2_6 () U (choice ((x U)) (P x)))\n\
         (define-fun __ay_sk_x171_205!278 () U (choice ((x U)) (P x)))\n\
         (define-fun __ay_ext_diff!69 () U (choice ((x U)) (P x)))\n\
         (step t0 (cl (P sk!?V_8_2_6) (P __ay_sk_x171_205!278) (P __ay_ext_diff!69)) :rule hole)\n\
         (step t1 (cl) :rule hole :premises (t0))\n",
    );
}

#[test]
fn accepts_define_fun_anywhere_including_after_steps() {
    // Probe `df_after_step` → valid.
    accept(
        "(step t0 (cl p) :rule hole)\n\
         (define-fun c () U a)\n\
         (step t1 (cl (P c)) :rule hole)\n\
         (step t2 (cl) :rule hole :premises (t0 t1))\n",
    );
}

#[test]
fn accepts_define_fun_with_arguments_and_chaining() {
    accept(
        "(define-fun Q ((x U)) Bool (P x))\n\
         (define-fun R ((x U)) Bool (Q x))\n\
         (step t0 (cl (R a)) :rule hole)\n\
         (step t1 (cl) :rule hole :premises (t0))\n",
    );
}

#[test]
fn accepts_quoted_symbols() {
    let s = ProblemScope::from_smtlib_source("(declare-fun |weird sym| () Bool)");
    let text = "(step t0 (cl |weird sym|) :rule hole)\n(step t1 (cl) :rule hole :premises (t0))\n";
    check_alethe_document(text, &s).expect("quoted symbols must lex");
}

#[test]
fn accepts_anchor_args_in_all_three_forms() {
    for args in [
        "((y Bool))",
        "((:= y p))",
        "((:= (y Bool) p))",
        "((:= (y Bool) p) (z Bool))",
    ] {
        accept(&format!(
            "(assume a0 p)\n\
             (anchor :step t5 :args {args})\n\
             (assume t5.h1 p)\n\
             (step t5.t2 (cl p) :rule hole :premises (t5.h1))\n\
             (step t5 (cl (not p) p) :rule subproof :discharge (t5.h1))\n\
             (step t9 (cl) :rule hole :premises (a0 t5))\n"
        ));
    }
}

#[test]
fn accepts_anchor_bound_variable_inside_the_subproof() {
    accept(
        "(assume a0 p)\n\
         (anchor :step t5 :args ((:= (y Bool) p)))\n\
         (assume t5.h1 y)\n\
         (step t5.t2 (cl y) :rule hole :premises (t5.h1))\n\
         (step t5 (cl (not p) p) :rule subproof :discharge (t5.h1))\n\
         (step t9 (cl) :rule hole :premises (a0 t5))\n",
    );
}

#[test]
fn accepts_nested_subproofs() {
    accept(
        "(assume a0 p)\n\
         (anchor :step t1)\n\
         (assume t1.h1 p)\n\
         (anchor :step t1.t1)\n\
         (assume t1.t1.h1 p)\n\
         (step t1.t1.s (cl p) :rule hole :premises (t1.t1.h1))\n\
         (step t1.t1 (cl (not p) p) :rule subproof :discharge (t1.t1.h1))\n\
         (step t1 (cl (not p) p) :rule subproof :discharge (t1.h1))\n\
         (step t9 (cl) :rule hole :premises (a0 t1))\n",
    );
}

#[test]
fn accepts_every_rule_ay_actually_emits() {
    // The 30 names measured across 2,243,957 emitted commands.
    const EMITTED: &[&str] = &[
        "resolution",
        "la_generic",
        "th_resolution",
        "hole",
        "and_pos",
        "or",
        "la_disequality",
        "eq_congruent",
        "eq_transitive",
        "or_pos",
        "contraction",
        "or_neg",
        "ite_pos1",
        "equiv_pos2",
        "lia_generic",
        "not_not",
        "ite_pos2",
        "cong",
        "trans",
        "subproof",
        "and_neg",
        "arrays_row",
        "symm",
        "arrays_idx",
        "reordering",
        "false",
        "ite_neg1",
        "not_symm",
        "equiv_neg1",
        "equiv_neg2",
    ];
    for rule in EMITTED {
        accept(&format!(
            "(step t0 (cl p) :rule {rule})\n(step t1 (cl) :rule hole :premises (t0))\n"
        ));
    }
}

#[test]
fn accepts_deep_nesting() {
    // The inventory measured paren depth 109.
    let mut term = "l".to_string();
    for _ in 0..150 {
        term = format!("(+ {term} 1)");
    }
    accept(&format!(
        "(step t0 (cl (<= {term} u)) :rule hole)\n(step t1 (cl) :rule hole :premises (t0))\n"
    ));
}

#[test]
fn accepts_premise_arity_up_to_seven() {
    let mut text = String::new();
    for i in 0..7 {
        text.push_str(&format!("(step s{i} (cl p) :rule hole)\n"));
    }
    text.push_str("(step t9 (cl) :rule hole :premises (s0 s1 s2 s3 s4 s5 s6))\n");
    accept(&text);
}

#[test]
fn accepts_comments_and_unsat_prefix() {
    accept(
        "unsat\n; a comment\n(assume a0 p)\n(step t0 (cl) :rule hole :premises (a0)) ; trailing\n",
    );
}

// -------------------------------------------------------------------------
// NEGATIVE: every parse-level rejection carcara makes
// -------------------------------------------------------------------------

#[test]
fn rejects_declare_fun_preamble_at_line_zero() {
    // THE defect: 22 of the 50 dangerous-cell instances, and 8 of the 150
    // inventoried proofs. carcara:
    //   parser error: unexpected token: 'declare-fun' (on line 0, column 1)
    let defect = reject(
        "(declare-fun sk!?V_6_10_12 () Int)\n\
         (step t0 (cl p) :rule hole)\n\
         (step t1 (cl) :rule hole :premises (t0))\n",
    );
    assert!(
        matches!(&defect, AletheDefect::DeclarationCommand { command, pos }
            if command == "declare-fun" && pos.line == 0 && pos.column == 1),
        "got {defect:?}"
    );
}

#[test]
fn rejects_declare_fun_mid_file() {
    let defect = reject(
        "(step t0 (cl p) :rule hole)\n\
         (declare-fun sk () Int)\n\
         (step t1 (cl) :rule hole :premises (t0))\n",
    );
    assert!(
        matches!(&defect, AletheDefect::DeclarationCommand { pos, .. } if pos.line == 1),
        "got {defect:?}"
    );
}

#[test]
fn rejects_every_declaration_command_form() {
    for command in [
        "(declare-const c Int)",
        "(declare-sort S 0)",
        "(declare-datatype D ((d)))",
        "(declare-datatypes ((D 0)) (((d))))",
        "(define-sort S () Int)",
        "(define-fun-rec f () Int 0)",
        "(define-const c Int 0)",
    ] {
        let defect = reject(&format!("{command}\n(step t0 (cl) :rule hole)\n"));
        assert_eq!(defect.tag(), "declaration-command", "for {command}");
    }
}

#[test]
fn rejects_non_proof_commands() {
    for command in [
        "(set-logic QF_UF)",
        "(assert p)",
        "(check-sat)",
        "(push 1)",
        "(set-info :status unsat)",
        "(set-option :x true)",
        "(exit)",
        "(get-proof)",
    ] {
        let defect = reject(&format!("{command}\n(step t0 (cl) :rule hole)\n"));
        assert_eq!(defect.tag(), "unknown-command", "for {command}");
    }
}

#[test]
fn rejects_undefined_symbol() {
    // carcara: identifier 'sk0' is not defined (probe sk_undeclared).
    let defect =
        reject("(step t0 (cl (P sk0)) :rule hole)\n(step t1 (cl) :rule hole :premises (t0))\n");
    assert!(
        matches!(&defect, AletheDefect::UndefinedSymbol { name, .. } if name == "sk0"),
        "got {defect:?}"
    );
}

#[test]
fn rejects_define_fun_used_before_definition() {
    // carcara: identifier 'c' is not defined (probe df_forward).
    let defect = reject(
        "(step t0 (cl (P c)) :rule hole)\n\
         (define-fun c () U a)\n\
         (step t1 (cl) :rule hole :premises (t0))\n",
    );
    assert_eq!(defect.tag(), "undefined-symbol");
}

#[test]
fn rejects_define_fun_with_undefined_body() {
    let defect = reject("(define-fun c () U nosuchsym)\n(step t0 (cl) :rule hole)\n");
    assert!(
        matches!(&defect, AletheDefect::UndefinedSymbol { name, .. } if name == "nosuchsym"),
        "got {defect:?}"
    );
}

#[test]
fn rejects_define_fun_arity_mismatch() {
    // Probe df_collide_arity: the proof definition SHADOWS the problem
    // declaration, so `(P a)` after `(define-fun P () Bool p)` is
    // `expected 0 arguments, got 1`.
    let defect = reject(
        "(define-fun P () Bool p)\n\
         (step t0 (cl (P a)) :rule hole)\n\
         (step t1 (cl) :rule hole :premises (t0))\n",
    );
    assert_eq!(defect.tag(), "unexpected-token");
}

#[test]
fn rejects_dangling_premise() {
    let defect = reject("(step t0 (cl) :rule hole :premises (nosuch))\n");
    assert!(
        matches!(&defect, AletheDefect::UndefinedStepId { id, .. } if id == "nosuch"),
        "got {defect:?}"
    );
}

#[test]
fn rejects_forward_premise() {
    // carcara resolves ids eagerly: a forward reference is not deferred.
    let defect = reject(
        "(step t1 (cl p) :rule hole :premises (t2))\n\
         (step t2 (cl p) :rule hole)\n\
         (step t3 (cl) :rule hole :premises (t1 t2))\n",
    );
    assert!(
        matches!(&defect, AletheDefect::UndefinedStepId { id, .. } if id == "t2"),
        "got {defect:?}"
    );
}

#[test]
fn rejects_self_premise() {
    let defect = reject("(step t1 (cl) :rule hole :premises (t1))\n");
    assert_eq!(defect.tag(), "undefined-step-id");
}

#[test]
fn rejects_duplicate_step_id() {
    let defect = reject(
        "(step t1 (cl p) :rule hole)\n\
         (step t1 (cl q) :rule hole)\n\
         (step t2 (cl) :rule hole :premises (t1))\n",
    );
    assert!(
        matches!(&defect, AletheDefect::DuplicateStepId { id, .. } if id == "t1"),
        "got {defect:?}"
    );
}

#[test]
fn rejects_step_reusing_an_assume_id() {
    // Assumes and steps share one namespace.
    let defect = reject("(assume a0 p)\n(step a0 (cl) :rule hole :premises (a0))\n");
    assert_eq!(defect.tag(), "duplicate-step-id");
}

#[test]
fn rejects_id_leaking_out_of_a_closed_subproof() {
    // Probe sp_leak: `t5.t2` is not defined after the subproof closes.
    let defect = reject(
        "(assume a0 p)\n\
         (anchor :step t5)\n\
         (assume t5.h1 p)\n\
         (step t5.t2 (cl p) :rule hole :premises (t5.h1))\n\
         (step t5 (cl (not p) p) :rule subproof :discharge (t5.h1))\n\
         (step t9 (cl) :rule hole :premises (a0 t5.t2))\n",
    );
    assert!(
        matches!(&defect, AletheDefect::UndefinedStepId { id, .. } if id == "t5.t2"),
        "got {defect:?}"
    );
}

#[test]
fn rejects_unknown_rule() {
    let defect = reject("(step t1 (cl) :rule ay_made_this_up)\n");
    assert!(
        matches!(&defect, AletheDefect::UnknownRule { rule, .. } if rule == "ay_made_this_up"),
        "got {defect:?}"
    );
}

#[test]
fn rejects_rules_that_always_degrade_to_hole() {
    // The 17 `AletheRule::name()` values that are never printable. If the
    // printer ever leaks one, carcara reports `unknown rule`.
    for rule in [
        "all_simplify",
        "arith_simplify",
        "array_ext_diff_intro",
        "extensionality",
        "read_over_write_pos",
        "trust",
    ] {
        let defect = reject(&format!("(step t1 (cl) :rule {rule})\n"));
        assert_eq!(defect.tag(), "unknown-rule", "for {rule}");
    }
}

#[test]
fn rejects_missing_rule_attribute() {
    let defect = reject("(step t1 (cl p))\n");
    assert_eq!(defect.tag(), "unexpected-token");
}

#[test]
fn rejects_missing_clause() {
    let defect = reject("(step t1 :rule hole)\n");
    assert_eq!(defect.tag(), "unexpected-token");
}

#[test]
fn rejects_clause_not_headed_by_cl() {
    // Probe cl_notcl: unexpected token 'or'.
    let defect = reject("(step t1 (or p (not p)) :rule hole)\n");
    assert!(
        matches!(&defect, AletheDefect::ClauseNotCl { found, .. } if found == "or"),
        "got {defect:?}"
    );
}

#[test]
fn rejects_assume_without_a_term() {
    let defect = reject("(assume a0)\n(step t0 (cl) :rule hole :premises (a0))\n");
    assert_eq!(defect.tag(), "unexpected-token");
}

#[test]
fn rejects_anchor_without_step() {
    let defect = reject("(anchor :args ((y Bool)))\n(step t0 (cl) :rule hole)\n");
    assert_eq!(defect.tag(), "unexpected-token");
}

#[test]
fn rejects_out_of_order_premises() {
    // STRICTER THAN CARCARA, deliberately. Probe silent_drop: carcara
    // discards a misordered `:premises` with NO diagnostic, so an undefined
    // premise id simply vanishes.
    let defect = reject("(step t1 (cl p) :premises (a0) :rule hole)\n(step t2 (cl) :rule hole)\n");
    assert!(
        matches!(&defect, AletheDefect::MisplacedAttribute { keyword, .. } if keyword == ":premises"),
        "got {defect:?}"
    );
}

#[test]
fn rejects_premises_after_args() {
    let defect = reject("(step t1 (cl p) :rule hole :args (1) :premises (t0))\n");
    assert_eq!(defect.tag(), "misplaced-attribute");
}

#[test]
fn rejects_unknown_attribute() {
    // STRICTER THAN CARCARA. Probe silent_garbage → `valid`.
    let defect = reject("(step t1 (cl) :rule hole :junk (((( nested )))))\n");
    assert!(
        matches!(&defect, AletheDefect::UnknownAttribute { keyword, .. } if keyword == ":junk"),
        "got {defect:?}"
    );
}

#[test]
fn rejects_empty_premise_and_arg_sequences() {
    assert_eq!(
        reject("(step t1 (cl) :rule hole :premises ())\n").tag(),
        "empty-sequence"
    );
    assert_eq!(
        reject("(step t1 (cl) :rule hole :args ())\n").tag(),
        "empty-sequence"
    );
    assert_eq!(
        reject("(anchor :step t5 :args ())\n(step t5 (cl) :rule hole)\n").tag(),
        "empty-sequence"
    );
}

#[test]
fn rejects_numeral_and_reserved_step_ids() {
    assert_eq!(
        reject("(step 1 (cl) :rule hole)\n").tag(),
        "invalid-step-id"
    );
    assert_eq!(
        reject("(step cl (cl) :rule hole)\n").tag(),
        "invalid-step-id"
    );
    assert_eq!(
        reject("(step step (cl) :rule hole)\n").tag(),
        "invalid-step-id"
    );
}

#[test]
fn rejects_empty_subproof() {
    // Probe sp_empty: anchor + closing step alone.
    let defect = reject(
        "(assume a0 p)\n\
         (anchor :step t5)\n\
         (step t5 (cl p) :rule hole)\n\
         (step t9 (cl) :rule hole :premises (a0 t5))\n",
    );
    assert!(
        matches!(&defect, AletheDefect::EmptySubproof { id, .. } if id == "t5"),
        "got {defect:?}"
    );
}

#[test]
fn rejects_unclosed_subproof() {
    let defect = reject(
        "(assume a0 p)\n\
         (anchor :step t5)\n\
         (assume t5.h1 p)\n\
         (step t5.t2 (cl p) :rule hole :premises (t5.h1))\n",
    );
    assert!(
        matches!(&defect, AletheDefect::UnclosedSubproof { id } if id == "t5"),
        "got {defect:?}"
    );
}

#[test]
fn rejects_subproof_closed_by_an_assume() {
    // Probe sp_allassume.
    let defect = reject(
        "(assume a0 p)\n\
         (anchor :step t5)\n\
         (assume t5.h1 p)\n\
         (assume t5 p)\n\
         (step t9 (cl) :rule hole :premises (a0 t5))\n",
    );
    assert_eq!(defect.tag(), "subproof-last-not-step");
}

#[test]
fn rejects_assume_after_step_inside_a_subproof() {
    // Probe as_after_step_sub. Note the same shape at TOP level is only a
    // warning in carcara, and is accepted below.
    let defect = reject(
        "(assume a0 p)\n\
         (anchor :step t5)\n\
         (assume t5.h1 p)\n\
         (step t5.t2 (cl p) :rule hole :premises (t5.h1))\n\
         (assume t5.h2 p)\n\
         (step t5 (cl (not p) p) :rule subproof :discharge (t5.h1))\n\
         (step t9 (cl) :rule hole :premises (a0 t5))\n",
    );
    assert_eq!(defect.tag(), "assume-after-step");
}

#[test]
fn rejects_assume_after_a_nested_subproof_closes() {
    // The closing step of an inner subproof is still a step of the OUTER one.
    let defect = reject(
        "(assume a0 p)\n\
         (anchor :step t1)\n\
         (assume t1.h1 p)\n\
         (anchor :step t1.t1)\n\
         (assume t1.t1.h1 p)\n\
         (step t1.t1.s (cl p) :rule hole :premises (t1.t1.h1))\n\
         (step t1.t1 (cl (not p) p) :rule subproof :discharge (t1.t1.h1))\n\
         (assume t1.h2 p)\n\
         (step t1 (cl (not p) p) :rule subproof :discharge (t1.h1))\n\
         (step t9 (cl) :rule hole :premises (a0 t1))\n",
    );
    assert_eq!(defect.tag(), "assume-after-step");
}

#[test]
fn accepts_assume_after_step_at_top_level() {
    // Probe as_after_step_top: `[WARN]` then `holey`, NOT a parse error.
    accept(
        "(step t0 (cl p) :rule hole)\n(assume a1 p)\n(step t1 (cl) :rule hole :premises (a1))\n",
    );
}

#[test]
fn rejects_document_without_empty_clause() {
    // carcara: `checker error: proof does not conclude empty clause`.
    assert_eq!(
        reject("(step t0 (cl p) :rule hole)\n").tag(),
        "no-empty-clause"
    );
    assert_eq!(reject("").tag(), "no-empty-clause");
}

#[test]
fn rejects_empty_clause_only_inside_a_subproof() {
    // A `(cl)` that never escapes the subproof does not conclude the proof.
    let defect = reject(
        "(assume a0 p)\n\
         (anchor :step t5)\n\
         (assume t5.h1 p)\n\
         (step t5.x (cl) :rule hole :premises (t5.h1))\n\
         (step t5 (cl (not p) p) :rule subproof :discharge (t5.h1))\n",
    );
    assert_eq!(defect.tag(), "no-empty-clause");
}

#[test]
fn rejects_match_which_crashes_carcara() {
    let dt = ProblemScope::from_smtlib_source(
        "(declare-datatypes ((Lst 0)) (((nil) (cons (head Int) (tail Lst)))))\n\
         (declare-fun z () Lst)",
    );
    let text = "(step t0 (cl (= z (match z ((nil nil) ((cons h t) t))))) :rule hole)\n\
                (step t1 (cl) :rule hole :premises (t0))\n";
    let defect = check_alethe_document(text, &dt).expect_err("match must be refused");
    assert!(
        matches!(&defect, AletheDefect::ForbiddenConstruct { what, .. } if *what == "match"),
        "got {defect:?}"
    );
}

#[test]
fn rejects_lexical_errors_carcara_rejects() {
    assert_eq!(
        reject("(step t1 (cl p) :rule hole :args (007))\n").tag(),
        "leading-zero-numeral"
    );
    assert_eq!(
        reject("(step t1 (cl \\) :rule hole)\n").tag(),
        "unexpected-character"
    );
    assert_eq!(
        reject("(step t1 (cl |a\\b|) :rule hole)\n").tag(),
        "backslash-in-quoted-symbol"
    );
    assert_eq!(
        reject("(step t1 (cl |unterminated) :rule hole)\n").tag(),
        "unterminated-quoted-symbol"
    );
    assert_eq!(
        reject("(step t1 (cl #b) :rule hole)\n").tag(),
        "empty-bitvector-literal"
    );
}

#[test]
fn rejects_truncated_document() {
    // The failure mode a killed emission leaves behind.
    assert_eq!(
        reject("(assume a0 p)\n(step t0 (cl (P ").tag(),
        "unexpected-eof"
    );
}

#[test]
fn rejects_undefined_sort_in_a_binder() {
    let defect = reject(
        "(step t0 (cl (forall ((x NoSuchSort)) p)) :rule hole)\n\
         (step t1 (cl) :rule hole :premises (t0))\n",
    );
    assert!(
        matches!(&defect, AletheDefect::UndefinedSort { name, .. } if name == "NoSuchSort"),
        "got {defect:?}"
    );
}

#[test]
fn let_bound_variable_does_not_escape_its_body() {
    let defect = reject(
        "(step t0 (cl (and (let ((v l)) (<= v u)) (<= v u))) :rule hole)\n\
         (step t1 (cl) :rule hole :premises (t0))\n",
    );
    assert!(
        matches!(&defect, AletheDefect::UndefinedSymbol { name, .. } if name == "v"),
        "got {defect:?}"
    );
}

#[test]
fn quantified_variable_does_not_escape_its_body() {
    let defect = reject(
        "(step t0 (cl (and (forall ((x Int)) (<= x u)) (<= x u))) :rule hole)\n\
         (step t1 (cl) :rule hole :premises (t0))\n",
    );
    assert!(
        matches!(&defect, AletheDefect::UndefinedSymbol { name, .. } if name == "x"),
        "got {defect:?}"
    );
}

#[test]
fn anchor_bound_variable_does_not_escape_the_subproof() {
    let defect = reject(
        "(assume a0 p)\n\
         (anchor :step t5 :args ((:= (y Bool) p)))\n\
         (assume t5.h1 y)\n\
         (step t5.t2 (cl y) :rule hole :premises (t5.h1))\n\
         (step t5 (cl (not p) p) :rule subproof :discharge (t5.h1))\n\
         (step t9 (cl y) :rule hole :premises (a0 t5))\n\
         (step t10 (cl) :rule hole :premises (t9))\n",
    );
    assert!(
        matches!(&defect, AletheDefect::UndefinedSymbol { name, .. } if name == "y"),
        "got {defect:?}"
    );
}

// -------------------------------------------------------------------------
// Streaming / round-trip plumbing
// -------------------------------------------------------------------------

#[test]
fn streaming_matches_one_shot_at_every_chunk_size() {
    let text = "(assume a0 p)\n\
                (assume a1 (not p))\n\
                (step t0 (cl (forall ((x Int)) (<= x x))) :rule hole)\n\
                (step t1 (cl) :rule resolution :premises (a0 a1))\n";
    let expected = check_alethe_document(text, &scope()).expect("one-shot must accept");
    for chunk in [1usize, 2, 3, 7, 13, 64, 4096] {
        let mut checker = AletheDocumentChecker::new(scope());
        for piece in text.as_bytes().chunks(chunk) {
            checker.push_bytes(piece).expect("streaming must accept");
        }
        let got = checker.finish().expect("streaming must accept");
        assert_eq!(got, expected, "chunk size {chunk}");
    }
}

#[test]
fn streaming_handles_a_split_utf8_sequence() {
    let s = ProblemScope::from_smtlib_source("(declare-fun |é| () Bool)");
    let text = "(assume a0 |é|)\n(step t0 (cl) :rule hole :premises (a0))\n";
    let mut checker = AletheDocumentChecker::new(s);
    for piece in text.as_bytes().chunks(1) {
        checker.push_bytes(piece).expect("must accept");
    }
    checker.finish().expect("must accept");
}

#[test]
fn self_check_writer_tees_and_reports() {
    use std::io::Write as _;
    let text = "(assume a0 p)\n(step t0 (cl) :rule hole :premises (a0))\n";
    let mut writer = AletheSelfCheckWriter::new(Vec::new(), scope());
    writer.write_all(text.as_bytes()).expect("write");
    let (sink, verdict) = writer.finish();
    assert_eq!(String::from_utf8(sink).expect("utf8"), text);
    let report = verdict.expect("must accept");
    assert_eq!(report.steps, 1);
    assert_eq!(report.assumes, 1);
}

#[test]
fn self_check_writer_reports_the_declaration_preamble() {
    use std::io::Write as _;
    let text = "(declare-fun sk () Int)\n(step t0 (cl) :rule hole)\n";
    let mut writer = AletheSelfCheckWriter::new(Vec::new(), scope());
    writer.write_all(text.as_bytes()).expect("write");
    let (sink, verdict) = writer.finish();
    // The bytes still reach the sink: the check observes, it does not censor.
    assert_eq!(String::from_utf8(sink).expect("utf8"), text);
    assert_eq!(
        verdict.expect_err("must reject").tag(),
        "declaration-command"
    );
}

#[test]
fn in_process_scope_accepts_unknown_sorts_but_still_checks_symbols() {
    let s = ProblemScope::from_symbols(["p", "a", "P"]);
    check_alethe_document(
        "(step t0 (cl (forall ((x SomeProblemSort)) p)) :rule hole)\n\
         (step t1 (cl) :rule hole :premises (t0))\n",
        &s,
    )
    .expect("unknown sorts are tolerated on the in-process path");
    let defect = check_alethe_document(
        "(step t0 (cl (P nosuchsym)) :rule hole)\n(step t1 (cl) :rule hole :premises (t0))\n",
        &s,
    )
    .expect_err("symbols are still checked");
    assert_eq!(defect.tag(), "undefined-symbol");
}

#[test]
fn every_checkable_rule_name_is_accepted_as_a_rule() {
    for rule in checkable_rule_names() {
        accept(&format!(
            "(step t0 (cl p) :rule {rule})\n(step t1 (cl) :rule hole :premises (t0))\n"
        ));
    }
}
