// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Datatype members and datatype sorts spelled `||`, the empty SMT-LIB symbol,
//! each solved beside a twin that renames every `||` it declares.
//!
//! With proofs on in the Clean and pinned Carcara dialects, each script in
//! `EMPTY_IDENTITY_UNSAT` and r1 (congruence over the selector `||`) answer
//! `unsat` with `unsat_admission=strict-proof`, as their twins do; the
//! published document has no `:rule trust` step, and the retained proof
//! passes `check_proof_strict_with_datatypes` with zero trust steps. w3
//! answers the same verdict and admission with proofs off, as its twin does.
//! w1 is refused as a tester collision, as its twin is.

use super::*;

/// An unsatisfiable script that declares a datatype member or datatype sort
/// named `||`, and its twin, which renames every `||` the script declares.
struct Case {
    label: &'static str,
    empty: &'static str,
    twin: &'static str,
    /// Whether the proof of `empty` contains the whole symbol `||`, as
    /// `contains_empty_symbol` decides; the test asserts it either way.
    prints_empty_member: bool,
}

/// Whether `text` contains `||` as a whole symbol: bounded on each side by
/// `(`, `)`, whitespace or the end of the text. The `||` at the end of
/// `|\|\||` is preceded by `\` and does not count.
fn contains_empty_symbol(text: &str) -> bool {
    let bounds = |c: Option<char>| c.is_none_or(|c| c == '(' || c == ')' || c.is_whitespace());
    text.match_indices("||").any(|(at, _)| {
        bounds(text[..at].chars().next_back()) && bounds(text[at + 2..].chars().next())
    })
}

const EMPTY_IDENTITY_UNSAT: &[Case] = &[
    Case {
        label: "p11_eq_2: nullary constructor ||",
        empty: "(declare-datatypes ((E 0)) (((||) (b))))\n(assert (= || b))",
        twin: "(declare-datatypes ((E 0)) (((a) (b))))\n(assert (= a b))",
        prints_empty_member: true,
    },
    Case {
        label: "p11_eq_4: constructors || and |\\|\\||",
        empty: "(declare-datatypes ((E 0)) (((||) (|\\|\\||))))\n(assert (= || |\\|\\||))",
        twin: "(declare-datatypes ((E 0)) (((a) (|\\|\\||))))\n(assert (= a |\\|\\||))",
        prints_empty_member: true,
    },
    Case {
        label: "p12_empty_ctor_var_unsat: a constant equal to ||",
        empty: "(declare-datatypes ((E 0)) (((||) (b))))\n(declare-const v E)\n\
                (assert (= v ||))\n(assert (= v b))",
        twin: "(declare-datatypes ((E 0)) (((a) (b))))\n(declare-const v E)\n\
               (assert (= v a))\n(assert (= v b))",
        prints_empty_member: true,
    },
    Case {
        label: "r2: tester (_ is ||)",
        empty: "(declare-datatypes ((E 0)) (((||) (b))))\n(declare-const v E)\n\
                (assert ((_ is ||) v))\n(assert (= v b))",
        twin: "(declare-datatypes ((E 0)) (((a) (b))))\n(declare-const v E)\n\
               (assert ((_ is a) v))\n(assert (= v b))",
        prints_empty_member: true,
    },
    Case {
        label: "q1: datatype sort ||",
        empty: "(declare-datatypes ((|| 0)) (((a) (b))))\n(assert (= a b))",
        twin: "(declare-datatypes ((D 0)) (((a) (b))))\n(assert (= a b))",
        prints_empty_member: false,
    },
    Case {
        label: "r5: a constant of datatype sort ||",
        empty: "(declare-datatypes ((|| 0)) (((a) (b))))\n(declare-const v ||)\n\
                (assert (= v a))\n(assert (= v b))",
        twin: "(declare-datatypes ((D 0)) (((a) (b))))\n(declare-const v D)\n\
               (assert (= v a))\n(assert (= v b))",
        prints_empty_member: false,
    },
    Case {
        label: "r6: || as the nil of a recursive list",
        empty: "(declare-datatypes ((L 0)) (((||) (cons (hd Int) (tl L)))))\n\
                (declare-const x L)\n(assert (= x (cons 1 x)))",
        twin: "(declare-datatypes ((L 0)) (((nil) (cons (hd Int) (tl L)))))\n\
               (declare-const x L)\n(assert (= x (cons 1 x)))",
        prints_empty_member: false,
    },
    Case {
        label: "u4: || overloaded in two datatypes",
        empty: "(declare-datatypes ((E 0) (F 0)) (((||) (b)) ((||) (c))))\n\
                (declare-const v E)\n(assert (= v (as || E)))\n(assert (= v b))",
        twin: "(declare-datatypes ((E 0) (F 0)) (((a) (b)) ((a) (c))))\n\
               (declare-const v E)\n(assert (= v (as a E)))\n(assert (= v b))",
        prints_empty_member: true,
    },
    Case {
        label: "q5: constructor is- beside ||, whose tester is is-",
        empty: "(declare-datatypes ((E 0)) (((||) (is-))))\n(assert (= || is-))",
        twin: "(declare-datatypes ((E 0)) (((a) (is-a))))\n(assert (= a is-a))",
        prints_empty_member: true,
    },
];

const DIALECTS: [ay_proof::AletheDialect; 2] = [
    ay_proof::AletheDialect::Clean,
    ay_proof::AletheDialect::PinnedCarcara,
];

/// Solve `body`, with proofs on in `dialect` when one is given.
fn solve(body: &str, dialect: Option<ay_proof::AletheDialect>) -> (Executor, Vec<String>) {
    let option = if dialect.is_some() {
        "(set-option :produce-proofs true)\n"
    } else {
        ""
    };
    let script = format!("{option}{body}\n(check-sat)\n");
    let commands = parse(&script).unwrap_or_else(|error| panic!("{script}: {error}"));
    let mut exec = Executor::new();
    if let Some(dialect) = dialect {
        exec.set_alethe_dialect(dialect);
    }
    let outputs = exec
        .execute_all(&commands)
        .unwrap_or_else(|error| panic!("{script}: {error}"));
    (exec, outputs)
}

/// The verdict is `unsat` under a strict-proof admission; with proofs on,
/// the published document and the retained proof carry no trust step and
/// the document is returned.
fn assert_strictly_admitted_unsat(
    label: &str,
    body: &str,
    dialect: Option<ay_proof::AletheDialect>,
) -> String {
    let (exec, outputs) = solve(body, dialect);
    assert_eq!(outputs, vec!["unsat"], "{label} {dialect:?}");
    assert_eq!(
        exec.last_command_unsat_admission_tag(),
        Some("strict-proof"),
        "{label} {dialect:?}"
    );
    if dialect.is_none() {
        return String::new();
    }
    let text = exec.get_proof();
    assert!(
        !text.contains(":rule trust"),
        "{label} {dialect:?}:\n{text}"
    );
    let proof = exec.last_proof.as_ref().expect("proof after UNSAT");
    let quality = exec
        .check_proof_strict_with_datatypes(proof)
        .unwrap_or_else(|error| panic!("{label} {dialect:?}: {error:?}\n{text}"));
    assert_eq!(quality.trust_count, 0, "{label} {dialect:?}");
    assert!(
        ay_proof::terminal_trust_report(proof).is_trust_free(),
        "{label} {dialect:?}"
    );
    text
}

#[test]
fn empty_datatype_identities_certify_like_their_twins() {
    for case in EMPTY_IDENTITY_UNSAT {
        for dialect in DIALECTS {
            let twin = format!("{} (twin)", case.label);
            assert_strictly_admitted_unsat(&twin, case.twin, Some(dialect));
            let text = assert_strictly_admitted_unsat(case.label, case.empty, Some(dialect));
            assert_eq!(
                contains_empty_symbol(&text),
                case.prints_empty_member,
                "{} {dialect:?}:\n{text}",
                case.label
            );
        }
    }
}

#[test]
fn empty_tester_prints_as_the_indexed_tester_of_the_empty_symbol() {
    let text = assert_strictly_admitted_unsat(
        "r2",
        EMPTY_IDENTITY_UNSAT[3].empty,
        Some(ay_proof::AletheDialect::PinnedCarcara),
    );
    assert!(text.contains("(_ is ||)"), "{text}");
}

/// Congruence over the empty selector leaves no unproved step in either
/// dialect, as for its twin selector `sx`.
#[test]
fn empty_selector_congruence_is_fully_checkable() {
    let script = |selector: &str| {
        format!(
            "(declare-datatypes ((P 0)) (((mk ({selector} Int)) (nil))))\n\
             (declare-const p P)\n(declare-const q P)\n\
             (assert (= p q))\n(assert (not (= ({selector} p) ({selector} q))))"
        )
    };
    for selector in ["sx", "||"] {
        for dialect in DIALECTS {
            let label = format!("r1 selector {selector}");
            let text = assert_strictly_admitted_unsat(&label, &script(selector), Some(dialect));
            assert!(!text.contains(":rule hole"), "{label} {dialect:?}:\n{text}");
            assert!(
                text.contains(&format!("({selector} p)")),
                "{label} {dialect:?}:\n{text}"
            );
        }
    }
}

/// w3: with a Bool selector `is-` declared after constructor `||`, the script
/// answers `unsat` with strict-proof admission with proofs off, as it does
/// with selector `is-a` after constructor `a`.
///
/// w1: a user function `is-` declared after constructor `||` is refused with
/// the tester-collision error, as `is-a` is after constructor `a`.
#[test]
fn names_spelled_like_the_empty_tester_keep_their_namespace() {
    for (constructor, tester) in [("a", "is-a"), ("||", "is-")] {
        let w3 = format!(
            "(declare-datatypes ((E 0)) ((({constructor}) (b))))\n\
             (declare-datatypes ((F 0)) (((mk ({tester} Bool)))))\n\
             (declare-const f F)\n(declare-const v E)\n\
             (assert ({tester} f))\n(assert (= v {constructor}))\n(assert (= v b))"
        );
        assert_strictly_admitted_unsat(&format!("w3 {constructor}"), &w3, None);
        let w1 = format!(
            "(declare-datatypes ((E 0)) ((({constructor}) (b))))\n\
             (declare-fun {tester} (E) Bool)\n(declare-const v E)\n\
             (assert (= v b))\n(assert ({tester} v))"
        );
        let commands = parse(&w1).expect("w1 parses");
        let error = Executor::new()
            .execute_all(&commands)
            .expect_err("the colliding declaration is refused")
            .to_string();
        assert!(
            error.contains(&format!(
                "symbol '{tester}' is already a datatype constructor/selector/tester"
            )),
            "{w1}: {error}"
        );
    }
}
