// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! LNH symmetry breaking over things that are not interchangeable constants.
//!
//! The finite-model symmetry pass (`executor/lnh_symmetry.rs`) adds
//! least-index pins (`e = t_0`) and lex-leader chains over a "domain" it reads
//! off a totality-shaped or-node. It took as domain elements nullary datatype
//! CONSTRUCTORS and COMPOUND terms (`(hd l_i)`, `(tl l_i)`, `(f a_i)`,
//! `(top (left s_i))`), and read the or-node from anywhere in the term store,
//! including scopes already popped. Its substitution check then passed
//! vacuously — nothing else mentions the swapped terms — although no model
//! symmetry exchanges their values, and the added clauses were false in every
//! model: wrong `unsat` in BOTH postures (E13 audit `l01`..`l06`, `pre11`,
//! `pre13`, verify-1 hunt). The domain is now restricted to declared free
//! constants, proven interchangeable over the live problem only.
//!
//! The scope fixtures pin the other half of the contract: symmetry clauses
//! derived for one check never constrain a later one.
//!
//! Every fixture runs in four postures; z3 5.1.0's answers are in `EXPECT`.

use std::time::Duration;

use ay_dpll::Executor;
use ay_frontend::parse;

/// `l01`: domain `{(hd l_0) .. (hd l_4)}`; the pin `e = (hd l0)` contradicts
/// `l0`'s head `A`.
const L01_COMPOUND_DOMAIN: &str = r#"
(set-logic QF_DT)
(declare-datatypes ((E 0) (L 0)) (((A) (B) (C) (D) (E5) (F)) ((cons (hd E) (tl L)) (nil))))
(declare-const e E)
(declare-const l0 L) (declare-const l1 L) (declare-const l2 L) (declare-const l3 L) (declare-const l4 L)
(assert (or (= e (hd l0)) (= e (hd l1)) (= e (hd l2)) (= e (hd l3)) (= e (hd l4))))
(assert (or (= l0 (cons A nil)) (= l0 (cons A (cons A nil)))))
(assert (not (= e A)))
(check-sat)
"#;

/// `l02`: the same defect in pure QF_UF, domain `{(f a_0) .. (f a_4)}`.
const L02_COMPOUND_DOMAIN_UF: &str = r#"
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun f (U) U)
(declare-const e U) (declare-const c U) (declare-const b U) (declare-const b2 U)
(declare-const a0 U) (declare-const a1 U) (declare-const a2 U) (declare-const a3 U) (declare-const a4 U)
(assert (or (= e (f a0)) (= e (f a1)) (= e (f a2)) (= e (f a3)) (= e (f a4))))
(assert (or (= a0 b) (= a0 b2)))
(assert (= (f b) c))
(assert (= (f b2) c))
(assert (not (= e c)))
(check-sat)
"#;

/// `l03`: a nested totality-shaped or over `(tl l_i)` drives the lex-leader
/// over the list testers.
const L03_LEXLEADER_COMPOUND: &str = r#"
(set-logic QF_DT)
(declare-datatypes ((E 0) (L 0)) (((A) (B) (C)) ((cons (hd E) (tl L)) (nil))))
(declare-const x L) (declare-const c Bool)
(declare-const l0 L) (declare-const l1 L) (declare-const l2 L) (declare-const l3 L) (declare-const l4 L) (declare-const l5 L)
(assert (= c (or (= x (tl l0)) (= x (tl l1)) (= x (tl l2)) (= x (tl l3)) (= x (tl l4)) (= x (tl l5)))))
(assert (or (= l0 (cons A (cons B nil))) (= l0 (cons B (cons B nil)))))
(assert (or (= l1 (cons A nil)) (= l1 (cons B nil))))
(assert (or ((_ is cons) x) ((_ is nil) x)))
(check-sat)
"#;

/// `l04`: least-index over list-valued compound terms `(tl l_i)`.
const L04_LEASTIDX_LIST_DOMAIN: &str = r#"
(set-logic QF_DT)
(declare-datatypes ((E 0) (L 0)) (((A) (B) (C)) ((cons (hd E) (tl L)) (nil))))
(declare-const x L)
(declare-const l0 L) (declare-const l1 L) (declare-const l2 L) (declare-const l3 L) (declare-const l4 L)
(assert (or (= x (tl l0)) (= x (tl l1)) (= x (tl l2)) (= x (tl l3)) (= x (tl l4))))
(assert (or (= l0 (cons A (cons B nil))) (= l0 (cons B (cons C nil)))))
(assert ((_ is nil) x))
(check-sat)
"#;

/// `l05`: the domain came from an or-node asserted only inside a popped
/// scope; the live query never mentions it.
const L05_STALE_POPPED_DOMAIN: &str = r#"
(set-logic QF_DT)
(declare-datatypes ((E 0) (L 0)) (((A) (B) (C)) ((cons (hd E) (tl L)) (nil))))
(declare-const x L)
(declare-const l0 L) (declare-const l1 L) (declare-const l2 L) (declare-const l3 L) (declare-const l4 L) (declare-const l5 L)
(push 1)
(assert (not (or (= x (tl l0)) (= x (tl l1)) (= x (tl l2)) (= x (tl l3)) (= x (tl l4)) (= x (tl l5)))))
(check-sat)
(pop 1)
(assert (or (= l0 (cons A (cons B nil))) (= l0 (cons B (cons B nil)))))
(assert (or (= l1 (cons A nil)) (= l1 (cons B nil))))
(assert (or ((_ is cons) x) ((_ is nil) x)))
(check-sat)
"#;

/// `l06`: the blocksworld signature, domain `{(top (left s_i))}`.
const L06_BLOCKSWORLD_SHAPE: &str = r#"
(set-logic QF_DT)
(declare-datatypes ((Enum_A_B_C_D_E_F 0)) (((A) (B) (C) (D) (E) (F))))
(declare-datatypes ((Tower 0)) (((stack (top Enum_A_B_C_D_E_F) (rest Tower)) (empty))))
(declare-datatypes ((Record_left_center_right 0)) (((Record_left_center_right (left Tower) (center Tower) (right Tower)))))
(declare-fun blk () Enum_A_B_C_D_E_F)
(declare-fun s0 () Record_left_center_right)
(declare-fun s1 () Record_left_center_right)
(declare-fun s2 () Record_left_center_right)
(declare-fun s3 () Record_left_center_right)
(declare-fun s4 () Record_left_center_right)
(assert (or (= blk (top (left s0))) (= blk (top (left s1))) (= blk (top (left s2))) (= blk (top (left s3))) (= blk (top (left s4)))))
(assert (or (= s0 (Record_left_center_right (stack A empty) empty empty))
            (= s0 (Record_left_center_right (stack A (stack B empty)) empty empty))))
(assert (not (= blk A)))
(check-sat)
"#;

/// `pre13`: a domain of the five nullary constructors of an enum.
const PRE13_ENUM_CONSTRUCTORS: &str = r#"
(set-logic QF_DT)
(declare-datatypes ((E 0)) (((A) (B) (C) (D) (E5))))
(declare-const e0 E)
(assert (or (= e0 A) (= e0 B) (= e0 C) (= e0 D) (= e0 E5)))
(assert ((_ is D) e0))
(check-sat)
"#;

/// `pre11`: ten constructors, a single totality subject.
const PRE11_SINGLE_TOTALITY_CONST: &str = r#"
(set-logic QF_DT)
(declare-datatypes ((E 0) (L 0)) (((A) (B) (C) (D) (E5) (E6) (E7) (E8) (E9) (E10)) ((cons (hd E) (tl L)) (nil))))
(declare-const e0 E)
(declare-const e1 E)
(declare-const x L)
(assert (or (= A e0) (= B e0) (= C e0) (= D e0) (= E5 e0) (= E6 e0) (= E7 e0) (= E8 e0) (= E9 e0) (= E10 e0)))
(assert ((_ is E7) e0))
(assert ((_ is cons) x))
(check-sat)
"#;

/// verify-1 hunt: the generated enum coverage disjunction over six
/// constructors, inside a push, checked twice.
const PUSH_SECOND_CHECKSAT: &str = r#"
(set-logic QF_DT)
(declare-datatype E ((C0) (C1) (C2) (C3) (C4) (C5)))
(declare-datatype L ((cons (hd E) (tl L)) (nil)))
(declare-const e E)
(declare-const x L)
(push 1)
(assert ((_ is C2) (hd x)))
(check-sat)
(check-sat)
"#;

/// A genuine symmetric domain at depth 0: the first check may pin `x = c0`;
/// the second asserts `x /= c0`, which the pin must not outlive.
const SCOPE_PIN_THEN_ASSERT: &str = r#"
(set-logic QF_UF)
(declare-sort U 0)
(declare-const x U)
(declare-const c0 U) (declare-const c1 U) (declare-const c2 U)
(declare-const c3 U) (declare-const c4 U) (declare-const c5 U)
(assert (distinct c0 c1 c2 c3 c4 c5))
(assert (or (= x c0) (= x c1) (= x c2) (= x c3) (= x c4) (= x c5)))
(check-sat)
(assert (not (= x c0)))
(check-sat)
"#;

/// The same inside a push, and again after the pop.
const SCOPE_PIN_IN_PUSH: &str = r#"
(set-logic QF_UF)
(declare-sort U 0)
(declare-const x U)
(declare-const c0 U) (declare-const c1 U) (declare-const c2 U)
(declare-const c3 U) (declare-const c4 U) (declare-const c5 U)
(assert (distinct c0 c1 c2 c3 c4 c5))
(push 1)
(assert (or (= x c0) (= x c1) (= x c2) (= x c3) (= x c4) (= x c5)))
(check-sat)
(push 1)
(assert (= x c3))
(check-sat)
(pop 1)
(pop 1)
(assert (= x c4))
(check-sat)
"#;

/// The symmetric domain checked under an assumption that breaks the symmetry.
const SCOPE_PIN_UNDER_ASSUMPTION: &str = r#"
(set-logic QF_UF)
(declare-sort U 0)
(declare-const x U)
(declare-const c0 U) (declare-const c1 U) (declare-const c2 U)
(declare-const c3 U) (declare-const c4 U) (declare-const c5 U)
(assert (distinct c0 c1 c2 c3 c4 c5))
(assert (or (= x c0) (= x c1) (= x c2) (= x c3) (= x c4) (= x c5)))
(check-sat-assuming ((= x c5)))
(check-sat)
"#;

/// Fixtures with z3 5.1.0's answers, and how many leading checks `--z3-mode`
/// must DECIDE. `l05`'s second check is `unknown` with the pass disabled too
/// (a datatype model after a pop that over-populates the enum sort: a
/// separate incompleteness, not a symmetry clause), so only its first check is
/// held to a decision.
const FIXTURES: [(&str, &str, &[&str], usize); 12] = [
    ("l01 compound domain", L01_COMPOUND_DOMAIN, &["sat"], 1),
    (
        "l02 compound domain (UF)",
        L02_COMPOUND_DOMAIN_UF,
        &["sat"],
        1,
    ),
    (
        "l03 lex-leader compound",
        L03_LEXLEADER_COMPOUND,
        &["sat"],
        1,
    ),
    (
        "l04 least-index list domain",
        L04_LEASTIDX_LIST_DOMAIN,
        &["sat"],
        1,
    ),
    (
        "l05 stale popped domain",
        L05_STALE_POPPED_DOMAIN,
        &["sat", "sat"],
        1,
    ),
    ("l06 blocksworld shape", L06_BLOCKSWORLD_SHAPE, &["sat"], 1),
    (
        "pre13 enum constructors",
        PRE13_ENUM_CONSTRUCTORS,
        &["sat"],
        1,
    ),
    (
        "pre11 single totality",
        PRE11_SINGLE_TOTALITY_CONST,
        &["sat"],
        1,
    ),
    (
        "push, second check-sat",
        PUSH_SECOND_CHECKSAT,
        &["sat", "sat"],
        2,
    ),
    ("pin then assert", SCOPE_PIN_THEN_ASSERT, &["sat", "sat"], 2),
    ("pin in push", SCOPE_PIN_IN_PUSH, &["sat", "sat", "sat"], 3),
    (
        "pin under assumption",
        SCOPE_PIN_UNDER_ASSUMPTION,
        &["sat", "sat"],
        2,
    ),
];

pub(crate) fn verdicts(results: &[String]) -> Vec<&str> {
    results
        .iter()
        .map(|line| line.trim())
        .filter(|line| matches!(*line, "sat" | "unsat" | "unknown"))
        .collect()
}

#[derive(Clone, Copy, Debug)]
pub(crate) enum Posture {
    /// `Executor::execute_all`, no flags.
    Plain,
    /// The caller-authored boundary the CLI uses.
    Authored,
    /// Fail-closed self-certification (`--self-check`).
    SelfCheck,
    /// The CLI's `--z3-mode` posture: the internal proof cycle is shed.
    Z3Mode,
}

pub(crate) const POSTURES: [Posture; 4] = [
    Posture::Plain,
    Posture::Authored,
    Posture::SelfCheck,
    Posture::Z3Mode,
];

/// Every wrong verdict pinned here was immediate on main.
pub(crate) const NEVER_WRONG_BUDGET: Duration = Duration::from_secs(5);
pub(crate) const DECIDED_BUDGET: Duration = Duration::from_secs(30);

pub(crate) fn solve(smt: &str, posture: Posture, budget: Duration) -> Vec<String> {
    let commands = parse(smt).unwrap_or_else(|err| panic!("parse failed: {err}\nSMT2:\n{smt}"));
    let mut exec = Executor::new();
    exec.set_timeout(Some(budget));
    match posture {
        Posture::SelfCheck => exec.set_self_check(true),
        Posture::Z3Mode => exec.set_competition_mode(true),
        Posture::Plain | Posture::Authored => {}
    }
    if matches!(posture, Posture::Authored) {
        let mut output = Vec::new();
        for command in &commands {
            if let Some(line) = exec
                .execute_authored(command)
                .unwrap_or_else(|err| panic!("execution failed: {err}\nSMT2:\n{smt}"))
            {
                output.push(line);
            }
        }
        output
    } else {
        exec.execute_all(&commands)
            .unwrap_or_else(|err| panic!("execution failed: {err}\nSMT2:\n{smt}"))
    }
}

/// A definite answer that contradicts z3 is wrong; `unknown` is not.
#[test]
fn lnh_never_breaks_symmetry_that_is_not_there() {
    for (name, smt, expect, _) in FIXTURES {
        for posture in POSTURES {
            let results = solve(smt, posture, NEVER_WRONG_BUDGET);
            let got = verdicts(&results);
            assert_eq!(
                got.len(),
                expect.len(),
                "{name} ({posture:?}): one verdict per check expected; got {results:?}"
            );
            for (index, (&got, &want)) in got.iter().zip(expect).enumerate() {
                assert!(
                    got == want || got == "unknown",
                    "WRONG VERDICT ({name}, {posture:?}, check {index}): z3 5.1.0 says \
                     `{want}`, got `{got}`; all answers {all:?}",
                    all = verdicts(&results)
                );
            }
        }
    }
}

/// The repair must not buy soundness with `unknown`: `--z3-mode` decides the
/// fixtures (each is decided in milliseconds; the budget absorbs a loaded
/// machine).
#[test]
fn lnh_fixtures_are_decided_in_z3_mode() {
    for (name, smt, expect, decided) in FIXTURES {
        let results = solve(smt, Posture::Z3Mode, DECIDED_BUDGET);
        assert_eq!(
            verdicts(&results).get(..decided),
            expect.get(..decided),
            "{name} (Z3Mode): z3 5.1.0's answers expected; got {results:?}"
        );
    }
}
