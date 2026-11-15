// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! A `get-value` model is a function (#ufnia-model-scope). The D10 scope-leak
//! verifier's `ufnia_40417_00072` (QF_UFNIA, check-sat-assuming windows,
//! `get-value` after every check): at check 5 main answered `x1 = x2 = 0` with
//! `(f x1) = 8` and `(f x2) = 9`, in both postures. The UF+NIA adapter tabled
//! every `f` application in the session's `TermStore`, including ones only an
//! earlier window or `get-value` interned; the Nelson-Oppen loop never related
//! those to the arithmetic values of their arguments, so each got its own row.

use std::time::Duration;

use crate::hunt_quantifier_wrong_verdicts::{solve, Posture};

const UFNIA_40417_00072_GET_VALUE: &str = r#"
(set-option :produce-models true)
(set-logic QF_UFNIA)
(declare-fun x0 () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun p0 () Bool)
(declare-fun p1 () Bool)
(declare-fun p2 () Bool)
(declare-fun f (Int) Int)
(declare-fun g (Int Int) Int)
(assert (and (<= (* x1 x2) 0) (<= (* x1 x2) 0)))
(assert (=> p2 (= (* x3 x1) 0)))
(check-sat-assuming ((< (f x0) 10) (not (= (* x3 x1) 0))))
(get-value (x0 x1 x2 x3 p0 p1 p2 (f x0) (f x1) (f x2) (g x3 x1)))
(check-sat-assuming ((= x2 (g x3 x1)) (< (f x1) 0)))
(get-value (x0 x1 x2 x3 p0 p1 p2 (f x0) (f x1) (f x2) (g x3 x1)))
(check-sat-assuming (p2))
(get-value (x0 x1 x2 x3 p0 p1 p2 (f x0) (f x1) (f x2) (g x3 x1)))
(check-sat-assuming ((< (+ x0 (* (- 1) x1)) 7)))
(get-value (x0 x1 x2 x3 p0 p1 p2 (f x0) (f x1) (f x2) (g x3 x1)))
(assert (=> p1 (not (< (f x0) 10))))
(check-sat-assuming ((not (< (+ x0 (* (- 1) x1)) 7))))
(get-value (x0 x1 x2 x3 p0 p1 p2 (f x0) (f x1) (f x2) (g x3 x1)))
(check-sat)
(get-value (x0 x1 x2 x3 p0 p1 p2 (f x0) (f x1) (f x2) (g x3 x1)))
(assert (not (= x1 (* x3 x0))))
(check-sat-assuming ((not (= (* x3 x1) 0)) (< (* x1 x2) 2) (= x1 2)))
(get-value (x0 x1 x2 x3 p0 p1 p2 (f x0) (f x1) (f x2) (g x3 x1)))
(check-sat-assuming ((not (< (f x1) 0))))
(get-value (x0 x1 x2 x3 p0 p1 p2 (f x0) (f x1) (f x2) (g x3 x1)))
(assert (< (+ x0 (* (- 1) x1)) 7))
(check-sat)
(get-value (x0 x1 x2 x3 p0 p1 p2 (f x0) (f x1) (f x2) (g x3 x1)))
(check-sat-assuming ((<= (* x1 x2) 0) (= x3 (f x2))))
(get-value (x0 x1 x2 x3 p0 p1 p2 (f x0) (f x1) (f x2) (g x3 x1)))
(check-sat)
(get-value (x0 x1 x2 x3 p0 p1 p2 (f x0) (f x1) (f x2) (g x3 x1)))
(assert (>= (* x2 x1) (- 3)))
(check-sat)
(get-value (x0 x1 x2 x3 p0 p1 p2 (f x0) (f x1) (f x2) (g x3 x1)))
(assert (not (= (* x3 x1) 0)))
(check-sat)
(get-value (x0 x1 x2 x3 p0 p1 p2 (f x0) (f x1) (f x2) (g x3 x1)))
(exit)
"#;

/// The integer a `get-value` answer gives `key` (`(x1 0)`, `((f x1) (- 6))`).
fn value_of(answer: &str, key: &str) -> Option<i64> {
    let start = answer.find(&format!("({key} "))? + key.len() + 2;
    let rest = &answer[start..];
    if let Some(negated) = rest.strip_prefix("(- ") {
        let digits: String = negated.chars().take_while(char::is_ascii_digit).collect();
        return digits.parse::<i64>().ok().map(|value| -value);
    }
    let digits: String = rest.chars().take_while(char::is_ascii_digit).collect();
    digits.parse().ok()
}

#[test]
fn get_value_answers_give_equal_arguments_equal_results() {
    for posture in [Posture::Plain, Posture::Z3Mode] {
        let output = solve(
            UFNIA_40417_00072_GET_VALUE,
            posture,
            Some(Duration::from_secs(20)),
        );
        let answers: Vec<&String> = output
            .iter()
            .filter(|line| line.starts_with("((x0 "))
            .collect();
        assert!(
            answers.len() >= 5,
            "{posture:?}: the sat checks answer get-value; got {output:?}"
        );
        for answer in answers {
            let args = ["x0", "x1", "x2"].map(|x| value_of(answer, x));
            let results = ["(f x0)", "(f x1)", "(f x2)"].map(|t| value_of(answer, t));
            for i in 0..3 {
                for j in (i + 1)..3 {
                    if args[i].is_some() && args[i] == args[j] {
                        assert_eq!(
                            results[i], results[j],
                            "{posture:?}: equal arguments, different `f` values in {answer}"
                        );
                    }
                }
            }
        }
    }
}
