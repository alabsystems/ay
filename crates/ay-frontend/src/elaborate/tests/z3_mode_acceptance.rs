// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Constructs this frontend accepted and z3 4.12.5 rejects. z3 drops such a
//! command, and a label in it, so `--z3-mode` rejects them; the CLI tests
//! pin the answers.

use super::*;

const PRELUDE: &str = "(declare-const p Bool)(declare-const x Int)(declare-const r Real)\
     (declare-const s String)(declare-const b (_ BitVec 8))(declare-const c (_ BitVec 4))\
     (declare-const q (Seq Int))(declare-const h (Array Int Bool))";

/// Whether the last command of `PRELUDE` + `input` is accepted.
fn accepted(z3: bool, input: &str) -> bool {
    let mut ctx = Context::new();
    ctx.set_z3_mode(z3);
    let commands = parse(&format!("{PRELUDE}{input}")).unwrap();
    let (last, rest) = commands.split_last().unwrap();
    for cmd in rest {
        ctx.process_command(cmd).unwrap();
    }
    ctx.process_command(last).is_ok()
}

/// Every z3 rejects a quantifier whose body is not Boolean, after reading it;
/// so does every mode here (the term store has no reading for one).
#[test]
fn a_quantifier_body_must_be_boolean() {
    for assertion in [
        "(assert (forall ((z Int)) 5))",
        "(assert (exists ((z Int)) x))",
        "(assert (and p (forall ((z Bool)) b)))",
        "(assert (or p (ite true true (forall ((z Int)) (+ z 1)))))",
    ] {
        assert!(!accepted(true, assertion), "{assertion}");
        assert!(!accepted(false, assertion), "{assertion}");
    }
    assert!(accepted(true, "(assert (forall ((z Int)) true))"));
    assert!(accepted(false, "(assert (forall ((z Int)) true))"));
}

/// z3 reads arithmetic over Int, Real and Bool only. z3 mode rejects any
/// other operand. Plain mode keeps reading a bit-vector beside a number as
/// its `bv2nat` value, which the CHC engine's abstraction relies on, and
/// rejects the rest: arithmetic over bit-vectors alone has no reading here.
#[test]
fn z3_mode_rejects_non_numeric_arithmetic_operands() {
    for assertion in [
        "(assert (> b c))",
        "(assert (= (+ b b) b))",
        "(assert (< x s))",
        "(assert (= (* x s) x))",
        "(assert (= (+ s s) s))",
    ] {
        assert!(!accepted(true, assertion), "{assertion}");
        assert!(!accepted(false, assertion), "{assertion}");
    }
    for assertion in ["(assert (> b x))", "(assert (= (+ b 1) x))"] {
        assert!(!accepted(true, assertion), "{assertion}");
        assert!(accepted(false, assertion), "{assertion}");
    }
    for assertion in ["(assert (= (+ p 1) x))", "(assert (< p r))"] {
        assert!(accepted(true, assertion), "{assertion}");
    }
}

/// Operators and sorts this frontend adds that z3 4.12.5 does not know are
/// unknown in z3 mode, unless the script declares the name itself.
#[test]
fn z3_mode_rejects_operators_and_sorts_z3_does_not_know() {
    for command in [
        "(assert (= (min x 1) x))",
        "(assert (= (max x 1) x))",
        "(assert (= (str.to_lower s) s))",
        "(assert (set.member x h))",
        "(assert (= (set.singleton x) h))",
        "(declare-const m (Map Int Int))",
        "(declare-const m (Multiset Int))",
        "(declare-const m (FiniteSet Int))",
    ] {
        assert!(!accepted(true, command), "{command}");
        assert!(accepted(false, command), "{command}");
    }
    assert!(accepted(
        true,
        "(declare-fun min (Int Int) Int)(assert (= (min x 1) x))"
    ));
}

/// Sequence operators check their operands as z3 does, in every mode: one
/// `(Seq T)` sort for the sequences, Int for indices, and no regular
/// expression over a non-String sequence. A String operand is the string
/// operator's.
#[test]
fn sequence_operands_are_sort_checked() {
    for assertion in [
        "(assert (= (seq.len (seq.++ q s)) 1))",
        "(assert (= (seq.++ q q s) q))",
        "(assert (= (seq.at q p) q))",
        "(assert (= (seq.nth q r) 1))",
        "(assert (seq.contains q s))",
        "(assert (seq.prefixof s q))",
        "(assert (= (seq.replace q q s) q))",
        "(assert (= (seq.indexof q q p) 1))",
        "(assert (seq.in.re q re.none))",
        "(assert (seq.in.re q (seq.to.re q)))",
    ] {
        assert!(!accepted(true, assertion), "{assertion}");
        assert!(!accepted(false, assertion), "{assertion}");
    }
    for assertion in [
        "(assert (= (seq.len (seq.++ q q)) 1))",
        "(assert (= (seq.nth q x) 1))",
        "(assert (seq.prefixof s s))",
        "(assert (seq.suffixof q q))",
        "(assert (= (seq.indexof q q 0) 1))",
        "(assert (seq.in.re s (str.to_re \"a\")))",
    ] {
        assert!(accepted(true, assertion), "{assertion}");
        assert!(accepted(false, assertion), "{assertion}");
    }
}

/// z3 registers `divisible` only when `:smtlib2_compliant` is true as its
/// session starts. Once the host says the session started, a later setting
/// does not register it.
#[test]
fn divisible_needs_smtlib2_compliant_as_the_session_starts() {
    let run = |set_before_start: bool| {
        let mut ctx = Context::new();
        ctx.set_z3_mode(true);
        let option = parse("(set-option :smtlib2_compliant true)").unwrap();
        if set_before_start {
            ctx.process_command(&option[0]).unwrap();
        }
        let declare = parse("(declare-const x Int)").unwrap();
        ctx.note_z3_session_started();
        ctx.process_command(&declare[0]).unwrap();
        if !set_before_start {
            ctx.process_command(&option[0]).unwrap();
        }
        let assertion = parse("(assert ((_ divisible 2) x))").unwrap();
        ctx.process_command(&assertion[0]).is_ok()
    };
    assert!(run(true));
    assert!(!run(false));
}
