// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! An `ite` whose condition is a nullary Bool `define-fun` is assumed as
//! written, and the certificate reads the macro through its definition
//! premise.
//!
//! MEASURED at 8b4bcfd5a (carcara 1.1.0, git 9a352ee): `ay --proof` on
//! `benchmarks/smt/known_bugs/bv_ite_shared_vars_minimal.smt2` and
//! `bv_ite_concat_extract_4op.smt2` answered `unsat` with `foreign_assumes=yes
//! trust_free=no carcara_surface=supported`, and pinned carcara answered
//! `invalid` in both invocations: "could not match term to any of the
//! original problem premises: (ite (= mode_1 (_ bv0 1)) ..)". The authored
//! `(ite m1 ..)` elaborates to an `ite` ROOT (a term constructor, not a
//! symbol application), the printer's definition schema had no `cong` head
//! for it, and the root kept its macro-expanded canonical text. Since the
//! schema reads `ite` as a head, the certificate assumes `(ite m1 ..)` plus
//! `(= m1 (= mode_1 (_ bv0 1)))`, and pinned carcara answers `valid`.

use super::super::alethe_dialect_disclosure::pinned_carcara_verdict_in;
use super::super::strict_admission_routes::ALL_ROUTES;
use super::super::strict_certificate_publication::{verdict_lines, QUERY_TIMEOUT};
use super::*;
use crate::spawn::OutputTimeout;
use std::process::Command;

const SHARED_VARS: &str = "benchmarks/smt/known_bugs/bv_ite_shared_vars_minimal.smt2";

/// `benchmarks/smt/known_bugs/bv_ite_concat_extract_4op.smt2` with its
/// comment lines dropped. Inline because the public export does not ship that
/// file (`publish/manifest.txt`). It differs from `SHARED_VARS` where the
/// bridge does: a bare Bool macro (`v19`, `v43`) is a conjunct of an `ite`
/// branch, not only bit-vector macros under an equality.
const CONCAT_EXTRACT_4OP: &str = "\
(set-logic QF_BV)
(set-info :status unsat)
(declare-fun opr1 () (_ BitVec 8))
(declare-fun opr2 () (_ BitVec 8))
(declare-fun opr3 () (_ BitVec 8))
(declare-fun opr4 () (_ BitVec 8))
(declare-fun dec_func () (_ BitVec 1))
(declare-fun deci_func () (_ BitVec 1))
(declare-fun decode_1 () (_ BitVec 33))
(declare-fun func_1 () (_ BitVec 1))
(declare-fun op1_1 () (_ BitVec 8))
(declare-fun op2_1 () (_ BitVec 8))
(declare-fun op3_1 () (_ BitVec 8))
(declare-fun op4_1 () (_ BitVec 8))
(declare-fun mode_1 () (_ BitVec 1))
(declare-fun decode_2 () (_ BitVec 33))
(declare-fun func_2 () (_ BitVec 1))
(declare-fun op1_2 () (_ BitVec 8))
(declare-fun op2_2 () (_ BitVec 8))
(declare-fun op3_2 () (_ BitVec 8))
(declare-fun op4_2 () (_ BitVec 8))
(declare-fun mode_2 () (_ BitVec 1))
(define-fun v18 () Bool (= mode_1 (_ bv0 1)))
(assert (ite v18
  (= decode_1 (concat (concat (concat (concat dec_func opr1) opr2) opr3) opr4))
  (= decode_1 (concat (concat (concat (concat deci_func opr4) opr3) opr2) opr1))))
(define-fun v19 () Bool (= func_1 ((_ extract 32 32) decode_1)))
(define-fun v20 () (_ BitVec 8) ((_ extract 31 24) decode_1))
(define-fun v21 () (_ BitVec 8) ((_ extract 23 16) decode_1))
(define-fun v22 () (_ BitVec 8) ((_ extract 15 8) decode_1))
(define-fun v23 () (_ BitVec 8) ((_ extract 7 0) decode_1))
(assert (ite v18
  (and v19 (= op1_1 v20) (= op2_1 v21) (= op3_1 v22) (= op4_1 v23))
  (and v19 (= op4_1 v20) (= op3_1 v21) (= op2_1 v22) (= op1_1 v23))))
(define-fun v41 () Bool (= mode_2 (_ bv0 1)))
(assert (ite v41
  (= decode_2 (concat (concat (concat (concat opr1 dec_func) opr2) opr3) opr4))
  (= decode_2 (concat (concat (concat (concat opr4 deci_func) opr3) opr2) opr1))))
(define-fun v42 () (_ BitVec 8) ((_ extract 32 25) decode_2))
(define-fun v43 () Bool (= func_2 ((_ extract 24 24) decode_2)))
(define-fun v44 () (_ BitVec 8) ((_ extract 23 16) decode_2))
(define-fun v45 () (_ BitVec 8) ((_ extract 15 8) decode_2))
(define-fun v46 () (_ BitVec 8) ((_ extract 7 0) decode_2))
(assert (ite v41
  (and (= op1_2 v42) v43 (= op2_2 v44) (= op3_2 v45) (= op4_2 v46))
  (and (= op4_2 v42) v43 (= op3_2 v44) (= op2_2 v45) (= op1_2 v46))))
(declare-fun out_1 () (_ BitVec 8))
(declare-fun out_2 () (_ BitVec 8))
(assert (ite (= func_1 (_ bv1 1))
  (= out_1 (bvadd (bvadd (bvadd op1_1 op2_1) op3_1) op4_1))
  (= out_1 (bvor (bvor (bvor op1_1 op2_1) op3_1) op4_1))))
(assert (ite (= func_2 (_ bv1 1))
  (= out_2 (bvadd (bvadd (bvadd op1_2 op2_2) op3_2) op4_2))
  (= out_2 (bvor (bvor (bvor op1_2 op2_2) op3_2) op4_2))))
(assert (= mode_1 mode_2))
(assert (not (= out_1 out_2)))
(check-sat)
";

/// `(= y (ite m x k))`: a bit-vector `ite` below an authored equality, its
/// guard and its else-branch both nullary macros. MEASURED at b9818f6c4 (no
/// commit since touches the bridge): `foreign_assumes=yes`, carcara `invalid`.
const ITE_UNDER_EQUALITY: &str = "(set-logic QF_BV)
(declare-const x (_ BitVec 4))
(declare-const y (_ BitVec 4))
(declare-const c (_ BitVec 1))
(define-fun m () Bool (= c #b1))
(define-fun k () (_ BitVec 4) #x3)
(assert (= y (ite m x k)))
(assert (= c #b1))
(assert (not (= y x)))
(check-sat)
";

/// A guard macro whose own body is an `ite` over another macro: the body is
/// bridged by the same schema and joined with `trans`. MEASURED at b9818f6c4:
/// `foreign_assumes=yes`, carcara `invalid`.
const ITE_MACRO_BODY: &str = "(set-logic QF_BV)
(declare-const x (_ BitVec 4))
(declare-const c (_ BitVec 1))
(declare-const d (_ BitVec 1))
(define-fun n () Bool (= d #b0))
(define-fun m () Bool (ite n (= c #b1) (= c #b0)))
(assert (ite m (= x #x1) (= x #x2)))
(assert (= c #b1))
(assert (= d #b0))
(assert (not (= x #x1)))
(check-sat)
";

/// NEGATIVE CONTROL: `(ite m a b)` over `(define-fun m () Bool (not p))`.
/// The term store orients `(ite (not p) a b)` as `(ite p b a)`, so `cong`
/// under `ite` cannot line the operands up and the bridge declines. Whatever
/// AY then does, it must not publish that root's expanded text as a premise.
const ITE_FLIPPED_BY_NORMALIZATION: &str = "(set-logic QF_UF)
(declare-const p Bool)
(declare-const a Bool)
(declare-const b Bool)
(define-fun m () Bool (not p))
(assert (ite m a b))
(assert (not a))
(assert (not b))
(check-sat)
";

/// The certificate line's fields.
pub(super) fn has_field(line: &str, field: &str) -> bool {
    line.split_whitespace().any(|word| word == field)
}

/// Every route: an `unsat` that prints a document assumes only assertions as
/// written and nullary definitions' equations. Returns the routes' verdicts.
pub(super) fn strict_routes_assume_only_problem_premises(
    name: &str,
    script: &str,
) -> Vec<Vec<String>> {
    let authored = authored_assertions(script);
    let definitions = nullary_definition_premises(script);
    let mut verdicts = Vec::new();
    for route in ALL_ROUTES {
        let outcome = run_route(route, script);
        let context = format!("{name}: {}", outcome.context);
        if outcome.verdicts == ["unsat"] && !matches!(route, StrictRoute::StdinPlain) {
            let assumes = premise_assumes(&outcome.document);
            assert!(!assumes.is_empty(), "unsat without its premises: {context}");
            for assume in &assumes {
                assert!(
                    authored.contains(assume) || definitions.contains(assume),
                    "strict published a certificate assuming `{assume}`, neither an assertion \
                     nor a nullary definition's equation: {context}"
                );
            }
        }
        verdicts.push(outcome.verdicts);
    }
    verdicts
}

/// Default mode: the certificate line, or `None` when no certificate was
/// written, after replaying pinned carcara on the written certificate in both
/// invocations AY's gates have used. A document carcara does not answer
/// `valid` must be labelled `trust_free=no` with the cause named
/// (`foreign_assumes=yes` or an unproved step).
pub(super) fn default_certificate_is_honest(
    name: &str,
    script: &str,
) -> Option<(String, Vec<String>)> {
    let dir = tempfile::tempdir().expect("tempdir");
    let smt2 = dir.path().join("query.smt2");
    let proof = dir.path().join("query.smt2.alethe");
    std::fs::write(&smt2, script).expect("write query");
    let output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .arg(&smt2)
        .output_timeout(QUERY_TIMEOUT)
        .expect("run ay");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    let context = format!("{name}\nstdout:\n{stdout}\nstderr:\n{stderr}");
    let line = stderr
        .lines()
        .find(|l| l.contains("c ay.proof.certificate "))?
        .to_string();
    assert_eq!(verdict_lines(&stdout), ["unsat"], "{context}");
    let mut verdicts = Vec::new();
    for flags in [&[][..], &["--expand-let-bindings"][..]] {
        let Some((verdict, checker_stderr)) = pinned_carcara_verdict_in(&smt2, &proof, flags)
        else {
            continue;
        };
        let disclosed = has_field(&line, "trust_free=no")
            && (has_field(&line, "foreign_assumes=yes") || !has_field(&line, "unproved_steps=0"));
        assert!(
            verdict == "valid" || disclosed,
            "pinned carcara {flags:?} answered `{verdict}` on a certificate labelled `{line}`: \
             {checker_stderr}\n{context}"
        );
        verdicts.push(format!("{flags:?}: {verdict} {checker_stderr}"));
    }
    Some((format!("{line}\n{context}"), verdicts))
}

#[test]
#[timeout(1_200_000)]
fn an_ite_over_a_nullary_bool_macro_is_assumed_as_written() {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join(SHARED_VARS);
    let shared_vars =
        std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
    // (name, script, the `ite` guard's definition premise)
    for (name, script, guard) in [
        (
            "bv_ite_shared_vars_minimal",
            shared_vars.as_str(),
            "(= m1 (= mode_1 (_ bv0 1)))",
        ),
        (
            "bv_ite_concat_extract_4op",
            CONCAT_EXTRACT_4OP,
            "(= v18 (= mode_1 (_ bv0 1)))",
        ),
        ("ite_under_equality", ITE_UNDER_EQUALITY, "(= m (= c #b1))"),
        (
            "ite_macro_body",
            ITE_MACRO_BODY,
            "(= m (ite n (= c #b1) (= c #b0)))",
        ),
    ] {
        let authored = authored_assertions(script);
        let definitions = nullary_definition_premises(script);
        assert!(
            definitions.iter().any(|definition| definition == guard),
            "{name}: {definitions:?}"
        );

        // Strict: every route publishes `unsat` on a certificate that assumes
        // the `ite` as written and reads its guard through the definition.
        let verdicts = strict_routes_assume_only_problem_premises(name, script);
        assert!(
            verdicts.iter().all(|v| v == &["unsat"]),
            "{name}: {verdicts:?}"
        );
        let outcome = run_route(StrictRoute::File, script);
        let context = format!("{name}: {}", outcome.context);
        let assumes = premise_assumes(&outcome.document);
        assert!(
            assumes
                .iter()
                .any(|assume| assume.contains("(ite ") && authored.contains(assume)),
            "the macro-guarded `ite` is assumed as written: {context}"
        );
        assert!(
            assumes.iter().any(|assume| assume == guard),
            "the certificate reads the `ite` guard through its definition premise: {context}"
        );

        // Default mode: honest whatever carcara says, and in fact `valid`.
        let (line, carcara) = default_certificate_is_honest(name, script)
            .unwrap_or_else(|| panic!("{name}: no certificate written"));
        assert!(
            carcara.iter().all(|verdict| verdict.contains(": valid ")),
            "{name}: {carcara:?}\n{line}"
        );
        for field in [
            "unproved_steps=0",
            "foreign_assumes=no",
            "trust_free=yes",
            "ay_self_checkable=yes",
            "carcara_surface=supported",
        ] {
            assert!(
                has_field(line.lines().next().unwrap_or(""), field),
                "{field}: {line}"
            );
        }
    }
}

/// NEGATIVE CONTROL of the `ite` arm: a guard whose normalization flips the
/// branches is not bridged, and AY neither publishes its expanded root as a
/// strict premise nor labels a document carcara rejects trust-free.
#[test]
#[timeout(600_000)]
fn an_unbridged_macro_guard_never_publishes_a_trust_free_foreign_premise() {
    let name = "ite_flipped_by_normalization";
    strict_routes_assume_only_problem_premises(name, ITE_FLIPPED_BY_NORMALIZATION);
    default_certificate_is_honest(name, ITE_FLIPPED_BY_NORMALIZATION);
}
