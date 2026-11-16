// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A frame macro read once per loaded byte is assumed as written: the
//! printer's definition schema bridges the macro's body once and cites that
//! step at every later read (`ay-proof`,
//! `alethe_printer/authored_assume/nullary_definition/shared_body.rs`).
//!
//! MEASURED at 4373bc24b (carcara 1.1.0, git 9a352ee): the `frame` and
//! `saved` macros of `positive-registers.smt2` read back as a FIVE-byte
//! little-endian load under `distinct` answered `unsat` with
//! `foreign_assumes=yes trust_free=no`, pinned carcara answered `invalid`
//! ("could not match term to any of the original problem premises"), and
//! `--strict-proofs` withheld `unsat`. Deriving `saved`'s 16-store body again
//! at each of the five reads needed 263 of the bridge's 256 nodes; a
//! four-byte load (218 nodes) was already `valid`. With the body shared, the
//! five-byte load plans in 80 nodes and the seven-byte one in 92.
//!
//! The fixture itself (two eight-byte loads) still exceeds the structural
//! canonical-render bound the planner checks before any bridge
//! (`authored_assume/bounds.rs`: 2,179 expanded canonical nodes, metered at
//! 32 bytes each, over the 64 KiB payload bound), so it keeps the honest
//! foreign label: the negative control.

use super::ite_guard::{
    default_certificate_is_honest, has_field, strict_routes_assume_only_problem_premises,
};
use super::*;
use std::fmt::Write as _;

const FRAME_FIXTURE: &str =
    "crates/ay-dpll/tests/fixtures/source_bound_stack_frame/positive-registers.smt2";

/// An `or` of `distinct`s over two reads of the same array macro, bridged by
/// `cong` under both heads before the body was shared too; the second read
/// now cites the first one's body step.
const OR_OF_DISTINCT_READS: &str = "(set-logic QF_ABV)
(declare-fun mem () (Array (_ BitVec 64) (_ BitVec 8)))
(declare-fun sp () (_ BitVec 64))
(declare-fun x () (_ BitVec 8))
(define-fun frame () (_ BitVec 64) (bvsub sp (_ bv16 64)))
(define-fun saved () (Array (_ BitVec 64) (_ BitVec 8)) (store mem frame x))
(assert (or (distinct (select saved frame) x) (distinct x (select saved frame))))
(check-sat)
";

fn frame_fixture() -> String {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join(FRAME_FIXTURE);
    std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()))
}

/// The fixture's declarations, alignment guards and macros, asserting that a
/// `bytes`-byte little-endian load of the saved frame differs from the low
/// bytes of `entry_fp` (stored there, so `unsat`).
fn frame_load(bytes: usize) -> String {
    let mut load = format!("(select saved (bvadd frame (_ bv{} 64)))", bytes - 1);
    for offset in (0..bytes - 1).rev() {
        load = format!("(concat {load} (select saved (bvadd frame (_ bv{offset} 64))))");
    }
    let mut script = {
        let fixture = frame_fixture();
        let mut script = String::new();
        for line in fixture
            .lines()
            .filter(|line| !line.starts_with("(assert (or ") && *line != "(check-sat)")
        {
            writeln!(&mut script, "{line}").expect("writing to a String cannot fail");
        }
        script
    };
    script.push_str(&format!(
        "(assert (distinct {load} ((_ extract {} 0) entry_fp)))\n(check-sat)\n",
        8 * bytes - 1
    ));
    script
}

#[test]
#[timeout(1_200_000)]
fn a_frame_macro_read_once_per_byte_is_assumed_as_written() {
    let five = frame_load(5);
    let seven = frame_load(7);
    for (name, script) in [
        ("five_byte_frame_load", five.as_str()),
        ("seven_byte_frame_load", seven.as_str()),
        ("or_of_distinct_reads", OR_OF_DISTINCT_READS),
    ] {
        let authored = authored_assertions(script);
        let definitions = nullary_definition_premises(script);
        let saved = definitions
            .iter()
            .find(|definition| definition.starts_with("(= saved "))
            .unwrap_or_else(|| panic!("{name}: {definitions:?}"));

        // Strict: every route publishes `unsat` on a certificate that assumes
        // only assertions as written and definition equations.
        let verdicts = strict_routes_assume_only_problem_premises(name, script);
        assert!(
            verdicts.iter().all(|v| v == &["unsat"]),
            "{name}: {verdicts:?}"
        );
        let outcome = run_route(StrictRoute::File, script);
        let context = format!("{name}: {}", outcome.context);
        let assumes = premise_assumes(&outcome.document);
        assert!(
            assumes.iter().any(|assume| {
                (assume.starts_with("(distinct ") || assume.starts_with("(or "))
                    && authored.contains(assume)
            }),
            "the macro-reading assertion is assumed as written: {context}"
        );
        assert!(
            assumes.iter().any(|assume| assume == saved),
            "the certificate reads `saved` through its definition premise: {context}"
        );

        // Default mode: honest whatever carcara says, and in fact `valid`.
        let (line, carcara) = default_certificate_is_honest(name, script)
            .unwrap_or_else(|| panic!("{name}: no certificate written"));
        assert!(
            carcara.iter().all(|verdict| verdict.contains(": valid ")),
            "{name}: {carcara:?}\n{line}"
        );
        for field in ["unproved_steps=0", "foreign_assumes=no", "trust_free=yes"] {
            assert!(
                has_field(line.lines().next().unwrap_or(""), field),
                "{field}: {line}"
            );
        }
    }
}

/// NEGATIVE CONTROL: past the canonical-render bound nothing is bridged, and
/// AY neither publishes the expanded root as a strict premise nor labels a
/// document carcara rejects trust-free.
#[test]
#[timeout(600_000)]
fn a_frame_load_past_the_render_bound_keeps_an_honest_label() {
    let name = "positive_registers";
    let script = frame_fixture();
    strict_routes_assume_only_problem_premises(name, &script);
    default_certificate_is_honest(name, &script);
}
