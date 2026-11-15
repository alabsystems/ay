// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The dialect selection, its report, and pinned-Carcara replays of both
//! lanes that print `bitblast_ashr` and `zero_extend`.
//!
//! REGRESSION (475ba9547, measured 2026-09-29): both `bitblast_ashr` printers
//! switched to Clean's sign-filled final layer, which pinned Carcara 9a352ee
//! refuses (`checking failed on step .. with rule 'bitblast_ashr'`), while the
//! certificate still said `carcara_surface=supported`. The Clean spelling
//! stays the default; every render now REPORTS it, and
//! `AletheDialect::PinnedCarcara` prints the zero fill pinned Carcara accepts.
//! A positive replay passes only on a literal `valid`; the replays are skipped
//! with a note when `carcara` is not on `PATH`, and the structural and report
//! pins run either way.

use super::super::AlethePrinter;
use super::*;
use ay_core::{ProofId, Sort, Symbol, TermId, TermStore};
use num_bigint::BigInt;
use std::collections::HashMap;
use std::fmt::Write as _;
use std::process::Command;

#[path = "dialect_divider_tests.rs"]
mod divider;
#[path = "dialect_dt_project_tests.rs"]
mod dt_project;
#[path = "dialect_let_rule_tests.rs"]
mod let_rule;
#[path = "dialect_zero_extend_tests.rs"]
mod zero_extend;
#[path = "dialect_zero_extend_identity_tests.rs"]
mod zero_extend_identity;

const SIGN: CleanOnlySpelling = CleanOnlySpelling::SignFilledAshrOvershift;
const ZERO_EXTEND: CleanOnlySpelling = CleanOnlySpelling::ZeroExtendAsConcat;

/// Pinned Carcara's last stdout line and its stderr, or `None` when absent.
fn carcara_verdict(case: &str, problem: &str, proof: &str) -> Option<(String, String)> {
    if let Err(misjudged) = ay_core::pinned_carcara::pinned_carcara_can_judge(problem, proof) {
        panic!("{case}: {misjudged}\n{proof}");
    }
    let probe = Command::new("carcara").arg("--version").output();
    if !probe.is_ok_and(|probe| probe.status.success()) {
        eprintln!("carcara not on PATH: the {case} replay is skipped");
        return None;
    }
    let dir = std::env::temp_dir().join(format!("ay-dialect-{}-{case}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("replay directory");
    std::fs::write(dir.join("p.smt2"), problem).expect("write the problem");
    std::fs::write(dir.join("p.alethe"), proof).expect("write the proof");
    let output = Command::new("carcara")
        .args(["check", "--expand-let-bindings", "--"])
        .arg(dir.join("p.alethe"))
        .arg(dir.join("p.smt2"))
        .output()
        .expect("run carcara");
    let _ = std::fs::remove_dir_all(&dir);
    let stdout = String::from_utf8_lossy(&output.stdout);
    let verdict = stdout.lines().last().unwrap_or("").trim().to_string();
    Some((verdict, String::from_utf8_lossy(&output.stderr).to_string()))
}

/// NEGATIVE CONTROL: the replay refuses, before the checker runs (so with or
/// without carcara on PATH), the pair pinned carcara prints `valid` for only
/// through its `evaluate` defect (`ay_core::pinned_carcara`), so neither the
/// `valid` assertions nor the disclosed refusals' not-`valid` can pass on it.
#[test]
#[should_panic(expected = "is not evidence")]
fn the_carcara_replay_refuses_a_document_pinned_carcara_misjudges() {
    carcara_verdict(
        "false_valid_control",
        ay_core::pinned_carcara::FALSE_VALID_CONTROL_PROBLEM,
        ay_core::pinned_carcara::FALSE_VALID_CONTROL_PROOF,
    );
}

fn assert_pinned_valid(case: &str, problem: &str, proof: &str) {
    if let Some((verdict, stderr)) = carcara_verdict(case, problem, proof) {
        assert_eq!(verdict, "valid", "{case}: {stderr}\n{proof}");
    }
}

/// The disclosure is true: pinned Carcara refuses the document, at `rule`.
fn assert_pinned_refuses_at(case: &str, problem: &str, proof: &str, rule: &str) {
    if let Some((verdict, stderr)) = carcara_verdict(case, problem, proof) {
        assert_ne!(
            verdict, "valid",
            "{case}: a disclosed Clean-only step was accepted"
        );
        assert!(
            stderr.contains(&format!("with rule '{rule}'")),
            "{case}: refused, but not at {rule}: {stderr}"
        );
    }
}

/// The top-level items of one printed s-expression `(a (b c) d)`.
fn top_level(list: &str) -> Vec<&str> {
    let inner = list
        .strip_prefix('(')
        .and_then(|rest| rest.strip_suffix(')'))
        .unwrap_or_else(|| panic!("not a list: {list}"));
    let (mut items, mut depth, mut start) = (Vec::new(), 0usize, None);
    for (index, byte) in inner.bytes().enumerate() {
        match byte {
            b'(' => {
                depth += 1;
                start.get_or_insert(index);
            }
            b')' => depth -= 1,
            b' ' if depth == 0 => {
                if let Some(begin) = start.take() {
                    items.push(&inner[begin..index]);
                }
            }
            _ => {
                start.get_or_insert(index);
            }
        }
    }
    if let Some(begin) = start {
        items.push(&inner[begin..]);
    }
    items
}

fn concat_bits(terms: &mut TermStore, bits: &[TermId]) -> TermId {
    if bits.len() == 1 {
        return bits[0];
    }
    let half = bits.len() / 2;
    let low = concat_bits(terms, &bits[..half]);
    let high = concat_bits(terms, &bits[half..]);
    let width = u32::try_from(bits.len()).expect("a narrow word");
    terms.mk_app(Symbol::named("concat"), [high, low], Sort::bitvec(width))
}

/// A closed problem and proof around one packed identity `equality` over the
/// free word `byte`, with the packed steps alone.
fn packed_certificate(terms: &TermStore, equality: TermId, width: u32) -> [String; 3] {
    let printer = AlethePrinter::new(terms);
    let steps = printer
        .format_bv_packed_identity(ProofId(7), &[equality])
        .unwrap_or_else(|| panic!("{} renders", printer.format_term(equality)));
    let assertion = format!("(not {})", printer.format_term(equality));
    let problem = format!(
        "(set-logic QF_BV)\n(declare-const byte (_ BitVec {width}))\n(assert {assertion})\n(check-sat)\n"
    );
    let proof = format!(
        "(assume a {assertion})\n{steps}(step done (cl) :rule resolution :premises (a t7))\n"
    );
    [problem, proof, steps]
}

/// `(bvashr byte #amount)` equated to its SMT-LIB meaning spelled with
/// `extract`/`concat`, rendered by the packed lane.
fn packed_ashr(width: u32, amount: u32) -> [String; 3] {
    let mut terms = TermStore::new();
    let byte = terms.mk_var("byte", Sort::bitvec(width));
    let count = terms.mk_bitvec(BigInt::from(amount), width);
    let shifted = terms.mk_app(Symbol::named("bvashr"), [byte, count], Sort::bitvec(width));
    let expected: Vec<TermId> = (0..width)
        .map(|bit| {
            let source = (bit + amount).min(width - 1);
            let extract = Symbol::indexed("extract", vec![source, source]);
            terms.mk_app(extract, [byte], Sort::bitvec(1))
        })
        .collect();
    let expected = concat_bits(&mut terms, &expected);
    let equality = terms.mk_app(Symbol::named("="), [shifted, expected], Sort::Bool);
    packed_certificate(&terms, equality, width)
}

/// The overshift fill of every final-layer bit of the `bitblast_ashr` step.
fn packed_ashr_fills(steps: &str) -> Vec<String> {
    let definitions: HashMap<&str, &str> = steps
        .lines()
        .filter(|line| line.starts_with("(define-fun "))
        .map(|line| (top_level(line)[1], top_level(line)[4]))
        .collect();
    let step = steps
        .lines()
        .find(|line| line.ends_with(":rule bitblast_ashr)"))
        .unwrap_or_else(|| panic!("no bitblast_ashr step in\n{steps}"));
    let blasted = top_level(top_level(top_level(step)[2])[1])[2];
    let word = top_level(definitions[blasted]);
    assert_eq!(word[0], "@bbterm", "{step}");
    word[1..]
        .iter()
        .map(|bit| top_level(definitions[bit])[3].to_string())
        .collect()
}

/// A complete bit-blast refutation of `assertion` over the declared words.
fn complete_blast(terms: &TermStore, assertion: TermId, words: &[(&str, u32)]) -> [String; 3] {
    let mut terms = terms.clone();
    let literal = terms.mk_not_raw(assertion);
    let printer = AlethePrinter::new(&terms);
    let spelled = printer.format_term(assertion);
    let document = printer
        .format_bv_complete_blast_refutation(ProofId(1), &[literal])
        .unwrap_or_else(|| panic!("{spelled} renders"));
    assert!(!document.contains(":rule hole"), "{document}");
    let mut declarations = String::new();
    for (name, width) in words {
        let _ = writeln!(declarations, "(declare-const {name} (_ BitVec {width}))");
    }
    let problem = format!("(set-logic QF_BV)\n{declarations}(assert {spelled})\n(check-sat)\n");
    let proof = format!(
        "(assume h {spelled})\n{document}\n(step done (cl) :rule resolution :premises (h t1))\n"
    );
    [problem, proof, document]
}

/// `(extract top low (bvashr a #amount))` equals the sign bit repeated: the
/// meaning of `bvashr` over a symbolic sign, refuted by complete bit-blasting.
fn complete_blast_ashr(width: u32, amount: u32) -> [String; 3] {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::bitvec(width));
    let count = terms.mk_bitvec(BigInt::from(amount), width);
    let shifted = terms.mk_app(Symbol::named("bvashr"), [a, count], Sort::bitvec(width));
    let largest_non_negative = terms.mk_bitvec(BigInt::from((1_u32 << (width - 1)) - 1), width);
    let negative = terms.mk_app(
        Symbol::named("bvult"),
        [largest_non_negative, a],
        Sort::Bool,
    );
    let (top, low) = (width - 1, width - 1 - amount);
    let high_bits = terms.mk_app(
        Symbol::indexed("extract", vec![top, low]),
        [shifted],
        Sort::bitvec(amount + 1),
    );
    let ones = terms.mk_bitvec(BigInt::from((1_u32 << (amount + 1)) - 1), amount + 1);
    let zeros = terms.mk_bitvec(BigInt::from(0), amount + 1);
    let fill = terms.mk_ite_raw(negative, ones, zeros);
    let equality = terms.mk_app(Symbol::named("="), [high_bits, fill], Sort::Bool);
    let assertion = terms.mk_not_raw(equality);
    complete_blast(&terms, assertion, &[("a", width)])
}

fn pinned<R>(render: impl FnOnce() -> R) -> (R, AletheDialectReport) {
    capture_alethe_dialect_report(|| with_alethe_dialect(AletheDialect::PinnedCarcara, render))
}

#[test]
fn the_dialect_and_its_report_are_scoped() {
    assert_eq!(current(), AletheDialect::Clean, "Clean is the default");
    let (inner, report) = capture_alethe_dialect_report(|| {
        with_alethe_dialect(AletheDialect::PinnedCarcara, || {
            let declined = attempt(|| {
                note_clean_only(ZERO_EXTEND);
                None::<()>
            });
            assert_eq!(declined, None);
            discarding_notes(|| note_clean_only(ZERO_EXTEND));
            let (kept, nested) = capture_alethe_dialect_report(|| {
                attempt(|| {
                    note_clean_only(SIGN);
                    Some(())
                })
            });
            assert_eq!(kept, Some(()));
            assert_eq!(nested.first_clean_only(), Some(SIGN));
            current()
        })
    });
    assert_eq!(inner, AletheDialect::PinnedCarcara);
    assert_eq!(current(), AletheDialect::Clean, "the selection is restored");
    assert_eq!(
        report.first_clean_only(),
        Some(SIGN),
        "nested notes reach the outer capture"
    );
    assert_eq!(
        report.clean_only_notes(),
        1,
        "a declined lane or a preflight keeps nothing"
    );
    let unwound = std::panic::catch_unwind(|| {
        with_alethe_dialect(AletheDialect::PinnedCarcara, || panic!("a render unwinds"))
    });
    assert!(unwound.is_err());
    assert_eq!(
        current(),
        AletheDialect::Clean,
        "an unwinding render restores it too"
    );
    assert!(SIGN.has_pinned_spelling() && !ZERO_EXTEND.has_pinned_spelling());
}

/// The packed lane: Clean's sign fill by default, reported, and refused by
/// pinned Carcara at `bitblast_ashr`; the pinned dialect's zero fill, not
/// reported, and a literal `valid`.
#[test]
fn packed_ashr_follows_the_dialect_and_the_clean_fill_is_disclosed() {
    for (width, amount) in [(1_u32, 0_u32), (4, 1), (8, 3), (8, 7), (64, 0), (64, 63)] {
        let case = format!("packed-ashr-{width}-{amount}");
        let ([problem, proof, steps], report) =
            capture_alethe_dialect_report(|| packed_ashr(width, amount));
        let sign = format!("((_ @bit_of {}) byte)", width - 1);
        assert!(
            packed_ashr_fills(&steps).iter().all(|fill| *fill == sign),
            "{case}\n{steps}"
        );
        assert_eq!(report.first_clean_only(), Some(SIGN), "{case}");
        assert_pinned_refuses_at(&format!("{case}-clean"), &problem, &proof, "bitblast_ashr");

        let ([problem, proof, steps], report) = pinned(|| packed_ashr(width, amount));
        assert!(
            packed_ashr_fills(&steps).iter().all(|fill| fill == "false"),
            "{case}\n{steps}"
        );
        assert!(report.is_pinned_spelling(), "{case}: {report:?}");
        assert_pinned_valid(&format!("{case}-pinned"), &problem, &proof);
    }
}

/// NEGATIVE TWIN: a literal amount AT the width over a symbolic sign is
/// exactly where the pinned zero fill is false, so neither dialect spells it
/// `bitblast_ashr`; it renders through the closed-case evaluation instead.
#[test]
fn packed_ashr_overshift_is_never_spelled_bitblast_ashr() {
    for width in [1_u32, 4] {
        for (dialect, name) in [
            (AletheDialect::Clean, "clean"),
            (AletheDialect::PinnedCarcara, "pinned"),
        ] {
            let case = format!("packed-ashr-overshift-{width}-{name}");
            let ([problem, proof, steps], report) = capture_alethe_dialect_report(|| {
                with_alethe_dialect(dialect, || packed_ashr(width, width))
            });
            assert!(!steps.contains(":rule bitblast_ashr"), "{case}:\n{steps}");
            assert!(!steps.contains(":rule hole"), "{case}:\n{steps}");
            assert!(report.is_pinned_spelling(), "{case}: {report:?}");
            assert_pinned_valid(&case, &problem, &proof);
        }
    }
}

/// The complete bit-blast lane, over a symbolic sign and literal amounts
/// below the width (the only symbolic-sign instances the guard admits).
#[test]
fn complete_blast_ashr_follows_the_dialect_and_the_clean_fill_is_disclosed() {
    for (width, amount) in [(1_u32, 0_u32), (3, 1), (8, 7)] {
        let case = format!("cbb-ashr-{width}-{amount}");
        let ([problem, proof, document], report) =
            capture_alethe_dialect_report(|| complete_blast_ashr(width, amount));
        assert!(
            document.contains(":rule bitblast_ashr"),
            "{case}:\n{document}"
        );
        assert_eq!(report.first_clean_only(), Some(SIGN), "{case}");
        assert_pinned_refuses_at(&format!("{case}-clean"), &problem, &proof, "bitblast_ashr");

        let ([problem, proof, document], report) = pinned(|| complete_blast_ashr(width, amount));
        assert!(
            document.contains(":rule bitblast_ashr"),
            "{case}:\n{document}"
        );
        assert!(report.is_pinned_spelling(), "{case}: {report:?}");
        assert_pinned_valid(&format!("{case}-pinned"), &problem, &proof);
    }
}

/// NEGATIVE CONTROL of the disclosure: a sign bit that is literally `false`
/// fills identically in both dialects, so the documents are byte-identical
/// and nothing is reported; a logical shift reports nothing either.
#[test]
fn a_literally_false_sign_or_a_logical_shift_discloses_nothing() {
    let mut terms = TermStore::new();
    let z = terms.mk_var("z", Sort::bitvec(7));
    let b = terms.mk_var("b", Sort::bitvec(8));
    let top = terms.mk_bitvec(BigInt::from(0), 1);
    let a = terms.mk_app(Symbol::named("concat"), [top, z], Sort::bitvec(8));
    let ashr = terms.mk_app(Symbol::named("bvashr"), [a, b], Sort::bitvec(8));
    let lshr = terms.mk_app(Symbol::named("bvlshr"), [a, b], Sort::bitvec(8));
    let equality = terms.mk_app(Symbol::named("="), [ashr, lshr], Sort::Bool);
    let assertion = terms.mk_not_raw(equality);
    let words = [("z", 7), ("b", 8)];
    let (clean, clean_report) =
        capture_alethe_dialect_report(|| complete_blast(&terms, assertion, &words));
    let (pinned_render, pinned_report) = pinned(|| complete_blast(&terms, assertion, &words));
    assert!(clean[2].contains(":rule bitblast_ashr"), "{}", clean[2]);
    assert_eq!(
        clean, pinned_render,
        "a literally false sign bit is spelled identically"
    );
    assert!(clean_report.is_pinned_spelling(), "{clean_report:?}");
    assert!(pinned_report.is_pinned_spelling(), "{pinned_report:?}");
    assert_pinned_valid("cbb-ashr-non-negative", &clean[0], &clean[1]);

    for op in ["bvlshr", "bvshl"] {
        let mut terms = TermStore::new();
        let byte = terms.mk_var("byte", Sort::bitvec(8));
        let count = terms.mk_bitvec(BigInt::from(3), 8);
        let shifted = terms.mk_app(Symbol::named(op), [byte, count], Sort::bitvec(8));
        let equality = terms.mk_app(Symbol::named("="), [shifted, shifted], Sort::Bool);
        let ([problem, proof, _], report) =
            capture_alethe_dialect_report(|| packed_certificate(&terms, equality, 8));
        assert!(report.is_pinned_spelling(), "{op}: {report:?}");
        assert_pinned_valid(&format!("packed-{op}"), &problem, &proof);
    }
}

/// `zero_extend` over more symbolic bits than the packed lane's closed cases
/// admit (nine; the complete bit-blast lane prints no cases) has no pinned
/// spelling: both lanes rely on Clean's reading through a `refl` identity
/// (`zero_extend_identity::`), which pinned Carcara refuses, and both dialects
/// report it. `zero_extend::` covers the closed cases.
#[test]
fn zero_extend_has_no_pinned_spelling_and_is_disclosed_in_both_dialects() {
    let mut terms = TermStore::new();
    let byte = terms.mk_var("byte", Sort::bitvec(9));
    let extend = Symbol::indexed("zero_extend", vec![3]);
    let wide = terms.mk_app(extend, [byte], Sort::bitvec(12));
    let packed = terms.mk_app(Symbol::named("="), [wide, wide], Sort::Bool);

    let mut blast = TermStore::new();
    let a = blast.mk_var("a", Sort::bitvec(4));
    let wide = blast.mk_app(
        Symbol::indexed("zero_extend", vec![4]),
        [a],
        Sort::bitvec(8),
    );
    let narrow = blast.mk_app(
        Symbol::indexed("extract", vec![3, 0]),
        [wide],
        Sort::bitvec(4),
    );
    let equality = blast.mk_app(Symbol::named("="), [narrow, a], Sort::Bool);
    let assertion = blast.mk_not_raw(equality);

    for (dialect, name) in [
        (AletheDialect::Clean, "clean"),
        (AletheDialect::PinnedCarcara, "pinned"),
    ] {
        let ([problem, proof, steps], report) = capture_alethe_dialect_report(|| {
            with_alethe_dialect(dialect, || packed_certificate(&terms, packed, 9))
        });
        assert!(
            steps.contains("(concat (_ bv0 3) byte)"),
            "{name}:\n{steps}"
        );
        assert_eq!(report.first_clean_only(), Some(ZERO_EXTEND), "{name}");
        assert_pinned_refuses_at(&format!("packed-zext-{name}"), &problem, &proof, "refl");

        let ([problem, proof, _], report) = capture_alethe_dialect_report(|| {
            with_alethe_dialect(dialect, || complete_blast(&blast, assertion, &[("a", 4)]))
        });
        assert_eq!(report.first_clean_only(), Some(ZERO_EXTEND), "{name}");
        assert_pinned_refuses_at(&format!("cbb-zext-{name}"), &problem, &proof, "refl");
    }
}
