// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::{capture_alethe_dialect_report, with_alethe_dialect, AletheDialect, CleanOnlySpelling};

#[test]
fn clean_zero_extend_zero_complete_words_carry_the_operand_bits() {
    for width in [1, 8, 64, 128] {
        let mut f = Fixture::new();
        let byte = f.bv("byte", width);
        let extended = f.indexed("zero_extend", vec![0], byte, width);
        let nested = f.indexed("zero_extend", vec![0], extended, width);
        let equality = f.equals(nested, byte);
        let assertion = f.not(equality);
        let (document, report) = capture_alethe_dialect_report(|| {
            with_alethe_dialect(AletheDialect::Clean, || f.refute(assertion))
        });
        let document = document.expect("zero extension0 uses the checked operand identity");
        assert_complete(&document);
        assert!(document.contains(".zx0"));
        assert_eq!(
            report.first_clean_only(),
            Some(CleanOnlySpelling::ZeroExtendAsConcat)
        );
        let printer = AlethePrinter::new(&f.terms);
        let assertion = printer.format_term(assertion);
        let problem = format!("(set-logic QF_BV)\n(declare-const byte (_ BitVec {width}))\n(assert {assertion})\n(check-sat)\n");
        let proof = format!("(assume a {assertion})\n{document}\n(step done (cl) :rule resolution :premises (a t1))\n");
        let envelope = serde_json::json!({"type":"alethe_certificate","version":"1.0","problem":problem,"proof":proof});
        let dir = std::env::temp_dir().join(format!("ay-zero-extend-zero-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let path = dir.join(format!("complete-clean-{width}.json"));
        std::fs::write(&path, serde_json::to_vec_pretty(&envelope).unwrap()).unwrap();
        println!("zero-extension replay: {}", path.display());
    }
}

#[test]
fn zero_extend_zero_complete_keeps_pinned_opacity_and_rejects_wrong_word() {
    let mut f = Fixture::new();
    let byte = f.bv("byte", 4);
    let other = f.bv("other", 4);
    let extended = f.indexed("zero_extend", vec![0], byte, 4);
    let right = f.equals(extended, byte);
    let right = f.not(right);
    assert!(with_alethe_dialect(AletheDialect::PinnedCarcara, || f.refute(right)).is_none());
    let wrong = f.equals(extended, other);
    let wrong = f.not(wrong);
    assert!(with_alethe_dialect(AletheDialect::Clean, || f.refute(wrong)).is_none());
}
