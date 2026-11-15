// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::TermStore;

fn concat_bits(terms: &mut TermStore, bits: &[TermId]) -> TermId {
    if bits.len() == 1 {
        return bits[0];
    }
    let half = bits.len() / 2;
    let low = concat_bits(terms, &bits[..half]);
    let high = concat_bits(terms, &bits[half..]);
    terms.mk_app(
        Symbol::named("concat"),
        [high, low],
        Sort::bitvec(bits.len() as u32),
    )
}

fn certificate(name: &str, terms: &TermStore, equality: TermId, width: u32) {
    let printer = AlethePrinter::new(terms);
    let steps = printer
        .format_bv_packed_identity(ProofId(7), &[equality])
        .expect(name);
    assert!(!steps.contains(":rule hole") && !steps.contains(":rule trust"));
    assert_eq!(
        steps.matches("(anchor ").count(),
        steps.matches(":discharge ").count()
    );
    let assertion = format!("(not {})", printer.format_term(equality));
    let problem = format!("(set-logic QF_BV)\n(declare-const byte (_ BitVec {width}))\n(assert {assertion})\n(check-sat)\n");
    let proof = format!(
        "(assume a {assertion})\n{steps}(step done (cl) :rule resolution :premises (a t7))\n"
    );
    let certificate = serde_json::json!({"type": "alethe_certificate", "version": "1.0", "problem": problem, "proof": proof});
    let path =
        std::env::temp_dir().join(format!("ay-packed-wire-{}-{name}.json", std::process::id()));
    std::fs::write(&path, serde_json::to_vec(&certificate).expect("JSON")).expect("certificate");
    println!("independent replay certificate: {}", path.display());
}

#[test]
fn packed_wire_closed_cases_export_original_extensions_and_shifts() {
    for (width, extended, op, amount) in [
        (1, 1, "bvshl", 0),
        (1, 1, "bvashr", 1),
        (2, 2, "bvashr", 1),
        (2, 2, "bvashr", 2),
        (8, 8, "bvashr", 3),
        (8, 64, "bvshl", 8),
        (8, 64, "bvshl", 56),
        (8, 64, "bvshl", 64),
        (8, 64, "bvlshr", 4),
        (8, 128, "bvshl", 120),
    ] {
        let mut terms = TermStore::new();
        let byte = terms.mk_var("byte", Sort::bitvec(width));
        let source = if width == extended {
            byte
        } else {
            terms.mk_app(
                Symbol::indexed("zero_extend", vec![extended - width]),
                [byte],
                Sort::bitvec(extended),
            )
        };
        let count = terms.mk_bitvec(amount.into(), extended);
        let shifted = terms.mk_app(Symbol::named(op), [source, count], Sort::bitvec(extended));
        let zero = terms.mk_bitvec(0.into(), 1);
        let mut expected = Vec::new();
        for bit in 0..extended {
            let input = match op {
                "bvshl" => (bit as i64) - amount as i64,
                _ => (bit as i64) + amount as i64,
            };
            let input = if op == "bvashr" && input >= extended as i64 {
                extended as i64 - 1
            } else {
                input
            };
            expected.push(if input < 0 || input >= width as i64 {
                zero
            } else {
                terms.mk_app(
                    Symbol::indexed("extract", vec![input as u32, input as u32]),
                    [byte],
                    Sort::bitvec(1),
                )
            });
        }
        let expected = concat_bits(&mut terms, &expected);
        let equality = terms.mk_app(Symbol::named("="), [shifted, expected], Sort::Bool);
        certificate(
            &format!("{op}-{width}-{extended}-{amount}"),
            &terms,
            equality,
            width,
        );
    }
}

#[test]
fn packed_wire_bitwise_or_reassembles_disjoint_bytes() {
    let mut terms = TermStore::new();
    let byte = terms.mk_var("byte", Sort::bitvec(8));
    let zero = terms.mk_bitvec(0.into(), 8);
    let low = terms.mk_app(Symbol::named("concat"), [zero, byte], Sort::bitvec(16));
    let high = terms.mk_app(Symbol::named("concat"), [byte, zero], Sort::bitvec(16));
    let actual = terms.mk_app(Symbol::named("bvor"), [low, high], Sort::bitvec(16));
    let expected = terms.mk_app(Symbol::named("concat"), [byte, byte], Sort::bitvec(16));
    let equality = terms.mk_app(Symbol::named("="), [actual, expected], Sort::Bool);
    certificate("disjoint-or", &terms, equality, 8);
}

#[test]
fn packed_wire_supports_wide_extensions_and_shift_congruence_but_refuses_bad_sorts() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("byte", Sort::bitvec(9));
    let extended = terms.mk_app(
        Symbol::indexed("zero_extend", vec![1]),
        [x],
        Sort::bitvec(10),
    );
    let equality = terms.mk_app(Symbol::named("="), [extended, extended], Sort::Bool);
    assert!(AlethePrinter::new(&terms)
        .format_bv_packed_identity(ProofId(0), &[equality])
        .is_some());
    let x = terms.mk_var("small", Sort::bitvec(2));
    let bad = terms.mk_app(
        Symbol::indexed("zero_extend", vec![2]),
        [x],
        Sort::bitvec(3),
    );
    let equality = terms.mk_app(Symbol::named("="), [bad, bad], Sort::Bool);
    assert!(AlethePrinter::new(&terms)
        .format_bv_packed_identity(ProofId(0), &[equality])
        .is_none());
    let shift = terms.mk_app(Symbol::named("bvshl"), [x, x], Sort::bitvec(2));
    let equality = terms.mk_app(Symbol::named("="), [shift, shift], Sort::Bool);
    assert!(AlethePrinter::new(&terms)
        .format_bv_packed_identity(ProofId(0), &[equality])
        .is_some());
}

#[test]
fn packed_wire_definitions_avoid_names_and_reject_changed_surface() {
    let mut terms = TermStore::new();
    let byte = terms.mk_var("byte", Sort::bitvec(2));
    let _reserved = terms.mk_var("__ay_packed_7_0!reserved", Sort::Bool);
    let zero = terms.mk_bitvec(0.into(), 2);
    let expected = terms.mk_app(Symbol::named("concat"), [zero, byte], Sort::bitvec(4));
    let extended = terms.mk_app(
        Symbol::indexed("zero_extend", vec![2]),
        [byte],
        Sort::bitvec(4),
    );
    let equality = terms.mk_app(Symbol::named("="), [extended, expected], Sort::Bool);
    let proof = AlethePrinter::new(&terms)
        .format_bv_packed_identity(ProofId(7), &[equality])
        .expect("extension");
    assert!(proof.contains("(define-fun __ay_packed_7_1!"));
    let mut overrides = DetHashMap::default();
    overrides.insert(extended, "#b0000".into());
    assert!(AlethePrinter::new_with_overrides(&terms, Some(&overrides))
        .format_bv_packed_identity(ProofId(7), &[equality])
        .is_none());
}

#[test]
fn packed_wire_bounds_the_checkers_constant_shift_evaluation() {
    for (width, op, amount) in [(2, "bvashr", 3_u128), (64, "bvshl", u64::MAX as u128)] {
        let mut terms = TermStore::new();
        let byte = terms.mk_var("byte", Sort::bitvec(1));
        let source = terms.mk_app(
            Symbol::indexed("zero_extend", vec![width - 1]),
            [byte],
            Sort::bitvec(width),
        );
        let amount = terms.mk_bitvec(amount.into(), width);
        let shifted = terms.mk_app(Symbol::named(op), [source, amount], Sort::bitvec(width));
        let equality = terms.mk_app(Symbol::named("="), [shifted, shifted], Sort::Bool);
        assert!(AlethePrinter::new(&terms)
            .format_bv_packed_identity(ProofId(7), &[equality])
            .is_none());
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

/// REGRESSION: Clean's vendored Carcara (since Clean 8f12024e4) builds a
/// `bitblast_ashr` step's expected bits with the overshift fill set to the
/// SIGN bit, as SMT-LIB `bvashr` requires, and compares the printed term
/// syntactically. AY spelled the fill `false`, so Clean rejected every packed
/// arithmetic-shift step (11 external-codegen proof-database rows, measured against
/// Clean 5390f432b). Each result bit of the blasted word must be
/// `(ite GUARD STAGE FILL)` with FILL the source's top bit for `bvashr` and
/// `false` for `bvlshr`/`bvshl`.
#[test]
fn packed_literal_shift_spells_the_overshift_fill_as_the_consumer_rule_does() {
    for (op, rule, width, amount) in [
        ("bvashr", "bitblast_ashr", 4_u32, 1_u32),
        ("bvashr", "bitblast_ashr", 8, 3),
        ("bvashr", "bitblast_ashr", 64, 0),
        ("bvlshr", "bitblast_lshr", 8, 3),
        ("bvshl", "bitblast_shl", 8, 3),
    ] {
        let mut terms = TermStore::new();
        let byte = terms.mk_var("byte", Sort::bitvec(width));
        let count = terms.mk_bitvec(amount.into(), width);
        let shifted = terms.mk_app(Symbol::named(op), [byte, count], Sort::bitvec(width));
        let equality = terms.mk_app(Symbol::named("="), [shifted, shifted], Sort::Bool);
        let printer = AlethePrinter::new(&terms);
        let steps = printer
            .format_bv_packed_identity(ProofId(7), &[equality])
            .unwrap_or_else(|| panic!("{op} {width} by {amount} renders"));
        let definitions: std::collections::HashMap<&str, &str> = steps
            .lines()
            .filter(|line| line.starts_with("(define-fun "))
            .map(|line| {
                let items = top_level(line);
                (items[1], items[4])
            })
            .collect();
        let step = steps
            .lines()
            .find(|line| line.ends_with(&format!(":rule {rule})")))
            .unwrap_or_else(|| panic!("{op}: no {rule} step in\n{steps}"));
        let clause = top_level(top_level(step)[2]);
        let blasted = top_level(clause[1])[2];
        let word = top_level(definitions[blasted]);
        assert_eq!(word[0], "@bbterm");
        assert_eq!(word.len() as u32, width + 1);
        let fill = if op == "bvashr" {
            format!("((_ @bit_of {}) byte)", width - 1)
        } else {
            "false".to_owned()
        };
        for bit in &word[1..] {
            let selection = top_level(definitions[bit]);
            assert_eq!(selection[0], "ite", "{op}: {bit}");
            assert_eq!(
                selection[3], fill,
                "{op} {width} by {amount}: overshift fill of {bit}"
            );
        }
    }
}
