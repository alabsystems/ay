// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `bitblast_udiv` / `bitblast_urem` in both dialects, replayed through
//! pinned Carcara 9a352ee.
//!
//! REGRESSION (e9b297e37, measured 2026-09-30 on 938ec0327): the complete
//! bit-blast lane spells every divider step with Clean's fixed divider,
//! pinned Carcara refuses it ("expected terms to be equal", 20 of 20 closed
//! `bvudiv`/`bvurem` probes), and the render reported nothing, so the
//! certificate said `carcara_surface=supported`. Now the render reports
//! `FixedDivider`, and the pinned dialect prints pinned Carcara's divider
//! where it is true (a zero divisor, closed operands it divides correctly),
//! where the replay must be a literal `valid`. Everywhere else both dialects
//! keep Clean's divider and report it; a literally zero dividend spells the
//! same terms in both and reports nothing.

use super::*;

const DIVIDER: CleanOnlySpelling = CleanOnlySpelling::FixedDivider;
const WIDTH: u32 = 4;

/// One 4-bit division lemma over the free word `x` and/or `y`.
struct Lemma {
    terms: TermStore,
    assertion: Option<TermId>,
    words: Vec<(&'static str, u32)>,
}

impl Lemma {
    fn new() -> Self {
        Self {
            terms: TermStore::new(),
            assertion: None,
            words: Vec::new(),
        }
    }

    fn free(&mut self, name: &'static str) -> TermId {
        self.words.push((name, WIDTH));
        self.terms.mk_var(name, Sort::bitvec(WIDTH))
    }

    fn constant(&mut self, value: u32) -> TermId {
        self.terms.mk_bitvec(BigInt::from(value), WIDTH)
    }

    /// Raw: the folding builders would rewrite exactly these shapes.
    fn op(&mut self, head: &str, args: [TermId; 2], sort: Sort) -> TermId {
        self.terms.mk_app(Symbol::named(head), args, sort)
    }

    fn divide(&mut self, head: &str, x: TermId, y: TermId) -> TermId {
        self.op(head, [x, y], Sort::bitvec(WIDTH))
    }

    /// Assert `(not (= left right))`, which the lemma refutes.
    fn differs(mut self, left: TermId, right: TermId) -> Self {
        let equality = self.op("=", [left, right], Sort::Bool);
        self.assertion = Some(self.terms.mk_not_raw(equality));
        self
    }

    fn render(&self, dialect: AletheDialect) -> ([String; 3], AletheDialectReport) {
        let assertion = self.assertion.expect("an asserted lemma");
        capture_alethe_dialect_report(|| {
            with_alethe_dialect(dialect, || {
                complete_blast(&self.terms, assertion, &self.words)
            })
        })
    }
}

fn rule(head: &str) -> &'static str {
    if head == "bvurem" {
        "bitblast_urem"
    } else {
        "bitblast_udiv"
    }
}

/// A free dividend under a non-zero divisor: pinned Carcara's divider would
/// be false, so both dialects keep Clean's, report it, and are refused.
#[test]
fn a_free_dividend_keeps_the_clean_divider_in_both_dialects_and_is_disclosed() {
    for head in ["bvudiv", "bvurem"] {
        let mut lemma = Lemma::new();
        let x = lemma.free("x");
        let three = lemma.constant(3);
        let divided = lemma.divide(head, x, three);
        // x < x / 3 and 2 < x mod 3 are both impossible.
        let (small, large) = if head == "bvudiv" {
            (x, divided)
        } else {
            (lemma.constant(2), divided)
        };
        lemma.assertion = Some(lemma.op("bvult", [small, large], Sort::Bool));
        let (clean, clean_report) = lemma.render(AletheDialect::Clean);
        let (pinned_render, pinned_report) = lemma.render(AletheDialect::PinnedCarcara);
        assert!(
            clean[2].contains(&format!(":rule {}", rule(head))),
            "{head}"
        );
        assert_eq!(
            clean, pinned_render,
            "{head}: the pinned dialect keeps Clean's divider"
        );
        assert_eq!(clean_report.first_clean_only(), Some(DIVIDER), "{head}");
        assert_eq!(pinned_report.first_clean_only(), Some(DIVIDER), "{head}");
        let case = format!("cbb-{head}-free");
        assert_pinned_refuses_at(&case, &clean[0], &clean[1], rule(head));
    }
}

/// A zero divisor, over a free dividend: the pinned dialect prints pinned
/// Carcara's divider, which is true there, reports nothing, and is `valid`;
/// the default reports Clean's and is refused.
#[test]
fn a_zero_divisor_is_spelled_for_pinned_carcara_in_the_pinned_dialect() {
    for head in ["bvudiv", "bvurem"] {
        let mut lemma = Lemma::new();
        let x = lemma.free("x");
        let zero = lemma.constant(0);
        let divided = lemma.divide(head, x, zero);
        let meaning = if head == "bvudiv" {
            lemma.constant(15)
        } else {
            x
        };
        let lemma = lemma.differs(divided, meaning);
        let case = format!("cbb-{head}-by-zero");
        let (clean, report) = lemma.render(AletheDialect::Clean);
        assert!(
            clean[2].contains(&format!(":rule {}", rule(head))),
            "{case}"
        );
        assert_eq!(report.first_clean_only(), Some(DIVIDER), "{case}");
        assert_pinned_refuses_at(&format!("{case}-clean"), &clean[0], &clean[1], rule(head));

        let (pinned_render, report) = lemma.render(AletheDialect::PinnedCarcara);
        assert!(
            pinned_render[2].contains(&format!(":rule {}", rule(head))),
            "{case}"
        );
        assert!(report.is_pinned_spelling(), "{case}: {report:?}");
        assert_pinned_valid(
            &format!("{case}-pinned"),
            &pinned_render[0],
            &pinned_render[1],
        );
    }
}

/// Closed operands: `7 div 2` is one pinned Carcara's divider gets right,
/// so the pinned dialect prints it (`valid`); `7 rem 2` and `8 div 2` it gets
/// wrong (an all-ones remainder, a zero quotient), so the pinned dialect keeps
/// Clean's divider there, reports it, and the replay refuses it. That
/// negative twin is the guard at work: the pinned spelling would be accepted
/// and false.
#[test]
fn closed_operands_are_spelled_for_pinned_carcara_only_where_it_divides_correctly() {
    for (head, x, y, meaning, pinned_is_true) in [
        ("bvudiv", 7, 2, 3, true),
        ("bvurem", 7, 2, 1, false),
        ("bvudiv", 8, 2, 4, false),
    ] {
        let case = format!("cbb-{head}-{x}-{y}");
        let mut lemma = Lemma::new();
        let (x, y, meaning) = (
            lemma.constant(x),
            lemma.constant(y),
            lemma.constant(meaning),
        );
        let divided = lemma.divide(head, x, y);
        let lemma = lemma.differs(divided, meaning);
        let (clean, report) = lemma.render(AletheDialect::Clean);
        assert!(
            clean[2].contains(&format!(":rule {}", rule(head))),
            "{case}"
        );
        assert_eq!(report.first_clean_only(), Some(DIVIDER), "{case}");
        assert_pinned_refuses_at(&format!("{case}-clean"), &clean[0], &clean[1], rule(head));

        let (pinned_render, report) = lemma.render(AletheDialect::PinnedCarcara);
        assert!(
            pinned_render[2].contains(&format!(":rule {}", rule(head))),
            "{case}"
        );
        if pinned_is_true {
            assert!(report.is_pinned_spelling(), "{case}: {report:?}");
            assert_pinned_valid(
                &format!("{case}-pinned"),
                &pinned_render[0],
                &pinned_render[1],
            );
        } else {
            assert_eq!(
                clean, pinned_render,
                "{case}: the guard kept Clean's divider"
            );
            assert_eq!(report.first_clean_only(), Some(DIVIDER), "{case}");
            let pinned = format!("{case}-pinned");
            assert_pinned_refuses_at(&pinned, &pinned_render[0], &pinned_render[1], rule(head));
        }
    }
}

/// NEGATIVE CONTROL of the disclosure: a literally zero dividend stops both
/// checkers' recursion at once, so the two dividers are the same terms, the
/// documents are byte-identical, nothing is reported, and both are `valid`.
#[test]
fn a_literally_zero_dividend_spells_the_same_divider_and_discloses_nothing() {
    let mut lemma = Lemma::new();
    let y = lemma.free("y");
    let zero = lemma.constant(0);
    let remainder = lemma.divide("bvurem", zero, y);
    let lemma = lemma.differs(remainder, zero);
    let (clean, clean_report) = lemma.render(AletheDialect::Clean);
    let (pinned_render, pinned_report) = lemma.render(AletheDialect::PinnedCarcara);
    assert!(clean[2].contains(":rule bitblast_urem"), "{}", clean[2]);
    assert_eq!(clean, pinned_render);
    assert!(clean_report.is_pinned_spelling(), "{clean_report:?}");
    assert!(pinned_report.is_pinned_spelling(), "{pinned_report:?}");
    assert_pinned_valid("cbb-bvurem-zero-dividend", &clean[0], &clean[1]);
}

#[test]
fn the_divider_disclosure_names_its_domain() {
    assert!(!DIVIDER.has_pinned_spelling());
    assert!(DIVIDER.describe().contains("bitblast_udiv"));
    assert!(DIVIDER
        .pinned_dialect_note()
        .contains("--alethe-dialect pinned-carcara"));
    let supported = crate::CarcaraSurface::Supported;
    assert_eq!(
        supported
            .clone()
            .with_dialect_report(&AletheDialectReport::default()),
        supported
    );
    let ((), kept) = capture_alethe_dialect_report(|| note_clean_only(DIVIDER));
    let disclosed = supported.with_dialect_report(&kept);
    assert_eq!(
        disclosed,
        crate::CarcaraSurface::CleanDialect { spelling: DIVIDER }
    );
    assert!(!disclosed.is_supported());
    assert_eq!(disclosed.unsupported_reason(), Some(DIVIDER.describe()));
    assert!(disclosed.to_string().starts_with("clean-dialect("));
    // An unparseable document stays unsupported: that verdict already refuses it.
    let unparseable = crate::CarcaraSurface::Unsupported {
        reason: "sort (Seq Int)".to_string(),
    };
    assert_eq!(unparseable.clone().with_dialect_report(&kept), unparseable);
}
