// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `zero_extend` in the packed lane, in both dialects, replayed through
//! pinned Carcara 9a352ee.
//!
//! Pinned Carcara has no rule for `zero_extend` over a symbolic word:
//! `refl`, `cong`, `evaluate` and every `bitblast_*` rule refuse
//! `((_ zero_extend k) x) = (concat (_ bv0 k) x)`, and `rare_rewrite` needs
//! a RARE file its gate invocation does not pass. It checks the word only
//! through `evaluate` on closed cases, one per assignment of its symbolic
//! bits, which the packed lane prints under an eight-bit bound
//! (`bv_packed::wire`). The packed-circuit and complete bit-blast lanes
//! print no cases; the parent module's `zero_extend` test covers them.
//!
//! REGRESSION (measured 2026-09-30 on c57bd8481): a source wider than a byte
//! whose symbolic bits fit that bound (a closed word, `(concat (_ bv0 8) b)`,
//! `((_ zero_extend 8) b)`) printed Clean's `refl` to `concat` under
//! `--alethe-dialect pinned-carcara` too, disclosed `clean-dialect`, and
//! pinned Carcara refused it at `refl`. The pinned dialect now prints the
//! closed cases there, a literal `valid`; Clean's document is unchanged.
//! NEGATIVE TWIN: nine symbolic bits in a sixteen-bit word exceed the bound,
//! so both dialects keep Clean's `refl` and report it.

use super::*;

/// Clean's definitional step for a 16-bit source extended to 32 bits.
const CLEAN_EXPANSION: &str = "(concat (_ bv0 16) ";

/// `(= w w)` for `w = ((_ zero_extend 16) source)`, over the free word `byte`
/// of `byte_width` bits; `source` builds the 16-bit source from `byte`.
fn extended_identity(
    byte_width: u32,
    source: impl FnOnce(&mut TermStore, TermId) -> TermId,
) -> (TermStore, TermId) {
    let mut terms = TermStore::new();
    let byte = terms.mk_var("byte", Sort::bitvec(byte_width));
    let source = source(&mut terms, byte);
    let extend = Symbol::indexed("zero_extend", vec![16]);
    let wide = terms.mk_app(extend, [source], Sort::bitvec(32));
    let identity = terms.mk_app(Symbol::named("="), [wide, wide], Sort::Bool);
    (terms, identity)
}

/// A closed word, a byte under eight literal zeros, and a byte under a
/// narrower extension: 0, 8 and 8 symbolic bits in a 16-bit source.
fn few_symbolic_bits() -> Vec<(&'static str, TermStore, TermId)> {
    let (closed, closed_identity) =
        extended_identity(8, |terms, _| terms.mk_bitvec(BigInt::from(5), 16));
    let (padded, padded_identity) = extended_identity(8, |terms, byte| {
        let zeros = terms.mk_bitvec(BigInt::from(0), 8);
        terms.mk_app(Symbol::named("concat"), [zeros, byte], Sort::bitvec(16))
    });
    let (nested, nested_identity) = extended_identity(8, |terms, byte| {
        let inner = Symbol::indexed("zero_extend", vec![8]);
        terms.mk_app(inner, [byte], Sort::bitvec(16))
    });
    vec![
        ("closed", closed, closed_identity),
        ("padded", padded, padded_identity),
        ("nested", nested, nested_identity),
    ]
}

#[test]
fn a_wide_zero_extend_with_few_symbolic_bits_is_pinned_valid_in_the_pinned_dialect() {
    for (name, terms, identity) in few_symbolic_bits() {
        let ([problem, proof, steps], report) =
            capture_alethe_dialect_report(|| packed_certificate(&terms, identity, 8));
        assert!(steps.contains(CLEAN_EXPANSION), "{name}-clean:\n{steps}");
        assert_eq!(report.first_clean_only(), Some(ZERO_EXTEND), "{name}");
        assert_pinned_refuses_at(
            &format!("packed-zext-{name}-clean"),
            &problem,
            &proof,
            "refl",
        );

        let ([problem, proof, steps], report) = pinned(|| packed_certificate(&terms, identity, 8));
        assert!(!steps.contains(CLEAN_EXPANSION), "{name}-pinned:\n{steps}");
        assert!(steps.contains(":rule evaluate"), "{name}-pinned:\n{steps}");
        assert!(!steps.contains(":rule hole"), "{name}-pinned:\n{steps}");
        assert!(report.is_pinned_spelling(), "{name}: {report:?}");
        assert_pinned_valid(&format!("packed-zext-{name}-pinned"), &problem, &proof);
    }
}

/// NEGATIVE TWIN: the bound counts symbolic bits, not the width. Nine of them
/// under seven literal zeros keep Clean's `refl` in both dialects.
#[test]
fn nine_symbolic_bits_keep_the_clean_spelling_in_both_dialects() {
    let (terms, identity) = extended_identity(9, |terms, byte| {
        let zeros = terms.mk_bitvec(BigInt::from(0), 7);
        terms.mk_app(Symbol::named("concat"), [zeros, byte], Sort::bitvec(16))
    });
    for (dialect, name) in [
        (AletheDialect::Clean, "clean"),
        (AletheDialect::PinnedCarcara, "pinned"),
    ] {
        let ([problem, proof, steps], report) = capture_alethe_dialect_report(|| {
            with_alethe_dialect(dialect, || packed_certificate(&terms, identity, 9))
        });
        assert!(steps.contains(CLEAN_EXPANSION), "{name}:\n{steps}");
        assert_eq!(report.first_clean_only(), Some(ZERO_EXTEND), "{name}");
        assert_pinned_refuses_at(
            &format!("packed-zext-nine-{name}"),
            &problem,
            &proof,
            "refl",
        );
    }
}
