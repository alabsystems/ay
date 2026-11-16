// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn exact_named_only_namespace_matches_the_legacy_guard() {
    let entries = entries();
    assert_eq!(names::NAMED_ONLY.len(), 116);
    for &name in names::NAMED_ONLY {
        assert!(requires_named_symbol(name));
        for indices in [vec![], vec![0], vec![0, 1]] {
            assert!(!compare(
                &entries,
                &Symbol::indexed(name, indices),
                &[],
                &Sort::Bool
            ));
        }
    }
    for name in ["extract", "repeat", "NaN", "unknown", "to_fp"] {
        assert!(!requires_named_symbol(name));
        assert!(!names::NAMED_ONLY.contains(&name));
    }
}

#[test]
fn indexed_bv_shapes_indices_and_result_widths_match_legacy() {
    let entries = entries();
    for (name, indices, width) in [
        ("extract", vec![6, 2], 5),
        ("zero_extend", vec![8], 16),
        ("sign_extend", vec![8], 16),
        ("rotate_left", vec![999], 8),
        ("rotate_right", vec![999], 8),
        ("repeat", vec![2], 16),
    ] {
        assert!(compare(
            &entries,
            &Symbol::indexed(name, indices.clone()),
            &[TermId(3)],
            &bv(width)
        ));
        assert!(!compare(
            &entries,
            &Symbol::named(name),
            &[TermId(3)],
            &bv(width)
        ));
        for bad_indices in [vec![], vec![0, 0, 0], vec![u32::MAX], vec![0, u32::MAX]] {
            compare(
                &entries,
                &Symbol::indexed(name, bad_indices),
                &[TermId(3)],
                &bv(width),
            );
        }
        for args in [vec![], vec![TermId(1)], vec![TermId(3); 2]] {
            compare(
                &entries,
                &Symbol::indexed(name, indices.clone()),
                &args,
                &bv(width),
            );
        }
        compare(
            &entries,
            &Symbol::indexed(name, indices.clone()),
            &[TermId(3)],
            &Sort::Int,
        );
        compare(
            &entries,
            &Symbol::indexed(name, indices),
            &[TermId(3)],
            &bv(width + 1),
        );
    }
}

#[test]
fn indexed_width_overflows_and_raw_app_boundaries_preserve_legacy_behavior() {
    let mut entries = entries();
    entries[3].1 = bv(u32::MAX);
    for name in ["zero_extend", "sign_extend", "repeat"] {
        assert!(!compare(
            &entries,
            &Symbol::indexed(name, vec![2]),
            &[TermId(3)],
            &bv(1)
        ));
    }
    assert!(!compare(
        &entries,
        &Symbol::indexed("repeat", vec![0]),
        &[TermId(3)],
        &bv(0)
    ));
    assert!(!compare(
        &entries,
        &Symbol::indexed("extract", vec![0, 1]),
        &[TermId(3)],
        &bv(1)
    ));
    assert!(!compare(
        &entries,
        &Symbol::indexed("extract", vec![u32::MAX, 0]),
        &[TermId(3)],
        &bv(1)
    ));
    assert!(compare(
        &entries,
        &Symbol::indexed("extract", vec![u32::MAX - 1, 0]),
        &[TermId(3)],
        &bv(u32::MAX)
    ));
    // Full sort validation rejects these widths, but app equality itself must
    // not silently acquire a second, different sort-validation policy.
    assert!(compare(
        &entries,
        &Symbol::named("bvneg"),
        &[TermId(3)],
        &bv(u32::MAX)
    ));
    assert!(!compare(
        &entries,
        &Symbol::named("concat"),
        &[TermId(3), TermId(3)],
        &bv(1)
    ));
    entries[9].1 = bv(u32::MAX);
    assert!(!compare(
        &entries,
        &Symbol::named("fp"),
        &[TermId(7), TermId(8), TermId(9)],
        &Sort::FloatingPoint(8, 0)
    ));
}

#[test]
fn indexed_fp_literals_keep_exact_indices_and_no_argument_policy() {
    let entries = entries();
    for name in ["+zero", "-zero", "+oo", "-oo", "NaN"] {
        assert!(compare(
            &entries,
            &Symbol::indexed(name, vec![8, 24]),
            &[],
            &Sort::FloatingPoint(8, 24)
        ));
        assert!(!compare(
            &entries,
            &Symbol::named(name),
            &[],
            &Sort::FloatingPoint(8, 24)
        ));
        for indices in [vec![], vec![8], vec![8, 23], vec![8, 24, 0]] {
            assert!(!compare(
                &entries,
                &Symbol::indexed(name, indices),
                &[],
                &Sort::FloatingPoint(8, 24)
            ));
        }
        assert!(!compare(
            &entries,
            &Symbol::indexed(name, vec![8, 24]),
            &[TermId(6)],
            &Sort::FloatingPoint(8, 24)
        ));
        assert!(!compare(
            &entries,
            &Symbol::indexed(name, vec![8, 24]),
            &[],
            &Sort::Bool
        ));
    }
}
