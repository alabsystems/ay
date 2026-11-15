// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn compare_root(eb: u32, sb: u32, mode: RoundingMode, end: Instant) {
    let mut terms = TermStore::new();
    let (fma, [x_term, y_term, z_term]) = root(&mut terms, eb, sb, mode);
    let mut original = FpSolver::new(&terms);
    // Exact old native caller order: z before x/y, then the old gate stream.
    let z = original.get_fp(z_term);
    let x = original.get_fp(x_term);
    let y = original.get_fp(y_term);
    let expected = original.make_fma_legacy(&x, &y, &z, mode.into());
    original.term_to_fp.insert(fma, expected.clone());
    let expected_cache = original.export_cache();
    let history = RefCell::new(Vec::new());
    let mut stop = |p| {
        history.borrow_mut().push(p);
        Instant::now() >= end
    };
    let mut attempt = FpConstruction::new(FpSolver::new(&terms), &mut stop).unwrap();
    let actual = attempt.try_get_fp(fma).unwrap();
    let built = attempt.finish().unwrap();
    assert_fp(&actual, &expected);
    assert_cache(&built.cache, &expected_cache);
    assert_eq!(built.clauses.as_slice(), original.clauses());
    assert_eq!(
        built.pending_condition_links,
        original.pending_condition_links
    );
    assert_eq!(built.has_encoding_gap, original.has_encoding_gap());
    assert_monotone(&history.borrow());
    assert_eq!(
        history
            .borrow()
            .iter()
            .filter(|p| p.stage == FpBuildStage::MultiplyRow)
            .count(),
        2 * sb as usize + 2
    );
    drop((built, original, expected_cache));
    assert!(Instant::now() < end);
}

#[test]
fn healthy_native_fma_keeps_frozen_complete_cnf_cache_and_namespace_in_all_five_modes() {
    let end = Instant::now() + Duration::from_secs(20);
    for (eb, sb) in [(5, 11), (3, 8)] {
        for mode in RM_ORDER {
            compare_root(eb, sb, mode, end);
        }
    }
}

#[test]
fn healthy_native_ieee32_and_ieee64_fma_keep_original_three_free_input_links() {
    let end = Instant::now() + Duration::from_secs(20);
    for (eb, sb) in [(8, 24), (11, 53)] {
        compare_root(eb, sb, RoundingMode::RNE, end);
    }
}

#[test]
fn public_uninterrupted_fma_keeps_original_arithmetic_for_literal_and_symbolic_modes() {
    let end = Instant::now() + Duration::from_secs(20);
    let mut terms = TermStore::new();
    let symbolic_rm = terms.mk_var("original-rm", Sort::Uninterpreted("RoundingMode".into()));
    for mode in RM_ORDER.map(Some).into_iter().chain([None]) {
        let mut old = FpSolver::new(&terms);
        let mut new = FpSolver::new(&terms);
        let mut no_stop = crate::construction::control::Uninterrupted;
        let old_rm = mode.map_or_else(
            || {
                old.rounding_operand_with_control(symbolic_rm, &mut no_stop)
                    .unwrap()
            },
            RmOperand::Literal,
        );
        let new_rm = mode.map_or_else(
            || {
                new.rounding_operand_with_control(symbolic_rm, &mut no_stop)
                    .unwrap()
            },
            RmOperand::Literal,
        );
        let precision = FpPrecision::Float16;
        let (ox, oy, oz) = (
            old.fresh_decomposed(precision),
            old.fresh_decomposed(precision),
            old.fresh_decomposed(precision),
        );
        let (nx, ny, nz) = (
            new.fresh_decomposed(precision),
            new.fresh_decomposed(precision),
            new.fresh_decomposed(precision),
        );
        let expected = old.make_fma_legacy(&ox, &oy, &oz, old_rm);
        let actual = new.make_fma(&nx, &ny, &nz, new_rm);
        assert_fp(&actual, &expected);
        assert_eq!(new.clauses(), old.clauses());
        assert_cache(&new.export_cache(), &old.export_cache());
        drop((old, new));
        assert!(Instant::now() < end);
    }
}

#[test]
fn zero_factor_fma_keeps_frozen_add_nan_selection_and_complete_native_cache() {
    let end = Instant::now() + Duration::from_secs(20);
    for (zero_name, class) in [
        ("+zero", FpConstClass::PosZero),
        ("-zero", FpConstClass::NegZero),
    ] {
        for mode in RM_ORDER {
            let mut terms = TermStore::new();
            let sort = Sort::FloatingPoint(5, 11);
            let zero = terms.mk_app(Symbol::named(zero_name), [], sort.clone());
            let y = terms.mk_var("other-original-input", sort.clone());
            let z = terms.mk_var("original-addend", sort.clone());
            let rm = terms.mk_app(
                Symbol::named(mode.name()),
                [],
                Sort::Uninterpreted("RoundingMode".into()),
            );
            let fma = terms.mk_app(Symbol::named("fp.fma"), [rm, zero, y, z], sort);
            let mut old = FpSolver::new(&terms);
            let old_z = old.get_fp(z);
            let old_y = old.get_fp(y);
            let expected = old.legacy_encode_fma_zero_factor(
                class,
                &old_y,
                &old_z,
                mode.into(),
                FpPrecision::Float16,
            );
            old.term_to_fp.insert(fma, expected.clone());
            let mut stop = |_| Instant::now() >= end;
            let mut attempt = FpConstruction::new(FpSolver::new(&terms), &mut stop).unwrap();
            let actual = attempt.try_get_fp(fma).unwrap();
            let built = attempt.finish().unwrap();
            assert_fp(&actual, &expected);
            assert_cache(&built.cache, &old.export_cache());
            assert_eq!(built.clauses.as_slice(), old.clauses());
            assert_eq!(built.pending_condition_links, old.pending_condition_links);
            assert_eq!(built.has_encoding_gap, old.has_encoding_gap());
            drop((old, built));
            assert!(Instant::now() < end);
        }
    }
}
