// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn sqrt_and_fma_reject_wrong_arity_formats_indices_and_dead_source_children() {
    with_owner(1, |budget| {
        budget.admit(8192, 65_536).unwrap();
        let mut terms = TermStore::new();
        let x = fp_constant(&mut terms, 0x3f800000, 32);
        let y = fp_constant(&mut terms, 0x3ff0000000000000, 64);
        let rm = mode(&mut terms, RoundingMode::RNE);
        for (name, good) in [("fp.sqrt", vec![rm, x]), ("fp.fma", vec![rm, x, x, x])] {
            let mut malformed = vec![vec![], vec![rm], good[..good.len() - 1].to_vec()];
            let mut extra = good.clone();
            extra.push(x);
            malformed.push(extra);
            let mut mixed = good.clone();
            mixed[1] = y;
            malformed.push(mixed);
            let mut missing = good.clone();
            missing[1] = TermId(999);
            malformed.push(missing);
            for args in malformed {
                let actual = terms.mk_app(Symbol::named(name), args, Sort::FloatingPoint(8, 24));
                let root = predicate(&mut terms, "fp.isZero", &[actual]);
                assert!(matches!(
                    error(&terms, root, budget),
                    FpAdapterError::Invalid(_) | FpAdapterError::Unsupported(_)
                ));
            }
            let indexed = terms.mk_app(
                Symbol::indexed(name, vec![8, 24]),
                good.clone(),
                Sort::FloatingPoint(8, 24),
            );
            let root = predicate(&mut terms, "fp.isZero", &[indexed]);
            assert!(matches!(
                error(&terms, root, budget),
                FpAdapterError::Unsupported(_)
            ));
            let wrong = terms.mk_app(Symbol::named(name), good, Sort::FloatingPoint(5, 11));
            let root = predicate(&mut terms, "fp.isZero", &[wrong]);
            assert!(matches!(
                error(&terms, root, budget),
                FpAdapterError::Unsupported(_)
            ));
        }
        drop(terms);
        budget.charge(0).unwrap();
    });
}

#[test]
fn rounded_modes_must_be_typed_nullary_literal_names_never_symbolic_or_indexed() {
    with_owner(1, |budget| {
        budget.admit(8192, 65_536).unwrap();
        let mut terms = TermStore::new();
        let x = fp_constant(&mut terms, 0x3f800000, 32);
        let sort = Sort::Uninterpreted("RoundingMode".into());
        let boolean = terms.mk_bool(true);
        let modes = [
            terms.mk_var("RNE", sort.clone()),
            terms.mk_app(Symbol::named("RNE"), [], Sort::Bool),
            terms.mk_app(Symbol::indexed("RNE", vec![]), [], sort.clone()),
            terms.mk_app(Symbol::named("RNE"), [boolean], sort.clone()),
            terms.mk_app(Symbol::named("nearestMaybe"), [], sort),
        ];
        for name in ["fp.sqrt", "fp.fma"] {
            for rm in modes {
                let args = if name == "fp.sqrt" {
                    vec![rm, x]
                } else {
                    vec![rm, x, x, x]
                };
                let actual = terms.mk_app(Symbol::named(name), args, Sort::FloatingPoint(8, 24));
                let root = predicate(&mut terms, "fp.isZero", &[actual]);
                assert!(matches!(
                    error(&terms, root, budget),
                    FpAdapterError::Unsupported(_)
                ));
            }
        }
        drop(terms);
        budget.charge(0).unwrap();
    });
}

#[test]
fn unchosen_rounded_operands_and_zero_fma_factor_cannot_hide_unbound_or_unsupported_sources() {
    with_owner(1, |budget| {
        for name in ["fp.sqrt", "fp.fma"] {
            for form in [IteForm::Direct, IteForm::Named] {
                for selected in [false, true] {
                    budget.admit(8192, 65_536).unwrap();
                    let mut terms = TermStore::new();
                    let zero = fp_constant(&mut terms, 0, 32);
                    let lost = terms.mk_var("lost_original", Sort::FloatingPoint(8, 24));
                    let actual = if name == "fp.sqrt" {
                        operation(&mut terms, name, 32, RoundingMode::RNE, &[lost])
                    } else {
                        operation(&mut terms, name, 32, RoundingMode::RNE, &[zero, lost, zero])
                    };
                    let c = terms.mk_bool(selected);
                    let (a, b) = if selected {
                        (zero, actual)
                    } else {
                        (actual, zero)
                    };
                    let choice = selection_choose(&mut terms, form, c, a, b);
                    let root = predicate(&mut terms, "fp.isZero", &[choice]);
                    assert!(matches!(
                        error(&terms, root, budget),
                        FpAdapterError::Invalid("unbound free input")
                    ));
                    drop(terms);
                    budget.charge(0).unwrap();
                }
            }
        }
        let mut terms = TermStore::new();
        let zero = fp_constant(&mut terms, 0, 32);
        let rm = mode(&mut terms, RoundingMode::RNE);
        let bad = terms.mk_app(
            Symbol::named("fp.roundToIntegral"),
            [rm, zero],
            Sort::FloatingPoint(8, 24),
        );
        let actual = operation(
            &mut terms,
            "fp.fma",
            32,
            RoundingMode::RNE,
            &[zero, bad, zero],
        );
        let root = predicate(&mut terms, "fp.isZero", &[actual]);
        assert!(matches!(
            error(&terms, root, budget),
            FpAdapterError::Unsupported(_)
        ));
    });
}

#[test]
fn whole_rounded_relation_keeps_three_words_original_namespace_and_ordered_roots() {
    with_owner(1, |budget| {
        budget.admit(8192, 65_536).unwrap();
        let mut terms = TermStore::new();
        let sources = ["round_x", "round_y", "round_z"]
            .map(|name| terms.mk_var(name, Sort::FloatingPoint(11, 53)));
        let fma = operation(&mut terms, "fp.fma", 64, RoundingMode::RNE, &sources);
        let sqrt = operation(&mut terms, "fp.sqrt", 64, RoundingMode::RNE, &[sources[0]]);
        let a = predicate(&mut terms, "fp.isNormal", &[fma]);
        let b = predicate(&mut terms, "fp.isNormal", &[sqrt]);
        let original = [a, b, a];
        let targets = ["round_x", "round_y", "round_z"]
            .map(|name| ChcVar::new(name, crate::ChcSort::BitVec(64)));
        let inputs = std::array::from_fn::<_, 3, _>(|i| FpInputBinding {
            source: sources[i],
            target: &targets[i],
        });
        let namespace = ChcProblem::new();
        let output = lower_fp_clause(&terms, &original, &inputs, &namespace, budget).unwrap();
        assert_eq!(output.source_roots(), &original);
        assert!(std::ptr::eq(output.source_terms(), &raw const terms));
        assert!(std::ptr::eq(
            output.source_namespace(),
            &raw const namespace
        ));
        assert_eq!(output.input_bindings().len(), 3);
        let ChcExpr::Op(crate::ChcOp::And, entries) = output.constraint() else {
            panic!()
        };
        let roots_at = entries.len() - 192 - original.len();
        assert_eq!(entries[roots_at], entries[roots_at + 2]);
        for (i, entry) in entries.iter().skip(entries.len() - 192).enumerate() {
            budget.charge(1).unwrap();
            let ChcExpr::Op(crate::ChcOp::Eq, link) = entry.as_ref() else {
                panic!()
            };
            let ChcExpr::Op(crate::ChcOp::Eq, value) = link[1].as_ref() else {
                panic!()
            };
            let ChcExpr::Op(crate::ChcOp::BvExtract(hi, lo), word) = value[0].as_ref() else {
                panic!()
            };
            assert_eq!((*hi, *lo), ((i % 64) as u32, (i % 64) as u32));
            assert_eq!(word[0].as_ref(), &ChcExpr::Var(targets[i / 64].clone()));
        }
        drop(output);
        budget.charge(0).unwrap();
    });
}
