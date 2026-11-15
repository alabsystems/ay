// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn cycle_fixture() -> TermStore {
    TermStore::from_entries(
        vec![
            literal_mode("RNE"),
            word(1, 8),
            (
                TermData::App(
                    Symbol::indexed("to_fp", vec![8, 24]),
                    vec![TermId(0), TermId(1)],
                ),
                Sort::FloatingPoint(8, 24),
            ),
            (TermData::Not(TermId(3)), Sort::Bool),
            (
                TermData::App(Symbol::indexed("+zero", vec![8, 24]), vec![]),
                Sort::FloatingPoint(8, 24),
            ),
            (
                TermData::Ite(TermId(3), TermId(2), TermId(4)),
                Sort::FloatingPoint(8, 24),
            ),
            (
                TermData::App(Symbol::named("fp.isNormal"), vec![TermId(5)]),
                Sort::Bool,
            ),
        ],
        None,
        None,
        0,
    )
}

#[test]
fn numeric_rm_must_be_live_named_zero_arity_rne_at_exact_rounding_sort() {
    owner(|budget| {
        let modes = [
            literal_mode("RNA"),
            (TermData::App(Symbol::named("RNE"), vec![]), Sort::Bool),
            (
                TermData::App(Symbol::indexed("RNE", vec![0]), vec![]),
                Sort::Uninterpreted("RoundingMode".into()),
            ),
            (
                TermData::Var("RNE".into(), 0),
                Sort::Uninterpreted("RoundingMode".into()),
            ),
            (
                TermData::App(Symbol::named("RNE"), vec![TermId(1)]),
                Sort::Uninterpreted("RoundingMode".into()),
            ),
        ];
        for mode in modes {
            let terms = fixture(
                mode,
                word(1, 8),
                Symbol::indexed("to_fp", vec![8, 24]),
                vec![TermId(0), TermId(1)],
            );
            refuses(&terms, budget);
        }
    });
}

#[test]
fn numeric_arity_format_width_and_canonical_payload_are_validated_before_clone() {
    owner(|budget| {
        for (value, width) in [(-1, 8), (256, 8), (1, 7), (1, 65)] {
            let terms = fixture(
                literal_mode("RNE"),
                word(value, width),
                Symbol::indexed("to_fp", vec![8, 24]),
                vec![TermId(0), TermId(1)],
            );
            refuses(&terms, budget);
        }
        for (symbol, args) in [
            (
                Symbol::indexed("to_fp", vec![11, 53]),
                vec![TermId(0), TermId(1)],
            ),
            (Symbol::named("to_fp"), vec![TermId(0), TermId(1)]),
            (
                Symbol::indexed("to_fp_unsigned", vec![8, 24]),
                vec![TermId(1)],
            ),
            (
                Symbol::indexed("to_fp", vec![8, 24]),
                vec![TermId(0), TermId(1), TermId(1)],
            ),
            (
                Symbol::indexed("to_fp", vec![8, 24]),
                vec![TermId(999), TermId(1)],
            ),
        ] {
            let terms = fixture(literal_mode("RNE"), word(1, 8), symbol, args);
            refuses(&terms, budget);
        }
    });
}

#[test]
fn numeric_compound_extracts_hidden_dead_descendants_and_cycles_never_become_inputs() {
    owner(|budget| {
        assert!(matches!(
            source::plan(&cycle_fixture(), &[TermId(6)], &[], budget),
            Err(FpAdapterError::Invalid("source cycle"))
        ));
        for operand in [
            TermData::App(Symbol::named("bvadd"), vec![TermId(1), TermId(1)]),
            TermData::App(Symbol::indexed("extract", vec![7, 0]), vec![TermId(999)]),
            TermData::App(Symbol::indexed("extract", vec![7, 0]), vec![TermId(1)]),
        ] {
            let terms = fixture(
                literal_mode("RNE"),
                (operand, Sort::bitvec(8)),
                Symbol::indexed("to_fp", vec![8, 24]),
                vec![TermId(0), TermId(1)],
            );
            refuses(&terms, budget);
        }
        let mut terms = TermStore::new();
        let raw = terms.mk_bitvec(1u8.into(), 32);
        let rm = terms.mk_app(
            Symbol::named("RNA"),
            [],
            Sort::Uninterpreted("RoundingMode".into()),
        );
        let unsupported = terms.mk_app(
            Symbol::indexed("to_fp", vec![8, 24]),
            [rm, raw],
            Sort::FloatingPoint(8, 24),
        );
        let good = fp_constant(&mut terms, 0, 32);
        for condition in [terms.mk_bool(true), terms.mk_bool(false)] {
            let selected = terms.mk_ite_raw(condition, good, unsupported);
            let root = predicate(&mut terms, "fp.isZero", &[selected]);
            assert!(source::plan(&terms, &[root], &[], budget).is_err());
        }
    });
}
