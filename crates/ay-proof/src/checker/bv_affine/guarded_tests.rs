// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn guard_clause(terms: &mut TermStore, source: TermId, guard: TermId, rhs: TermId) -> TermId {
    let eq = terms.mk_app(Symbol::named("="), [source, rhs], Sort::Bool);
    let neq = terms.mk_not_raw(eq);
    let root = terms.mk_app(Symbol::named("and"), [guard, neq], Sort::Bool);
    terms.mk_not_raw(root)
}

fn mask(terms: &mut TermStore, x: TermId, value: u128, width: u32) -> TermId {
    let value = terms.mk_bitvec(value.into(), width);
    terms.mk_app(Symbol::named("bvand"), [x, value], Sort::bitvec(width))
}

#[test]
fn guarded_mask_and_range_agree_with_exhaustive_small_domains() {
    let mut cases = 0;
    for width in 1..=5 {
        let maximum = (1u128 << width) - 1;
        for range in [false, true] {
            for guard_value in 0..=maximum {
                if range && !guard_value.is_power_of_two() {
                    continue;
                }
                for keep in 0..=maximum {
                    let mut terms = TermStore::new();
                    let x = terms.mk_var("x", Sort::bitvec(width));
                    let value = terms.mk_bitvec(guard_value.into(), width);
                    let guard = if range {
                        terms.mk_app(Symbol::named("bvult"), [x, value], Sort::Bool)
                    } else {
                        let masked = mask(&mut terms, x, guard_value, width);
                        let zero = terms.mk_bitvec(0.into(), width);
                        terms.mk_app(Symbol::named("="), [masked, zero], Sort::Bool)
                    };
                    let rhs = mask(&mut terms, x, keep, width);
                    let clause = guard_clause(&mut terms, x, guard, rhs);
                    let expected = (0..=maximum).all(|value| {
                        let premise = if range {
                            value < guard_value
                        } else {
                            value & guard_value == 0
                        };
                        !premise || value == value & keep
                    });
                    assert_eq!(
                        guarded_mask_identity(&terms, &[clause], &mut |_, _| true)
                            .unwrap()
                            .is_some(),
                        expected,
                        "width={width}, range={range}, guard={guard_value}, keep={keep}"
                    );
                    cases += 1;
                }
            }
        }
    }
    assert_eq!(cases, 1622);
}

#[test]
fn guarded_checks_hidden_source_shape_widths_and_resource_limits() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(64));
    let other = terms.mk_var("other", Sort::bitvec(32));
    let bound = terms.mk_bitvec(1.into(), 64);
    let zero = terms.mk_bitvec(0.into(), 64);
    let mut deep = x;
    for _ in 0..=MAX_DEPTH {
        deep = terms.mk_app(Symbol::named("bvadd"), [deep, x], Sort::bitvec(64));
    }
    let mut wide = x;
    for _ in 0..12 {
        wide = terms.mk_app(Symbol::named("bvadd"), [wide, wide], Sort::bitvec(64));
    }
    for source in [
        terms.mk_app(Symbol::named("bvadd"), [x, other], Sort::bitvec(64)),
        terms.mk_app(Symbol::named("bvadd"), [x], Sort::bitvec(64)),
        terms.mk_app(Symbol::named("unmodeled"), [x], Sort::bitvec(64)),
        deep,
        wide,
    ] {
        let guard = terms.mk_app(Symbol::named("bvult"), [source, bound], Sort::Bool);
        let clause = guard_clause(&mut terms, source, guard, zero);
        let mut charges = Vec::new();
        assert!(
            guarded_mask_identity(&terms, &[clause], &mut |work, bytes| {
                charges.push((work, bytes));
                true
            })
            .unwrap()
            .is_none()
        );
        assert_eq!(charges, [(MAX_WORK, MAX_ALLOCATION)]);
    }
    let guard = terms.mk_app(Symbol::named("bvult"), [x, bound], Sort::Bool);
    let rhs = terms.mk_app(Symbol::named("bvadd"), [x, x], Sort::bitvec(64));
    let clause = guard_clause(&mut terms, x, guard, rhs);
    // Both addends are known zero under this guard: their sum is exact.
    assert!(guarded_mask_identity(&terms, &[clause], &mut |_, _| true)
        .unwrap()
        .is_some());
    let bound = terms.mk_bitvec(2.into(), 64);
    let guard = terms.mk_app(Symbol::named("bvult"), [x, bound], Sort::Bool);
    let clause = guard_clause(&mut terms, x, guard, rhs);
    assert!(guarded_mask_identity(&terms, &[clause], &mut |_, _| true)
        .unwrap()
        .is_none());
    assert!(
        guarded_mask_identity(&terms, &[TermId(u32::MAX)], &mut |_, _| true)
            .unwrap()
            .is_none()
    );
}
