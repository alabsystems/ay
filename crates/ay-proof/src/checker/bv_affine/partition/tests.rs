// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn indicator(
    terms: &mut TermStore,
    start: TermId,
    pc: TermId,
    end: TermId,
    one: TermId,
    zero: TermId,
) -> TermId {
    let lower = terms.mk_app(Symbol::named("bvule"), [start, pc], Sort::Bool);
    let upper = terms.mk_app(Symbol::named("bvult"), [pc, end], Sort::Bool);
    let guard = terms.mk_app(Symbol::named("and"), [lower, upper], Sort::Bool);
    terms.mk_ite_raw(guard, one, zero)
}

fn fixture(
    terms: &mut TermStore,
    width: u32,
    pc: u128,
    upper: u128,
    reverse: bool,
    bad: Option<TermId>,
) -> TermId {
    let sort = Sort::bitvec(width);
    let zero = terms.mk_bitvec(0.into(), width);
    let one = terms.mk_bitvec(1.into(), width);
    let pc = terms.mk_bitvec(pc.into(), width);
    let upper = terms.mk_bitvec(upper.into(), width);
    let upper = if let Some(source) = bad {
        let cancelled = terms.mk_app(Symbol::named("bvsub"), [source, source], sort.clone());
        terms.mk_app(Symbol::named("bvadd"), [upper, cancelled], sort.clone())
    } else {
        upper
    };
    let s = terms.mk_var("s", sort.clone());
    let e = terms.mk_var("e", sort.clone());
    let a = indicator(terms, zero, pc, s, one, zero);
    let b = indicator(terms, e, pc, upper, one, zero);
    let c = indicator(terms, s, pc, e, one, zero);
    let sum = terms.mk_app(Symbol::named("bvadd"), [a, b], sort.clone());
    let sum = terms.mk_app(Symbol::named("bvadd"), [sum, c], sort);
    let eq = terms.mk_app(Symbol::named("="), [sum, one], Sort::Bool);
    let t = terms.true_term();
    let eq = terms.mk_app(Symbol::named("="), [t, eq], Sort::Bool);
    let negated = terms.mk_not_raw(eq);
    let ordered = if reverse {
        terms.mk_app(Symbol::named("bvuge"), [e, s], Sort::Bool)
    } else {
        terms.mk_app(Symbol::named("bvule"), [s, e], Sort::Bool)
    };
    let root = terms.mk_app(Symbol::named("and"), [ordered, negated], Sort::Bool);
    terms.mk_not_raw(root)
}

#[test]
fn native_partition_matches_exhaustive_unsigned_interval_semantics() {
    let mut cases = 0;
    for width in 1..=4 {
        let modulus = 1u128 << width;
        for pc in 0..modulus {
            for upper in 0..modulus {
                for reverse in [false, true] {
                    let expected = (0..modulus).all(|s| {
                        (0..modulus).all(|e| {
                            let count = u128::from(pc < s)
                                + u128::from(e <= pc && pc < upper)
                                + u128::from(s <= pc && pc < e);
                            s > e || count % modulus == 1
                        })
                    });
                    let mut terms = TermStore::new();
                    let root = fixture(&mut terms, width, pc, upper, reverse, None);
                    let actual = partition_identity(&terms, &[root], &mut |_, _| true)
                        .unwrap()
                        .is_some();
                    assert_eq!(
                        actual, expected,
                        "width={width} pc={pc} upper={upper} reverse={reverse}"
                    );
                    cases += 1;
                }
            }
        }
    }
    assert_eq!(cases, 680);
}

#[test]
fn partition_validates_hidden_nodes_and_declines_cancelled_work() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("hidden", Sort::bitvec(32));
    let other = terms.mk_var("other", Sort::bitvec(64));
    let zero = terms.mk_bitvec(0.into(), 32);
    let bad = terms.mk_app(Symbol::named("bvadd"), [x, other], Sort::bitvec(32));
    let mut deep = x;
    for _ in 0..=MAX_DEPTH {
        deep = terms.mk_app(Symbol::named("bvadd"), [deep, zero], Sort::bitvec(32));
    }
    for source in [
        bad,
        deep,
        terms.mk_app(Symbol::named("unknown"), [x], Sort::bitvec(32)),
    ] {
        // The malformed source cancels algebraically, but the entire source
        // must still be validated before the affine endpoint is normalized.
        let root = fixture(&mut terms, 32, 0, 1, false, Some(source));
        assert!(partition_identity(&terms, &[root], &mut |_, _| true)
            .unwrap()
            .is_none());
    }
    let root = fixture(&mut terms, 32, 0, 1, false, None);
    assert!(partition_identity(&terms, &[root], &mut |_, _| true)
        .unwrap()
        .is_some());
    let mut charges = Vec::new();
    assert!(partition_identity(&terms, &[root], &mut |work, bytes| {
        charges.push((work, bytes));
        false
    })
    .is_err());
    assert_eq!(charges, [(MAX_WORK, MAX_ALLOCATION)]);
    assert!(
        partition_identity(&terms, &[TermId(u32::MAX)], &mut |_, _| true)
            .unwrap()
            .is_none()
    );
}
