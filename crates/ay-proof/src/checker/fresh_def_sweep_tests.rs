// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exhaustive sweeps over a bounded configuration box.
//!
//! Every configuration the registry ACCEPTS is re-checked for the property the
//! soundness argument actually claims — the extension is CONSERVATIVE: for
//! every point of an integer box, some value of the introduced symbol satisfies
//! every bound the configuration carries. That re-check is performed by a
//! plain-`i64` evaluator (`LinSpec`) that shares NO code with the registry: no
//! `TermStore`, no `recognize_fresh_def_bound`, no `TermId` comparison. The two
//! agreeing is therefore evidence rather than a tautology.
//!
//! The sweeps are two-sided where that is meaningful: every REJECT is also
//! evaluated, and the counts of "rejected AND genuinely non-conservative" vs
//! "rejected but harmless" are asserted, so a future loosening that admits a
//! non-conservative configuration cannot pass unnoticed.

use super::{fixture, push_bound, FreshDefRegistry};
use ay_core::{Proof, TermId, TermStore};
use num_bigint::BigInt;

/// `a*x + b*y + c + p*d1 + q*d2`, evaluated with plain `i64`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct LinSpec {
    a: i64,
    b: i64,
    c: i64,
    p: i64,
    q: i64,
}

impl LinSpec {
    fn value(self, x: i64, y: i64, d1: i64, d2: i64) -> i64 {
        self.a * x + self.b * y + self.c + self.p * d1 + self.q * d2
    }

    fn build(self, terms: &mut TermStore, x: TermId, y: TermId, d1: TermId, d2: TermId) -> TermId {
        let mut summands = Vec::new();
        for (coeff, term) in [(self.a, x), (self.b, y), (self.p, d1), (self.q, d2)] {
            if coeff == 0 {
                continue;
            }
            if coeff == 1 {
                summands.push(term);
            } else {
                let k = terms.mk_int(BigInt::from(coeff));
                summands.push(terms.mk_mul(vec![k, term]));
            }
        }
        if self.c != 0 || summands.is_empty() {
            summands.push(terms.mk_int(BigInt::from(self.c)));
        }
        if summands.len() == 1 {
            summands[0]
        } else {
            terms.mk_add(summands)
        }
    }
}

/// One bound: which introduced symbol it is about, whether the symbol is the
/// UPPER-bounded side, and the defining term.
#[derive(Clone, Copy, Debug)]
struct BoundSpec {
    symbol: u8,
    upper: bool,
    lin: LinSpec,
}

impl BoundSpec {
    /// `d <= lin` (upper) or `lin <= d` (lower), at the given point.
    fn holds(self, x: i64, y: i64, d1: i64, d2: i64) -> bool {
        let d = if self.symbol == 1 { d1 } else { d2 };
        let lin = self.lin.value(x, y, d1, d2);
        if self.upper {
            d <= lin
        } else {
            lin <= d
        }
    }
}

const BOX: i64 = 3;
/// Wide enough that the canonical witness `d := lin` always lies inside it for
/// every configuration in these boxes, and then some.
const WITNESS_RANGE: i64 = 24;

/// Whether SOME assignment of the introduced symbols satisfies every bound, at
/// EVERY point of the authored box. This is exactly "the extension is
/// conservative" for a problem whose models are the whole box.
fn conservative(bounds: &[BoundSpec], two_symbols: bool) -> bool {
    for x in -BOX..=BOX {
        for y in -BOX..=BOX {
            let mut witnessed = false;
            'search: for d1 in -WITNESS_RANGE..=WITNESS_RANGE {
                let d2_range: Vec<i64> = if two_symbols {
                    (-WITNESS_RANGE..=WITNESS_RANGE).collect()
                } else {
                    vec![0]
                };
                for d2 in d2_range {
                    if bounds.iter().all(|bound| bound.holds(x, y, d1, d2)) {
                        witnessed = true;
                        break 'search;
                    }
                }
            }
            if !witnessed {
                return false;
            }
        }
    }
    true
}

/// Run the REAL registry over a proof carrying exactly `bounds`.
fn registry_accepts(bounds: &[BoundSpec]) -> bool {
    let mut f = fixture();
    let d1 = f.fresh(1);
    let d2 = f.fresh(2);
    let (x, y) = (f.x, f.y);
    let zero = f.int(0);
    let authored = f.terms.mk_le(zero, x);
    let mut proof = Proof::new();
    proof.add_assume(authored, None);
    for bound in bounds {
        let lin = bound.lin.build(&mut f.terms, x, y, d1, d2);
        let symbol = if bound.symbol == 1 { d1 } else { d2 };
        push_bound(&mut proof, &mut f.terms, symbol, lin, !bound.upper);
    }
    FreshDefRegistry::collect(&proof, &f.terms, Some(&[authored])).is_ok()
}

/// The single-symbol definiens family: `a*x + b*y + c` for `a, b, c ∈ {-1,0,1}`,
/// plus the self-referential `d1 + c`, which is what the INDEPENDENT guard is
/// for.
fn single_symbol_family() -> Vec<LinSpec> {
    let mut family = Vec::new();
    for a in -1..=1 {
        for b in -1..=1 {
            for c in -1..=1 {
                family.push(LinSpec {
                    a,
                    b,
                    c,
                    p: 0,
                    q: 0,
                });
            }
        }
    }
    for c in -1..=1 {
        family.push(LinSpec {
            a: 0,
            b: 0,
            c,
            p: 1,
            q: 0,
        });
    }
    family
}

#[test]
fn sweep_single_symbol_one_bound_every_accept_is_conservative() {
    let family = single_symbol_family();
    let (mut accepted, mut rejected) = (0_usize, 0_usize);
    for &lin in &family {
        for upper in [true, false] {
            let bounds = [BoundSpec {
                symbol: 1,
                upper,
                lin,
            }];
            let accepts = registry_accepts(&bounds);
            let is_conservative = conservative(&bounds, false);
            if accepts {
                accepted += 1;
                assert!(
                    is_conservative,
                    "registry ACCEPTED a non-conservative single bound: {bounds:?}"
                );
            } else {
                rejected += 1;
            }
        }
    }
    // 27 definientia over authored symbols only, in both directions, are
    // accepted (54). All 3 self-referential ones are refused in both
    // directions (6): two by the INDEPENDENT guard, and the bare `d1` by the
    // SHAPE gate, because `mk_le(d1, d1)` folds to `true` and a `true` clause
    // is not a `<=` application at all.
    assert_eq!(accepted, 54, "unexpected accept count");
    assert_eq!(rejected, 6, "unexpected reject count");
    assert_eq!(accepted + rejected, family.len() * 2);
}

#[test]
fn sweep_single_symbol_two_bounds_every_accept_is_conservative() {
    let family = single_symbol_family();
    let mut accepted = 0_usize;
    let mut rejected_but_conservative = 0_usize;
    let mut rejected_and_unsound = 0_usize;
    for &lin1 in &family {
        for upper1 in [true, false] {
            for &lin2 in &family {
                for upper2 in [true, false] {
                    let bounds = [
                        BoundSpec {
                            symbol: 1,
                            upper: upper1,
                            lin: lin1,
                        },
                        BoundSpec {
                            symbol: 1,
                            upper: upper2,
                            lin: lin2,
                        },
                    ];
                    let is_conservative = conservative(&bounds, false);
                    if registry_accepts(&bounds) {
                        accepted += 1;
                        assert!(
                            is_conservative,
                            "registry ACCEPTED a non-conservative pair: {bounds:?}"
                        );
                    } else if is_conservative {
                        rejected_but_conservative += 1;
                    } else {
                        rejected_and_unsound += 1;
                    }
                }
            }
        }
    }
    assert_eq!(
        accepted + rejected_but_conservative + rejected_and_unsound,
        3600
    );
    // The rule is deliberately fail-closed, so some conservative
    // configurations are refused (two DIFFERENT upper bounds, for instance,
    // are satisfied by the smaller one but are not a definition). What must
    // never happen is the other direction, which the assertion above pins.
    assert!(
        rejected_and_unsound > 0,
        "the box must contain genuinely non-conservative pairs, or it proves nothing"
    );
    assert!(accepted > 0, "the box must contain accepted pairs");
}

/// The two-symbol family, small enough to enumerate all four-bound
/// configurations: authored terms, and the cross-references that make a cycle.
fn two_symbol_family() -> Vec<LinSpec> {
    vec![
        LinSpec {
            a: 1,
            b: 0,
            c: 0,
            p: 0,
            q: 0,
        },
        LinSpec {
            a: 0,
            b: 1,
            c: 0,
            p: 0,
            q: 0,
        },
        LinSpec {
            a: 0,
            b: 0,
            c: 0,
            p: 0,
            q: 0,
        },
        LinSpec {
            a: 0,
            b: 0,
            c: 1,
            p: 1,
            q: 0,
        },
        LinSpec {
            a: 0,
            b: 0,
            c: 1,
            p: 0,
            q: 1,
        },
        LinSpec {
            a: 1,
            b: 0,
            c: 0,
            p: 0,
            q: 1,
        },
        LinSpec {
            a: 0,
            b: 0,
            c: 0,
            p: 0,
            q: 1,
        },
    ]
}

#[test]
fn sweep_two_symbols_every_accept_is_conservative() {
    let family = two_symbol_family();
    let mut accepted = 0_usize;
    let mut cycles_rejected = 0_usize;
    for &lin1 in &family {
        for &lin2 in &family {
            let bounds = [
                BoundSpec {
                    symbol: 1,
                    upper: true,
                    lin: lin1,
                },
                BoundSpec {
                    symbol: 1,
                    upper: false,
                    lin: lin1,
                },
                BoundSpec {
                    symbol: 2,
                    upper: true,
                    lin: lin2,
                },
                BoundSpec {
                    symbol: 2,
                    upper: false,
                    lin: lin2,
                },
            ];
            let is_conservative = conservative(&bounds, true);
            if registry_accepts(&bounds) {
                accepted += 1;
                assert!(
                    is_conservative,
                    "registry ACCEPTED a non-conservative two-symbol configuration: {bounds:?}"
                );
            } else if lin1.p != 0 || lin1.q != 0 || lin2.p != 0 || lin2.q != 0 {
                cycles_rejected += 1;
            }
        }
    }
    // Only the 3x3 sub-box of definientia over authored symbols survives; every
    // configuration whose definiens mentions an introduced symbol is refused,
    // which is what makes a mutual cycle unreachable.
    assert_eq!(accepted, 9, "unexpected two-symbol accept count");
    assert_eq!(cycles_rejected, 40, "unexpected two-symbol reject count");
}

#[test]
fn the_canonical_witness_is_the_definiens_at_every_point_of_the_box() {
    // The soundness argument does not merely say a witness EXISTS — it names
    // it: `d := lin`. Check that specific assignment directly, independently of
    // the search above.
    for &lin in &single_symbol_family() {
        if lin.p != 0 {
            continue;
        }
        let bounds = [
            BoundSpec {
                symbol: 1,
                upper: true,
                lin,
            },
            BoundSpec {
                symbol: 1,
                upper: false,
                lin,
            },
        ];
        assert!(registry_accepts(&bounds));
        for x in -BOX..=BOX {
            for y in -BOX..=BOX {
                let witness = lin.value(x, y, 0, 0);
                assert!(
                    bounds.iter().all(|bound| bound.holds(x, y, witness, 0)),
                    "`d := lin` must satisfy both bounds at ({x}, {y}) for {lin:?}"
                );
            }
        }
    }
}
