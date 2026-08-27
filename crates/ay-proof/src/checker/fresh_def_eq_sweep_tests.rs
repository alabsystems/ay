// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exhaustive sweeps over a bounded alphabet, for the EQUALITY form and for
//! MIXED equality/bound configurations.
//!
//! Every configuration the registry ACCEPTS is re-checked for the property the
//! soundness argument actually claims — the extension is CONSERVATIVE: at every
//! point of an integer box, some value of the introduced symbols satisfies
//! every atom the configuration carries. The re-check is performed by
//! [`AtomSpec::holds`], a plain-`i64` evaluator that shares NO code with the
//! registry: no `TermStore`, no `recognize_fresh_def_*`, no `TermId`
//! comparison. The two agreeing is therefore evidence rather than a tautology.
//!
//! The sweeps are two-sided: every REJECT is also evaluated, and the counts of
//! "rejected AND genuinely non-conservative" vs "rejected but harmless" are
//! asserted, so a future loosening that admits a non-conservative configuration
//! cannot pass unnoticed.
//!
//! The MIXED sweep is the one that would be missing if the equality rule had
//! its own registry: it enumerates every (equality, bound) pair over one symbol
//! and pins that the accepted set is exactly the agreeing-definiens diagonal.

use super::super::{fixture, push_bound, FreshDefRegistry};
use super::push_eq;
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

/// `a*x + b*y + c + p*d1 + q*d2`, terse enough that a whole family reads as a
/// table rather than as a page of struct literals.
const fn lin(a: i64, b: i64, c: i64, p: i64, q: i64) -> LinSpec {
    LinSpec { a, b, c, p, q }
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

/// Which relation an atom asserts between its symbol and its defining term.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Kind {
    /// `(= d lin)` — a `fresh_def_eq` step.
    Eq,
    /// `(<= d lin)` — a `fresh_def_bound` step.
    Upper,
    /// `(<= lin d)` — a `fresh_def_bound` step.
    Lower,
}

/// One introduced atom: which symbol it is about, which relation, and the
/// defining term.
#[derive(Clone, Copy, Debug)]
struct AtomSpec {
    symbol: u8,
    kind: Kind,
    lin: LinSpec,
}

impl AtomSpec {
    /// The atom's truth value at a point, computed independently of the
    /// registry and of the `TermStore`.
    fn holds(self, x: i64, y: i64, d1: i64, d2: i64) -> bool {
        let d = if self.symbol == 1 { d1 } else { d2 };
        let lin = self.lin.value(x, y, d1, d2);
        match self.kind {
            Kind::Eq => d == lin,
            Kind::Upper => d <= lin,
            Kind::Lower => lin <= d,
        }
    }
}

const BOX: i64 = 3;
/// Wide enough that the canonical witness `d := lin` always lies inside it for
/// every configuration in these boxes, and then some.
const WITNESS_RANGE: i64 = 24;

/// Whether SOME assignment of the introduced symbols satisfies every atom, at
/// EVERY point of the authored box. This is exactly "the extension is
/// conservative" for a problem whose models are the whole box.
fn conservative(atoms: &[AtomSpec], two_symbols: bool) -> bool {
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
                    if atoms.iter().all(|atom| atom.holds(x, y, d1, d2)) {
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

/// Run the REAL registry over a proof carrying exactly `atoms`.
fn registry_accepts(atoms: &[AtomSpec]) -> bool {
    let mut f = fixture();
    let d1 = f.fresh(1);
    let d2 = f.fresh(2);
    let (x, y) = (f.x, f.y);
    let zero = f.int(0);
    let authored = f.terms.mk_le(zero, x);
    let mut proof = Proof::new();
    proof.add_assume(authored, None);
    for atom in atoms {
        let lin = atom.lin.build(&mut f.terms, x, y, d1, d2);
        let symbol = if atom.symbol == 1 { d1 } else { d2 };
        match atom.kind {
            Kind::Eq => push_eq(&mut proof, &mut f.terms, symbol, lin),
            Kind::Upper => push_bound(&mut proof, &mut f.terms, symbol, lin, false),
            Kind::Lower => push_bound(&mut proof, &mut f.terms, symbol, lin, true),
        }
    }
    FreshDefRegistry::collect(&proof, &f.terms, Some(&[authored])).is_ok()
}

/// `a*x + b*y + c` for `a, b, c ∈ {-1,0,1}`, plus the self-referential
/// `d1 + c`, which is what the INDEPENDENT guard is for.
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

/// A smaller family for the quadratic sweeps: `x`, `y`, `x+y`, `0`, `1`, `-1`,
/// plus the self-referential `d1` and `d1 + 1`.
fn small_family() -> Vec<LinSpec> {
    vec![
        lin(1, 0, 0, 0, 0),
        lin(0, 1, 0, 0, 0),
        lin(1, 1, 0, 0, 0),
        lin(0, 0, 0, 0, 0),
        lin(0, 0, 1, 0, 0),
        lin(0, 0, -1, 0, 0),
        lin(0, 0, 0, 1, 0),
        lin(0, 0, 1, 1, 0),
    ]
}

#[test]
fn sweep_single_equality_every_accept_is_conservative() {
    let family = single_symbol_family();
    let (mut accepted, mut rejected) = (0_usize, 0_usize);
    for &lin in &family {
        let atoms = [AtomSpec {
            symbol: 1,
            kind: Kind::Eq,
            lin,
        }];
        if registry_accepts(&atoms) {
            accepted += 1;
            assert!(
                conservative(&atoms, false),
                "registry ACCEPTED a non-conservative single equality: {atoms:?}"
            );
        } else {
            rejected += 1;
        }
    }
    // The 27 definientia over authored symbols only are accepted. All 3
    // self-referential ones are refused: `d1 + 1` and `d1 - 1` by the
    // INDEPENDENT guard, and the bare `d1` by the SHAPE gate, because
    // `mk_eq(d1, d1)` folds to `true` and a `true` clause is not an `=`
    // application at all.
    assert_eq!(accepted, 27, "unexpected accept count");
    assert_eq!(rejected, 3, "unexpected reject count");
    assert_eq!(accepted + rejected, family.len());
}

#[test]
fn sweep_two_atoms_one_symbol_every_accept_is_conservative() {
    // The MIXED sweep: every (kind, lin) x (kind, lin) pair over one symbol,
    // so equality/equality, equality/bound and bound/bound configurations are
    // all enumerated by the same code path. 8 definientia x 3 kinds = 24
    // atoms, 576 ordered pairs.
    let family = small_family();
    let kinds = [Kind::Eq, Kind::Upper, Kind::Lower];
    let mut accepted = 0_usize;
    let mut rejected_but_conservative = 0_usize;
    let mut rejected_and_unsound = 0_usize;
    let mut mixed_accepted = 0_usize;
    let mut total = 0_usize;
    for &lin1 in &family {
        for kind1 in kinds {
            for &lin2 in &family {
                for kind2 in kinds {
                    total += 1;
                    let atoms = [
                        AtomSpec {
                            symbol: 1,
                            kind: kind1,
                            lin: lin1,
                        },
                        AtomSpec {
                            symbol: 1,
                            kind: kind2,
                            lin: lin2,
                        },
                    ];
                    let is_conservative = conservative(&atoms, false);
                    if registry_accepts(&atoms) {
                        accepted += 1;
                        let mixed = (kind1 == Kind::Eq) != (kind2 == Kind::Eq);
                        if mixed {
                            mixed_accepted += 1;
                        }
                        assert!(
                            is_conservative,
                            "registry ACCEPTED a non-conservative pair: {atoms:?}"
                        );
                        // Every accepted pair must name ONE definiens; that is
                        // what the cross-rule SINGLE DEFINIENS guard buys.
                        assert_eq!(
                            lin1, lin2,
                            "an accepted pair must agree on the definiens: {atoms:?}"
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
    assert_eq!(total, 576);
    assert_eq!(
        accepted + rejected_but_conservative + rejected_and_unsound,
        total
    );
    assert!(
        mixed_accepted > 0,
        "the box must actually exercise mixed equality/bound pairs"
    );
    // The rule is deliberately fail-closed, so some conservative
    // configurations are refused (two DIFFERENT upper bounds, for instance, are
    // satisfied by the smaller one but are not a definition). What must never
    // happen is the other direction, which the assertion above pins.
    assert!(
        rejected_and_unsound > 0,
        "the box must contain genuinely non-conservative pairs, or it proves nothing"
    );
}

#[test]
fn sweep_two_symbols_every_accept_is_conservative() {
    // Two symbols, each with one equality, over a family that includes the
    // cross-references `d1` and `d2` — which is how a mutual cycle is built.
    let family = vec![
        lin(1, 0, 0, 0, 0),
        lin(0, 1, 0, 0, 0),
        lin(0, 0, 0, 0, 0),
        lin(0, 0, 1, 1, 0),
        lin(0, 0, 1, 0, 1),
        lin(1, 0, 0, 0, 1),
        lin(0, 0, 0, 0, 1),
    ];
    let mut accepted = 0_usize;
    let mut cycles_rejected = 0_usize;
    for &lin1 in &family {
        for &lin2 in &family {
            let atoms = [
                AtomSpec {
                    symbol: 1,
                    kind: Kind::Eq,
                    lin: lin1,
                },
                AtomSpec {
                    symbol: 2,
                    kind: Kind::Eq,
                    lin: lin2,
                },
            ];
            if registry_accepts(&atoms) {
                accepted += 1;
                assert!(
                    conservative(&atoms, true),
                    "registry ACCEPTED a non-conservative two-symbol configuration: {atoms:?}"
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
fn sweep_two_symbols_one_equality_one_bound_every_accept_is_conservative() {
    // The cross-rule version of the cycle sweep: `d1` defined by an EQUALITY,
    // `d2` by a BOUND. A cycle spanning the two rules is only reachable if the
    // two share a registry, so this is where that sharing is exercised over
    // two symbols rather than one.
    let family = vec![
        lin(1, 0, 0, 0, 0),
        lin(0, 1, 0, 0, 0),
        lin(0, 0, 0, 0, 0),
        lin(0, 0, 1, 0, 1),
        lin(0, 0, 1, 1, 0),
    ];
    let mut accepted = 0_usize;
    let mut rejected = 0_usize;
    for &lin1 in &family {
        for &lin2 in &family {
            for kind2 in [Kind::Upper, Kind::Lower] {
                let atoms = [
                    AtomSpec {
                        symbol: 1,
                        kind: Kind::Eq,
                        lin: lin1,
                    },
                    AtomSpec {
                        symbol: 2,
                        kind: kind2,
                        lin: lin2,
                    },
                ];
                if registry_accepts(&atoms) {
                    accepted += 1;
                    assert!(
                        conservative(&atoms, true),
                        "registry ACCEPTED a non-conservative cross-rule configuration: {atoms:?}"
                    );
                } else {
                    rejected += 1;
                }
            }
        }
    }
    assert_eq!(accepted + rejected, 50);
    assert!(accepted > 0 && rejected > 0, "the box must be two-sided");
}

#[test]
fn the_canonical_witness_is_the_definiens_at_every_point_of_the_box() {
    // The soundness argument does not merely say a witness EXISTS — it names
    // it: `d := expr`. Check that specific assignment directly, independently
    // of the search above, for the equality form and for an equality carrying
    // its two agreeing bounds.
    for &lin in &single_symbol_family() {
        if lin.p != 0 {
            continue;
        }
        let atoms = [
            AtomSpec {
                symbol: 1,
                kind: Kind::Eq,
                lin,
            },
            AtomSpec {
                symbol: 1,
                kind: Kind::Upper,
                lin,
            },
            AtomSpec {
                symbol: 1,
                kind: Kind::Lower,
                lin,
            },
        ];
        assert!(registry_accepts(&atoms), "{atoms:?}");
        for x in -BOX..=BOX {
            for y in -BOX..=BOX {
                let witness = lin.value(x, y, 0, 0);
                assert!(
                    atoms.iter().all(|atom| atom.holds(x, y, witness, 0)),
                    "`d := lin` must satisfy every atom at ({x}, {y}) for {lin:?}"
                );
            }
        }
    }
}
