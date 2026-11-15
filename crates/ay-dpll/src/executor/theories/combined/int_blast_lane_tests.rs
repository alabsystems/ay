// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The Int-blast lane's reads of constant atoms, offset classes and residue
//! widths, checked against brute force, and its isolation from the caller's
//! term store (2026-09-24 fix-up of the bit-vector repair).

use super::*;

#[path = "int_blast_window_tests.rs"]
mod windows;

fn lit(v: i64) -> String {
    if v < 0 {
        format!("(- {})", -v)
    } else {
        v.to_string()
    }
}

/// `k·v REL c` on one member of the class, in one of four spellings.
#[derive(Clone, Copy)]
struct BoundAtom {
    /// 0 = `x`, 1 = `z`, 2 = `u`.
    member: usize,
    /// 0 `<=`, 1 `<`, 2 `>=`, 3 `>`.
    rel: u64,
    k: i64,
    c: i64,
    /// Written `(MIRROR c k·v)`.
    flip: bool,
    /// Written `(not (COMPLEMENT ...))`.
    negate: bool,
}

impl BoundAtom {
    fn draw(next: &mut impl FnMut(u64) -> u64, members: usize) -> Self {
        let k = [1, 1, 1, -1, 2, -2, 3, -3][next(8) as usize];
        Self {
            member: next(members as u64) as usize,
            rel: next(4),
            k,
            c: next(41) as i64 - 20 + if k.abs() > 1 { next(21) as i64 - 10 } else { 0 },
            flip: next(2) == 0,
            negate: next(3) == 0,
        }
    }

    fn holds(&self, v: i64) -> bool {
        let lhs = self.k * v;
        match self.rel {
            0 => lhs <= self.c,
            1 => lhs < self.c,
            2 => lhs >= self.c,
            _ => lhs > self.c,
        }
    }

    /// Whether the atom bounds `v` from above (else from below).
    fn is_upper(&self) -> bool {
        (self.rel < 2) == (self.k > 0)
    }

    fn smt(&self) -> String {
        let v = ["x", "z", "u"][self.member];
        let scaled = if self.k == 1 {
            v.to_string()
        } else {
            format!("(* {} {v})", lit(self.k))
        };
        let c = lit(self.c);
        // The relation actually written, before negation.
        let rel = if self.negate {
            // not (k·v > c) is k·v <= c, and so on.
            [">", ">=", "<", "<="][self.rel as usize]
        } else {
            ["<=", "<", ">=", ">"][self.rel as usize]
        };
        let atom = if self.flip {
            let mirror = match rel {
                "<=" => ">=",
                "<" => ">",
                ">=" => "<=",
                _ => "<",
            };
            format!("({mirror} {c} {scaled})")
        } else {
            format!("({rel} {scaled} {c})")
        };
        if self.negate {
            format!("(not {atom})")
        } else {
            atom
        }
    }
}

/// One generated query over `x` and the offset class `z = x + c1`,
/// `u = z + c2`: residue obligations on `x` and on `z` at their own widths,
/// up to two bound atoms on class members, excluded values of `x` (one
/// `distinct` of any arity), and sometimes a read of `x` under `or`.
struct LaneCase {
    wx: u32,
    ox: i64,
    op: u64,
    greater: bool,
    tx: i64,
    link_z: Option<i64>,
    link_u: Option<i64>,
    obligation_z: Option<(u32, bool, i64)>,
    bounds: Vec<BoundAtom>,
    excluded: Vec<i64>,
    elsewhere: Option<i64>,
}

impl LaneCase {
    fn draw(next: &mut impl FnMut(u64) -> u64) -> Self {
        let wx = 1 + next(5) as u32;
        let link_z = (next(2) == 0).then(|| next(11) as i64 - 5);
        let link_u = link_z.and_then(|_| (next(2) == 0).then(|| next(11) as i64 - 5));
        let obligation_z = link_z.and_then(|_| {
            (next(2) == 0).then(|| {
                let wz = 1 + next(5) as u32;
                (wz, next(2) == 0, next(1 << wz) as i64)
            })
        });
        let members = 1 + usize::from(link_z.is_some()) + usize::from(link_u.is_some());
        let bounds = (0..next(3))
            .map(|_| BoundAtom::draw(next, members))
            .collect();
        let excluded = match next(4) {
            0 => vec![next(41) as i64 - 20],
            1 => {
                let d = next(41) as i64 - 20;
                vec![d, d + 1 + next(5) as i64]
            }
            _ => Vec::new(),
        };
        Self {
            wx,
            ox: next(7) as i64 - 3,
            op: next(3),
            greater: next(2) == 0,
            tx: next(1 << wx) as i64,
            link_z,
            link_u,
            obligation_z,
            bounds,
            excluded,
            elsewhere: (next(4) == 0).then(|| next(41) as i64 - 20),
        }
    }

    fn smt(&self) -> String {
        let wx = self.wx;
        let conv = format!("((_ int2bv {wx}) (+ x {}))", lit(self.ox));
        let term = match self.op {
            0 => conv,
            1 => format!("(bvnot {conv})"),
            _ => format!("(bvneg {conv})"),
        };
        let cmp = if self.greater { ">" } else { "<" };
        let mut smt = format!(
            "(set-logic ALL) (declare-const x Int) (declare-const z Int) \
             (declare-const u Int) (assert ({cmp} (bv2nat {term}) {}))",
            self.tx
        );
        if let Some(c1) = self.link_z {
            smt.push_str(&format!(" (assert (= z (+ x {})))", lit(c1)));
        }
        if let Some(c2) = self.link_u {
            smt.push_str(&format!(" (assert (= u (+ z {})))", lit(c2)));
        }
        if let Some((wz, greater, tz)) = self.obligation_z {
            let cmp = if greater { ">" } else { "<" };
            smt.push_str(&format!(
                " (assert ({cmp} (bv2nat ((_ int2bv {wz}) z)) {tz}))"
            ));
        }
        for bound in &self.bounds {
            smt.push_str(&format!(" (assert {})", bound.smt()));
        }
        if !self.excluded.is_empty() {
            let values: Vec<String> = self.excluded.iter().map(|&d| lit(d)).collect();
            smt.push_str(&format!(" (assert (distinct {} x))", values.join(" ")));
        }
        if let Some(e) = self.elsewhere {
            smt.push_str(&format!(
                " (assert (or (<= x {}) (>= x {})))",
                lit(e),
                lit(e + 3)
            ));
        }
        smt
    }

    fn members(&self, x: i64) -> [i64; 3] {
        let z = x + self.link_z.unwrap_or(0);
        [x, z, z + self.link_u.unwrap_or(0)]
    }

    fn bounds_hold(&self, x: i64) -> bool {
        let members = self.members(x);
        self.bounds.iter().all(|b| b.holds(members[b.member]))
    }

    fn holds(&self, x: i64) -> bool {
        let residue = |v: i64, w: u32| v.rem_euclid(1 << w);
        let r = residue(x + self.ox, self.wx);
        let modulus = 1i64 << self.wx;
        let v = match self.op {
            0 => r,
            1 => modulus - 1 - r,
            _ => (modulus - r) % modulus,
        };
        let obligation_x = if self.greater {
            v > self.tx
        } else {
            v < self.tx
        };
        let z = self.members(x)[1];
        let obligation_z = self.obligation_z.is_none_or(|(wz, greater, tz)| {
            let v = residue(z, wz);
            if greater {
                v > tz
            } else {
                v < tz
            }
        });
        let elsewhere = self.elsewhere.is_none_or(|e| x <= e || x >= e + 3);
        obligation_x
            && obligation_z
            && self.bounds_hold(x)
            && !self.excluded.contains(&x)
            && elsewhere
    }

    fn two_sided(&self) -> bool {
        let upper = self.bounds.iter().any(BoundAtom::is_upper);
        let lower = self.bounds.iter().any(|b| !b.is_upper());
        upper && lower
    }

    /// `x` is read under `or` (`x <= e` or `x >= e + 3`) by a class not
    /// bounded on both sides: the window is cut at `e` and `e + 3`
    /// (#int-blast-split-points). Before the cut the lane had to decline
    /// these, because its window ignored the comparison.
    fn read_under_or_one_sided(&self) -> bool {
        self.elsewhere.is_some() && !self.two_sided()
    }

    /// Bounds with no integer between them: the lane may decline (an empty
    /// class interval) or refute; either way nothing is `sat`.
    fn bounds_are_empty(&self) -> bool {
        self.two_sided() && !(-300..=300).any(|x| self.bounds_hold(x))
    }
}

/// Generated queries spell the class's bounds in every way the lane reads
/// (`<`, `<=`, `>`, `>=`, either operand order, negated, scaled by `k`),
/// read the class at two residue widths, move bounds across one or two
/// offset equalities, exclude values with `distinct` of any arity and
/// sometimes read `x` under `or`. The lane decides each one as brute force
/// over `[-300, 300]` says (every window it builds lies inside it, and the
/// range holds every residue class of every cell, beyond any bound or
/// constant, several times over); it may decline only bounds with no
/// integer between them. A one-sided class read under `or` is decided
/// through its split points (#int-blast-split-points).
#[test]
fn lane_reads_constant_atoms_offsets_and_widths_as_brute_force_says() {
    let mut state = 0x1a4e_b0a5_7e57_2409u64;
    let mut next = |n: u64| {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state % n
    };
    let (mut sat, mut unsat, mut declined, mut split) = (0, 0, 0, 0);
    for case in 0..400 {
        let query = LaneCase::draw(&mut next);
        let smt = query.smt();
        let expected_sat = (-300..=300).any(|x| query.holds(x));
        let may_decline = query.bounds_are_empty();

        let commands = ay_frontend::parse(&smt).expect("valid query");
        let mut executor = Executor::new();
        executor.execute_all(&commands).expect("install query");
        let roots = executor.ctx.assertions.clone();
        let got = executor
            .solve_bv_lia_by_int_blast(&roots)
            .expect("probe does not error");
        let decided = match got {
            None if may_decline => {
                declined += 1;
                false
            }
            Some(result) if result.is_sat() && expected_sat => {
                sat += 1;
                true
            }
            Some(result) if result.is_unsat() && !expected_sat => {
                unsat += 1;
                true
            }
            other => panic!(
                "case {case}: {smt}\nbrute force says {}, the lane {other:?}",
                if expected_sat { "sat" } else { "unsat" },
            ),
        };
        split += usize::from(decided && query.read_under_or_one_sided());
    }
    assert!(
        sat > 80 && unsat > 30 && split > 40,
        "sat {sat}, unsat {unsat}, decided through split points {split}, declined {declined}"
    );
}

/// The lane builds its translation in the probe's clone of the term store:
/// the caller's store gains no term from it, and the model it publishes
/// names only terms the caller's store already had. A translation left in
/// the caller's store changed which candidate a later `check-sat` of the
/// session found and cost that check its verdict (`im_275_asis`).
#[test]
fn lane_leaves_the_callers_term_store_untouched() {
    for (query, expected_sat) in [
        (
            "(assert (< x 65509)) (assert (= ((_ int2bv 33) x) #b001010110110011010111001001011100))",
            true,
        ),
        (
            "(assert (<= x 5)) (assert (> (bv2nat ((_ int2bv 8) x)) 5)) (assert (distinct x (- 1)))",
            true,
        ),
        ("(assert (<= x 5)) (assert (> x 2)) (assert (= ((_ int2bv 2) x) #b10))", false),
    ] {
        let commands = ay_frontend::parse(&format!(
            "(set-logic ALL) (declare-const x Int) {query}"
        ))
        .expect("valid query");
        let mut executor = Executor::new();
        executor.execute_all(&commands).expect("install query");
        let roots = executor.ctx.assertions.clone();
        let terms_before = executor.ctx.terms.len();
        let got = executor
            .solve_bv_lia_by_int_blast(&roots)
            .expect("probe does not error");
        assert_eq!(
            got.as_ref().map(SolveResult::is_sat),
            Some(expected_sat),
            "{query}: the lane decides it"
        );
        let lane_terms = (0..executor.ctx.terms.len())
            .filter(|&id| {
                matches!(
                    executor.ctx.terms.get(TermId(id as u32)),
                    TermData::Var(name, _) if name.starts_with("__ay_bv_lia_i")
                )
            })
            .count();
        assert_eq!(lane_terms, 0, "{query}: a lane vector reached the caller's store");
        if !expected_sat {
            assert_eq!(executor.ctx.terms.len(), terms_before, "{query}");
            continue;
        }
        let model = executor.last_model.as_ref().expect("a validated SAT installs its model");
        let shared = |term: &TermId| (term.0 as usize) < terms_before;
        assert!(model.term_to_var.keys().all(shared), "{query}");
        assert!(model.bool_overrides.keys().all(shared), "{query}");
        let bv = model.bv_model.as_ref().expect("the blaster's model");
        assert!(bv.values.keys().all(shared), "{query}");
        assert!(bv.term_to_bits.keys().all(shared), "{query}");
    }
}

/// The parser never hands the lane `>`, `>=` or a `distinct` application:
/// `TermStore::mk_gt` / `mk_ge` swap into `<` / `<=`, and `mk_distinct`
/// expands into pairwise `(not (= a b))`. Terms other passes build with
/// `mk_app` can still carry them, so every spelling is built RAW here and
/// `constant_atom` must read exactly the bound brute force gives over
/// `[-60, 60]`: strict and non-strict, either operand order, negated, the
/// variable scaled by `k` (`(- v)` for `k = -1`, `(* v k)` otherwise).
#[test]
fn constant_atoms_read_raw_spellings_as_brute_force_says() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let mut checked = 0;
    for k in [1i64, -1, 2, -2, 3, -3, 5] {
        let scaled = match k {
            1 => x,
            -1 => terms.mk_app(Symbol::named("-"), vec![x], Sort::Int),
            _ => {
                let coefficient = terms.mk_int(BigInt::from(k));
                terms.mk_app(Symbol::named("*"), vec![x, coefficient], Sort::Int)
            }
        };
        for c in -9i64..=9 {
            let constant = terms.mk_int(BigInt::from(c));
            for rel in ["<", "<=", ">", ">="] {
                for constant_left in [false, true] {
                    let (lhs, rhs) = if constant_left {
                        (constant, scaled)
                    } else {
                        (scaled, constant)
                    };
                    let atom = terms.mk_app(Symbol::named(rel), vec![lhs, rhs], Sort::Bool);
                    for negate in [false, true] {
                        let atom = if negate { terms.mk_not_raw(atom) } else { atom };
                        let holds = |v: i64| {
                            let (l, r) = if constant_left {
                                (c, k * v)
                            } else {
                                (k * v, c)
                            };
                            let order = match rel {
                                "<" => l < r,
                                "<=" => l <= r,
                                ">" => l > r,
                                _ => l >= r,
                            };
                            order != negate
                        };
                        let Some(ConstantAtom::Bound { var, lower, upper }) =
                            constant_atom(&terms, atom)
                        else {
                            panic!("{rel} k={k} c={c} left={constant_left} not={negate}: not read");
                        };
                        assert_eq!(var, x);
                        for v in -60i64..=60 {
                            let read = lower.as_ref().is_none_or(|l| BigInt::from(v) >= *l)
                                && upper.as_ref().is_none_or(|u| BigInt::from(v) <= *u);
                            assert_eq!(
                                read,
                                holds(v),
                                "{rel} k={k} c={c} left={constant_left} not={negate} v={v}: \
                                 read [{lower:?}, {upper:?}]"
                            );
                        }
                        checked += 1;
                    }
                }
            }
        }
    }
    assert_eq!(checked, 7 * 19 * 4 * 2 * 2);
}

/// A raw `(distinct x c1 c2)` excludes TWO values, so the one-sided window
/// holds three integers of each residue class: `x <= 5` read mod 2^16 with
/// `5` and `5 - 2^16` excluded still has `5 - 2 * 2^16`. Counting the atom
/// as one exclusion leaves two integers of the class, both excluded, and the
/// lane would refute a satisfiable query. A repeated constant makes the atom
/// false; it is not read as a disequality at all.
#[test]
fn raw_nary_distinct_widens_the_window_per_excluded_value() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let five = terms.mk_int(BigInt::from(5));
    let at_most_five = terms.mk_le(x, five);
    let conv = terms.mk_int2bv(16, x);
    let hidden = terms.mk_bvnot(conv);
    let pin = terms.mk_bitvec(BigInt::from(0xfffa), 16);
    let residue_is_five = terms.mk_eq(hidden, pin);
    let below = terms.mk_int(BigInt::from(5 - 65536));
    let distinct = terms.mk_app(Symbol::named("distinct"), vec![x, five, below], Sort::Bool);
    assert!(matches!(
        constant_atom(&terms, distinct),
        Some(ConstantAtom::Disequality { excluded: 2, .. })
    ));
    let plan = IntBlastPlan::analyze(&terms, &[at_most_five, residue_is_five, distinct])
        .expect("x is half-bounded");
    assert_eq!(
        plan.synthetic,
        vec![(
            x,
            Interval {
                lo: BigInt::from(5 - 3 * 65536 + 1),
                hi: BigInt::from(5),
            }
        )]
    );

    let repeated = terms.mk_app(Symbol::named("distinct"), vec![x, five, five], Sort::Bool);
    assert!(constant_atom(&terms, repeated).is_none());
}
