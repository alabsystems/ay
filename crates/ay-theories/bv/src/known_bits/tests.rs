// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Soundness of every transfer rule, exhaustively at small widths; soundness
//! of whole regions against brute force; and the replay contract (every
//! region refutation replays by unit propagation on the independent
//! encoding) on random cones.

use ay_core::term::{Symbol, TermData, TermId, TermStore};
use ay_core::Sort;
use num_bigint::BigInt;

use super::rules::{self, mask, CarryChain, KnownBits};
use super::*;

/// Every knowledge state of a `width`-bit value.
fn all_states(width: u32) -> Vec<KnownBits> {
    let mut out = Vec::new();
    for code in 0..3u32.pow(width) {
        let mut kb = KnownBits::UNKNOWN;
        let mut c = code;
        for bit in 0..width {
            match c % 3 {
                1 => kb.zero |= 1 << bit,
                2 => kb.one |= 1 << bit,
                _ => {}
            }
            c /= 3;
        }
        out.push(kb);
    }
    out
}

fn values(kb: KnownBits, width: u32) -> impl Iterator<Item = u64> {
    (0..=mask(width)).filter(move |&v| kb.admits(v))
}

fn sext(v: u64, from: u32, to: u32) -> u64 {
    let sign = (v >> (from - 1)) & 1;
    if sign == 1 {
        (v | (mask(to) & !mask(from))) & mask(to)
    } else {
        v
    }
}

fn signed(v: u64, width: u32) -> i64 {
    let s = sext(v, width, 64);
    s as i64
}

/// Check forward and backward soundness of a binary bitwise rule pair.
fn check_binary(
    width: u32,
    op: impl Fn(u64, u64) -> u64,
    fwd: impl Fn(KnownBits, KnownBits) -> KnownBits,
    bwd_a: impl Fn(KnownBits, KnownBits, KnownBits) -> KnownBits,
    bwd_b: impl Fn(KnownBits, KnownBits, KnownBits) -> KnownBits,
) {
    let states = all_states(width);
    for &ka in &states {
        for &kb in &states {
            let f = fwd(ka, kb);
            for a in values(ka, width) {
                for b in values(kb, width) {
                    let z = op(a, b) & mask(width);
                    assert!(
                        f.admits(z),
                        "fwd {ka:?} {kb:?} -> {f:?} misses {a} op {b} = {z}"
                    );
                    for &kz in &states {
                        if !kz.admits(z) {
                            continue;
                        }
                        let na = bwd_a(kz, ka, kb);
                        let nb = bwd_b(kz, ka, kb);
                        assert!(
                            na.admits(a),
                            "bwd_a {kz:?} {ka:?} {kb:?} -> {na:?} misses {a}"
                        );
                        assert!(
                            nb.admits(b),
                            "bwd_b {kz:?} {ka:?} {kb:?} -> {nb:?} misses {b}"
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn bitwise_rules_are_sound_exhaustively() {
    for w in 1..=3 {
        check_binary(
            w,
            |a, b| a & b,
            rules::and_fwd,
            |z, _, b| rules::and_bwd(z, b),
            |z, a, _| rules::and_bwd(z, a),
        );
        check_binary(
            w,
            |a, b| a | b,
            rules::or_fwd,
            |z, _, b| rules::or_bwd(z, b),
            |z, a, _| rules::or_bwd(z, a),
        );
        check_binary(
            w,
            |a, b| a ^ b,
            |a, b| rules::xor_fwd(a, b, w),
            |z, _, b| rules::xor_fwd(z, b, w),
            |z, a, _| rules::xor_fwd(z, a, w),
        );
        check_binary(
            w,
            |a, b| u64::from(a == b),
            |a, b| rules::eq_fwd(a, b, w),
            |z, a, b| rules::eq_bwd(z.restrict(1), a, b, w),
            |z, a, b| rules::eq_bwd(z.restrict(1), b, a, w),
        );
    }
}

#[test]
fn not_rule_is_sound_exhaustively() {
    for w in 1..=4 {
        for ka in all_states(w) {
            let f = rules::not_fwd(ka).restrict(mask(w));
            for a in values(ka, w) {
                let z = !a & mask(w);
                assert!(f.admits(z));
                for kz in all_states(w).into_iter().filter(|k| k.admits(z)) {
                    assert!(rules::not_bwd(kz).admits(a));
                }
            }
        }
    }
}

#[test]
fn ite_rules_are_sound_exhaustively() {
    for w in 1..=2 {
        let states = all_states(w);
        for kc in all_states(1) {
            for &kt in &states {
                for &ke in &states {
                    let f = rules::ite_fwd(kc, kt, ke);
                    for c in values(kc, 1) {
                        for t in values(kt, w) {
                            for e in values(ke, w) {
                                let z = if c == 1 { t } else { e };
                                assert!(f.admits(z));
                                for &kz in states.iter().filter(|k| k.admits(z)) {
                                    assert!(rules::ite_bwd_cond(kz, kt, ke).admits(c));
                                    assert!(rules::ite_bwd_branch(kz, kc, 1).admits(t));
                                    assert!(rules::ite_bwd_branch(kz, kc, 0).admits(e));
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn shift_rules_are_sound_exhaustively() {
    for w in 1..=4u32 {
        let states = all_states(w);
        for amount in 0..=u64::from(w) + 1 {
            let k = amount.min(63) as u32;
            for &ka in &states {
                for a in values(ka, w) {
                    let shl = if amount >= u64::from(w) {
                        0
                    } else {
                        (a << k) & mask(w)
                    };
                    let lshr = if amount >= u64::from(w) { 0 } else { a >> k };
                    let ashr = (signed(a, w) >> amount.min(u64::from(w - 1))) as u64 & mask(w);
                    assert!(rules::shl_fwd(ka, amount, w).admits(shl));
                    assert!(rules::lshr_fwd(ka, amount, w).admits(lshr));
                    assert!(rules::ashr_fwd(ka, amount, w).admits(ashr));
                    for &kz in &states {
                        if kz.admits(shl) {
                            assert!(rules::shl_bwd(kz, amount, w).admits(a));
                        }
                        if kz.admits(lshr) {
                            assert!(rules::lshr_bwd(kz, amount, w).admits(a));
                        }
                        if kz.admits(ashr) {
                            assert!(
                                rules::ashr_bwd(kz, amount, w).admits(a),
                                "ashr_bwd {kz:?} by {amount} at {w} misses {a}"
                            );
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn width_changing_rules_are_sound_exhaustively() {
    for wa in 1..=3u32 {
        let sa = all_states(wa);
        for wb in 1..=2u32 {
            let sb = all_states(wb);
            let wz = wa + wb;
            for &ka in &sa {
                for &kb in &sb {
                    let f = rules::concat_fwd(ka, kb, wb);
                    for a in values(ka, wa) {
                        for b in values(kb, wb) {
                            let z = (a << wb) | b;
                            assert!(f.admits(z));
                            for kz in all_states(wz).into_iter().filter(|k| k.admits(z)) {
                                assert!(rules::concat_bwd_high(kz, wb).admits(a));
                                assert!(rules::concat_bwd_low(kz, wb).admits(b));
                            }
                        }
                    }
                }
            }
        }
        for extra in 0..=2u32 {
            let wz = wa + extra;
            for &ka in &sa {
                for a in values(ka, wa) {
                    let z = a;
                    let s = sext(a, wa, wz);
                    assert!(rules::zext_fwd(ka, wa, wz).admits(z));
                    assert!(rules::sext_fwd(ka, wa, wz).admits(s));
                    for kz in all_states(wz) {
                        if kz.admits(z) {
                            assert!(kz.restrict(mask(wa)).admits(a));
                        }
                        if kz.admits(s) {
                            assert!(rules::sext_bwd(kz, wa, wz).admits(a));
                        }
                    }
                }
            }
        }
        for lo in 0..wa {
            for wz in 1..=wa - lo {
                for &ka in &sa {
                    for a in values(ka, wa) {
                        let z = (a >> lo) & mask(wz);
                        assert!(rules::extract_fwd(ka, lo, wz).admits(z));
                        for kz in all_states(wz).into_iter().filter(|k| k.admits(z)) {
                            assert!(rules::extract_bwd(kz, lo).admits(a));
                        }
                    }
                }
            }
        }
    }
}

/// The carry chain is sound: every concrete chain consistent with the input
/// knowledge is consistent with the output, and `None` means there is none.
#[test]
fn carry_chain_closure_is_sound_exhaustively() {
    for w in 1..=3u32 {
        let states = all_states(w);
        for carry_in in [false, true] {
            for &kx in &states {
                for &ky in &states {
                    for ks in states.iter().copied().map(Some).chain([None]) {
                        for kco in all_states(1) {
                            let chain = CarryChain {
                                x: kx,
                                y: ky,
                                sum: ks,
                                carry_out: kco,
                            };
                            let closed = rules::carry_chain_closure(chain, carry_in, w);
                            let mut any = false;
                            for x in values(kx, w) {
                                for y in values(ky, w) {
                                    let total = x + y + u64::from(carry_in);
                                    let s = total & mask(w);
                                    let co = total >> w;
                                    if ks.is_some_and(|k| !k.admits(s)) || !kco.admits(co) {
                                        continue;
                                    }
                                    any = true;
                                    let c = closed.unwrap_or_else(|| {
                                        panic!("closure refuted {chain:?} cin={carry_in} but {x}+{y} fits")
                                    });
                                    assert!(c.x.admits(x) && c.y.admits(y), "{chain:?} -> {c:?}");
                                    assert!(c.carry_out.admits(co), "{chain:?} -> {c:?}");
                                    if let Some(sum) = c.sum {
                                        assert!(sum.admits(s), "{chain:?} -> {c:?}");
                                    }
                                }
                            }
                            if !any {
                                // Incomplete is allowed; a claimed model is not checked here.
                                let _ = closed;
                            }
                        }
                    }
                }
            }
        }
    }
}

/// The word program and the per-bit schedule reach the same fixpoint.
#[test]
fn carry_chain_word_program_matches_per_bit_reference() {
    for w in 1..=3u32 {
        let states = all_states(w);
        for carry_in in [false, true] {
            for &kx in &states {
                for &ky in &states {
                    for ks in states.iter().copied().map(Some).chain([None]) {
                        for kco in all_states(1) {
                            let chain = CarryChain {
                                x: kx,
                                y: ky,
                                sum: ks,
                                carry_out: kco,
                            };
                            assert_eq!(
                                rules::carry_chain_closure(chain, carry_in, w),
                                reference_closure(chain, carry_in, w),
                                "{chain:?} cin={carry_in} w={w}"
                            );
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn compare_operand_mapping_round_trips() {
    for w in 1..=4u32 {
        for ka in all_states(w) {
            for kb in all_states(w).into_iter().take(9) {
                for signed in [false, true] {
                    let (x, y) = rules::compare_operands(ka, kb, signed, w);
                    let (a, b) = rules::compare_results(x, y, signed, w);
                    assert_eq!((a, b), (ka, kb));
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Whole regions on random cones.
// ---------------------------------------------------------------------------

/// A small deterministic generator (xorshift64*).
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545_f491_4f6c_dd1d)
    }

    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

const W: u32 = 4;

struct Gen<'a> {
    terms: &'a mut TermStore,
    rng: Rng,
    vars: Vec<TermId>,
}

impl Gen<'_> {
    fn app(&mut self, name: &str, args: &[TermId], sort: Sort) -> TermId {
        self.terms
            .mk_app_structural(Symbol::named(name), args, sort)
    }

    fn bv_const(&mut self) -> TermId {
        let v = self.rng.below(1 << W);
        self.terms.mk_bitvec(BigInt::from(v), W)
    }

    fn bv(&mut self, depth: u32) -> TermId {
        let bv = Sort::bitvec(W);
        if depth == 0 {
            return if self.rng.below(3) == 0 {
                self.bv_const()
            } else {
                let i = self.rng.below(self.vars.len() as u64) as usize;
                self.vars[i]
            };
        }
        let pick = self.rng.below(15);
        let a = self.bv(depth - 1);
        match pick {
            0 => {
                let b = self.bv_const_or(depth);
                self.app("bvand", &[a, b], bv)
            }
            1 => {
                let b = self.bv(depth - 1);
                self.app("bvor", &[a, b], bv)
            }
            2 => {
                let b = self.bv(depth - 1);
                self.app("bvxor", &[a, b], bv)
            }
            3 => self.app("bvnot", &[a], bv),
            4 => {
                let b = self.bv(depth - 1);
                self.app("bvadd", &[a, b], bv)
            }
            5 => {
                let b = self.bv(depth - 1);
                self.app("bvsub", &[a, b], bv)
            }
            6 => self.app("bvneg", &[a], bv),
            7 | 8 | 9 => {
                let amount = if self.rng.below(4) == 0 {
                    self.bv(0)
                } else {
                    let k = self.rng.below(u64::from(W) + 2);
                    self.terms.mk_bitvec(BigInt::from(k), W)
                };
                let name = ["bvshl", "bvlshr", "bvashr"][(pick - 7) as usize];
                self.app(name, &[a, amount], bv)
            }
            10 => {
                // concat of two extracts back to width W.
                let split = 1 + self.rng.below(u64::from(W) - 1) as u32;
                let b = self.bv(depth - 1);
                let hi = self.terms.mk_app_structural(
                    Symbol::indexed("extract", vec![split - 1, 0]),
                    [a],
                    Sort::bitvec(split),
                );
                let lo = self.terms.mk_app_structural(
                    Symbol::indexed("extract", vec![W - 1, split]),
                    [b],
                    Sort::bitvec(W - split),
                );
                self.app("concat", &[hi, lo], bv)
            }
            11 | 12 => {
                let from = 1 + self.rng.below(u64::from(W) - 1) as u32;
                let narrow = self.terms.mk_app_structural(
                    Symbol::indexed("extract", vec![from - 1, 0]),
                    [a],
                    Sort::bitvec(from),
                );
                let name = if pick == 11 {
                    "zero_extend"
                } else {
                    "sign_extend"
                };
                self.terms
                    .mk_app_structural(Symbol::indexed(name, vec![W - from]), [narrow], bv)
            }
            13 => {
                let c = self.boolean(depth - 1);
                let b = self.bv(depth - 1);
                self.terms.mk_ite(c, a, b)
            }
            _ => {
                // An operation outside the region's vocabulary: a leaf.
                let b = self.bv(depth - 1);
                self.app("bvmul", &[a, b], bv)
            }
        }
    }

    fn bv_const_or(&mut self, depth: u32) -> TermId {
        if self.rng.below(2) == 0 {
            self.bv_const()
        } else {
            self.bv(depth - 1)
        }
    }

    fn boolean(&mut self, depth: u32) -> TermId {
        let pick = self.rng.below(if depth == 0 { 3 } else { 8 });
        match pick {
            0 => {
                let (a, b) = (self.bv(depth), self.bv(depth));
                self.app("=", &[a, b], Sort::Bool)
            }
            1 | 2 => {
                let (a, b) = (self.bv(depth), self.bv(depth));
                let names = [
                    "bvult", "bvule", "bvslt", "bvsle", "bvugt", "bvuge", "bvsgt", "bvsge",
                ];
                let name = names[self.rng.below(names.len() as u64) as usize];
                self.app(name, &[a, b], Sort::Bool)
            }
            3 => {
                let a = self.boolean(depth - 1);
                self.terms.mk_not(a)
            }
            4 => {
                let (a, b) = (self.boolean(depth - 1), self.boolean(depth - 1));
                self.app("and", &[a, b], Sort::Bool)
            }
            5 => {
                let (a, b) = (self.boolean(depth - 1), self.boolean(depth - 1));
                self.app("or", &[a, b], Sort::Bool)
            }
            6 => {
                let (a, b) = (self.boolean(depth - 1), self.boolean(depth - 1));
                self.app("=>", &[a, b], Sort::Bool)
            }
            _ => {
                let (a, b) = (self.boolean(depth - 1), self.boolean(depth - 1));
                self.app("xor", &[a, b], Sort::Bool)
            }
        }
    }
}

/// Concrete evaluation for the test oracle (independent of the rules).
fn eval(terms: &TermStore, t: TermId, env: &[(TermId, u64)]) -> u64 {
    if let Some((_, v)) = env.iter().find(|(id, _)| *id == t) {
        return *v;
    }
    let width = match terms.sort(t) {
        Sort::Bool => 1,
        s => s.bitvec_width().expect("test terms are Bool or BV"),
    };
    let m = mask(width);
    let e = |x: TermId| eval(terms, x, env);
    let w_of = |x: TermId| terms.sort(x).bitvec_width().unwrap_or(1);
    match terms.get(t).clone() {
        TermData::Const(ay_core::term::Constant::Bool(b)) => u64::from(b),
        TermData::Const(ay_core::term::Constant::BitVec { value, .. }) => {
            value.to_u64_digits().1.first().copied().unwrap_or(0)
        }
        TermData::Not(a) => 1 - e(a),
        TermData::Ite(c, a, b) => {
            if e(c) == 1 {
                e(a)
            } else {
                e(b)
            }
        }
        TermData::App(sym, args) => {
            let v: Vec<u64> = args.iter().map(|&a| e(a)).collect();
            let wa = args.first().map_or(1, |&a| w_of(a));
            let sa = |x: u64| signed(x, wa);
            // The associative operators are n-ary; `=>` associates to the
            // right and `=` chains.
            let fold = |f: fn(u64, u64) -> u64| v[1..].iter().fold(v[0], |acc, &x| f(acc, x)) & m;
            match sym.name() {
                "bvand" | "and" => fold(|a, b| a & b),
                "bvor" | "or" => fold(|a, b| a | b),
                "bvxor" | "xor" => fold(|a, b| a ^ b),
                "bvnot" | "not" => !v[0] & m,
                "=>" => v[..v.len() - 1]
                    .iter()
                    .rev()
                    .fold(v[v.len() - 1], |acc, &p| u64::from(p == 0 || acc == 1)),
                "bvadd" => fold(u64::wrapping_add),
                "bvsub" => fold(u64::wrapping_sub),
                "bvneg" => v[0].wrapping_neg() & m,
                "bvmul" => fold(u64::wrapping_mul),
                "bvshl" => {
                    if v[1] >= u64::from(width) {
                        0
                    } else {
                        (v[0] << v[1]) & m
                    }
                }
                "bvlshr" => {
                    if v[1] >= u64::from(width) {
                        0
                    } else {
                        v[0] >> v[1]
                    }
                }
                "bvashr" => (signed(v[0], width) >> v[1].min(u64::from(width - 1))) as u64 & m,
                "=" => u64::from(v.windows(2).all(|p| p[0] == p[1])),
                "bvult" => u64::from(v[0] < v[1]),
                "bvule" => u64::from(v[0] <= v[1]),
                "bvugt" => u64::from(v[0] > v[1]),
                "bvuge" => u64::from(v[0] >= v[1]),
                "bvslt" => u64::from(sa(v[0]) < sa(v[1])),
                "bvsle" => u64::from(sa(v[0]) <= sa(v[1])),
                "bvsgt" => u64::from(sa(v[0]) > sa(v[1])),
                "bvsge" => u64::from(sa(v[0]) >= sa(v[1])),
                "extract" => {
                    let Symbol::Indexed(_, idx) = &sym else {
                        unreachable!()
                    };
                    (v[0] >> idx[1]) & m
                }
                "concat" => (v[0] << w_of(args[1])) | v[1],
                "zero_extend" => v[0],
                "sign_extend" => sext(v[0], wa, width),
                other => panic!("test evaluator: {other}"),
            }
        }
        other => panic!("test evaluator: {other:?}"),
    }
}

fn assignments(vars: &[TermId]) -> impl Iterator<Item = Vec<(TermId, u64)>> + '_ {
    let total = 1u64 << (W as usize * vars.len());
    (0..total).map(move |code| {
        vars.iter()
            .enumerate()
            .map(|(i, &v)| (v, (code >> (W as usize * i)) & mask(W)))
            .collect()
    })
}

/// A random obligation over two 4-bit variables: (terms, variables,
/// assertions).
fn random_obligation(seed: u64) -> (TermStore, Vec<TermId>, Vec<TermId>) {
    let mut terms = TermStore::new();
    let vars: Vec<TermId> = (0..2)
        .map(|i| terms.mk_var(format!("v{i}"), Sort::bitvec(W)))
        .collect();
    let mut g = Gen {
        terms: &mut terms,
        rng: Rng(seed.wrapping_mul(0x9e37_79b9_7f4a_7c15) | 1),
        vars: vars.clone(),
    };
    let count = 1 + g.rng.below(3);
    let depth = 1 + g.rng.below(3) as u32;
    let assertions: Vec<TermId> = (0..count).map(|_| g.boolean(depth)).collect();
    (terms, vars, assertions)
}

/// Every node's value under `env`, computed from the region's own semantics
/// (leaves from their source terms), so a test can tell a wrong derivation
/// from a wrong cone.
fn region_values(cone: &Cone, terms: &TermStore, env: &[(TermId, u64)]) -> Vec<u64> {
    use ay_jit::known_bits_region::KbOp;
    let nodes = &cone.region.nodes;
    let mut v: Vec<u64> = Vec::with_capacity(nodes.len());
    for (i, node) in nodes.iter().enumerate() {
        let w = node.width;
        let m = mask(w);
        let width = |x: u32| nodes[x as usize].width;
        let g = |x: u32| v[x as usize];
        let value = match node.op {
            KbOp::Leaf => eval(terms, cone.sources[i].expect("a leaf has a source"), env),
            KbOp::Const => cone.initial[i].one,
            KbOp::Not { a } => !g(a) & m,
            KbOp::And { a, b } => g(a) & g(b),
            KbOp::Or { a, b } => g(a) | g(b),
            KbOp::Xor { a, b } => g(a) ^ g(b),
            KbOp::Ite { c, t, e } => {
                if g(c) == 1 {
                    g(t)
                } else {
                    g(e)
                }
            }
            KbOp::Eq { a, b } => u64::from(g(a) == g(b)),
            KbOp::Cmp {
                a,
                b,
                signed: s,
                or_equal,
            } => {
                let wa = width(a);
                let (x, y) = if s {
                    (signed(g(a), wa) as i128, signed(g(b), wa) as i128)
                } else {
                    (i128::from(g(a)), i128::from(g(b)))
                };
                u64::from(if or_equal { x <= y } else { x < y })
            }
            KbOp::Add { a, b } => g(a).wrapping_add(g(b)) & m,
            KbOp::Sub { a, b } => g(a).wrapping_sub(g(b)) & m,
            KbOp::Neg { a } => g(a).wrapping_neg() & m,
            KbOp::Shl { a, s } => {
                if g(s) >= u64::from(w) {
                    0
                } else {
                    (g(a) << g(s)) & m
                }
            }
            KbOp::Lshr { a, s } => {
                if g(s) >= u64::from(w) {
                    0
                } else {
                    g(a) >> g(s)
                }
            }
            KbOp::Ashr { a, s } => {
                let amount = g(s).min(u64::from(w - 1));
                ((signed(g(a), w) >> amount) as u64) & m
            }
            KbOp::Extract { a, lo } => (g(a) >> lo) & m,
            KbOp::Concat { a, b } => ((g(a) << width(b)) | g(b)) & m,
            KbOp::Zext { a } => g(a),
            KbOp::Sext { a } => sext(g(a), width(a), w),
        };
        v.push(value);
    }
    v
}

/// Random cones: a region refutation is never wrong and always replays, and
/// at a fixpoint every derived fact admits every model.
#[test]
fn random_regions_are_sound_and_replay() {
    let mut refuted = 0;
    let mut fixpoints = 0;
    for seed in 1..=1500u64 {
        let (terms, vars, assertions) = random_obligation(seed);
        let cone = Cone::build(&terms, &assertions).expect("cone");
        cone.region.validate().expect("valid region");
        let mut state = cone.initial.clone();
        let mut trail = Vec::new();
        let status = run_interpreted(&cone.region, &mut state, &mut trail, DEFAULT_MAX_ROUNDS);
        let models: Vec<_> = assignments(&vars)
            .filter(|env| assertions.iter().all(|&a| eval(&terms, a, env) == 1))
            .collect();
        match status {
            RegionStatus::Conflict => {
                refuted += 1;
                assert!(models.is_empty(), "seed {seed}: refuted a satisfiable cone");
                replay_refutation(&terms, &assertions)
                    .unwrap_or_else(|r| panic!("seed {seed}: refutation does not replay: {r:?}"));
            }
            RegionStatus::Fixpoint => {
                fixpoints += 1;
                for env in &models {
                    // The cone means what its terms mean, and every trail
                    // entry admits the model.
                    let v = region_values(&cone, &terms, env);
                    for (node, source) in cone.sources.iter().enumerate() {
                        if let Some(term) = source {
                            assert_eq!(
                                v[node],
                                eval(&terms, *term, env),
                                "seed {seed}: node {node} {:?} disagrees with its term",
                                cone.region.nodes[node]
                            );
                        }
                    }
                    for (step, entry) in trail.iter().enumerate() {
                        let node = entry.node as usize;
                        assert!(
                            entry.bits.admits(v[node]),
                            "seed {seed}: trail step {step} gives node {node} {:?} {:?}, \
                             but a model has {}; nodes {:?}; initial {:?}; trail {:?}",
                            cone.region.nodes[node],
                            entry.bits,
                            v[node],
                            cone.region.nodes,
                            cone.initial,
                            &trail[..=step]
                        );
                    }
                    for (node, source) in cone.sources.iter().enumerate() {
                        if let Some(term) = source {
                            let value = eval(&terms, *term, env);
                            assert!(
                                state[node].admits(value),
                                "seed {seed}: node {node} {:?} knows {:?} but a model has {value}",
                                cone.region.nodes[node],
                                state[node]
                            );
                        }
                    }
                }
            }
            other => panic!("seed {seed}: unexpected {other:?}"),
        }
        // The trail is the record of every change, in order.
        let mut replayed = cone.initial.clone();
        for entry in &trail {
            let old = replayed[entry.node as usize];
            assert_eq!(
                old.union(entry.bits),
                entry.bits,
                "trail entries only add knowledge"
            );
            replayed[entry.node as usize] = entry.bits;
        }
        assert_eq!(replayed, state);
    }
    assert!(
        refuted > 50,
        "only {refuted} refutations: the test exercises too little"
    );
    assert!(fixpoints > 50, "only {fixpoints} fixpoints");
}

/// A mask-and-shift refutation the region decides, and its replay.
#[test]
fn mask_and_shift_obligation_is_refuted_and_replays() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(32));
    let mask_ff = terms.mk_bitvec(BigInt::from(0xffu32), 32);
    let eight = terms.mk_bitvec(BigInt::from(8u32), 32);
    let limit = terms.mk_bitvec(BigInt::from(0xffffu32), 32);
    let shifted = terms.mk_app_structural(Symbol::named("bvshl"), [x, eight], Sort::bitvec(32));
    let masked =
        terms.mk_app_structural(Symbol::named("bvand"), [shifted, mask_ff], Sort::bitvec(32));
    let or = terms.mk_app_structural(Symbol::named("bvor"), [masked, x], Sort::bitvec(32));
    let small = terms.mk_app_structural(Symbol::named("bvule"), [x, mask_ff], Sort::Bool);
    // ((x << 8) & 0xff) | x  >  0xffff  while  x <= 0xff: impossible.
    let big = terms.mk_app_structural(Symbol::named("bvugt"), [or, limit], Sort::Bool);
    let assertions = [small, big];
    let cone = Cone::build(&terms, &assertions).expect("cone");
    let mut state = cone.initial.clone();
    let mut trail = Vec::new();
    let status = run_interpreted(&cone.region, &mut state, &mut trail, DEFAULT_MAX_ROUNDS);
    assert_eq!(status, RegionStatus::Conflict);
    replay_refutation(&terms, &assertions).expect("replays");
}

/// The replay refuses a satisfiable obligation: the checker is not a rubber
/// stamp.
#[test]
fn replay_refuses_satisfiable_assertions() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(8));
    let c = terms.mk_bitvec(BigInt::from(3u32), 8);
    let lt = terms.mk_app_structural(Symbol::named("bvult"), [x, c], Sort::Bool);
    assert_eq!(
        replay_refutation(&terms, &[lt]),
        Err(ReplayRefusal::NotRefuted)
    );
}

/// The replay encoder agrees with evaluation on every operator it encodes:
/// fixing the inputs by unit clauses, the output's negation is refuted.
#[test]
fn replay_encoder_matches_evaluation() {
    let w = 3u32;
    let bv = Sort::bitvec(w);
    let binary = [
        "bvand", "bvor", "bvxor", "bvadd", "bvsub", "bvshl", "bvlshr", "bvashr",
    ];
    let compare = [
        "=", "bvult", "bvule", "bvslt", "bvsle", "bvugt", "bvuge", "bvsgt", "bvsge",
    ];
    for a in 0..(1u64 << w) {
        for b in 0..(1u64 << w) {
            let mut terms = TermStore::new();
            let x = terms.mk_var("x", bv.clone());
            let y = terms.mk_var("y", bv.clone());
            let ca = terms.mk_bitvec(BigInt::from(a), w);
            let cb = terms.mk_bitvec(BigInt::from(b), w);
            let fix_x = terms.mk_app_structural(Symbol::named("="), [x, ca], Sort::Bool);
            let fix_y = terms.mk_app_structural(Symbol::named("="), [y, cb], Sort::Bool);
            let env = [(x, a), (y, b)];
            for name in binary {
                let z = terms.mk_app_structural(Symbol::named(name), [x, y], bv.clone());
                let want = eval(&terms, z, &env);
                let cz = terms.mk_bitvec(BigInt::from(want), w);
                let eq = terms.mk_app_structural(Symbol::named("="), [z, cz], Sort::Bool);
                let ne = terms.mk_not(eq);
                assert!(
                    replay_refutation(&terms, &[fix_x, fix_y, ne]).is_ok(),
                    "{name} {a} {b} = {want} is not forced"
                );
                // And the value is consistent: the right answer is not refuted.
                assert!(replay_refutation(&terms, &[fix_x, fix_y, eq]).is_err());
            }
            for name in compare {
                let z = terms.mk_app_structural(Symbol::named(name), [x, y], Sort::Bool);
                let want = eval(&terms, z, &env);
                let wrong = if want == 1 { terms.mk_not(z) } else { z };
                assert!(
                    replay_refutation(&terms, &[fix_x, fix_y, wrong]).is_ok(),
                    "{name} {a} {b} = {want} is not forced"
                );
            }
        }
    }
}

// ---------------------------------------------------------------------------
// The per-bit reference schedule for the carry chain.
// ---------------------------------------------------------------------------

/// The chain's unit propagation one bit position at a time (low to high,
/// then high to low, until a round changes nothing): the schedule the word
/// program must agree with, since unit propagation has one fixpoint.
fn reference_closure(chain: CarryChain, carry_in: bool, width: u32) -> Option<CarryChain> {
    let mut state = ChainState::new(chain, carry_in, width);
    if state.is_conflict() {
        return None;
    }
    loop {
        let before = state.signature();
        for j in 0..width {
            if !state.step(j) {
                return None;
            }
        }
        for j in (0..width).rev() {
            if !state.step(j) {
                return None;
            }
        }
        if state.signature() == before {
            return Some(state.finish());
        }
    }
}

/// The chain's working values: operand knowledge plus carry knowledge
/// `carry_zero`/`carry_one` over carries `0..=width` (bit `j` is the carry
/// into position `j`; bit `width` is the carry out).
struct ChainState {
    x: KnownBits,
    y: KnownBits,
    sum: KnownBits,
    has_sum: bool,
    carry_zero: u128,
    carry_one: u128,
    width: u32,
}

impl ChainState {
    fn new(chain: CarryChain, carry_in: bool, width: u32) -> Self {
        let out = u128::from(chain.carry_out.zero & 1) << width;
        let out_one = u128::from(chain.carry_out.one & 1) << width;
        Self {
            x: chain.x,
            y: chain.y,
            sum: chain.sum.unwrap_or_default(),
            has_sum: chain.sum.is_some(),
            carry_zero: out | u128::from(!carry_in),
            carry_one: out_one | u128::from(carry_in),
            width,
        }
    }

    fn is_conflict(&self) -> bool {
        self.x.is_conflict()
            || self.y.is_conflict()
            || self.sum.is_conflict()
            || self.carry_zero & self.carry_one != 0
    }

    fn signature(&self) -> (KnownBits, KnownBits, KnownBits, u128, u128) {
        (self.x, self.y, self.sum, self.carry_zero, self.carry_one)
    }

    fn finish(self) -> CarryChain {
        let w = self.width;
        CarryChain {
            x: self.x,
            y: self.y,
            sum: self.has_sum.then_some(self.sum),
            carry_out: KnownBits {
                zero: ((self.carry_zero >> w) & 1) as u64,
                one: ((self.carry_one >> w) & 1) as u64,
            },
        }
    }

    /// One bit position's unit propagation. Returns false on a conflict.
    fn step(&mut self, j: u32) -> bool {
        let bit = 1u64 << j;
        let cin = 1u128 << j;
        let cout = 1u128 << (j + 1);
        // Tri-state reads: Some(value) when known.
        let read = |kb: KnownBits| -> Option<bool> {
            if kb.one & bit != 0 {
                Some(true)
            } else if kb.zero & bit != 0 {
                Some(false)
            } else {
                None
            }
        };
        let read_carry = |zero: u128, one: u128, at: u128| -> Option<bool> {
            if one & at != 0 {
                Some(true)
            } else if zero & at != 0 {
                Some(false)
            } else {
                None
            }
        };
        let x = read(self.x);
        let y = read(self.y);
        let c = read_carry(self.carry_zero, self.carry_one, cin);
        let co = read_carry(self.carry_zero, self.carry_one, cout);

        // Sum: any three of x, y, c, s give the fourth.
        if self.has_sum {
            let s = read(self.sum);
            match (x, y, c, s) {
                (Some(x), Some(y), Some(c), _) => set(&mut self.sum, bit, x ^ y ^ c),
                (Some(x), Some(y), None, Some(s)) => {
                    set_carry(&mut self.carry_zero, &mut self.carry_one, cin, x ^ y ^ s)
                }
                (Some(x), None, Some(c), Some(s)) => set(&mut self.y, bit, x ^ c ^ s),
                (None, Some(y), Some(c), Some(s)) => set(&mut self.x, bit, y ^ c ^ s),
                _ => {}
            }
        }
        // Re-read after the sum step.
        let x = read(self.x);
        let y = read(self.y);
        let c = read_carry(self.carry_zero, self.carry_one, cin);
        // Majority forward: two equal known inputs give the carry out.
        let inputs = [x, y, c];
        for v in [false, true] {
            if inputs.iter().filter(|i| **i == Some(v)).count() >= 2 {
                set_carry(&mut self.carry_zero, &mut self.carry_one, cout, v);
            }
        }
        // Majority backward: a carry out contradicted by one input forces the
        // other two to the carry out's value.
        let co = read_carry(self.carry_zero, self.carry_one, cout).or(co);
        if let Some(v) = co {
            if x == Some(!v) {
                set(&mut self.y, bit, v);
                set_carry(&mut self.carry_zero, &mut self.carry_one, cin, v);
            }
            if y == Some(!v) {
                set(&mut self.x, bit, v);
                set_carry(&mut self.carry_zero, &mut self.carry_one, cin, v);
            }
            if c == Some(!v) {
                set(&mut self.x, bit, v);
                set(&mut self.y, bit, v);
            }
        }
        !self.is_conflict()
    }
}

fn set(kb: &mut KnownBits, bit: u64, value: bool) {
    if value {
        kb.one |= bit;
    } else {
        kb.zero |= bit;
    }
}

fn set_carry(zero: &mut u128, one: &mut u128, at: u128, value: bool) {
    if value {
        *one |= at;
    } else {
        *zero |= at;
    }
}

// ---------------------------------------------------------------------------
// Bounded integers (Trust's machine-integer encoding).
// ---------------------------------------------------------------------------

/// Evaluate an integer or Boolean term with SMT-LIB integer semantics
/// (Booleans as 0/1, bit-vectors as their unsigned value).
fn eval_int(terms: &TermStore, t: TermId, env: &[(TermId, i128)]) -> i128 {
    use ay_core::term::Constant;
    use num_traits::ToPrimitive;
    if let Some((_, v)) = env.iter().find(|(id, _)| *id == t) {
        return *v;
    }
    let e = |x: TermId| eval_int(terms, x, env);
    match terms.get(t).clone() {
        TermData::Const(Constant::Bool(b)) => i128::from(b),
        TermData::Const(Constant::Int(v)) => v.to_i128().expect("small"),
        TermData::Const(Constant::BitVec { value, .. }) => value.to_i128().expect("small"),
        TermData::Not(a) => 1 - e(a),
        TermData::Ite(c, a, b) => {
            if e(c) == 1 {
                e(a)
            } else {
                e(b)
            }
        }
        TermData::App(sym, args) => {
            let v: Vec<i128> = args.iter().map(|&a| e(a)).collect();
            let bv_w = |x: TermId| i128::from(terms.sort(x).bitvec_width().unwrap_or(1));
            match sym.name() {
                "+" => v.iter().sum(),
                "-" if v.len() == 1 => -v[0],
                "-" => v[0] - v[1..].iter().sum::<i128>(),
                "*" => v.iter().product(),
                "div" => v[0].div_euclid(v[1]),
                "mod" => v[0].rem_euclid(v[1]),
                "<=" => i128::from(v[0] <= v[1]),
                "<" => i128::from(v[0] < v[1]),
                ">=" => i128::from(v[0] >= v[1]),
                ">" => i128::from(v[0] > v[1]),
                "=" => i128::from(v[0] == v[1]),
                "and" => i128::from(v.iter().all(|&x| x == 1)),
                "or" => i128::from(v.iter().any(|&x| x == 1)),
                "bv2nat" => v[0],
                "int2bv" => {
                    let w = terms.sort(t).bitvec_width().expect("bv");
                    v[0].rem_euclid(1i128 << w)
                }
                "bvand" => v[0] & v[1],
                "bvor" => v[0] | v[1],
                "bvshl" => {
                    let w = bv_w(t);
                    if v[1] >= w {
                        0
                    } else {
                        (v[0] << v[1]) & ((1 << w) - 1)
                    }
                }
                "bvlshr" => {
                    if v[1] >= bv_w(t) {
                        0
                    } else {
                        v[0] >> v[1]
                    }
                }
                other => panic!("eval_int: {other}"),
            }
        }
        other => panic!("eval_int: {other:?}"),
    }
}

/// Random bounded-integer obligations in Trust's shape: top-level bounds on
/// every variable, integer arithmetic, and bit operations reached through
/// `int2bv` and `bv2nat`. A region refutation is never wrong and replays.
#[test]
fn random_integer_regions_are_sound_and_replay() {
    let mut refuted = 0;
    for seed in 1..=1200u64 {
        let mut terms = TermStore::new();
        let mut rng = Rng(seed.wrapping_mul(0xd1b5_4a32_d192_ed03) | 1);
        let x = terms.mk_var("x", Sort::Int);
        let y = terms.mk_var("y", Sort::Int);
        let int = |terms: &mut TermStore, v: i64| terms.mk_int(BigInt::from(v));
        let app = |terms: &mut TermStore, name: &str, args: &[TermId], sort: Sort| {
            terms.mk_app_structural(Symbol::named(name), args, sort)
        };
        let mut bounds = Vec::new();
        // y is unbounded (never certified) in half the obligations.
        let y_bounded = rng.below(2) == 0;
        for v in [x, y] {
            if v == y && !y_bounded {
                continue;
            }
            let lo = int(&mut terms, 0);
            let hi = int(&mut terms, 15);
            bounds.push(app(&mut terms, "<=", &[lo, v], Sort::Bool));
            bounds.push(app(&mut terms, "<=", &[v, hi], Sort::Bool));
        }
        // Random integer terms over x, y.
        let mut pool = vec![x, y];
        for _ in 0..(2 + rng.below(4)) {
            let a = pool[rng.below(pool.len() as u64) as usize];
            let b = pool[rng.below(pool.len() as u64) as usize];
            let t = match rng.below(8) {
                0 => app(&mut terms, "+", &[a, b], Sort::Int),
                1 => app(&mut terms, "-", &[a, b], Sort::Int),
                2 => {
                    let c = int(&mut terms, [3, 4, -2, 5][rng.below(4) as usize]);
                    app(&mut terms, "*", &[c, a], Sort::Int)
                }
                3 => {
                    let c = int(&mut terms, [2, 4, 8][rng.below(3) as usize]);
                    app(&mut terms, "div", &[a, c], Sort::Int)
                }
                4 => {
                    let c = int(&mut terms, [2, 4, 8][rng.below(3) as usize]);
                    app(&mut terms, "mod", &[a, c], Sort::Int)
                }
                5 | 6 => {
                    let ba = terms.mk_app_structural(
                        Symbol::indexed("int2bv", vec![8]),
                        [a],
                        Sort::bitvec(8),
                    );
                    let bb = if rng.below(2) == 0 {
                        terms.mk_bitvec(BigInt::from(rng.below(256)), 8)
                    } else {
                        let k = terms.mk_bitvec(BigInt::from(rng.below(5)), 8);
                        app(&mut terms, "bvshl", &[ba, k], Sort::bitvec(8))
                    };
                    let op = if pick_and(&mut rng) { "bvand" } else { "bvor" };
                    let r = app(&mut terms, op, &[ba, bb], Sort::bitvec(8));
                    app(&mut terms, "bv2nat", &[r], Sort::Int)
                }
                _ => {
                    let c = int(&mut terms, rng.below(40) as i64 - 10);
                    let cond = app(&mut terms, "<", &[a, c], Sort::Bool);
                    terms.mk_ite(cond, a, b)
                }
            };
            pool.push(t);
        }
        // A violation over the generated terms.
        let p = pool[pool.len() - 1];
        let q = pool[rng.below(pool.len() as u64) as usize];
        let c = int(&mut terms, rng.below(60) as i64 - 10);
        let atom = match rng.below(4) {
            0 => app(&mut terms, ">", &[p, c], Sort::Bool),
            1 => app(&mut terms, "<", &[p, q], Sort::Bool),
            2 => app(&mut terms, "=", &[p, c], Sort::Bool),
            _ => app(&mut terms, ">=", &[p, c], Sort::Bool),
        };
        let mut conjuncts = bounds.clone();
        conjuncts.push(atom);
        let assertion = app(&mut terms, "and", &conjuncts, Sort::Bool);
        let assertions = [assertion];
        let cone = Cone::build(&terms, &assertions).expect("cone");
        let mut state = cone.initial.clone();
        let mut trail = Vec::new();
        let status = run_interpreted(&cone.region, &mut state, &mut trail, DEFAULT_MAX_ROUNDS);
        let y_range = if y_bounded { 0..16i128 } else { -64..64i128 };
        let satisfiable = (0..16i128).any(|vx| {
            y_range
                .clone()
                .any(|vy| eval_int(&terms, assertion, &[(x, vx), (y, vy)]) == 1)
        });
        if status == RegionStatus::Conflict {
            refuted += 1;
            assert!(
                !satisfiable,
                "seed {seed}: refuted a satisfiable obligation"
            );
            replay_refutation(&terms, &assertions)
                .unwrap_or_else(|r| panic!("seed {seed}: refutation does not replay: {r:?}"));
        }
        if satisfiable {
            assert!(
                replay_refutation(&terms, &assertions).is_err(),
                "seed {seed}: replay refuted a model"
            );
        }
    }
    assert!(refuted > 100, "only {refuted} refutations");
}

fn pick_and(rng: &mut Rng) -> bool {
    rng.below(2) == 0
}
