// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Linear word-level lemmas: word expressions are bit-blasted the way the
//! checker does it, word relations become bit-level facts, and the
//! bit-serial chain prover discharges the target relation.

use super::chain::{cone, Chain, ChainResult};
use super::clean::{bb_equal, const_bits, neg_bits, rca, ult_bits};
use super::helpers::{eq_step, transfer, word_eq};
use super::proof::{Arg, Prem, Proof, S};
use super::term::{Op, T};
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};

/// Bit-blasts word expressions; every compound node gets a step `(= e (@bbterm bits))`.
pub(crate) struct Blaster {
    memo: HashMap<T, (Vec<T>, Option<S>)>,
    pub(crate) chains: Vec<Vec<T>>,
    opaque: HashSet<T>,
    pub(crate) leaf_bits: Vec<T>,
}

impl Blaster {
    pub(crate) fn new(opaque: &[T], known: &[(T, Vec<T>, S)]) -> Self {
        let mut b = Blaster {
            memo: HashMap::default(),
            chains: Vec::new(),
            opaque: opaque.iter().copied().collect(),
            leaf_bits: Vec::new(),
        };
        for (t, bits, s) in known {
            b.memo.insert(*t, (bits.clone(), Some(*s)));
        }
        b
    }

    fn respelled(&mut self, p: &mut Proof<'_>, e: T) -> Option<(Vec<T>, Vec<S>)> {
        let mut words = Vec::new();
        let mut prem = Vec::new();
        for &a in p.t.args(e).to_vec().iter() {
            let (bits, s) = self.blast(p, a)?;
            words.push(p.t.bb(&bits));
            prem.extend(s);
        }
        Some((words, prem))
    }

    fn finish(p: &mut Proof<'_>, e: T, re: T, bits: &[T], rule: &str, prem: &[S]) -> S {
        let w = p.t.bb(bits);
        let s2 = eq_step(p, re, w, rule, &[]);
        if prem.is_empty() {
            return s2;
        }
        let s1 = eq_step(p, e, re, "cong", prem);
        eq_step(p, e, w, "trans", &[s1, s2])
    }

    pub(crate) fn blast(&mut self, p: &mut Proof<'_>, e: T) -> Option<(Vec<T>, Option<S>)> {
        if let Some(r) = self.memo.get(&e) {
            return Some(r.clone());
        }
        let r = self.blast_node(p, e)?;
        self.memo.insert(e, r.clone());
        Some(r)
    }

    fn blast_node(&mut self, p: &mut Proof<'_>, e: T) -> Option<(Vec<T>, Option<S>)> {
        if self.opaque.contains(&e) || p.opaque.contains(&e) {
            return Some(Self::var(p, e));
        }
        match p.t.op(e).clone() {
            Op::BbTerm => {
                let bits = p.t.args(e).to_vec();
                self.leaf_bits.extend(&bits);
                Some((bits, None))
            }
            Op::Lit(v) => {
                let bits = const_bits(&p.t, &v);
                let w = p.t.bb(&bits);
                Some((bits, Some(eq_step(p, e, w, "bitblast_const", &[]))))
            }
            Op::Add => {
                let (words, prem) = self.respelled(p, e)?;
                let re = p.t.add(&words);
                let mut bits = p.t.bits(words[0]);
                for &w in &words[1..] {
                    let wb = p.t.bits(w);
                    let a = rca(&mut p.t, &bits, &wb, None);
                    self.chains.push(a.carries);
                    bits = a.sum;
                }
                Some((
                    bits.clone(),
                    Some(Self::finish(p, e, re, &bits, "bitblast_add", &prem)),
                ))
            }
            Op::Neg => {
                let (words, prem) = self.respelled(p, e)?;
                let re = p.t.neg(words[0]);
                let xb = p.t.bits(words[0]);
                let (bits, carries) = neg_bits(&mut p.t, &xb);
                self.chains.push(carries);
                Some((
                    bits.clone(),
                    Some(Self::finish(p, e, re, &bits, "bitblast_neg", &prem)),
                ))
            }
            Op::Concat => {
                let (words, prem) = self.respelled(p, e)?;
                let re = p.t.concat(&words);
                let mut bits = Vec::new();
                for &w in words.iter().rev() {
                    bits.extend(p.t.bits(w));
                }
                Some((
                    bits.clone(),
                    Some(Self::finish(p, e, re, &bits, "bitblast_concat", &prem)),
                ))
            }
            Op::ZeroExt(k) => {
                // the consumer's parsing boundary spells it as (concat (_ bv0 k) x)
                let z = p.t.lit(vec![false; k as usize]);
                let a = p.t.args(e)[0];
                let c = p.t.concat(&[z, a]);
                self.blast(p, c)
            }
            Op::Extract(hi, lo) => {
                let a = p.t.args(e)[0];
                let (b, s) = self.blast(p, a)?;
                let w = p.t.bb(&b);
                let bits = b[lo as usize..=hi as usize].to_vec();
                let re = p.t.extract(hi, lo, w);
                let prem: Vec<S> = s.into_iter().collect();
                Some((
                    bits.clone(),
                    Some(Self::finish(p, e, re, &bits, "bitblast_extract", &prem)),
                ))
            }
            _ => Some(Self::var(p, e)),
        }
    }

    fn var(p: &mut Proof<'_>, e: T) -> (Vec<T>, Option<S>) {
        let bits = p.t.bits(e);
        let w = p.t.bb(&bits);
        (bits, Some(eq_step(p, e, w, "bitblast_var", &[])))
    }
}

pub(crate) enum Kind {
    Eq { bits: usize },
    Ult { bits: usize },
}

/// `(= a circuit)` for a word atom `a` = `(= E1 E2)` or `(bvult E1 E2)`.
pub(crate) fn atom_bits(p: &mut Proof<'_>, b: &mut Blaster, a: T) -> Option<(S, T, Kind)> {
    let (e1, e2) = (p.t.args(a)[0], p.t.args(a)[1]);
    let (b1, s1) = b.blast(p, e1)?;
    let (b2, s2) = b.blast(p, e2)?;
    let (w1, w2) = (p.t.bb(&b1), p.t.bb(&b2));
    let prem: Vec<S> = s1.into_iter().chain(s2).collect();
    let is_eq = matches!(p.t.op(a), Op::Eq);
    let (ra, circ, kind, rule) = if is_eq {
        let ra = p.t.eq(w1, w2);
        (
            ra,
            bb_equal(&mut p.t, &b1, &b2),
            Kind::Eq { bits: b1.len() },
            "bitblast_equal",
        )
    } else {
        let ra = p.t.ult(w1, w2);
        let ch = ult_bits(&mut p.t, &b1, &b2);
        let mut chain = vec![p.t.ff];
        chain.extend(&ch);
        b.chains.push(chain);
        (
            ra,
            ch[ch.len() - 1],
            Kind::Ult { bits: b1.len() },
            "bitblast_ult",
        )
    };
    let sb = eq_step(p, ra, circ, rule, &[]);
    if ra == a {
        return Some((sb, circ, kind));
    }
    let sc = eq_step(p, a, ra, "cong", &prem);
    Some((eq_step(p, a, circ, "trans", &[sc, sb]), circ, kind))
}

#[derive(Default)]
pub(crate) struct LinOpts {
    pub(crate) params: Vec<(T, S)>,
    pub(crate) extra_chains: Vec<Vec<T>>,
    pub(crate) opaque: Vec<T>,
    pub(crate) known: Vec<(T, Vec<T>, S)>,
    pub(crate) defs: Vec<T>,
    pub(crate) opaque_leaves: bool,
    pub(crate) cut_extra: Vec<T>,
}

enum Plan {
    Out(Vec<(usize, usize)>),
    Fin(usize),
}

struct Setup {
    hyp_pos: HashMap<usize, Vec<S>>,
    hyp_at: Vec<(usize, S)>,
    params: Vec<(T, S)>,
}

fn add_hyps(p: &mut Proof<'_>, b: &mut Blaster, hyps: &[S], o: &LinOpts) -> Option<Setup> {
    let mut st = Setup {
        hyp_pos: HashMap::default(),
        hyp_at: Vec::new(),
        params: o.params.clone(),
    };
    for &sid in hyps {
        let lit = p.unit(sid);
        let (a, pol) = p.t.lit_of(lit);
        let word = matches!(p.t.op(a), Op::Eq | Op::Ult) && p.t.width(p.t.args(a)[0]) > 0;
        if !word {
            st.params.push((lit, sid));
            continue;
        }
        let (eqs, circ, kind) = atom_bits(p, b, a)?;
        let f = transfer(p, eqs, sid)?;
        match kind {
            Kind::Eq { bits } if pol => {
                for i in 0..bits {
                    let fi = if bits > 1 {
                        let c = p.t.args(circ)[i];
                        let nc = p.t.not(circ);
                        let ap = p.emit(&[nc, c], "and_pos", &[], &[Arg::Int(i)]);
                        p.derive(&[c], &[Prem::Step(ap), Prem::Step(f)], &[])?
                    } else {
                        f
                    };
                    st.hyp_pos.entry(i).or_default().push(fi);
                }
            }
            Kind::Eq { bits } | Kind::Ult { bits } => st.hyp_at.push((bits, f)),
        }
    }
    for &d in &o.defs {
        let (eqd, _, kind) = atom_bits(p, b, d)?;
        let (Kind::Eq { bits } | Kind::Ult { bits }) = kind;
        st.hyp_at.push((bits, eqd));
    }
    Some(st)
}

/// Prove each target literal (a word relation or its negation) from `hyps`.
pub(crate) fn lin_prove(
    p: &mut Proof<'_>,
    hyps: &[S],
    targets: &[T],
    o: &LinOpts,
) -> Option<Vec<S>> {
    let mut b = Blaster::new(&o.opaque, &o.known);
    let st = add_hyps(p, &mut b, hyps, o)?;
    let mut infos = Vec::new();
    for &t in targets {
        let (a, pol) = p.t.lit_of(t);
        let (eqs, circ, kind) = atom_bits(p, &mut b, a)?;
        infos.push((eqs, circ, kind, pol));
    }
    let n = infos
        .iter()
        .map(|i| match i.2 {
            Kind::Eq { bits } | Kind::Ult { bits } => bits,
        })
        .max()
        .unwrap_or(0);
    let len = b
        .chains
        .iter()
        .map(|c| c.len() - 1)
        .chain(std::iter::once(n))
        .max()
        .unwrap_or(n);
    let mut chain = Chain {
        bounds: vec![Vec::new(); len + 1],
        ..Chain::default()
    };
    for ch in b.chains.iter().chain(&o.extra_chains) {
        for i in 0..=len {
            chain.bounds[i].push(if i < ch.len() {
                ch[i]
            } else {
                ch[ch.len() - 1]
            });
        }
    }
    let mut plan = Vec::new();
    for (_, circ, kind, pol) in &infos {
        match kind {
            Kind::Eq { bits } if *pol => {
                let tb: Vec<T> = if *bits > 1 {
                    p.t.args(*circ).to_vec()
                } else {
                    vec![*circ]
                };
                let mut idx = Vec::new();
                for (i, &bit) in tb.iter().enumerate() {
                    let v = chain.outputs.entry(i).or_default();
                    v.push(vec![bit]);
                    idx.push((i, v.len() - 1));
                }
                plan.push(Plan::Out(idx));
            }
            _ => {
                let l = if *pol { *circ } else { p.t.not(*circ) };
                chain.finals.push(vec![l]);
                plan.push(Plan::Fin(chain.finals.len() - 1));
            }
        }
    }
    let mut cut: HashSet<T> = o.cut_extra.iter().copied().collect();
    for ch in b.chains.iter().chain(&o.extra_chains) {
        cut.extend(ch);
    }
    let mut leafcut = HashSet::default();
    if o.opaque_leaves {
        for &x in &b.leaf_bits {
            if !matches!(p.t.op(x), Op::True | Op::False | Op::Var(_) | Op::BitOf(_)) {
                leafcut.insert(x);
            }
        }
    }
    cut.extend(&leafcut);
    chain.hyps = st.hyp_pos.clone();
    add_carried(p, &mut chain, &cut, &leafcut);
    for (w, f) in st.hyp_at {
        if w >= len {
            chain.final_hyps.push(f);
        } else {
            chain.hyps.entry(w).or_default().push(f);
        }
    }
    chain.params = st.params;
    chain.cut = cut;
    chain.leafcut = leafcut;
    let res = chain.run(p)?;
    conclude(p, infos, plan, &res)
}

/// Each target from the chain's outputs or finals, transferred back from its
/// bit-level circuit to the atom.
fn conclude(
    p: &mut Proof<'_>,
    infos: Vec<(S, T, Kind, bool)>,
    plan: Vec<Plan>,
    res: &ChainResult,
) -> Option<Vec<S>> {
    let mut out = Vec::new();
    for ((eqs, circ, _, _), pl) in infos.into_iter().zip(plan) {
        let fin = match pl {
            Plan::Fin(k) => *res.finals.get(k)?,
            Plan::Out(idx) => {
                let mut prem = Vec::new();
                if matches!(p.t.op(circ), Op::And) {
                    let mut l = vec![circ];
                    for &c in p.t.args(circ).to_vec().iter() {
                        l.push(p.t.not(c));
                    }
                    prem.push(Prem::Step(p.emit(&l, "and_neg", &[], &[])));
                }
                for (i, j) in idx {
                    prem.push(Prem::Step(*res.outputs.get(&i)?.get(j)?));
                }
                p.derive(&[circ], &prem, &[])?
            }
        };
        out.push(transfer(p, eqs, fin)?);
    }
    Some(out)
}

pub(crate) fn lin1(p: &mut Proof<'_>, hyps: &[S], target: T, o: &LinOpts) -> Option<S> {
    lin_prove(p, hyps, &[target], o)?.pop()
}

/// Carry every leaf atom used at several bit positions through the boundaries between its uses.
fn add_carried(p: &Proof<'_>, chain: &mut Chain, cut: &HashSet<T>, leafcut: &HashSet<T>) {
    let len = chain.bounds.len() - 1;
    let mut stop = HashSet::default();
    for b in &chain.bounds {
        for &t in b {
            stop.insert(p.t.lit_of(t).0);
        }
    }
    let mut uses: HashMap<T, (usize, usize)> = HashMap::default();
    for i in 0..len {
        let mut tg: Vec<T> = chain.bounds[i + 1].clone();
        for cl in chain.outputs.get(&i).into_iter().flatten() {
            tg.extend(cl);
        }
        for &h in chain.hyps.get(&i).into_iter().flatten() {
            tg.extend(p.clause(h).to_vec());
        }
        for t in tg {
            let a0 = p.t.lit_of(t).0;
            let mut st2 = stop.clone();
            st2.remove(&a0);
            let (_, leaves) = cone(p, a0, &st2, cut, leafcut);
            for x in leaves {
                let a = p.t.lit_of(x).0;
                if stop.contains(&a) || matches!(p.t.op(a), Op::True | Op::False) {
                    continue;
                }
                let e = uses.entry(a).or_insert((i, i));
                e.0 = e.0.min(i);
                e.1 = e.1.max(i);
            }
        }
    }
    for (a, (lo, hi)) in uses {
        for bound in &mut chain.bounds[lo + 1..=hi] {
            bound.push(a);
        }
    }
}

/// From `(not (bvult x y))` and `(not (bvult y x))` over `@bbterm` words, `(= x y)`.
pub(crate) fn tri_eq(p: &mut Proof<'_>, xw: T, yw: T, nlt: S, ngt: S) -> Option<S> {
    let (xb, yb) = (p.t.bits(xw), p.t.bits(yw));
    let n = xb.len();
    let ch1 = ult_bits(&mut p.t, &xb, &yb);
    let ch2 = ult_bits(&mut p.t, &yb, &xb);
    let (u1, u2) = (p.t.ult(xw, yw), p.t.ult(yw, xw));
    let b1 = eq_step(p, u1, ch1[n - 1], "bitblast_ult", &[]);
    let b2 = eq_step(p, u2, ch2[n - 1], "bitblast_ult", &[]);
    let mut f1 = transfer(p, b1, nlt)?;
    let mut f2 = transfer(p, b2, ngt)?;
    let mut bits = vec![0; n];
    for i in (0..n).rev() {
        let mut prem = vec![Prem::Step(f1), Prem::Step(f2)];
        let lower = if i > 0 {
            [Some(ch1[i - 1]), Some(ch2[i - 1])]
        } else {
            [None, None]
        };
        for g in [ch1[i], ch2[i]] {
            level_gates(p, g, &lower, &mut prem);
        }
        let e = p.t.eq(xb[i], yb[i]);
        prem.extend(p.gate(e));
        bits[i] = p.derive(&[e], &prem, &[])?;
        if i > 0 {
            let (n1, n2) = (p.t.not(ch1[i - 1]), p.t.not(ch2[i - 1]));
            f1 = p.derive(&[n1], &prem, &[])?;
            f2 = p.derive(&[n2], &prem, &[])?;
        }
    }
    word_eq(p, xw, yw, &bits)
}

fn level_gates(p: &mut Proof<'_>, g: T, lower: &[Option<T>; 2], prem: &mut Vec<Prem>) {
    let mut stack = vec![g];
    let mut seen = HashSet::default();
    while let Some(u) = stack.pop() {
        if !seen.insert(u) || lower.contains(&Some(u)) {
            continue;
        }
        match p.t.op(u) {
            Op::And | Op::Or | Op::Eq => {
                prem.extend(p.gate(u));
                stack.extend(p.t.args(u).to_vec());
            }
            Op::Not => stack.extend(p.t.args(u).to_vec()),
            _ => {}
        }
    }
}
