// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Restoring-division range invariant, specialized by proof demand, not values.
//!
//! The algorithm and exact circuit are the existing `clean::udiv_stage`
//! (Clean's `bitblast_udiv_urem_rec`). The full specification in `div.rs`
//! also proves a quotient/product identity and a quotient cap. A remainder
//! bound uses neither. We retain exactly R < Y and R <= X: the second is
//! essential to prove the incoming remainder's top bit false, so doubling
//! it cannot silently lose a bit. Every fact below uses the same emitted
//! Boolean/bit-vector rules and local CDCL derivations as the full stage.

use super::super::clean::{udiv_stage, ult_bits, Stage};
use super::super::div::{gates_rec, shifted_x};
use super::super::helpers::{eq_step, forall_lemma, project, transfer, word_eq};
use super::super::horner::{and_from, body_from_clause};
use super::super::lin::{lin_prove, LinOpts};
use super::super::proof::{Prem, Proof, S};
use super::super::term::{Sort, T};

mod specification;
#[cfg(test)]
mod tests;

pub(super) struct RangeStage {
    pub(super) n: u32,
    r2: Vec<T>,
    x: Vec<T>,
    st: Stage,
    invp: T,
    invc: T,
    body: T,
    fact: S,
}

fn invariant(p: &mut Proof<'_>, r: &[T], x: &[T], y: &[T]) -> T {
    let (rw, xw, yw) = (p.t.bb(r), p.t.bb(x), p.t.bb(y));
    let range = p.t.ult(rw, yw);
    let exceeds = p.t.ult(xw, rw);
    let upper = p.t.not(exceeds);
    p.t.and(&[range, upper])
}

impl RangeStage {
    pub(super) fn new(p: &mut Proof<'_>, n: u32, prefix: &str) -> Option<Self> {
        p.observe()?;
        if !(1..=crate::checker::bv_urem_bound::MAX_WIDTH).contains(&n) {
            return None;
        }
        let mut words = Vec::new();
        for tag in ["r", "x", "y"] {
            let mut bits = Vec::new();
            for i in 0..n {
                p.observe()?;
                bits.push(p.t.var(&format!("{prefix}{tag}{i}"), Sort::Bool));
            }
            words.push(bits);
        }
        let (r2, x, y) = (words.remove(0), words.remove(0), words.remove(0));
        let q2 = vec![p.t.ff; n as usize];
        let st = udiv_stage(&mut p.t, &x, &y, &q2, &r2);
        let xs = shifted_x(p, &x);
        let invp = invariant(p, &r2, &xs, &y);
        let invc = invariant(p, &st.rem, &x, &y);
        let negative = p.t.not(invp);
        let body = p.t.or(&[negative, invc]);
        let mut vars = r2.clone();
        vars.extend(&x);
        vars.extend(&y);
        let mut stage = Self {
            n,
            r2,
            x,
            st,
            invp,
            invc,
            body,
            fact: 0,
        };
        p.observe()?;
        stage.fact = forall_lemma(p, &vars, |p| Some((body, stage.prove(p)?)))?;
        p.observe()?;
        Some(stage)
    }

    fn options(&self) -> LinOpts {
        let mut cut = self.st.c_sa.clone();
        cut.extend(&self.st.c_my);
        cut.extend(&self.st.c_lt);
        LinOpts {
            cut_extra: cut,
            ..LinOpts::default()
        }
    }

    fn prove(&self, p: &mut Proof<'_>) -> Option<S> {
        p.observe()?;
        let anchor = p.anchor(&[]);
        let previous = p.assume(self.invp);
        let range = project(p, previous, 0)?;
        let upper = project(p, previous, 1)?;
        let top = self.previous_top_is_false(p, upper)?;
        let mut cases = vec![self.case_less(p)?];
        for carry in [true, false] {
            p.observe()?;
            cases.push(self.case_ge(p, range, upper, top, carry)?);
        }
        let premises: Vec<_> = cases.into_iter().map(Prem::Step).collect();
        p.derive(&[self.invc], &premises, &[])?;
        let negative = p.t.not(self.invp);
        let closed = p.close(anchor, &[negative, self.invc], "subproof", &[previous]);
        let result = body_from_clause(p, self.body, closed)?;
        p.observe()?;
        Some(result)
    }

    fn previous_top_is_false(&self, p: &mut Proof<'_>, upper: S) -> Option<S> {
        p.observe()?;
        let xs = shifted_x(p, &self.x);
        let chain = ult_bits(&mut p.t, &xs, &self.r2);
        let (xw, rw) = (p.t.bb(&xs), p.t.bb(&self.r2));
        let comparison = p.t.ult(xw, rw);
        let last = *chain.last()?;
        let blasted = eq_step(p, comparison, last, "bitblast_ult", &[]);
        let fact = transfer(p, blasted, upper)?;
        let mut premises = gates_rec(p, last, 3);
        premises.push(Prem::Step(fact));
        let (ff, tt) = (p.t.ff, p.t.tt);
        premises.extend(p.gate(ff));
        premises.extend(p.gate(tt));
        let top = p.t.not(*self.r2.last()?);
        p.derive(&[top], &premises, &[])
    }

    fn bit_fact(p: &mut Proof<'_>, equality: T, gates: &[T], facts: &[S]) -> Option<S> {
        p.observe()?;
        let mut premises = Vec::new();
        for &gate in gates {
            premises.extend(p.gate(gate));
        }
        premises.extend(facts.iter().copied().map(Prem::Step));
        p.derive(&[equality], &premises, &[])
    }

    fn case_less(&self, p: &mut Proof<'_>) -> Option<S> {
        p.observe()?;
        let anchor = p.anchor(&[]);
        let less = p.assume(self.st.xlt);
        let mut bits = Vec::new();
        for (&output, &input) in self.st.rem.iter().zip(&self.x) {
            let equality = p.t.eq(output, input);
            bits.push(Self::bit_fact(p, equality, &[output, equality], &[less])?);
        }
        let (rw, xw) = (p.t.bb(&self.st.rem), p.t.bb(&self.x));
        let same = word_eq(p, rw, xw, &bits)?;
        let targets = p.t.args(self.invc).to_vec();
        let mut options = self.options();
        options.params = vec![(self.st.xlt, less)];
        options.extra_chains = vec![self.st.c_lt.clone()];
        let facts = lin_prove(p, &[same], &targets, &options)?;
        and_from(p, self.invc, &facts)?;
        let negative = p.t.not(self.st.xlt);
        let result = p.close(anchor, &[negative, self.invc], "subproof", &[less]);
        p.observe()?;
        Some(result)
    }

    fn case_ge(&self, p: &mut Proof<'_>, range: S, upper: S, top: S, carry: bool) -> Option<S> {
        p.observe()?;
        let anchor = p.anchor(&[]);
        let ge = p.t.not(self.st.xlt);
        let ge_fact = p.assume(ge);
        let carry_lit = if carry {
            self.st.co1
        } else {
            p.t.not(self.st.co1)
        };
        let carry_fact = p.assume(carry_lit);
        let target = if carry { &self.st.rmy } else { &self.st.r1sa };
        let mut bits = Vec::new();
        for (i, &output) in self.st.rem.iter().enumerate() {
            let equality = p.t.eq(output, target[i]);
            bits.push(Self::bit_fact(
                p,
                equality,
                &[output, self.st.r1sa2[i], equality],
                &[ge_fact, carry_fact],
            )?);
        }
        let (rw, target_word) = (p.t.bb(&self.st.rem), p.t.bb(target));
        let same = word_eq(p, rw, target_word, &bits)?;
        let mut options = self.options();
        options.params = vec![(ge, ge_fact), (carry_lit, carry_fact)];
        options.extra_chains = vec![self.st.c_my.clone(), self.st.c_sa.clone()];
        let hypotheses = if carry {
            vec![same, range, upper, top]
        } else {
            vec![same, upper]
        };
        let targets = p.t.args(self.invc).to_vec();
        let facts = lin_prove(p, &hypotheses, &targets, &options)?;
        and_from(p, self.invc, &facts)?;
        let (n1, n2) = (p.t.not(ge), p.t.not(carry_lit));
        let result = p.close(
            anchor,
            &[n1, n2, self.invc],
            "subproof",
            &[ge_fact, carry_fact],
        );
        p.observe()?;
        Some(result)
    }
}
