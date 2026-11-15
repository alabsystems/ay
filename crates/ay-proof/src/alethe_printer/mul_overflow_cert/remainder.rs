// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! A source-instantiated remainder bound using a checked range-only stage.
//! No multiplication-row recognition, source assumptions, or sampled values.

use super::bits;
use super::div_lemma::zero_test;
use super::helpers::{eq_step, project, trans, transfer, word_eq};
use super::horner::body_from_clause;
use super::proof::{Prem, Proof, S};
use super::term::{Op, Sort, T};
use super::EmissionProgress;

mod range;
use range::RangeStage;

pub(in crate::alethe_printer) fn certificate(
    width: u32,
    dividend: &str,
    divisor: &str,
    prefix: &str,
    final_id: &str,
    clause: &str,
    progress: EmissionProgress<'_>,
) -> Option<String> {
    if !(1..=crate::checker::bv_urem_bound::MAX_WIDTH).contains(&width) {
        return None;
    }
    progress.poll().then_some(())?;
    let mut p = Proof::new_with_progress(format!("{final_id}.ur"), format!("{prefix}w"), progress);
    // These are already authenticated complete source-term spellings. Var
    // here is the certificate DAG's opaque word leaf, NOT a declaration or
    // a new free variable. `bitblast_var` projects that exact printed term.
    let x = p.t.var(dividend, Sort::Bv(width));
    let y = p.t.var(divisor, Sort::Bv(width));
    p.observe()?;
    let ds = RangeStage::new(&mut p, width, &format!("{prefix}s"))?;
    let proved = bound(&mut p, &ds, x, y)?;
    let theorem = p.unit(proved);
    p.observe()?;
    p.named_spelling = Some(clause.to_owned());
    p.emit_named(final_id, &[theorem], "reordering", &[proved]);
    p.observe()?;
    Some(p.out)
}

fn bound(p: &mut Proof<'_>, ds: &RangeStage, x: T, y: T) -> Option<S> {
    if p.t.width(x) != ds.n || p.t.width(y) != ds.n {
        return None;
    }
    p.observe()?;
    let zero = p.t.lit(bits::zero(ds.n));
    let is_zero = p.t.eq(y, zero);
    let nonzero = p.t.not(is_zero);
    let r = p.t.mk(Op::Urem, &[x, y]);
    let range = p.t.ult(r, y);
    let theorem = p.t.or(&[is_zero, range]);
    let anchor = p.anchor(&[]);
    let hypothesis = p.assume(nonzero);
    let yz = zero_test(p, y);
    let nonzero_bits = nonzero_bits(p, y, zero, yz, hypothesis)?;
    let range_fact = remainder_range(p, ds, x, y, r, yz, nonzero_bits)?;
    // The final step inside the subproof is the exact range fact.
    p.emit(&[range], "reordering", &[range_fact], &[]);
    let negated_guard = p.t.not(nonzero);
    let closed = p.close(anchor, &[negated_guard, range], "subproof", &[hypothesis]);
    let result = body_from_clause(p, theorem, closed)?;
    p.observe()?;
    Some(result)
}

/// Translate the source word's nonzero hypothesis to the divider's exact
/// conjunction of bit equalities. No assumption about a private bit replaces it.
fn nonzero_bits(p: &mut Proof<'_>, y: T, zero: T, yz: T, hypothesis: S) -> Option<S> {
    p.observe()?;
    let ybits = p.t.bits(y);
    let yword = p.t.bb(&ybits);
    let zbits = vec![p.t.ff; ybits.len()];
    let zword = p.t.bb(&zbits);
    let py = eq_step(p, y, yword, "bitblast_var", &[]);
    let pz = eq_step(p, zero, zword, "bitblast_const", &[]);
    let source_test = p.t.eq(y, zero);
    let word_test = p.t.eq(yword, zword);
    let same = eq_step(p, source_test, word_test, "cong", &[py, pz]);
    let bit_test = super::clean::bb_equal(&mut p.t, &ybits, &zbits);
    let bits = eq_step(p, word_test, bit_test, "bitblast_equal", &[]);
    let equivalence = if bit_test == yz {
        trans(p, &[same, bits])
    } else {
        // Width one: the checker collapses equality's single conjunction,
        // while the divider retains `(and (= bit false))` in its zero test.
        let equivalent = p.t.eq(bit_test, yz);
        let mut premises = p.gate(yz);
        premises.extend(p.gate(equivalent));
        let bridge = p.derive(&[equivalent], &premises, &[])?;
        trans(p, &[same, bits, bridge])
    };
    transfer(p, equivalence, hypothesis)
}

/// Project the range-only stage invariant's remainder fact, then connect the
/// exact Clean `bitblast_urem` outer zero-divisor mux to that stage word.
fn remainder_range(
    p: &mut Proof<'_>,
    ds: &RangeStage,
    x: T,
    y: T,
    r: T,
    yz: T,
    nonzero_bits: S,
) -> Option<S> {
    p.observe()?;
    let xb = p.t.bits(x);
    let yb = p.t.bits(y);
    let (stage_bits, invariant) = ds.specification(p, &xb, &yb, nonzero_bits)?;
    let mut rem = Vec::with_capacity(stage_bits.len());
    let mut equalities = Vec::with_capacity(stage_bits.len());
    for (&bit, &input) in stage_bits.iter().zip(&xb) {
        p.observe()?;
        let output = p.t.ite(yz, input, bit);
        let equality = p.t.eq(output, bit);
        let mut premises = p.gate(output);
        premises.extend(p.gate(equality));
        premises.push(Prem::Step(nonzero_bits));
        equalities.push(p.derive(&[equality], &premises, &[])?);
        rem.push(output);
    }
    let word = p.t.bb(&rem);
    let stage_word = p.t.bb(&stage_bits);
    let blast = eq_step(p, r, word, "bitblast_urem", &[]);
    let same_bits = word_eq(p, word, stage_word, &equalities)?;
    let same_rem = trans(p, &[blast, same_bits]);
    let yword = p.t.bb(&yb);
    let same_y = eq_step(p, y, yword, "bitblast_var", &[]);
    let source_range = p.t.ult(r, y);
    let stage_range = p.t.ult(stage_word, yword);
    let same_range = eq_step(p, source_range, stage_range, "cong", &[same_rem, same_y]);
    let projected = project(p, invariant, 0)?;
    let result = transfer(p, same_range, projected)?;
    p.observe()?;
    Some(result)
}

#[cfg(test)]
mod tests;
