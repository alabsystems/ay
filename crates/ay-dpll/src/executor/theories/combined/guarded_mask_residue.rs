// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The guarded alignment-mask residue of the BV<->LIA bridge
//! (#guarded-mask-residue).
//!
//! `TermStore::mk_bv2nat` folds `bv2nat(bvand(v, int2bv_w(c)))` for a
//! CONSTANT low-bit mask `c = 2^k - 1` to the residue `v mod 2^k`, so an
//! alignment check `p & 7` reaches arithmetic as `p mod 8`. Trust spells the
//! check over a MIR local: `(= m 7)` and
//! `(bv2nat (bvand (int2bv_64 p) (int2bv_64 m)))`. When the VC states
//! `(= m 7)` only inside each path disjunct, no constant reaches the fold.
//! The bridge's AUFLIA solve then treats the `bv2nat` term as an opaque Int,
//! its candidate model gives that Int a value no `p` realises, the model gate
//! over the original roots rejects it, and the query stops at
//! `unknown (incomplete)` (Trust `finalize_tail_realmir` line 437, 2026-11-08).
//!
//! The bridge therefore emits the fold's identity under the guard that makes
//! the mask constant. For every `bv2nat(B)`, `B = bvand(v, int2bv_w(m))`
//! (either operand order, one width `w`) with `m` not a constant, and every
//! Int equality atom `(= m c)` in the roots whose `c mod 2^w` is a low-bit
//! mask `2^k - 1` (`0 <= k <= w`):
//!
//! ```text
//!   (= m c)  ==>  (= bv2nat(B) (mod s 2^k))
//! ```
//!
//! where `s` is `x` when `v = int2bv_w(x)` and `bv2nat(v)` otherwise.
//!
//! SOUNDNESS. Under `m = c`, `int2bv_w(m)` is the vector of `c mod 2^w`
//! (SMT-LIB `int2bv`, negative `c` included), whose low `k` bits are set and
//! the rest clear. `bvand` with it keeps the low `k` bits of `v`, whose
//! unsigned value is `bv2nat(v) mod 2^k`; for `v = int2bv_w(x)` that is
//! `x mod 2^k`, because `int2bv_w(x)` is `x mod 2^w` and `2^k` divides `2^w`.
//! Each clause is a valid implication, so adding it removes no model. A SAT
//! is still published only after the model gate re-checks the ORIGINAL roots,
//! and a bridge UNSAT is still only a candidate that an independent
//! authentication must certify.
//!
//! SCOPE. Only an atom `(= m c)` that occurs in the roots guards a clause, so
//! the clauses add no guard atom the search does not already decide. A mask
//! pinned through a chain (`m = y`, `y = 7`) is not covered.

use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::{Sort, Symbol, TermData, TermId, TermStore};
use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::{One, Zero};

use super::super::super::Executor;
use super::{bv_width, collect_bv2nat_arg_subterms, int2bv_arg, int_const_value};

/// Clause budget per bridge solve: the clauses are `masks x guards`, and
/// past this many the bridge keeps what it has rather than grow the query.
const MAX_GUARDED_MASK_RESIDUE_CLAUSES: usize = 256;

/// One `bvand(value, int2bv_w(mask))` read under `bv2nat`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct MaskedRead {
    /// The `bvand` term `B`.
    and_term: TermId,
    /// The operand that is not the mask.
    value: TermId,
    /// The Int source `m` of the mask operand `int2bv_w(m)`.
    mask_source: TermId,
    /// The common width `w`.
    width: u32,
}

impl Executor {
    /// The guarded mask-residue clauses for `roots` (module doc).
    pub(super) fn collect_guarded_mask_residue_assertions(
        &mut self,
        roots: &[TermId],
    ) -> Vec<TermId> {
        guarded_mask_residue_clauses(&mut self.ctx.terms, roots)
    }
}

/// The clauses of the module doc, at most [`MAX_GUARDED_MASK_RESIDUE_CLAUSES`].
fn guarded_mask_residue_clauses(terms: &mut TermStore, roots: &[TermId]) -> Vec<TermId> {
    let reads = collect_masked_reads(terms, roots);
    if reads.is_empty() {
        return Vec::new();
    }
    let guards = collect_int_const_equalities(terms, roots);
    if guards.is_empty() {
        return Vec::new();
    }
    let mut out = Vec::new();
    let mut seen = HashSet::default();
    for read in reads {
        for (guard, _, value) in guards
            .iter()
            .filter(|(_, side, _)| *side == read.mask_source)
        {
            let Some(k) = low_bit_mask_width(value, read.width) else {
                continue;
            };
            let source = match int2bv_arg(terms, read.value, read.width) {
                Some(x) => x,
                None => terms.mk_bv2nat(read.value),
            };
            let modulus = terms.mk_int(BigInt::one() << k);
            let residue = terms.mk_mod(source, modulus);
            let nat = terms.mk_bv2nat(read.and_term);
            let read_is_residue = terms.mk_eq(nat, residue);
            let not_guard = terms.mk_not(*guard);
            let clause = terms.mk_or(vec![not_guard, read_is_residue]);
            if seen.insert(clause) {
                out.push(clause);
                if out.len() >= MAX_GUARDED_MASK_RESIDUE_CLAUSES {
                    return out;
                }
            }
        }
    }
    out
}

/// Every `bvand(v, int2bv_w(m))` that is a `bv2nat` argument in `roots`, once
/// per operand order whose second operand is such a mask with `m` not an Int
/// constant (a constant mask is `mk_bv2nat`'s own fold).
fn collect_masked_reads(terms: &TermStore, roots: &[TermId]) -> Vec<MaskedRead> {
    let mut out = Vec::new();
    for and_term in collect_bv2nat_arg_subterms(terms, roots) {
        let TermData::App(Symbol::Named(name), args) = terms.get(and_term) else {
            continue;
        };
        if name != "bvand" || args.len() != 2 {
            continue;
        }
        let Some(width) = bv_width(terms, and_term) else {
            continue;
        };
        for (value, mask) in [(args[0], args[1]), (args[1], args[0])] {
            if bv_width(terms, value) != Some(width) {
                continue;
            }
            let Some(mask_source) = int2bv_arg(terms, mask, width) else {
                continue;
            };
            if int_const_value(terms, mask_source).is_some() {
                continue;
            }
            out.push(MaskedRead {
                and_term,
                value,
                mask_source,
                width,
            });
        }
    }
    out
}

/// Every Int equality atom `(= t c)` / `(= c t)` in `roots` with `c` an Int
/// constant and `t` not, as `(atom, t, c)`, in first-visit order.
fn collect_int_const_equalities(
    terms: &TermStore,
    roots: &[TermId],
) -> Vec<(TermId, TermId, BigInt)> {
    let mut out = Vec::new();
    let mut seen = HashSet::default();
    let mut stack: Vec<TermId> = roots.iter().rev().copied().collect();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if let TermData::App(Symbol::Named(name), args) = terms.get(term) {
            if name == "=" && args.len() == 2 && *terms.sort(args[0]) == Sort::Int {
                match (
                    int_const_value(terms, args[0]),
                    int_const_value(terms, args[1]),
                ) {
                    (Some(c), None) => out.push((term, args[1], c)),
                    (None, Some(c)) => out.push((term, args[0], c)),
                    _ => {}
                }
            }
        }
        stack.extend(terms.children(term).into_iter().rev());
    }
    out
}

/// `Some(k)` when `c mod 2^width` is `2^k - 1`: the vector `int2bv_width(c)`
/// has exactly its low `k` bits set.
fn low_bit_mask_width(c: &BigInt, width: u32) -> Option<u32> {
    if width == 0 {
        return None;
    }
    let modulus = BigInt::one() << width;
    let residue = c.mod_floor(&modulus);
    let successor = residue + BigInt::one();
    // A power of two `2^k` has `bits() == k + 1` and no lower bit set.
    let k = successor.bits().checked_sub(1)?;
    let predecessor = &successor - BigInt::one();
    if (&successor & &predecessor).is_zero() {
        u32::try_from(k).ok()
    } else {
        None
    }
}

#[cfg(test)]
#[path = "guarded_mask_residue_tests.rs"]
mod tests;
