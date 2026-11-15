// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Word-level slice identities over open bit-vector terms.
//!
//! x86 translation-validation queries spell one value two ways. The source
//! side keeps a 32-bit word (`(= p0 ((_ extract 31 0) e_rdi))`); the machine
//! side keeps it zero-extended in a 64-bit register and re-reads the low half
//! (`(= m0 ((_ zero_extend 32) ((_ extract 31 0) e_rdi)))`, then
//! `((_ extract 31 0) m0)`). The two reads are equal by one slice identity,
//! `extract(zero_extend(v)) = v`, and from there congruence carries the
//! equality through any operator, including a 64-bit `bvmul` whose bit-level
//! miter no SAT budget closes.
//!
//! The rewrite is applied THROUGH the closure, e-graph style: for a
//! registered `op(a)` (`op` an `extract`, `zero_extend` or `sign_extend`) and
//! a member `u` of `a`'s class whose own head is a slice operator, the term
//! `op(u)` is registered (congruence joins it to `op(a)`) and merged with its
//! one-level rewrite `r` by a [`EdgeReason::SliceIdentity`] edge. The edge
//! is emitted as the unit `BvBitBlast` lemma `(cl (= op(u) r))`, which the
//! strict checker re-derives by bit-blasting (a wiring identity: no
//! arithmetic circuit) and the printer lowers through Carcara's checked
//! `bitblast_*` rules. Nothing here is an authority: a wrong rewrite would be refused by
//! that checker and cost the lane its candidate, never soundness.
//!
//! The rewrites, for `v` of width `w`:
//!
//! | `op(u)`                                   | `r`                              |
//! |-------------------------------------------|----------------------------------|
//! | `extract[w-1:0](v)`                       | `v`                              |
//! | `extract[h:l](zero_extend_k(v))`, `h < w` | `extract[h:l](v)` (or `v`)       |
//! | `extract[h:l](zero_extend_k(v))`, `l ≥ w` | `#b0…0` (`h-l+1` bits)           |
//! | `extract[h:l](zero_extend_k(v))`, else    | `zero_extend_{h-w+1}(extract[w-1:l](v))` |
//! | `extract[h:l](sign_extend_k(v))`, `h < w` | `extract[h:l](v)` (or `v`)       |
//! | `extract[h:0](sign_extend_k(v))`, `h ≥ w` | `sign_extend_{h-w+1}(v)`         |
//! | `extract[h:l](extract[h2:l2](v))`         | `extract[h+l2:l+l2](v)` (or `v`) |
//! | `extract[h:l](concat(.., s, ..))`, `[h:l]` inside segment `s` | `extract` of `s` (or `s`) |
//! | `extract[h:l](c)`, `c` a constant         | the constant slice               |
//! | `zero_extend_0(v)`                        | `v`                              |
//! | `zero_extend_k(zero_extend_j(v))`         | `zero_extend_{k+j}(v)`           |
//! | `zero_extend_k(c)`, `c` a constant        | the widened constant             |
//! | `sign_extend_0(v)`                        | `v`                              |
//! | `sign_extend_k(sign_extend_j(v))`         | `sign_extend_{k+j}(v)`           |
//! | `sign_extend_k(c)`, `c` a constant        | the widened constant             |
//! | `op(ite(c, k1, k2))`, `k1`, `k2` constants | `ite(c, op(k1), op(k2))`, folded |
//!
//! Also propose `bvmul(v, 1) = v` (either orientation), plus one Boolean
//! identity for a flag computed by subtraction:
//! `(= (bvsub a b) #b0…0)` is `(= a b)`. The closure carries it into an `ite`
//! condition by congruence over `=`, `not` and `ite` (`saturate.rs`).

use super::state::EdgeReason;
use super::*;

/// Slice identities one search may propose.
const MAX_SLICE_IDENTITIES: usize = 512;
/// Class members one rewrite site may try.
pub(super) const MAX_MEMBERS_PER_SITE: usize = 8;

/// The slice view of one term.
enum Slice<'t> {
    Extract { high: u32, low: u32, arg: TermId },
    ZeroExtend { extra: u32, arg: TermId },
    SignExtend { extra: u32, arg: TermId },
    Concat(&'t [TermId]),
    Const { value: &'t BigInt, width: u32 },
}

fn slice_view(terms: &TermStore, term: TermId) -> Option<Slice<'_>> {
    match terms.get(term) {
        TermData::App(Symbol::Indexed(name, indices), args) if args.len() == 1 => {
            match (name.as_str(), indices.as_slice()) {
                ("extract", &[high, low]) if high >= low => Some(Slice::Extract {
                    high,
                    low,
                    arg: args[0],
                }),
                ("zero_extend", &[extra]) => Some(Slice::ZeroExtend {
                    extra,
                    arg: args[0],
                }),
                ("sign_extend", &[extra]) => Some(Slice::SignExtend {
                    extra,
                    arg: args[0],
                }),
                _ => None,
            }
        }
        TermData::App(Symbol::Named(name), args)
            if name.as_str() == "concat" && args.len() >= 2 =>
        {
            Some(Slice::Concat(args))
        }
        TermData::Const(Constant::BitVec { value, width }) => Some(Slice::Const {
            value,
            width: *width,
        }),
        _ => None,
    }
}

fn bv_width(terms: &TermStore, term: TermId) -> Option<u32> {
    terms.sort(term).bitvec_width().filter(|&width| width > 0)
}

impl Executor {
    /// A multiplication by the literal bit-vector unit. This only proposes
    /// the wiring identity; its equality is independently checked as a
    /// BvBitBlast lemma before any candidate can be committed.
    fn unit_product(&self, term: TermId) -> Option<TermId> {
        let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(term) else {
            return None;
        };
        if name != "bvmul" || args.len() != 2 {
            return None;
        }
        let sort = self.ctx.terms.sort(term);
        if sort.bitvec_width().is_none() || args.iter().any(|&a| self.ctx.terms.sort(a) != sort) {
            return None;
        }
        for (unit, value) in [(args[0], args[1]), (args[1], args[0])] {
            if matches!(self.ctx.terms.get(unit),TermData::Const(Constant::BitVec{value,..}) if *value==BigInt::from(1))
            {
                return Some(value);
            }
        }
        None
    }

    /// `extract[high:low](term)` spelled raw, or `term` itself for the full
    /// width.
    fn raw_extract(&mut self, high: u32, low: u32, term: TermId) -> Option<TermId> {
        let width = bv_width(&self.ctx.terms, term)?;
        if high < low || high >= width {
            return None;
        }
        if low == 0 && high + 1 == width {
            return Some(term);
        }
        Some(self.ctx.terms.mk_app(
            Symbol::indexed("extract", vec![high, low]),
            [term],
            Sort::bitvec(high - low + 1),
        ))
    }

    /// `zero_extend_extra(term)` spelled raw, or `term` itself for zero.
    fn raw_zero_extend(&mut self, extra: u32, term: TermId) -> Option<TermId> {
        let width = bv_width(&self.ctx.terms, term)?;
        if extra == 0 {
            return Some(term);
        }
        Some(self.ctx.terms.mk_app(
            Symbol::indexed("zero_extend", vec![extra]),
            [term],
            Sort::bitvec(width.checked_add(extra)?),
        ))
    }

    /// `sign_extend_extra(term)` spelled raw, or `term` itself for zero.
    fn raw_sign_extend(&mut self, extra: u32, term: TermId) -> Option<TermId> {
        let width = bv_width(&self.ctx.terms, term)?;
        if extra == 0 {
            return Some(term);
        }
        Some(self.ctx.terms.mk_app(
            Symbol::indexed("sign_extend", vec![extra]),
            [term],
            Sort::bitvec(width.checked_add(extra)?),
        ))
    }

    /// The one-level rewrite of `outer` applied to `member` in place of its
    /// argument (see the module table), or `None` when no rule applies.
    pub(super) fn slice_rewrite(&mut self, outer: TermId, member: TermId) -> Option<TermId> {
        if let Some(lifted) = self.slice_through_constant_ite(outer, member) {
            return Some(lifted);
        }
        let terms = &self.ctx.terms;
        match slice_view(terms, outer)? {
            Slice::Extract { high, low, .. } => self.extract_rewrite(high, low, member),
            Slice::ZeroExtend { extra, .. } => {
                if extra == 0 {
                    return Some(member);
                }
                match slice_view(terms, member)? {
                    Slice::ZeroExtend { extra: inner, arg } => {
                        self.raw_zero_extend(extra.checked_add(inner)?, arg)
                    }
                    Slice::Const { value, width } => {
                        let value = value.clone();
                        Some(self.ctx.terms.mk_bitvec(value, width.checked_add(extra)?))
                    }
                    _ => None,
                }
            }
            Slice::SignExtend { extra, .. } => {
                if extra == 0 {
                    return Some(member);
                }
                match slice_view(terms, member)? {
                    Slice::SignExtend { extra: inner, arg } => {
                        self.raw_sign_extend(extra.checked_add(inner)?, arg)
                    }
                    Slice::Const { value, width } => {
                        let negative = width > 0 && value.bit(u64::from(width - 1));
                        let mut value = value.clone();
                        if negative {
                            value |= ((BigInt::from(1) << extra) - 1) << width;
                        }
                        Some(self.ctx.terms.mk_bitvec(value, width.checked_add(extra)?))
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// The `extract[high:low]` rows of the module table, over `member`.
    fn extract_rewrite(&mut self, high: u32, low: u32, member: TermId) -> Option<TermId> {
        let terms = &self.ctx.terms;
        let member_width = bv_width(terms, member)?;
        if high >= member_width {
            return None;
        }
        if low == 0 && high + 1 == member_width {
            return Some(member);
        }
        match slice_view(terms, member)? {
            Slice::Const { value, .. } => {
                let mask = (BigInt::from(1) << (high - low + 1)) - 1;
                let sliced = (value >> low) & mask;
                Some(self.ctx.terms.mk_bitvec(sliced, high - low + 1))
            }
            Slice::ZeroExtend { arg, .. } => {
                let width = bv_width(terms, arg)?;
                if high < width {
                    self.raw_extract(high, low, arg)
                } else if low >= width {
                    Some(self.ctx.terms.mk_bitvec(BigInt::from(0), high - low + 1))
                } else {
                    let kept = self.raw_extract(width - 1, low, arg)?;
                    self.raw_zero_extend(high - width + 1, kept)
                }
            }
            Slice::SignExtend { arg, .. } => {
                let width = bv_width(terms, arg)?;
                if high < width {
                    self.raw_extract(high, low, arg)
                } else if low == 0 {
                    self.raw_sign_extend(high + 1 - width, arg)
                } else {
                    None
                }
            }
            Slice::Extract {
                low: inner_low,
                arg,
                ..
            } => self.raw_extract(
                high.checked_add(inner_low)?,
                low.checked_add(inner_low)?,
                arg,
            ),
            Slice::Concat(parts) => {
                let parts = parts.to_vec();
                let mut offset = 0u32;
                for &part in parts.iter().rev() {
                    let width = bv_width(&self.ctx.terms, part)?;
                    let end = offset.checked_add(width)?;
                    if low >= offset && high < end {
                        return self.raw_extract(high - offset, low - offset, part);
                    }
                    offset = end;
                }
                None
            }
        }
    }

    /// `op(ite(c, k1, k2))` for constant branches `k1`, `k2` is
    /// `ite(c, op(k1), op(k2))` with both branches folded to constants: a
    /// flag materialized as a byte (`(ite c #x01 #x00)`) and read back
    /// zero-extended or sliced. `None` unless `member` has that shape and
    /// `op` folds both branches.
    fn slice_through_constant_ite(&mut self, outer: TermId, member: TermId) -> Option<TermId> {
        let TermData::Ite(condition, then_term, else_term) = self.ctx.terms.get(member) else {
            return None;
        };
        let (condition, then_term, else_term) = (*condition, *then_term, *else_term);
        let constant = |terms: &TermStore, term| {
            matches!(terms.get(term), TermData::Const(Constant::BitVec { .. }))
        };
        if !constant(&self.ctx.terms, then_term) || !constant(&self.ctx.terms, else_term) {
            return None;
        }
        let then_folded = self.slice_rewrite(outer, then_term)?;
        let else_folded = self.slice_rewrite(outer, else_term)?;
        if !constant(&self.ctx.terms, then_folded) || !constant(&self.ctx.terms, else_folded) {
            return None;
        }
        Some(
            self.ctx
                .terms
                .mk_ite_raw(condition, then_folded, else_folded),
        )
    }

    /// `(= (bvsub a b) #b0..0)` (either orientation) is `(= a b)`: a flag
    /// computed by subtraction and a zero test. `None` for any other term.
    fn zero_difference_equality(&mut self, term: TermId) -> Option<TermId> {
        let (lhs, rhs) = decode_eq_local(&self.ctx.terms, term)?;
        let is_zero = |terms: &TermStore, side| {
            matches!(terms.get(side), TermData::Const(Constant::BitVec { value, .. })
                if value.sign() == num_bigint::Sign::NoSign)
        };
        let difference = if is_zero(&self.ctx.terms, rhs) {
            lhs
        } else if is_zero(&self.ctx.terms, lhs) {
            rhs
        } else {
            return None;
        };
        let TermData::App(symbol, args) = self.ctx.terms.get(difference) else {
            return None;
        };
        let [minuend, subtrahend] = args.as_slice() else {
            return None;
        };
        if symbol.name() != "bvsub" {
            return None;
        }
        let (minuend, subtrahend) = (*minuend, *subtrahend);
        Some(
            self.ctx
                .terms
                .mk_app(Symbol::named("="), [minuend, subtrahend], Sort::Bool),
        )
    }

    /// Whether `term` is a CLOSED extension: every leaf below it is a
    /// bit-vector literal and some node is a `zero_extend` or `sign_extend`.
    /// Such a slice is left to the evaluation edges and their operator
    /// policy (`EVALUATED_OPERATORS`): a closed `zero_extend` prints as
    /// Clean's `refl` to `concat`, which pinned Carcara refuses, so the lane
    /// never proposes one (`tests/operators.rs`). A closed `extract` stays
    /// admitted, as it is there. Bounded; a larger term is not closed.
    fn is_closed_extension(&self, term: TermId) -> bool {
        let mut pending = vec![term];
        let mut work = MAX_CLOSED_TERM_WORK;
        let mut extends = false;
        while let Some(current) = pending.pop() {
            let Some(remaining) = work.checked_sub(1) else {
                return false;
            };
            work = remaining;
            match self.ctx.terms.get(current) {
                TermData::Const(Constant::BitVec { .. }) => {}
                TermData::App(symbol, args) if !args.is_empty() => {
                    extends |= matches!(symbol.name(), "zero_extend" | "sign_extend");
                    pending.extend(args.iter().copied());
                }
                TermData::Ite(condition, then_term, else_term) => {
                    pending.extend([*condition, *then_term, *else_term]);
                }
                TermData::Not(inner) => pending.push(*inner),
                _ => return false,
            }
        }
        extends
    }

    /// One pass of unit-product and zero-difference identities over the registered
    /// equalities, then of slice rewriting over the registered `extract`,
    /// `zero_extend` and `sign_extend` applications; see the module
    /// documentation. `None` once the node bound is exceeded.
    pub(super) fn add_ground_slice_identity_edges(
        &mut self,
        closure: &mut GroundClosure,
        budget: &mut usize,
    ) -> Option<()> {
        let nodes = closure.nodes().to_vec();
        let mut members: ay_core::kani_compat::DetHashMap<usize, Vec<TermId>> =
            ay_core::kani_compat::DetHashMap::default();
        for &node in &nodes {
            if slice_view(&self.ctx.terms, node).is_some()
                || matches!(self.ctx.terms.get(node), TermData::Ite(..))
            {
                members.entry(closure.class(node)?).or_default().push(node);
            }
        }
        for &node in &nodes {
            if *budget == 0 {
                return Some(());
            }
            let Some(rewritten) = self
                .zero_difference_equality(node)
                .or_else(|| self.unit_product(node))
            else {
                continue;
            };
            if closure.same_class(node, rewritten) {
                continue;
            }
            self.register_ground_subterms(closure, rewritten)?;
            *budget -= 1;
            closure.merge(node, rewritten, EdgeReason::SliceIdentity);
        }
        for outer in nodes {
            let argument = match slice_view(&self.ctx.terms, outer) {
                Some(
                    Slice::Extract { arg, .. }
                    | Slice::ZeroExtend { arg, .. }
                    | Slice::SignExtend { arg, .. },
                ) => arg,
                _ => continue,
            };
            let mut candidates = vec![argument];
            if let Some(class_members) = closure.class(argument).and_then(|c| members.get(&c)) {
                candidates.extend(
                    class_members
                        .iter()
                        .copied()
                        .filter(|&member| member != argument)
                        .take(MAX_MEMBERS_PER_SITE),
                );
            }
            for member in candidates {
                if *budget == 0 {
                    return Some(());
                }
                let Some(rewritten) = self.slice_rewrite(outer, member) else {
                    continue;
                };
                let applied = if member == argument {
                    outer
                } else {
                    let TermData::App(symbol, _) = self.ctx.terms.get(outer) else {
                        continue;
                    };
                    let (symbol, sort) = (symbol.clone(), self.ctx.terms.sort(outer).clone());
                    self.ctx.terms.mk_app(symbol, [member], sort)
                };
                if applied == rewritten
                    || self.ctx.terms.sort(applied) != self.ctx.terms.sort(rewritten)
                    || closure.same_class(applied, rewritten)
                    || self.is_closed_extension(applied)
                {
                    continue;
                }
                self.register_ground_subterms(closure, applied)?;
                self.register_ground_subterms(closure, rewritten)?;
                *budget -= 1;
                closure.merge(applied, rewritten, EdgeReason::SliceIdentity);
            }
        }
        Some(())
    }
}

/// The per-search budget for [`Executor::add_ground_slice_identity_edges`].
pub(super) const fn slice_identity_budget() -> usize {
    MAX_SLICE_IDENTITIES
}
