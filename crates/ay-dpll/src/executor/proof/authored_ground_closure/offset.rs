// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Proof proposals for open modular constant offsets.
//!
//! The existing BV constructors combine constants modulo the word width.
//! Apply those same constructors to a raw offset and to offset-shaped members
//! of its operand's justified class. An identity edge proves only the applied
//! expression's normalization; ordinary congruence supplies the separate lift
//! from an aliased operand. Literal offset spines use the checked bounded
//! intrinsic; other admitted forms retain the shared modular affine checker.
//! The complete candidate still passes strict replay. No source term changes.

use super::slice::MAX_MEMBERS_PER_SITE;
use super::*;

#[derive(Clone, Copy)]
struct Offset {
    base: TermId,
    constant: TermId,
    subtract: bool,
    swapped: bool,
    width: u32,
}

// A syntactically closed addition prefix, not a value read from an assumed
// equality class. The existing constructor and affine checker own arithmetic;
// this walk only admits the spelling under the shared signature-work owner.
fn constant_add_prefix(
    terms: &TermStore,
    term: TermId,
    width: u32,
    work: &mut SharedGroundWork,
) -> Option<bool> {
    if !matches!(terms.get(term), TermData::App(Symbol::Named(name), _) if name == "bvadd") {
        return Some(false);
    }
    let mut pending = vec![term];
    while let Some(current) = pending.pop() {
        work.spend(1)?;
        if terms.entry_stamp(current).is_none() || terms.sort(current).bitvec_width() != Some(width)
        {
            return Some(false);
        }
        match terms.get(current) {
            TermData::Const(Constant::BitVec {
                value,
                width: literal_width,
            }) if *literal_width == width
                && value.sign() != num_bigint::Sign::Minus
                && value.bits() <= u64::from(width) => {}
            TermData::App(Symbol::Named(name), args) if name == "bvadd" && args.len() == 2 => {
                pending.extend(args.iter().copied());
            }
            _ => return Some(false),
        }
    }
    Some(true)
}

fn offset(terms: &TermStore, term: TermId, work: &mut SharedGroundWork) -> Option<Offset> {
    terms.entry_stamp(term)?;
    let width = terms
        .sort(term)
        .bitvec_width()
        .filter(|w| (1..=128).contains(w))?;
    let TermData::App(Symbol::Named(name), args) = terms.get(term) else {
        return None;
    };
    let &[left, right] = args.as_slice() else {
        return None;
    };
    if !matches!(name.as_str(), "bvadd" | "bvsub")
        || [left, right]
            .into_iter()
            .any(|arg| terms.entry_stamp(arg).is_none() || terms.sort(arg) != terms.sort(term))
    {
        return None;
    }
    let constant = |arg| matches!(terms.get(arg), TermData::Const(Constant::BitVec { .. }));
    let (base, constant, swapped) = match (constant(left), constant(right), name.as_str()) {
        (false, true, _) => (left, right, false),
        (true, false, "bvadd") => (right, left, true),
        (false, false, "bvadd") => {
            let left_constant = constant_add_prefix(terms, left, width, work)?;
            let right_constant = constant_add_prefix(terms, right, width, work)?;
            match (left_constant, right_constant) {
                (true, false) => (right, left, true),
                (false, true) => (left, right, false),
                _ => return None,
            }
        }
        _ => return None,
    };
    Some(Offset {
        base,
        constant,
        subtract: name == "bvsub",
        swapped,
        width,
    })
}

// `mk_bvadd` can follow a nested constant-addition spine. Pay for that walk
// before invoking it, including this preflight, through the search's existing
// signature-work allowance. Two open operands stop the constructor's offset
// chaining, so their interiors are opaque here too.
fn bounded_add_spine(
    terms: &TermStore,
    mut term: TermId,
    width: u32,
    work: &mut SharedGroundWork,
) -> Option<bool> {
    loop {
        work.spend(2)?;
        if terms.entry_stamp(term).is_none() || terms.sort(term).bitvec_width() != Some(width) {
            return Some(false);
        }
        let TermData::App(Symbol::Named(name), args) = terms.get(term) else {
            return Some(true);
        };
        if !matches!(name.as_str(), "bvadd" | "bvsub") {
            return Some(true);
        }
        let &[left, right] = args.as_slice() else {
            return Some(false);
        };
        if [left, right].into_iter().any(|arg| {
            terms.entry_stamp(arg).is_none() || terms.sort(arg).bitvec_width() != Some(width)
        }) {
            return Some(false);
        }
        // Addition may also cancel `c + (a - c)`. Validate that immediate
        // subtraction before the constructor can return its minuend.
        if name == "bvsub" {
            return Some(true);
        }
        let constant = |arg| matches!(terms.get(arg), TermData::Const(Constant::BitVec { .. }));
        term = match (constant(left), constant(right)) {
            (false, true) => left,
            (true, false) => right,
            _ => return Some(true),
        };
    }
}

impl Executor {
    /// Share the existing slice-identity proposal allowance. Class-member
    /// inspection has the same bound as slice rewriting, and introduced terms
    /// and merges retain the closure's ordinary node/edge caps.
    pub(super) fn add_ground_modular_offset_identity_edges(
        &mut self,
        closure: &mut GroundClosure,
        budget: &mut usize,
        work: &mut SharedGroundWork,
    ) -> Option<()> {
        if *budget == 0 {
            return Some(());
        }
        let nodes = closure.nodes().to_vec();
        let mut members: ay_core::kani_compat::DetHashMap<usize, Vec<TermId>> =
            ay_core::kani_compat::DetHashMap::default();
        for &node in &nodes {
            work.spend(1)?;
            if offset(&self.ctx.terms, node, work).is_some() {
                let members = members.entry(closure.class(node)?).or_default();
                if members.len() < MAX_MEMBERS_PER_SITE {
                    members.push(node);
                }
            }
        }
        let stop = self.make_proof_assembly_should_stop();
        for node in nodes {
            if *budget == 0 {
                return Some(());
            }
            if stop() {
                return None;
            }
            work.spend(1)?;
            let Some(shape) = offset(&self.ctx.terms, node, work) else {
                continue;
            };
            let compound_constant = !matches!(
                self.ctx.terms.get(shape.constant),
                TermData::Const(Constant::BitVec { .. })
            );
            let class_members = closure.class(shape.base).and_then(|c| members.get(&c));
            let mut candidates = vec![shape.base];
            if let Some(class_members) = class_members {
                if compound_constant {
                    // Normalize through one already justified, canonical add
                    // member first. Wait for a subtraction member's ordinary
                    // normalization rather than allocate both intermediate
                    // address families for every byte of a word.
                    let preferred = class_members.iter().copied().find(|&member| {
                        matches!(self.ctx.terms.get(member), TermData::App(Symbol::Named(name), args)
                            if name == "bvadd" && args.len() == 2
                                && matches!(self.ctx.terms.get(args[1]), TermData::Const(Constant::BitVec { .. })))
                    });
                    let Some(preferred) = preferred else {
                        continue;
                    };
                    candidates.clear();
                    candidates.push(preferred);
                } else {
                    candidates.extend(
                        class_members
                            .iter()
                            .copied()
                            .filter(|&member| member != shape.base),
                    );
                }
            }
            for member in candidates {
                if *budget == 0 {
                    return Some(());
                }
                if stop() {
                    return None;
                }
                if self.ctx.terms.sort(member) != self.ctx.terms.sort(shape.base) {
                    continue;
                }
                if !bounded_add_spine(&self.ctx.terms, member, shape.width, work)? {
                    continue;
                }
                let constant = if shape.subtract {
                    let TermData::Const(Constant::BitVec { value, .. }) =
                        self.ctx.terms.get(shape.constant)
                    else {
                        return None;
                    };
                    self.ctx.terms.mk_bitvec(-value.clone(), shape.width)
                } else {
                    shape.constant
                };
                let rewritten = self.ctx.terms.mk_bvadd(vec![member, constant]);
                if self.ctx.terms.sort(rewritten).bitvec_width() != Some(shape.width) {
                    continue;
                }
                let args = if shape.swapped {
                    [shape.constant, member]
                } else {
                    [member, shape.constant]
                };
                let name = if shape.subtract { "bvsub" } else { "bvadd" };
                let applied = if member == shape.base {
                    node
                } else {
                    self.ctx
                        .terms
                        .mk_app(Symbol::named(name), args, Sort::bitvec(shape.width))
                };
                if applied == rewritten || closure.same_class(applied, rewritten) {
                    continue;
                }
                if closure.edges().len() >= MAX_EDGES {
                    return None;
                }
                self.register_ground_subterms(closure, applied)?;
                self.register_ground_subterms(closure, rewritten)?;
                *budget -= 1;
                closure.merge(applied, rewritten, EdgeReason::ModularOffset);
            }
        }
        Some(())
    }
}
