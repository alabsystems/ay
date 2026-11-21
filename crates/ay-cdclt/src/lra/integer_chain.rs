// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Before branching on an unbounded fractional vertex, combine the current
//! integer rows. Individual equalities can each have gcd one while their
//! combination has no integer solution. The existing exact cut-chain
//! validator derives the theorem; current SAT assignments only select its
//! literals and never serve as unchecked arithmetic authority.

use super::LraPlugin;
use crate::plugin::{Conflict, Ctx, GiveUp, ProofHint};
use ay_core::{Constant, Sort, Symbol, TermData, TermId, TermStore, TheoryLemmaKind, TheoryLit};

const MAX_ATOMS: usize = 16;
const MAX_OCCURRENCES: usize = 192;
const MAX_DEPTH: usize = 24;
const MAX_LITERAL_BITS: u64 = 256;
const MAX_ARGS: usize = 8;
const SEARCH_WORK: u64 = 65_536;

/// Preflight the physical incoming edges, all raw sorts and literal payloads
/// before the older recursive linearizer/cut proposer sees them. Opaque Int
/// applications are independent integer atoms, which needs no UF equation.
fn admitted(terms: &TermStore, roots: &[TermId]) -> bool {
    if roots.len() > MAX_ATOMS {
        return false;
    }
    let mut pending = Vec::with_capacity(MAX_OCCURRENCES);
    pending.extend(roots.iter().map(|&term| (term, 0usize)));
    let mut visited = 0usize;
    let mut bits = 0u64;
    while let Some((term, depth)) = pending.pop() {
        visited += 1;
        if visited > MAX_OCCURRENCES || depth > MAX_DEPTH || terms.entry_stamp(term).is_none() {
            return false;
        }
        let sort = terms.sort(term);
        let children = match terms.get(term) {
            TermData::Var(name, _) if name.len() <= 256 && sort == &Sort::Int => &[][..],
            TermData::Const(Constant::Int(value)) if sort == &Sort::Int => {
                bits = bits.saturating_add(value.bits());
                if bits > MAX_LITERAL_BITS {
                    return false;
                }
                &[][..]
            }
            TermData::App(Symbol::Named(name), args)
                if name.len() <= 256 && args.len() <= MAX_ARGS =>
            {
                let comparison = matches!(name.as_str(), "=" | "<" | "<=" | ">" | ">=");
                if if comparison {
                    depth != 0 || sort != &Sort::Bool || args.len() != 2
                } else {
                    sort != &Sort::Int
                } {
                    return false;
                }
                if matches!(name.as_str(), "+" | "*") && args.is_empty()
                    || name == "-" && !matches!(args.len(), 1 | 2)
                {
                    return false;
                }
                for &child in args {
                    if child.0 >= term.0
                        || terms.entry_stamp(child).is_none()
                        || terms.sort(child) != &Sort::Int
                    {
                        return false;
                    }
                }
                args.as_slice()
            }
            _ => return false,
        };
        if visited + pending.len() + children.len() > MAX_OCCURRENCES {
            return false;
        }
        pending.extend(children.iter().map(|&child| (child, depth + 1)));
    }
    true
}

impl LraPlugin {
    pub(super) fn integer_chain_conflict(&mut self, ctx: &mut Ctx<'_>) -> Result<bool, GiveUp> {
        if self.integer_chain_attempted {
            return Ok(false);
        }
        self.integer_chain_attempted = true;
        // Never scan an unbounded atom registry, truncate a candidate or retry
        // the allowance after a failed proposal. A miss keeps normal solving.
        if self.atom_terms.is_empty() || self.atom_terms.len() > MAX_ATOMS {
            return Ok(false);
        }
        ctx.tick((MAX_OCCURRENCES * 2) as u64)?;
        let mut reasons = Vec::with_capacity(self.atom_terms.len());
        for &atom in &self.atom_terms {
            let Some(value) = ctx.value(atom) else {
                continue;
            };
            if !ctx.is_relevant(atom) {
                continue;
            }
            let TermData::App(Symbol::Named(name), _) = ctx.terms().get(atom) else {
                continue;
            };
            if !matches!(name.as_str(), "=" | "<" | "<=" | ">" | ">=") || name == "=" && !value {
                continue;
            }
            reasons.push(TheoryLit::new(atom, value));
        }
        let atoms: Vec<_> = reasons.iter().map(|literal| literal.term).collect();
        if reasons.is_empty() || !admitted(ctx.terms(), &atoms) {
            return Ok(false);
        }
        // One prepaid bounded cut search, against the original live guard.
        ctx.tick(SEARCH_WORK)?;
        let clause: Vec<_> = reasons
            .iter()
            .map(|literal| {
                if literal.value {
                    ctx.terms_mut().mk_not_raw(literal.term)
                } else {
                    literal.term
                }
            })
            .collect();
        let valid =
            ay_core::proof_validation::lia_cut_chain_witness(ctx.terms(), &clause).is_some();
        ctx.tick(64)?;
        if !valid {
            return Ok(false);
        }
        ctx.conflict(Conflict {
            lits: reasons,
            hint: ProofHint::kind(TheoryLemmaKind::IntCgCutChain),
        });
        Ok(true)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn integer_chain_admission_rejects_raw_sort_and_payload_mismatches() {
        let mut terms = TermStore::new();
        let yes = terms.mk_bool(true);
        let bad_int = terms.mk_app(Symbol::named("opaque"), vec![yes], Sort::Int);
        let zero = terms.mk_int(0.into());
        let bad = terms.mk_eq(bad_int, zero);
        assert!(!admitted(&terms, &[bad]));
        let huge = terms.mk_int(num_bigint::BigInt::from(1u32) << 300);
        let too_big = terms.mk_eq(huge, zero);
        assert!(!admitted(&terms, &[too_big]));
    }

    #[test]
    fn integer_chain_admission_counts_repeated_edges_and_depth() {
        let mut terms = TermStore::new();
        let mut value = terms.mk_var("x", Sort::Int);
        let zero = terms.mk_int(0.into());
        for _ in 0..10 {
            value = terms.mk_app(Symbol::named("opaque"), vec![value, value], Sort::Int);
        }
        let repeated = terms.mk_eq(value, zero);
        assert!(!admitted(&terms, &[repeated]));
        let mut value = terms.mk_var("y", Sort::Int);
        for _ in 0..25 {
            value = terms.mk_app(Symbol::named("unary"), vec![value], Sort::Int);
        }
        let deep = terms.mk_eq(value, zero);
        assert!(!admitted(&terms, &[deep]));
    }
}
