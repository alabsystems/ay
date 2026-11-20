// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Lazy completion of a BV congruence pass that stopped at its count cap
//! (#bv-congruence-lazy, wishlist AY-SMT-7).
//!
//! The eager pass (`generate_euf_bv_axioms_debug`) expands congruence for
//! every same-symbol pair of BV/Bool-result applications. On large QF_UFBV
//! files its clause or literal budget ends the pass, and a SAT under the
//! partial axiomatization used to become `unknown (incomplete)` at once
//! (QF_UFBV 9eb8ffea, 04135f62, 43ef76e6: `unknown` after 10 to 35 s of 48).
//!
//! Here the SAT model is checked against EVERY pair the full pass would have
//! emitted instead: the applications of one symbol are grouped by the values
//! of their argument literals (an argument with no literals by its term, as
//! the eager pass relates such arguments only when they are the same term),
//! and within a group every result must equal the first one. Each pair that
//! disagrees gets exactly the clauses the eager pass would have emitted for
//! it, which the current model falsifies, and the SAT solver runs again. A
//! model with no disagreeing pair satisfies every clause of the full pass
//! (the clauses of a pair whose arguments differ in the model are satisfied
//! by a difference variable), so it is as good as a model of the full
//! encoding; an UNSAT is sound because every added clause is a congruence
//! axiom. The loop is bounded by the same literal budget as the eager pass
//! and stops at a deadline, interrupt or memory stop, leaving the bail in
//! place.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{Sort, TermId};
use ay_sat::{SatResult, Solver as SatSolver};

use super::super::Executor;
use super::{ChainSpend, CongruenceBail};

/// Literal budget for the clauses the lazy loop adds, the eager pass's own.
const MAX_LAZY_CONGRUENCE_LITERALS: usize = 16_000_000;

/// One argument of an application as the congruence encoding sees it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum CongruenceArg {
    /// BV bits (or one Bool literal), DIMACS literals in the SAT solver's
    /// space; `bool_sorted` keeps a Bool literal apart from a one-bit vector.
    Lits { bool_sorted: bool, lits: Vec<i32> },
    /// No literals: related to another argument only when it is the same term.
    Opaque(TermId),
}

/// One application of a congruence group: its result literals and arguments.
#[derive(Clone, Debug)]
pub(super) struct CongruenceApp {
    pub(super) result_bool: bool,
    pub(super) result: Vec<i32>,
    pub(super) args: Vec<CongruenceArg>,
}

#[derive(Hash, PartialEq, Eq)]
enum ArgKey {
    Bits(bool, Vec<bool>),
    Term(TermId),
}

fn lit_value(model: &[bool], lit: i32) -> Option<bool> {
    let index = usize::try_from(lit.unsigned_abs()).ok()?.checked_sub(1)?;
    let value = *model.get(index)?;
    Some(if lit > 0 { value } else { !value })
}

fn lits_value(model: &[bool], lits: &[i32]) -> Option<Vec<bool>> {
    lits.iter().map(|&lit| lit_value(model, lit)).collect()
}

/// The congruence clauses of one pair, exactly as the eager pass encodes
/// them: `d_j <-> (a_j xor b_j)` for each differing argument bit, then
/// `d_1 | ... | d_k | ~r1_i | r2_i` and `d_1 | ... | d_k | r1_i | ~r2_i` for
/// each result bit. Fresh variables are taken from `next_var` upwards.
fn pair_clauses(
    left: &CongruenceApp,
    right: &CongruenceApp,
    next_var: &mut u32,
    out: &mut Vec<Vec<i32>>,
) -> Option<()> {
    let mut diff_vars = Vec::new();
    for (a, b) in left.args.iter().zip(&right.args) {
        let (CongruenceArg::Lits { lits: la, .. }, CongruenceArg::Lits { lits: lb, .. }) = (a, b)
        else {
            // Same term (the grouping guarantees it): no difference.
            continue;
        };
        for (&bit1, &bit2) in la.iter().zip(lb) {
            if bit1 == bit2 {
                continue;
            }
            *next_var = next_var.checked_add(1)?;
            let d = i32::try_from(*next_var).ok()?;
            diff_vars.push(d);
            out.push(vec![-d, bit1, bit2]);
            out.push(vec![-d, -bit1, -bit2]);
            out.push(vec![-bit1, bit2, d]);
            out.push(vec![bit1, -bit2, d]);
        }
    }
    for (&r1, &r2) in left.result.iter().zip(&right.result) {
        if r1 == r2 {
            continue;
        }
        let mut c1 = diff_vars.clone();
        c1.extend([-r1, r2]);
        out.push(c1);
        let mut c2 = diff_vars.clone();
        c2.extend([r1, -r2]);
        out.push(c2);
    }
    Some(())
}

/// The clauses of every congruence pair `model` violates, over `groups`
/// (the applications of one symbol each). `Some(empty)` means the model is
/// congruent on every pair; `None` means some literal has no value in the
/// model (or variables ran out), so nothing can be concluded.
pub(super) fn violated_congruence_clauses(
    groups: &[Vec<CongruenceApp>],
    model: &[bool],
    next_var: &mut u32,
) -> Option<Vec<Vec<i32>>> {
    let mut out = Vec::new();
    for apps in groups {
        let mut first_of: HashMap<(bool, usize, Vec<ArgKey>), usize> = HashMap::default();
        for (index, app) in apps.iter().enumerate() {
            let mut key = Vec::with_capacity(app.args.len());
            for arg in &app.args {
                key.push(match arg {
                    CongruenceArg::Lits { bool_sorted, lits } => {
                        ArgKey::Bits(*bool_sorted, lits_value(model, lits)?)
                    }
                    CongruenceArg::Opaque(term) => ArgKey::Term(*term),
                });
            }
            let key = (app.result_bool, app.result.len(), key);
            match first_of.get(&key) {
                None => {
                    first_of.insert(key, index);
                }
                Some(&rep) => {
                    let rep_app = &apps[rep];
                    if lits_value(model, &rep_app.result)? != lits_value(model, &app.result)? {
                        pair_clauses(rep_app, app, next_var, &mut out)?;
                    }
                }
            }
        }
    }
    Some(out)
}

impl Executor {
    /// The congruence groups the eager BV pass works on, with every literal
    /// shifted into the SAT solver's space by `bv_offset`.
    fn lazy_congruence_groups(
        &self,
        term_bits: &HashMap<TermId, Vec<i32>>,
        bool_to_var: &HashMap<TermId, i32>,
        bv_offset: i32,
        extra_terms: &[TermId],
    ) -> Vec<Vec<CongruenceApp>> {
        let mut uf_apps: HashMap<(String, usize), Vec<(TermId, Vec<TermId>)>> = HashMap::default();
        let mut visited = HashSet::default();
        for &assertion in &self.ctx.assertions {
            self.collect_uf_applications(assertion, &mut uf_apps, &mut visited);
        }
        for &term in extra_terms {
            self.collect_uf_applications(term, &mut uf_apps, &mut visited);
        }
        let shift = |lit: i32| {
            if lit > 0 {
                lit + bv_offset
            } else {
                lit - bv_offset
            }
        };
        // The eager pass's `bv_lits_for`.
        let lits_for = |t: TermId| -> Option<Vec<i32>> {
            if let Some(bits) = term_bits.get(&t) {
                return Some(bits.iter().map(|&b| shift(b)).collect());
            }
            if matches!(self.ctx.terms.sort(t), Sort::Bool) {
                return bool_to_var.get(&t).map(|&lit| vec![shift(lit)]);
            }
            None
        };
        let mut keys: Vec<&(String, usize)> = uf_apps.keys().collect();
        keys.sort();
        let mut groups = Vec::new();
        for key in keys {
            let applications = &uf_apps[key];
            if applications.len() < 2 {
                continue;
            }
            let mut apps = Vec::new();
            for (term, args) in applications {
                let Some(result) = lits_for(*term).filter(|r| !r.is_empty()) else {
                    continue;
                };
                let args = args
                    .iter()
                    .map(|&arg| match lits_for(arg) {
                        Some(lits) if !lits.is_empty() => CongruenceArg::Lits {
                            bool_sorted: matches!(self.ctx.terms.sort(arg), Sort::Bool),
                            lits,
                        },
                        _ => CongruenceArg::Opaque(arg),
                    })
                    .collect();
                apps.push(CongruenceApp {
                    result_bool: matches!(self.ctx.terms.sort(*term), Sort::Bool),
                    result,
                    args,
                });
            }
            if apps.len() >= 2 {
                groups.push(apps);
            }
        }
        groups
    }

    /// Complete a capped BV congruence pass lazily (see the module docs).
    /// Returns the new result and the bail that still stands: `None` when a
    /// SAT result is congruent on every pair (or the result is not SAT),
    /// [`CongruenceBail::Count`] when the literal budget ran out or a model
    /// could not be read, the stop itself when a stop ended the loop. Also
    /// returns whether any clause was added (the caller re-audits what the
    /// added clauses can disturb).
    #[allow(clippy::too_many_arguments)]
    pub(in crate::executor) fn refine_capped_bv_congruence(
        &mut self,
        mut solve_result: SatResult,
        term_bits: &HashMap<TermId, Vec<i32>>,
        bool_to_var: &HashMap<TermId, i32>,
        bv_offset: i32,
        extra_terms: &[TermId],
        solver: &mut SatSolver,
        spent: &mut ChainSpend,
    ) -> (SatResult, Option<CongruenceBail>, bool) {
        let groups = self.lazy_congruence_groups(term_bits, bool_to_var, bv_offset, extra_terms);
        let mut next_var = u32::try_from(solver.total_num_vars()).unwrap_or(u32::MAX);
        let mut literals_added = 0usize;
        let mut rounds = 0u64;
        let mut added_any = false;
        let remaining = loop {
            let SatResult::Sat(model) = &solve_result else {
                break None;
            };
            let Some(clauses) = violated_congruence_clauses(&groups, model, &mut next_var) else {
                break Some(CongruenceBail::Count);
            };
            if clauses.is_empty() {
                break None;
            }
            literals_added = clauses
                .iter()
                .map(Vec::len)
                .fold(literals_added, usize::saturating_add);
            if literals_added > MAX_LAZY_CONGRUENCE_LITERALS {
                break Some(CongruenceBail::Count);
            }
            if let Some(origin) = self.encoding_phase_stop() {
                break Some(CongruenceBail::Stop(origin));
            }
            rounds += 1;
            added_any = true;
            solver.ensure_num_vars(next_var as usize);
            for clause in clauses {
                solver.add_clause(clause.into_iter().map(crate::cnf_lit_to_sat).collect());
            }
            solve_result = self.solve_sat_in_budget_chain(solver, spent);
            if matches!(solve_result, SatResult::Unknown) {
                self.propagate_bv_unknown_reason(true);
            }
        };
        self.last_statistics
            .set_int("smt.bv.congruence_lazy.refinement_rounds", rounds);
        (solve_result, remaining, added_any)
    }
}

#[cfg(test)]
#[path = "bv_congruence_refine_tests.rs"]
mod tests;
