// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared BV encoding helpers for literal offsetting, linking, and BV equality
//! congruence.
//!
//! Both the fresh-state and persistent-state phases of the unified BV pipeline
//! (`solve_bv_core_inner`) need to link Tseitin variables to their BV
//! bitblasted counterparts. This module extracts that shared linking logic
//! (#6691).
//!
//! The two encoding phases differ in how they consume the equivalence pairs:
//! - Fresh (non-incremental): pushes binary `CnfClause`s into `all_clauses`
//! - Persistent (incremental): adds global `SatLiteral` clauses to the SAT solver

use std::borrow::Borrow;
use std::collections::BTreeMap;

// #8529: Use deterministic hash maps in all builds.
use ay_bv::BvSolver;
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::TermData;
use ay_core::{CnfClause, Sort, TermId, TermStore};
use ay_sat::Solver as SatSolver;

use super::debug_linking_enabled;

/// Offset a DIMACS-style CNF literal by `var_offset`.
///
/// Positive literals are shifted up, negative literals are shifted down,
/// preserving sign semantics. Both BV solve paths use this to translate
/// bitblasted variables past the Tseitin range.
#[inline]
pub(in crate::executor::theories) fn offset_cnf_lit(lit: i32, var_offset: i32) -> i32 {
    if lit > 0 {
        lit + var_offset
    } else {
        lit - var_offset
    }
}

/// Offset all literals in `clauses` by `var_offset` and push into `all_clauses`.
pub(in crate::executor::theories) fn offset_and_push_clauses(
    clauses: impl IntoIterator<Item = CnfClause>,
    var_offset: i32,
    all_clauses: &mut Vec<CnfClause>,
) {
    for clause in clauses {
        let offset_lits: Vec<i32> = clause
            .literals()
            .iter()
            .map(|&lit| offset_cnf_lit(lit, var_offset))
            .collect();
        all_clauses.push(CnfClause::new(offset_lits));
    }
}

/// Add `clauses` to the persistent SAT solver without changing variable IDs.
pub(in crate::executor::theories) fn add_clauses_global<T>(
    solver: &mut SatSolver,
    clauses: impl IntoIterator<Item = T>,
) where
    T: Borrow<CnfClause>,
{
    for clause in clauses {
        let lits = clause
            .borrow()
            .literals()
            .iter()
            .map(|&lit| crate::cnf_lit_to_sat(lit))
            .collect();
        solver.add_clause_global(lits);
    }
}

/// Add `clauses` to the persistent SAT solver after offsetting each literal.
pub(in crate::executor::theories) fn add_offset_clauses_global<T>(
    solver: &mut SatSolver,
    clauses: impl IntoIterator<Item = T>,
    var_offset: i32,
) where
    T: Borrow<CnfClause>,
{
    for clause in clauses {
        let lits = clause
            .borrow()
            .literals()
            .iter()
            .map(|&lit| crate::cnf_lit_to_sat(offset_cnf_lit(lit, var_offset)))
            .collect();
        solver.add_clause_global(lits);
    }
}

/// Shared result of BV predicate/Bool linking.
pub(in crate::executor::theories) struct BvLinkingBatch {
    predicate_equivs: Vec<(i32, i32)>,
    bool_equivs: Vec<(i32, i32)>,
    newly_linked_terms: Vec<TermId>,
    extra_bv_clauses: Vec<CnfClause>,
}

impl BvLinkingBatch {
    /// Add Tseitin↔BV equivalence clauses to a CNF clause list.
    pub(in crate::executor::theories) fn push_equivalence_clauses(
        &self,
        all_clauses: &mut Vec<CnfClause>,
    ) {
        self.for_each_equiv(|tseitin_lit, bv_lit| {
            all_clauses.push(CnfClause::binary(-tseitin_lit, bv_lit));
            all_clauses.push(CnfClause::binary(tseitin_lit, -bv_lit));
        });
    }

    /// Add Tseitin↔BV equivalence clauses to the persistent SAT solver.
    pub(in crate::executor::theories) fn add_global_equivalence_clauses(
        &self,
        solver: &mut SatSolver,
    ) {
        self.for_each_equiv(|tseitin_lit, bv_lit| {
            solver.add_clause_global(vec![
                crate::cnf_lit_to_sat(-tseitin_lit),
                crate::cnf_lit_to_sat(bv_lit),
            ]);
            solver.add_clause_global(vec![
                crate::cnf_lit_to_sat(tseitin_lit),
                crate::cnf_lit_to_sat(-bv_lit),
            ]);
        });
    }

    /// Newly linked terms for incremental dedup tracking.
    pub(in crate::executor::theories) fn newly_linked_terms(&self) -> &[TermId] {
        &self.newly_linked_terms
    }

    /// Generated BV clauses from `bitblast_predicate`.
    pub(in crate::executor::theories) fn take_extra_bv_clauses(&mut self) -> Vec<CnfClause> {
        std::mem::take(&mut self.extra_bv_clauses)
    }

    fn for_each_equiv(&self, mut f: impl FnMut(i32, i32)) {
        for &(tseitin_lit, bv_lit) in &self.predicate_equivs {
            f(tseitin_lit, bv_lit);
        }
        for &(tseitin_lit, bv_lit) in &self.bool_equivs {
            f(tseitin_lit, bv_lit);
        }
    }
}

pub(in crate::executor::theories) struct BvEqCongruenceBatch {
    clauses: Vec<CnfClause>,
    newly_emitted_pairs: Vec<(TermId, TermId)>,
}

impl BvEqCongruenceBatch {
    pub(in crate::executor::theories) fn clauses(&self) -> &[CnfClause] {
        &self.clauses
    }

    pub(in crate::executor::theories) fn newly_emitted_pairs(&self) -> &[(TermId, TermId)] {
        &self.newly_emitted_pairs
    }
}

/// Collect BV predicate/Bool linking as one shared batch.
///
/// This preserves the existing linking algorithm and the `AY_DEBUG_LINKING`
/// instrumentation while moving the duplicated batch construction out of the
/// two BV solve paths.
pub(in crate::executor::theories) fn build_linking_batch(
    var_to_term: &BTreeMap<u32, TermId>,
    bv_solver: &mut BvSolver<'_>,
    var_offset: i32,
    terms: &TermStore,
    already_linked: Option<&HashSet<TermId>>,
) -> BvLinkingBatch {
    let debug_linking = debug_linking_enabled();
    let mut predicate_equivs = Vec::new();
    let mut newly_linked = Vec::new();
    for (&tseitin_var, &term) in var_to_term {
        if let Some(linked) = already_linked {
            if linked.contains(&term) {
                if debug_linking {
                    safe_eprintln!("[linking] Skip {:?}: already linked", term);
                }
                continue;
            }
        }
        if debug_linking {
            safe_eprintln!(
                "[linking] tseitin_var={} term={:?} sort={:?}",
                tseitin_var,
                term,
                terms.sort(term)
            );
        }
        if let Some(bv_lit) = bv_solver.bitblast_predicate(term) {
            let bv_lit_offset = offset_cnf_lit(bv_lit, var_offset);
            if debug_linking {
                safe_eprintln!(
                    "[linking #858] tseitin_var={} -> bv_lit={} (var_offset={}, offset_lit={})",
                    tseitin_var,
                    bv_lit,
                    var_offset,
                    bv_lit_offset
                );
            }
            predicate_equivs.push((tseitin_var as i32, bv_lit_offset));
            newly_linked.push(term);
        }
    }

    if debug_linking {
        safe_eprintln!("[linking] bool_to_var: {:?}", bv_solver.bool_to_var());
    }
    let mut bool_equivs = Vec::new();
    for (&tseitin_var, &term) in var_to_term {
        if !matches!(terms.sort(term), Sort::Bool) {
            continue;
        }
        if bv_solver.predicate_to_var().contains_key(&term) {
            if debug_linking {
                safe_eprintln!("[linking] Skip {:?}: in predicate_to_var", term);
            }
            continue;
        }
        if let Some(linked) = already_linked {
            if linked.contains(&term) {
                if debug_linking {
                    safe_eprintln!("[linking] Skip {:?}: already linked", term);
                }
                continue;
            }
        }
        let Some(&bv_lit) = bv_solver.bool_to_var().get(&term) else {
            if debug_linking {
                safe_eprintln!("[linking] Skip {:?}: not in bool_to_var", term);
            }
            continue;
        };
        if debug_linking {
            let kind = if matches!(terms.get(term), TermData::Ite(..)) {
                "ITE"
            } else if bv_solver.bv_ite_conditions().contains(&term) {
                "condition"
            } else {
                "bool_atom"
            };
            safe_eprintln!(
                "[linking] LINK {:?} ({}): tseitin_var={} <-> bv_lit={}",
                term,
                kind,
                tseitin_var,
                bv_lit
            );
        }
        let bv_lit_offset = offset_cnf_lit(bv_lit, var_offset);
        bool_equivs.push((tseitin_var as i32, bv_lit_offset));
        newly_linked.push(term);
    }
    if debug_linking {
        safe_eprintln!(
            "[linking] Total linked: {}",
            predicate_equivs.len() + bool_equivs.len()
        );
    }

    BvLinkingBatch {
        predicate_equivs,
        bool_equivs,
        newly_linked_terms: newly_linked,
        extra_bv_clauses: bv_solver.take_clauses(),
    }
}

/// Build a negation map from a var→term mapping.
///
/// For each term in `var_to_term` values, creates a `(term, ¬term)` entry.
/// Used by both BV solve paths to set up proof tracking state (#340, #4176).
pub(in crate::executor::theories) fn build_negation_map(
    terms: &mut TermStore,
    var_to_term: &BTreeMap<u32, TermId>,
) -> HashMap<TermId, TermId> {
    let mut negations = HashMap::default();
    for &term in var_to_term.values() {
        let not_term = terms.mk_not(term);
        negations.insert(term, not_term);
    }
    negations
}

/// Generate BV equality congruence axiom clauses (#1708, #5441).
///
/// When `a = b` is asserted and the formula contains BV predicates `(= a c)`
/// and `(= b c)`, these get independent SAT variables via Tseitin/bitblasting.
/// This function generates equivalence clauses `(= a c) ↔ (= b c)` at the
/// SAT level, providing a direct connection that helps the SAT solver propagate
/// conflicts without traversing the full bit-level encoding chain.
///
/// Used by both fresh-state and persistent-state phases of the unified BV
/// pipeline to maintain axiom parity (#5441, #6691 config-driven gating).
pub(in crate::executor::theories) fn generate_bv_eq_congruence_clauses(
    terms: &TermStore,
    assertions: &[TermId],
    bv_solver: &BvSolver<'_>,
    var_offset: i32,
) -> Vec<CnfClause> {
    build_bv_eq_congruence_batch(terms, assertions, bv_solver, var_offset, None).clauses
}

pub(in crate::executor::theories) fn build_bv_eq_congruence_batch(
    terms: &TermStore,
    assertions: &[TermId],
    bv_solver: &BvSolver<'_>,
    var_offset: i32,
    already_emitted: Option<&HashSet<(TermId, TermId)>>,
) -> BvEqCongruenceBatch {
    let mut bv_eq_terms: Vec<(TermId, i32)> = Vec::new();
    let mut seen_terms: HashSet<TermId> = HashSet::default();

    for (&term, &bv_lit) in bv_solver.predicate_to_var() {
        if let TermData::App(ref sym, ref args) = terms.get(term) {
            if sym.name() == "=" && args.len() == 2 {
                let sort = terms.sort(args[0]);
                if matches!(sort, Sort::BitVec(_)) && seen_terms.insert(term) {
                    bv_eq_terms.push((term, offset_cnf_lit(bv_lit, var_offset)));
                }
            }
        }
    }
    for (&term, &bv_lit) in bv_solver.bool_to_var() {
        if let TermData::App(ref sym, ref args) = terms.get(term) {
            if sym.name() == "=" && args.len() == 2 {
                let sort = terms.sort(args[0]);
                if matches!(sort, Sort::BitVec(_)) && seen_terms.insert(term) {
                    bv_eq_terms.push((term, offset_cnf_lit(bv_lit, var_offset)));
                }
            }
        }
    }

    let mut var_eq_index: HashMap<(TermId, TermId), (TermId, i32)> = HashMap::default();
    for (eq_term, eq_lit) in &bv_eq_terms {
        if let TermData::App(_, ref args) = terms.get(*eq_term) {
            var_eq_index.insert((args[0], args[1]), (*eq_term, *eq_lit));
            var_eq_index.insert((args[1], args[0]), (*eq_term, *eq_lit));
        }
    }

    let mut asserted_bv_eqs: Vec<(TermId, TermId)> = Vec::new();
    fn collect_bv_eqs(terms: &TermStore, term: TermId, eqs: &mut Vec<(TermId, TermId)>) {
        match terms.get(term) {
            TermData::App(ref sym, ref args) if sym.name() == "and" => {
                for &arg in args {
                    collect_bv_eqs(terms, arg, eqs);
                }
            }
            TermData::App(ref sym, ref args) if sym.name() == "=" && args.len() == 2 => {
                if matches!(terms.sort(args[0]), Sort::BitVec(_)) {
                    eqs.push((args[0], args[1]));
                }
            }
            _ => {}
        }
    }
    for &assertion in assertions {
        collect_bv_eqs(terms, assertion, &mut asserted_bv_eqs);
    }

    let mut clauses = Vec::new();
    let mut newly_emitted_pairs = Vec::new();
    let mut seen_pairs: HashSet<(TermId, TermId)> = HashSet::default();
    for &(var_a, var_b) in &asserted_bv_eqs {
        for (eq_term, eq_lit) in &bv_eq_terms {
            if let TermData::App(_, ref eq_args) = terms.get(*eq_term) {
                let other_c = if eq_args[0] == var_a {
                    Some(eq_args[1])
                } else if eq_args[1] == var_a {
                    Some(eq_args[0])
                } else if eq_args[0] == var_b {
                    Some(eq_args[1])
                } else if eq_args[1] == var_b {
                    Some(eq_args[0])
                } else {
                    None
                };

                if let Some(c) = other_c {
                    if c == var_a || c == var_b {
                        continue;
                    }
                    let other_var = if eq_args[0] == var_a || eq_args[1] == var_a {
                        var_b
                    } else {
                        var_a
                    };
                    if let Some(&(other_eq_term, other_eq_lit)) = var_eq_index.get(&(other_var, c))
                    {
                        let pair = if *eq_term < other_eq_term {
                            (*eq_term, other_eq_term)
                        } else {
                            (other_eq_term, *eq_term)
                        };
                        if !seen_pairs.insert(pair) {
                            continue;
                        }
                        if let Some(emitted) = already_emitted {
                            if emitted.contains(&pair) {
                                continue;
                            }
                        }
                        clauses.push(CnfClause::binary(-*eq_lit, other_eq_lit));
                        clauses.push(CnfClause::binary(*eq_lit, -other_eq_lit));
                        newly_emitted_pairs.push(pair);
                    }
                }
            }
        }
    }

    BvEqCongruenceBatch {
        clauses,
        newly_emitted_pairs,
    }
}

// --- JIT batch compilation helpers (#8275) ---

/// Convert a DIMACS-style signed literal to JIT-encoded literal.
///
/// DIMACS: positive `v` (1-indexed), negative `-v`.
/// JIT: `(var_index) * 2 + polarity` where polarity 0 = positive, 1 = negative.
///
/// Example: DIMACS `3` -> JIT `(3-1)*2 = 4`, DIMACS `-3` -> JIT `(3-1)*2+1 = 5`.
#[cfg(feature = "jit")]
#[allow(dead_code)] // cfg-gated: used when BV JIT compilation path is enabled
#[inline]
pub(in crate::executor::theories) fn cnf_lit_to_jit(lit: i32) -> u32 {
    debug_assert_ne!(lit, 0, "literal 0 is invalid in DIMACS encoding");
    if lit > 0 {
        ((lit - 1) as u32) * 2
    } else {
        ((-lit - 1) as u32) * 2 + 1
    }
}

/// Classify a CnfClause as a BV gate type based on its length.
///
/// BV bit-blasting produces characteristic clause patterns:
/// - Unit (1 literal): constant propagation
/// - Binary (2 literals): forward implications from AND/OR gates
/// - Ternary (3 literals): backward implications or XOR/MUX clauses
/// - Longer (4+ literals): rare in standard BV encoding
#[cfg(feature = "jit")]
#[allow(dead_code)] // cfg-gated: used when BV JIT compilation path is enabled
fn classify_bv_gate(clause: &CnfClause) -> ay_jit::BvGateType {
    match clause.literals().len() {
        0 => ay_jit::BvGateType::Other,
        1 => ay_jit::BvGateType::Unit,
        2 => ay_jit::BvGateType::And, // Binary clauses from AND/OR forward implications
        3 => ay_jit::BvGateType::Xor, // Most ternary clauses are XOR/MUX gate encoding
        _ => ay_jit::BvGateType::Other,
    }
}

/// Build a JIT clause batch from BV-generated CNF clauses.
///
/// Converts DIMACS-style literals to JIT encoding and classifies each clause
/// by gate type. The returned batch can be passed to `ay_jit::compile_bv_batch()`
/// for compilation into native propagation functions.
///
/// Unit and binary clauses are included in the batch for statistics but will be
/// filtered out by `BvClauseBatch::into_jit_clauses()` before compilation,
/// since they are more efficient in the 2-watched-literal scheme (#8261).
#[cfg(feature = "jit")]
#[allow(dead_code)] // cfg-gated: used when BV JIT compilation path is enabled
pub(in crate::executor::theories) fn build_bv_jit_batch(
    clauses: &[CnfClause],
    _num_total_vars: u32,
) -> ay_jit::BvClauseBatch {
    let mut batch = ay_jit::BvClauseBatch::with_capacity(clauses.len());
    for (i, clause) in clauses.iter().enumerate() {
        let gate_type = classify_bv_gate(clause);
        let jit_lits: Vec<u32> = clause
            .literals()
            .iter()
            .map(|&lit| cnf_lit_to_jit(lit))
            .collect();
        batch.add_clause(i as u32, &jit_lits, gate_type);
    }
    batch
}
