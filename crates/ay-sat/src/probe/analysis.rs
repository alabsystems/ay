// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Failed literal analysis: UIP extraction, dominator finding, and hyper-binary resolution.
//!
//! These are standalone functions used during failed literal probing to:
//! - Find the 1UIP via trail-based resolution (`find_failed_literal_uip`)
//! - Find dominators in the binary implication tree (`probe_dominator`)
//! - Compute failed-literal UIP via dominator walk (`failed_literal_dominator`)
//! - Derive binary clauses via hyper-binary resolution (`hyper_binary_resolve`)
//!
//! References:
//! - CaDiCaL probe.cpp
//! - Heule & van Maaren, "Look-Ahead Based SAT Solvers" (2009)

use crate::clause_arena::ClauseArena;
use crate::literal::Literal;
use crate::solver::{is_clause_reason, VarData};

/// Result of the 1UIP computation in failed literal probing.
#[derive(Debug)]
pub(crate) struct UipResult {
    /// The negation of the 1UIP literal (the forced unit), or None if no UIP found.
    pub(crate) forced: Option<Literal>,
}

/// Why dominator-based UIP extraction failed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum DominatorFailure {
    /// No dominator found (empty conflict, no level-1 literals, etc.).
    NoDominator,
    /// Parent metadata was missing for a level-1 literal with a reason.
    /// This indicates a contract violation in `probe_parent` population.
    MissingMetadata,
    /// Parent-chain walk exceeded trail length (cycle or corruption).
    ParentChainCycle,
}

/// Result of dominator-based failed-literal analysis.
#[derive(Debug)]
pub(crate) struct FailedLiteralDominatorResult {
    /// The negation of the probing UIP literal (forced unit), if found.
    pub(crate) forced: Option<Literal>,
    /// Ordered parent chain from UIP parent up to and including the failed decision.
    /// Reference: CaDiCaL probe.cpp:547-553.
    pub(crate) parent_chain: Vec<Literal>,
    /// If `forced` is `None`, why the dominator extraction failed.
    pub(crate) failure: Option<DominatorFailure>,
}

/// Result of a hyper-binary resolution attempt.
#[derive(Debug, Clone)]
pub(crate) struct HyperBinaryResult {
    /// The binary clause to add: (-dominator, unit_lit)
    /// None if HBR didn't produce a useful clause.
    pub(crate) binary_clause: Option<(Literal, Literal)>,
    /// The dominator literal found during HBR computation.
    /// Always populated when a dominator was found, even if no binary clause
    /// was created. Used to set probe_parent for the propagated literal.
    /// CaDiCaL always sets parent = dominator (probe.cpp:485).
    pub(crate) dominator: Option<Literal>,
    /// Whether the new clause is redundant (learned/derived)
    pub(crate) is_redundant: bool,
    /// Whether the HBR clause subsumes the original (dominator contained in original)
    pub(crate) subsumes_original: bool,
}

impl HyperBinaryResult {
    /// Returns a "no result" value indicating HBR didn't produce a useful clause.
    fn no_result() -> Self {
        Self {
            binary_clause: None,
            dominator: None,
            is_redundant: true,
            subsumes_original: false,
        }
    }
}

/// Find the 1UIP dominator in a failed literal conflict at level 1.
/// Returns the negation of the UIP (the forced literal) along with the
/// clause indices in the resolution chain for LRAT hint generation.
pub(crate) fn find_failed_literal_uip(
    conflict_clause: &[Literal],
    trail: &[Literal],
    var_data: &[VarData],
    clauses: &ClauseArena,
    uip_seen: &mut Vec<bool>,
) -> UipResult {
    // CaDiCaL probe.cpp:334: conflict clause must be non-empty
    debug_assert!(
        !conflict_clause.is_empty(),
        "BUG: find_failed_literal_uip called with empty conflict clause",
    );
    // CaDiCaL probe.cpp:335: trail must be non-empty during probing
    debug_assert!(
        !trail.is_empty(),
        "BUG: find_failed_literal_uip with empty trail"
    );

    if uip_seen.len() < var_data.len() {
        uip_seen.resize(var_data.len(), false);
    }
    let seen = &mut uip_seen[..var_data.len()];
    seen.fill(false);
    let mut count_at_level_1 = 0;

    // Mark literals from conflict clause
    for &lit in conflict_clause {
        let var_idx = lit.variable().index();
        // (#8478) Skip OOB literals from clauses with stale/eliminated variables.
        if var_idx >= var_data.len() {
            continue;
        }
        let var_level = var_data[var_idx].level;

        if var_level == 1 {
            seen[var_idx] = true;
            count_at_level_1 += 1;
        }
    }

    if count_at_level_1 == 0 {
        return UipResult { forced: None };
    }

    // Walk backward through trail to find 1UIP
    let mut uip: Option<Literal> = None;

    for &lit in trail.iter().rev() {
        let var_idx = lit.variable().index();

        if !seen[var_idx] {
            continue;
        }

        seen[var_idx] = false;
        count_at_level_1 -= 1;

        if count_at_level_1 == 0 {
            // This is the 1UIP
            uip = Some(lit);
            break;
        }

        // Expand the reason clause
        let reason_raw = var_data[var_idx].reason;
        if is_clause_reason(reason_raw) {
            let clause_idx = reason_raw as usize;
            if clause_idx < clauses.len() && !clauses.is_empty_clause(clause_idx) {
                let reason_lits = clauses.literals(clause_idx);
                for &reason_lit in reason_lits {
                    let reason_var_idx = reason_lit.variable().index();
                    if reason_var_idx == var_idx {
                        continue;
                    }
                    // (#8478) Skip OOB literals from reason clauses.
                    if reason_var_idx >= var_data.len() || reason_var_idx >= seen.len() {
                        continue;
                    }
                    let reason_level = var_data[reason_var_idx].level;
                    if reason_level == 1 && !seen[reason_var_idx] {
                        seen[reason_var_idx] = true;
                        count_at_level_1 += 1;
                    }
                }
            }
        }
    }

    // Return the negation of the UIP (the forced literal)
    UipResult {
        forced: uip.map(Literal::negated),
    }
}

/// Get the parent literal in the binary implication tree at level 1.
///
/// Uses the exact `probe_parent` array (populated during probe propagation)
/// when available. Falls back to reason-clause parsing for callers without
/// probe_parent data. Reference: CaDiCaL probe.cpp:30-43.
///
/// Returns the parent literal (the literal that implied this one),
/// or None if this is the decision literal (no parent).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ParentReasonLookup {
    Parent(Literal),
    Root,
    MissingMetadata,
}

fn lookup_parent_reason_literal(
    lit: Literal,
    probe_parent: &[Option<Literal>],
    var_data: &[VarData],
    clauses: &ClauseArena,
) -> ParentReasonLookup {
    let var_idx = lit.variable().index();

    // Probing callers must use exact `probe_parent` metadata.
    // Missing parent at level 1 with a reason is a contract violation.
    if var_idx < probe_parent.len() {
        if let Some(parent) = probe_parent[var_idx] {
            return ParentReasonLookup::Parent(parent);
        }
        let has_reason = var_data
            .get(var_idx)
            .is_some_and(|vd| is_clause_reason(vd.reason));
        if var_data.get(var_idx).is_some_and(|vd| vd.level == 1) && has_reason {
            return ParentReasonLookup::MissingMetadata;
        }
        return ParentReasonLookup::Root;
    }

    // Fallback: parse reason clause (only used when probe_parent is empty/undersized)
    let Some(vd) = var_data.get(var_idx) else {
        return ParentReasonLookup::Root;
    };
    if !is_clause_reason(vd.reason) {
        return ParentReasonLookup::Root;
    }
    let clause_idx = vd.reason as usize;

    if clause_idx >= clauses.len() {
        return ParentReasonLookup::Root;
    }
    if clauses.is_empty_clause(clause_idx) {
        return ParentReasonLookup::Root;
    }

    let lits = clauses.literals(clause_idx);
    if lits.len() == 2 {
        let other = if lits[0].variable() == lit.variable() {
            lits[1]
        } else {
            lits[0]
        };
        return ParentReasonLookup::Parent(other.negated());
    }

    for &reason_lit in lits {
        if reason_lit.variable() == lit.variable() {
            continue;
        }
        let reason_var_idx = reason_lit.variable().index();
        if reason_var_idx < var_data.len() && var_data[reason_var_idx].level == 1 {
            return ParentReasonLookup::Parent(reason_lit.negated());
        }
    }

    ParentReasonLookup::Root
}

/// Find the dominator (lowest common ancestor) of two literals in the
/// binary implication tree at decision level 1.
///
/// This is used during hyper-binary resolution to find the single literal
/// that dominates all false literals in a long clause.
///
/// Reference: CaDiCaL `probe_dominator` in `probe.cpp:150-169`
pub(crate) fn probe_dominator(
    a: Literal,
    b: Literal,
    trail: &[Literal],
    var_data: &[VarData],
    probe_parent: &[Option<Literal>],
    clauses: &ClauseArena,
) -> Option<Literal> {
    // Quick path: same literal
    if a == b {
        return Some(a);
    }

    // Both must be at level 1
    let a_var = a.variable().index();
    let b_var = b.variable().index();

    if a_var >= var_data.len() || b_var >= var_data.len() {
        return None;
    }
    if var_data[a_var].level != 1 || var_data[b_var].level != 1 {
        return None;
    }

    // Walk up the implication tree from both literals until they meet
    let mut l = a;
    let mut k = b;

    // Safety: prevent infinite loops with iteration limit
    let max_iters = trail.len() + 1;
    let mut iters = 0;

    while l != k && iters < max_iters {
        iters += 1;

        // Get trail positions (earlier = smaller position)
        let l_var = l.variable().index();
        let k_var = k.variable().index();

        let l_pos = var_data.get(l_var).map_or(u32::MAX, |vd| vd.trail_pos);
        let k_pos = var_data.get(k_var).map_or(u32::MAX, |vd| vd.trail_pos);

        // Move the later one up to its parent
        if l_pos > k_pos {
            // l is later, move it to its parent
            match lookup_parent_reason_literal(l, probe_parent, var_data, clauses) {
                ParentReasonLookup::Parent(parent) => l = parent,
                // l has no parent (decision literal): it is the dominator.
                ParentReasonLookup::Root => return Some(l),
                // Missing probing metadata must not be reinterpreted as root.
                ParentReasonLookup::MissingMetadata => return None,
            }
        } else {
            // k is later (or equal), move it to its parent
            match lookup_parent_reason_literal(k, probe_parent, var_data, clauses) {
                ParentReasonLookup::Parent(parent) => k = parent,
                // k has no parent (decision literal): it is the dominator.
                ParentReasonLookup::Root => return Some(k),
                // Missing probing metadata must not be reinterpreted as root.
                ParentReasonLookup::MissingMetadata => return None,
            }
        }
    }

    if l == k {
        Some(l)
    } else {
        None // Failed to find dominator (shouldn't happen in valid implication tree)
    }
}

/// Compute failed-literal UIP via parent dominator and extract parent chain.
///
/// Mirrors CaDiCaL `failed_literal` (probe.cpp:529-553):
/// 1. Fold `probe_dominator` across conflict literals at level 1.
/// 2. Walk parents from UIP to failed decision.
fn failed_literal_uip_from_dominator(
    conflict_clause: &[Literal],
    trail: &[Literal],
    var_data: &[VarData],
    probe_parent: &[Option<Literal>],
    clauses: &ClauseArena,
) -> Result<Literal, DominatorFailure> {
    let mut uip: Option<Literal> = None;
    for &lit in conflict_clause {
        let var_idx = lit.variable().index();
        if var_idx >= var_data.len() || var_data[var_idx].level == 0 {
            continue;
        }
        let other = lit.negated();
        uip = match uip {
            None => Some(other),
            Some(current) => {
                probe_dominator(current, other, trail, var_data, probe_parent, clauses)
            }
        };
        if uip.is_none() {
            return Err(DominatorFailure::NoDominator);
        }
    }

    uip.ok_or(DominatorFailure::NoDominator)
}

fn validate_failed_literal_parent_chain(
    uip_lit: Literal,
    failed_decision: Literal,
    trail: &[Literal],
    var_data: &[VarData],
    probe_parent: &[Option<Literal>],
    clauses: &ClauseArena,
) -> Result<(), DominatorFailure> {
    let mut parent = uip_lit;
    let mut steps = 0usize;
    while parent != failed_decision {
        if steps > trail.len() {
            // Production soundness gate: parent chain walk is cycling.
            // Return a typed error so the caller can skip this probe
            // without corrupting solver state.
            safe_eprintln!(
                "BUG: probing parent chain walk exceeded trail length ({uip_lit:?} -> {failed_decision:?})",
            );
            return Err(DominatorFailure::ParentChainCycle);
        }
        steps += 1;

        parent = match lookup_parent_reason_literal(parent, probe_parent, var_data, clauses) {
            ParentReasonLookup::Parent(next) => next,
            ParentReasonLookup::MissingMetadata => return Err(DominatorFailure::MissingMetadata),
            ParentReasonLookup::Root => return Err(DominatorFailure::NoDominator),
        };
    }

    Ok(())
}

/// Compute only the forced UIP literal for failed-literal probing.
///
/// This mirrors the dominator fold used by `failed_literal_dominator` but skips
/// parent-chain extraction allocation. Callers that only need the forced unit
/// still run parent-walk validation to preserve metadata/cycle failure behavior.
pub(crate) fn failed_literal_dominator_forced_only(
    conflict_clause: &[Literal],
    failed_decision: Literal,
    trail: &[Literal],
    var_data: &[VarData],
    probe_parent: &[Option<Literal>],
    clauses: &ClauseArena,
) -> FailedLiteralDominatorResult {
    debug_assert!(
        !conflict_clause.is_empty(),
        "BUG: failed_literal_dominator_forced_only called with empty conflict clause",
    );

    match failed_literal_uip_from_dominator(conflict_clause, trail, var_data, probe_parent, clauses)
    {
        Ok(uip_lit) => match validate_failed_literal_parent_chain(
            uip_lit,
            failed_decision,
            trail,
            var_data,
            probe_parent,
            clauses,
        ) {
            Ok(()) => FailedLiteralDominatorResult {
                forced: Some(uip_lit.negated()),
                parent_chain: Vec::new(),
                failure: None,
            },
            Err(failure) => FailedLiteralDominatorResult {
                forced: None,
                parent_chain: Vec::new(),
                failure: Some(failure),
            },
        },
        Err(failure) => FailedLiteralDominatorResult {
            forced: None,
            parent_chain: Vec::new(),
            failure: Some(failure),
        },
    }
}

pub(crate) fn failed_literal_dominator(
    conflict_clause: &[Literal],
    failed_decision: Literal,
    trail: &[Literal],
    var_data: &[VarData],
    probe_parent: &[Option<Literal>],
    clauses: &ClauseArena,
) -> FailedLiteralDominatorResult {
    debug_assert!(
        !conflict_clause.is_empty(),
        "BUG: failed_literal_dominator called with empty conflict clause",
    );

    let uip_lit = match failed_literal_uip_from_dominator(
        conflict_clause,
        trail,
        var_data,
        probe_parent,
        clauses,
    ) {
        Ok(uip_lit) => uip_lit,
        Err(failure) => {
            return FailedLiteralDominatorResult {
                forced: None,
                parent_chain: Vec::new(),
                failure: Some(failure),
            };
        }
    };

    let mut parent_chain = Vec::new();
    let mut parent = uip_lit;
    let mut steps = 0usize;
    while parent != failed_decision {
        if steps > trail.len() {
            // Production soundness gate: parent chain walk is cycling.
            // Return a typed failure so the caller can skip this probe.
            safe_eprintln!(
                "BUG: probing parent chain walk exceeded trail length ({uip_lit:?} -> {failed_decision:?})",
            );
            return FailedLiteralDominatorResult {
                forced: None,
                parent_chain: Vec::new(),
                failure: Some(DominatorFailure::ParentChainCycle),
            };
        }
        steps += 1;

        match lookup_parent_reason_literal(parent, probe_parent, var_data, clauses) {
            ParentReasonLookup::Parent(next) => {
                parent = next;
                parent_chain.push(parent);
            }
            ParentReasonLookup::MissingMetadata => {
                // Contract violation: level-1 literal with reason but no
                // probe_parent entry. Report typed failure; caller asserts.
                return FailedLiteralDominatorResult {
                    forced: None,
                    parent_chain: Vec::new(),
                    failure: Some(DominatorFailure::MissingMetadata),
                };
            }
            ParentReasonLookup::Root => {
                // Unexpected root in middle of parent chain walk.
                return FailedLiteralDominatorResult {
                    forced: None,
                    parent_chain: Vec::new(),
                    failure: Some(DominatorFailure::NoDominator),
                };
            }
        }
    }

    FailedLiteralDominatorResult {
        forced: Some(uip_lit.negated()),
        parent_chain,
        failure: None,
    }
}

/// Hyper-binary resolution: derive `(-dominator, unit)` from a long clause
/// forced at level 1. Reference: CaDiCaL probe.cpp:218-280.
pub(crate) fn hyper_binary_resolve(
    clause_lits: &[Literal],
    trail: &[Literal],
    var_data: &[VarData],
    probe_parent: &[Option<Literal>],
    clauses: &ClauseArena,
    is_redundant_clause: bool,
) -> HyperBinaryResult {
    // CaDiCaL probe.cpp:221: clause must be non-empty
    debug_assert!(!clause_lits.is_empty(), "BUG: HBR called with empty clause");
    // Clause must have >2 literals for HBR to be meaningful
    if clause_lits.len() <= 2 {
        return HyperBinaryResult::no_result();
    }

    // First literal (lits[0]) is the unit being propagated (unassigned)
    let unit_lit = clause_lits[0];

    // Start with the second literal as initial dominator
    let lit1 = clause_lits[1];
    let lit1_var = lit1.variable().index();

    // The second literal must be at level 1
    if lit1_var >= var_data.len() || var_data[lit1_var].level != 1 {
        return HyperBinaryResult::no_result();
    }

    // Initial dominator is the negation of the second literal
    // (the literal that implied the second one to be false)
    let mut dom = lit1.negated();
    let mut non_root_level_literals = 0;

    // Find the dominator of all false literals at level 1
    for &lit in &clause_lits[2..] {
        let var_idx = lit.variable().index();
        if var_idx >= var_data.len() {
            continue;
        }

        // Skip level-0 literals (they're always false)
        if var_data[var_idx].level == 0 {
            continue;
        }

        // This literal is at level 1, find dominator with it
        let other = lit.negated(); // The literal that's true
        dom = match probe_dominator(dom, other, trail, var_data, probe_parent, clauses) {
            Some(d) => d,
            None => return HyperBinaryResult::no_result(),
        };
        non_root_level_literals += 1;
    }

    // Always return the dominator for probe_parent tracking (#4719).
    // Only create the binary clause when there are non-root-level literals
    // beyond lits[1] (matching original AY guard).
    if non_root_level_literals == 0 {
        return HyperBinaryResult {
            binary_clause: None,
            dominator: Some(dom),
            is_redundant: true,
            subsumes_original: false,
        };
    }

    // Check if dominator is already in the original clause (subsumption check)
    let dom_negated = dom.negated();
    let contained = clause_lits[1..].contains(&dom_negated);

    // New clause is redundant if dominator not contained OR original was redundant
    let is_redundant = !contained || is_redundant_clause;

    // Return the binary clause: (-dominator, unit)
    // Subsumes original if the negated dominator is contained in original clause
    HyperBinaryResult {
        binary_clause: Some((dom.negated(), unit_lit)),
        dominator: Some(dom),
        is_redundant,
        subsumes_original: contained,
    }
}
