// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Pattern matching engine for E-matching.
//!
//! Standalone matching functions extracted from `mod.rs` for code health (#5970).

use ay_core::term::TermData;
use ay_core::{Sort, TermId, TermStore};

use super::pattern::{EMatchArg, EMatchPattern, EqualityClasses, TermIndex};
use super::{EMATCH_STACK_RED_ZONE, EMATCH_STACK_SIZE, MAX_MULTI_TRIGGER_BINDINGS};

/// Trail-based binding save/restore to avoid per-call `binding.to_vec()` (#8602).
///
/// Each entry records `(slot_index, old_value)` before a slot is modified.
/// On failure, entries are popped back to a saved mark to undo modifications.
/// This replaces O(num_vars) clone per recursive call with O(modified_slots) undo.
struct BindingTrail {
    entries: Vec<(usize, Option<TermId>)>,
}

impl BindingTrail {
    fn new() -> Self {
        Self {
            entries: Vec::new(),
        }
    }

    /// Returns the current trail position (mark) for later restore.
    #[inline]
    fn mark(&self) -> usize {
        self.entries.len()
    }

    /// Record that `binding[slot]` is about to be modified. Saves old value.
    #[inline]
    fn save(&mut self, slot: usize, old_value: Option<TermId>) {
        self.entries.push((slot, old_value));
    }

    /// Restore binding to the state at `mark` by undoing all trail entries after it.
    #[inline]
    fn restore(&mut self, mark: usize, binding: &mut [Option<TermId>]) {
        while self.entries.len() > mark {
            let (slot, old_value) = self.entries.pop().expect("trail not empty");
            binding[slot] = old_value;
        }
    }
}

/// Try to match a pattern against a ground term.
/// If `eqclasses` is provided, ground term comparisons use equivalence classes
/// instead of syntactic equality (#3325 Gap 1).
pub(super) fn match_pattern(
    terms: &TermStore,
    pattern: &EMatchPattern,
    ground_term: TermId,
    var_sorts: &[Sort],
    eqclasses: Option<&EqualityClasses>,
) -> Option<Vec<TermId>> {
    let num_vars = var_sorts.len();
    let mut binding: Vec<Option<TermId>> = vec![None; num_vars];
    let mut trail = BindingTrail::new();

    if !match_pattern_recursive(
        terms,
        pattern,
        ground_term,
        &mut binding,
        &mut trail,
        var_sorts,
        eqclasses,
    ) {
        return None;
    }

    // All variables must be bound
    let full: Vec<TermId> = binding.iter().filter_map(|&b| b).collect();
    if full.len() == num_vars {
        Some(full)
    } else {
        None
    }
}

/// Match a multi-trigger group: ALL patterns must match with consistent bindings.
///
/// For each pattern in the group, collects all candidate matches from the term index.
/// Joins bindings across patterns: a variable bound by pattern 1 must have the same
/// value when checked by pattern 2. Returns all complete, consistent bindings.
///
/// This is the fix for #3325 Gap 2: multi-trigger support.
pub(super) fn match_multi_trigger(
    terms: &TermStore,
    patterns: &[EMatchPattern],
    index: &TermIndex,
    var_sorts: &[Sort],
    eqclasses: Option<&EqualityClasses>,
) -> Vec<Vec<TermId>> {
    let num_vars = var_sorts.len();
    if patterns.is_empty() {
        return vec![];
    }

    // Start with a single empty binding
    let mut all_bindings: Vec<Vec<Option<TermId>>> = vec![vec![None; num_vars]];

    // For each pattern, extend all existing bindings with matches from the index
    for pattern in patterns {
        let candidates = index.get_by_symbol(pattern.symbol.name());
        let mut next_bindings = Vec::new();

        'join: for existing_binding in &all_bindings {
            for &ground_term in candidates {
                let mut binding = existing_binding.clone();
                let mut trail = BindingTrail::new();
                if match_pattern_recursive(
                    terms,
                    pattern,
                    ground_term,
                    &mut binding,
                    &mut trail,
                    var_sorts,
                    eqclasses,
                ) {
                    next_bindings.push(binding);
                    if next_bindings.len() >= MAX_MULTI_TRIGGER_BINDINGS {
                        break 'join;
                    }
                }
            }
        }

        all_bindings = next_bindings;
        if all_bindings.is_empty() {
            return vec![]; // No way to satisfy this trigger group
        }
    }

    // Filter: all variables must be bound
    all_bindings
        .into_iter()
        .filter_map(|binding| {
            let full: Vec<TermId> = binding.iter().filter_map(|&b| b).collect();
            if full.len() == num_vars {
                Some(full)
            } else {
                None
            }
        })
        .collect()
}

/// Recursively match a pattern against a ground term, accumulating bindings.
/// Returns true if the match succeeds, false otherwise.
///
/// When equality classes are provided and the direct structural match fails,
/// tries all equivalent terms in the same class (#3325 Gap 1).
///
/// Uses a trail-based save/restore instead of cloning the entire binding
/// vector on every recursive call (#8602). The trail records only the slots
/// that are actually modified, making undo O(modified) instead of O(num_vars).
fn match_pattern_recursive(
    terms: &TermStore,
    pattern: &EMatchPattern,
    ground_term: TermId,
    binding: &mut [Option<TermId>],
    trail: &mut BindingTrail,
    var_sorts: &[Sort],
    eqclasses: Option<&EqualityClasses>,
) -> bool {
    stacker::maybe_grow(EMATCH_STACK_RED_ZONE, EMATCH_STACK_SIZE, || {
        // Save trail mark before the direct match attempt. The direct match
        // can partially fill binding slots before failing (e.g., pattern f(x,x)
        // against f(a,b) sets binding[0]=a then fails on the second x). Without
        // this save/restore, the equivalence class fallback loop would start from
        // dirty binding state and potentially miss valid alternative matches.
        let mark = trail.mark();

        // Try direct structural match first
        if match_pattern_recursive_direct(
            terms,
            pattern,
            ground_term,
            binding,
            trail,
            var_sorts,
            eqclasses,
        ) {
            return true;
        }

        // Restore binding after failed direct match before trying equivalences
        trail.restore(mark, binding);

        // Direct match failed. Try equivalent terms if equality classes available.
        if let Some(eq) = eqclasses {
            let members = eq.class_members(ground_term);
            for &member_id in members {
                let member = TermId(member_id);
                if member != ground_term {
                    // Save trail mark to restore on failure
                    let mark = trail.mark();
                    if match_pattern_recursive_direct(
                        terms,
                        pattern,
                        member,
                        binding,
                        trail,
                        var_sorts,
                        Some(eq),
                    ) {
                        return true;
                    }
                    // Restore binding on failure
                    trail.restore(mark, binding);
                }
            }
        }

        false
    }) // stacker::maybe_grow
}

/// Direct structural match without equivalence class expansion.
fn match_pattern_recursive_direct(
    terms: &TermStore,
    pattern: &EMatchPattern,
    ground_term: TermId,
    binding: &mut [Option<TermId>],
    trail: &mut BindingTrail,
    var_sorts: &[Sort],
    eqclasses: Option<&EqualityClasses>,
) -> bool {
    let (sym, args) = match terms.get(ground_term) {
        TermData::App(s, a) => (s, a),
        _ => return false,
    };

    if sym.name() != pattern.symbol.name() || args.len() != pattern.args.len() {
        return false;
    }

    for (pat_arg, &ground_arg) in pattern.args.iter().zip(args.iter()) {
        if !match_arg(
            terms, pat_arg, ground_arg, binding, trail, var_sorts, eqclasses,
        ) {
            return false;
        }
    }

    true
}

/// Match a single pattern argument against a ground term argument.
/// When `eqclasses` is provided, ground term comparisons use equivalence
/// classes instead of syntactic equality (#3325 Gap 1).
fn match_arg(
    terms: &TermStore,
    pat_arg: &EMatchArg,
    ground_arg: TermId,
    binding: &mut [Option<TermId>],
    trail: &mut BindingTrail,
    var_sorts: &[Sort],
    eqclasses: Option<&EqualityClasses>,
) -> bool {
    match pat_arg {
        EMatchArg::Var(var_idx) => {
            // SORT COHERENCE: only bind a pattern variable to a ground term of
            // the variable's declared sort. The pattern extractor keys ground
            // candidates by symbol NAME only, so a width-polymorphic symbol
            // (e.g. `bvmul` at 32 vs 64 bits — the 64-bit one is minted
            // internally by bvumul_noovfl's widening) can offer a ground arg
            // whose sort differs from the bound variable's. Substituting such
            // a binding into the quantifier body builds ill-sorted terms:
            // debug builds panic in `mk_eq_coerce` ("cannot coerce
            // BitVec(32) = BitVec(64)") and release builds intern a malformed
            // equality — a soundness hazard. Rejecting the match here is
            // fail-closed: it only prunes instantiations that were never
            // well-sorted to begin with.
            if var_sorts
                .get(*var_idx)
                .is_some_and(|expected| terms.sort(ground_arg) != expected)
            {
                return false;
            }
            if let Some(existing) = binding[*var_idx] {
                // Variable already bound - must match (or be equivalent)
                if existing == ground_arg {
                    true
                } else if let Some(eq) = eqclasses {
                    eq.in_same_class(existing, ground_arg)
                } else {
                    false
                }
            } else {
                // Record old value (None) in trail before binding (#8602)
                trail.save(*var_idx, None);
                // Bind variable to this ground term
                binding[*var_idx] = Some(ground_arg);
                true
            }
        }
        EMatchArg::Ground(pat_subterm) => {
            // Ground pattern must match exactly (or be equivalent)
            if *pat_subterm == ground_arg {
                true
            } else if let Some(eq) = eqclasses {
                eq.in_same_class(*pat_subterm, ground_arg)
            } else {
                false
            }
        }
        EMatchArg::Nested(nested_pattern) => {
            // Recursively match nested pattern
            match_pattern_recursive(
                terms,
                nested_pattern,
                ground_arg,
                binding,
                trail,
                var_sorts,
                eqclasses,
            )
        }
    }
}
