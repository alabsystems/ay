// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Incremental split-loop helpers for DPLL(T) theory solving.
//!
//! Extracted from `solve_harness.rs` to keep that file under 500 lines.
//! These functions are used by `solve_incremental_split_loop_pipeline!` to:
//! - Encode split atom pairs via Tseitin into a persistent SAT solver
//! - Map theory conflicts to SAT blocking clauses
//!
//! Part of #3536 (solve-harness-refactor).

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{
    term::TermData, BoundRefinementRequest, CnfClause, CnfLit, TermId, TermStore, TheoryConflict,
    TheoryLit, Tseitin,
};
use ay_sat::{Literal as SatLiteral, Solver as SatSolver, Variable as SatVariable};
use num_rational::BigRational;

use crate::incremental_proof_cache::IncrementalNegationCache;

use super::freeze_var_if_needed;

/// Stable key for deduplicating incremental split clauses.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(in crate::executor) struct SplitClauseKey {
    left_atom: TermId,
    right_atom: TermId,
    pub(crate) disequality_guard: Option<(TermId, bool)>,
}

/// Stable key for deduplicating replayed bound-refinement implication clauses.
///
/// This key is computed from the request itself so duplicate replays can be
/// detected before materializing a fresh bound atom into the term store.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct BoundRefinementReplayKey {
    variable: TermId,
    rhs_term: Option<TermId>,
    normalized_bound: BigRational,
    is_upper: bool,
    is_integer: bool,
    reason_lits: Vec<(TermId, bool)>,
}

impl BoundRefinementReplayKey {
    pub(crate) fn new(request: &BoundRefinementRequest) -> Self {
        let mut reason_lits: Vec<(TermId, bool)> = request
            .reason
            .iter()
            .map(|lit| (lit.term, lit.value))
            .collect();
        reason_lits.sort_unstable();
        reason_lits.dedup();
        let normalized_bound = if request.is_integer {
            let int_bound = if request.is_upper {
                request.bound_value.floor().to_integer()
            } else {
                request.bound_value.ceil().to_integer()
            };
            BigRational::from_integer(int_bound)
        } else {
            request.bound_value.clone()
        };
        Self {
            variable: request.variable,
            rhs_term: request.rhs_term,
            normalized_bound,
            is_upper: request.is_upper,
            is_integer: request.is_integer,
            reason_lits,
        }
    }
}

/// Encode a split-atom pair into the incremental SAT solver and return the
/// 0-indexed SAT variables for `(left_atom, right_atom)`.
pub(in crate::executor) fn encode_split_pair_incremental(
    terms: &TermStore,
    solver: &mut SatSolver,
    local_term_to_var: &mut HashMap<TermId, u32>,
    local_var_to_term: &mut HashMap<u32, TermId>,
    local_next_var: &mut u32,
    negations: &mut IncrementalNegationCache,
    split_pair: (TermId, TermId),
) -> Option<(SatVariable, SatVariable)> {
    let (left_atom, right_atom) = split_pair;

    fn reuse_encoded_atom(
        solver: &mut SatSolver,
        local_term_to_var: &HashMap<TermId, u32>,
        atom: TermId,
    ) -> Option<SatVariable> {
        let var = SatVariable::new(*local_term_to_var.get(&atom)?);
        freeze_var_if_needed(solver, var);
        Some(var)
    }

    fn encode_new_atom(
        terms: &TermStore,
        solver: &mut SatSolver,
        local_term_to_var: &mut HashMap<TermId, u32>,
        local_var_to_term: &mut HashMap<u32, TermId>,
        local_next_var: &mut u32,
        negations: &mut IncrementalNegationCache,
        atom: TermId,
    ) -> Option<SatVariable> {
        // Fast path for OPAQUE arithmetic predicates (`<=`, `>=`, `<`, `>`) —
        // the shape of every split atom this module mints. Tseitin encodes
        // these as a bare `get_var` leaf (see `encode_app`'s theory-predicate
        // arm): no descent, no definitional clauses, and the root-asserting
        // unit is separated out by `encode_assertion` anyway. The general
        // `encode_atom_delta` path below is a more expensive no-op for them
        // (move the encoder out of `negations`, run `encode_assertion`, delta-
        // merge, move it back). Allocating the very same fresh var directly is
        // byte-identical in outcome: same var id (the seeded Tseitin's first
        // `fresh_var()` is `local_next_var + 1` 1-indexed = `*local_next_var`
        // 0-indexed), same map entries, same `note_fresh_term`, same
        // `ensure_num_vars`, and no clauses. `mirror_encoder_var` keeps the
        // persistent encoder in sync so a later composite that references this
        // predicate as a sub-term reuses the same var. Non-predicate shapes
        // (constant-folded atoms, boolean structure) keep the general path.
        if matches!(
            terms.get(atom),
            TermData::App(sym, _) if matches!(sym.name(), "<=" | ">=" | "<" | ">")
        ) {
            let var_0idx = *local_next_var;
            local_term_to_var.insert(atom, var_0idx);
            local_var_to_term.insert(var_0idx, atom);
            negations.note_fresh_term(atom);
            // Keep the persistent Tseitin encoder consistent with this direct
            // allocation so a later encode that references `atom` reuses this
            // var instead of minting a fresh duplicate (#8786).
            negations.mirror_encoder_var(atom, var_0idx);
            *local_next_var = var_0idx + 1;
            solver.ensure_num_vars(*local_next_var as usize);
            let atom_var = SatVariable::new(var_0idx);
            freeze_var_if_needed(solver, atom_var);
            return Some(atom_var);
        }

        // #8786 / #incr-tseitin-persist: delta-encode this atom into the
        // persistent Tseitin encoder so already-encoded sub-terms reuse their
        // stable SAT vars (Tseitin::new() would mint FRESH vars for sub-terms
        // already in the SAT solver, orphaning prior unit clauses and producing
        // two SAT vars for one TermId — spurious Unknown on QF_UFLRA/QF_UFLIA).
        // Only this atom's new sub-terms and def clauses are touched.
        let _root_lit = encode_atom_delta(
            terms,
            solver,
            local_term_to_var,
            local_var_to_term,
            local_next_var,
            negations,
            atom,
        );

        let atom_var = *local_term_to_var.get(&atom)?;
        let atom_var = SatVariable::new(atom_var);
        freeze_var_if_needed(solver, atom_var);
        Some(atom_var)
    }

    // Repeated disequality/expression split requests can target the same atoms
    // across split-loop iterations. Reusing the original SAT vars keeps the
    // persistent SAT state aligned with the theory term mapping.
    let left_var = reuse_encoded_atom(solver, local_term_to_var, left_atom).or_else(|| {
        encode_new_atom(
            terms,
            solver,
            local_term_to_var,
            local_var_to_term,
            local_next_var,
            negations,
            left_atom,
        )
    })?;
    let right_var = reuse_encoded_atom(solver, local_term_to_var, right_atom).or_else(|| {
        encode_new_atom(
            terms,
            solver,
            local_term_to_var,
            local_var_to_term,
            local_next_var,
            negations,
            right_atom,
        )
    })?;

    Some((left_var, right_var))
}

/// Delta-encode a single `atom` into the persistent incremental Tseitin encoder
/// (held inside `negations`), emitting only the NEW definitional clauses and
/// merging only the NEW variables into the local 0-indexed maps.
///
/// This replaces the former rebuild-everything pair (`local_tseitin_state` +
/// `merge_local_mappings_from_tseitin`), which copied the ENTIRE term↔var map
/// into a fresh `TseitinState` and iterated the whole result map back on EVERY
/// cache-miss atom — O(total-encoded-terms) per atom, O(n²) over a run
/// (#incr-tseitin-persist). Now:
///
/// - the encoder state is *moved* out of `negations` (O(1)) rather than rebuilt;
/// - `encode_assertion` clausifies only sub-terms not already in the persisted
///   `term_to_var`, returning just the new `def_clauses` (the root-asserting
///   unit is separated out into `root_lit` and never emitted here);
/// - only variables in `[prev_next_var, next_var)` are merged into the local
///   maps — O(size-of-atom), not O(map).
///
/// **Behavior preservation**: `take_tseitin_encoder` seeds `term_to_var` /
/// `var_to_term` / `next_var` identically to the old `local_tseitin_state`
/// (1-indexed, `next_var = local_next_var + 1` floor) and resets `encoded` to
/// empty every call, so the emitted CNF equals the old `transform_all(&[atom])`
/// clauses minus the skipped root unit — same variable numbering, equisatisfiable.
///
/// `local_next_var` is advanced to strictly bound every variable that can reach
/// the SAT solver (all allocated vars plus any literal in the new def clauses),
/// preserving the #8805 / #8785 out-of-bounds guarantee over the delta.
///
/// Returns the assertion's root literal (signed, 1-indexed Tseitin namespace).
fn encode_atom_delta(
    terms: &TermStore,
    solver: &mut SatSolver,
    local_term_to_var: &mut HashMap<TermId, u32>,
    local_var_to_term: &mut HashMap<u32, TermId>,
    local_next_var: &mut u32,
    negations: &mut IncrementalNegationCache,
    atom: TermId,
) -> CnfLit {
    let state =
        negations.take_tseitin_encoder(local_term_to_var, local_var_to_term, *local_next_var);
    let prev_next_var = state.next_var;
    let mut tseitin = if negations.proof_enabled() {
        Tseitin::from_state_with_proofs(terms, state)
    } else {
        Tseitin::from_state(terms, state)
    };
    let enc = tseitin.encode_assertion(atom);
    let state = tseitin.into_state();
    let new_next_var = state.next_var;

    // Delta-merge: only variables allocated by THIS encode carry 1-indexed ids
    // in `[prev_next_var, new_next_var)`. Seeded sub-terms kept their existing
    // vars (via the persisted `term_to_var`), so they already live in the local
    // maps and need no re-merge.
    for var_1idx in prev_next_var..new_next_var {
        if let Some(&term) = state.var_to_term.get(&var_1idx) {
            let sat_var = var_1idx - 1; // 1-indexed Tseitin var -> 0-indexed local var
            local_var_to_term.insert(sat_var, term);
            if local_term_to_var.insert(term, sat_var).is_none() {
                negations.note_fresh_term(term);
            }
        }
    }

    // Advance `local_next_var` to strictly bound every SAT var that can appear
    // in a clause handed to the solver: all allocated vars (`new_next_var - 1`
    // = 0-indexed var count) plus any literal in the new def clauses. The clause
    // scan is the #8805 belt-and-braces guard, now over the delta only.
    let mut var_count = *local_next_var;
    if new_next_var.saturating_sub(1) > var_count {
        var_count = new_next_var - 1;
    }
    for clause in &enc.def_clauses {
        for &lit in clause.literals() {
            let var_0idx = lit.unsigned_abs() - 1;
            if var_0idx >= var_count {
                var_count = var_0idx + 1;
            }
        }
    }
    *local_next_var = var_count;
    solver.ensure_num_vars(*local_next_var as usize);

    // Put the encoder state back BEFORE any subsequent `mirror_encoder_var`
    // (root-alias fallback in `ensure_incremental_atom_encoded`) so those mirror
    // writes land in the live persisted state.
    negations.put_tseitin_encoder(state);

    add_def_clauses(
        solver,
        &enc.def_clauses,
        enc.def_proof_annotations.as_deref(),
        negations,
    );

    enc.root_lit
}

/// Emit Tseitin definitional clauses into the SAT solver.
///
/// Vars are already in the shared 1-indexed DIMACS namespace (offset 0): each
/// literal `lit` maps to `SatVariable::new(|lit| - 1)`. `encode_assertion`
/// excludes the root-asserting unit, so (unlike the former
/// `add_split_def_clauses`) there is no unit clause to skip.
fn add_def_clauses(
    solver: &mut SatSolver,
    def_clauses: &[CnfClause],
    annotations: Option<&[Option<ay_core::ClausificationProof>]>,
    negations: &mut IncrementalNegationCache,
) {
    if let Some(annotations) = annotations {
        assert_eq!(annotations.len(), def_clauses.len());
    }
    for (index, clause) in def_clauses.iter().enumerate() {
        let lits: Vec<SatLiteral> = clause
            .literals()
            .iter()
            .map(|&lit| {
                if lit > 0 {
                    SatLiteral::positive(SatVariable::new((lit - 1) as u32))
                } else {
                    SatLiteral::negative(SatVariable::new((-lit - 1) as u32))
                }
            })
            .collect();
        // #8805 instrumentation: catch out-of-bounds literal before panic.
        if let Some(bad) = lits
            .iter()
            .find(|l| l.variable().index() >= solver.user_num_vars())
        {
            eprintln!(
                "[#8805] add_def_clauses: OUT-OF-BOUNDS lit var={} solver.user_num_vars={} clause={:?}",
                bad.variable().index(),
                solver.user_num_vars(),
                clause.literals(),
            );
        }
        let before = solver.issued_original_clause_id_max();
        solver.add_clause(lits);
        if let (Some(original_id), Some(Some(annotation))) = (
            single_issued_original_id_since(solver, before),
            annotations.map(|all| all[index].clone()),
        ) {
            negations.note_clausification_authority(original_id, annotation);
        }
    }
}

/// Ensure an atom is Tseitin-encoded into the incremental SAT solver.
///
/// Returns the SAT variable representing `atom` with positive polarity:
/// `SatLiteral::positive(result)` asserts `atom` as true, `SatLiteral::negative`
/// asserts it as false. This semantic is load-bearing for callers that build
/// blocking clauses or triangle-adapter clauses using the returned variable.
pub(crate) fn ensure_incremental_atom_encoded(
    terms: &TermStore,
    solver: &mut SatSolver,
    local_term_to_var: &mut HashMap<TermId, u32>,
    local_var_to_term: &mut HashMap<u32, TermId>,
    local_next_var: &mut u32,
    negations: &mut IncrementalNegationCache,
    atom: TermId,
) -> SatVariable {
    if let Some(&var) = local_term_to_var.get(&atom) {
        let sat_var = SatVariable::new(var);
        freeze_var_if_needed(solver, sat_var);
        return sat_var;
    }

    // #8786 / #incr-tseitin-persist: delta-encode this atom into the persistent
    // Tseitin encoder so sub-terms already encoded (e.g., literals re-used across
    // triangle axioms) reuse their stable SAT vars rather than getting fresh
    // duplicates. Only this atom's new sub-terms and def clauses are emitted.
    let root_lit = encode_atom_delta(
        terms,
        solver,
        local_term_to_var,
        local_var_to_term,
        local_next_var,
        negations,
        atom,
    );

    // Tseitin may not map the top-level atom in `term_to_var` for several
    // reasons (see `encode_inner` in `ay-core/src/tseitin/encode.rs`):
    //
    // - `Not(inner)`: `encode_inner` returns `-encode(inner, !positive)` and
    //   never inserts the outer `Not` term itself. `root_lit` will be the
    //   negated inner var.
    // - `Bool(true)` / `Bool(false)`: `encode_inner` creates a fresh variable
    //   via `fresh_var()` but never calls `get_var(term_id)`, so no mapping
    //   for the constant is created.
    // - Single-argument `And([x])` / `Or([x])`: delegates to
    //   `encode(x, positive)` without mapping the outer term.
    //
    // In each case `root_lit` is the CnfLit representing the atom's truth value.
    // When `root_lit` is positive, the omitted wrapper preserves the same
    // "positive var means atom=true" semantics, so we can alias the atom to the
    // root var. When `root_lit` is negative (for example, `Not(x)` or another
    // wrapper that delegates to a negated inner literal), aliasing the atom to
    // `abs(root)` would invert polarity. In that case allocate a fresh adapter
    // variable `v_atom <=> root_lit` so callers can safely treat
    // `positive(v_atom)` as "atom is true".
    if !local_term_to_var.contains_key(&atom) {
        let root_var = root_lit.unsigned_abs();
        let sat_var = root_var - 1;
        if root_lit > 0 {
            // The root var is already in the shared 1-indexed SAT namespace;
            // subtract 1 for the 0-indexed local scheme.
            local_term_to_var.insert(atom, sat_var);
            local_var_to_term.entry(sat_var).or_insert(atom);
            // Keep the persistent encoder aware that `atom` aliases this var.
            negations.mirror_encoder_var(atom, sat_var);
        } else {
            let atom_var = *local_next_var;
            *local_next_var += 1;
            solver.ensure_num_vars(*local_next_var as usize);

            let root_sat_var = SatVariable::new(sat_var);
            let atom_sat_var = SatVariable::new(atom_var);
            let adapter_complement = match terms.get(atom) {
                TermData::Not(inner) => Some(*inner),
                _ => None,
            };
            // v_atom <=> root_lit, where root_lit is negative in this branch.
            let first_before = solver.issued_original_clause_id_max();
            solver.add_clause(vec![
                SatLiteral::negative(atom_sat_var),
                SatLiteral::negative(root_sat_var),
            ]);
            if let (Some(original_id), Some(complement)) = (
                single_issued_original_id_since(solver, first_before),
                adapter_complement,
            ) {
                negations.note_theory_authority(
                    original_id,
                    ay_core::TheoryLemmaProof {
                        clause: vec![complement, atom],
                        kind: ay_core::TheoryLemmaKind::BoolTautology,
                        farkas: None,
                        lia: None,
                    },
                );
            }
            let second_before = solver.issued_original_clause_id_max();
            solver.add_clause(vec![
                SatLiteral::positive(atom_sat_var),
                SatLiteral::positive(root_sat_var),
            ]);
            if let (Some(original_id), Some(complement)) = (
                single_issued_original_id_since(solver, second_before),
                adapter_complement,
            ) {
                negations.note_theory_authority(
                    original_id,
                    ay_core::TheoryLemmaProof {
                        clause: vec![atom, complement],
                        kind: ay_core::TheoryLemmaKind::BoolTautology,
                        farkas: None,
                        lia: None,
                    },
                );
            }

            local_term_to_var.insert(atom, atom_var);
            local_var_to_term.insert(atom_var, atom);
            // Reserve the fresh adapter var in the persistent encoder so a later
            // encode never re-mints it.
            negations.mirror_encoder_var(atom, atom_var);
        }
        negations.note_fresh_term(atom);
    }

    let atom_var = local_term_to_var
        .get(&atom)
        .copied()
        .expect("Tseitin should always map incremental refinement atoms (root fallback)");
    let atom_var = SatVariable::new(atom_var);
    freeze_var_if_needed(solver, atom_var);
    atom_var
}

/// Ensure every Bool-sorted argument of a UF application has a SAT variable so
/// DPLL(T) can DECIDE its truth value. (#bool-arg-congruence)
///
/// When a UF takes a Bool argument — e.g. `(bool (and ...))` or `f(p, x)` with
/// `p : Bool` — congruence requires that two applications whose Bool arguments
/// share a truth value be merged. EUF enforces this completeness (it rejects
/// non-congruent assignments as conflicts), but only AFTER the Bool-arg atom is
/// actually assigned a truth value. A Bool arg that appears *only* inside UF
/// applications (clauseless) gets no SAT variable from Tseitin, so the SAT
/// solver never branches on it, the EUF model stays partial, and the model
/// validator degrades the result to `unknown`.
///
/// This pass allocates+freezes a SAT variable for each such atom. Freshly
/// allocated SAT variables are inserted into the decision heap (VSIDS/VMTF), so
/// the solver branches on them before declaring SAT — letting EUF's now-complete
/// Bool-argument congruence either find a congruent model (sound `sat`) or drive
/// the search to backtrack (sound `unsat`).
///
/// Gated by `AY_EUF_BOOL_ARG_CONGRUENCE` (default ON); a `false` flag skips the
/// pass, preserving the prior (sound `unknown`) behavior.
#[allow(clippy::too_many_arguments)]
pub(in crate::executor) fn encode_bool_uf_arg_atoms(
    terms: &TermStore,
    solver: &mut SatSolver,
    local_term_to_var: &mut HashMap<TermId, u32>,
    local_var_to_term: &mut HashMap<u32, TermId>,
    local_next_var: &mut u32,
    negations: &mut IncrementalNegationCache,
    active_atoms: &HashSet<TermId>,
    incremental_mode: bool,
) -> usize {
    // Decides clauseless Bool-UF-arg atoms so a SAT-buried Bool arg (one that
    // appears ONLY inside opaque UF applications, e.g. the deeply nested
    // xor/and args of the `uf_fs2` witness) gets a SAT variable and is forwarded
    // to EUF, where the Bool-arg merge enforces congruence. Required for the
    // `uf_fs2` false-SAT witness.
    //
    // Gated to NON-incremental (single check-sat) mode: in deep incremental
    // sessions, re-encoding+freezing thousands of accumulated clauseless atoms
    // every check-sat collapses CLEARSY completeness (121 -> ~50 solved); those
    // files surface their Bool args through the SAT skeleton, so the cheap
    // EUF-side Bool-arg merge already enforces congruence there without this
    // pass. (The former `AY_EUF_BOOL_ARG_SAT_ENCODE=1` incremental
    // force-enable is removed; OFF in incremental mode is the default.)
    if incremental_mode {
        return 0;
    }
    // Deterministic iteration: collect candidate atoms, sort, then encode.
    let mut candidates: Vec<TermId> = Vec::new();
    let mut seen: HashSet<TermId> = HashSet::default();
    for idx in 0..terms.len() {
        let term_id = TermId(idx as u32);
        if let TermData::App(ay_core::term::Symbol::Named(name), args) = terms.get(term_id) {
            // Skip Boolean connectives / builtins: their arguments are owned by
            // the SAT skeleton and already encoded. Only genuine UF applications
            // (which take Bool args opaquely) need their Bool args decided.
            match name.as_str() {
                "and" | "or" | "xor" | "=>" | "not" | "=" | "distinct" | "ite" => continue,
                _ => {}
            }
            for &arg in args {
                if terms.sort(arg) == &ay_core::Sort::Bool
                    && local_term_to_var.get(&arg).is_none()
                    && seen.insert(arg)
                {
                    // Only encode atoms that the theory considers active (i.e.,
                    // reachable from live assertions). `active_atoms` already
                    // contains UF Bool args via collect_active_theory_atoms.
                    if active_atoms.contains(&arg) {
                        candidates.push(arg);
                    }
                }
            }
        }
    }
    candidates.sort_unstable_by_key(|t| t.0);

    let mut encoded = 0usize;
    for atom in candidates {
        if local_term_to_var.contains_key(&atom) {
            continue;
        }
        ensure_incremental_atom_encoded(
            terms,
            solver,
            local_term_to_var,
            local_var_to_term,
            local_next_var,
            negations,
            atom,
        );
        encoded += 1;
    }
    encoded
}

/// Replay pending bound refinements into the persistent incremental SAT solver.
///
/// Returns `false` if a reason literal is unmapped; duplicate clauses are skipped.
#[allow(clippy::too_many_arguments)]
pub(in crate::executor) fn replay_incremental_bound_refinements(
    terms: &mut TermStore,
    solver: &mut SatSolver,
    local_term_to_var: &mut HashMap<TermId, u32>,
    local_var_to_term: &mut HashMap<u32, TermId>,
    local_next_var: &mut u32,
    negations: &mut IncrementalNegationCache,
    pending_refinements: &[BoundRefinementRequest],
    added_refinement_clauses: &mut HashSet<BoundRefinementReplayKey>,
) -> bool {
    for request in pending_refinements {
        let key = BoundRefinementReplayKey::new(request);
        if !added_refinement_clauses.insert(key) {
            continue;
        }
        let atom = crate::bound_refinement::materialize_bound_refinement_atom_term(terms, request);
        let bound_var = ensure_incremental_atom_encoded(
            terms,
            solver,
            local_term_to_var,
            local_var_to_term,
            local_next_var,
            negations,
            atom,
        );

        let mut clause = Vec::with_capacity(request.reason.len() + 1);
        for reason_lit in &request.reason {
            let Some(&var) = local_term_to_var.get(&reason_lit.term) else {
                return false;
            };
            clause.push(if reason_lit.value {
                SatLiteral::negative(SatVariable::new(var))
            } else {
                SatLiteral::positive(SatVariable::new(var))
            });
        }
        clause.push(SatLiteral::positive(bound_var));
        solver.add_clause(clause);
    }

    true
}

/// Result of mapping a theory conflict to a SAT blocking clause.
pub(in crate::executor) enum BlockingClauseResult {
    /// Primary clause was added to the SAT solver, plus all mappable
    /// extra_conflicts. Continue the SAT loop.
    Added {
        primary_original_id: Option<u64>,
        extra_original_ids: Vec<(usize, u64)>,
    },
    /// The conflict mapped to an empty clause, meaning unconditional UNSAT.
    /// The caller should pop the SAT scope and return `SolveResult::Unsat`.
    Unsat,
    /// Some conflict terms failed to map through `local_term_to_var`.
    /// The blocking clause would be STRONGER than what the theory proved,
    /// so the caller should return `SolveResult::Unknown` (#5117).
    Unmapped,
}

/// Map theory conflict literals to SAT literals for a blocking clause.
///
/// Each `TheoryLit { term, value }` is negated (value=true → negative literal,
/// value=false → positive literal) so the clause blocks the conflicting assignment.
///
/// Returns `BlockingClauseResult::Unmapped` if any conflict term fails to map.
/// Returns the clause via `BlockingClauseResult` for the caller to log/add.
///
/// Deduplicates the conflict-term-mapping pattern that appeared twice in
/// `solve_lia_incremental` (for `TheoryResult::Unsat` and `UnsatWithFarkas`).
fn map_conflict_lits(
    conflict_lits: &[TheoryLit],
    local_term_to_var: &HashMap<TermId, u32>,
) -> Result<Vec<SatLiteral>, (usize, usize)> {
    let mut dropped = 0usize;
    let clause: Vec<SatLiteral> = conflict_lits
        .iter()
        .filter_map(|t| {
            local_term_to_var
                .get(&t.term)
                .map(|&var| {
                    if t.value {
                        SatLiteral::negative(SatVariable::new(var))
                    } else {
                        SatLiteral::positive(SatVariable::new(var))
                    }
                })
                .or_else(|| {
                    dropped += 1;
                    None
                })
        })
        .collect();

    if dropped > 0 {
        Err((dropped, conflict_lits.len()))
    } else {
        Ok(clause)
    }
}

/// Map theory conflict literals to a SAT blocking clause and add it to the solver.
///
/// Each `TheoryLit { term, value }` is negated (value=true → negative literal,
/// value=false → positive literal) so the clause blocks the conflicting assignment.
///
/// This function also processes `extra_conflicts` (batch-collected bound conflicts
/// from `collect_all_bound_conflicts`), adding each as a blocking clause. Extra
/// conflicts with unmapped terms are silently skipped (partial mapping is unsound).
///
/// Deduplicates the conflict-to-blocking-clause pattern that appeared twice in
/// `solve_lia_incremental` (for `TheoryResult::Unsat` and `UnsatWithFarkas`).
pub(in crate::executor) fn map_conflict_to_blocking_clause(
    solver: &mut SatSolver,
    conflict_lits: &[TheoryLit],
    extra_conflicts: &[TheoryConflict],
    local_term_to_var: &HashMap<TermId, u32>,
) -> BlockingClauseResult {
    let clause = match map_conflict_lits(conflict_lits, local_term_to_var) {
        Ok(c) => c,
        Err(_) => {
            return BlockingClauseResult::Unmapped;
        }
    };

    if clause.is_empty() {
        debug_assert!(
            conflict_lits.is_empty(),
            "BUG(#3820): conflict terms all failed to map: {conflict_lits:?}"
        );
        return BlockingClauseResult::Unsat;
    }

    // #unguarded-tvalid-lemmas STAGE 1: this is the split-loop Farkas/theory
    // conflict lemma — a THEORY TAUTOLOGY over term-semantic atom literals.
    // T-validity provenance: `map_conflict_lits` above maps ONLY TermId-keyed
    // atoms (partial map => `Unmapped` => no clause is ever added), so the
    // clause is the negation of a theory-inconsistent atom conjunction, valid
    // at every scope forever. Routed through the conflict-lemma gate: scoped
    // (old behavior) unless the solver's `unguarded_theory_conflict_lemmas`
    // flag is set (the inc-engine QF_LRA lane), in which case it persists
    // across pop() in the deletable learned tier.
    let primary_before = solver.issued_original_clause_id_max();
    let _ = solver.add_theory_conflict_lemma(clause);
    let primary_original_id = single_issued_original_id_since(solver, primary_before);

    // Add blocking clauses for remaining batch-collected bound conflicts (#5117).
    // Skip any extra clause where a conflict term fails to map — a partial
    // clause is stronger than what the theory proved and could cause false UNSAT.
    let extra_original_ids = add_extra_blocking_clauses(solver, extra_conflicts, local_term_to_var);

    BlockingClauseResult::Added {
        primary_original_id,
        extra_original_ids,
    }
}

/// Encode a split pair into the incremental SAT solver, build a disjunctive
/// clause (optionally with a disequality guard literal), and add it.
///
/// Returns the SAT variables for `(left_atom, right_atom)` plus whether this
/// call inserted fresh SAT-visible split clauses.
///
/// This deduplicates the encode → clause → add_clause pattern that appeared in
/// `NeedSplit`, `NeedDisequalitySplit`, and `NeedExpressionSplit` handlers of
/// `solve_incremental_split_loop_pipeline!` (#6321).
#[allow(clippy::too_many_arguments)]
pub(in crate::executor) fn encode_and_add_split_clause(
    terms: &mut TermStore,
    solver: &mut SatSolver,
    local_term_to_var: &mut HashMap<TermId, u32>,
    local_var_to_term: &mut HashMap<u32, TermId>,
    local_next_var: &mut u32,
    negations: &mut IncrementalNegationCache,
    left_atom: TermId,
    right_atom: TermId,
    disequality_guard: Option<(TermId, bool)>,
    added_split_clauses: &mut HashSet<SplitClauseKey>,
) -> (SatVariable, SatVariable, bool) {
    let (left_var, right_var) = encode_split_pair_incremental(
        terms,
        solver,
        local_term_to_var,
        local_var_to_term,
        local_next_var,
        negations,
        (left_atom, right_atom),
    )
    .expect("Tseitin should always map split atoms");

    let key = SplitClauseKey {
        left_atom,
        right_atom,
        disequality_guard,
    };
    if !added_split_clauses.insert(key) {
        return (left_var, right_var, false);
    }

    let mut clause = vec![
        SatLiteral::positive(left_var),
        SatLiteral::positive(right_var),
    ];
    let mut proof_clause = vec![left_atom, right_atom];
    if let Some((diseq_term, is_distinct)) = disequality_guard {
        let mut guard_lit_mapped =
            split_guard_clause_literal(terms, local_term_to_var, diseq_term, is_distinct);
        // (#ground-conflict-decomp, guard restoration) When the guard atom has
        // no SAT variable, the historical behavior emitted the 2-literal
        // branch clause WITHOUT its equality guard — sound only in the
        // requesting context and NOT standalone-valid, so no theory authority
        // could ever be recorded and the proof surfaced it as an
        // uncertifiable Generic clause. Encode the guard's equality atom
        // (delta-Tseitin: stable vars, only new definitional clauses) so the
        // emitted clause is the guarded 3-literal integer-split TAUTOLOGY
        // (`x<=c-1 ∨ x>=c+1 ∨ x=c`). Strictly weaker than the historical
        // clause, so it can never manufacture a wrong verdict; the theory
        // refutes a `guard=true` assignment through its ordinary conflict
        // path. `distinct` guards keep the historical behavior.
        if guard_lit_mapped.is_none()
            && !is_distinct
            && crate::quant_unit_authority::ground_conflict_decomp_enabled()
        {
            let inner = match terms.get(diseq_term) {
                TermData::Not(inner) => Some(*inner),
                TermData::App(sym, args) if sym.name() == "not" && args.len() == 1 => Some(args[0]),
                _ => None,
            };
            if let Some(inner) = inner {
                if matches!(
                    terms.get(inner),
                    TermData::App(sym, args) if sym.name() == "=" && args.len() == 2
                ) {
                    let _ = encode_atom_delta(
                        terms,
                        solver,
                        local_term_to_var,
                        local_var_to_term,
                        local_next_var,
                        negations,
                        inner,
                    );
                    guard_lit_mapped = local_term_to_var.get(&inner).map(|&mapped| {
                        let var = SatVariable::new(mapped);
                        freeze_var_if_needed(solver, var);
                        SatLiteral::positive(var)
                    });
                }
            }
        }
        if let Some(guard_lit) = guard_lit_mapped {
            clause.push(guard_lit);
            let guard_term = if guard_lit.is_positive() {
                local_var_to_term
                    .get(&(guard_lit.variable().index() as u32))
                    .copied()
            } else {
                local_var_to_term
                    .get(&(guard_lit.variable().index() as u32))
                    .copied()
                    .map(|term| match terms.get(term) {
                        TermData::Not(inner) => *inner,
                        _ => terms.mk_not(term),
                    })
            };
            if let Some(guard_term) = guard_term {
                proof_clause.push(guard_term);
            }
        }
    }
    // ORIGINAL-ledger route (scoped): split progress clauses are added once
    // per key (see `added_split_clauses`) and must survive every
    // `reset_search_state` for the rest of their scope. The theory-lemma
    // route stores them LEARNED-tier, which a destructive arena rebuild
    // (BVE/L0-GC count drift) silently discards — the SAT model then
    // revisits the excluded assignment, the theory re-requests the same
    // split, the dedup skips re-adding, and the refinement loop LIVELOCKS
    // (observed: the 2^64-guarded array-frame certification ground >10^5
    // rounds re-requesting one wiped expression split). `add_clause`
    // registers the clause in the scoped original ledger, which every
    // rebuild path re-adds; this also matches the non-incremental
    // pipelines, where split clauses are re-encoded as input clauses.
    let cover_before = solver.issued_original_clause_id_max();
    let mut added_any = solver.add_clause(clause);
    if let Some(original_id) = single_issued_original_id_since(solver, cover_before) {
        let kind =
            if ay_core::proof_validation::recognize_int_bounds_tautology(terms, &proof_clause) {
                Some(ay_core::TheoryLemmaKind::IntBoundsTautology)
            } else if ay_core::proof_validation::recognize_arith_disequality_split(
                terms,
                &proof_clause,
            ) {
                Some(ay_core::TheoryLemmaKind::ArithDisequalitySplit)
            } else {
                None
            };
        if let Some(kind) = kind {
            negations.note_theory_authority(
                original_id,
                ay_core::TheoryLemmaProof {
                    clause: proof_clause,
                    kind,
                    farkas: None,
                    lia: None,
                },
            );
        }
    }

    // #8762 optimization: disequality and expression splits encode genuinely
    // mutually exclusive branches — `x <= c-1` and `x >= c+1` for int splits,
    // `x < c` and `x > c` for real splits, and `E <= F-1` and `E >= F+1` for
    // expression splits. All LRA-level bound pairs are mutex. Adding
    // `(¬left ∨ ¬right)` gives the SAT layer the full exactly-one semantics so
    // BCP can eliminate bad decisions without needing an LRA check round.
    //
    // Without this clause, on puzzle-style QF_LIA with many pairwise
    // disequalities (8-queens = 56 disequalities), the SAT solver may try
    // configurations that assert both `left` and `right` true, only learning
    // they conflict via an LRA Farkas conflict — 28–300x slowdown per decision.
    //
    // For branch-and-bound (`NeedSplit`) splits the branches `x<=floor` and
    // `x>=ceil` are still mutex whenever `floor < ceil` (the only case
    // `create_int_split_atoms` produces), so the mutex clause is always sound
    // for every caller of this helper.
    //
    // Safety: if Tseitin reused the same SAT variable for both atoms (left_atom
    // == right_atom or they simplified to identical sub-terms), emitting
    // `(¬v ∨ ¬v)` would combine with the `(v ∨ v)` at-least-one clause above
    // to force UNSAT. Skip the mutex clause in that degenerate case; the
    // at-least-one already forced `v=true`, which is the correct semantics for
    // a tautologically-true split.
    if left_var != right_var {
        let not_left = terms.mk_not(left_atom);
        let not_right = terms.mk_not(right_atom);
        let mutex_clause = vec![
            SatLiteral::negative(left_var),
            SatLiteral::negative(right_var),
        ];
        let mutex_before = solver.issued_original_clause_id_max();
        added_any |= solver.add_clause(mutex_clause);
        if let Some(original_id) = single_issued_original_id_since(solver, mutex_before) {
            let proof_clause = vec![not_left, not_right];
            if ay_core::proof_validation::recognize_int_bounds_tautology(terms, &proof_clause) {
                negations.note_theory_authority(
                    original_id,
                    ay_core::TheoryLemmaProof {
                        clause: proof_clause,
                        kind: ay_core::TheoryLemmaKind::IntBoundsTautology,
                        farkas: None,
                        lia: None,
                    },
                );
            } else {
                let conflict = vec![
                    TheoryLit::new(left_atom, true),
                    TheoryLit::new(right_atom, true),
                ];
                let farkas = ay_core::FarkasAnnotation::from_ints(&[1, 1]);
                if ay_core::proof_validation::verify_farkas_conflict_lits_full(
                    terms, &conflict, &farkas,
                )
                .is_ok()
                {
                    negations.note_theory_authority(
                        original_id,
                        ay_core::TheoryLemmaProof {
                            clause: proof_clause,
                            kind: ay_core::TheoryLemmaKind::LraFarkas,
                            farkas: Some(farkas),
                            lia: None,
                        },
                    );
                }
            }
        }
    }

    (left_var, right_var, added_any)
}

/// Encode the binary theory lemma `⟨diseq guard⟩ ∨ ¬atom`
/// (#array-index-split companion, see `array_select_index_diseq_lemma_atom`).
///
/// Unlike [`encode_and_add_split_clause`] the atom literal is NEGATIVE: the
/// lemma is an implication (`diseq ⟹ ¬atom`), not a branch pair, so there is
/// no second branch atom and no mutex clause.
///
/// SOUNDNESS: the clause is only valid UNDER the guard — if the guard term
/// cannot be mapped to a SAT literal, adding the remaining `¬atom` unit
/// would assert the consequence unconditionally, so the lemma is dropped
/// instead (fail closed; the ordinary value split still handles the
/// disequality, merely without the convergence help).
#[allow(clippy::too_many_arguments)]
pub(in crate::executor) fn encode_and_add_negated_atom_lemma(
    terms: &mut TermStore,
    solver: &mut SatSolver,
    local_term_to_var: &mut HashMap<TermId, u32>,
    local_var_to_term: &mut HashMap<u32, TermId>,
    local_next_var: &mut u32,
    negations: &mut IncrementalNegationCache,
    atom: TermId,
    disequality_guard: (TermId, bool),
    added_split_clauses: &mut HashSet<SplitClauseKey>,
) -> bool {
    let Some((atom_var, _)) = encode_split_pair_incremental(
        terms,
        solver,
        local_term_to_var,
        local_var_to_term,
        local_next_var,
        negations,
        (atom, atom),
    ) else {
        return false;
    };

    let (diseq_term, is_distinct) = disequality_guard;
    let Some(guard_lit) =
        split_guard_clause_literal(terms, local_term_to_var, diseq_term, is_distinct)
    else {
        return false;
    };

    // Dedup namespace: real splits never use the same term for both branch
    // slots, so (atom, atom, guard) cannot collide with a value-split key.
    let key = SplitClauseKey {
        left_atom: atom,
        right_atom: atom,
        disequality_guard: Some(disequality_guard),
    };
    if !added_split_clauses.insert(key) {
        return false;
    }

    let clause = vec![SatLiteral::negative(atom_var), guard_lit];
    // ORIGINAL-ledger route: same rebuild-survival rationale as the split
    // clauses in `encode_and_add_split_clause` above.
    let before = solver.issued_original_clause_id_max();
    let added = solver.add_clause(clause);
    if let Some(original_id) = single_issued_original_id_since(solver, before) {
        let not_atom = terms.mk_not(atom);
        let guard_term = if guard_lit.is_positive() {
            local_var_to_term
                .get(&(guard_lit.variable().index() as u32))
                .copied()
        } else {
            local_var_to_term
                .get(&(guard_lit.variable().index() as u32))
                .copied()
                .map(|term| match terms.get(term) {
                    TermData::Not(inner) => *inner,
                    _ => terms.mk_not(term),
                })
        };
        // The native checker has an exact schema for this optimization, but
        // the pinned external checker still lacks a premise-free presentation
        // for its congruence contrapositive. Deliberately leave the indexed
        // authority absent: a strict proof depending on the clause fails
        // closed instead of exporting a hole.
        let _ = (original_id, not_atom, guard_term);
    }
    added
}

/// #qfuflia-diseq-preencode: eagerly encode the arithmetic case split for
/// every syntactic integer/real disequality occurrence, up front, instead of
/// discovering them ~2 per split-loop round trip.
///
/// The crafted QF_UFLIA hash/xs families assert hundreds of `(distinct u v)` /
/// `(not (= u v))` facts over Int-valued terms. The lazy flow only surfaces
/// the pairs a candidate model happens to violate — measured on
/// hash_sat_08_14: 52 full SAT re-solves in 10s adding ~2 split atoms each
/// against 448 pairs, then the no-progress cap declares `unknown` (z3: 10 ms).
/// Every split clause emitted here is a guarded theory TAUTOLOGY
/// (`¬diseq ∨ lhs≤rhs-1 ∨ lhs≥rhs+1` over Int, strict `<`/`>` over Real) —
/// the same clause the lazy `NeedDisequalitySplit`/`NeedExpressionSplit`
/// handlers add one at a time — so pre-encoding never changes any verdict; it
/// only lets LIA/LRA eager propagation refute bad candidate models DURING
/// search instead of one final-check round trip per pair.
///
/// Budgeted: at most `MAX_PRE_ENCODED_DISEQ_PAIRS` pairs (first-come), n-ary
/// `distinct` capped per occurrence; over-budget occurrences simply stay on
/// the lazy path. (The former `AY_PRE_ENCODE_INT_DISEQ=0` kill switch is
/// removed; the pass is always on.)
#[allow(clippy::too_many_arguments)]
pub(in crate::executor) fn pre_encode_int_disequality_splits(
    terms: &mut TermStore,
    assertions: &[TermId],
    solver: &mut SatSolver,
    local_term_to_var: &mut HashMap<TermId, u32>,
    local_var_to_term: &mut HashMap<u32, TermId>,
    local_next_var: &mut u32,
    negations: &mut IncrementalNegationCache,
    added_split_clauses: &mut HashSet<SplitClauseKey>,
) -> usize {
    const MAX_PRE_ENCODED_DISEQ_PAIRS: usize = 1024;
    const MAX_DISTINCT_ARITY: usize = 16;

    // Collect (guard_term, guard_is_distinct, lhs, rhs) for every negated
    // Int/Real equality atom and every `distinct` occurrence, mirroring the
    // guards the lazy LRA path attaches (`DisequalitySplitRequest
    // {disequality_term, is_distinct}`): a negated equality guards on the
    // equality atom with `is_distinct=false`; a `distinct` term guards on
    // itself with `is_distinct=true`.
    let mut pairs: Vec<(TermId, bool, TermId, TermId)> = Vec::new();
    let mut stack: Vec<TermId> = assertions.to_vec();
    let mut seen: HashSet<TermId> = HashSet::default();
    let arith_sorted = |terms: &TermStore, t: TermId| {
        matches!(terms.sort(t), ay_core::Sort::Int | ay_core::Sort::Real)
    };
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        if pairs.len() >= MAX_PRE_ENCODED_DISEQ_PAIRS {
            break;
        }
        // Array-carrying formulas are OUT of scope: their disequalities are
        // owned by the EUF/array layer, and pre-encoded LIA split atoms are
        // pure search bloat there (measured: QF_AUFLIA 400-sample -21 solved
        // with pre-encoding on, restored with it off). The hash/hard target
        // shapes are pure UF+LIA.
        if matches!(terms.sort(t), ay_core::Sort::Array(_)) {
            return 0;
        }
        match terms.get(t) {
            TermData::Not(inner) => {
                let inner = *inner;
                if let TermData::App(sym, args) = terms.get(inner) {
                    if sym.name() == "=" && args.len() == 2 && arith_sorted(terms, args[0]) {
                        pairs.push((inner, false, args[0], args[1]));
                    }
                }
                stack.push(inner);
            }
            TermData::App(sym, args) => {
                if sym.name() == "distinct"
                    && args.len() >= 2
                    && args.len() <= MAX_DISTINCT_ARITY
                    && arith_sorted(terms, args[0])
                {
                    for i in 0..args.len() {
                        for j in (i + 1)..args.len() {
                            pairs.push((t, true, args[i], args[j]));
                        }
                    }
                }
                stack.extend(args.iter().copied());
            }
            TermData::Ite(c, a, b) => {
                stack.push(*c);
                stack.push(*a);
                stack.push(*b);
            }
            _ => {}
        }
    }
    pairs.truncate(MAX_PRE_ENCODED_DISEQ_PAIRS);

    // Only worth it in the whack-a-mole regime: with few pairs the lazy path
    // resolves them in one or two rounds anyway, and the extra atoms/clauses
    // measurably perturb borderline searches (QF_UFLIA xs-*: 0-2 diseqs,
    // 15 borderline files regressed past the 10s line when pre-encoded).
    const MIN_PRE_ENCODED_DISEQ_PAIRS: usize = 32;
    if pairs.len() < MIN_PRE_ENCODED_DISEQ_PAIRS {
        return 0;
    }

    let mut encoded = 0usize;
    for (guard_term, is_distinct, lhs, rhs) in pairs {
        if terms.sort(lhs) != terms.sort(rhs) {
            continue;
        }
        let (left_atom, right_atom) = match terms.sort(lhs).clone() {
            ay_core::Sort::Int => {
                // E != F  =>  E <= F-1  OR  E >= F+1 (integer-exact split).
                let neg_one = terms.mk_int(num_bigint::BigInt::from(-1));
                let pos_one = terms.mk_int(num_bigint::BigInt::from(1));
                let rhs_minus_one = terms.mk_add(vec![rhs, neg_one]);
                let rhs_plus_one = terms.mk_add(vec![rhs, pos_one]);
                (
                    terms.mk_le(lhs, rhs_minus_one),
                    terms.mk_ge(lhs, rhs_plus_one),
                )
            }
            ay_core::Sort::Real => (terms.mk_lt(lhs, rhs), terms.mk_gt(lhs, rhs)),
            _ => continue,
        };
        let (_, _, added) = encode_and_add_split_clause(
            terms,
            solver,
            local_term_to_var,
            local_var_to_term,
            local_next_var,
            negations,
            left_atom,
            right_atom,
            Some((guard_term, is_distinct)),
            added_split_clauses,
        );
        if added {
            encoded += 1;
        }
    }
    encoded
}

fn split_guard_clause_literal(
    terms: &TermStore,
    local_term_to_var: &HashMap<TermId, u32>,
    diseq_term: TermId,
    is_distinct: bool,
) -> Option<SatLiteral> {
    if let Some(&diseq_var) = local_term_to_var.get(&diseq_term) {
        let var = SatVariable::new(diseq_var);
        return Some(if term_is_not_app(terms, diseq_term) || is_distinct {
            SatLiteral::negative(var)
        } else {
            SatLiteral::positive(var)
        });
    }

    let inner = match terms.get(diseq_term) {
        TermData::Not(inner) => Some(*inner),
        TermData::App(sym, args) if sym.name() == "not" && args.len() == 1 => Some(args[0]),
        _ => None,
    }?;
    local_term_to_var
        .get(&inner)
        .map(|&inner_var| SatLiteral::positive(SatVariable::new(inner_var)))
}

fn term_is_not_app(terms: &TermStore, term: TermId) -> bool {
    match terms.get(term) {
        TermData::Not(_) => true,
        TermData::App(sym, args) => sym.name() == "not" && args.len() == 1,
        _ => false,
    }
}

/// Bias a disjunctive split pair toward a deterministic branch.
///
/// Disequality and expression splits encode `(left_var ∨ right_var)` plus a
/// mutex clause. For pairwise distinct graphs, letting both disjuncts prefer
/// true can produce arbitrary tournament orientations and many LRA conflicts.
/// Prefer the canonical left branch and keep the right branch available for
/// conflict-driven repair.
pub(in crate::executor) fn bias_split_clause_vars(
    solver: &mut SatSolver,
    left_var: SatVariable,
    right_var: SatVariable,
) {
    solver.set_var_phase(left_var, true);
    solver.set_var_phase(right_var, false);
    solver.bump_variable_activity(left_var);
    solver.bump_variable_activity(right_var);
}

/// Encode every disequality split request drained from the theory into the
/// persistent SAT solver (#8762).
///
/// When a theory `check()` batches N violated single-variable disequalities and
/// returns only the first via `NeedDisequalitySplit(first)`, the remaining
/// `N-1` are buffered internally. Without this helper, those extras are
/// discarded on the next `check()` call and the DPLL(T) split loop pays one
/// full SAT resolve per disequality, producing 40x–300x slowdowns on
/// puzzle-style QF_LIA benchmarks.
///
/// The caller must first drain extras from the theory via
/// `TheorySolver::drain_pending_diseq_splits()` so the theory borrow is
/// released before we mutate the term store and SAT solver here.
#[allow(clippy::too_many_arguments)]
pub(in crate::executor) fn encode_pending_diseq_split_extras(
    extras: Vec<ay_core::DisequalitySplitRequest>,
    terms: &mut TermStore,
    solver: &mut SatSolver,
    local_term_to_var: &mut HashMap<TermId, u32>,
    local_var_to_term: &mut HashMap<u32, TermId>,
    local_next_var: &mut u32,
    negations: &mut IncrementalNegationCache,
    added_split_clauses: &mut HashSet<SplitClauseKey>,
) {
    use crate::executor::theories::solve_harness::{
        create_disequality_split_atoms, DisequalitySplitAtoms,
    };
    for split in extras {
        match create_disequality_split_atoms(terms, &split) {
            DisequalitySplitAtoms::Skip => {}
            DisequalitySplitAtoms::IntFractional { le, ge } => {
                let (le_var, ge_var, _) = encode_and_add_split_clause(
                    terms,
                    solver,
                    local_term_to_var,
                    local_var_to_term,
                    local_next_var,
                    negations,
                    le,
                    ge,
                    None,
                    added_split_clauses,
                );
                bias_split_clause_vars(solver, le_var, ge_var);
            }
            DisequalitySplitAtoms::IntExact {
                le,
                ge,
                disequality_term,
                is_distinct,
            } => {
                let guard = disequality_term.map(|dt| (dt, is_distinct));
                let (le_var, ge_var, _) = encode_and_add_split_clause(
                    terms,
                    solver,
                    local_term_to_var,
                    local_var_to_term,
                    local_next_var,
                    negations,
                    le,
                    ge,
                    guard,
                    added_split_clauses,
                );
                bias_split_clause_vars(solver, le_var, ge_var);
            }
            DisequalitySplitAtoms::Real {
                lt,
                gt,
                disequality_term,
                is_distinct,
            } => {
                let guard = disequality_term.map(|dt| (dt, is_distinct));
                let (lt_var, gt_var, _) = encode_and_add_split_clause(
                    terms,
                    solver,
                    local_term_to_var,
                    local_var_to_term,
                    local_next_var,
                    negations,
                    lt,
                    gt,
                    guard,
                    added_split_clauses,
                );
                bias_split_clause_vars(solver, lt_var, gt_var);
            }
        }
    }
}

pub(in crate::executor) mod lemmas;
pub(in crate::executor) use lemmas::apply_string_lemma_incremental;
pub(in crate::executor) use lemmas::apply_theory_lemma_incremental;
pub(in crate::executor) use lemmas::apply_theory_lemma_incremental_persistent;
pub(in crate::executor) use lemmas::take_new_theory_lemmas;

pub(crate) mod model_equality;
pub(crate) use model_equality::ModelEqualityTracker;
pub(crate) use model_equality::{
    RescuePairCounter, SharedRescuePairCounter, DEFAULT_RESCUE_PAIR_BUDGET,
};

#[cfg(test)]
mod tests;

/// Add blocking clauses for batch-collected extra bound conflicts (#5117).
///
/// Each extra conflict is mapped through `local_term_to_var` independently.
/// Conflicts with any unmapped terms are silently skipped (partial mapping
/// is unsound — a partial clause is stronger than what the theory proved).
pub(in crate::executor) fn add_extra_blocking_clauses(
    solver: &mut SatSolver,
    extra_conflicts: &[TheoryConflict],
    local_term_to_var: &HashMap<TermId, u32>,
) -> Vec<(usize, u64)> {
    let mut original_ids = Vec::new();
    for (source_index, extra) in extra_conflicts.iter().enumerate() {
        if let Ok(extra_clause) = map_conflict_lits(&extra.literals, local_term_to_var) {
            if !extra_clause.is_empty() {
                // #unguarded-tvalid-lemmas STAGE 1: batch bound conflicts are
                // theory tautologies over term-semantic atoms (same
                // `map_conflict_lits` full-mapping guarantee as the primary
                // conflict) — route through the conflict-lemma gate so the
                // inc-engine lane retains them across pop(). Scoped (old
                // behavior) whenever the solver flag is off.
                let before = solver.issued_original_clause_id_max();
                let _ = solver.add_theory_conflict_lemma(extra_clause);
                if let Some(id) = single_issued_original_id_since(solver, before) {
                    original_ids.push((source_index, id));
                }
            }
        }
        // Err = some terms unmapped → skip this clause (partial mapping is unsound)
    }
    original_ids
}

pub(crate) fn single_issued_original_id_since(solver: &SatSolver, before: u64) -> Option<u64> {
    let after = solver.issued_original_clause_id_max();
    if after <= before {
        return None;
    }
    let mut issued = (before + 1..=after).filter(|&id| solver.is_issued_original_clause_id(id));
    let id = issued.next()?;
    issued.next().is_none().then_some(id)
}
