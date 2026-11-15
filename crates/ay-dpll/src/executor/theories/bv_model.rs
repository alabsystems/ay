// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! BV model extraction from SAT assignments and array model recovery.
//!
//! Converts SAT solver bit assignments back into bitvector values and
//! recovers array models from BV select terms.
//!
//! Expression evaluation (evaluate_bv_expr, evaluate_bv_bool_predicate,
//! evaluate_bool_substitution) is in `bv_eval.rs`.

// #8529: Use deterministic hash maps in all builds.
use ay_arrays::{ArrayInterpretation, ArrayModel};
use ay_bv::{BvBits, BvModel};
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::TermData;
use ay_core::{Sort, TermId, TermStore};
use num_bigint::BigInt;

use super::super::Executor;
use super::bv_eval::BvEvalMemo;
use crate::executor_format::format_bitvec;

mod array_model;
mod array_reads;
mod definition_operands;
mod definition_order;
mod equality_align;
mod field_targets;
mod ground_definition;
mod live_definitions;
mod model_defaults;
mod nested_cells;
mod nested_reads;
mod read_pins;
mod store_chains;
mod true_store_chain_defs;

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum StoreChainTruth {
    BoolTrue,
    Bv1True,
}

/// Index-value congruence over the bit-blasted `select` reads of one BV model
/// (#abv-select-congruence, wishlist#1).
///
/// Maps `(array base Var, concrete index value)` to the element value the SAT
/// model assigned that read, or `None` when two same-index reads DISAGREE —
/// a poisoned entry that must never be used (fail closed). Built lazily by
/// substitution recovery to resolve a select whose ORIGINAL index term
/// mentions eliminated variables: that term is decoupled from its bit-blasted
/// instance (the defining equalities were consumed by VariableSubstitution),
/// so its stale bit-blast value is untrustworthy, but any OTHER read of the
/// same array at the same concrete index is exact by select congruence.
struct BvSelectCongruence {
    map: HashMap<(TermId, BigInt), Option<BigInt>>,
}

impl Executor {
    /// Extract a bitvector model from SAT solver bit assignments.
    ///
    /// Given a SAT model (variable truth assignments) and the mapping from BV terms
    /// to their bit-blasted SAT literals, reconstruct the bitvector values.
    /// Includes all BV-sorted terms (variables AND function applications) so the
    /// model evaluator can resolve expressions like `(bvult (f x) #x10)`.
    pub(in crate::executor) fn extract_bv_model_from_bits(
        sat_model: &[bool],
        term_bits: &HashMap<TermId, BvBits>,
        var_offset: i32,
        terms: &TermStore,
    ) -> BvModel {
        use num_bigint::BigInt;

        let mut values = HashMap::default();
        let mut stored_term_to_bits = HashMap::default();

        for (&term_id, bits) in term_bits {
            // Include all BV-sorted terms (variables and function applications).
            // Function applications like (f x) are bit-blasted and have concrete
            // SAT assignments; including them lets the model evaluator resolve
            // BV comparison predicates over uninterpreted functions.
            let sort = terms.sort(term_id);
            if !matches!(sort, Sort::BitVec(_)) {
                continue;
            }

            stored_term_to_bits.insert(term_id, bits.clone());

            // Reconstruct value from bits (LSB at index 0)
            let mut value = BigInt::from(0);
            for (i, &bit_lit) in bits.iter().enumerate() {
                let offset_lit = if bit_lit > 0 {
                    bit_lit + var_offset
                } else {
                    bit_lit - var_offset
                };
                let sat_var_idx = if offset_lit > 0 {
                    (offset_lit - 1) as usize
                } else {
                    (-offset_lit - 1) as usize
                };
                let bit_value = if sat_var_idx < sat_model.len() {
                    let sat_val = sat_model[sat_var_idx];
                    if offset_lit > 0 {
                        sat_val
                    } else {
                        !sat_val
                    }
                } else {
                    false
                };
                if bit_value {
                    value |= BigInt::from(1) << i;
                }
            }

            // BV value must fit within declared bit-width (#4661)
            if let Sort::BitVec(bv) = sort {
                debug_assert!(
                    value >= BigInt::from(0) && value < (BigInt::from(1) << bv.width),
                    "BUG: BV model value {} for term {:?} exceeds {}-bit range",
                    value,
                    term_id,
                    bv.width
                );
            }

            values.insert(term_id, value);
        }

        BvModel {
            values,
            term_to_bits: stored_term_to_bits,
            bool_overrides: HashMap::default(),
        }
    }

    /// Seed `bool_overrides` with the SAT assignments of Bool-sorted VARIABLES
    /// that were bit-blasted *inside* BV terms (#bv-ite-bool-model).
    ///
    /// A free Bool variable that appears only as the condition of a BV `ite`
    /// (e.g. `(bvand x (ite b #x2b x))`) gets its SAT literal from the BV
    /// solver's `bitblast_bool` cache (`bool_to_var`), not from the Tseitin
    /// encoding — the Boolean skeleton never sees it. Without this seeding the
    /// emitted model silently defaults such variables to `false`, which can
    /// contradict the mux circuit the SAT solver actually satisfied (the SAT
    /// assignment picked the *then* branch, the printed model claims *else*),
    /// producing an invalid model even though the sat verdict is correct.
    ///
    /// Only `TermData::Var` entries are seeded: variables are the free model
    /// choice points whose bit-blast literal assignment is authoritative.
    /// Compound Bool terms (predicates, connectives) are derivable from leaves
    /// by the model evaluator, and seeding them could pin arbitrary values for
    /// opaque terms the bit-blaster assigned an unconstrained fresh literal.
    ///
    /// Uses `or_insert` so Tseitin-side seeding (#5115) keeps precedence for
    /// variables present in both encodings (they are equal anyway through the
    /// Tseitin-BV linking clauses, #1696/#1708).
    pub(in crate::executor) fn seed_bv_bool_assignments_from_bitblast(
        sat_model: &[bool],
        bool_to_lit: &HashMap<TermId, i32>,
        var_offset: i32,
        terms: &TermStore,
        bv_model: &mut BvModel,
    ) {
        for (&term_id, &lit) in bool_to_lit {
            if lit == 0
                || !matches!(terms.get(term_id), TermData::Var(_, _))
                || *terms.sort(term_id) != Sort::Bool
            {
                continue;
            }
            // Same DIMACS offset/sign decoding as the bit extraction above.
            let offset_lit = if lit > 0 {
                lit + var_offset
            } else {
                lit - var_offset
            };
            let sat_var_idx = (offset_lit.unsigned_abs() - 1) as usize;
            let Some(&raw) = sat_model.get(sat_var_idx) else {
                continue;
            };
            let value = if offset_lit > 0 { raw } else { !raw };
            bv_model.bool_overrides.entry(term_id).or_insert(value);
        }
    }

    // BV expression evaluators (evaluate_bv_expr, evaluate_bv_bool_predicate,
    // evaluate_bool_substitution) moved to bv_eval.rs (#7006).

    /// Recover BV/Bool values for variables eliminated by preprocessing substitution.
    ///
    /// This is a progress fixpoint over the substitution graph. Each successful
    /// recovery uses the same value sources as the old bounded loop: existing
    /// model values, literal constants, and semantic BV/Bool expression
    /// evaluation. Bool recovery is restricted to targets that do not mention
    /// other substituted variables, so an incomplete array/BV axiom set cannot
    /// turn a recovered guard into a false SAT proof.
    pub(in crate::executor) fn recover_substituted_bv_bool_values(
        terms: &TermStore,
        substitutions: &[(TermId, TermId)],
        bv_model: &mut BvModel,
    ) {
        if substitutions.is_empty() {
            return;
        }
        let _t_recover = std::time::Instant::now();

        let substitution_vars: HashSet<TermId> = substitutions
            .iter()
            .map(|(from_var, _)| *from_var)
            .collect();
        for &from_var in &substitution_vars {
            bv_model.values.remove(&from_var);
            bv_model.bool_overrides.remove(&from_var);
        }

        // Seed default values for free variables referenced by substitution
        // RHS expressions but absent from the model (mirrors the LIA lane's
        // recovery, #3201). Such representatives are unconstrained in the
        // post-substitution SAT instance (otherwise extraction or the Tseitin
        // bool_overrides seeding would have assigned them), so any value is
        // consistent. Seeding happens BEFORE the recovery fixpoint so the
        // eliminated variables get values evaluated against the same defaults
        // the validation evaluator uses (Bool: false, BV: zero). Substituted
        // variables themselves are never seeded — they always get evaluated
        // RHS values from the fixpoint below.
        let mut rhs_vars = HashSet::default();
        // Shared visited set across ALL substitution RHS walks: the term store
        // is a hash-consed DAG and substitution RHSs share subterms heavily
        // (post-SSA BMC instances chain substitutions), so without it this
        // walk is once-per-tree-PATH — exponential (the DAG→tree pathology;
        // measured as ~550s of a 600s solve on a 30M-clause BMC instance).
        // Context-free walk: a visited node's vars are already in `rhs_vars`,
        // so cross-call sharing is semantics-preserving.
        let mut rhs_visited = HashSet::default();
        for (_, to_var) in substitutions {
            Self::collect_substitution_rhs_vars(terms, *to_var, &mut rhs_vars, &mut rhs_visited);
        }
        for rhs_var in rhs_vars {
            if substitution_vars.contains(&rhs_var) {
                continue;
            }
            match terms.sort(rhs_var) {
                Sort::Bool => {
                    if !bv_model.bool_overrides.contains_key(&rhs_var) {
                        bv_model.bool_overrides.insert(rhs_var, false);
                    }
                }
                Sort::BitVec(_) => {
                    if !bv_model.values.contains_key(&rhs_var) {
                        bv_model.values.insert(rhs_var, BigInt::from(0));
                    }
                }
                _ => {}
            }
        }

        let mut recovered_vars = HashSet::default();
        let ptrace = ay_core::misc_cli_flags().phase_trace;
        // Shared evaluation memo for the WHOLE recovery pass: bv_model's maps only
        // GAIN leaf entries during recovery (the removals happen above).
        // Definition-owned array-read correction explicitly starts a fresh
        // cache scope before replacing stale compound read entries.
        let mut eval_memo = BvEvalMemo::default();
        // Lazily-built select index-value congruence (#abv-select-congruence):
        // constructed at most once per recovery (from the bit-blasted select
        // reads, whose values never change during recovery), only when some
        // substitution RHS actually carries a decoupled select.
        let mut select_congruence: Option<BvSelectCongruence> = None;

        // Topological (Kahn) recovery (#subst-recovery-toposort). A substitution
        // `from := to` is recoverable once every substitution-var its RHS `to`
        // depends on is itself recovered. The prior fixpoint re-traversed every
        // unresolved RHS EACH round — O(rounds x subs x term-size); a depth-N
        // dependency chain took N rounds (~40 rounds / ~223s of model extraction
        // on the aterm parser instance). Instead compute each RHS's blocking
        // substitution-var deps ONCE, then resolve in dependency order via a
        // ready-queue. Identical recovered values (whether a substitution recovers
        // depends only on WHETHER its deps are recovered, not the order — and
        // dependents are released only on SUCCESS, exactly as the fixpoint would),
        // in a single pass over the term forest.
        let sub_to: HashMap<TermId, TermId> = substitutions.iter().copied().collect();
        let mut array_reads = array_reads::Recovery::new(terms, &sub_to);
        let mut array_read_plans = HashMap::default();
        let mut pending: HashMap<TermId, usize> = HashMap::default();
        let mut dependents: HashMap<TermId, Vec<TermId>> = HashMap::default();
        let mut ready: Vec<TermId> = Vec::new();
        for &(from_var, to_var) in substitutions {
            // Array variables are reconstructed separately. Scalar reads must
            // nevertheless see their complete substitution definitions BEFORE
            // the original scalar assertions are validated.
            if matches!(terms.sort(from_var), Sort::Array(_)) {
                continue;
            }
            let mut deps: HashSet<TermId> = HashSet::default();
            if array_reads.enabled() {
                let Some(plan) = array_reads.plan(to_var, &mut deps) else {
                    continue;
                };
                array_read_plans.insert(from_var, plan);
            } else {
                let mut visited: HashSet<TermId> = HashSet::default();
                Self::collect_unrecovered_substitution_deps(
                    terms,
                    to_var,
                    &substitution_vars,
                    &mut deps,
                    &mut visited,
                );
            }
            deps.remove(&from_var); // a self-reference is not a blocking dep
            if deps.is_empty() {
                ready.push(from_var);
            } else {
                pending.insert(from_var, deps.len());
                for d in deps {
                    dependents.entry(d).or_default().push(from_var);
                }
            }
        }

        let mut recovered_count = 0usize;
        while let Some(from_var) = ready.pop() {
            let Some(&to_var) = sub_to.get(&from_var) else {
                continue;
            };
            if let Some(plan) = array_read_plans.get(&from_var) {
                if array_reads
                    .seed(plan, bv_model, &mut eval_memo, &substitution_vars)
                    .is_none()
                {
                    // A definition-owned read cannot fall back to decoupled
                    // original select bits when its interpretation is absent.
                    continue;
                }
            }
            let ok = Self::recover_one_substituted_value(
                terms,
                from_var,
                to_var,
                &substitution_vars,
                &recovered_vars,
                bv_model,
                &mut eval_memo,
                &mut select_congruence,
            );
            if !ok {
                // Genuinely unrecoverable (eval could not fold): leave its default
                // seed and DO NOT release dependents — exactly as the fixpoint left
                // it blocked.
                continue;
            }
            recovered_vars.insert(from_var);
            recovered_count += 1;
            if let Some(deps_on) = dependents.remove(&from_var) {
                for dependent in deps_on {
                    if let Some(p) = pending.get_mut(&dependent) {
                        *p = p.saturating_sub(1);
                        if *p == 0 {
                            ready.push(dependent);
                        }
                    }
                }
            }
        }
        if ptrace {
            eprintln!(
                "c phase-trace subst-recovery done recovered={} total={} took={:.1}s",
                recovered_count,
                substitutions.len(),
                _t_recover.elapsed().as_secs_f64(),
            );
        }
    }

    /// Collect into `deps` the substitution-vars (from `substitution_vars`) that
    /// `term` depends on — the blocking set for topological recovery. Mirrors
    /// [`Self::term_contains_unrecovered_substitution_var_inner`]'s traversal
    /// (Array-sorted substitution vars do NOT block; they route to the separate
    /// array-recovery path), but COLLECTS every dep in one visit instead of
    /// re-checking each round.
    fn collect_unrecovered_substitution_deps(
        terms: &TermStore,
        term: TermId,
        substitution_vars: &HashSet<TermId>,
        deps: &mut HashSet<TermId>,
        visited: &mut HashSet<TermId>,
    ) {
        if !visited.insert(term) {
            return;
        }
        match terms.get(term) {
            TermData::Var(_, _) => {
                if matches!(terms.sort(term), Sort::Array(_)) {
                    return;
                }
                if substitution_vars.contains(&term) {
                    deps.insert(term);
                }
            }
            TermData::Const(_) => {}
            TermData::App(_, args) => {
                for &arg in args {
                    Self::collect_unrecovered_substitution_deps(
                        terms,
                        arg,
                        substitution_vars,
                        deps,
                        visited,
                    );
                }
            }
            TermData::Not(inner) => {
                Self::collect_unrecovered_substitution_deps(
                    terms,
                    *inner,
                    substitution_vars,
                    deps,
                    visited,
                );
            }
            TermData::Ite(c, t, e) => {
                Self::collect_unrecovered_substitution_deps(
                    terms,
                    *c,
                    substitution_vars,
                    deps,
                    visited,
                );
                Self::collect_unrecovered_substitution_deps(
                    terms,
                    *t,
                    substitution_vars,
                    deps,
                    visited,
                );
                Self::collect_unrecovered_substitution_deps(
                    terms,
                    *e,
                    substitution_vars,
                    deps,
                    visited,
                );
            }
            TermData::Let(bindings, body) => {
                for (_, v) in bindings {
                    Self::collect_unrecovered_substitution_deps(
                        terms,
                        *v,
                        substitution_vars,
                        deps,
                        visited,
                    );
                }
                Self::collect_unrecovered_substitution_deps(
                    terms,
                    *body,
                    substitution_vars,
                    deps,
                    visited,
                );
            }
            TermData::Forall(_, body, triggers) | TermData::Exists(_, body, triggers) => {
                Self::collect_unrecovered_substitution_deps(
                    terms,
                    *body,
                    substitution_vars,
                    deps,
                    visited,
                );
                for &t in triggers.iter().flatten() {
                    Self::collect_unrecovered_substitution_deps(
                        terms,
                        t,
                        substitution_vars,
                        deps,
                        visited,
                    );
                }
            }
            _ => {}
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn recover_one_substituted_value(
        terms: &TermStore,
        from_var: TermId,
        to_var: TermId,
        substitution_vars: &HashSet<TermId>,
        recovered_vars: &HashSet<TermId>,
        bv_model: &mut BvModel,
        eval_memo: &mut BvEvalMemo,
        select_congruence: &mut Option<BvSelectCongruence>,
    ) -> bool {
        let has_unrecovered_substitution_target = Self::term_contains_unrecovered_substitution_var(
            terms,
            to_var,
            substitution_vars,
            recovered_vars,
        );

        if has_unrecovered_substitution_target {
            return false;
        }
        // For a PLAIN-Var target, the bit-blasted extracted value is
        // authoritative (there are no leaves to recompute), so the cached
        // shortcut is exact. `evaluate_bv_expr_with_bools` returns the very
        // same `values[to_var]` for a Var (see bv_eval.rs), so this is a
        // behavior-preserving fast path for that case only.
        if matches!(terms.get(to_var), TermData::Var(_, _)) {
            if let Some(value) = bv_model.values.get(&to_var).cloned() {
                bv_model.values.insert(from_var, value);
                return true;
            }
        }
        if let TermData::Const(ay_core::term::Constant::BitVec { value, .. }) = terms.get(to_var) {
            bv_model.values.insert(from_var, value.clone());
            return true;
        }
        // For a COMPOUND target (App/Ite/Not/Let/…) recompute the value
        // bottom-up from the now-recovered leaves. The stale cached bit-blast
        // value of a compound node can be decoupled from its leaves when the
        // defining equality was eliminated by VariableSubstitution and dropped
        // from the CNF; reading it directly would report a value inconsistent
        // with the definition and false-evaluate against the independent
        // validator. Recomputing yields the definitionally-entailed value.
        if let Some(value) = Self::evaluate_bv_expr_with_bools(
            terms,
            to_var,
            &bv_model.values,
            &bv_model.bool_overrides,
            eval_memo,
        ) {
            bv_model.values.insert(from_var, value);
            return true;
        }
        // #abv-select-congruence (wishlist#1): a select-over-Var-base whose
        // INDEX mentions substitution-eliminated variables is DECOUPLED from
        // the bit-blasted instance — the defining equalities that pinned the
        // index components were consumed by VariableSubstitution and dropped
        // from the CNF, so the select's own bit-blast bits (if any) are
        // unconstrained junk relative to the RECOVERED index value. Resolve
        // such reads by index-value congruence against the other bit-blasted
        // reads of the same array (exact: same array + same concrete index
        // ⇒ same value in the SAT-consistent bit-level model), then re-run
        // semantic evaluation with those reads seeded into the memo. When the
        // congruent value is missing or conflicted, FAIL CLOSED — leave the
        // variable unresolved rather than default it (the strict/independent
        // gates then reject the incomplete witness and `check_sat_guarded`
        // re-solves once without preprocessing, #abv-subst-model-retry).
        let decoupled_selects =
            Self::collect_decoupled_var_base_selects(terms, to_var, substitution_vars);
        if !decoupled_selects.is_empty() {
            let congruence = select_congruence.get_or_insert_with(|| {
                Self::build_bv_select_congruence(terms, bv_model, substitution_vars)
            });
            let mut all_reads_resolved = true;
            for &sel in &decoupled_selects {
                if eval_memo.bv.contains_key(&sel) {
                    continue;
                }
                let TermData::App(_, args) = terms.get(sel) else {
                    unreachable!("BUG: collected decoupled select is not an App");
                };
                let (base, idx) = (args[0], args[1]);
                let Some(idx_val) = Self::evaluate_bv_expr_with_bools(
                    terms,
                    idx,
                    &bv_model.values,
                    &bv_model.bool_overrides,
                    eval_memo,
                ) else {
                    all_reads_resolved = false;
                    continue;
                };
                match congruence.map.get(&(base, idx_val)) {
                    Some(Some(value)) => {
                        // Exact by congruence AND consistent with the array
                        // interpretation later extracted from the same reads.
                        eval_memo.bv.insert(sel, value.clone());
                    }
                    // Missing (no bit-blasted read at this index) or poisoned
                    // (conflicting same-index reads): fail closed.
                    _ => {
                        all_reads_resolved = false;
                    }
                }
            }
            if all_reads_resolved {
                if let Some(value) = Self::evaluate_bv_expr_with_bools(
                    terms,
                    to_var,
                    &bv_model.values,
                    &bv_model.bool_overrides,
                    eval_memo,
                ) {
                    bv_model.values.insert(from_var, value);
                    return true;
                }
                if *terms.sort(from_var) == Sort::Bool {
                    if let Some(bool_val) = Self::evaluate_bool_substitution(
                        terms,
                        to_var,
                        &bv_model.values,
                        &bv_model.bool_overrides,
                        eval_memo,
                    ) {
                        bv_model.bool_overrides.insert(from_var, bool_val);
                        return true;
                    }
                }
            }
            // FAIL CLOSED: never fall through to `to_var`'s stale bit-blast
            // value — for a decoupled-select RHS that stale value is exactly
            // the invalid-model manufactory this path exists to stop.
            return false;
        }
        // Cached fallback: reached only when semantic eval could not fold the
        // RHS (e.g. it carries an array select/store the BV evaluator does not
        // model). Preserve recovery for those array-carrying RHS forms exactly
        // as before, using the extracted bit-blast value. (RHS forms whose
        // select indices mention eliminated variables never reach here — they
        // take the fail-closed congruence path above.)
        if let Some(value) = bv_model.values.get(&to_var).cloned() {
            bv_model.values.insert(from_var, value);
            return true;
        }
        if *terms.sort(from_var) == Sort::Bool {
            if let TermData::Const(ay_core::term::Constant::Bool(b)) = terms.get(to_var) {
                bv_model.bool_overrides.insert(from_var, *b);
                return true;
            }
            if let Some(bool_val) = Self::evaluate_bool_substitution(
                terms,
                to_var,
                &bv_model.values,
                &bv_model.bool_overrides,
                eval_memo,
            ) {
                bv_model.bool_overrides.insert(from_var, bool_val);
                return true;
            }
        }

        false
    }

    /// Collect BV-sorted `(select <Var-base> idx)` subterms of `term` whose
    /// index subtree mentions at least one substitution-eliminated variable
    /// (#abv-select-congruence). These are exactly the reads decoupled from
    /// their bit-blasted instances by VariableSubstitution: post-substitution,
    /// every formula occurrence of the index was rewritten, so the ORIGINAL
    /// select term either has no bits at all or carries bits constrained only
    /// through free (eliminated-from-CNF) index components. Iterative walk
    /// with a visited set over the hash-consed DAG (no per-path re-visits).
    fn collect_decoupled_var_base_selects(
        terms: &TermStore,
        term: TermId,
        substitution_vars: &HashSet<TermId>,
    ) -> Vec<TermId> {
        let mut out = Vec::new();
        if substitution_vars.is_empty() {
            return out;
        }
        let mut visited: HashSet<TermId> = HashSet::default();
        let mut stack = vec![term];
        while let Some(t) = stack.pop() {
            if !visited.insert(t) {
                continue;
            }
            if let TermData::App(sym, args) = terms.get(t) {
                if sym.name() == "select"
                    && args.len() == 2
                    && matches!(terms.get(args[0]), TermData::Var(_, _))
                    && matches!(terms.sort(t), Sort::BitVec(_))
                    && Self::term_mentions_any_var(terms, args[1], substitution_vars)
                {
                    out.push(t);
                }
            }
            stack.extend(terms.children(t));
        }
        out
    }

    /// Whether `term`'s subtree contains any variable from `vars`.
    /// Visited-set DAG walk (see `collect_decoupled_var_base_selects`).
    fn term_mentions_any_var(terms: &TermStore, term: TermId, vars: &HashSet<TermId>) -> bool {
        let mut visited: HashSet<TermId> = HashSet::default();
        let mut stack = vec![term];
        while let Some(t) = stack.pop() {
            if !visited.insert(t) {
                continue;
            }
            if matches!(terms.get(t), TermData::Var(_, _)) && vars.contains(&t) {
                return true;
            }
            stack.extend(terms.children(t));
        }
        false
    }

    /// Build the select index-value congruence table from the bit-blasted
    /// reads recorded in `bv_model` (#abv-select-congruence). Index resolution
    /// mirrors `extract_array_model_from_bv_model` (model value first, then
    /// semantic evaluation), so a congruence-resolved read always agrees with
    /// the array interpretation later extracted from the same reads —
    /// including the exclusion of decoupled reads (index mentions an
    /// eliminated variable), whose bit-blast values are unconstrained junk on
    /// both paths. Two same-index reads with DIFFERENT values poison the entry
    /// (`None`): the eager FC/ROW axiom budget left them unlinked, so neither
    /// value is authoritative — callers must fail closed on a poisoned entry
    /// (#8510 applies the matching fail-closed rule at extraction).
    fn build_bv_select_congruence(
        terms: &TermStore,
        bv_model: &BvModel,
        substitution_vars: &HashSet<TermId>,
    ) -> BvSelectCongruence {
        let mut map: HashMap<(TermId, BigInt), Option<BigInt>> = HashMap::default();
        for (&term_id, elem_val) in &bv_model.values {
            let TermData::App(sym, args) = terms.get(term_id) else {
                continue;
            };
            if sym.name() != "select"
                || args.len() != 2
                || !matches!(terms.get(args[0]), TermData::Var(_, _))
                || !matches!(terms.sort(term_id), Sort::BitVec(_))
                || Self::term_mentions_any_var(terms, args[1], substitution_vars)
            {
                continue;
            }
            let Some(idx_val) = bv_model
                .values
                .get(&args[1])
                .cloned()
                .or_else(|| Self::evaluate_bv_expr(terms, args[1], &bv_model.values))
            else {
                continue;
            };
            map.entry((args[0], idx_val))
                .and_modify(|entry| {
                    if entry.as_ref() != Some(elem_val) {
                        *entry = None;
                    }
                })
                .or_insert_with(|| Some(elem_val.clone()));
        }
        BvSelectCongruence { map }
    }

    /// Per-call visited set: the term store is a hash-consed DAG; without it
    /// this walk is once-per-tree-PATH — exponential in sharing depth (the
    /// DAG→tree pathology; measured as the dominant cost of the phase-11
    /// recovery fixpoint on a 30M-clause BMC instance). Sound: `any`/`||`
    /// short-circuit on the first `true`, so a continued-past node evaluated
    /// `false`, which is fixed for the (term table, substitution_vars,
    /// recovered_vars) of THIS call. The set must not outlive the call —
    /// `recovered_vars` grows across the recovery fixpoint.
    fn term_contains_unrecovered_substitution_var(
        terms: &TermStore,
        term: TermId,
        substitution_vars: &HashSet<TermId>,
        recovered_vars: &HashSet<TermId>,
    ) -> bool {
        let mut visited: HashSet<TermId> = HashSet::default();
        Self::term_contains_unrecovered_substitution_var_inner(
            terms,
            term,
            substitution_vars,
            recovered_vars,
            &mut visited,
        )
    }

    fn term_contains_unrecovered_substitution_var_inner(
        terms: &TermStore,
        term: TermId,
        substitution_vars: &HashSet<TermId>,
        recovered_vars: &HashSet<TermId>,
        visited: &mut HashSet<TermId>,
    ) -> bool {
        if !visited.insert(term) {
            return false;
        }
        match terms.get(term) {
            TermData::Var(_, _) => {
                // ARRAY substitution vars are never recovered by BV recovery —
                // they route to the separate `array_substitutions` path — so a
                // BV var whose definition READS THROUGH such an array (e.g. a
                // lifted `(_ extract .. (select (store fld_data ..) ..))`) would
                // be treated as permanently "unrecovered" and default to a
                // decoupled 0, false-evaluating against its ROW definition
                // (#g4-array-subst-var, the follow-on the 92f4f142 fix left on
                // its carries-an-array-select/store path). A read through the
                // array is resolved by the select-over-store ROW fold in
                // `evaluate_bv_expr_with_bools`, or falls back to the committed
                // bit-blast value; so an Array subst var does NOT block recovery.
                if matches!(terms.sort(term), Sort::Array(_)) {
                    return false;
                }
                substitution_vars.contains(&term) && !recovered_vars.contains(&term)
            }
            TermData::Const(_) => false,
            TermData::App(_, args) => args.iter().any(|&arg| {
                Self::term_contains_unrecovered_substitution_var_inner(
                    terms,
                    arg,
                    substitution_vars,
                    recovered_vars,
                    visited,
                )
            }),
            TermData::Not(inner) => Self::term_contains_unrecovered_substitution_var_inner(
                terms,
                *inner,
                substitution_vars,
                recovered_vars,
                visited,
            ),
            TermData::Ite(c, t, e) => {
                Self::term_contains_unrecovered_substitution_var_inner(
                    terms,
                    *c,
                    substitution_vars,
                    recovered_vars,
                    visited,
                ) || Self::term_contains_unrecovered_substitution_var_inner(
                    terms,
                    *t,
                    substitution_vars,
                    recovered_vars,
                    visited,
                ) || Self::term_contains_unrecovered_substitution_var_inner(
                    terms,
                    *e,
                    substitution_vars,
                    recovered_vars,
                    visited,
                )
            }
            TermData::Let(bindings, body) => {
                bindings.iter().any(|(_, t)| {
                    Self::term_contains_unrecovered_substitution_var_inner(
                        terms,
                        *t,
                        substitution_vars,
                        recovered_vars,
                        visited,
                    )
                }) || Self::term_contains_unrecovered_substitution_var_inner(
                    terms,
                    *body,
                    substitution_vars,
                    recovered_vars,
                    visited,
                )
            }
            TermData::Forall(_, body, triggers) | TermData::Exists(_, body, triggers) => {
                Self::term_contains_unrecovered_substitution_var_inner(
                    terms,
                    *body,
                    substitution_vars,
                    recovered_vars,
                    visited,
                ) || triggers.iter().flatten().any(|&t| {
                    Self::term_contains_unrecovered_substitution_var_inner(
                        terms,
                        t,
                        substitution_vars,
                        recovered_vars,
                        visited,
                    )
                })
            }
            other => {
                unreachable!(
                    "unhandled TermData variant in term_contains_unrecovered_substitution_var(): {other:?}"
                )
            }
        }
    }

    /// Collect leaf variables referenced by a substitution RHS expression.
    ///
    /// Used by `recover_substituted_bv_bool_values` to seed default values
    /// for representatives left unconstrained after variable substitution
    /// (#3201 precedent in the LIA lane).
    /// `visited` dedups interior nodes across the hash-consed term DAG (and
    /// across sibling calls sharing one `visited`): without it the walk is
    /// once-per-tree-PATH — exponential in sharing depth. Context-free, so a
    /// visited subterm's vars are already in `vars`.
    fn collect_substitution_rhs_vars(
        terms: &TermStore,
        term: TermId,
        vars: &mut HashSet<TermId>,
        visited: &mut HashSet<TermId>,
    ) {
        if !visited.insert(term) {
            return;
        }
        match terms.get(term) {
            TermData::Var(_, _) => {
                vars.insert(term);
            }
            TermData::Const(_) => {}
            TermData::App(_, args) => {
                for &arg in args {
                    Self::collect_substitution_rhs_vars(terms, arg, vars, visited);
                }
            }
            TermData::Not(inner) => {
                Self::collect_substitution_rhs_vars(terms, *inner, vars, visited);
            }
            TermData::Ite(cond, then_t, else_t) => {
                Self::collect_substitution_rhs_vars(terms, *cond, vars, visited);
                Self::collect_substitution_rhs_vars(terms, *then_t, vars, visited);
                Self::collect_substitution_rhs_vars(terms, *else_t, vars, visited);
            }
            TermData::Let(bindings, body) => {
                for (_, bound) in bindings {
                    Self::collect_substitution_rhs_vars(terms, *bound, vars, visited);
                }
                Self::collect_substitution_rhs_vars(terms, *body, vars, visited);
            }
            // Quantified bodies reference bound variables that must not be
            // seeded; substitution RHS terms are quantifier-free in practice.
            TermData::Forall(_, _, _) | TermData::Exists(_, _, _) => {}
            _ => {}
        }
    }

    fn model_bool_value(terms: &TermStore, bv_model: &BvModel, term: TermId) -> Option<bool> {
        // Local memo: one-shot evaluation, fixed env for its duration.
        let mut memo = BvEvalMemo::default();
        Self::model_bool_value_memo(terms, bv_model, term, &mut memo)
    }

    /// Whether `term` is definitely FALSE under the BV model, decided
    /// STRUCTURALLY through `and`/`or`/`not` so one false conjunct settles a
    /// conjunction whose siblings are not evaluable at all.
    ///
    /// `model_bool_value` propagates `None` out of `and` as soon as any operand
    /// is unevaluable. That is the right answer to "what is this term's value",
    /// but too weak for "can this arm still be satisfied": the arms this is
    /// asked about are hundred-conjunct BMC blocks that always contain an array
    /// equality, which the BV model cannot evaluate, so the whole arm would come
    /// back `None` even when a scalar conjunct already falsifies it.
    ///
    /// One-sided by construction: `true` means "false in this model", `false`
    /// means only "not known to be false" — never "known true". Callers may
    /// therefore treat a `true` answer as a refutation and must treat `false`
    /// as no information.
    fn model_bool_is_false(
        terms: &TermStore,
        bv_model: &BvModel,
        term: TermId,
        depth: usize,
        memo: &mut BvEvalMemo,
        cache: &mut HashMap<TermId, bool>,
    ) -> bool {
        const MAX_DEPTH: usize = 256;
        if depth >= MAX_DEPTH {
            return false;
        }
        if let Some(&known) = cache.get(&term) {
            return known;
        }
        let decided = match terms.get(term) {
            TermData::App(sym, args) if *terms.sort(term) == Sort::Bool => match sym.name() {
                // False as soon as ANY conjunct is false, whatever the rest do.
                "and" => args.iter().any(|&arg| {
                    Self::model_bool_is_false(terms, bv_model, arg, depth + 1, memo, cache)
                }),
                // False only when EVERY disjunct is false.
                "or" => {
                    !args.is_empty()
                        && args.iter().all(|&arg| {
                            Self::model_bool_is_false(terms, bv_model, arg, depth + 1, memo, cache)
                        })
                }
                _ => Self::model_bool_value_memo(terms, bv_model, term, memo) == Some(false),
            },
            // A negated atom is false when the atom is true, read from the same
            // source as a bare atom arm (`bool_overrides`, then evaluation). A
            // Bool-element `select` is a SAT atom with no BV bits, so evaluating
            // the `not` alone never sees its value.
            TermData::Not(inner) => {
                Self::model_bool_value_memo(terms, bv_model, term, memo) == Some(false)
                    || Self::model_bool_value_memo(terms, bv_model, *inner, memo) == Some(true)
            }
            _ => Self::model_bool_value_memo(terms, bv_model, term, memo) == Some(false),
        };
        cache.insert(term, decided);
        decided
    }

    /// [`Self::model_bool_value`] against a caller-owned evaluation memo, so a
    /// scan over many sibling terms shares one memo instead of rebuilding it per
    /// term. The memo caches only `Some` results and the environment is fixed
    /// for its lifetime, so sharing cannot change any answer.
    fn model_bool_value_memo(
        terms: &TermStore,
        bv_model: &BvModel,
        term: TermId,
        memo: &mut BvEvalMemo,
    ) -> Option<bool> {
        if *terms.sort(term) != Sort::Bool {
            return None;
        }
        bv_model.bool_overrides.get(&term).copied().or_else(|| {
            Self::evaluate_bool_substitution(
                terms,
                term,
                &bv_model.values,
                &bv_model.bool_overrides,
                memo,
            )
        })
    }

    fn model_bv1_value(terms: &TermStore, bv_model: &BvModel, term: TermId) -> Option<bool> {
        if !matches!(terms.sort(term), Sort::BitVec(bv) if bv.width == 1) {
            return None;
        }
        bv_model
            .values
            .get(&term)
            .cloned()
            .or_else(|| Self::evaluate_bv_expr(terms, term, &bv_model.values))
            .map(|value| (value & BigInt::from(1u8)) == BigInt::from(1u8))
    }
}

#[cfg(test)]
#[path = "bv_model_tests.rs"]
mod tests;

#[cfg(test)]
#[path = "bv_model_store_tests.rs"]
mod store_tests;
