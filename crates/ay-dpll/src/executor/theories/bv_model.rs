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
        // GAIN entries during recovery (the removals happen above, before any
        // evaluation), so cached Some results stay correct - see `BvEvalMemo`.
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
        let mut pending: HashMap<TermId, usize> = HashMap::default();
        let mut dependents: HashMap<TermId, Vec<TermId>> = HashMap::default();
        let mut ready: Vec<TermId> = Vec::new();
        for &(from_var, to_var) in substitutions {
            let mut deps: HashSet<TermId> = HashSet::default();
            let mut visited: HashSet<TermId> = HashSet::default();
            Self::collect_unrecovered_substitution_deps(
                terms,
                to_var,
                &substitution_vars,
                &mut deps,
                &mut visited,
            );
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

    /// Extract array model from BV model for QF_ABV/QF_AUFBV (#5449).
    ///
    /// Scans bit-blasted select terms in the BV model to recover concrete
    /// index-value mappings for each root array variable. Without this,
    /// array models default to `((as const ...) 0)`.
    ///
    /// Also scans assertions for `(= array_var (store ...))` patterns to
    /// populate models for array variables defined by store chains. After
    /// variable substitution, selects on such variables are rewritten to
    /// selects on the store chain, so the select-scan alone misses them.
    pub(in crate::executor) fn extract_array_model_from_bv_model(
        terms: &TermStore,
        bv_model: &BvModel,
        assertions: &[TermId],
        substituted_vars: &HashSet<TermId>,
    ) -> ArrayModel {
        use num_bigint::BigInt;

        // Group select(array_var, index) terms by array variable.
        // Only collect selects where the array arg is a variable (Var), NOT a
        // store chain. Selects through stores give the post-store value, not the
        // root array's value — collecting them would cause non-deterministic
        // model output when a direct select and a store-chain select at the same
        // index map to the same root with different values.
        // ROW2 axioms ensure that store-chain selects at non-matching indices
        // have corresponding direct selects from the root array.
        //
        // #abv-select-congruence (wishlist#1): selects whose INDEX mentions a
        // substitution-eliminated variable are excluded. Their bit-blast values
        // are decoupled junk (the index components are free in the CNF), so a
        // pair derived from them either plants a garbage store entry at an
        // arbitrary index or #8510-conflicts with the authoritative
        // post-substitution read of the same array — masking a pinned read
        // with the default. The post-substitution counterpart of every such
        // read is present in the model and supplies the authoritative pair.
        let mut selects_by_array: HashMap<TermId, Vec<(TermId, TermId)>> = HashMap::default();
        // Memoized per index TERM: many selects share hash-consed index terms
        // on BMC instances, so the walk runs once per distinct index.
        let mut decoupled_memo: HashMap<TermId, bool> = HashMap::default();
        let mut decoupled = |idx: TermId| {
            !substituted_vars.is_empty()
                && *decoupled_memo
                    .entry(idx)
                    .or_insert_with(|| Self::term_mentions_any_var(terms, idx, substituted_vars))
        };

        // Scan BV-sorted select terms from bv_model.values
        for &term_id in bv_model.values.keys() {
            if let TermData::App(sym, args) = terms.get(term_id) {
                if sym.name() == "select"
                    && args.len() == 2
                    && matches!(terms.get(args[0]), TermData::Var(_, _))
                    && !decoupled(args[1])
                {
                    selects_by_array
                        .entry(args[0])
                        .or_default()
                        .push((args[1], term_id));
                }
            }
        }

        // #6047: Also scan Bool-sorted select terms from bool_overrides.
        // Arrays like (Array BV32 Bool) have Bool-element selects whose values
        // are in the SAT assignment (seeded into bool_overrides), not bv_model.values.
        // Without this, (Array BV Bool) arrays get default const(false) models
        // even when select(arr, idx) is asserted true.
        for &term_id in bv_model.bool_overrides.keys() {
            if let TermData::App(sym, args) = terms.get(term_id) {
                if sym.name() == "select"
                    && args.len() == 2
                    && matches!(terms.get(args[0]), TermData::Var(_, _))
                    && !decoupled(args[1])
                {
                    selects_by_array
                        .entry(args[0])
                        .or_default()
                        .push((args[1], term_id));
                }
            }
        }

        let mut array_values = HashMap::default();
        for (root_id, selects) in &selects_by_array {
            let Sort::Array(arr_sort) = terms.sort(*root_id) else {
                continue;
            };
            let Sort::BitVec(idx_bv) = &arr_sort.index_sort else {
                continue;
            };
            let idx_width = idx_bv.width;

            // Element sort determines how to format the default and store values.
            // (Array BV BV) → bitvec default/values
            // (Array BV Bool) → "false"/"true" default/values
            let (default_val, is_bool_elem) = match &arr_sort.element_sort {
                Sort::BitVec(elem_bv) => (format_bitvec(&BigInt::from(0u64), elem_bv.width), false),
                Sort::Bool => ("false".to_string(), true),
                _ => continue,
            };

            let mut interp = ArrayInterpretation {
                index_sort: Some(arr_sort.index_sort.clone()),
                element_sort: Some(arr_sort.element_sort.clone()),
                default: Some(default_val),
                ..Default::default()
            };

            // Collect ALL (index, value) pairs, detecting conflicts (#8510).
            //
            // Multiple select terms at the same array index can have different
            // BV model values. This happens when the array axiom fixpoint or
            // FC axiom generation creates new select terms with fresh
            // unconstrained bits, while the original select term (from an
            // assertion like `(= #x00 (select arr idx))`) has constrained bits.
            //
            // HashMap iteration order is non-deterministic, so the first-seen
            // select term at any index may be the unconstrained one with
            // arbitrary bit values. When values conflict at an index, we remove
            // the store entry entirely and let the default value (typically
            // `#x00`) apply via `lookup_array_model`. This prevents false SAT
            // on QF_ABV benchmarks like csplit-query where ~2000 constant
            // selects share indices with FC-generated selects.
            let mut index_to_value: HashMap<String, String> = HashMap::default();
            let mut conflicted_indices: HashSet<String> = HashSet::default();

            for &(idx_id, sel_id) in selects {
                let idx_val = bv_model
                    .values
                    .get(&idx_id)
                    .cloned()
                    .or_else(|| Self::evaluate_bv_expr(terms, idx_id, &bv_model.values));

                // Element value: from BV model for BV elements, bool_overrides for Bool elements
                let elem_str = if is_bool_elem {
                    bv_model
                        .bool_overrides
                        .get(&sel_id)
                        .map(|&b| if b { "true" } else { "false" }.to_string())
                } else {
                    bv_model
                        .values
                        .get(&sel_id)
                        .cloned()
                        .or_else(|| Self::evaluate_bv_expr(terms, sel_id, &bv_model.values))
                        .map(|ev| {
                            let Sort::BitVec(elem_bv) = &arr_sort.element_sort else {
                                unreachable!(
                                    "BUG: BV array element sort is not BitVec in model extraction"
                                );
                            };
                            format_bitvec(&ev, elem_bv.width)
                        })
                };

                if let (Some(ref iv), Some(ref ev_str)) = (idx_val, &elem_str) {
                    let idx_str = format_bitvec(iv, idx_width);
                    match index_to_value.get(&idx_str) {
                        None => {
                            index_to_value.insert(idx_str, ev_str.clone());
                        }
                        Some(existing_val) if existing_val != ev_str => {
                            // Conflict: different select terms at the same index
                            // have different BV model values. One is constrained
                            // by an assertion, the other has unconstrained bits.
                            // Remove this index from the store so the default
                            // applies, avoiding non-deterministic wrong models.
                            conflicted_indices.insert(idx_str);
                        }
                        Some(_) => {
                            // Same value: no conflict, keep the existing entry
                        }
                    }
                }
            }

            // Build store entries, excluding conflicted indices
            for (idx_str, val_str) in index_to_value {
                if !conflicted_indices.contains(&idx_str) {
                    interp.stores.push((idx_str, val_str));
                }
            }

            array_values.insert(*root_id, interp);
        }

        // #8512: Scan assertions for `(= array_var (store ...))` patterns to
        // populate models for array variables defined by store chains.
        //
        // After variable substitution, `select(b, idx)` is rewritten to
        // `select(store(a, i, v), idx)`, then `expand_select_store` may
        // eliminate the select entirely (replacing it with an ITE or constant).
        // When assertions are restored before model extraction, the original
        // `(= b (store a #x01 #x42))` is present but `b` has no select terms
        // in the BV model. Walking the store chain and resolving index/value
        // pairs from the BV model fills the gap.
        //
        // This is needed for EXTERNAL_CODEGEN GPU/memory semantic encoding where array
        // variables represent memory states connected by store chains.
        let store_chain_populated =
            Self::populate_store_chain_array_models(terms, bv_model, assertions, &mut array_values);

        // #array-def-equality: an array variable asserted equal — transitively
        // through `(= x y)` chains — to a const-array or store chain must adopt
        // that AUTHORITATIVE interpretation, even when select-derived extraction
        // gave it a divergent entry from orphaned/skolem `select` terms. Two
        // datatype-field arrays asserted equal but reconstructed independently
        // (e.g. `(= s!fld_data t!fld_osc_data!fld_data)`, one resolving via its
        // definition to `(const-array #xff)`, the other carrying a garbage
        // select-derived entry) otherwise disagree, and the strict array oracle
        // refutes the asserted equality — demoting a genuine model to `unknown`.
        //
        // Sound: the definitional equality is an assertion (ground truth in every
        // model), so overwriting with the definition's value can only make the
        // reported interpretation match what the formula already requires; any
        // OTHER assertion the definite value violates still fails its own oracle
        // check. Pure var↔var equalities with no const/store ground reachable are
        // deliberately left untouched, so genuinely spurious models (where the
        // bit-blaster left two asserted-equal arrays inconsistent) are still
        // refuted by comparing their independent entries.
        Self::propagate_definitional_array_equalities(
            terms,
            bv_model,
            assertions,
            &mut array_values,
        );

        // #8512-nested-def: an array variable whose ONLY definition is a
        // store-chain / const-array equality nested inside `or`/`ite`/`not`
        // cannot adopt that definition — a conditional equality is not
        // unconditionally asserted, so applying it would fabricate a value.
        // But the select-derived interpretation we DO have for such a variable
        // is knowingly PARTIAL (the defining stores were never scanned), and
        // publishing it as a total array makes every missing index read back as
        // the array's `default`. That is a positive claim, not "unknown", so a
        // store-chain equality over a missing index evaluates FALSE and the
        // independent gate reports a MODEL VIOLATION for a model that is merely
        // incomplete — fail-closing a correct `sat` to `unknown`.
        //
        // Declare the interpretation partial instead. `ArrayModel::read_conflicted`
        // is the established channel (`array_from_model` refuses a listed term as
        // evidence for a total array and the leaf becomes unevaluable), so the
        // gate reports an honest coverage gap rather than a false violation.
        //
        // #8512-forced-or: withholding is only the right answer while the store
        // set really is incomplete. When the model FORCES the arm the definition
        // sits in (every sibling disjunct is false), the chain was walked and
        // every (index, value) pair resolved concretely, so the interpretation
        // covers each index the definition constrains and is no longer partial —
        // keeping it withheld would cost a provable `sat` for nothing.
        //
        // A variable is released only if its store-chain BASE is not itself a
        // nested-only definition: the chain inherits the base's entries for the
        // indices it does not overwrite, so an unresolved base leaves the same
        // hole one level down. That test reads the ORIGINAL nested set, not the
        // set being edited, so the outcome does not depend on iteration order.
        let nested_only = Self::array_vars_defined_only_under_nested_equality(terms, assertions);
        let mut read_conflicted = nested_only.clone();
        for (var, base) in &store_chain_populated {
            if !nested_only.contains(base) {
                read_conflicted.remove(var);
            }
        }

        // Both fields listed exhaustively, no `..Default::default()`: if a third
        // field is ever added to `ArrayModel` this builder must make a decision
        // about it rather than silently inherit a default — the entire bug this
        // code path exists for was a silent default standing in for "unknown".
        ArrayModel {
            array_values,
            read_conflicted,
        }
    }

    /// Array variables that appear in a store-chain / const-array defining
    /// equality ONLY at a nested (non-top-level, non-top-level-`and`) position.
    ///
    /// `propagate_definitional_array_equalities` scans top-level `=` assertions
    /// only, so these variables never receive their authoritative interpretation
    /// and keep a partial select-derived one. Listing them as read-conflicted is
    /// the sound response: it withholds totality without inventing a value.
    fn array_vars_defined_only_under_nested_equality(
        terms: &TermStore,
        assertions: &[TermId],
    ) -> HashSet<TermId> {
        fn is_array_ground_def(terms: &TermStore, t: TermId) -> bool {
            matches!(terms.get(t), TermData::App(sym, _)
                if sym.name() == "store" || sym.name() == "const-array")
        }
        // Definitions reachable unconditionally: top level, or a conjunct of a
        // top-level `and`. These ARE applied elsewhere, so exclude them.
        let mut unconditional: HashSet<TermId> = HashSet::default();
        let mut top: Vec<TermId> = assertions.to_vec();
        while let Some(t) = top.pop() {
            match terms.get(t) {
                TermData::App(sym, args) if sym.name() == "and" => top.extend(args.iter().copied()),
                TermData::App(sym, args) if sym.name() == "=" && args.len() == 2 => {
                    for (a, b) in [(args[0], args[1]), (args[1], args[0])] {
                        if matches!(terms.get(a), TermData::Var(_, _))
                            && matches!(terms.sort(a), Sort::Array(_))
                            && is_array_ground_def(terms, b)
                        {
                            unconditional.insert(a);
                        }
                    }
                }
                _ => {}
            }
        }
        // Every array-var store-chain definition anywhere in the formula.
        let mut nested: HashSet<TermId> = HashSet::default();
        let mut stack: Vec<TermId> = assertions.to_vec();
        let mut seen: HashSet<TermId> = HashSet::default();
        while let Some(t) = stack.pop() {
            if !seen.insert(t) {
                continue;
            }
            match terms.get(t) {
                TermData::App(sym, args) => {
                    if sym.name() == "=" && args.len() == 2 {
                        for (a, b) in [(args[0], args[1]), (args[1], args[0])] {
                            if matches!(terms.get(a), TermData::Var(_, _))
                                && matches!(terms.sort(a), Sort::Array(_))
                                && is_array_ground_def(terms, b)
                                && !unconditional.contains(&a)
                            {
                                nested.insert(a);
                            }
                        }
                    }
                    stack.extend(args.iter().copied());
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, x, y) => {
                    stack.push(*c);
                    stack.push(*x);
                    stack.push(*y);
                }
                _ => {}
            }
        }
        nested
    }

    /// Overwrite array-variable interpretations with the authoritative
    /// interpretation implied by a const-array / store-chain definitional
    /// equality reachable through asserted `(= x y)` chains. See the call site
    /// in [`Self::extract_array_model_from_bv_model`] for the rationale and the
    /// soundness argument. (#array-def-equality)
    fn propagate_definitional_array_equalities(
        terms: &TermStore,
        bv_model: &BvModel,
        assertions: &[TermId],
        array_values: &mut HashMap<TermId, ArrayInterpretation>,
    ) {
        // Collect every array variable that appears in an asserted array
        // equality — those are the only ones a definition can speak to.
        let mut def_vars: Vec<TermId> = Vec::new();
        for &assertion in assertions {
            if let TermData::App(sym, args) = terms.get(assertion) {
                if sym.name() == "=" && args.len() == 2 {
                    for &side in &[args[0], args[1]] {
                        if matches!(terms.get(side), TermData::Var(_, _))
                            && matches!(terms.sort(side), Sort::Array(_))
                        {
                            def_vars.push(side);
                        }
                    }
                }
            }
        }
        def_vars.sort_by_key(|t| t.0);
        def_vars.dedup();

        for v in def_vars {
            let interp = {
                let mut visited = HashSet::default();
                Self::resolve_authoritative_array_interp(
                    terms,
                    bv_model,
                    assertions,
                    array_values,
                    v,
                    &mut visited,
                )
            };
            if let Some(interp) = interp {
                array_values.insert(v, interp);
            }
        }
    }

    /// Resolve an array variable to the AUTHORITATIVE interpretation implied by
    /// a const-array / store-chain definitional equality in `assertions`,
    /// following var→var definitional equalities transitively. Returns `None`
    /// when no const/store ground definition is reachable (the `visited` set
    /// breaks var↔var cycles), so the caller leaves the existing entry intact.
    fn resolve_authoritative_array_interp(
        terms: &TermStore,
        bv_model: &BvModel,
        assertions: &[TermId],
        array_values: &HashMap<TermId, ArrayInterpretation>,
        var: TermId,
        visited: &mut HashSet<TermId>,
    ) -> Option<ArrayInterpretation> {
        if !visited.insert(var) {
            return None;
        }
        for &assertion in assertions {
            let TermData::App(sym, args) = terms.get(assertion) else {
                continue;
            };
            if sym.name() != "=" || args.len() != 2 {
                continue;
            }
            let (lhs, rhs) = (args[0], args[1]);
            let other = if lhs == var {
                rhs
            } else if rhs == var {
                lhs
            } else {
                continue;
            };
            match terms.get(other) {
                TermData::App(s, a) if s.name() == "const-array" && a.len() == 1 => {
                    if let Some(interp) = Self::const_array_interp(terms, bv_model, other, a[0]) {
                        return Some(interp);
                    }
                }
                TermData::App(s, a) if s.name() == "store" && a.len() == 3 => {
                    if let Some(interp) =
                        Self::build_store_chain_interp(terms, bv_model, other, array_values)
                    {
                        return Some(interp);
                    }
                }
                TermData::Var(_, _) if matches!(terms.sort(other), Sort::Array(_)) => {
                    if let Some(interp) = Self::resolve_authoritative_array_interp(
                        terms,
                        bv_model,
                        assertions,
                        array_values,
                        other,
                        visited,
                    ) {
                        return Some(interp);
                    }
                }
                _ => {}
            }
        }
        None
    }

    /// Build the interpretation of a `(const-array default)` term: a default
    /// value (resolved through `bv_model`) and no stores. Returns `None` for
    /// non-BitVec-indexed or unsupported element sorts.
    fn const_array_interp(
        terms: &TermStore,
        bv_model: &BvModel,
        const_array_term: TermId,
        default_term: TermId,
    ) -> Option<ArrayInterpretation> {
        let Sort::Array(arr_sort) = terms.sort(const_array_term) else {
            return None;
        };
        if !matches!(arr_sort.index_sort, Sort::BitVec(_)) {
            return None;
        }
        let default = match &arr_sort.element_sort {
            Sort::BitVec(elem_bv) => {
                let value =
                    bv_model.values.get(&default_term).cloned().or_else(|| {
                        Self::evaluate_bv_expr(terms, default_term, &bv_model.values)
                    })?;
                format_bitvec(&value, elem_bv.width)
            }
            Sort::Bool => {
                let b = bv_model.bool_overrides.get(&default_term).copied()?;
                if b { "true" } else { "false" }.to_string()
            }
            _ => return None,
        };
        Some(ArrayInterpretation {
            index_sort: Some(arr_sort.index_sort.clone()),
            element_sort: Some(arr_sort.element_sort.clone()),
            default: Some(default),
            ..Default::default()
        })
    }

    /// Add array-model entries for array variables eliminated by variable substitution.
    ///
    /// QF_ABV preprocessing can rewrite `(= arr2 arr1)` by substituting
    /// `arr2 -> arr1`. The SAT/BV model is then built over the post-substitution
    /// terms, while validation runs over restored original assertions. Copying
    /// the resolved array interpretation back to substituted variables prevents
    /// strict validation from treating model-completion defaults as concrete
    /// counterexamples.
    ///
    /// The substitution *target* `to_term` is frequently a `store` chain rather
    /// than another array variable — e.g. `(= a2 (store a 0 5))` and `(= b a2)`
    /// both collapse to `b, a2 -> store(a, 0, 5)`. The store term has no
    /// `array_values` entry of its own (only variables that appear in select
    /// terms or in explicit `(= var store)` assertions get one), so a flat
    /// `array_values[to_term]` lookup misses it and the eliminated variables
    /// keep whatever stale select-derived entry their now-orphaned `select`
    /// terms produced (unconstrained bits → garbage). Because both `b` and `a2`
    /// alias the *same* store term, that left two asserted-equal arrays with
    /// divergent interpretations, which the strict array oracle then refuted —
    /// demoting a genuine SAT to `unknown`. Building the store-chain
    /// interpretation for such targets gives every variable aliasing the same
    /// target one identical, consistent interpretation. (#array-subst-store-target)
    pub(in crate::executor) fn populate_array_models_from_substitutions(
        terms: &TermStore,
        bv_model: &BvModel,
        substitutions: &[(TermId, TermId)],
        array_values: &mut HashMap<TermId, ArrayInterpretation>,
    ) {
        if substitutions.is_empty() {
            return;
        }

        // Fixpoint over the chain length so transitive substitutions
        // (`a2 -> b`, `b -> store(...)`) all resolve to the final target.
        for _ in 0..substitutions.len() {
            for &(from_var, to_term) in substitutions {
                if !matches!(terms.sort(from_var), Sort::Array(_)) {
                    continue;
                }
                let Some(interp) = Self::resolve_substitution_target_interp(
                    terms,
                    bv_model,
                    to_term,
                    array_values,
                ) else {
                    continue;
                };
                array_values.insert(from_var, interp);
            }
        }
    }

    /// Resolve the array interpretation of a substitution *target* term.
    ///
    /// Prefers an existing `array_values` entry; otherwise, when the target is
    /// a `store` chain, builds the interpretation by walking the chain against
    /// `bv_model` (see [`Self::build_store_chain_interp`]). Returns `None` for
    /// targets that are neither (e.g. a bare base variable with no entry), so
    /// the caller leaves the eliminated variable's existing entry untouched.
    fn resolve_substitution_target_interp(
        terms: &TermStore,
        bv_model: &BvModel,
        to_term: TermId,
        array_values: &HashMap<TermId, ArrayInterpretation>,
    ) -> Option<ArrayInterpretation> {
        if let Some(interp) = array_values.get(&to_term) {
            return Some(interp.clone());
        }
        Self::build_store_chain_interp(terms, bv_model, to_term, array_values)
    }

    /// Resolve the model value of a store-chain index or value operand.
    ///
    /// For a LEAF (`Var`/`Const`) the bit-blaster's own assignment is the model,
    /// so `bv_model.values` is authoritative. For a COMPOUND term the value is a
    /// FUNCTION of its leaves, and computing it from them is authoritative
    /// instead — a cached entry for an interior node is not.
    ///
    /// #store-chain-dead-node: preferring the cached entry for a compound term
    /// committed FABRICATED array cells. Preprocessing substitutes
    /// `(= x #x00000007)` into `(bvadd x y)`, the folded node is never
    /// constrained, and its bits read back all-zero — so `(store a i (bvadd x y))`
    /// was extracted as `a[i] = #x00000000` while the true value is `#x0000000a`.
    /// The independent gate then found the definition-derived candidate
    /// disagreeing with the extracted interpretation, tainted the target AND —
    /// through completion's taint propagation — the innocent store BASE, leaving
    /// both `read_conflicted`. `array_from_model` refuses a read-conflicted term,
    /// so the base became unresolvable, the defining store expression could not
    /// be evaluated, and a trivially satisfiable query was reported
    /// `unknown: model does not pin this leaf`. This is the whole reason a
    /// `store` of any COMPUTED value (`bvadd` as much as `bvsdiv`) degraded, and
    /// why a store of a bare variable did not.
    ///
    /// SOUND, and fail-closed in both directions. The computed value is exactly
    /// what the model's own leaf assignments entail, and the gate still re-checks
    /// every authored assertion against whatever is committed, so a wrong cell can
    /// only produce `ModelViolates` (a downgrade to `unknown`), never a
    /// confirmation. Declining to guess is equally safe: an omitted cell leaves
    /// the chain INCOMPLETE, which is the honest report — the caller already
    /// treats an incompletely-resolved chain as one that may not be published as
    /// a total array — and the definitional-equality path then supplies the cell
    /// from the definition itself, with no conflict to taint.
    fn store_chain_operand_value(
        terms: &TermStore,
        bv_model: &BvModel,
        t: TermId,
    ) -> Option<BigInt> {
        if matches!(terms.get(t), TermData::Var(_, _) | TermData::Const(_)) {
            return bv_model
                .values
                .get(&t)
                .cloned()
                .or_else(|| Self::evaluate_bv_expr(terms, t, &bv_model.values));
        }
        // COMPOUND term: computed or nothing. `evaluate_bv_expr` models every BV
        // operator, `ite`, and the ROW `select`-over-`store` fold, so it returns
        // `None` only when the value genuinely depends on something this BV-level
        // view cannot see — in practice a `select` on an array VARIABLE, whose
        // contents live in the array model. That is precisely the case in which
        // the cached interior-node entry is least trustworthy, so falling back to
        // it FABRICATES a cell rather than recovering one.
        Self::evaluate_bv_expr(terms, t, &bv_model.values)
    }

    /// Build an [`ArrayInterpretation`] for a `store` chain term by resolving
    /// each stored (index, value) pair through `bv_model` and inheriting the
    /// base array's entry for indices the chain does not overwrite.
    ///
    /// Mirrors the per-variable logic in
    /// [`Self::populate_store_chain_array_models`] but is keyed on an arbitrary
    /// store *term* rather than a `(= var store)` assertion, so it can supply
    /// interpretations for substitution targets that never appear as the named
    /// side of a defining equality. Returns `None` when `store_term` is not a
    /// BitVec-indexed BitVec/Bool-element store chain.
    fn build_store_chain_interp(
        terms: &TermStore,
        bv_model: &BvModel,
        store_term: TermId,
        array_values: &HashMap<TermId, ArrayInterpretation>,
    ) -> Option<ArrayInterpretation> {
        use num_bigint::BigInt;

        let Sort::Array(arr_sort) = terms.sort(store_term) else {
            return None;
        };
        let Sort::BitVec(idx_bv) = &arr_sort.index_sort else {
            return None;
        };
        let idx_width = idx_bv.width;
        let default_val = match &arr_sort.element_sort {
            Sort::BitVec(elem_bv) => format_bitvec(&BigInt::from(0u64), elem_bv.width),
            Sort::Bool => "false".to_string(),
            _ => return None,
        };

        let chain_entries = Self::collect_store_chain_entries(terms, store_term);
        if chain_entries.is_empty() {
            return None;
        }

        // Find the base array under the store chain (where the walk stops).
        let mut base = store_term;
        loop {
            match terms.get(base) {
                TermData::App(sym, args) if sym.name() == "store" && args.len() == 3 => {
                    base = args[0];
                }
                _ => break,
            }
        }

        let mut index_to_value: HashMap<String, String> = HashMap::default();

        // Store-chain entries (ground truth; outermost store wins).
        for (idx_term, val_term) in &chain_entries {
            let idx_val = Self::store_chain_operand_value(terms, bv_model, *idx_term);
            let elem_val = match &arr_sort.element_sort {
                Sort::Bool => bv_model
                    .bool_overrides
                    .get(val_term)
                    .map(|&b| if b { "true" } else { "false" }.to_string()),
                Sort::BitVec(elem_bv) => {
                    Self::store_chain_operand_value(terms, bv_model, *val_term)
                        .map(|ev| format_bitvec(&ev, elem_bv.width))
                }
                _ => None,
            };
            if let (Some(ref iv), Some(ref ev_str)) = (idx_val, &elem_val) {
                let idx_str = format_bitvec(iv, idx_width);
                index_to_value
                    .entry(idx_str)
                    .or_insert_with(|| ev_str.clone());
            }
        }

        let mut interp = ArrayInterpretation {
            index_sort: Some(arr_sort.index_sort.clone()),
            element_sort: Some(arr_sort.element_sort.clone()),
            default: Some(default_val),
            ..Default::default()
        };

        // Inherit the base array's entries (ROW2) and default when present.
        if let Some(base_interp) = array_values.get(&base) {
            for (idx_str, val_str) in &base_interp.stores {
                index_to_value
                    .entry(idx_str.clone())
                    .or_insert_with(|| val_str.clone());
            }
            if let Some(ref base_default) = base_interp.default {
                interp.default = Some(base_default.clone());
            }
        }

        interp.stores = index_to_value.into_iter().collect();
        Some(interp)
    }

    /// Walk a store chain and collect (index_term, value_term) pairs.
    ///
    /// Returns pairs in outermost-first order (last store first).
    /// Stops at a base Var (or at depth limit to prevent unbounded recursion).
    fn collect_store_chain_entries(
        terms: &TermStore,
        mut array_term: TermId,
    ) -> Vec<(TermId, TermId)> {
        let mut entries = Vec::new();
        let mut depth = 0;
        const MAX_DEPTH: usize = 500;

        loop {
            if depth >= MAX_DEPTH {
                break;
            }
            match terms.get(array_term) {
                TermData::App(sym, args) if sym.name() == "store" && args.len() == 3 => {
                    entries.push((args[1], args[2])); // (index, value)
                    array_term = args[0]; // recurse into base
                    depth += 1;
                }
                _ => break, // base array (Var or other)
            }
        }
        entries
    }

    /// Populate array model entries for variables defined via store chains (#8512).
    ///
    /// Scans `assertions` for `(= Var store_chain)` or `(= store_chain Var)`
    /// patterns. For each, walks the store chain to collect index/value pairs,
    /// resolves them through the BV model, and merges with the base array's
    /// model entries.
    ///
    /// After variable substitution, `select(b, idx)` is rewritten to
    /// `select(store(a, i, v), idx)` and may be further simplified by
    /// `expand_select_store`. When assertions are restored, selects on `b`
    /// may not appear in the BV model at all. This function recovers the
    /// correct model by:
    /// 1. Extracting store chain entries (index/value pairs with ground truth)
    /// 2. Inheriting base array entries for indices not in the store chain
    /// 3. Removing any select-based entries that conflict with store chain values
    ///
    /// Returns the `(array_var, store_chain_base)` pairs whose chain resolved
    /// COMPLETELY — every (index, value) term in the chain came back concrete
    /// from the BV model. Only those interpretations cover every index the
    /// definition speaks to; a chain with even one unresolved pair leaves a hole
    /// that would read back as the array's `default`. The caller uses this to
    /// decide which nested-only definitions no longer need to be withheld as
    /// read-conflicted (see [`Self::extract_array_model_from_bv_model`]).
    fn populate_store_chain_array_models(
        terms: &TermStore,
        bv_model: &BvModel,
        assertions: &[TermId],
        array_values: &mut HashMap<TermId, ArrayInterpretation>,
    ) -> Vec<(TermId, TermId)> {
        use num_bigint::BigInt;

        // First pass: collect all (Var, store_chain_term, base_array) tuples.
        //
        // Store-chain definitions may be nested inside BV1 guards such as
        // `(ite (= arr (store ...)) #b1 #b0)`. Only trust nested definitions
        // reached through a top-level true assertion and model-forced true
        // BV1/Bool wrappers.
        let mut store_defs: Vec<(TermId, TermId, TermId)> = Vec::new();
        let mut seen_store_defs: HashSet<(TermId, TermId, TermId)> = HashSet::default();

        for &assertion in assertions {
            let mut visited: HashSet<(TermId, StoreChainTruth)> = HashSet::default();
            Self::collect_true_store_chain_defs(
                terms,
                bv_model,
                assertion,
                StoreChainTruth::BoolTrue,
                0,
                &mut visited,
                &mut seen_store_defs,
                &mut store_defs,
            );
        }

        if store_defs.is_empty() {
            return Vec::new();
        }

        let mut fully_resolved: Vec<(TermId, TermId)> = Vec::new();

        // Second pass: for each store-defined array variable, build the model.
        for (var_id, store_term, base_array) in store_defs {
            let Sort::Array(arr_sort) = terms.sort(var_id) else {
                continue;
            };
            let Sort::BitVec(idx_bv) = &arr_sort.index_sort else {
                continue;
            };
            let idx_width = idx_bv.width;

            let (default_val, _is_bool_elem) = match &arr_sort.element_sort {
                Sort::BitVec(elem_bv) => (format_bitvec(&BigInt::from(0u64), elem_bv.width), false),
                Sort::Bool => ("false".to_string(), true),
                _ => continue,
            };

            let chain_entries = Self::collect_store_chain_entries(terms, store_term);
            if chain_entries.is_empty() {
                continue;
            }

            let mut index_to_value: HashMap<String, String> = HashMap::default();
            // Cleared by any chain pair the BV model cannot make concrete: the
            // resulting interpretation then has a hole at an index the
            // definition constrains, and reporting it as total would claim the
            // `default` holds there.
            let mut all_pairs_resolved = true;

            // Step 1: Store chain entries (ground truth, highest priority).
            for (idx_term, val_term) in &chain_entries {
                let idx_val = bv_model
                    .values
                    .get(idx_term)
                    .cloned()
                    .or_else(|| Self::evaluate_bv_expr(terms, *idx_term, &bv_model.values));

                let elem_val = match &arr_sort.element_sort {
                    Sort::Bool => bv_model
                        .bool_overrides
                        .get(val_term)
                        .map(|&b| if b { "true" } else { "false" }.to_string()),
                    Sort::BitVec(elem_bv) => bv_model
                        .values
                        .get(val_term)
                        .cloned()
                        .or_else(|| Self::evaluate_bv_expr(terms, *val_term, &bv_model.values))
                        .map(|ev| format_bitvec(&ev, elem_bv.width)),
                    _ => None,
                };

                if let (Some(ref iv), Some(ref ev_str)) = (idx_val, &elem_val) {
                    let idx_str = format_bitvec(iv, idx_width);
                    // Outermost store wins: first occurrence at any index
                    // is the final value.
                    index_to_value
                        .entry(idx_str)
                        .or_insert_with(|| ev_str.clone());
                } else {
                    all_pairs_resolved = false;
                }
            }

            // Step 2: Inherit base array entries for indices not in the
            // store chain. ROW2 says: for index j != i in store(a,i,v),
            // select(store(a,i,v), j) = select(a, j). So b's value at
            // non-stored indices equals a's value at those indices.
            if let Some(base_interp) = array_values.get(&base_array) {
                for (idx_str, val_str) in &base_interp.stores {
                    index_to_value
                        .entry(idx_str.clone())
                        .or_insert_with(|| val_str.clone());
                }
            }

            let mut interp = array_values
                .remove(&var_id)
                .unwrap_or_else(|| ArrayInterpretation {
                    index_sort: Some(arr_sort.index_sort.clone()),
                    element_sort: Some(arr_sort.element_sort.clone()),
                    default: Some(default_val),
                    ..Default::default()
                });

            // Replace all stores with the computed values.
            // Discard select-based entries which may have incorrect values
            // from unconstrained bits after variable substitution.
            interp.stores = index_to_value.into_iter().collect();

            // Inherit default from base array if available.
            if let Some(base_interp) = array_values.get(&base_array) {
                if let Some(ref base_default) = base_interp.default {
                    interp.default = Some(base_default.clone());
                }
            }

            array_values.insert(var_id, interp);

            if all_pairs_resolved {
                fully_resolved.push((var_id, base_array));
            }
        }

        fully_resolved
    }

    fn collect_true_store_chain_defs(
        terms: &TermStore,
        bv_model: &BvModel,
        term: TermId,
        truth: StoreChainTruth,
        depth: usize,
        visited: &mut HashSet<(TermId, StoreChainTruth)>,
        seen_store_defs: &mut HashSet<(TermId, TermId, TermId)>,
        store_defs: &mut Vec<(TermId, TermId, TermId)>,
    ) {
        const MAX_DEPTH: usize = 4096;
        if depth >= MAX_DEPTH || !visited.insert((term, truth)) {
            return;
        }

        match truth {
            StoreChainTruth::BoolTrue => {
                if let Some((var_id, store_term)) =
                    Self::store_chain_definition_from_equality(terms, term)
                {
                    let base = Self::store_chain_base(terms, store_term);
                    if seen_store_defs.insert((var_id, store_term, base)) {
                        store_defs.push((var_id, store_term, base));
                    }
                    return;
                }
                Self::propagate_bool_true_store_chain_defs(
                    terms,
                    bv_model,
                    term,
                    depth,
                    visited,
                    seen_store_defs,
                    store_defs,
                );
            }
            StoreChainTruth::Bv1True => {
                Self::propagate_bv1_true_store_chain_defs(
                    terms,
                    bv_model,
                    term,
                    depth,
                    visited,
                    seen_store_defs,
                    store_defs,
                );
            }
        }
    }

    fn propagate_bool_true_store_chain_defs(
        terms: &TermStore,
        bv_model: &BvModel,
        term: TermId,
        depth: usize,
        visited: &mut HashSet<(TermId, StoreChainTruth)>,
        seen_store_defs: &mut HashSet<(TermId, TermId, TermId)>,
        store_defs: &mut Vec<(TermId, TermId, TermId)>,
    ) {
        match terms.get(term) {
            TermData::Not(_) | TermData::Const(_) | TermData::Var(_, _) => {}
            TermData::Ite(cond, then_term, else_term) if *terms.sort(term) == Sort::Bool => {
                Self::propagate_true_bool_ite(
                    terms,
                    bv_model,
                    *cond,
                    *then_term,
                    *else_term,
                    depth,
                    visited,
                    seen_store_defs,
                    store_defs,
                );
            }
            TermData::Ite(_, _, _) => {}
            TermData::App(sym, args) if *terms.sort(term) == Sort::Bool => match sym.name() {
                "and" => {
                    for &arg in args {
                        Self::collect_true_store_chain_defs(
                            terms,
                            bv_model,
                            arg,
                            StoreChainTruth::BoolTrue,
                            depth + 1,
                            visited,
                            seen_store_defs,
                            store_defs,
                        );
                    }
                }
                "=" if args.len() == 2 => {
                    Self::propagate_true_equality_side(
                        terms,
                        bv_model,
                        args[0],
                        args[1],
                        depth,
                        visited,
                        seen_store_defs,
                        store_defs,
                    );
                    Self::propagate_true_equality_side(
                        terms,
                        bv_model,
                        args[1],
                        args[0],
                        depth,
                        visited,
                        seen_store_defs,
                        store_defs,
                    );
                }
                "ite" if args.len() == 3 => {
                    Self::propagate_true_bool_ite(
                        terms,
                        bv_model,
                        args[0],
                        args[1],
                        args[2],
                        depth,
                        visited,
                        seen_store_defs,
                        store_defs,
                    );
                }
                "or" if !args.is_empty() => {
                    Self::propagate_forced_or_arm(
                        terms,
                        bv_model,
                        args,
                        depth,
                        visited,
                        seen_store_defs,
                        store_defs,
                    );
                }
                _ => {}
            },
            TermData::App(_, _) => {}
            TermData::Let(_, _) | TermData::Forall(_, _, _) | TermData::Exists(_, _, _) => {}
            _ => {}
        }
    }

    /// #8512-forced-or: an asserted-true disjunction forces an arm exactly when
    /// every OTHER arm is false under the model — unit propagation. That arm
    /// then holds, so its conjuncts (including a store-chain definition) are
    /// real definitions and may be walked, the same discipline
    /// [`Self::propagate_true_bool_ite`] applies to a model-forced `ite` branch.
    ///
    /// With two or more arms still live the model is free to satisfy either one,
    /// and adopting a definition out of one of them would FABRICATE an array
    /// value. Nothing is collected then, and the variables involved keep their
    /// partial interpretation and stay read-conflicted (see
    /// [`Self::array_vars_defined_only_under_nested_equality`]).
    ///
    /// The liveness test never consults an array interpretation — only the BV
    /// assignment — so it cannot depend on the very definitions being decided.
    fn propagate_forced_or_arm(
        terms: &TermStore,
        bv_model: &BvModel,
        args: &[TermId],
        depth: usize,
        visited: &mut HashSet<(TermId, StoreChainTruth)>,
        seen_store_defs: &mut HashSet<(TermId, TermId, TermId)>,
        store_defs: &mut Vec<(TermId, TermId, TermId)>,
    ) {
        let mut memo = BvEvalMemo::default();
        let mut false_cache: HashMap<TermId, bool> = HashMap::default();
        let mut live: Option<TermId> = None;
        let mut live_count = 0usize;
        for &arg in args {
            if Self::model_bool_is_false(terms, bv_model, arg, 0, &mut memo, &mut false_cache) {
                continue;
            }
            live_count += 1;
            if live_count > 1 {
                return;
            }
            live = Some(arg);
        }
        if let Some(arm) = live {
            Self::collect_true_store_chain_defs(
                terms,
                bv_model,
                arm,
                StoreChainTruth::BoolTrue,
                depth + 1,
                visited,
                seen_store_defs,
                store_defs,
            );
        }
    }

    fn propagate_true_bool_ite(
        terms: &TermStore,
        bv_model: &BvModel,
        cond: TermId,
        then_term: TermId,
        else_term: TermId,
        depth: usize,
        visited: &mut HashSet<(TermId, StoreChainTruth)>,
        seen_store_defs: &mut HashSet<(TermId, TermId, TermId)>,
        store_defs: &mut Vec<(TermId, TermId, TermId)>,
    ) {
        match Self::model_bool_value(terms, bv_model, cond) {
            Some(true) => Self::collect_true_store_chain_defs(
                terms,
                bv_model,
                then_term,
                StoreChainTruth::BoolTrue,
                depth + 1,
                visited,
                seen_store_defs,
                store_defs,
            ),
            Some(false) => Self::collect_true_store_chain_defs(
                terms,
                bv_model,
                else_term,
                StoreChainTruth::BoolTrue,
                depth + 1,
                visited,
                seen_store_defs,
                store_defs,
            ),
            None => match (
                Self::model_bool_value(terms, bv_model, then_term),
                Self::model_bool_value(terms, bv_model, else_term),
            ) {
                (Some(true), Some(false)) => Self::collect_true_store_chain_defs(
                    terms,
                    bv_model,
                    cond,
                    StoreChainTruth::BoolTrue,
                    depth + 1,
                    visited,
                    seen_store_defs,
                    store_defs,
                ),
                (Some(false), Some(true)) => Self::collect_true_store_chain_defs(
                    terms,
                    bv_model,
                    else_term,
                    StoreChainTruth::BoolTrue,
                    depth + 1,
                    visited,
                    seen_store_defs,
                    store_defs,
                ),
                _ => {}
            },
        }
    }

    fn propagate_true_equality_side(
        terms: &TermStore,
        bv_model: &BvModel,
        known_side: TermId,
        implied_side: TermId,
        depth: usize,
        visited: &mut HashSet<(TermId, StoreChainTruth)>,
        seen_store_defs: &mut HashSet<(TermId, TermId, TermId)>,
        store_defs: &mut Vec<(TermId, TermId, TermId)>,
    ) {
        if *terms.sort(known_side) != *terms.sort(implied_side) {
            return;
        }
        match terms.sort(known_side) {
            Sort::Bool if Self::model_bool_value(terms, bv_model, known_side) == Some(true) => {
                Self::collect_true_store_chain_defs(
                    terms,
                    bv_model,
                    implied_side,
                    StoreChainTruth::BoolTrue,
                    depth + 1,
                    visited,
                    seen_store_defs,
                    store_defs,
                );
            }
            Sort::BitVec(bv)
                if bv.width == 1
                    && Self::model_bv1_value(terms, bv_model, known_side) == Some(true) =>
            {
                Self::collect_true_store_chain_defs(
                    terms,
                    bv_model,
                    implied_side,
                    StoreChainTruth::Bv1True,
                    depth + 1,
                    visited,
                    seen_store_defs,
                    store_defs,
                );
            }
            _ => {}
        }
    }

    fn propagate_bv1_true_store_chain_defs(
        terms: &TermStore,
        bv_model: &BvModel,
        term: TermId,
        depth: usize,
        visited: &mut HashSet<(TermId, StoreChainTruth)>,
        seen_store_defs: &mut HashSet<(TermId, TermId, TermId)>,
        store_defs: &mut Vec<(TermId, TermId, TermId)>,
    ) {
        if !matches!(terms.sort(term), Sort::BitVec(bv) if bv.width == 1) {
            return;
        }

        match terms.get(term) {
            TermData::Ite(cond, then_term, else_term) => {
                Self::propagate_true_bv1_ite(
                    terms,
                    bv_model,
                    *cond,
                    *then_term,
                    *else_term,
                    depth,
                    visited,
                    seen_store_defs,
                    store_defs,
                );
            }
            TermData::App(sym, args) => match sym.name() {
                "bvand" => {
                    for &arg in args {
                        Self::collect_true_store_chain_defs(
                            terms,
                            bv_model,
                            arg,
                            StoreChainTruth::Bv1True,
                            depth + 1,
                            visited,
                            seen_store_defs,
                            store_defs,
                        );
                    }
                }
                "ite" if args.len() == 3 => {
                    Self::propagate_true_bv1_ite(
                        terms,
                        bv_model,
                        args[0],
                        args[1],
                        args[2],
                        depth,
                        visited,
                        seen_store_defs,
                        store_defs,
                    );
                }
                _ => {}
            },
            _ => {}
        }
    }

    fn propagate_true_bv1_ite(
        terms: &TermStore,
        bv_model: &BvModel,
        cond: TermId,
        then_term: TermId,
        else_term: TermId,
        depth: usize,
        visited: &mut HashSet<(TermId, StoreChainTruth)>,
        seen_store_defs: &mut HashSet<(TermId, TermId, TermId)>,
        store_defs: &mut Vec<(TermId, TermId, TermId)>,
    ) {
        match (
            Self::model_bv1_value(terms, bv_model, then_term),
            Self::model_bv1_value(terms, bv_model, else_term),
        ) {
            (Some(true), Some(false)) => {
                Self::collect_true_store_chain_defs(
                    terms,
                    bv_model,
                    cond,
                    StoreChainTruth::BoolTrue,
                    depth + 1,
                    visited,
                    seen_store_defs,
                    store_defs,
                );
            }
            _ => match Self::model_bool_value(terms, bv_model, cond) {
                Some(true) => Self::collect_true_store_chain_defs(
                    terms,
                    bv_model,
                    then_term,
                    StoreChainTruth::Bv1True,
                    depth + 1,
                    visited,
                    seen_store_defs,
                    store_defs,
                ),
                Some(false) => Self::collect_true_store_chain_defs(
                    terms,
                    bv_model,
                    else_term,
                    StoreChainTruth::Bv1True,
                    depth + 1,
                    visited,
                    seen_store_defs,
                    store_defs,
                ),
                None => {}
            },
        }
    }

    fn store_chain_definition_from_equality(
        terms: &TermStore,
        term: TermId,
    ) -> Option<(TermId, TermId)> {
        let TermData::App(sym, args) = terms.get(term) else {
            return None;
        };
        if sym.name() != "=" || args.len() != 2 {
            return None;
        }

        let lhs = args[0];
        let rhs = args[1];
        if matches!(terms.get(lhs), TermData::Var(_, _))
            && matches!(terms.sort(lhs), Sort::Array(_))
            && matches!(terms.get(rhs), TermData::App(s, _) if s.name() == "store")
        {
            Some((lhs, rhs))
        } else if matches!(terms.get(rhs), TermData::Var(_, _))
            && matches!(terms.sort(rhs), Sort::Array(_))
            && matches!(terms.get(lhs), TermData::App(s, _) if s.name() == "store")
        {
            Some((rhs, lhs))
        } else {
            None
        }
    }

    fn store_chain_base(terms: &TermStore, store_term: TermId) -> TermId {
        let mut base = store_term;
        loop {
            match terms.get(base) {
                TermData::App(sym, args) if sym.name() == "store" && args.len() == 3 => {
                    base = args[0];
                }
                _ => return base,
            }
        }
    }

    fn model_bool_value(terms: &TermStore, bv_model: &BvModel, term: TermId) -> Option<bool> {
        // Local memo: one-shot evaluation, fixed env for its duration.
        let mut memo = BvEvalMemo::default();
        Self::model_bool_value_memo(terms, bv_model, term, &mut memo)
    }

    /// Whether `term` is definitely FALSE under the BV model, decided
    /// STRUCTURALLY through `and`/`or` so one false conjunct settles a
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
