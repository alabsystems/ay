// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Variable substitution preprocessing pass
//!
//! Extracts equalities from assertions and substitutes variables with
//! their equivalent terms. This is critical for BV soundness (#1708, #1720):
//!
//! When `(= mode_1 mode_2)` is asserted, predicates `(= mode_1 c)` and
//! `(= mode_2 c)` must become the same SAT variable. Without substitution,
//! they are encoded as different variables with no semantic link.
//!
//! # Algorithm
//!
//! 1. Extract equalities `(= var term)` from top-level assertions
//! 2. Build substitution map: var -> term
//! 3. Apply substitutions to all assertions
//!
//! # Reference
//! - `reference/bitwuzla/src/preprocess/pass/variable_substitution.cpp`
//! - the development design notes

use super::PreprocessingPass;
// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::TermData;
use ay_core::{Sort, TermId, TermStore};

/// Red zone size for `stacker::maybe_grow` in variable substitution helper recursion (#8414).
const VAR_SUBST_HELPER_STACK_RED_ZONE: usize = 32 * 1024;

/// Stack segment size allocated by stacker for variable substitution helper recursion.
const VAR_SUBST_HELPER_STACK_SIZE: usize = 1024 * 1024;

/// Maximum distinct DAG nodes for scalar replacement RHS terms.
///
/// QF_ABV array SSA substitutions intentionally allow large store chains (#8140),
/// but substituting giant scalar ITE/select expressions can spend the whole
/// timeout in cycle checks and select/store expansion on linked-list encodings.
pub(crate) const VAR_SUBST_SCALAR_REPLACEMENT_NODE_LIMIT: usize = 32;

/// Variable substitution preprocessing pass.
///
/// Scope (per #1782, extended #2767):
/// - Direct equalities `(= var term)` only
/// - Direct substitution (no transitive chains initially)
/// - Bool, BV, Int, Real, and Array sorts
pub(crate) struct VariableSubstitution {
    /// Substitution map: variable TermId -> replacement TermId
    substitutions: HashMap<TermId, TermId>,
    /// Source equality assertion that introduced each substitution.
    substitution_sources: HashMap<TermId, TermId>,
    /// Cache for substituted terms to avoid redundant work
    subst_cache: HashMap<TermId, TermId>,
    /// When true, skip Array-sorted variable substitutions (#7890).
    /// The AUFLIA deferred-postprocessing path restores original assertions
    /// for model validation; array variable substitutions remove defining
    /// equalities that the validator needs, causing false Unknown.
    skip_array_sort: bool,
    /// Optional maximum distinct DAG nodes for scalar replacement RHS terms.
    scalar_replacement_node_limit: Option<usize>,
    /// Accept only substitutions whose replacement is a literal CONSTANT
    /// (#qfuflia-const-subst). Safe in the presence of uninterpreted
    /// functions: a constant RHS pushes no UF application anywhere, so the
    /// EUF-linking hazard that gates full substitution off on UF routes
    /// (#7884) cannot arise. Lets QF_UFLIA/QF_AUFLIA fold facts like
    /// `(= adr_lo 4)` through the formula the way z3's preprocessing does.
    constants_only: bool,
}

impl VariableSubstitution {
    /// Create a new VariableSubstitution pass.
    pub(crate) fn new() -> Self {
        Self {
            substitutions: HashMap::default(),
            substitution_sources: HashMap::default(),
            subst_cache: HashMap::default(),
            skip_array_sort: false,
            scalar_replacement_node_limit: None,
            constants_only: false,
        }
    }

    /// Create a pass that only substitutes variables defined equal to literal
    /// constants (#qfuflia-const-subst) — safe alongside uninterpreted
    /// functions; used by the UF-carrying preprocessing routes.
    pub(crate) fn new_constants_only() -> Self {
        Self {
            substitutions: HashMap::default(),
            substitution_sources: HashMap::default(),
            subst_cache: HashMap::default(),
            skip_array_sort: true,
            scalar_replacement_node_limit: None,
            constants_only: true,
        }
    }

    /// Create a VariableSubstitution pass that skips Array-sorted variables.
    ///
    /// Used by the AUFLIA preprocessor (#7890) where array substitutions
    /// conflict with deferred postprocessing model validation.
    pub(crate) fn new_skip_arrays() -> Self {
        Self {
            substitutions: HashMap::default(),
            substitution_sources: HashMap::default(),
            subst_cache: HashMap::default(),
            skip_array_sort: true,
            scalar_replacement_node_limit: None,
            constants_only: false,
        }
    }

    /// Rebuild a map-only substitution view from a recorded `from -> to` map
    /// (#A1-repair-resync). The validation pipeline re-runs the #A1 LIA model
    /// reconciliation passes AFTER post-validation repair passes mutate Int
    /// leaf values; at that point only the executor's
    /// `recorded_var_substitutions` survive, and the reconciliation passes
    /// consume nothing beyond [`Self::substitutions`].
    pub(crate) fn from_recorded_map(map: HashMap<TermId, TermId>) -> Self {
        Self {
            substitutions: map,
            substitution_sources: HashMap::default(),
            subst_cache: HashMap::default(),
            skip_array_sort: true,
            scalar_replacement_node_limit: None,
            constants_only: false,
        }
    }

    pub(crate) fn set_scalar_replacement_node_limit(&mut self, limit: usize) {
        self.scalar_replacement_node_limit = Some(limit);
    }

    /// Get the substitution map (from -> to).
    ///
    /// This can be used after preprocessing to recover original variable values
    /// from the preprocessed model: if `from -> to` is in the map, then the
    /// original variable `from` has the same value as `to` in any model.
    pub(crate) fn substitutions(&self) -> &HashMap<TermId, TermId> {
        &self.substitutions
    }

    /// Get the equality assertion that introduced each substitution variable.
    pub(crate) fn substitution_sources(&self) -> &HashMap<TermId, TermId> {
        &self.substitution_sources
    }

    /// Check if a term is a variable (not a constant, not a compound term).
    fn is_variable(terms: &TermStore, term: TermId) -> bool {
        matches!(terms.get(term), TermData::Var(_, _))
    }

    /// Check whether a candidate replacement is cheap enough to substitute.
    ///
    /// Array replacements are exempt because QF_ABV needs store-chain array SSA
    /// collapse before array axiom generation (#8140). Scalars are budgeted by
    /// distinct DAG nodes so shared subterms are not over-counted.
    fn replacement_within_budget(
        terms: &TermStore,
        replacement: TermId,
        existing_substs: &HashMap<TermId, TermId>,
        scalar_replacement_node_limit: Option<usize>,
    ) -> bool {
        // Array (#8140) and Datatype (#dt-selector-subst) replacements are exempt
        // from the scalar node budget: a store-chain array SSA or an ite-of-
        // constructors datatype reconstruction is large pre-fold but collapses
        // once read-over-write / selector-over-constructor simplification fires at
        // the use sites, so the apparent node count is not the post-substitution cost.
        if matches!(terms.sort(replacement), Sort::Array(_) | Sort::Datatype(_)) {
            return true;
        }
        let Some(limit) = scalar_replacement_node_limit else {
            return true;
        };
        Self::term_dag_size_within_limit(terms, replacement, existing_substs, limit)
    }

    fn term_dag_size_within_limit(
        terms: &TermStore,
        root: TermId,
        existing_substs: &HashMap<TermId, TermId>,
        limit: usize,
    ) -> bool {
        let mut seen = HashSet::default();
        let mut stack = vec![root];

        while let Some(term) = stack.pop() {
            if !seen.insert(term) {
                continue;
            }
            if seen.len() > limit {
                return false;
            }

            match terms.get(term) {
                TermData::Const(_) => {}
                TermData::Var(_, _) => {
                    if let Some(&replacement) = existing_substs.get(&term) {
                        if !matches!(terms.sort(replacement), Sort::Array(_)) {
                            stack.push(replacement);
                        }
                    }
                }
                TermData::App(_, args) => stack.extend(args.iter().copied()),
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, t, e) => {
                    stack.push(*c);
                    stack.push(*t);
                    stack.push(*e);
                }
                TermData::Let(bindings, body) => {
                    stack.push(*body);
                    for (_, binding) in bindings {
                        stack.push(*binding);
                    }
                }
                TermData::Forall(_, body, triggers) | TermData::Exists(_, body, triggers) => {
                    stack.push(*body);
                    for &trigger in triggers.iter().flatten() {
                        stack.push(trigger);
                    }
                }
                // All current TermData variants are handled above.
                // This arm is required by #[non_exhaustive] and catches future variants.
                other => unreachable!(
                    "unhandled TermData variant in term_dag_size_within_limit(): {other:?}"
                ),
            }
        }

        true
    }

    /// Check if `term` contains `var` (for cycle detection).
    /// Uses `stacker::maybe_grow` for stack safety on deeply nested terms (#8414).
    ///
    /// Visited-set deduplication: the term store is a hash-consed DAG; without
    /// it this walk enumerates every tree PATH — exponential in sharing depth
    /// (the DAG→tree pathology; a large BMC instance hung here for minutes).
    /// Skipping a revisited node is sound: `any`/`||` short-circuit on the
    /// first `true`, so any node the walk CONTINUES past evaluated `false`,
    /// and that value is fixed for this (term table, `var`) pair.
    fn contains_var(terms: &TermStore, term: TermId, var: TermId) -> bool {
        let mut visited: HashSet<TermId> = HashSet::default();
        Self::contains_var_inner(terms, term, var, &mut visited)
    }

    fn contains_var_inner(
        terms: &TermStore,
        term: TermId,
        var: TermId,
        visited: &mut HashSet<TermId>,
    ) -> bool {
        stacker::maybe_grow(
            VAR_SUBST_HELPER_STACK_RED_ZONE,
            VAR_SUBST_HELPER_STACK_SIZE,
            || {
                if term == var {
                    return true;
                }
                if !visited.insert(term) {
                    return false;
                }

                match terms.get(term) {
                    TermData::Const(_) | TermData::Var(_, _) => false,
                    TermData::App(_, args) => args
                        .iter()
                        .any(|&arg| Self::contains_var_inner(terms, arg, var, visited)),
                    TermData::Not(inner) => Self::contains_var_inner(terms, *inner, var, visited),
                    TermData::Ite(c, t, e) => {
                        Self::contains_var_inner(terms, *c, var, visited)
                            || Self::contains_var_inner(terms, *t, var, visited)
                            || Self::contains_var_inner(terms, *e, var, visited)
                    }
                    TermData::Let(bindings, body) => {
                        bindings
                            .iter()
                            .any(|(_, t)| Self::contains_var_inner(terms, *t, var, visited))
                            || Self::contains_var_inner(terms, *body, var, visited)
                    }
                    TermData::Forall(_, body, triggers) | TermData::Exists(_, body, triggers) => {
                        Self::contains_var_inner(terms, *body, var, visited)
                            || triggers
                                .iter()
                                .flatten()
                                .any(|&t| Self::contains_var_inner(terms, t, var, visited))
                    }
                    // All current TermData variants are handled above.
                    // This arm is required by #[non_exhaustive] and catches future variants.
                    other => {
                        unreachable!("unhandled TermData variant in contains_var(): {other:?}")
                    }
                }
            },
        ) // stacker::maybe_grow
    }

    /// Check whether `var -> replacement` is a cycle-safe substitution
    /// given the existing and pending substitutions.
    ///
    /// We require:
    /// - `replacement` does not contain `var` (occurs check).
    /// - Adding `var -> replacement` does not create a cycle through existing
    ///   substitutions (e.g., `a -> b+2` and `b -> a` would cycle).
    fn is_cycle_safe_substitution(
        terms: &TermStore,
        var: TermId,
        replacement: TermId,
        existing_substs: &HashMap<TermId, TermId>,
        pending_vars: &HashSet<TermId>,
    ) -> bool {
        // Occurs check: replacement must not contain var directly
        if Self::contains_var(terms, replacement, var) {
            return false;
        }

        // Collect all variables in the replacement expression
        let mut vars_in_replacement = Vec::new();
        Self::collect_vars(terms, replacement, &mut vars_in_replacement);

        // Check: would any variable in replacement transitively reach var
        // through the existing + pending substitution chain?
        for &v in &vars_in_replacement {
            if Self::reaches_var_through_substs(terms, v, var, existing_substs, pending_vars) {
                return false;
            }
        }

        true
    }

    fn is_allowed_substitution(
        terms: &TermStore,
        var: TermId,
        replacement: TermId,
        existing_substs: &HashMap<TermId, TermId>,
        pending_vars: &HashSet<TermId>,
        scalar_replacement_node_limit: Option<usize>,
    ) -> bool {
        let within_budget = Self::replacement_within_budget(
            terms,
            replacement,
            existing_substs,
            scalar_replacement_node_limit,
        );
        within_budget
            && Self::is_cycle_safe_substitution(
                terms,
                var,
                replacement,
                existing_substs,
                pending_vars,
            )
    }

    fn existing_substitutions_within_budget(
        terms: &TermStore,
        existing_substs: &HashMap<TermId, TermId>,
        candidate_substs: &HashMap<TermId, TermId>,
        scalar_replacement_node_limit: Option<usize>,
    ) -> bool {
        existing_substs.values().all(|&replacement| {
            Self::replacement_within_budget(
                terms,
                replacement,
                candidate_substs,
                scalar_replacement_node_limit,
            )
        })
    }

    /// Collect all variable TermIds appearing in `term`.
    /// Uses `stacker::maybe_grow` for stack safety on deeply nested terms (#8414).
    /// Visited-set deduplication: without it a hash-consed DAG is walked once
    /// per tree PATH (exponential; see `contains_var`), and `out` collected one
    /// entry per path to each leaf. Both callers (`is_cycle_safe_substitution`,
    /// `reaches_var_through_substs`) consume `out` as a SET (membership /
    /// worklist seeding), so per-distinct-node collection is semantics-preserving.
    fn collect_vars(terms: &TermStore, term: TermId, out: &mut Vec<TermId>) {
        let mut visited: HashSet<TermId> = HashSet::default();
        Self::collect_vars_inner(terms, term, out, &mut visited)
    }

    fn collect_vars_inner(
        terms: &TermStore,
        term: TermId,
        out: &mut Vec<TermId>,
        visited: &mut HashSet<TermId>,
    ) {
        stacker::maybe_grow(
            VAR_SUBST_HELPER_STACK_RED_ZONE,
            VAR_SUBST_HELPER_STACK_SIZE,
            || {
                if !visited.insert(term) {
                    return;
                }
                match terms.get(term) {
                    TermData::Var(_, _) => out.push(term),
                    TermData::Const(_) => {}
                    TermData::App(_, args) => {
                        for &arg in args {
                            Self::collect_vars_inner(terms, arg, out, visited);
                        }
                    }
                    TermData::Not(inner) => Self::collect_vars_inner(terms, *inner, out, visited),
                    TermData::Ite(c, t, e) => {
                        Self::collect_vars_inner(terms, *c, out, visited);
                        Self::collect_vars_inner(terms, *t, out, visited);
                        Self::collect_vars_inner(terms, *e, out, visited);
                    }
                    TermData::Let(bindings, body) => {
                        for (_, t) in bindings {
                            Self::collect_vars_inner(terms, *t, out, visited);
                        }
                        Self::collect_vars_inner(terms, *body, out, visited);
                    }
                    TermData::Forall(_, body, triggers) | TermData::Exists(_, body, triggers) => {
                        Self::collect_vars_inner(terms, *body, out, visited);
                        for &t in triggers.iter().flatten() {
                            Self::collect_vars_inner(terms, t, out, visited);
                        }
                    }
                    // All current TermData variants are handled above.
                    // This arm is required by #[non_exhaustive] and catches future variants.
                    other => {
                        unreachable!("unhandled TermData variant in collect_vars(): {other:?}")
                    }
                }
            },
        ) // stacker::maybe_grow
    }

    /// Check if variable `start` can reach `target` by following the substitution
    /// chain transitively.
    ///
    /// Follows the chain: if `start` is substituted with an expression, collect
    /// all variables in that expression. If any of them is `target`, return true.
    /// Otherwise, recursively check each of those variables.
    fn reaches_var_through_substs(
        terms: &TermStore,
        start: TermId,
        target: TermId,
        existing_substs: &HashMap<TermId, TermId>,
        _pending_vars: &HashSet<TermId>,
    ) -> bool {
        let mut visited = HashSet::default();
        let mut worklist = vec![start];

        while let Some(current) = worklist.pop() {
            if !visited.insert(current) {
                continue;
            }
            if let Some(&replacement) = existing_substs.get(&current) {
                if Self::contains_var(terms, replacement, target) {
                    return true;
                }
                // Follow chain: collect variables in the replacement and
                // check them too
                let mut vars = Vec::new();
                Self::collect_vars(terms, replacement, &mut vars);
                for v in vars {
                    if !visited.contains(&v) {
                        worklist.push(v);
                    }
                }
            }
        }
        false
    }

    /// Try to extract a substitution from an equality assertion.
    ///
    /// Returns `Some((var, term))` if the assertion is `(= var term)` or
    /// `(= term var)` where var is a variable and term doesn't contain var.
    ///
    /// `existing_substs` and `pending_vars` are used for graph-based cycle
    /// detection, replacing the overly strict TermId-ordering that blocked
    /// substitutions like `a -> (+ b 2)` when `b > a` (#2830).
    fn find_substitution(
        terms: &mut TermStore,
        assertion: TermId,
        existing_substs: &HashMap<TermId, TermId>,
        pending_vars: &HashSet<TermId>,
        skip_array_sort: bool,
        scalar_replacement_node_limit: Option<usize>,
        constants_only: bool,
    ) -> Option<(TermId, TermId)> {
        match terms.get(assertion) {
            TermData::App(sym, args) if sym.name() == "=" && args.len() == 2 => {
                let (lhs, rhs) = (args[0], args[1]);

                // #qfuflia-const-subst: constants-only mode accepts a
                // substitution only when one side is a Var and the other a
                // literal constant.
                if constants_only {
                    let var_const = |a: TermId, b: TermId| {
                        matches!(terms.get(a), TermData::Var(_, _))
                            && matches!(terms.get(b), TermData::Const(_))
                    };
                    if !var_const(lhs, rhs) && !var_const(rhs, lhs) {
                        return None;
                    }
                }

                // Prefer substituting sort-compatible variables
                let lhs_sort = terms.sort(lhs);
                let rhs_sort = terms.sort(rhs);

                // Substitute Bool, BV, Int, Real, and Array sorts.
                // Int/Real enables elimination of equality chains like
                // result_a = self_a + 1 that the LRA simplex can't resolve (#2767).
                // Array sort (#8140): enables collapsing array variable chains like
                // array_Q_22 = store(array_Q_21, ...). After substitution,
                // select(array_Q_22, i) becomes select(store(array_Q_21, ...), i)
                // which expand_select_store resolves into ITE chains. This is safe
                // because preprocessing runs BEFORE array axiom generation.
                // skip_array_sort (#7890): the AUFLIA deferred-postprocessing path
                // needs array defining equalities for model validation.
                let is_substitutable_sort = |s: &Sort| {
                    if skip_array_sort && matches!(s, Sort::Array(_)) {
                        return false;
                    }
                    // Datatype (#dt-selector-subst): substituting a datatype SSA
                    // variable defined `(= local_N (ite c (C ..) ..))` lets the
                    // selector-over-constructor/ite fold collapse `(fld_x local_N)`
                    // to its concrete field — critical for Parser/Vec post-state
                    // reconstructions whose slice-len/field reads otherwise stay
                    // opaque selectors over a giant ite-tree. SOUND (definitional
                    // equality + datatype selector axiom).
                    matches!(
                        s,
                        Sort::Bool
                            | Sort::BitVec(_)
                            | Sort::Int
                            | Sort::Real
                            | Sort::Array(_)
                            | Sort::Datatype(_)
                    )
                };

                if !is_substitutable_sort(lhs_sort) && !is_substitutable_sort(rhs_sort) {
                    return None;
                }

                // If both sides are variables, orient substitution by TermId to avoid cycles.
                if Self::is_variable(terms, lhs) && Self::is_variable(terms, rhs) {
                    if lhs == rhs {
                        return None;
                    }
                    let (var, replacement) = if lhs > rhs { (lhs, rhs) } else { (rhs, lhs) };
                    if Self::is_allowed_substitution(
                        terms,
                        var,
                        replacement,
                        existing_substs,
                        pending_vars,
                        scalar_replacement_node_limit,
                    ) {
                        return Some((var, replacement));
                    }
                    return None;
                }

                // Try lhs -> rhs
                if Self::is_variable(terms, lhs)
                    && Self::is_allowed_substitution(
                        terms,
                        lhs,
                        rhs,
                        existing_substs,
                        pending_vars,
                        scalar_replacement_node_limit,
                    )
                {
                    return Some((lhs, rhs));
                }

                // Try rhs -> lhs
                if Self::is_variable(terms, rhs)
                    && Self::is_allowed_substitution(
                        terms,
                        rhs,
                        lhs,
                        existing_substs,
                        pending_vars,
                        scalar_replacement_node_limit,
                    )
                {
                    return Some((rhs, lhs));
                }

                None
            }
            // Bool equality is encoded as ite(a, b, not(b)) by mk_eq (#3421).
            // Recognize this pattern for variable substitution.
            TermData::Ite(cond, then_br, else_br)
                if *terms.sort(*cond) == Sort::Bool
                    && *terms.sort(*then_br) == Sort::Bool
                    && matches!(terms.get(*else_br), TermData::Not(inner) if *inner == *then_br) =>
            {
                let (lhs, rhs) = (*cond, *then_br);

                if Self::is_variable(terms, lhs) && Self::is_variable(terms, rhs) {
                    if lhs == rhs {
                        return None;
                    }
                    let (var, replacement) = if lhs > rhs { (lhs, rhs) } else { (rhs, lhs) };
                    if Self::is_allowed_substitution(
                        terms,
                        var,
                        replacement,
                        existing_substs,
                        pending_vars,
                        scalar_replacement_node_limit,
                    ) {
                        return Some((var, replacement));
                    }
                    return None;
                }

                if Self::is_variable(terms, lhs)
                    && Self::is_allowed_substitution(
                        terms,
                        lhs,
                        rhs,
                        existing_substs,
                        pending_vars,
                        scalar_replacement_node_limit,
                    )
                {
                    return Some((lhs, rhs));
                }

                if Self::is_variable(terms, rhs)
                    && Self::is_allowed_substitution(
                        terms,
                        rhs,
                        lhs,
                        existing_substs,
                        pending_vars,
                        scalar_replacement_node_limit,
                    )
                {
                    return Some((rhs, lhs));
                }

                None
            }
            // ITE-wrapped equality: mk_eq expands (= var (ite c a b)) into
            // (ite c (= var a) (= var b)) during frontend elaboration.
            // Recover the substitution var -> ite(c, a, b).
            TermData::Ite(cond, then_br, else_br) => {
                let (cond, then_br, else_br) = (*cond, *then_br, *else_br);
                if constants_only {
                    // var := ite(...) is never a constant fold.
                    return None;
                }
                Self::find_ite_wrapped_substitution(
                    terms,
                    cond,
                    then_br,
                    else_br,
                    existing_substs,
                    pending_vars,
                    skip_array_sort,
                    scalar_replacement_node_limit,
                    false,
                )
            }
            _ => None,
        }
    }

    /// Recognize ITE-expanded equality and recover the substitution.
    ///
    /// When `mk_eq` processes `(= var (ite c a b))` for non-Bool sorts, it
    /// expands to `(ite c (= var a) (= var b))`. This defeats variable
    /// substitution because the outer ITE is not an equality.
    ///
    /// This method recognizes the pattern:
    ///   `ite(c, (= X a), (= X b))` where X is the same variable in both branches
    /// and recovers the substitution `X -> ite(c, a, b)`.
    fn find_ite_wrapped_substitution(
        terms: &mut TermStore,
        cond: TermId,
        then_br: TermId,
        else_br: TermId,
        existing_substs: &HashMap<TermId, TermId>,
        pending_vars: &HashSet<TermId>,
        skip_array_sort: bool,
        scalar_replacement_node_limit: Option<usize>,
        _constants_only: bool,
    ) -> Option<(TermId, TermId)> {
        // Both branches must be equalities: (= X a) and (= X b)
        let (then_lhs, then_rhs) = match terms.get(then_br) {
            TermData::App(sym, args) if sym.name() == "=" && args.len() == 2 => (args[0], args[1]),
            _ => return None,
        };

        // Nested ITE chain: `ite(c, (= var a), ite(c2, (= var b), ...))`. The else
        // branch is itself an ite of equalities, not a single equality — the shape
        // of a multi-arm SSA datatype reconstruction (one arm per dispatch branch
        // distributed by `fold_datatype_eq`). Recover the whole chain
        // `var -> ite(c, a, ite(c2, b, ...))` so the post-state datatype variable
        // can be eliminated and its selectors folded. (#dt-selector-subst)
        if matches!(terms.get(else_br), TermData::Ite(..)) {
            for var_candidate in [then_lhs, then_rhs] {
                if !Self::is_variable(terms, var_candidate) {
                    continue;
                }
                let sort = terms.sort(var_candidate).clone();
                if skip_array_sort && matches!(sort, Sort::Array(_)) {
                    continue;
                }
                if !matches!(
                    sort,
                    Sort::Bool
                        | Sort::BitVec(_)
                        | Sort::Int
                        | Sort::Real
                        | Sort::Array(_)
                        | Sort::Datatype(_)
                ) {
                    continue;
                }
                if let Some(replacement) =
                    Self::recover_var_ite_chain(terms, var_candidate, cond, then_br, else_br)
                {
                    if Self::is_allowed_substitution(
                        terms,
                        var_candidate,
                        replacement,
                        existing_substs,
                        pending_vars,
                        scalar_replacement_node_limit,
                    ) {
                        return Some((var_candidate, replacement));
                    }
                }
            }
            return None;
        }

        let (else_lhs, else_rhs) = match terms.get(else_br) {
            TermData::App(sym, args) if sym.name() == "=" && args.len() == 2 => (args[0], args[1]),
            _ => return None,
        };

        // Find the common variable across the two equalities.
        // Possible arrangements:
        //   (= var a) and (= var b) -> var is common, replacement is ite(c, a, b)
        //   (= a var) and (= var b) -> var is common, replacement is ite(c, a, b)
        //   (= var a) and (= b var) -> var is common, replacement is ite(c, a, b)
        //   (= a var) and (= b var) -> var is common, replacement is ite(c, a, b)
        let candidates: [(TermId, TermId, TermId); 4] = [
            (then_lhs, then_rhs, else_rhs), // var=then_lhs=else_lhs
            (then_rhs, then_lhs, else_rhs), // var=then_rhs=else_lhs
            (then_lhs, then_rhs, else_lhs), // var=then_lhs=else_rhs
            (then_rhs, then_lhs, else_lhs), // var=then_rhs=else_rhs
        ];

        for (var_candidate, a, b) in candidates {
            // The variable must appear in the matching position of both equalities
            let matches_then = var_candidate == then_lhs || var_candidate == then_rhs;
            let matches_else = var_candidate == else_lhs || var_candidate == else_rhs;
            if !matches_then || !matches_else {
                continue;
            }

            if !Self::is_variable(terms, var_candidate) {
                continue;
            }

            // Check sort is substitutable
            let sort = terms.sort(var_candidate).clone();
            if skip_array_sort && matches!(sort, Sort::Array(_)) {
                continue;
            }
            if !matches!(
                sort,
                Sort::Bool
                    | Sort::BitVec(_)
                    | Sort::Int
                    | Sort::Real
                    | Sort::Array(_)
                    | Sort::Datatype(_)
            ) {
                continue;
            }

            // Build the replacement: ite(c, a, b)
            let replacement = terms.mk_ite(cond, a, b);

            if Self::is_allowed_substitution(
                terms,
                var_candidate,
                replacement,
                existing_substs,
                pending_vars,
                scalar_replacement_node_limit,
            ) {
                return Some((var_candidate, replacement));
            }
        }

        None
    }

    /// The side of an equality `(= var X)` / `(= X var)` that is not `var`.
    /// Returns `None` when `eq_term` is not an equality binding `var`.
    fn eq_other_side(terms: &TermStore, eq_term: TermId, var: TermId) -> Option<TermId> {
        match terms.get(eq_term) {
            TermData::App(sym, args) if sym.name() == "=" && args.len() == 2 => {
                if args[0] == var {
                    Some(args[1])
                } else if args[1] == var {
                    Some(args[0])
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    /// Recover `var`'s definition from a (possibly nested) ite of equalities
    /// `ite(cond, (= var a), <else>)`, where `<else>` is either `(= var b)` or a
    /// further such ite. Returns the value-level `ite(cond, a, <else-value>)`, or
    /// `None` if any leaf is not an equality binding `var`. This rebuilds the
    /// substitution `var -> ite(...)` that `fold_datatype_eq` distributed into an
    /// ite of per-arm equalities during elaboration. (#dt-selector-subst)
    fn recover_var_ite_chain(
        terms: &mut TermStore,
        var: TermId,
        cond: TermId,
        then_br: TermId,
        else_br: TermId,
    ) -> Option<TermId> {
        let then_val = Self::eq_other_side(terms, then_br, var)?;
        let else_val = match terms.get(else_br).clone() {
            TermData::Ite(c, t, e) => Self::recover_var_ite_chain(terms, var, c, t, e)?,
            _ => Self::eq_other_side(terms, else_br, var)?,
        };
        Some(terms.mk_ite(cond, then_val, else_val))
    }
}

impl Default for VariableSubstitution {
    fn default() -> Self {
        Self::new()
    }
}

impl PreprocessingPass for VariableSubstitution {
    fn apply(&mut self, terms: &mut TermStore, assertions: &mut Vec<TermId>) -> bool {
        let debug = crate::theory_debug_flags::debug_var_subst();

        // Phase 1: Extract all substitutions from assertions
        let mut new_substitutions: Vec<(TermId, TermId, TermId)> = Vec::new();
        let mut substituted_vars: HashSet<TermId> = HashSet::default();

        if debug {
            safe_eprintln!("[var_subst] Scanning {} assertions", assertions.len());
        }

        // Build combined substitution map for cycle detection: includes both
        // previously-committed and newly-found substitutions. This allows
        // graph-based cycle checks that are less restrictive than TermId ordering (#2830).
        let mut combined_substs = self.substitutions.clone();

        for &assertion in assertions.iter() {
            if let Some((var, replacement)) = Self::find_substitution(
                terms,
                assertion,
                &combined_substs,
                &substituted_vars,
                self.skip_array_sort,
                self.scalar_replacement_node_limit,
                self.constants_only,
            ) {
                // Don't substitute a variable twice (within this pass, or across fixed-point rounds).
                if self.substitutions.contains_key(&var) || substituted_vars.contains(&var) {
                    if debug {
                        safe_eprintln!("[var_subst] Skip: {:?} already substituted", var);
                    }
                    continue;
                }
                let mut inserted_into_combined = false;
                if self.scalar_replacement_node_limit.is_some() {
                    combined_substs.insert(var, replacement);
                    inserted_into_combined = true;
                    if !Self::existing_substitutions_within_budget(
                        terms,
                        &self.substitutions,
                        &combined_substs,
                        self.scalar_replacement_node_limit,
                    ) {
                        if debug {
                            safe_eprintln!(
                                "[var_subst] Skip: {:?} would push an existing scalar substitution over budget",
                                var
                            );
                        }
                        combined_substs.remove(&var);
                        continue;
                    }
                }
                if debug {
                    let var_name = if let TermData::Var(n, _) = terms.get(var) {
                        n.clone()
                    } else {
                        format!("{var:?}")
                    };
                    let rep_name = if let TermData::Var(n, _) = terms.get(replacement) {
                        n.clone()
                    } else {
                        format!("{replacement:?}")
                    };
                    safe_eprintln!(
                        "[var_subst] Found: {} ({:?}) -> {} ({:?})",
                        var_name,
                        var,
                        rep_name,
                        replacement
                    );
                }
                new_substitutions.push((var, replacement, assertion));
                substituted_vars.insert(var);
                // Add to combined map so future assertions see this substitution
                // for cycle detection purposes
                if !inserted_into_combined {
                    combined_substs.insert(var, replacement);
                }
            }
        }

        // If no new substitutions, nothing to do
        if new_substitutions.is_empty() {
            return false;
        }

        if self.scalar_replacement_node_limit.is_some() {
            // Close the assertion-order gap for scalar chains. A candidate like
            // x0 -> (ite c v x1) is locally small before x1's substitution is
            // seen, but can become huge once the full pass-local substitution
            // graph is known.
            let mut budgeted_combined_substs = combined_substs.clone();
            new_substitutions.retain(|(var, replacement, _)| {
                let within_budget = Self::replacement_within_budget(
                    terms,
                    *replacement,
                    &budgeted_combined_substs,
                    self.scalar_replacement_node_limit,
                );
                if !within_budget {
                    if debug {
                        safe_eprintln!(
                            "[var_subst] Skip: {:?} replacement exceeds scalar budget after pass-local substitutions",
                            var
                        );
                    }
                    budgeted_combined_substs.remove(var);
                }
                within_budget
            });
            if new_substitutions.is_empty() {
                return false;
            }
        }

        // Add new substitutions to the map
        for (var, replacement, assertion) in new_substitutions {
            self.substitutions.insert(var, replacement);
            self.substitution_sources.insert(var, assertion);
        }

        // Phase 2: Apply substitutions to all assertions
        let mut modified = false;
        for assertion in assertions.iter_mut() {
            let new_assertion = self.substitute_term(terms, *assertion);
            if new_assertion != *assertion {
                *assertion = new_assertion;
                modified = true;
            }
        }

        modified
    }

    fn reset(&mut self) {
        // Clear caches but preserve substitutions for fixed-point iteration
        self.subst_cache.clear();
    }
}

mod apply;

#[allow(clippy::panic)]
#[cfg(test)]
mod tests;
