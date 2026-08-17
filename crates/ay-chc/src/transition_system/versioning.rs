// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Time-indexed variable versioning, unrolling, and transition system accessors.

use super::TransitionSystem;
use crate::{ChcExpr, ChcSort, ChcVar};
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};

/// Whether unrolled-frame constant/alias folding is enabled (`AY_FOLD_FRAMES=1`
/// enables). Default OFF: measured NEUTRAL on SYNAPSE_2 — leaf const/alias
/// chains are not the lustre frame bloat (the Bool definitional `v = (or ...)`
/// layers are), and the re-conjoined bindings slightly grow the tableau
/// (1748 vs 1172 rows @120s). Kept as sound, tested machinery for a future
/// var=term folding pass; the transform is equivalence-preserving (bindings
/// re-conjoined), so enabling it is sound for every consumer by construction.
fn fold_frames_enabled() -> bool {
    false // B24: never-set opt-in retired.
}

impl TransitionSystem {
    /// Create a time-indexed version of a variable.
    ///
    /// - Time 0: returns the original variable (`x`)
    /// - Time t>0: returns `x_t`
    ///
    /// This convention matches standard BMC/KIND unrolling.
    pub(crate) fn version_var(var: &ChcVar, k: usize) -> ChcVar {
        if k == 0 {
            var.clone()
        } else {
            ChcVar::new(format!("{}_{}", var.name, k), var.sort.clone())
        }
    }

    /// Version an expression for timestep k.
    ///
    /// Substitutes all state variables with their time-indexed versions.
    pub(crate) fn version_expr(expr: &ChcExpr, vars: &[ChcVar], k: usize) -> ChcExpr {
        let substitutions: Vec<_> = vars
            .iter()
            .map(|v| (v.clone(), ChcExpr::var(Self::version_var(v, k))))
            .collect();
        expr.substitute(&substitutions)
    }

    /// Version local (non-canonical) variables in an expression per timestep.
    ///
    /// After `version_expr` has handled canonical state variables, any remaining
    /// free variables are clause-local existentials. When the same formula is
    /// instantiated at multiple timesteps (e.g., Tr(0) ∧ Tr(1)), these locals
    /// collide and add spurious constraints. This function gives each timestep's
    /// locals unique names by appending `__{tag}{k}`.
    ///
    /// The `canonical_vars` slice lists base state variables. Variables matching
    /// these names (or their versioned forms like "v0_1", "v0_2") are excluded
    /// from renaming. `next_vars` optionally lists next-state variables to also
    /// exclude.
    ///
    /// Fixes #6789: Kind engine false-Safe from local variable collision across
    /// BMC unrollings.
    fn version_local_vars(
        expr: &ChcExpr,
        canonical_vars: &[ChcVar],
        next_vars: Option<&[ChcVar]>,
        k: usize,
        tag: &str,
    ) -> ChcExpr {
        let all_vars = expr.vars();

        // Build set of state variable names that should NOT be versioned.
        // These are canonical vars at various timesteps (v0, v0_1, v0_2, ...).
        let canonical_base_names: FxHashSet<&str> =
            canonical_vars.iter().map(|v| v.name.as_str()).collect();

        let is_canonical = |name: &str| -> bool {
            // Direct match: v0, v1, etc.
            if canonical_base_names.contains(name) {
                return true;
            }
            // Versioned match: v0_1, v0_2, etc.
            if let Some(base) = name.rsplit_once('_') {
                if base.1.chars().all(|c| c.is_ascii_digit())
                    && canonical_base_names.contains(base.0)
                {
                    return true;
                }
            }
            false
        };

        let substitutions: Vec<(ChcVar, ChcExpr)> = all_vars
            .into_iter()
            .filter(|v| {
                if is_canonical(&v.name) {
                    return false;
                }
                if let Some(nvars) = next_vars {
                    if nvars.iter().any(|nv| nv.name == v.name) {
                        return false;
                    }
                }
                true
            })
            .map(|v| {
                let versioned = ChcVar::new(format!("{}__{}{}", v.name, tag, k), v.sort.clone());
                (v, ChcExpr::var(versioned))
            })
            .collect();

        if substitutions.is_empty() {
            expr.clone()
        } else {
            expr.substitute(&substitutions)
        }
    }

    /// Send formula through time by k steps.
    ///
    /// Convenience method that versions using this system's variables.
    pub(crate) fn send_through_time(&self, formula: &ChcExpr, k: usize) -> ChcExpr {
        Self::version_expr(formula, &self.vars, k)
    }

    /// Rename state variables at exactly one timestep to another timestep.
    ///
    /// This is more targeted than `shift_versioned_state_vars`: it only affects
    /// variables at exactly `from_k`, leaving all other timesteps unchanged.
    ///
    /// Used by TPA for:
    /// - `rename_state_vars_at(expr, 1, 2)`: shifts v1 → v2 (Golem's `shiftOnlyNextVars`)
    /// - `rename_state_vars_at(expr, 2, 1)`: shifts v2 → v1 (Golem's `cleanInterpolant`)
    ///
    /// Part of #1008.
    pub(crate) fn rename_state_vars_at(
        &self,
        expr: &ChcExpr,
        from_k: usize,
        to_k: usize,
    ) -> ChcExpr {
        if from_k == to_k {
            return expr.clone();
        }

        let subst: Vec<(ChcVar, ChcExpr)> = self
            .vars
            .iter()
            .map(|v| {
                let from_var = Self::version_var(v, from_k);
                let to_var = Self::version_var(v, to_k);
                (from_var, ChcExpr::var(to_var))
            })
            .collect();

        expr.substitute(&subst)
    }

    /// Shift state variables by `delta` timesteps.
    ///
    /// This operates on the naming scheme produced by `version_var`:
    /// - Time 0: `x`
    /// - Time t>0: `x_t`
    ///
    /// Only canonical `x_<pos>` suffixes are treated as time indices. This avoids
    /// rewriting original variables like `x_0`, `x_-1`, `x_01`, or `x_+1`.
    ///
    /// The shift is clamped at time 0 to avoid creating negative time indices.
    pub(crate) fn shift_versioned_state_vars(&self, expr: &ChcExpr, delta: i32) -> ChcExpr {
        fn split_base_and_time(name: &str) -> (&str, i32) {
            if let Some((base, suffix)) = name.rsplit_once('_') {
                let bytes = suffix.as_bytes();
                let is_canonical_pos_int = !bytes.is_empty()
                    && bytes[0].is_ascii_digit()
                    && (bytes[0] != b'0' || bytes.len() == 1)
                    && bytes.iter().all(u8::is_ascii_digit);

                if is_canonical_pos_int {
                    if let Ok(t) = suffix.parse::<i32>() {
                        // Treat only strictly-positive suffixes as time indices.
                        //
                        // This matches `version_var` which uses `x` (not `x_0`) for time 0.
                        if t > 0 {
                            return (base, t);
                        }
                    }
                }
            }
            (name, 0)
        }

        let state_bases: FxHashSet<&str> = self.vars.iter().map(|v| v.name.as_str()).collect();

        let subst: Vec<(ChcVar, ChcExpr)> = expr
            .vars()
            .into_iter()
            .filter_map(|v| {
                let (base, t) = split_base_and_time(&v.name);
                if !state_bases.contains(base) {
                    return None;
                }

                let new_t = (t + delta).max(0);
                let new_name = if new_t == 0 {
                    base.to_string()
                } else {
                    format!("{base}_{new_t}")
                };
                if new_name == v.name {
                    return None;
                }
                let sort = v.sort.clone();
                Some((v, ChcExpr::var(ChcVar::new(new_name, sort))))
            })
            .collect();

        if subst.is_empty() {
            return expr.clone();
        }
        expr.substitute(&subst)
    }

    // ========================================================================
    // Unrolling
    // ========================================================================

    /// Create the k-step unrolled transition relation.
    ///
    /// Returns: `trans@0 ∧ trans@1 ∧ ... ∧ trans@(k-1)`
    ///
    /// Where `trans@i` is the transition from time `i` to time `i+1`.
    pub(crate) fn k_transition(&self, k: usize) -> ChcExpr {
        if k == 0 {
            return ChcExpr::Bool(true);
        }

        let mut conjuncts = Vec::with_capacity(k);
        for i in 0..k {
            conjuncts.push(self.transition_at(i));
        }

        let unrolled = ChcExpr::and_all(conjuncts);
        if fold_frames_enabled() {
            Self::fold_frame_constants_and_aliases(&unrolled)
        } else {
            unrolled
        }
    }

    /// Equivalence-preserving constant + alias folding over an unrolled frame
    /// conjunction (gap-attribution rank 3; the leaf-binding analog of golem's
    /// `TermUtils::extractSubstitutionsAndSimplify` / OpenSMT's
    /// `MainSolver::simplifyFormulas` substitution pass).
    ///
    /// Collects top-level-conjunct bindings `v = c` (Int, incl. the linear
    /// `k+v = c` form) and `v = w` aliases, replaces every other occurrence
    /// with the class representative (the constant when one is known), folds
    /// constants, and RE-CONJOINS one binding per substituted variable so the
    /// result is EQUIVALENT to the input — not merely equisatisfiable. Models
    /// and interpolation vocabulary are therefore preserved for every
    /// consumer, and a contradictory input (two different constants in one
    /// alias class) still reduces to `false` through the substituted
    /// equalities. Only leaf right-hand sides are substituted, so there is no
    /// term-growth risk. The win: solvers no longer rediscover thousands of
    /// trivial equality chains in unrolled tableaus (lustre frames measured at
    /// rows=37885 / vars=62483 for a 43-var system near k=64 before folding).
    pub(crate) fn fold_frame_constants_and_aliases(expr: &ChcExpr) -> ChcExpr {
        // Union-find over variable names (path-halving on lookup).
        fn find(parent: &mut FxHashMap<String, String>, name: &str) -> String {
            let mut cur = name.to_string();
            loop {
                let Some(p) = parent.get(&cur) else {
                    return cur;
                };
                if *p == cur {
                    return cur;
                }
                let gp = parent.get(p).cloned().unwrap_or_else(|| p.clone());
                parent.insert(cur.clone(), gp.clone());
                cur = gp;
            }
        }

        let mut current = expr.clone();
        // One binding per substituted variable name (later rounds only add
        // newly discovered bindings; a substituted var cannot reappear).
        let mut bindings: FxHashMap<String, ChcExpr> = FxHashMap::default();

        for _ in 0..8 {
            let consts = current.extract_var_const_equalities();
            let aliases = current.extract_var_var_equalities();
            if consts.is_empty() && aliases.is_empty() {
                break;
            }

            let mut parent: FxHashMap<String, String> = FxHashMap::default();
            let mut var_of: FxHashMap<String, ChcVar> = FxHashMap::default();
            for (a, b) in &aliases {
                var_of.entry(a.name.clone()).or_insert_with(|| a.clone());
                var_of.entry(b.name.clone()).or_insert_with(|| b.clone());
                let ra = find(&mut parent, &a.name);
                let rb = find(&mut parent, &b.name);
                if ra != rb {
                    // Deterministic root: lexicographically smallest name, so
                    // the representative choice is stable across runs.
                    let (root, child) = if ra <= rb { (ra, rb) } else { (rb, ra) };
                    parent.insert(child, root);
                }
            }
            // Class constant (first one wins; a conflicting second constant
            // stays in the formula as a substituted equality that folds to
            // `false`, preserving unsatisfiability).
            let mut class_const: FxHashMap<String, i128> = FxHashMap::default();
            for (v, c) in &consts {
                var_of.entry(v.name.clone()).or_insert_with(|| v.clone());
                let r = find(&mut parent, &v.name);
                class_const.entry(r).or_insert(*c);
            }

            // Build the substitution: every variable in a class maps to the
            // class constant, or (for non-root members) to the root variable.
            let mut subst: Vec<(ChcVar, ChcExpr)> = Vec::new();
            let names: Vec<String> = var_of.keys().cloned().collect();
            for name in names {
                let root = find(&mut parent, &name);
                let var = var_of[&name].clone();
                if let Some(&c) = class_const.get(&root) {
                    if var.sort == ChcSort::Int {
                        subst.push((var, ChcExpr::Int(c)));
                        continue;
                    }
                }
                if name != root {
                    let root_var = var_of
                        .get(&root)
                        .cloned()
                        .unwrap_or_else(|| ChcVar::new(root.clone(), var.sort.clone()));
                    if root_var.sort == var.sort {
                        subst.push((var, ChcExpr::var(root_var)));
                    }
                }
            }
            if subst.is_empty() {
                break;
            }
            for (v, rhs) in &subst {
                bindings
                    .entry(v.name.clone())
                    .or_insert_with(|| ChcExpr::eq(ChcExpr::var(v.clone()), rhs.clone()));
            }
            current = current.substitute(&subst).simplify_constants();
        }

        if bindings.is_empty() {
            return current;
        }
        // Deterministic binding order (DetHashMap iteration is deterministic,
        // but sort by name anyway so the output is stable and reviewable).
        let mut bound: Vec<(String, ChcExpr)> = bindings.into_iter().collect();
        bound.sort_by(|a, b| a.0.cmp(&b.0));
        ChcExpr::and(current, ChcExpr::and_all(bound.into_iter().map(|(_, e)| e)))
    }

    /// Create transition constraint from step k to step k+1.
    ///
    /// Substitutes:
    /// - `vars` → `vars_k`
    /// - `vars_next` → `vars_{k+1}`
    pub(crate) fn transition_at(&self, k: usize) -> ChcExpr {
        let mut substitutions: Vec<_> = self
            .vars
            .iter()
            .map(|v| (v.clone(), ChcExpr::var(Self::version_var(v, k))))
            .collect();

        // Handle _next variables
        let mut canonical_names: FxHashSet<String> =
            self.vars.iter().map(|v| v.name.clone()).collect();
        for v in &self.vars {
            let next_var = ChcVar::new(format!("{}_next", v.name), v.sort.clone());
            canonical_names.insert(next_var.name.clone());
            substitutions.push((next_var, ChcExpr::var(Self::version_var(v, k + 1))));
            // Also recognize versioned forms (v_0, v_1, v_2, ...) as canonical.
            // TransitionSystems created via `new()` may use numeric suffixes (x_1)
            // instead of _next (x_next) for next-state variables. Without this,
            // `x_1` in the transition would be erroneously renamed as a local.
            canonical_names.insert(Self::version_var(v, k).name);
            canonical_names.insert(Self::version_var(v, k + 1).name);
        }

        // Version local (non-canonical) variables per timestep to avoid collisions
        // across unrollings (#6789). Without this, Tr(0) ∧ Tr(1) shares local vars,
        // adding spurious constraints that make reachable states unreachable.
        let all_vars = self.transition.vars();
        for v in all_vars {
            if !canonical_names.contains(&v.name) {
                let versioned = ChcVar::new(format!("{}__t{}", v.name, k), v.sort.clone());
                substitutions.push((v, ChcExpr::var(versioned)));
            }
        }

        self.transition.substitute(&substitutions)
    }

    /// Create init constraint at step k.
    pub(crate) fn init_at(&self, k: usize) -> ChcExpr {
        let versioned = Self::version_expr(&self.init, &self.vars, k);
        // Version local variables per timestep (#6789)
        Self::version_local_vars(&versioned, &self.vars, None, k, "i")
    }

    /// Create query constraint at step k.
    pub(crate) fn query_at(&self, k: usize) -> ChcExpr {
        let versioned = Self::version_expr(&self.query, &self.vars, k);
        // Version local variables per timestep (#6789)
        Self::version_local_vars(&versioned, &self.vars, None, k, "q")
    }

    /// Create ¬query at step k.
    ///
    /// Uses the raw (pre-mod-elimination) query to avoid free auxiliary
    /// variables in the negation. See `init_raw` field doc for details.
    pub(crate) fn neg_query_at(&self, k: usize) -> ChcExpr {
        let versioned = Self::version_expr(&self.query_raw, &self.vars, k);
        let with_locals = Self::version_local_vars(&versioned, &self.vars, None, k, "nq");
        ChcExpr::not(with_locals)
    }

    /// Create ¬init at step k.
    ///
    /// Uses the raw (pre-mod-elimination) init to avoid free auxiliary
    /// variables in the negation. See `init_raw` field doc for details.
    pub(crate) fn neg_init_at(&self, k: usize) -> ChcExpr {
        let versioned = Self::version_expr(&self.init_raw, &self.vars, k);
        let with_locals = Self::version_local_vars(&versioned, &self.vars, None, k, "ni");
        ChcExpr::not(with_locals)
    }

    // ========================================================================
    // Variable Queries
    // ========================================================================

    /// Get all state variable names (for interpolation shared_vars).
    pub(crate) fn state_var_names(&self) -> FxHashSet<String> {
        self.vars.iter().map(|v| v.name.clone()).collect()
    }

    /// Get state variable names at timestep `k` (e.g. `x_1`) for interpolation boundaries.
    pub(crate) fn state_var_names_at(&self, k: usize) -> FxHashSet<String> {
        self.vars
            .iter()
            .map(|v| Self::version_var(v, k).name)
            .collect()
    }

    /// Get the state variables.
    pub(crate) fn state_vars(&self) -> &[ChcVar] {
        &self.vars
    }

    /// Get the raw (pre-mod-elimination) query.
    ///
    /// Used when negating the query: the raw form ensures `check_sat` handles
    /// mod elimination with properly scoped aux vars per call.
    pub(crate) fn query_raw(&self) -> &ChcExpr {
        &self.query_raw
    }

    /// Returns the first state sort unsupported by interpolation engines, if any.
    ///
    /// Interpolation-based engines (IMC, DAR) support Int, Real, BitVec, and
    /// Array sorts. Bool is rejected because Craig interpolation over 100+
    /// shared Boolean variables is inefficient (#5877). This scans state
    /// variables and returns the first unsupported sort for early rejection
    /// (#1940). BV support added (#5595, #5644).
    pub(crate) fn find_unsupported_interpolation_state_sort(&self) -> Option<ChcSort> {
        for var in self.state_vars() {
            match &var.sort {
                ChcSort::Int | ChcSort::Real | ChcSort::BitVec(_) | ChcSort::Array(_, _) => {
                    continue
                }
                sort => return Some(sort.clone()),
            }
        }
        None
    }

    /// Like [`find_unsupported_interpolation_state_sort`], but additionally
    /// admits Bool state variables (F1, the LRA-Lin unlock).
    ///
    /// The mixed `Bool…Real…` state predicates that dominate the LRA-Lin track
    /// (sally/oral_messages, vmt/cav12, etc.) made IMC/LAWI/DAR self-skip as
    /// `NotApplicable`, so the interpolation engines that Golem wins this track
    /// with (IMC alone solves oral_messages in 0.05–1.5s) never ran. Bool state
    /// vars are kept propositional and versioned alongside the arithmetic ones;
    /// the interpolating SMT backend is already Bool-capable (the dual-MBP
    /// strategy in `interpolation::mbp_interpolation` interpolates mixed
    /// Bool+LIA via AllSAT+MBP on models rather than syntactic structure).
    ///
    /// Soundness (#5660/#5877): the original guard was added against false-SAT.
    /// Admitting Bool here does NOT weaken validation — every Safe invariant and
    /// every Unsafe counterexample produced by IMC/LAWI/DAR is still replayed
    /// against the ORIGINAL clauses by the portfolio acceptance pipeline
    /// (`portfolio::accept::accept_or_reject` → `validate_safe_*` /
    /// `validate_unsafe_translating`, strict proofs). A Bool+Real result that
    /// fails to validate is demoted to Unknown, never returned as a wrong
    /// verdict. PDKIND deliberately keeps the strict (Bool-rejecting) guard to
    /// avoid false-unsat from SingleLoop location variables (#6500), so this is
    /// a separate method rather than a relaxation of the shared one.
    pub(crate) fn find_unsupported_interpolation_state_sort_allowing_bool(
        &self,
    ) -> Option<ChcSort> {
        for var in self.state_vars() {
            match &var.sort {
                ChcSort::Bool
                | ChcSort::Int
                | ChcSort::Real
                | ChcSort::BitVec(_)
                | ChcSort::Array(_, _) => continue,
                sort => return Some(sort.clone()),
            }
        }
        None
    }

    /// Returns the first state sort unsupported by transition-system engines, if any.
    ///
    /// Non-interpolation engines (PDKIND, BMC) can handle Bool-state transition
    /// systems that arise from BvToBool preprocessing (#5877). This accepts
    /// Bool in addition to Int, Real, BitVec, and Array.
    pub(crate) fn find_unsupported_transition_state_sort(&self) -> Option<ChcSort> {
        for var in self.state_vars() {
            match &var.sort {
                ChcSort::Bool
                | ChcSort::Int
                | ChcSort::Real
                | ChcSort::BitVec(_)
                | ChcSort::Array(_, _) => continue,
                sort => return Some(sort.clone()),
            }
        }
        None
    }
}
