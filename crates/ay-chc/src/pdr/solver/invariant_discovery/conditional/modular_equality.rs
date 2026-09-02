// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

mod candidates;

#[cfg(test)]
mod tests;

use candidates::{MAX_MODULAR_EQUALITY_MODULUS, MODULAR_EQUALITY_SCAN_NODE_BUDGET};

const MODULAR_EQUALITY_DISCOVERY_BUDGET: std::time::Duration =
    std::time::Duration::from_millis(500);
const MODULAR_EQUALITY_SMT_CALL_BUDGET: std::time::Duration = std::time::Duration::from_millis(500);
const MAX_CASE_SPLIT_MODULUS: i128 = 16;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ModularEqualityDomain {
    Int,
    BitVec(u32),
}

impl ModularEqualityDomain {
    fn from_sorts(lhs: &ChcSort, rhs: &ChcSort) -> Option<Self> {
        match (lhs, rhs) {
            (ChcSort::Int, ChcSort::Int) => Some(Self::Int),
            (ChcSort::BitVec(lhs_width), ChcSort::BitVec(rhs_width))
                if lhs_width == rhs_width && *lhs_width > 0 =>
            {
                Some(Self::BitVec(*lhs_width))
            }
            _ => None,
        }
    }

    fn supports_modulus(self, modulus: i128) -> bool {
        if !(2..=MAX_MODULAR_EQUALITY_MODULUS).contains(&modulus) {
            return false;
        }
        match self {
            Self::Int => true,
            Self::BitVec(width) if width >= 128 => true,
            Self::BitVec(width) => (modulus as u128) < (1u128 << width),
        }
    }

    fn supports_init_value(self, value: i128) -> bool {
        match self {
            Self::Int => true,
            Self::BitVec(_) if value < 0 => false,
            Self::BitVec(width) if width >= 128 => true,
            Self::BitVec(width) => (value as u128) < (1u128 << width),
        }
    }

    fn constant(self, value: i128) -> ChcExpr {
        match self {
            Self::Int => ChcExpr::Int(value),
            Self::BitVec(width) => ChcExpr::BitVec(value as u128, width),
        }
    }

    fn remainder(self, dividend: ChcExpr, modulus: i128) -> ChcExpr {
        match self {
            Self::Int => ChcExpr::mod_op(dividend, ChcExpr::Int(modulus)),
            Self::BitVec(width) => {
                ChcExpr::bv_urem(dividend, ChcExpr::BitVec(modulus as u128, width))
            }
        }
    }
}

struct ModularClauseQuery<'a> {
    domain: ModularEqualityDomain,
    body_i: &'a ChcExpr,
    body_j: &'a ChcExpr,
    head_i: &'a ChcExpr,
    head_j: &'a ChcExpr,
    constraint: &'a ChcExpr,
    modulus: i128,
    lhs_name: &'a str,
    rhs_name: &'a str,
}

struct ModularDiscoveryPair<'a> {
    predicate: PredicateId,
    lhs_index: usize,
    rhs_index: usize,
    lhs: &'a ChcVar,
    rhs: &'a ChcVar,
    domain: ModularEqualityDomain,
    lhs_init: i128,
    rhs_init: i128,
    start: ay_core::time::Instant,
}

impl PdrSolver {
    fn discover_modular_equality_pair(
        &mut self,
        pair: &ModularDiscoveryPair<'_>,
        moduli: &[i128],
    ) -> bool {
        for &k in moduli {
            if !pair.domain.supports_modulus(k)
                || pair.rhs_init < 0
                || pair.rhs_init >= k
                || pair.lhs_init.rem_euclid(k) != pair.rhs_init
            {
                continue;
            }
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: Testing modular equality ({} mod {}) = {} (init: {} mod {} = {})",
                    pair.lhs.name,
                    k,
                    pair.rhs.name,
                    pair.lhs_init,
                    k,
                    pair.rhs_init
                );
            }
            if self.is_cancelled() || pair.start.elapsed() >= MODULAR_EQUALITY_DISCOVERY_BUDGET {
                return false;
            }
            if !self.is_modular_equality_preserved_by_transitions(
                pair.predicate,
                pair.lhs_index,
                pair.rhs_index,
                k,
                Some(pair.start),
            ) {
                continue;
            }

            let invariant = ChcExpr::eq(
                pair.domain.remainder(ChcExpr::var((*pair.lhs).clone()), k),
                ChcExpr::var((*pair.rhs).clone()),
            );
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: Discovered modular equality invariant for pred {}: ({} mod {}) = {}",
                    pair.predicate.index(),
                    pair.lhs.name,
                    k,
                    pair.rhs.name
                );
            }
            self.add_discovered_invariant_algebraic(pair.predicate, invariant, 1);
        }
        true
    }

    fn discover_modular_equality_pairs(
        &mut self,
        predicate: PredicateId,
        canonical_vars: &[ChcVar],
        moduli: &[i128],
        start: ay_core::time::Instant,
    ) -> bool {
        let init_values = self.get_init_values(predicate);
        for lhs_index in 0..canonical_vars.len() {
            for rhs_index in 0..canonical_vars.len() {
                if lhs_index == rhs_index {
                    continue;
                }
                let lhs = &canonical_vars[lhs_index];
                let rhs = &canonical_vars[rhs_index];
                let Some(domain) = ModularEqualityDomain::from_sorts(&lhs.sort, &rhs.sort) else {
                    continue;
                };
                let (Some(lhs_init), Some(rhs_init)) = (
                    init_values
                        .get(&lhs.name)
                        .filter(|bounds| bounds.min == bounds.max)
                        .map(|bounds| bounds.min),
                    init_values
                        .get(&rhs.name)
                        .filter(|bounds| bounds.min == bounds.max)
                        .map(|bounds| bounds.min),
                ) else {
                    continue;
                };
                if !domain.supports_init_value(lhs_init) || !domain.supports_init_value(rhs_init) {
                    continue;
                }
                let pair = ModularDiscoveryPair {
                    predicate,
                    lhs_index,
                    rhs_index,
                    lhs,
                    rhs,
                    domain,
                    lhs_init,
                    rhs_init,
                    start,
                };
                if !self.discover_modular_equality_pair(&pair, moduli) {
                    return false;
                }
            }
        }
        true
    }

    /// Discover modular equality invariants proactively before the PDR loop starts.
    ///
    /// For each predicate with fact clauses, finds same-domain `Int` or `BitVec`
    /// variable pairs `(vi, vj)` where:
    /// 1. (vi mod k) = vj at init (where vj is in range [0, k-1])
    /// 2. The modular equality is preserved by all self-transitions
    ///
    /// This captures counter/residue and ring-buffer state machines. Candidate
    /// moduli come from the predicate's own transitions, never a static list.
    pub(in crate::pdr::solver) fn discover_modular_equality_invariants(&mut self) {
        if self.config.verbose {
            safe_eprintln!("PDR: Searching for modular equality invariants");
        }

        // Wall-clock budget for modular equality discovery (#3121).
        // Each SMT call can take up to 500ms; with O(n^2) variable pairs this
        // can consume multiple seconds. Cap total time to leave budget for the
        // main blocking loop and verify_model.
        let mod_eq_start = ay_core::time::Instant::now();

        let predicates: Vec<_> = self.problem.predicates().to_vec();
        let mut remaining_scan_nodes = MODULAR_EQUALITY_SCAN_NODE_BUDGET;

        for pred in &predicates {
            if self.is_cancelled() || mod_eq_start.elapsed() >= MODULAR_EQUALITY_DISCOVERY_BUDGET {
                return;
            }

            // Skip predicates without fact clauses (no initial state)
            if !self.predicate_has_facts(pred.id) {
                continue;
            }

            let canonical_vars = match self.canonical_vars(pred.id) {
                Some(v) => v.to_vec(),
                None => continue,
            };

            // Derive a small, stable set of moduli from this predicate's own
            // self-transitions.  Exhausting the structural scan budget rejects
            // the remainder of discovery instead of using a partial scan.
            let Some(moduli) =
                self.data_driven_modular_equality_moduli(pred.id, &mut remaining_scan_nodes)
            else {
                return;
            };
            if moduli.is_empty() {
                continue;
            }

            if !self.discover_modular_equality_pairs(
                pred.id,
                &canonical_vars,
                &moduli,
                mod_eq_start,
            ) {
                return;
            }
        }
    }

    /// Check if (var_i mod k) = var_j is preserved by all transitions for a predicate.
    ///
    /// Uses SMT to check that for each transition clause:
    ///   If (body_i mod k) = body_j in pre-state,
    ///   then (head_i mod k) = head_j in post-state.
    #[cfg(test)]
    fn is_modular_equality_preserved_without_budget(
        &mut self,
        predicate: PredicateId,
        idx_i: usize,
        idx_j: usize,
        k: i128,
    ) -> bool {
        self.is_modular_equality_preserved_by_transitions(predicate, idx_i, idx_j, k, None)
    }

    fn substitute_modular_head_definitions(
        head_args: &[ChcExpr],
        head_i: &ChcExpr,
        head_j: &ChcExpr,
        clause_constraint: &ChcExpr,
    ) -> (ChcExpr, ChcExpr) {
        let head_var_names: Vec<&str> = head_args
            .iter()
            .filter_map(|arg| match arg {
                ChcExpr::Var(var) => Some(var.name.as_str()),
                _ => None,
            })
            .collect();
        if head_var_names.is_empty() {
            return (head_i.clone(), head_j.clone());
        }

        let mut substitutions = Vec::new();
        for conjunct in clause_constraint.collect_conjuncts() {
            let ChcExpr::Op(ChcOp::Eq, ref args) = conjunct else {
                continue;
            };
            if args.len() != 2 {
                continue;
            }
            let definition = match (args[0].as_ref(), args[1].as_ref()) {
                (ChcExpr::Var(var), value) if head_var_names.contains(&var.name.as_str()) => {
                    Some(((*var).clone(), (*value).clone()))
                }
                (value, ChcExpr::Var(var)) if head_var_names.contains(&var.name.as_str()) => {
                    Some(((*var).clone(), (*value).clone()))
                }
                _ => None,
            };
            if let Some(definition) = definition {
                substitutions.push(definition);
            }
        }
        if substitutions.is_empty() {
            (head_i.clone(), head_j.clone())
        } else {
            (
                head_i.substitute(&substitutions),
                head_j.substitute(&substitutions),
            )
        }
    }

    fn large_modular_equality_clause_preserved(
        smt: &mut crate::smt::SmtContext,
        verbose: bool,
        request: &ModularClauseQuery<'_>,
        discovery_start: Option<ay_core::time::Instant>,
    ) -> bool {
        let k = request.modulus;
        let query = ChcExpr::and_vec(vec![
            (*request.constraint).clone(),
            ChcExpr::eq(
                request.domain.remainder((*request.body_i).clone(), k),
                (*request.body_j).clone(),
            ),
            ChcExpr::ne(
                request.domain.remainder((*request.head_i).clone(), k),
                (*request.head_j).clone(),
            ),
        ])
        .propagate_constants()
        .simplify_constants();
        if matches!(query, ChcExpr::Bool(false)) {
            return true;
        }

        smt.reset();
        let timeout = discovery_start.map_or(MODULAR_EQUALITY_SMT_CALL_BUDGET, |start| {
            MODULAR_EQUALITY_DISCOVERY_BUDGET.saturating_sub(start.elapsed())
        });
        if timeout.is_zero() {
            return false;
        }
        match smt.check_sat_with_timeout(&query, timeout.min(MODULAR_EQUALITY_SMT_CALL_BUDGET)) {
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => true,
            SmtResult::Sat(_) => {
                if verbose {
                    safe_eprintln!(
                        "PDR: Modular equality ({} mod {k}) = {} NOT preserved",
                        request.lhs_name,
                        request.rhs_name
                    );
                }
                false
            }
            SmtResult::Unknown => {
                if verbose {
                    safe_eprintln!(
                        "PDR: Modular equality ({} mod {k}) = {} Unknown",
                        request.lhs_name,
                        request.rhs_name
                    );
                }
                false
            }
        }
    }

    fn modular_equality_case_query(request: &ModularClauseQuery<'_>, residue: i128) -> ChcExpr {
        let k = request.modulus;
        let query = ChcExpr::and_vec(vec![
            (*request.constraint).clone(),
            ChcExpr::eq((*request.body_j).clone(), request.domain.constant(residue)),
            ChcExpr::eq(
                request.domain.remainder((*request.body_i).clone(), k),
                request.domain.constant(residue),
            ),
            ChcExpr::ne(
                request.domain.remainder((*request.head_i).clone(), k),
                (*request.head_j).clone(),
            ),
        ])
        .propagate_constants();

        match (request.domain, request.body_i) {
            (ModularEqualityDomain::Int, ChcExpr::Var(body_var)) => {
                Self::resolve_mod_with_known_residue(&query, &body_var.name, k, residue)
                    .simplify_constants()
            }
            // BV wrap can change a residue unless k divides 2^w, so the
            // integer rewrite is inapplicable. The SMT checker sees exact BV.
            _ => query,
        }
    }

    fn finish_modular_preservation(
        &self,
        checked_self_loop: bool,
        canonical_vars: &[ChcVar],
        lhs_index: usize,
        rhs_index: usize,
        modulus: i128,
    ) -> bool {
        if !checked_self_loop {
            return false;
        }
        if self.config.verbose {
            safe_eprintln!(
                "PDR: Modular equality ({} mod {}) = {} is preserved by all transitions",
                canonical_vars[lhs_index].name,
                modulus,
                canonical_vars[rhs_index].name
            );
        }
        true
    }

    pub(in crate::pdr::solver) fn is_modular_equality_preserved_by_transitions(
        &mut self,
        predicate: PredicateId,
        idx_i: usize,
        idx_j: usize,
        k: i128,
        discovery_start: Option<ay_core::time::Instant>,
    ) -> bool {
        let canonical_vars = match self.canonical_vars(predicate) {
            Some(v) => v.to_vec(),
            None => return false,
        };
        let Some(var_i) = canonical_vars.get(idx_i) else {
            return false;
        };
        let Some(var_j) = canonical_vars.get(idx_j) else {
            return false;
        };
        let Some(domain) = ModularEqualityDomain::from_sorts(&var_i.sort, &var_j.sort) else {
            return false;
        };
        if !domain.supports_modulus(k) {
            return false;
        }

        // Track whether we checked at least one self-loop clause (#1388).
        let mut checked_any_self_loop = false;

        // Check all transition clauses that define this predicate
        for clause in self.problem.clauses_defining(predicate) {
            // Skip fact clauses (no body predicates)
            if clause.body.predicates.is_empty() {
                continue;
            }

            let head_args = match &clause.head {
                crate::ClauseHead::Predicate(_, a) => a.as_slice(),
                crate::ClauseHead::False => continue,
            };

            if head_args.len() != canonical_vars.len() {
                return false;
            }

            // Get the head expressions for var_i and var_j (post-state values)
            let head_i_raw = &head_args[idx_i];
            let head_j_raw = &head_args[idx_j];

            // For single-predicate body self-transitions
            if clause.body.predicates.len() != 1 {
                // Hyperedge - be conservative
                return false;
            }

            let (body_pred, body_args) = &clause.body.predicates[0];
            if *body_pred != predicate {
                // Inter-predicate transition: skip, only check self-loops for preservation.
                // If zero self-loops exist, we'll return false at the end (#1388).
                continue;
            }
            if body_args.len() != canonical_vars.len() {
                return false;
            }

            // This is a self-loop clause - mark that we're checking at least one
            checked_any_self_loop = true;

            let body_i = &body_args[idx_i];
            let body_j = &body_args[idx_j];

            // Check: IF (body_i mod k) = body_j THEN (head_i mod k) = head_j
            // Equivalently: (body_i mod k) = body_j AND (head_i mod k) != head_j is UNSAT
            let clause_constraint = clause
                .body
                .constraint
                .clone()
                .unwrap_or(ChcExpr::Bool(true));

            // Substitute head variable definitions from clause constraint (#3211).
            // For clauses like `C = A+1 ∧ D = ite(B=0,1,0) → inv(C,D)`, this
            // replaces Var(C) → A+1 and Var(D) → ite(...), enabling algebraic
            // mod resolution on body variables instead of head variables.
            let (head_i, head_j) = Self::substitute_modular_head_definitions(
                head_args,
                head_i_raw,
                head_j_raw,
                &clause_constraint,
            );
            let request = ModularClauseQuery {
                domain,
                body_i,
                body_j,
                head_i: &head_i,
                head_j: &head_j,
                constraint: &clause_constraint,
                modulus: k,
                lhs_name: &canonical_vars[idx_i].name,
                rhs_name: &canonical_vars[idx_j].name,
            };

            // Enumerating every residue is effective for small k, but scales
            // linearly in both queries and formula rewrites.  Larger moduli
            // use one direct consecution query for this clause.  SAT and
            // Unknown both reject the candidate; only an UNSAT result admits
            // it, under the same cancellation and remaining-time checks.
            if k > MAX_CASE_SPLIT_MODULUS {
                if self.is_cancelled()
                    || discovery_start
                        .is_some_and(|start| start.elapsed() >= MODULAR_EQUALITY_DISCOVERY_BUDGET)
                {
                    return false;
                }
                if !Self::large_modular_equality_clause_preserved(
                    &mut self.smt,
                    self.config.verbose,
                    &request,
                    discovery_start,
                ) {
                    return false;
                }
                continue;
            }

            // Case-split on possible remainder values to avoid mod+LIA
            // incompleteness (#3211). The LIA solver can return Unknown on
            // formulas with mod-elimination auxiliary variables (euclidean
            // decomposition creates unbounded quotient variables that cause
            // branch-and-bound to spiral). By grounding body_j to each
            // possible remainder value c ∈ {0, ..., k-1} and propagating
            // constants before check_sat, the formula simplifies enough
            // that the SMT solver handles it directly.
            let mut clause_preserved = true;
            for c in 0..k {
                if self.is_cancelled()
                    || discovery_start
                        .is_some_and(|start| start.elapsed() >= MODULAR_EQUALITY_DISCOVERY_BUDGET)
                {
                    return false;
                }
                let query_resolved = Self::modular_equality_case_query(&request, c);

                // Early exit: if constant propagation resolved to false,
                // this case is trivially UNSAT (e.g., body_j=1 contradicts
                // clause constraint B=0).
                if matches!(query_resolved, ChcExpr::Bool(false)) {
                    continue;
                }

                self.smt.reset();
                let timeout = discovery_start.map_or(MODULAR_EQUALITY_SMT_CALL_BUDGET, |start| {
                    MODULAR_EQUALITY_DISCOVERY_BUDGET.saturating_sub(start.elapsed())
                });
                if timeout.is_zero() {
                    return false;
                }
                match self.smt.check_sat_with_timeout(
                    &query_resolved,
                    timeout.min(MODULAR_EQUALITY_SMT_CALL_BUDGET),
                ) {
                    SmtResult::Sat(_) => {
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: Modular equality ({} mod {}) = {} NOT preserved (case c={})",
                                canonical_vars[idx_i].name,
                                k,
                                canonical_vars[idx_j].name,
                                c
                            );
                        }
                        clause_preserved = false;
                        break;
                    }
                    SmtResult::Unsat
                    | SmtResult::UnsatWithCore(_)
                    | SmtResult::UnsatWithFarkas(_) => {
                        // This case is UNSAT - preservation holds for remainder=c
                    }
                    SmtResult::Unknown => {
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: Modular equality ({} mod {}) = {} Unknown (case c={})",
                                canonical_vars[idx_i].name,
                                k,
                                canonical_vars[idx_j].name,
                                c
                            );
                        }
                        clause_preserved = false;
                        break;
                    }
                }
            }
            if !clause_preserved {
                return false;
            }
        }

        self.finish_modular_preservation(checked_any_self_loop, &canonical_vars, idx_i, idx_j, k)
    }

    /// Resolve `(expr mod k)` subexpressions using a known modular residue (#1362).
    ///
    /// Given that `var_name mod k = known_residue`, replaces all occurrences of
    /// `((var_name + offset) mod k)` with the algebraically computed value
    /// `(known_residue + offset) rem_euclid k`. This avoids sending multiple mod
    /// operations to the LIA solver, which often returns Unknown on such formulas.
    ///
    /// Handles patterns:
    /// - `(var mod k)` → `known_residue`
    /// - `((var + offset) mod k)` → `(known_residue + offset) rem_euclid k`
    /// - `(((offset + var) mod k)` → same as above (commutative)
    fn resolve_mod_with_known_residue(
        expr: &ChcExpr,
        var_name: &str,
        k: i128,
        known_residue: i128,
    ) -> ChcExpr {
        Self::resolve_mod_inner(expr, var_name, k, known_residue, 0)
    }

    fn resolve_mod_inner(
        expr: &ChcExpr,
        var_name: &str,
        k: i128,
        known_residue: i128,
        depth: usize,
    ) -> ChcExpr {
        if depth >= 200 {
            return expr.clone();
        }
        match expr {
            ChcExpr::Op(ChcOp::Mod, args) if args.len() == 2 => {
                // Check if this is (something mod k)
                if let ChcExpr::Int(modulus) = args[1].as_ref() {
                    if *modulus == k {
                        // Try to extract the dividend as var_name + offset
                        if let Some(offset) = Self::extract_var_offset(args[0].as_ref(), var_name) {
                            // Algebraically compute the result
                            let result = (known_residue + offset).rem_euclid(k);
                            return ChcExpr::Int(result);
                        }
                    }
                }
                // Can't resolve — recurse into children
                let new_args: Vec<Arc<ChcExpr>> = args
                    .iter()
                    .map(|a| {
                        Arc::new(Self::resolve_mod_inner(
                            a,
                            var_name,
                            k,
                            known_residue,
                            depth + 1,
                        ))
                    })
                    .collect();
                ChcExpr::Op(ChcOp::Mod, new_args)
            }
            ChcExpr::Op(op, args) => {
                let new_args: Vec<Arc<ChcExpr>> = args
                    .iter()
                    .map(|a| {
                        Arc::new(Self::resolve_mod_inner(
                            a,
                            var_name,
                            k,
                            known_residue,
                            depth + 1,
                        ))
                    })
                    .collect();
                ChcExpr::Op(*op, new_args)
            }
            _ => expr.clone(),
        }
    }

    /// Extract the offset from an expression of the form `var + offset` or just `var`.
    ///
    /// Returns `Some(offset)` if `expr` is:
    /// - `Var(var_name)` → offset = 0
    /// - `Add(Var(var_name), Int(offset))` → offset
    /// - `Add(Int(offset), Var(var_name))` → offset
    /// - `Sub(Var(var_name), Int(offset))` → -offset
    /// - `Add(Var(var_name), Neg(Int(offset)))` → -offset
    fn extract_var_offset(expr: &ChcExpr, var_name: &str) -> Option<i128> {
        match expr {
            ChcExpr::Var(v) if v.name == var_name => Some(0),
            ChcExpr::Op(ChcOp::Add, args) if args.len() == 2 => {
                // (var + offset) or (offset + var)
                // Handles Op(Neg,[Int(n)]) via as_i128()
                if let ChcExpr::Var(v) = args[0].as_ref() {
                    if v.name == var_name {
                        return args[1].as_i128();
                    }
                }
                if let ChcExpr::Var(v) = args[1].as_ref() {
                    if v.name == var_name {
                        return args[0].as_i128();
                    }
                }
                None
            }
            ChcExpr::Op(ChcOp::Sub, args) if args.len() == 2 => {
                // (var - offset)
                if let ChcExpr::Var(v) = args[0].as_ref() {
                    if v.name == var_name {
                        return args[1].as_i128().and_then(i128::checked_neg);
                    }
                }
                None
            }
            _ => None,
        }
    }
}
