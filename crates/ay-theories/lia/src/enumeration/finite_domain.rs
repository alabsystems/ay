// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[derive(Clone, Debug)]
struct FiniteLinearExpr {
    coeffs: Vec<(usize, BigInt)>,
    constant: BigInt,
}

#[derive(Clone, Copy, Debug)]
enum FiniteCmp {
    Eq,
    Ne,
    Le,
    Lt,
    Ge,
    Gt,
}

#[derive(Clone, Debug)]
enum FiniteConstraint {
    Cmp(FiniteLinearExpr, FiniteCmp),
    AllDistinct(Vec<FiniteLinearExpr>),
}

/// A uninterpreted-function application registered as an opaque Int column,
/// used to Ackermannize congruence into the UFLIA finite-domain search
/// (`try_finite_domain_uflia`): `idx` is the application's own column in the
/// search assignment, `symbol` its function symbol, and `args` its argument
/// terms (evaluated on the fly under the current partial assignment).
#[derive(Clone, Debug)]
struct FdApp {
    idx: usize,
    symbol: String,
    args: Vec<TermId>,
}

impl LiaSolver<'_> {
    pub(crate) fn try_finite_domain_search(&mut self) -> DirectEnumResult {
        const MAX_FD_VARS: usize = 96;
        const MAX_FD_DOMAIN: usize = 16;
        const MAX_FD_ASSERTED_LITS: usize = 2_048;
        const MAX_FD_SEARCH_NODES: u64 = 2_000_000;

        let debug = self.debug_enum;
        self.direct_enum_witness = None;

        if self.integer_vars.is_empty()
            || self.integer_vars.len() > MAX_FD_VARS
            || self.asserted.len() > MAX_FD_ASSERTED_LITS
            || !self.shared_equalities.is_empty()
            // INTERFACE-DIET C4/R2 (empty-unlocks-Sat site): a withheld pure-UF=UF
            // equality means the empty `shared_equalities` is not the true
            // interface; a CSP witness over the arith projection could violate
            // the hidden equality (the false-SAT firewall). Fail-closed.
            || self.hidden_interface
        {
            return DirectEnumResult::NoConclusion;
        }

        let (term_to_idx, idx_to_term) = self.build_var_index();
        let Some(constraints) = self.collect_finite_domain_constraints(&term_to_idx) else {
            return DirectEnumResult::NoConclusion;
        };

        if constraints.is_empty() {
            return DirectEnumResult::NoConclusion;
        }

        // Synthesized-domain width for variables that lack a finite bound.
        //
        // The disequality-dense SAT shapes this path targets (pairwise
        // `(not (= ei ej))` / n-ary `distinct`, possibly over scaled or offset
        // expressions like `(* 2 x)` or `(+ x k)`) are satisfiable over the
        // integers by assigning sufficiently-spread distinct values. With every
        // variable free (no bounds), `build_finite_domain_domains` otherwise
        // bails to `NoConclusion`, forcing the formula into the exponential
        // LIA/LRA disequality split loop (combinatorial blowup → unknown/timeout
        // on ~12+ variables). Synthesizing a finite window for unbounded
        // variables lets the CSP search find a witness directly.
        //
        // Scope guard: synthesis is enabled ONLY when the constraint set is
        // actually disequality-dense — i.e. it contains an n-ary `distinct` or a
        // binary disequality (`!=`). Pure equality / inequality conjunctions are
        // left to fall through to the Diophantine / simplex solvers exactly as
        // before, so this change is a no-op for every non-disequality path
        // (e.g. solving `x = y` still routes through Dioph and populates its
        // caches). Width `0` disables synthesis inside
        // `build_finite_domain_domains`, restoring the bounded-only behaviour.
        //
        // Soundness: synthesis only ever helps *find* a SAT witness — it can
        // never produce a false UNSAT, because `try_finite_domain_search` never
        // returns `Unsat` (an exhausted/empty search yields `NoConclusion`, see
        // the `Some(true) = found else` arm below), and it can never produce a
        // false SAT, because every candidate witness is re-verified against ALL
        // asserted literals by `check_solution_satisfies_asserted` before
        // `SatWitness` is returned. If the synthesized window happens to be too
        // narrow for a satisfiable instance, the search simply finds no witness
        // and the normal solver runs unchanged.
        //
        // Width: a window of `n` distinct integer slots suffices to place `n`
        // pairwise-distinct values; offset/scaled disequalities only relabel
        // those slots, so the spread requirement is still bounded by the slot
        // count. Capped at `MAX_FD_DOMAIN` so the per-variable branching factor
        // (and total search) stays bounded.
        let is_disequality_dense = constraints.iter().any(|c| {
            matches!(
                c,
                FiniteConstraint::AllDistinct(_) | FiniteConstraint::Cmp(_, FiniteCmp::Ne)
            )
        });
        // Nonlinear/reification guard: a product/`div`/`mod` term (e.g. `n*n`)
        // is registered as an opaque LIA "variable" so the simplex can carry it
        // as a column, but its *definitional* constraint (`p = n*n`) lives
        // outside the linear `FiniteConstraint` set this search understands.
        // Synthesizing an independent finite domain for such a column would let
        // the CSP pick a `p` unrelated to `n*n`, and the witness re-check only
        // re-evaluates the asserted *linear* atoms — so the unsound assignment
        // could slip through (e.g. masking a genuine nonlinear conflict). Only
        // synthesize when EVERY indexed integer variable is an atomic declared
        // variable (`TermData::Var`); if any is a compound term, leave the
        // problem to the nonlinear / Diophantine paths by disabling synthesis.
        let all_vars_atomic = idx_to_term
            .iter()
            .all(|&t| matches!(self.terms.get(t), TermData::Var(_, _)));
        let synth_domain_width = if is_disequality_dense && all_vars_atomic {
            self.integer_vars.len().min(MAX_FD_DOMAIN)
        } else {
            0
        };
        let Some(domains) =
            self.build_finite_domain_domains(&term_to_idx, MAX_FD_DOMAIN, synth_domain_width)
        else {
            return DirectEnumResult::NoConclusion;
        };

        let mut assignment = vec![None; idx_to_term.len()];
        let mut nodes = 0u64;
        let found = self.search_finite_domain(
            &domains,
            &constraints,
            &mut assignment,
            &mut nodes,
            MAX_FD_SEARCH_NODES,
        );

        let Some(true) = found else {
            if debug {
                safe_eprintln!(
                    "[FD] finite-domain search no witness: nodes={}, budget={}",
                    nodes,
                    MAX_FD_SEARCH_NODES
                );
            }
            return DirectEnumResult::NoConclusion;
        };

        let solution: Vec<(usize, BigInt)> = assignment
            .into_iter()
            .enumerate()
            .filter_map(|(idx, value)| value.map(|v| (idx, v)))
            .collect();

        match self.check_solution_satisfies_asserted(&solution, &idx_to_term, debug) {
            Some(true) => {
                if debug {
                    safe_eprintln!("[FD] finite-domain search found SAT witness in {nodes} nodes");
                }
                self.direct_enum_witness = Some(Self::solution_to_model(&solution, &idx_to_term));
                DirectEnumResult::SatWitness
            }
            Some(false) | None => DirectEnumResult::NoConclusion,
        }
    }

    fn build_finite_domain_domains(
        &self,
        term_to_idx: &HashMap<TermId, usize>,
        max_domain: usize,
        synth_width: usize,
    ) -> Option<Vec<Vec<BigInt>>> {
        let mut lower: Vec<Option<BigInt>> = vec![None; term_to_idx.len()];
        let mut upper: Vec<Option<BigInt>> = vec![None; term_to_idx.len()];
        let view = self.assertion_view();

        for (&term, bounds) in &view.bounds_by_term {
            let Some(&idx) = term_to_idx.get(&term) else {
                continue;
            };
            if let Some(lb) = &bounds.lower {
                lower[idx] = Some(
                    lower[idx]
                        .as_ref()
                        .map_or_else(|| lb.clone(), |current| current.max(lb).clone()),
                );
            }
            if let Some(ub) = &bounds.upper {
                upper[idx] = Some(
                    upper[idx]
                        .as_ref()
                        .map_or_else(|| ub.clone(), |current| current.min(ub).clone()),
                );
            }
        }

        for &(literal, value) in &self.asserted {
            if !value {
                continue;
            }
            let TermData::App(Symbol::Named(name), args) = self.terms.get(literal) else {
                continue;
            };
            if name != "=" || args.len() != 2 {
                continue;
            }

            let fixed = term_to_idx
                .get(&args[0])
                .and_then(|&idx| {
                    self.terms
                        .extract_integer_constant(args[1])
                        .map(|c| (idx, c))
                })
                .or_else(|| {
                    term_to_idx.get(&args[1]).and_then(|&idx| {
                        self.terms
                            .extract_integer_constant(args[0])
                            .map(|c| (idx, c))
                    })
                });

            if let Some((idx, constant)) = fixed {
                lower[idx] = Some(lower[idx].as_ref().map_or_else(
                    || constant.clone(),
                    |current| current.max(&constant).clone(),
                ));
                upper[idx] = Some(upper[idx].as_ref().map_or_else(
                    || constant.clone(),
                    |current| current.min(&constant).clone(),
                ));
            }
        }

        let mut domains = Vec::with_capacity(term_to_idx.len());
        let max_span = BigInt::from(max_domain.saturating_sub(1));
        // Synthesized window size for unbounded sides, in number of slots.
        // `synth_width == 0` disables synthesis (every variable must already be
        // finitely bounded), preserving the legacy behaviour.
        let synth_slots = BigInt::from(synth_width.saturating_sub(1) as i64);
        for idx in 0..term_to_idx.len() {
            // Resolve a concrete `[lb, ub]` window for this variable.
            //
            // - Both bounds known: use them as-is (unchanged legacy path; a
            //   too-wide span still bails to `None` exactly as before).
            // - One bound known: synthesize the missing side `synth_width`
            //   slots away from the known one (upward from a lower bound,
            //   downward from an upper bound).
            // - Neither bound known: synthesize the window `[0, synth_width-1]`.
            //
            // Synthesis only ever expands which SAT witnesses the search may
            // discover; soundness is enforced downstream by
            // `check_solution_satisfies_asserted` and the never-UNSAT contract
            // of `try_finite_domain_search`.
            let (lb, ub) = match (lower[idx].as_ref(), upper[idx].as_ref()) {
                (Some(lb), Some(ub)) => (lb.clone(), ub.clone()),
                (Some(lb), None) => {
                    if synth_width == 0 {
                        return None;
                    }
                    let ub = lb + &synth_slots;
                    (lb.clone(), ub)
                }
                (None, Some(ub)) => {
                    if synth_width == 0 {
                        return None;
                    }
                    let lb = ub - &synth_slots;
                    (lb, ub.clone())
                }
                (None, None) => {
                    if synth_width == 0 {
                        return None;
                    }
                    (BigInt::zero(), synth_slots.clone())
                }
            };
            if lb > ub {
                return None;
            }
            let span = &ub - &lb;
            if span > max_span {
                return None;
            }

            let mut domain = Vec::new();
            let mut value = lb.clone();
            while value <= ub {
                domain.push(value.clone());
                value += BigInt::one();
            }
            if domain.is_empty() || domain.len() > max_domain {
                return None;
            }
            domains.push(domain);
        }

        Some(domains)
    }

    fn collect_finite_domain_constraints(
        &self,
        term_to_idx: &HashMap<TermId, usize>,
    ) -> Option<Vec<FiniteConstraint>> {
        let mut constraints = Vec::new();

        for &(literal, value) in &self.asserted {
            match self.terms.get(literal) {
                TermData::Const(Constant::Bool(b)) => {
                    if value != *b {
                        return None;
                    }
                }
                TermData::App(Symbol::Named(name), args) if name == "distinct" => {
                    if !value {
                        return None;
                    }
                    let mut exprs = Vec::with_capacity(args.len());
                    for &arg in args {
                        exprs.push(self.finite_linear_expr(arg, term_to_idx)?);
                    }
                    if exprs.len() > 1 {
                        constraints.push(FiniteConstraint::AllDistinct(exprs));
                    }
                }
                TermData::App(Symbol::Named(name), args) if args.len() == 2 => {
                    let cmp = match (name.as_str(), value) {
                        ("=", true) => FiniteCmp::Eq,
                        ("=", false) => FiniteCmp::Ne,
                        ("<=", true) => FiniteCmp::Le,
                        ("<=", false) => FiniteCmp::Gt,
                        ("<", true) => FiniteCmp::Lt,
                        ("<", false) => FiniteCmp::Ge,
                        (">=", true) => FiniteCmp::Ge,
                        (">=", false) => FiniteCmp::Lt,
                        (">", true) => FiniteCmp::Gt,
                        (">", false) => FiniteCmp::Le,
                        _ => return None,
                    };
                    let expr = self.finite_linear_difference(args[0], args[1], term_to_idx)?;
                    constraints.push(FiniteConstraint::Cmp(expr, cmp));
                }
                _ => return None,
            }
        }

        Some(constraints)
    }

    fn finite_linear_difference(
        &self,
        lhs: TermId,
        rhs: TermId,
        term_to_idx: &HashMap<TermId, usize>,
    ) -> Option<FiniteLinearExpr> {
        let mut coeffs = HashMap::default();
        let mut constant = BigInt::zero();
        self.collect_finite_linear_terms(
            lhs,
            &BigInt::one(),
            &mut coeffs,
            &mut constant,
            term_to_idx,
        )?;
        self.collect_finite_linear_terms(
            rhs,
            &-BigInt::one(),
            &mut coeffs,
            &mut constant,
            term_to_idx,
        )?;
        Some(Self::finish_finite_linear_expr(coeffs, constant))
    }

    fn finite_linear_expr(
        &self,
        term: TermId,
        term_to_idx: &HashMap<TermId, usize>,
    ) -> Option<FiniteLinearExpr> {
        let mut coeffs = HashMap::default();
        let mut constant = BigInt::zero();
        self.collect_finite_linear_terms(
            term,
            &BigInt::one(),
            &mut coeffs,
            &mut constant,
            term_to_idx,
        )?;
        Some(Self::finish_finite_linear_expr(coeffs, constant))
    }

    fn collect_finite_linear_terms(
        &self,
        term: TermId,
        scale: &BigInt,
        coeffs: &mut HashMap<usize, BigInt>,
        constant: &mut BigInt,
        term_to_idx: &HashMap<TermId, usize>,
    ) -> Option<()> {
        if let Some(&idx) = term_to_idx.get(&term) {
            *coeffs.entry(idx).or_insert_with(BigInt::zero) += scale;
            return Some(());
        }

        match self.terms.get(term) {
            TermData::Const(Constant::Int(n)) => {
                *constant += scale * n;
                Some(())
            }
            TermData::Const(Constant::Rational(r)) if r.0.denom().is_one() => {
                *constant += scale * r.0.numer();
                Some(())
            }
            TermData::App(Symbol::Named(name), args) => match name.as_str() {
                "+" => {
                    for &arg in args {
                        self.collect_finite_linear_terms(
                            arg,
                            scale,
                            coeffs,
                            constant,
                            term_to_idx,
                        )?;
                    }
                    Some(())
                }
                "-" if args.len() == 1 => self.collect_finite_linear_terms(
                    args[0],
                    &-scale.clone(),
                    coeffs,
                    constant,
                    term_to_idx,
                ),
                "-" if args.len() >= 2 => {
                    self.collect_finite_linear_terms(
                        args[0],
                        scale,
                        coeffs,
                        constant,
                        term_to_idx,
                    )?;
                    let neg_scale = -scale.clone();
                    for &arg in &args[1..] {
                        self.collect_finite_linear_terms(
                            arg,
                            &neg_scale,
                            coeffs,
                            constant,
                            term_to_idx,
                        )?;
                    }
                    Some(())
                }
                "*" => {
                    let mut const_factor = BigInt::one();
                    let mut non_const = None;
                    for &arg in args {
                        if let Some(c) = self.terms.extract_integer_constant(arg) {
                            const_factor *= c;
                        } else if non_const.replace(arg).is_some() {
                            return None;
                        }
                    }
                    let new_scale = scale * const_factor;
                    if let Some(arg) = non_const {
                        self.collect_finite_linear_terms(
                            arg,
                            &new_scale,
                            coeffs,
                            constant,
                            term_to_idx,
                        )
                    } else {
                        *constant += new_scale;
                        Some(())
                    }
                }
                _ => None,
            },
            _ => None,
        }
    }

    fn finish_finite_linear_expr(
        coeffs: HashMap<usize, BigInt>,
        constant: BigInt,
    ) -> FiniteLinearExpr {
        let mut coeffs: Vec<_> = coeffs.into_iter().filter(|(_, c)| !c.is_zero()).collect();
        coeffs.sort_by_key(|(idx, _)| *idx);
        FiniteLinearExpr { coeffs, constant }
    }

    fn search_finite_domain(
        &self,
        domains: &[Vec<BigInt>],
        constraints: &[FiniteConstraint],
        assignment: &mut [Option<BigInt>],
        nodes: &mut u64,
        max_nodes: u64,
    ) -> Option<bool> {
        if *nodes >= max_nodes || self.should_timeout() {
            return None;
        }

        if assignment.iter().all(Option::is_some) {
            return Some(constraints.iter().all(|constraint| {
                self.finite_constraint_possible(constraint, assignment, domains)
            }));
        }

        let mut best_idx = None;
        let mut best_candidates = Vec::new();
        for idx in 0..assignment.len() {
            if assignment[idx].is_some() {
                continue;
            }
            let mut candidates = Vec::new();
            for value in &domains[idx] {
                assignment[idx] = Some(value.clone());
                let possible = constraints.iter().all(|constraint| {
                    self.finite_constraint_possible(constraint, assignment, domains)
                });
                assignment[idx] = None;
                if possible {
                    candidates.push(value.clone());
                }
            }
            if candidates.is_empty() {
                return Some(false);
            }
            if best_idx.is_none() || candidates.len() < best_candidates.len() {
                best_idx = Some(idx);
                best_candidates = candidates;
                if best_candidates.len() == 1 {
                    break;
                }
            }
        }

        let idx = best_idx?;
        for value in best_candidates {
            *nodes += 1;
            assignment[idx] = Some(value);
            match self.search_finite_domain(domains, constraints, assignment, nodes, max_nodes) {
                Some(true) => return Some(true),
                None => {
                    assignment[idx] = None;
                    return None;
                }
                Some(false) => {}
            }
            assignment[idx] = None;
        }

        Some(false)
    }

    fn finite_constraint_possible(
        &self,
        constraint: &FiniteConstraint,
        assignment: &[Option<BigInt>],
        domains: &[Vec<BigInt>],
    ) -> bool {
        match constraint {
            FiniteConstraint::Cmp(expr, cmp) => {
                let (min, max, complete) = Self::finite_expr_range(expr, assignment, domains);
                match cmp {
                    FiniteCmp::Eq => min <= BigInt::zero() && max >= BigInt::zero(),
                    FiniteCmp::Ne => !complete || min != BigInt::zero(),
                    FiniteCmp::Le => min <= BigInt::zero(),
                    FiniteCmp::Lt => min < BigInt::zero(),
                    FiniteCmp::Ge => max >= BigInt::zero(),
                    FiniteCmp::Gt => max > BigInt::zero(),
                }
            }
            FiniteConstraint::AllDistinct(exprs) => {
                let mut seen = HashSet::default();
                for expr in exprs {
                    let Some(value) = Self::finite_eval_complete(expr, assignment) else {
                        continue;
                    };
                    if !seen.insert(value) {
                        return false;
                    }
                }
                true
            }
        }
    }

    fn finite_expr_range(
        expr: &FiniteLinearExpr,
        assignment: &[Option<BigInt>],
        domains: &[Vec<BigInt>],
    ) -> (BigInt, BigInt, bool) {
        let mut min = expr.constant.clone();
        let mut max = expr.constant.clone();
        let mut complete = true;

        for (idx, coeff) in &expr.coeffs {
            if let Some(value) = &assignment[*idx] {
                let contribution = coeff * value;
                min += &contribution;
                max += contribution;
            } else {
                complete = false;
                let lo = domains[*idx]
                    .first()
                    .expect("finite domain must be non-empty");
                let hi = domains[*idx]
                    .last()
                    .expect("finite domain must be non-empty");
                if coeff.is_negative() {
                    min += coeff * hi;
                    max += coeff * lo;
                } else {
                    min += coeff * lo;
                    max += coeff * hi;
                }
            }
        }

        (min, max, complete)
    }

    fn finite_eval_complete(
        expr: &FiniteLinearExpr,
        assignment: &[Option<BigInt>],
    ) -> Option<BigInt> {
        let mut value = expr.constant.clone();
        for (idx, coeff) in &expr.coeffs {
            value += coeff * assignment[*idx].as_ref()?;
        }
        Some(value)
    }

    // ------------------------------------------------------------------
    // UFLIA finite-domain model finder (Nelson-Oppen / shared equalities).
    // ------------------------------------------------------------------

    /// Finite-domain congruence-consistent model finder for the UFLIA
    /// (`shared_equalities` present) setting. **Combiner-invoked only** — it is
    /// deliberately NOT called from `check()` (returning a tight finite-domain
    /// model as a theory-`Sat` there floods the combiner's model-based
    /// interface-equality discovery `discover_model_eq`, a proven net-negative).
    /// Instead the combiner calls this as a *rescue* at its accept point, after
    /// the split-based congruence repair is exhausted, to obtain a
    /// congruence-consistent candidate model that the class-based
    /// materialization missed.
    ///
    /// It enumerates the finite domain of every integer column WITH UF
    /// congruence Ackermannized in: for each pair of same-symbol applications
    /// whose argument values coincide under the enumerated assignment, their
    /// result values are forced equal. On success the witness is stored in
    /// `direct_enum_witness` (so `extract_model` returns it) and `true` is
    /// returned; otherwise `direct_enum_witness` is left cleared and `false` is
    /// returned.
    ///
    /// SOUNDNESS. NEVER proves UNSAT — the finite box is used only to FIND a
    /// witness. The returned witness satisfies EVERY asserted literal
    /// (`check_solution_satisfies_asserted`), every shared equality, and UF
    /// congruence over the registered application columns; it is a genuine
    /// LIA+congruence model. It still flows through the combiner's
    /// materialization and the always-on independent gate unchanged — this path
    /// never weakens any gate, so the worst case is a fail-closed `unknown`.
    #[must_use]
    pub fn try_finite_domain_uflia(&mut self) -> bool {
        // Var-count cap is generous: the true branching factor is bounded by
        // `MAX_FD_FREE_CLASSES` (equality-classes with a non-singleton domain),
        // not the raw column count, and UFLIA problems carry many pinned UF
        // application columns (e.g. the Hash family has ~10 free vars but 80+
        // app columns). The node budget + `should_timeout` keep it bounded.
        const MAX_FD_VARS: usize = 384;
        const MAX_FD_DOMAIN: usize = 16;
        const MAX_FD_ASSERTED_LITS: usize = 8_192;
        const MAX_FD_FREE_CLASSES: usize = 16;
        const MAX_FD_SEARCH_NODES: u64 = 2_000_000;
        const MAX_FD_APPS: usize = 512;

        self.direct_enum_witness = None;
        let debug = self.debug_enum;

        if self.shared_equalities.is_empty()
            || self.integer_vars.is_empty()
            || self.integer_vars.len() > MAX_FD_VARS
            || self.asserted.len() > MAX_FD_ASSERTED_LITS
            // INTERFACE-DIET C4/R2 (explicit disable): the uflia congruence
            // rescue Ackermannizes `shared_equalities` into a witness, but under
            // a hidden interface that set is incomplete, so the witness could
            // violate a withheld equality. Never install such a witness.
            || self.hidden_interface
        {
            return false;
        }

        let (term_to_idx, idx_to_term) = self.build_var_index();

        // UF-application columns (opaque Int apps with a non-arithmetic
        // symbol). Without at least one, this is a pure-LIA problem covered by
        // the shared-eq-free path.
        let apps = self.collect_fd_apps(&idx_to_term);
        if apps.is_empty() || apps.len() > MAX_FD_APPS {
            return false;
        }

        let Some(mut constraints) = self.collect_finite_domain_constraints(&term_to_idx) else {
            return false;
        };
        // Shared (Nelson-Oppen) equalities become hard Eq constraints so the
        // witness respects what EUF has already derived.
        for (lhs, rhs, _reasons) in &self.shared_equalities {
            let Some(expr) = self.finite_linear_difference(*lhs, *rhs, &term_to_idx) else {
                return false;
            };
            constraints.push(FiniteConstraint::Cmp(expr, FiniteCmp::Eq));
        }
        if constraints.is_empty() {
            return false;
        }

        // Domains: bounds propagated across asserted/shared equalities, with a
        // synthesized window for still-unbounded application columns.
        let Some(domains) = self.build_uflia_domains(&term_to_idx, MAX_FD_DOMAIN) else {
            return false;
        };

        // Branching guard: only equality-classes whose domain is not a
        // singleton drive search cost. Bail when too many so this stays bounded.
        if self.count_free_fd_classes(&term_to_idx, &domains) > MAX_FD_FREE_CLASSES {
            return false;
        }

        let mut assignment = vec![None; idx_to_term.len()];
        let mut nodes = 0u64;
        let found = self.search_uflia_domain(
            &domains,
            &constraints,
            &apps,
            &term_to_idx,
            &mut assignment,
            &mut nodes,
            MAX_FD_SEARCH_NODES,
        );

        let Some(true) = found else {
            if debug {
                safe_eprintln!(
                    "[FD] uflia finite-domain rescue: no witness (nodes={}, budget={})",
                    nodes,
                    MAX_FD_SEARCH_NODES
                );
            }
            return false;
        };

        let solution: Vec<(usize, BigInt)> = assignment
            .into_iter()
            .enumerate()
            .filter_map(|(idx, value)| value.map(|v| (idx, v)))
            .collect();

        match self.check_solution_satisfies_asserted(&solution, &idx_to_term, debug) {
            Some(true) => {
                if debug {
                    safe_eprintln!(
                        "[FD] uflia finite-domain rescue SAT witness in {nodes} nodes ({} apps)",
                        apps.len()
                    );
                }
                self.direct_enum_witness = Some(Self::solution_to_model(&solution, &idx_to_term));
                true
            }
            Some(false) | None => false,
        }
    }

    /// Symbols the linear parser decomposes rather than treats as opaque
    /// functions — congruence does not apply to these (`+`/`-`/`*` are handled
    /// structurally; comparisons/`ite`/`distinct` are not function columns).
    fn is_fd_arith_symbol(name: &str) -> bool {
        matches!(
            name,
            "+" | "-" | "*" | "distinct" | "=" | "<" | "<=" | ">" | ">=" | "ite"
        )
    }

    /// Gather the UF-application columns among the indexed integer variables.
    fn collect_fd_apps(&self, idx_to_term: &[TermId]) -> Vec<FdApp> {
        let mut apps = Vec::new();
        for (idx, &term) in idx_to_term.iter().enumerate() {
            if let TermData::App(Symbol::Named(name), args) = self.terms.get(term) {
                if Self::is_fd_arith_symbol(name) {
                    continue;
                }
                apps.push(FdApp {
                    idx,
                    symbol: name.clone(),
                    args: args.clone(),
                });
            }
        }
        apps
    }

    /// Equality edges between integer columns: positive asserted `= a b` and
    /// the Nelson-Oppen shared equalities, restricted to pairs where BOTH sides
    /// are indexed columns.
    fn collect_fd_equality_edges(
        &self,
        term_to_idx: &HashMap<TermId, usize>,
    ) -> Vec<(usize, usize)> {
        let mut edges = Vec::new();
        for &(literal, value) in &self.asserted {
            if !value {
                continue;
            }
            if let TermData::App(Symbol::Named(name), args) = self.terms.get(literal) {
                if name == "=" && args.len() == 2 {
                    if let (Some(&a), Some(&b)) =
                        (term_to_idx.get(&args[0]), term_to_idx.get(&args[1]))
                    {
                        edges.push((a, b));
                    }
                }
            }
        }
        for (lhs, rhs, _reasons) in &self.shared_equalities {
            if let (Some(&a), Some(&b)) = (term_to_idx.get(lhs), term_to_idx.get(rhs)) {
                edges.push((a, b));
            }
        }
        edges
    }

    /// Build a finite domain for each integer column.
    ///
    /// Bounds come from the LRA assertion view and `var = constant` literals,
    /// then are propagated to a fixpoint across equality edges (equal columns
    /// share the tightest interval). Columns still lacking a bound (e.g. the
    /// intermediate applications of a nested `f(f(g(..)))` chain) are given a
    /// synthesized window equal to the globally-observed bounded range, so the
    /// search can place them on the same finite lattice as the bounded columns
    /// and let congruence tie them down. Returns `None` (bail to the ordinary
    /// solver) if no column is bounded, if an interval is empty, or if any
    /// two-sided interval is wider than `max_domain`.
    fn build_uflia_domains(
        &self,
        term_to_idx: &HashMap<TermId, usize>,
        max_domain: usize,
    ) -> Option<Vec<Vec<BigInt>>> {
        let n = term_to_idx.len();
        let mut lower: Vec<Option<BigInt>> = vec![None; n];
        let mut upper: Vec<Option<BigInt>> = vec![None; n];

        let view = self.assertion_view();
        for (&term, bounds) in &view.bounds_by_term {
            let Some(&idx) = term_to_idx.get(&term) else {
                continue;
            };
            if let Some(lb) = &bounds.lower {
                lower[idx] = Some(
                    lower[idx]
                        .as_ref()
                        .map_or_else(|| lb.clone(), |cur| cur.max(lb).clone()),
                );
            }
            if let Some(ub) = &bounds.upper {
                upper[idx] = Some(
                    upper[idx]
                        .as_ref()
                        .map_or_else(|| ub.clone(), |cur| cur.min(ub).clone()),
                );
            }
        }

        for &(literal, value) in &self.asserted {
            if !value {
                continue;
            }
            let TermData::App(Symbol::Named(name), args) = self.terms.get(literal) else {
                continue;
            };
            if name != "=" || args.len() != 2 {
                continue;
            }
            let fixed = term_to_idx
                .get(&args[0])
                .and_then(|&idx| {
                    self.terms
                        .extract_integer_constant(args[1])
                        .map(|c| (idx, c))
                })
                .or_else(|| {
                    term_to_idx.get(&args[1]).and_then(|&idx| {
                        self.terms
                            .extract_integer_constant(args[0])
                            .map(|c| (idx, c))
                    })
                });
            if let Some((idx, constant)) = fixed {
                lower[idx] = Some(
                    lower[idx]
                        .as_ref()
                        .map_or_else(|| constant.clone(), |cur| cur.max(&constant).clone()),
                );
                upper[idx] = Some(
                    upper[idx]
                        .as_ref()
                        .map_or_else(|| constant.clone(), |cur| cur.min(&constant).clone()),
                );
            }
        }

        // Propagate bounds across equality edges to a fixpoint.
        let edges = self.collect_fd_equality_edges(term_to_idx);
        loop {
            let mut changed = false;
            for &(a, b) in &edges {
                // Lower: both sides adopt the larger lower bound.
                let new_lo = match (lower[a].as_ref(), lower[b].as_ref()) {
                    (Some(x), Some(y)) => Some(x.max(y).clone()),
                    (Some(x), None) => Some(x.clone()),
                    (None, Some(y)) => Some(y.clone()),
                    (None, None) => None,
                };
                if let Some(v) = new_lo {
                    if lower[a].as_ref() != Some(&v) {
                        lower[a] = Some(v.clone());
                        changed = true;
                    }
                    if lower[b].as_ref() != Some(&v) {
                        lower[b] = Some(v);
                        changed = true;
                    }
                }
                // Upper: both sides adopt the smaller upper bound.
                let new_hi = match (upper[a].as_ref(), upper[b].as_ref()) {
                    (Some(x), Some(y)) => Some(x.min(y).clone()),
                    (Some(x), None) => Some(x.clone()),
                    (None, Some(y)) => Some(y.clone()),
                    (None, None) => None,
                };
                if let Some(v) = new_hi {
                    if upper[a].as_ref() != Some(&v) {
                        upper[a] = Some(v.clone());
                        changed = true;
                    }
                    if upper[b].as_ref() != Some(&v) {
                        upper[b] = Some(v);
                        changed = true;
                    }
                }
            }
            if !changed {
                break;
            }
        }

        // Global window for still-unbounded columns.
        let gmin = lower.iter().flatten().min().cloned();
        let gmax = upper.iter().flatten().max().cloned();
        let (Some(gmin), Some(gmax)) = (gmin, gmax) else {
            // No column is bounded — not a finite-domain problem.
            return None;
        };
        let max_span = BigInt::from(max_domain.saturating_sub(1));
        // Clamp the synthesized window width to `max_domain`.
        let whi = {
            let span = &gmax - &gmin;
            if span > max_span {
                &gmin + &max_span
            } else {
                gmax.clone()
            }
        };

        let mut domains = Vec::with_capacity(n);
        for idx in 0..n {
            let lb = lower[idx].clone().unwrap_or_else(|| gmin.clone());
            let ub = upper[idx].clone().unwrap_or_else(|| whi.clone());
            if lb > ub {
                return None;
            }
            let span = &ub - &lb;
            if span > max_span {
                return None;
            }
            let mut domain = Vec::new();
            let mut value = lb.clone();
            while value <= ub {
                domain.push(value.clone());
                value += BigInt::one();
            }
            if domain.is_empty() || domain.len() > max_domain {
                return None;
            }
            domains.push(domain);
        }
        Some(domains)
    }

    /// Count the equality-classes (under `collect_fd_equality_edges`) that
    /// still have a non-singleton domain — the true branching factor of the
    /// search. Pinned classes (singleton domains) cost nothing.
    fn count_free_fd_classes(
        &self,
        term_to_idx: &HashMap<TermId, usize>,
        domains: &[Vec<BigInt>],
    ) -> usize {
        let n = domains.len();
        let mut parent: Vec<usize> = (0..n).collect();
        fn find(parent: &mut [usize], mut x: usize) -> usize {
            while parent[x] != x {
                parent[x] = parent[parent[x]];
                x = parent[x];
            }
            x
        }
        for (a, b) in self.collect_fd_equality_edges(term_to_idx) {
            let ra = find(&mut parent, a);
            let rb = find(&mut parent, b);
            if ra != rb {
                parent[ra] = rb;
            }
        }
        let mut reps: HashSet<usize> = HashSet::default();
        for i in 0..n {
            if domains[i].len() > 1 {
                let r = find(&mut parent, i);
                reps.insert(r);
            }
        }
        reps.len()
    }

    /// Backtracking search over `domains` satisfying the linear `constraints`
    /// AND UF congruence over `apps`. Mirrors `search_finite_domain` (MRV
    /// forward-checking over the linear constraints) but prunes each committed
    /// assignment against congruence before recursing, and checks congruence at
    /// every complete assignment. Never blocks: honours the node budget and the
    /// global timeout (returning `None`).
    #[allow(clippy::too_many_arguments)]
    fn search_uflia_domain(
        &self,
        domains: &[Vec<BigInt>],
        constraints: &[FiniteConstraint],
        apps: &[FdApp],
        term_to_idx: &HashMap<TermId, usize>,
        assignment: &mut [Option<BigInt>],
        nodes: &mut u64,
        max_nodes: u64,
    ) -> Option<bool> {
        if *nodes >= max_nodes || self.should_timeout() {
            return None;
        }

        if assignment.iter().all(Option::is_some) {
            let ok = constraints
                .iter()
                .all(|c| self.finite_constraint_possible(c, assignment, domains))
                && self.uflia_congruence_ok(apps, assignment, term_to_idx);
            return Some(ok);
        }

        let mut best_idx = None;
        let mut best_candidates = Vec::new();
        for idx in 0..assignment.len() {
            if assignment[idx].is_some() {
                continue;
            }
            let mut candidates = Vec::new();
            for value in &domains[idx] {
                assignment[idx] = Some(value.clone());
                let possible = constraints
                    .iter()
                    .all(|c| self.finite_constraint_possible(c, assignment, domains));
                assignment[idx] = None;
                if possible {
                    candidates.push(value.clone());
                }
            }
            if candidates.is_empty() {
                return Some(false);
            }
            if best_idx.is_none() || candidates.len() < best_candidates.len() {
                best_idx = Some(idx);
                best_candidates = candidates;
                if best_candidates.len() == 1 {
                    break;
                }
            }
        }

        let idx = best_idx?;
        for value in best_candidates {
            *nodes += 1;
            assignment[idx] = Some(value);
            // Prune the committed partial assignment against congruence before
            // descending (keeps the free application chains from exploding).
            if self.uflia_congruence_ok(apps, assignment, term_to_idx) {
                match self.search_uflia_domain(
                    domains,
                    constraints,
                    apps,
                    term_to_idx,
                    assignment,
                    nodes,
                    max_nodes,
                ) {
                    Some(true) => return Some(true),
                    None => {
                        assignment[idx] = None;
                        return None;
                    }
                    Some(false) => {}
                }
            }
            assignment[idx] = None;
        }

        Some(false)
    }

    /// Congruence check over `apps` at the current (partial) assignment: any two
    /// same-symbol applications whose arguments ALL evaluate to equal values
    /// must share the same result value. Applications whose value or any
    /// argument is not yet evaluable are skipped (checked once enough is
    /// assigned). A violation returns `false`.
    fn uflia_congruence_ok(
        &self,
        apps: &[FdApp],
        assignment: &[Option<BigInt>],
        term_to_idx: &HashMap<TermId, usize>,
    ) -> bool {
        let mut buckets: HashMap<(String, Vec<BigInt>), BigInt> = HashMap::default();
        for app in apps {
            let Some(val) = assignment[app.idx].as_ref() else {
                continue;
            };
            let mut argvals = Vec::with_capacity(app.args.len());
            let mut evaluable = true;
            for &arg in &app.args {
                match self.fd_eval_int(arg, assignment, term_to_idx) {
                    Some(v) => argvals.push(v),
                    None => {
                        evaluable = false;
                        break;
                    }
                }
            }
            if !evaluable {
                continue;
            }
            let key = (app.symbol.clone(), argvals);
            match buckets.get(&key) {
                Some(existing) if existing != val => return false,
                Some(_) => {}
                None => {
                    buckets.insert(key, val.clone());
                }
            }
        }
        true
    }

    /// Evaluate an integer term under the current partial assignment. Columns
    /// resolve to their assigned value (or `None` if unassigned); constants,
    /// linear `+`/`-`/`*` combinations and `ite` are computed structurally;
    /// anything else (an opaque application not indexed as a column) is `None`.
    fn fd_eval_int(
        &self,
        term: TermId,
        assignment: &[Option<BigInt>],
        term_to_idx: &HashMap<TermId, usize>,
    ) -> Option<BigInt> {
        if let Some(&idx) = term_to_idx.get(&term) {
            return assignment[idx].clone();
        }
        match self.terms.get(term) {
            TermData::Const(Constant::Int(n)) => Some(n.clone()),
            TermData::Const(Constant::Rational(r)) if r.0.denom().is_one() => {
                Some(r.0.numer().clone())
            }
            TermData::Ite(cond, then_branch, else_branch) => {
                if self.fd_eval_bool(*cond, assignment, term_to_idx)? {
                    self.fd_eval_int(*then_branch, assignment, term_to_idx)
                } else {
                    self.fd_eval_int(*else_branch, assignment, term_to_idx)
                }
            }
            TermData::App(Symbol::Named(name), args) => match name.as_str() {
                "+" => {
                    let mut sum = BigInt::zero();
                    for &arg in args {
                        sum += self.fd_eval_int(arg, assignment, term_to_idx)?;
                    }
                    Some(sum)
                }
                "-" if args.len() == 1 => {
                    Some(-self.fd_eval_int(args[0], assignment, term_to_idx)?)
                }
                "-" if args.len() >= 2 => {
                    let mut result = self.fd_eval_int(args[0], assignment, term_to_idx)?;
                    for &arg in &args[1..] {
                        result -= self.fd_eval_int(arg, assignment, term_to_idx)?;
                    }
                    Some(result)
                }
                "*" => {
                    let mut product = BigInt::one();
                    for &arg in args {
                        product *= self.fd_eval_int(arg, assignment, term_to_idx)?;
                    }
                    Some(product)
                }
                _ => None,
            },
            _ => None,
        }
    }

    /// Evaluate a boolean term (an `ite` condition) under the current partial
    /// assignment. Supports integer comparisons, `and`/`or`/`not`, and boolean
    /// constants; returns `None` when not evaluable.
    fn fd_eval_bool(
        &self,
        term: TermId,
        assignment: &[Option<BigInt>],
        term_to_idx: &HashMap<TermId, usize>,
    ) -> Option<bool> {
        match self.terms.get(term) {
            TermData::Const(Constant::Bool(b)) => Some(*b),
            TermData::Not(inner) => Some(!self.fd_eval_bool(*inner, assignment, term_to_idx)?),
            TermData::App(Symbol::Named(name), args) => match name.as_str() {
                "not" if args.len() == 1 => {
                    Some(!self.fd_eval_bool(args[0], assignment, term_to_idx)?)
                }
                "and" => {
                    for &arg in args {
                        if !self.fd_eval_bool(arg, assignment, term_to_idx)? {
                            return Some(false);
                        }
                    }
                    Some(true)
                }
                "or" => {
                    for &arg in args {
                        if self.fd_eval_bool(arg, assignment, term_to_idx)? {
                            return Some(true);
                        }
                    }
                    Some(false)
                }
                "<" | "<=" | ">" | ">=" | "=" if args.len() == 2 => {
                    let lhs = self.fd_eval_int(args[0], assignment, term_to_idx)?;
                    let rhs = self.fd_eval_int(args[1], assignment, term_to_idx)?;
                    Some(match name.as_str() {
                        "<" => lhs < rhs,
                        "<=" => lhs <= rhs,
                        ">" => lhs > rhs,
                        ">=" => lhs >= rhs,
                        "=" => lhs == rhs,
                        _ => unreachable!(),
                    })
                }
                _ => None,
            },
            _ => None,
        }
    }
}
