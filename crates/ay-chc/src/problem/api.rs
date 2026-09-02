// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

const MAX_DATATYPE_FEATURE_SYMBOLS: usize = 32_768;
const MAX_DATATYPE_FEATURE_NAME_BYTES: usize = 1024 * 1024;
const MAX_DATATYPE_FEATURE_EXPR_NODES: usize = 1_000_000;
const MAX_DATATYPE_FEATURE_SORT_NODES: usize = 32_768;

impl ChcProblem {
    /// Create a new empty CHC problem
    pub fn new() -> Self {
        Self {
            predicates: Vec::new(),
            predicate_names: FxHashMap::default(),
            clauses: Vec::new(),
            pruned_false_queries: 0,
            fixedpoint_format: false,
            stripped_body_forall: false,
            datatype_defs: FxHashMap::default(),
            action_names: Vec::new(),
        }
    }

    /// Declare a new predicate
    pub fn declare_predicate(
        &mut self,
        name: impl Into<String>,
        arg_sorts: Vec<ChcSort>,
    ) -> PredicateId {
        let name = name.into();
        let id = PredicateId::new(self.predicates.len() as u32);
        let pred = Predicate::new(id, name.clone(), arg_sorts);
        self.predicates.push(pred);
        self.predicate_names.insert(name, id);
        id
    }

    /// Get a predicate by ID
    pub fn get_predicate(&self, id: PredicateId) -> Option<&Predicate> {
        self.predicates.get(id.index())
    }

    /// Get a predicate by name
    pub fn get_predicate_by_name(&self, name: &str) -> Option<&Predicate> {
        self.predicate_names
            .get(name)
            .and_then(|id| self.predicates.get(id.index()))
    }

    /// Look up predicate ID by name
    pub fn lookup_predicate(&self, name: &str) -> Option<PredicateId> {
        self.predicate_names.get(name).copied()
    }

    /// Add a Horn clause
    pub fn add_clause(&mut self, clause: HornClause) {
        if let Some(clause) = self.simplify_clause_body_constants(clause) {
            self.clauses.push(clause);
        }
    }

    /// Split the active safety queries into exact independent obligations.
    ///
    /// Each returned problem contains exactly one false-head query and only
    /// predicate definitions in that query's backwards dependency cone.  For
    /// the common fixedpoint encoding
    ///
    /// ```text
    /// error_p0 => error
    /// error_p1 => error
    /// error => false
    /// ```
    ///
    /// the nullary `error` marker is unfolded one level, producing separate
    /// `error_p0 => false` and `error_p1 => false` problems.  This is an exact
    /// least-fixed-point equivalence: the source problem is Safe iff every
    /// returned obligation is Safe, and it is Unsafe if any returned
    /// obligation is Unsafe.
    ///
    /// Queries previously removed because their body simplified to `false`
    /// are already vacuously Safe and have no surviving clause identity, so
    /// they are not returned.  Such a validated problem returns `Ok([])`.
    /// Invalid input, including a problem that never had a query, returns its
    /// typed [`ChcError`](crate::ChcError) instead of an ambiguous empty list.
    pub fn query_obligations(&self) -> ChcResult<Vec<ChcQueryObligation>> {
        self.validate()?;

        let mut obligations = Vec::new();

        for (query_index, query) in self.clauses.iter().enumerate() {
            if !query.is_query() {
                continue;
            }

            let marker = match query.body.predicates.as_slice() {
                [(predicate, arguments)] if arguments.is_empty() => Some(*predicate),
                _ => None,
            };
            // A constrained marker query has variables quantified in a scope
            // separate from each defining clause.  Combining the two bodies
            // would require capture-avoiding alpha-renaming.  Keep it as one
            // direct obligation instead of risking a same-spelling collision.
            let definitions: Vec<(usize, &HornClause)> = if query.body.constraint.is_none() {
                marker
                    .map(|predicate| self.clauses_defining_with_index(predicate).collect())
                    .unwrap_or_default()
            } else {
                Vec::new()
            };

            if definitions.is_empty() {
                let label = marker
                    .and_then(|predicate| self.get_predicate(predicate))
                    .map_or_else(
                        || format!("query_{query_index}"),
                        |predicate| predicate.name.clone(),
                    );
                obligations.push(self.build_query_obligation(
                    query_index,
                    None,
                    label,
                    query.clone(),
                ));
                continue;
            }

            let Some(marker) = marker else {
                continue;
            };
            for (definition_index, definition) in definitions {
                let direct_query = HornClause::query(ClauseBody {
                    predicates: definition.body.predicates.clone(),
                    constraint: Self::conjoin_optional_constraints(
                        definition.body.constraint.clone(),
                        query.body.constraint.clone(),
                    ),
                });
                let label =
                    Self::query_obligation_label(self, &direct_query, marker, definition_index);
                obligations.push(self.build_query_obligation(
                    query_index,
                    Some(definition_index),
                    label,
                    direct_query,
                ));
            }
        }

        Ok(obligations)
    }

    fn build_query_obligation(
        &self,
        query_clause_index: usize,
        defining_clause_index: Option<usize>,
        label: String,
        query: HornClause,
    ) -> ChcQueryObligation {
        let constraint_only = query.body.predicates.is_empty();
        let mut problem = self.clone();
        problem.clauses.retain(|clause| !clause.is_query());
        problem.pruned_false_queries = 0;
        problem.clauses.push(query);

        // Backwards slicing is verdict-preserving: every predicate used by a
        // retained definition also lies in the cone, while a definition whose
        // head is outside the cone cannot contribute to this query.
        // A constraint-only query has an empty predicate cone, so no predicate
        // definition can affect its truth; retain only the query itself.  The
        // general analysis intentionally returns `None` for this case because
        // its other callers use `None` as a fail-closed signal.
        if constraint_only {
            problem.clauses.retain(HornClause::is_query);
        } else if let Some(cone) = problem.query_cone_of_influence() {
            problem.clauses.retain(|clause| {
                clause.is_query()
                    || clause
                        .head
                        .predicate_id()
                        .is_some_and(|predicate| cone.contains(&predicate))
            });
        }

        let content_sha256 = problem.normalized_input_sha256();

        ChcQueryObligation {
            id: ChcQueryObligationId {
                query_clause_index,
                defining_clause_index,
                label,
                content_sha256,
            },
            problem,
        }
    }

    fn conjoin_optional_constraints(
        left: Option<ChcExpr>,
        right: Option<ChcExpr>,
    ) -> Option<ChcExpr> {
        match (left, right) {
            (Some(left), Some(right)) => Some(ChcExpr::and(left, right)),
            (Some(constraint), None) | (None, Some(constraint)) => Some(constraint),
            (None, None) => None,
        }
    }

    fn query_obligation_label(
        problem: &Self,
        query: &HornClause,
        marker: PredicateId,
        defining_clause_index: usize,
    ) -> String {
        if let [(predicate, arguments)] = query.body.predicates.as_slice() {
            if arguments.is_empty() {
                if let Some(predicate) = problem.get_predicate(*predicate) {
                    return predicate.name.clone();
                }
            }
        }

        let marker = problem
            .get_predicate(marker)
            .map_or("query", |predicate| predicate.name.as_str());
        format!("{marker}_definition_{defining_clause_index}")
    }

    /// Eliminate trivial 0-arity Bool "query marker" predicates (e.g. `fail`)
    /// by unfolding them into the goal (#9078).
    ///
    /// A predicate `M` with arity 0 that occurs ONLY as the sole body predicate
    /// of goal clauses `M ⇒ false` and in the heads of its own defining clauses
    /// `B_i ⇒ M` is removed by replacing each (goal, def) pair with the
    /// equivalent `B_i ∧ c_goal ⇒ false`. This rewrites the common
    /// `inv(x) ∧ φ ⇒ fail`, `fail ⇒ false` encoding (aeval / reve / llreve)
    /// into a single-predicate transition system, so SimpleLoop routing and the
    /// Houdini/PDR engines apply. `M`'s declaration is kept as a harmless orphan
    /// (PredicateId is a Vec index — removing it would renumber the others); it
    /// no longer appears in any clause. The unfold is an exact equivalence, so
    /// this is sound and verdict-preserving.
    pub(crate) fn eliminate_trivial_bool_markers(&mut self) {
        // Scoped to pure arithmetic (LIA/LRA) problems — the aeval/reve/llreve
        // target. The unfold is sound for any sort, but leaving BV/array/
        // datatype problems untouched avoids perturbing their (separately
        // tuned) routing and validation paths (#9078).
        if self.has_bv_sorts() || self.has_array_sorts() || self.has_datatype_sorts() {
            return;
        }
        // Only unfold when a real (arity > 0) transition-system predicate
        // exists. A problem whose ONLY predicate is the 0-arity marker is
        // query-only (e.g. a satisfiable datatype/array constraint ⇒ marker ⇒
        // false) and has its own dedicated handling — unfolding it there would
        // perturb that route. The aeval target always has the real `inv`.
        if !self.predicates.iter().any(|p| !p.arg_sorts.is_empty()) {
            return;
        }
        while let Some(mid) = self.find_trivial_bool_marker() {
            let mut goals: Vec<HornClause> = Vec::new();
            let mut defs: Vec<HornClause> = Vec::new();
            let mut rest: Vec<HornClause> = Vec::new();
            for cl in std::mem::take(&mut self.clauses) {
                if cl.head.predicate_id() == Some(mid) {
                    defs.push(cl);
                } else if cl.head.is_query()
                    && cl.body.predicates.len() == 1
                    && cl.body.predicates[0].0 == mid
                {
                    goals.push(cl);
                } else {
                    rest.push(cl);
                }
            }
            let mut new_clauses = rest;
            for goal in &goals {
                for def in &defs {
                    let constraint =
                        match (def.body.constraint.clone(), goal.body.constraint.clone()) {
                            (Some(a), Some(b)) => Some(ChcExpr::and(a, b)),
                            (Some(a), None) | (None, Some(a)) => Some(a),
                            (None, None) => None,
                        };
                    new_clauses.push(HornClause::new(
                        ClauseBody {
                            predicates: def.body.predicates.clone(),
                            constraint,
                        },
                        ClauseHead::False,
                    ));
                }
            }
            self.clauses = new_clauses;
        }
    }

    /// Find a 0-arity Bool predicate that occurs only as a goal marker
    /// (`M ⇒ false`, sole body predicate) and in its own defining-clause heads
    /// (`B ⇒ M`), with at least one of each — i.e. exactly unfoldable.
    fn find_trivial_bool_marker(&self) -> Option<PredicateId> {
        'preds: for p in &self.predicates {
            if !p.arg_sorts.is_empty() {
                continue;
            }
            let mid = p.id;
            let (mut has_def, mut has_goal) = (false, false);
            for cl in &self.clauses {
                let in_head = cl.head.predicate_id() == Some(mid);
                let body_uses = cl
                    .body
                    .predicates
                    .iter()
                    .filter(|(id, _)| *id == mid)
                    .count();
                if in_head {
                    if body_uses > 0 {
                        continue 'preds; // self-referential — not trivial
                    }
                    has_def = true;
                } else if body_uses > 0 {
                    // Only allowed: M as the sole body predicate of a goal.
                    if cl.head.is_query() && cl.body.predicates.len() == 1 {
                        has_goal = true;
                    } else {
                        continue 'preds;
                    }
                }
            }
            if has_def && has_goal {
                return Some(mid);
            }
        }
        None
    }

    /// Declare a named TLA+ action and return its identifier.
    ///
    /// Action names are used in counterexample traces and per-action invariant
    /// reports. Typical names come from the TLA+ spec: `"Send"`, `"Recv"`, etc.
    pub fn declare_action(&mut self, name: impl Into<String>) -> ActionId {
        let id = ActionId::new(self.action_names.len() as u32);
        self.action_names.push(name.into());
        id
    }

    /// Add a Horn clause tagged with a TLA+ action identifier.
    pub fn add_clause_with_action(&mut self, clause: HornClause, action: ActionId) {
        if let Some(clause) = self.simplify_clause_body_constants(clause.with_action(action)) {
            self.clauses.push(clause);
        }
    }

    fn simplify_clause_body_constants(&mut self, mut clause: HornClause) -> Option<HornClause> {
        let Some(constraint) = clause.body.constraint.take() else {
            return Some(clause);
        };

        let simplified = constraint.simplify_constants();
        if matches!(simplified, ChcExpr::Bool(false)) {
            if clause.is_query() {
                self.pruned_false_queries += 1;
            }
            return None;
        }
        clause.body.constraint = Some(simplified);
        Some(clause)
    }

    /// Get the human-readable name for an action, if declared.
    pub fn action_name(&self, id: ActionId) -> Option<&str> {
        self.action_names.get(id.index()).map(String::as_str)
    }

    /// Get all declared action names. Indexed by `ActionId`.
    pub fn action_names(&self) -> &[String] {
        &self.action_names
    }

    /// Whether this problem has a TLA+-style action decomposition.
    pub fn has_action_decomposition(&self) -> bool {
        !self.action_names.is_empty()
    }

    /// Get the action ID for a clause, if the clause has an action tag.
    pub fn clause_action(&self, clause_index: usize) -> Option<ActionId> {
        self.clauses.get(clause_index).and_then(|c| c.action_id)
    }

    /// Iteratively tear down owned clause expressions to avoid recursive Drop.
    pub(crate) fn iterative_drop(mut self) {
        for clause in self.clauses.drain(..) {
            clause.iterative_drop();
        }
    }

    /// Get all clauses
    pub fn clauses(&self) -> &[HornClause] {
        &self.clauses
    }

    /// Get mutable access to all clauses
    pub fn clauses_mut(&mut self) -> &mut [HornClause] {
        &mut self.clauses
    }

    /// Get all predicates
    pub fn predicates(&self) -> &[Predicate] {
        &self.predicates
    }

    /// Whether the input used Z3 fixedpoint format (declare-rel/rule/query).
    /// When true, the sat/unsat output polarity must be inverted:
    /// Safe => "unsat", Unsafe => "sat" (opposite of HORN convention).
    pub fn is_fixedpoint_format(&self) -> bool {
        self.fixedpoint_format
    }

    /// Mark this problem as using Z3 fixedpoint format.
    pub fn set_fixedpoint_format(&mut self) {
        self.fixedpoint_format = true;
    }

    /// True when a `forall` was stripped from a rule BODY, weakening the
    /// antecedent. Proofs remain valid; counterexamples do not.
    pub fn has_stripped_body_forall(&self) -> bool {
        self.stripped_body_forall
    }

    /// Record that a body-position `forall` was stripped (over-approximation).
    pub fn mark_stripped_body_forall(&mut self) {
        self.stripped_body_forall = true;
    }

    /// Datatype definitions from declare-datatype commands (#7016).
    /// Maps datatype name → Vec<(constructor_name, Vec<(selector_name, selector_sort)>)>.
    pub fn datatype_defs(&self) -> &FxHashMap<String, Vec<(String, Vec<(String, ChcSort)>)>> {
        &self.datatype_defs
    }

    /// Register a datatype definition parsed from declare-datatype (#7016).
    pub fn add_datatype_def(
        &mut self,
        name: String,
        constructors: Vec<(String, Vec<(String, ChcSort)>)>,
    ) {
        self.datatype_defs.insert(name, constructors);
    }

    /// Create an SmtContext pre-configured with this problem's DT definitions (#7016).
    pub fn make_smt_context(&self) -> crate::smt::SmtContext {
        let mut smt = crate::smt::SmtContext::new();
        if !self.datatype_defs.is_empty() {
            smt.set_datatype_defs(self.datatype_defs.clone());
        }
        smt
    }

    /// Whether any predicate has a BitVec-sorted argument (possibly nested
    /// inside a Datatype or Array sort).
    /// Used to skip pure QF_LIA assumptions in model verification
    /// (BV constraints are expected to produce Unknown from the LIA solver).
    pub fn has_bv_sorts(&self) -> bool {
        self.predicates
            .iter()
            .any(|p| p.arg_sorts.iter().any(Self::sort_contains_bitvec))
    }

    /// Maximum predicate arity if BvToBool bit-blasting were applied.
    /// Each `BitVec(w)` argument expands to `w` Bool arguments.
    /// Used to decide whether BvToBool arity explosion is too severe (#5877).
    pub fn max_bv_expanded_arity(&self) -> usize {
        self.predicates
            .iter()
            .map(|p| {
                p.arg_sorts
                    .iter()
                    .map(|s| match s {
                        ChcSort::BitVec(w) => *w as usize,
                        _ => 1,
                    })
                    .sum::<usize>()
            })
            .max()
            .unwrap_or(0)
    }

    /// Whether the problem contains BV operations that BvToInt cannot encode
    /// exactly (bitwise, shift, rotation, signed div/rem/mod).
    ///
    /// When false, BvToInt preserves full precision and BvToBool bit-blasting
    /// can be skipped to avoid predicate arity explosion. For example, a
    /// predicate with 10 BV32 arguments stays at arity 10 (as Int) instead of
    /// expanding to 320 Bool parameters (#5877).
    pub fn has_bv_bitwise_ops(&self) -> bool {
        self.clauses.iter().any(|clause| {
            // Check body constraint
            if let Some(c) = &clause.body.constraint {
                if c.contains_bv_bitwise_ops() {
                    return true;
                }
            }
            // Check body predicate arguments
            for (_, args) in &clause.body.predicates {
                for arg in args {
                    if arg.contains_bv_bitwise_ops() {
                        return true;
                    }
                }
            }
            // Check head predicate arguments
            if let ClauseHead::Predicate(_, args) = &clause.head {
                for arg in args {
                    if arg.contains_bv_bitwise_ops() {
                        return true;
                    }
                }
            }
            false
        })
    }

    /// Whether any predicate has an Array-sorted argument.
    /// Used to guard engines whose transition-system encodings only handle
    /// scalar predicate state.
    pub fn has_array_sorts(&self) -> bool {
        self.predicates
            .iter()
            .any(|p| p.arg_sorts.iter().any(Self::sort_contains_array))
    }

    fn sort_contains_array(sort: &ChcSort) -> bool {
        match sort {
            ChcSort::Array(_, _) => true,
            _ => false,
        }
    }

    /// Whether any predicate has a Real-sorted argument.
    /// Used to guard Kind deferred-safe and other paths that lack LRA model support.
    pub fn has_real_sorts(&self) -> bool {
        self.predicates
            .iter()
            .any(|p| p.arg_sorts.iter().any(Self::sort_contains_real))
    }

    fn sort_contains_real(sort: &ChcSort) -> bool {
        match sort {
            ChcSort::Real => true,
            ChcSort::Array(k, v) => Self::sort_contains_real(k) || Self::sort_contains_real(v),
            _ => false,
        }
    }

    /// Whether any predicate has a Datatype-sorted argument (#7930).
    /// Used to skip Kind engine and cap PDR escalation for DT+BV problems.
    pub fn has_datatype_sorts(&self) -> bool {
        let mut sort_nodes = 0usize;
        self.predicates.iter().any(|predicate| {
            predicate
                .arg_sorts
                .iter()
                .any(|sort| Self::sort_contains_datatype_bounded(sort, &mut sort_nodes))
        })
    }

    /// Whether the active predicate signature or clause terms use a declared
    /// algebraic datatype.
    ///
    /// This is deliberately more precise than `has_datatype_sorts()`: a Horn
    /// clause may bind a datatype only in its constraint while every predicate
    /// remains scalar. Conversely, MODEL_CHECKER_CONSUMER emits a reusable datatype prelude,
    /// so a declaration that is never referenced must not admit or suppress a
    /// datatype-specific engine.
    pub(crate) fn uses_datatype_features(&self) -> bool {
        if self.has_datatype_sorts() {
            return true;
        }

        let mut datatype_functions = FxHashSet::default();
        let mut datatype_constructors = FxHashSet::default();
        let mut symbol_count = 0usize;
        let mut name_bytes = 0usize;
        for constructors in self.datatype_defs.values() {
            for (constructor, selectors) in constructors {
                symbol_count = match symbol_count.checked_add(1) {
                    Some(count) if count <= MAX_DATATYPE_FEATURE_SYMBOLS => count,
                    _ => return true,
                };
                name_bytes = match name_bytes.checked_add(constructor.len()) {
                    Some(bytes) if bytes <= MAX_DATATYPE_FEATURE_NAME_BYTES => bytes,
                    _ => return true,
                };
                datatype_functions.insert(constructor.as_str());
                datatype_constructors.insert(constructor.as_str());
                for (selector, _) in selectors {
                    symbol_count = match symbol_count.checked_add(1) {
                        Some(count) if count <= MAX_DATATYPE_FEATURE_SYMBOLS => count,
                        _ => return true,
                    };
                    name_bytes = match name_bytes.checked_add(selector.len()) {
                        Some(bytes) if bytes <= MAX_DATATYPE_FEATURE_NAME_BYTES => bytes,
                        _ => return true,
                    };
                    datatype_functions.insert(selector.as_str());
                }
            }
        }

        let mut expr_nodes = 0usize;
        let mut sort_nodes = 0usize;
        self.clauses.iter().any(|clause| {
            clause.body.constraint.as_ref().is_some_and(|constraint| {
                Self::expr_uses_datatype_features(
                    constraint,
                    &datatype_functions,
                    &datatype_constructors,
                    &mut expr_nodes,
                    &mut sort_nodes,
                )
            }) || clause
                .body
                .predicates
                .iter()
                .flat_map(|(_, arguments)| arguments)
                .any(|argument| {
                    Self::expr_uses_datatype_features(
                        argument,
                        &datatype_functions,
                        &datatype_constructors,
                        &mut expr_nodes,
                        &mut sort_nodes,
                    )
                })
                || match &clause.head {
                    ClauseHead::Predicate(_, arguments) => arguments.iter().any(|argument| {
                        Self::expr_uses_datatype_features(
                            argument,
                            &datatype_functions,
                            &datatype_constructors,
                            &mut expr_nodes,
                            &mut sort_nodes,
                        )
                    }),
                    ClauseHead::False => false,
                }
        })
    }

    fn expr_uses_datatype_features(
        root: &ChcExpr,
        datatype_functions: &FxHashSet<&str>,
        datatype_constructors: &FxHashSet<&str>,
        expr_nodes: &mut usize,
        sort_nodes: &mut usize,
    ) -> bool {
        *expr_nodes = match expr_nodes.checked_add(1) {
            Some(count) if count <= MAX_DATATYPE_FEATURE_EXPR_NODES => count,
            _ => return true,
        };
        let mut stack = vec![root];
        while let Some(expr) = stack.pop() {
            match expr {
                ChcExpr::Bool(_)
                | ChcExpr::Int(_)
                | ChcExpr::Real(_, _)
                | ChcExpr::BitVec(_, _) => {}
                ChcExpr::Var(var) => {
                    if Self::sort_contains_datatype_bounded(&var.sort, sort_nodes) {
                        return true;
                    }
                }
                ChcExpr::Op(_, arguments) | ChcExpr::PredicateApp(_, _, arguments) => {
                    *expr_nodes = match expr_nodes.checked_add(arguments.len()) {
                        Some(count) if count <= MAX_DATATYPE_FEATURE_EXPR_NODES => count,
                        _ => return true,
                    };
                    stack.extend(arguments.iter().map(AsRef::as_ref));
                }
                ChcExpr::FuncApp(name, sort, arguments) => {
                    if datatype_functions.contains(name.as_str())
                        || name
                            .strip_prefix("is-")
                            .is_some_and(|constructor| datatype_constructors.contains(constructor))
                        || Self::sort_contains_datatype_bounded(sort, sort_nodes)
                    {
                        return true;
                    }
                    *expr_nodes = match expr_nodes.checked_add(arguments.len()) {
                        Some(count) if count <= MAX_DATATYPE_FEATURE_EXPR_NODES => count,
                        _ => return true,
                    };
                    stack.extend(arguments.iter().map(AsRef::as_ref));
                }
                ChcExpr::ConstArrayMarker(sort) => {
                    if Self::sort_contains_datatype_bounded(sort, sort_nodes) {
                        return true;
                    }
                }
                ChcExpr::ConstArray(key_sort, value) => {
                    if Self::sort_contains_datatype_bounded(key_sort, sort_nodes) {
                        return true;
                    }
                    *expr_nodes = match expr_nodes.checked_add(1) {
                        Some(count) if count <= MAX_DATATYPE_FEATURE_EXPR_NODES => count,
                        _ => return true,
                    };
                    stack.push(value.as_ref());
                }
                ChcExpr::IsTesterMarker(_) => return true,
            }
        }
        false
    }

    /// Return `true` on either a datatype hit or resource exhaustion.  Every
    /// caller uses this detector as a conservative safety guard, so a bounded
    /// classification failure must retain datatype handling/downgrades rather
    /// than silently classify the problem as scalar.
    fn sort_contains_datatype_bounded(root: &ChcSort, sort_nodes: &mut usize) -> bool {
        *sort_nodes = match sort_nodes.checked_add(1) {
            Some(count) if count <= MAX_DATATYPE_FEATURE_SORT_NODES => count,
            _ => return true,
        };
        let mut stack = vec![root];
        while let Some(sort) = stack.pop() {
            match sort {
                ChcSort::Datatype { .. } => return true,
                ChcSort::Array(key, value) => {
                    *sort_nodes = match sort_nodes.checked_add(2) {
                        Some(count) if count <= MAX_DATATYPE_FEATURE_SORT_NODES => count,
                        _ => return true,
                    };
                    stack.push(value.as_ref());
                    stack.push(key.as_ref());
                }
                ChcSort::Bool
                | ChcSort::Int
                | ChcSort::Real
                | ChcSort::BitVec(_)
                | ChcSort::Uninterpreted(_) => {}
            }
        }
        false
    }

    /// Whether any datatype sort reachable in this problem's signature is
    /// RECURSIVE — i.e. its constructor field sorts transitively reference the
    /// datatype itself, either directly (`List = Nil | Cons(T, List)`) or via
    /// mutual recursion (`A` has a field of sort `B` and `B` has a field of
    /// sort `A`).
    ///
    /// # Why this distinction is soundness-critical
    ///
    /// The exhaustive *acyclic* BMC decider proves a loop-free Horn problem
    /// Safe by unrolling every path to every error query and discharging each
    /// branch formula UNSAT in the original theory. That is a COMPLETE Safe
    /// proof — regardless of the theories involved — **only when every value
    /// space reachable in the bounded unrolling is finite**:
    ///
    /// - A NON-recursive (finite) datatype — a struct of bitvectors,
    ///   `Option<bv64>`, an enum of unit/scalar variants, `CoroutineState`,
    ///   `Pin<bv64>` — has a finite value space. Bounded acyclic unrolling
    ///   covers it exhaustively, so admitting its acyclic-BMC Safe is sound.
    /// - A RECURSIVE datatype has an UNBOUNDED value space. Bounded acyclic
    ///   unrolling is NOT complete for it, so admitting an acyclic-BMC Safe
    ///   over a recursive datatype would be a FALSE PROOF (unsound). Such
    ///   problems must stay Unknown.
    ///
    /// Recursion is detected structurally: a datatype's self-reference survives
    /// in the sort metadata either as a nested `Datatype { name }` or as an
    /// `Uninterpreted(name)` referencing its own name (see the parser's mutual
    /// DT resolution, which leaves the deepest self-reference unresolved). We
    /// build a sort-dependency graph over the declared datatype names and
    /// report `true` iff it contains a cycle (self-loop or mutual). Fail-closed:
    /// any `Uninterpreted` field whose name coincides with a datatype name is
    /// treated as a dependency edge.
    pub fn has_recursive_datatype_sorts(&self) -> bool {
        // Build a dependency graph: datatype name -> set of datatype/sort names
        // its constructor fields reference. Seed from BOTH the datatype sorts
        // inlined in predicate argument sorts (the transition-system state,
        // consistent with `has_datatype_sorts`) AND the declared datatype
        // registry (authoritative; catches recursion even when a nested
        // reference was left as an `Uninterpreted` placeholder).
        let mut deps: FxHashMap<String, FxHashSet<String>> = FxHashMap::default();

        for p in &self.predicates {
            for sort in &p.arg_sorts {
                Self::collect_datatype_sort_deps(sort, &mut deps);
            }
        }

        for (name, ctors) in &self.datatype_defs {
            let mut refs = FxHashSet::default();
            let mut children = Vec::new();
            for (_ctor, sels) in ctors {
                for (_sel, sort) in sels {
                    Self::collect_referenced_datatype_names(sort, &mut refs);
                    children.push(sort.clone());
                }
            }
            deps.entry(name.clone()).or_default().extend(refs);
            for child in &children {
                Self::collect_datatype_sort_deps(child, &mut deps);
            }
        }

        if deps.is_empty() {
            return false;
        }
        Self::datatype_dep_graph_has_cycle(&deps)
    }

    /// Register `sort` and every datatype nested inside it into the dependency
    /// graph `deps`. The `deps.contains_key` guard also protects against sort
    /// structures that are cyclic in memory (a shared `Arc` self-reference).
    fn collect_datatype_sort_deps(sort: &ChcSort, deps: &mut FxHashMap<String, FxHashSet<String>>) {
        match sort {
            ChcSort::Datatype { name, constructors } => {
                if deps.contains_key(name) {
                    return;
                }
                let mut refs = FxHashSet::default();
                let mut children = Vec::new();
                for ctor in constructors.iter() {
                    for sel in &ctor.selectors {
                        Self::collect_referenced_datatype_names(&sel.sort, &mut refs);
                        children.push(sel.sort.clone());
                    }
                }
                // Insert BEFORE recursing so a nested self-reference terminates.
                deps.insert(name.clone(), refs);
                for child in &children {
                    Self::collect_datatype_sort_deps(child, deps);
                }
            }
            ChcSort::Array(k, v) => {
                Self::collect_datatype_sort_deps(k, deps);
                Self::collect_datatype_sort_deps(v, deps);
            }
            _ => {}
        }
    }

    /// Record the datatype/sort names directly referenced by `sort` (the
    /// outgoing edges of a datatype in the dependency graph). Both `Datatype`
    /// and `Uninterpreted` occurrences are recorded by name — a recursive
    /// self-reference can surface as either form.
    fn collect_referenced_datatype_names(sort: &ChcSort, into: &mut FxHashSet<String>) {
        match sort {
            ChcSort::Datatype { name, .. } | ChcSort::Uninterpreted(name) => {
                into.insert(name.clone());
            }
            ChcSort::Array(k, v) => {
                Self::collect_referenced_datatype_names(k, into);
                Self::collect_referenced_datatype_names(v, into);
            }
            _ => {}
        }
    }

    /// DFS cycle detection over the datatype dependency graph. A cycle
    /// (self-loop or mutual) means at least one datatype is recursive.
    fn datatype_dep_graph_has_cycle(deps: &FxHashMap<String, FxHashSet<String>>) -> bool {
        // State per node: 1 = on the current DFS stack, 2 = fully explored.
        fn dfs<'a>(
            node: &'a str,
            deps: &'a FxHashMap<String, FxHashSet<String>>,
            state: &mut FxHashMap<&'a str, u8>,
        ) -> bool {
            match state.get(node) {
                Some(2) => return false,
                Some(1) => return true, // back edge -> cycle
                _ => {}
            }
            state.insert(node, 1);
            if let Some(children) = deps.get(node) {
                for child in children {
                    if dfs(child.as_str(), deps, state) {
                        return true;
                    }
                }
            }
            state.insert(node, 2);
            false
        }

        let mut state: FxHashMap<&str, u8> = FxHashMap::default();
        deps.keys().any(|n| dfs(n.as_str(), deps, &mut state))
    }

    /// Recursively check whether a sort contains BitVec (including inside
    /// Datatype selectors and Array key/value sorts).
    fn sort_contains_bitvec(sort: &ChcSort) -> bool {
        match sort {
            ChcSort::BitVec(_) => true,
            ChcSort::Array(k, v) => Self::sort_contains_bitvec(k) || Self::sort_contains_bitvec(v),
            ChcSort::Datatype { constructors, .. } => constructors.iter().any(|ctor| {
                ctor.selectors
                    .iter()
                    .any(|sel| Self::sort_contains_bitvec(&sel.sort))
            }),
            _ => false,
        }
    }
}
