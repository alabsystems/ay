// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::formula::MAX_QBF_VARS;

/// Bound matrix scanning as well as search-tree size. The public limit remains
/// a node budget; each node grants this fixed amount of literal-inspection
/// work. Exhausting either counter returns `Unknown`.
const MATRIX_LITERAL_WORK_PER_NODE: u64 = 64;

impl QbfSolver {
    /// Create a new QBF solver for the given formula
    pub fn new(formula: QbfFormula) -> Self {
        let num_vars = formula.num_vars();
        let mut input_valid = num_vars <= MAX_QBF_VARS;
        let mut matrix_variables = HashSet::new();
        for literal in formula.clauses().iter().flatten() {
            let variable = literal.variable().id() as usize;
            if variable == 0 || variable > num_vars {
                input_valid = false;
            } else {
                matrix_variables.insert(variable as u32);
            }
        }

        // Build decision order from quantifier prefix
        let mut decision_order = Vec::with_capacity(matrix_variables.len());
        let mut quantified = HashSet::with_capacity(matrix_variables.len());
        for block in formula.prefix() {
            for &var in &block.variables {
                if matrix_variables.contains(&var) && quantified.insert(var) {
                    decision_order.push(var);
                }
            }
        }

        // Add any unquantified variables (implicitly existential at outermost).
        // Preserve the historical reverse-numeric order without repeatedly
        // inserting at the front of `decision_order`: a sparse or absent
        // prefix can contain millions of implicit variables, and front
        // insertion made construction quadratic in that common malformed-but-
        // accepted input case.
        let mut implicit_outer: Vec<u32> = matrix_variables
            .iter()
            .copied()
            .filter(|variable| !quantified.contains(variable))
            .collect();
        implicit_outer.sort_unstable_by(|left, right| right.cmp(left));
        implicit_outer.append(&mut decision_order);
        decision_order = implicit_outer;

        // Oversized native formulas are invalid and receive no dense state.
        // `solve_with_limit` returns Unknown before any of these vectors are
        // indexed. Parsed inputs never reach this path above the limit.
        let dense_num_vars = if input_valid { num_vars } else { 0 };
        let solver = Self {
            formula,
            input_valid,
            assignments: vec![Assignment::Unassigned; dense_num_vars],
            levels: vec![0; dense_num_vars],
            reasons: vec![Reason::Decision; dense_num_vars],
            trail: Vec::with_capacity(dense_num_vars),
            trail_lim: Vec::new(),
            decision_level: 0,
            learned: Vec::new(),
            cubes: Vec::new(),
            decision_order,
            activity: vec![0.0; dense_num_vars],
            var_inc: 1.0,
            var_decay: 0.95,
            conflicts: 0,
            propagations: 0,
            decisions: 0,
            // The public verdict path is exact QDPLL and does not use QCDCL
            // watches. Allocate them lazily only if the retained experimental
            // engine is invoked, avoiding 2 * num_vars empty Vec headers.
            watches: Vec::new(),
            qhead: 0,
            clause_used: Vec::new(),
            cube_used: Vec::new(),
            next_reduce: REDUCE_DB_INIT,
            reductions: 0,
            clauses_deleted: 0,
            cubes_deleted: 0,
        };

        // The experimental QCDCL watch structure assumes valid dense variable
        // indices. Invalid direct-native matrices are retained for diagnostics
        // but never indexed; the public exact solver fails closed with Unknown.
        solver
    }

    /// Solve the QBF formula
    pub fn solve(&mut self) -> QbfResult {
        self.solve_with_limit(1_000_000)
    }

    /// Solve with an exact-QDPLL node limit.
    ///
    /// Matrix work is bounded by a fixed multiple of the node limit so a small
    /// search tree with very large clauses cannot evade the resource bound.
    pub fn solve_with_limit(&mut self, max_iterations: u64) -> QbfResult {
        // The experimental QCDCL engine's constant certificates are not yet
        // rich enough to validate a quantified strategy. Use the independent,
        // complete QDPLL evaluator as the sole verdict authority. If it
        // exhausts the caller's node budget, fail closed with Unknown.
        let mut budget = ExactBudget::new(max_iterations);
        self.assignments.fill(Assignment::Unassigned);
        self.trail.clear();
        if !self.input_valid {
            return QbfResult::Unknown;
        }
        let mut true_path = None;
        let mut false_path = None;
        match self.exact_qdpll(&mut budget, &mut true_path, &mut false_path) {
            ExactVerdict::True => {
                self.restore_terminal_path(true_path);
                QbfResult::Sat(Certificate::None)
            }
            ExactVerdict::False => {
                self.restore_terminal_path(false_path);
                QbfResult::Unsat(Certificate::None)
            }
            ExactVerdict::Unknown => QbfResult::Unknown,
        }
    }

    /// Experimental QCDCL search retained for continued algorithm work, but
    /// deliberately disconnected from public verdict authority.
    #[expect(
        dead_code,
        reason = "non-authoritative QCDCL research engine retained behind the exact QDPLL firewall"
    )]
    fn solve_qcdcl_with_limit(&mut self, max_iterations: u64) -> QbfResult {
        if !self.input_valid {
            return QbfResult::Unknown;
        }
        if self.watches.is_empty() {
            self.watches = vec![Vec::new(); self.formula.num_vars().saturating_mul(2) + 2];
            self.init_watches();
        }
        // Apply initial universal reduction
        self.apply_universal_reduction();

        // Check for empty clause (immediate UNSAT)
        if self.has_empty_clause() {
            return QbfResult::Unsat(Certificate::None);
        }

        let mut iterations: u64 = 0;
        loop {
            iterations += 1;
            if iterations > max_iterations {
                return QbfResult::Unknown;
            }

            // Unit propagation
            match self.propagate() {
                PropResult::Ok => {}
                PropResult::Conflict(clause_idx) => {
                    self.conflicts += 1;

                    if self.decision_level == 0 {
                        // Conflict at level 0 - UNSAT
                        return QbfResult::Unsat(self.build_herbrand_certificate());
                    }

                    // Analyze conflict and learn
                    let (learned_clause, backtrack_level) = self.analyze_conflict(clause_idx);
                    self.bump_clause_activity(&learned_clause);
                    self.var_decay_activity();

                    // Backtrack
                    self.backtrack(backtrack_level);

                    // Add learned clause, reduce DB if due
                    self.add_learned_clause(learned_clause);
                    self.maybe_reduce_db();

                    // Continue to propagate the learned clause before deciding
                    continue;
                }
            }

            // Check if all variables assigned
            if self.all_assigned() {
                // Check if formula is satisfied
                if self.is_satisfied() {
                    return QbfResult::Sat(self.build_skolem_certificate());
                } else {
                    // Should not happen with correct propagation
                    return QbfResult::Unknown;
                }
            }

            // Check for partial solution (all clauses satisfied but not all vars assigned)
            // This is a "solution" state where we can learn a cube
            if self.is_satisfied() {
                // All clauses satisfied - existential player wins for this universal path
                // Learn a cube to block this universal search path
                if let Some(cube_result) = self.learn_cube_from_solution() {
                    match cube_result {
                        CubeResult::Learned(backtrack_level) => {
                            self.backtrack(backtrack_level);
                            continue;
                        }
                        CubeResult::Solved => {
                            // All universal paths lead to SAT
                            return QbfResult::Sat(self.build_skolem_certificate());
                        }
                    }
                }
            }

            // Make a decision
            match self.decide() {
                Some(_) => {
                    self.decisions += 1;
                }
                None => {
                    // No more decisions possible but not all assigned?
                    // This shouldn't happen
                    return QbfResult::Unknown;
                }
            }
        }
    }

    /// Independently evaluate the prenex CNF with textbook QDPLL semantics.
    ///
    /// Existential nodes are disjunctions of their two assignments; universal
    /// nodes are conjunctions. Matrix evaluation short-circuits as soon as one
    /// clause is false or every clause is already true. The budget counts DFS
    /// nodes and turns exhaustion into `Unknown`, never a guessed verdict.
    fn exact_qdpll(
        &mut self,
        budget: &mut ExactBudget,
        true_path: &mut Option<Vec<Assignment>>,
        false_path: &mut Option<Vec<Assignment>>,
    ) -> ExactVerdict {
        let mut frames: Vec<ExactFrame> = Vec::with_capacity(self.decision_order.len().min(1024));
        let mut order_index = 0usize;
        let mut completed = None;

        loop {
            if let Some(child_verdict) = completed.take() {
                let Some(frame) = frames.pop() else {
                    return child_verdict;
                };
                let slot = frame.variable as usize - 1;

                match frame.state {
                    ExactFrameState::AwaitingFalse => {
                        let short_circuits = (frame.existential
                            && child_verdict == ExactVerdict::True)
                            || (!frame.existential && child_verdict == ExactVerdict::False);
                        if short_circuits {
                            self.assignments[slot] = Assignment::Unassigned;
                            completed = Some(child_verdict);
                        } else {
                            self.assignments[slot] = Assignment::True;
                            order_index = frame.next_order_index;
                            frames.push(ExactFrame {
                                state: ExactFrameState::AwaitingTrue(child_verdict),
                                ..frame
                            });
                        }
                    }
                    ExactFrameState::AwaitingTrue(when_false) => {
                        self.assignments[slot] = Assignment::Unassigned;
                        completed = Some(if frame.existential {
                            when_false.or(child_verdict)
                        } else {
                            when_false.and(child_verdict)
                        });
                    }
                }
                continue;
            }

            match self.partial_matrix_value(budget) {
                PartialMatrixValue::True => {
                    if true_path.is_none() {
                        *true_path = Some(self.assignments.clone());
                    }
                    completed = Some(ExactVerdict::True);
                    continue;
                }
                PartialMatrixValue::False => {
                    self.conflicts += 1;
                    if false_path.is_none() {
                        *false_path = Some(self.assignments.clone());
                    }
                    completed = Some(ExactVerdict::False);
                    continue;
                }
                PartialMatrixValue::WorkExhausted => {
                    completed = Some(ExactVerdict::Unknown);
                    continue;
                }
                PartialMatrixValue::Unresolved => {}
            }

            if !budget.take_node() {
                completed = Some(ExactVerdict::Unknown);
                continue;
            }

            let Some(variable) = self.decision_order.get(order_index).copied() else {
                // Every decision variable is assigned, so an unresolved matrix
                // indicates malformed native input. Stay fail-closed.
                completed = Some(ExactVerdict::Unknown);
                continue;
            };
            let slot = variable as usize - 1;
            if slot >= self.assignments.len() {
                completed = Some(ExactVerdict::Unknown);
                continue;
            }
            self.decisions += 1;

            self.assignments[slot] = Assignment::False;
            frames.push(ExactFrame {
                variable,
                next_order_index: order_index + 1,
                existential: self.formula.is_existential(variable),
                state: ExactFrameState::AwaitingFalse,
            });
            order_index += 1;
        }
    }

    /// Restore one terminal search path so the read-only solver context keeps
    /// exposing a coherent post-solve assignment, as it did before the exact
    /// evaluator became authoritative. A single path is diagnostic state, not
    /// a quantified strategy certificate.
    fn restore_terminal_path(&mut self, path: Option<Vec<Assignment>>) {
        let Some(path) = path else {
            return;
        };
        self.assignments = path;
        self.trail.clear();
        for &variable in &self.decision_order {
            let assignment = self.assignments[variable as usize - 1];
            let literal = match assignment {
                Assignment::True => Literal::positive(Variable::new(variable)),
                Assignment::False => Literal::negative(Variable::new(variable)),
                Assignment::Unassigned => continue,
            };
            self.trail.push(literal);
        }
    }

    /// Evaluate the matrix under the current partial assignment while charging
    /// every literal inspection to the exact-search work budget.
    fn partial_matrix_value(&self, budget: &mut ExactBudget) -> PartialMatrixValue {
        let mut all_satisfied = true;
        for clause in self.formula.clauses() {
            let mut clause_satisfied = false;
            let mut clause_unresolved = false;
            for &literal in clause {
                if !budget.take_literal_check() {
                    return PartialMatrixValue::WorkExhausted;
                }
                match self.lit_value(literal) {
                    Assignment::True => {
                        clause_satisfied = true;
                        break;
                    }
                    Assignment::False => {}
                    Assignment::Unassigned => clause_unresolved = true,
                }
            }
            if !clause_satisfied && !clause_unresolved {
                return PartialMatrixValue::False;
            }
            all_satisfied &= clause_satisfied;
        }
        if all_satisfied {
            PartialMatrixValue::True
        } else {
            PartialMatrixValue::Unresolved
        }
    }

    /// Apply universal reduction to all clauses
    fn apply_universal_reduction(&mut self) {
        self.formula.universally_reduce_matrix();
    }

    /// Check if any clause is empty
    fn has_empty_clause(&self) -> bool {
        self.formula.clauses().iter().any(Vec::is_empty) || self.learned.iter().any(Vec::is_empty)
    }

    /// Build Skolem certificate for SAT result
    fn build_skolem_certificate(&self) -> Certificate {
        let mut functions = Vec::new();
        for &var in &self.decision_order {
            if self.formula.is_existential(var) {
                let value = self.value(var).to_bool().unwrap_or(false);
                functions.push(SkolemFunction {
                    variable: var,
                    value,
                });
            }
        }
        Certificate::Skolem(functions)
    }

    /// Build Herbrand certificate for UNSAT result
    fn build_herbrand_certificate(&self) -> Certificate {
        let mut functions = Vec::new();
        for &var in &self.decision_order {
            if self.formula.is_universal(var) {
                let value = self.value(var).to_bool().unwrap_or(false);
                functions.push(HerbrandFunction {
                    variable: var,
                    value,
                });
            }
        }
        Certificate::Herbrand(functions)
    }

    /// Get statistics
    pub fn stats(&self) -> QbfStats {
        let active_clauses = self.learned.iter().filter(|c| !c.is_empty()).count();
        let active_cubes = self.cubes.iter().filter(|c| !c.is_empty()).count();
        QbfStats {
            conflicts: self.conflicts,
            propagations: self.propagations,
            decisions: self.decisions,
            learned_clauses: active_clauses as u64,
            learned_cubes: active_cubes as u64,
            reductions: self.reductions,
            clauses_deleted: self.clauses_deleted,
            cubes_deleted: self.cubes_deleted,
        }
    }
}

#[derive(Debug, Clone, Copy)]
struct ExactBudget {
    remaining_nodes: u64,
    remaining_literal_checks: u64,
}

impl ExactBudget {
    fn new(node_limit: u64) -> Self {
        Self {
            remaining_nodes: node_limit,
            remaining_literal_checks: node_limit.saturating_mul(MATRIX_LITERAL_WORK_PER_NODE),
        }
    }

    fn take_node(&mut self) -> bool {
        if self.remaining_nodes == 0 {
            return false;
        }
        self.remaining_nodes -= 1;
        true
    }

    fn take_literal_check(&mut self) -> bool {
        if self.remaining_literal_checks == 0 {
            return false;
        }
        self.remaining_literal_checks -= 1;
        true
    }
}

#[derive(Debug, Clone, Copy)]
struct ExactFrame {
    variable: u32,
    next_order_index: usize,
    existential: bool,
    state: ExactFrameState,
}

#[derive(Debug, Clone, Copy)]
enum ExactFrameState {
    AwaitingFalse,
    AwaitingTrue(ExactVerdict),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum PartialMatrixValue {
    True,
    False,
    Unresolved,
    WorkExhausted,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ExactVerdict {
    True,
    False,
    Unknown,
}

impl ExactVerdict {
    fn or(self, other: Self) -> Self {
        match (self, other) {
            (Self::True, _) | (_, Self::True) => Self::True,
            (Self::False, Self::False) => Self::False,
            _ => Self::Unknown,
        }
    }

    fn and(self, other: Self) -> Self {
        match (self, other) {
            (Self::False, _) | (_, Self::False) => Self::False,
            (Self::True, Self::True) => Self::True,
            _ => Self::Unknown,
        }
    }
}
