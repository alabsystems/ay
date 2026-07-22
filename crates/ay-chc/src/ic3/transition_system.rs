// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bit-level transition system for clause-level IC3 (#8211).
//!
//! Represents a hardware model checking problem at the gate level:
//! each state variable (latch) is a single Boolean SAT variable.

use super::definition_library::DefinitionLibrary;
use ay_sat::{Literal, Variable};

/// A bit-level transition system for hardware model checking.
///
/// Each state variable is a single Boolean (one SAT variable per latch).
/// The transition relation, initial state, and bad-state property are all
/// represented as CNF clauses over these variables.
///
/// Variable layout (contiguous allocation):
/// - `state_vars[0..num_state_vars]`: current-state latch values
/// - `input_vars[0..num_input_vars]`: primary inputs
/// - `next_vars[0..num_state_vars]`: next-state latch values
/// - Additional auxiliary variables for Tseitin encoding of gates
#[derive(Debug, Clone)]
pub(crate) struct BitLevelTransitionSystem {
    /// Number of state variables (latches)
    pub(crate) num_state_vars: usize,
    /// Number of primary input variables
    pub(crate) num_input_vars: usize,
    /// Current-state variables
    pub(crate) state_vars: Vec<Variable>,
    /// Next-state variables (next_vars[i] corresponds to state_vars[i])
    pub(crate) next_vars: Vec<Variable>,
    /// Primary input variables
    pub(crate) input_vars: Vec<Variable>,
    /// Initial state constraints as CNF clauses over state_vars.
    /// For AIGER, typically unit clauses setting each latch to its reset value.
    pub(crate) init_clauses: Vec<Vec<Literal>>,
    /// Transition relation as CNF clauses over state_vars + input_vars + next_vars.
    /// Encodes the combinational logic (AND gates) connecting current state and
    /// inputs to next state.
    pub(crate) trans_clauses: Vec<Vec<Literal>>,
    /// Bad-state property literals over state_vars.
    /// The property to check: is any state satisfying these literals reachable?
    pub(crate) bad_literals: Vec<Literal>,
    /// Extended-resolution definitions extracted from the transition relation.
    pub(crate) definitions: DefinitionLibrary,
    /// Total number of SAT variables needed (for solver pre-allocation).
    pub(crate) total_vars: usize,
    /// Precomputed variable dependency graph for COI computation (#8430).
    ///
    /// `dep_graph[var_index]` = sorted list of variables that share a transition
    /// clause with `var`. Built once at construction time, making per-query COI
    /// computation O(|COI|) instead of O(|trans_clauses| * |worklist|).
    ///
    /// Reference: GipSAT domain.rs uses `dc.dep(var)` which is the same concept
    /// -- a precomputed per-variable dependency list from the DAG-CNF structure.
    dep_graph: Vec<Vec<Variable>>,
}

impl BitLevelTransitionSystem {
    /// Create a new bit-level transition system.
    ///
    /// Precomputes the variable dependency graph from `trans_clauses` for
    /// efficient COI computation during IC3 queries (#8430).
    pub(crate) fn new(
        num_state_vars: usize,
        num_input_vars: usize,
        state_vars: Vec<Variable>,
        next_vars: Vec<Variable>,
        input_vars: Vec<Variable>,
        init_clauses: Vec<Vec<Literal>>,
        trans_clauses: Vec<Vec<Literal>>,
        bad_literals: Vec<Literal>,
        total_vars: usize,
    ) -> Self {
        debug_assert_eq!(state_vars.len(), num_state_vars);
        debug_assert_eq!(next_vars.len(), num_state_vars);
        debug_assert_eq!(input_vars.len(), num_input_vars);

        // Build the dependency graph (#8430): for each variable, collect all
        // other variables that appear in the same transition clause. This
        // replaces the O(trans_clauses) scan per worklist entry in compute_coi
        // with an O(neighbors) lookup, making COI computation O(|COI|) total.
        let mut dep_graph: Vec<Vec<Variable>> = vec![Vec::new(); total_vars];
        for clause in &trans_clauses {
            // Collect unique variables in this clause.
            let clause_vars: Vec<Variable> = clause.iter().map(|lit| lit.variable()).collect();
            for &var in &clause_vars {
                let idx = var.index();
                if idx < total_vars {
                    for &other in &clause_vars {
                        if other != var {
                            dep_graph[idx].push(other);
                        }
                    }
                }
            }
        }
        // Deduplicate and sort each dependency list for determinism.
        for deps in &mut dep_graph {
            deps.sort_unstable_by_key(|v| v.index());
            deps.dedup();
        }

        let definitions = DefinitionLibrary::from_transition_clauses(&trans_clauses);

        Self {
            num_state_vars,
            num_input_vars,
            state_vars,
            next_vars,
            input_vars,
            init_clauses,
            trans_clauses,
            bad_literals,
            definitions,
            total_vars,
            dep_graph,
        }
    }

    /// Map a cube over current-state variables to next-state variables.
    ///
    /// For each literal in the cube, if it refers to `state_vars[i]`,
    /// replace it with the corresponding `next_vars[i]`.
    pub(crate) fn cube_to_next_state(&self, cube: &[Literal]) -> Vec<Literal> {
        cube.iter()
            .map(|&lit| {
                let var = lit.variable();
                if let Some(idx) = self.state_vars.iter().position(|&sv| sv == var) {
                    if lit.is_positive() {
                        Literal::positive(self.next_vars[idx])
                    } else {
                        Literal::negative(self.next_vars[idx])
                    }
                } else {
                    lit
                }
            })
            .collect()
    }

    /// Map a cube over next-state variables back to current-state variables.
    pub(crate) fn cube_to_current_state(&self, cube: &[Literal]) -> Vec<Literal> {
        cube.iter()
            .map(|&lit| {
                let var = lit.variable();
                if let Some(idx) = self.next_vars.iter().position(|&nv| nv == var) {
                    if lit.is_positive() {
                        Literal::positive(self.state_vars[idx])
                    } else {
                        Literal::negative(self.state_vars[idx])
                    }
                } else {
                    lit
                }
            })
            .collect()
    }

    /// Check if a literal refers to a state variable.
    pub(crate) fn is_state_var(&self, var: Variable) -> bool {
        self.state_vars.contains(&var)
    }

    /// Extract the state-variable subset of a model (full assignment).
    /// Returns a cube (conjunction of literals) over state variables.
    pub(crate) fn extract_state_cube(&self, model: &[bool]) -> Vec<Literal> {
        self.state_vars
            .iter()
            .map(|&var| {
                let idx = var.index();
                if idx < model.len() && model[idx] {
                    Literal::positive(var)
                } else {
                    Literal::negative(var)
                }
            })
            .collect()
    }

    /// Compute the Cone-Of-Influence (COI) from a set of next-state literals (#8430, #8443).
    ///
    /// Starting from the variables in `next_state_lits`, walks the precomputed
    /// dependency graph to collect all variables that transitively influence them.
    /// The resulting set is the minimal variable domain needed for IC3 queries
    /// involving these next-state literals.
    ///
    /// Uses the precomputed `dep_graph` for O(|COI|) total work instead of
    /// the previous O(|trans_clauses| * |worklist|) per-query scan (#8430).
    ///
    /// Reference: GipSAT domain.rs:30-52 (enable_local with dep graph expansion).
    pub(crate) fn compute_coi(&self, next_state_lits: &[Literal]) -> Vec<Variable> {
        if next_state_lits.is_empty() {
            return Vec::new();
        }

        let mut coi: ay_core::kani_compat::DetHashSet<Variable> =
            ay_core::kani_compat::DetHashSet::default();
        let mut worklist = std::collections::VecDeque::new();

        for lit in next_state_lits {
            let var = lit.variable();
            if coi.insert(var) {
                worklist.push_back(var);
            }
        }

        while let Some(var) = worklist.pop_front() {
            let idx = var.index();
            if idx < self.dep_graph.len() {
                for &dep_var in &self.dep_graph[idx] {
                    if coi.insert(dep_var) {
                        worklist.push_back(dep_var);
                    }
                }
            }
        }

        let mut vars: Vec<Variable> = coi.into_iter().collect();
        vars.sort_unstable_by_key(|var| var.index());
        vars
    }

    /// Compute the IC3 query domain for a consecution check (#8443).
    ///
    /// Domain = V(frame activation) ∪ V(cube) ∪ V(next_cube) ∪ COI(next_cube)
    ///
    /// This is the set of variables relevant to checking whether
    /// F_{k-1} /\ T /\ not-cube /\ cube' is UNSAT. Domain-restricting
    /// SAT decisions to this set skips ~80% of variables in typical
    /// hardware model checking problems.
    ///
    /// Reference: GipSAT solve_with_param (mod.rs:257-259) domain computation.
    pub(crate) fn compute_query_domain(
        &self,
        frame_activation: Option<Literal>,
        cube_lits: &[Literal],
        next_cube_lits: &[Literal],
    ) -> Vec<Variable> {
        let mut domain_set: ay_core::kani_compat::DetHashSet<Variable> =
            ay_core::kani_compat::DetHashSet::default();

        // Add frame activation variable.
        if let Some(act) = frame_activation {
            domain_set.insert(act.variable());
        }

        // Add cube variables.
        for lit in cube_lits {
            domain_set.insert(lit.variable());
        }

        // Add next-cube variables.
        for lit in next_cube_lits {
            domain_set.insert(lit.variable());
        }

        // Add COI of the next-state literals.
        let coi_vars = self.compute_coi(next_cube_lits);
        for var in coi_vars {
            domain_set.insert(var);
        }

        let mut vars: Vec<Variable> = domain_set.into_iter().collect();
        vars.sort_unstable_by_key(|var| var.index());
        vars
    }

    /// Extract the next-state subset of a model, mapped back to current-state vars.
    pub(crate) fn extract_next_state_cube(&self, model: &[bool]) -> Vec<Literal> {
        self.next_vars
            .iter()
            .zip(self.state_vars.iter())
            .map(|(&nv, &sv)| {
                let idx = nv.index();
                if idx < model.len() && model[idx] {
                    Literal::positive(sv)
                } else {
                    Literal::negative(sv)
                }
            })
            .collect()
    }
}
