// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Extended-resolution definition library for clause-level IC3/PDR.
//!
//! PdrER introduces auxiliary definition variables and then uses them during
//! generalization and propagation. This module is the structural substrate for
//! those later hooks: it extracts simple Tseitin definitions from the bit-level
//! transition relation and provides deterministic cube/clause substitution.

use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};
use ay_sat::{Literal, Variable};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum DefinitionKind {
    /// Two-input AND definition: `output <-> input[0] /\ input[1]`.
    And,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Definition {
    /// Extension variable introduced by the transition relation.
    pub(crate) output: Literal,
    /// Signed input literals for the Boolean operator.
    pub(crate) inputs: Vec<Literal>,
    /// Boolean operator represented by this definition.
    pub(crate) kind: DefinitionKind,
}

/// Collection of ER definitions extracted from the transition relation.
#[derive(Debug, Clone, Default)]
pub(crate) struct DefinitionLibrary {
    definitions: Vec<Definition>,
    by_output_var: FxHashMap<Variable, usize>,
}

impl DefinitionLibrary {
    /// Extract currently supported definitions from transition CNF.
    ///
    /// This first PdrER slice recognizes the canonical two-input AND Tseitin
    /// shape:
    ///
    /// ```text
    /// output <-> a /\ b
    /// ( output \/ !a \/ !b ) /\ ( !output \/ a ) /\ ( !output \/ b )
    /// ```
    ///
    /// Inputs may be signed literals; the output is restricted to a positive
    /// variable to avoid ambiguity while the IC3 ER integration is still
    /// scaffolding.
    pub(crate) fn from_transition_clauses(trans_clauses: &[Vec<Literal>]) -> Self {
        let mut binary_clauses: FxHashSet<Vec<Literal>> = FxHashSet::default();
        for clause in trans_clauses {
            if clause.len() == 2 {
                binary_clauses.insert(normalized_clause(clause));
            }
        }

        let mut candidates = Vec::new();
        for clause in trans_clauses {
            if clause.len() != 3 {
                continue;
            }

            for output_pos in 0..clause.len() {
                let output = clause[output_pos];
                if !output.is_positive() {
                    continue;
                }

                let mut inputs = Vec::with_capacity(2);
                for (idx, &lit) in clause.iter().enumerate() {
                    if idx != output_pos {
                        inputs.push(lit.negated());
                    }
                }

                if !is_valid_and_shape(output, &inputs) {
                    continue;
                }

                let required_binary_a = normalized_clause(&[output.negated(), inputs[0]]);
                let required_binary_b = normalized_clause(&[output.negated(), inputs[1]]);
                if binary_clauses.contains(&required_binary_a)
                    && binary_clauses.contains(&required_binary_b)
                {
                    inputs.sort_unstable_by_key(|lit| lit.raw());
                    candidates.push(Definition {
                        output,
                        inputs,
                        kind: DefinitionKind::And,
                    });
                }
            }
        }

        candidates.sort_unstable_by_key(|def| {
            (
                def.output.variable().index(),
                def.inputs.first().map_or(0, |lit| lit.raw()),
                def.inputs.get(1).map_or(0, |lit| lit.raw()),
            )
        });
        candidates.dedup_by(|left, right| left.output.variable() == right.output.variable());

        let mut library = Self::default();
        for def in candidates {
            library.add_definition(def);
        }
        library
    }

    pub(crate) fn len(&self) -> usize {
        self.definitions.len()
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.definitions.is_empty()
    }

    pub(crate) fn definitions(&self) -> &[Definition] {
        &self.definitions
    }

    pub(crate) fn is_extension_variable(&self, var: Variable) -> bool {
        self.by_output_var.contains_key(&var)
    }

    pub(crate) fn definition_for(&self, var: Variable) -> Option<&Definition> {
        self.by_output_var
            .get(&var)
            .and_then(|&idx| self.definitions.get(idx))
    }

    /// Replace a cube containing all AND inputs with the corresponding
    /// extension literal.
    pub(crate) fn compact_cube(&self, cube: &[Literal]) -> Vec<Literal> {
        let mut literals = cube.to_vec();
        for def in &self.definitions {
            if matches!(def.kind, DefinitionKind::And)
                && all_literals_present(&literals, &def.inputs)
                && !literals.contains(&def.output.negated())
            {
                literals.retain(|lit| !def.inputs.contains(lit));
                push_unique(&mut literals, def.output);
            }
        }
        normalized_clause(&literals)
    }

    /// Expand extension literals in a cube back to their input literals.
    pub(crate) fn expand_cube(&self, cube: &[Literal]) -> Vec<Literal> {
        let mut expanded = Vec::new();
        for &lit in cube {
            match self.definition_for(lit.variable()) {
                Some(def) if lit == def.output => {
                    for &input in &def.inputs {
                        push_unique(&mut expanded, input);
                    }
                }
                _ => push_unique(&mut expanded, lit),
            }
        }
        normalized_clause(&expanded)
    }

    /// Replace a clause containing the negated inputs of an AND definition with
    /// the negated extension literal. This is the clause-side dual of
    /// [`compact_cube`].
    pub(crate) fn compact_clause(&self, clause: &[Literal]) -> Vec<Literal> {
        let mut literals = clause.to_vec();
        for def in &self.definitions {
            let negated_inputs: Vec<Literal> = def.inputs.iter().map(|lit| lit.negated()).collect();
            if matches!(def.kind, DefinitionKind::And)
                && all_literals_present(&literals, &negated_inputs)
                && !literals.contains(&def.output)
            {
                literals.retain(|lit| !negated_inputs.contains(lit));
                push_unique(&mut literals, def.output.negated());
            }
        }
        normalized_clause(&literals)
    }

    /// Produce one-step clause expansions for fractional propagation.
    ///
    /// For `output <-> a /\ b`:
    /// - `( !output \/ rest )` expands to `( !a \/ !b \/ rest )`
    /// - `( output \/ rest )` expands to the fractions
    ///   `( a \/ rest )` and `( b \/ rest )`
    pub(crate) fn expand_clause_fractions(&self, clause: &[Literal]) -> Option<Vec<Vec<Literal>>> {
        for (idx, &lit) in clause.iter().enumerate() {
            let Some(def) = self.definition_for(lit.variable()) else {
                continue;
            };

            let mut rest = Vec::with_capacity(clause.len().saturating_sub(1) + def.inputs.len());
            rest.extend_from_slice(&clause[..idx]);
            rest.extend_from_slice(&clause[idx + 1..]);

            if lit == def.output.negated() {
                let mut expanded = rest;
                for &input in &def.inputs {
                    push_unique(&mut expanded, input.negated());
                }
                return Some(vec![normalized_clause(&expanded)]);
            }

            if lit == def.output {
                let mut fractions = Vec::with_capacity(def.inputs.len());
                for &input in &def.inputs {
                    let mut fraction = rest.clone();
                    push_unique(&mut fraction, input);
                    fractions.push(normalized_clause(&fraction));
                }
                fractions.sort_unstable();
                fractions.dedup();
                return Some(fractions);
            }
        }

        None
    }

    fn add_definition(&mut self, def: Definition) {
        let var = def.output.variable();
        if self.by_output_var.contains_key(&var) {
            return;
        }

        let idx = self.definitions.len();
        self.definitions.push(def);
        self.by_output_var.insert(var, idx);
    }
}

fn is_valid_and_shape(output: Literal, inputs: &[Literal]) -> bool {
    inputs.len() == 2
        && inputs[0].variable() != inputs[1].variable()
        && inputs.iter().all(|lit| lit.variable() != output.variable())
}

fn all_literals_present(literals: &[Literal], required: &[Literal]) -> bool {
    required.iter().all(|lit| literals.contains(lit))
}

fn push_unique(literals: &mut Vec<Literal>, lit: Literal) {
    if !literals.contains(&lit) {
        literals.push(lit);
    }
}

fn normalized_clause(clause: &[Literal]) -> Vec<Literal> {
    let mut normalized = clause.to_vec();
    normalized.sort_unstable_by_key(|lit| lit.raw());
    normalized.dedup();
    normalized
}
