// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl PdrSolver {
    /// Check if a relational invariant in the frame directly contradicts the bad state.
    ///
    /// This is a quick syntactic check that doesn't require an SMT solver. It handles cases
    /// where the SMT solver returns Unknown due to complex constraints (e.g., mod) but the
    /// relational invariants clearly contradict the bad state.
    ///
    /// Example: frame has (a <= b), bad state is (a >= b /\ a != b) = (a > b) -> contradiction!
    pub(in crate::pdr::solver) fn relational_invariant_blocks_state(
        &self,
        predicate: PredicateId,
        level: usize,
        bad_state: &ChcExpr,
    ) -> bool {
        if level >= self.frames.len() {
            return false;
        }

        let mut relational_lemmas: Vec<_> = Vec::new();
        for lvl in 1..=level.min(self.frames.len() - 1) {
            relational_lemmas.extend(
                self.frames[lvl]
                    .lemmas
                    .iter()
                    .filter(|l| l.predicate == predicate)
                    .filter_map(|l| Self::extract_relational_constraint(&l.formula)),
            );
        }

        if relational_lemmas.is_empty() {
            return false;
        }

        let bad_state_relations = Self::extract_implied_relations(bad_state);

        for (frame_var1, frame_var2, frame_rel) in &relational_lemmas {
            for (bad_var1, bad_var2, bad_rel) in &bad_state_relations {
                if frame_var1 == bad_var1 && frame_var2 == bad_var2 {
                    if Self::relations_contradict(*frame_rel, *bad_rel) {
                        return true;
                    }
                } else if frame_var1 == bad_var2 && frame_var2 == bad_var1 {
                    let flipped_bad_rel = Self::flip_relation(*bad_rel);
                    if Self::relations_contradict(*frame_rel, flipped_bad_rel) {
                        return true;
                    }
                }
            }
        }

        false
    }

    /// Check if parity invariants in the frame syntactically contradict the bad state.
    /// Example: frame has (= (mod x 6) 0), bad state is (not (= (mod x 6) 0)) -> contradiction
    pub(in crate::pdr::solver) fn parity_invariant_blocks_state(
        &self,
        predicate: PredicateId,
        level: usize,
        bad_state: &ChcExpr,
    ) -> bool {
        if level >= self.frames.len() {
            return false;
        }

        let mut parity_lemmas: Vec<(String, i128, i128)> = Vec::new();
        for lvl in 1..=level.min(self.frames.len() - 1) {
            for lemma in &self.frames[lvl].lemmas {
                if lemma.predicate != predicate {
                    continue;
                }
                if let Some((var_name, modulus, remainder)) =
                    extract_parity_constraint(&lemma.formula)
                {
                    parity_lemmas.push((var_name, modulus, remainder));
                }
            }
        }

        if parity_lemmas.is_empty() {
            return false;
        }

        if let Some((bad_var, bad_modulus, bad_remainder)) =
            extract_negated_parity_constraint(bad_state)
        {
            for (frame_var, frame_modulus, frame_remainder) in &parity_lemmas {
                if &bad_var == frame_var
                    && bad_modulus == *frame_modulus
                    && bad_remainder == *frame_remainder
                {
                    return true;
                }
            }
        }

        false
    }

    /// Extract a relational constraint from an expression.
    /// Returns (var1_name, var2_name, relation) if the expression is of the form var1 op var2.
    pub(in crate::pdr::solver) fn extract_relational_constraint(
        expr: &ChcExpr,
    ) -> Option<(String, String, RelationType)> {
        match expr {
            ChcExpr::Op(ChcOp::Le, args) if args.len() == 2 => {
                let (v1, v2) = Self::extract_var_pair(&args[0], &args[1])?;
                Some((v1, v2, RelationType::Le))
            }
            ChcExpr::Op(ChcOp::Lt, args) if args.len() == 2 => {
                let (v1, v2) = Self::extract_var_pair(&args[0], &args[1])?;
                Some((v1, v2, RelationType::Lt))
            }
            ChcExpr::Op(ChcOp::Ge, args) if args.len() == 2 => {
                let (v1, v2) = Self::extract_var_pair(&args[0], &args[1])?;
                Some((v1, v2, RelationType::Ge))
            }
            ChcExpr::Op(ChcOp::Gt, args) if args.len() == 2 => {
                let (v1, v2) = Self::extract_var_pair(&args[0], &args[1])?;
                Some((v1, v2, RelationType::Gt))
            }
            _ => None,
        }
    }

    /// Extract two variable names from expressions if both are simple variables.
    pub(in crate::pdr::solver) fn extract_var_pair(
        e1: &ChcExpr,
        e2: &ChcExpr,
    ) -> Option<(String, String)> {
        match (e1, e2) {
            (ChcExpr::Var(v1), ChcExpr::Var(v2)) => Some((v1.name.clone(), v2.name.clone())),
            _ => None,
        }
    }

    /// Extract implied relations from a bad state expression.
    /// Handles conjunctions and recognizes patterns like (a >= b /\ a != b) as (a > b).
    pub(in crate::pdr::solver) fn extract_implied_relations(
        expr: &ChcExpr,
    ) -> Vec<(String, String, RelationType)> {
        let mut result = Vec::new();
        let conjuncts = expr.collect_conjuncts();

        for c in &conjuncts {
            if let Some(rel) = Self::extract_relational_constraint(c) {
                result.push(rel);
            }
        }

        for i in 0..conjuncts.len() {
            for j in 0..conjuncts.len() {
                if i == j {
                    continue;
                }
                if let Some((v1, v2, rel)) = Self::extract_relational_constraint(&conjuncts[i]) {
                    if Self::is_disequality(&conjuncts[j], &v1, &v2) {
                        let strengthened = match rel {
                            RelationType::Ge => Some(RelationType::Gt),
                            RelationType::Le => Some(RelationType::Lt),
                            _ => None,
                        };
                        if let Some(new_rel) = strengthened {
                            result.push((v1, v2, new_rel));
                        }
                    }
                }
            }
        }

        result
    }
}
