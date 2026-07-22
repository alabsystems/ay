// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Kani proofs for BVE reconstruction soundness.
//!
//! These proofs verify the critical properties of the reconstruction stack:
//! 1. Cascading multi-variable BVE reconstruction satisfies all clauses
//! 2. Reconstruction is idempotent (no oscillation)
//!
//! Reference: CaDiCaL `extend.cpp:121-204`.

#[cfg(kani)]
mod kani_proofs {
    use crate::literal::{Literal, Variable};
    use crate::reconstruct::ReconstructionStack;

    /// Check if a literal is satisfied in a model.
    fn lit_satisfied(model: &[bool], lit: Literal) -> bool {
        let vi = lit.variable().index();
        if vi >= model.len() {
            return false;
        }
        model[vi] == lit.is_positive()
    }

    /// Check if a clause (slice of literals) is satisfied in a model.
    fn clause_satisfied(model: &[bool], clause: &[Literal]) -> bool {
        clause.iter().any(|&l| lit_satisfied(model, l))
    }

    /// Proof: multi-variable cascading BVE reconstruction soundness.
    ///
    /// Variables: A (var 0), B (var 1), C (var 2), D (var 3).
    /// Elimination order: A eliminated first, then B.
    /// B's clauses may reference A (cascading dependency).
    ///
    /// Property: after reconstruction, every clause on the stack is satisfied.
    /// This is the soundness invariant that CaDiCaL extend.cpp:121-204
    /// guarantees via reverse-order processing.
    ///
    /// This proof covers the #5059 failure mode: cascading eliminations where
    /// a later-eliminated variable's clauses reference an earlier-eliminated
    /// variable.
    #[kani::proof]
    #[kani::unwind(8)]
    fn proof_cascading_bve_reconstruction_soundness() {
        // 4 variables: A=0, B=1, C=2, D=3.
        // Model starts with symbolic values for non-eliminated vars C, D.
        let model_c: bool = kani::any();
        let model_d: bool = kani::any();
        let mut model = vec![false, false, model_c, model_d];

        // Phase 1: Eliminate variable A (var 0).
        // A has one positive clause and one negative clause.
        // Positive clause: (A | c2) where c2 is a symbolic literal over C or D.
        let c2_var: usize = kani::any();
        kani::assume(c2_var == 2 || c2_var == 3);
        let c2_pos: bool = kani::any();
        let c2_lit = if c2_pos {
            Literal::positive(Variable(c2_var as u32))
        } else {
            Literal::negative(Variable(c2_var as u32))
        };
        let pos_clause_a = vec![Literal::positive(Variable(0)), c2_lit];

        // Negative clause: (!A | c3) where c3 is a symbolic literal over C or D.
        let c3_var: usize = kani::any();
        kani::assume(c3_var == 2 || c3_var == 3);
        let c3_pos: bool = kani::any();
        let c3_lit = if c3_pos {
            Literal::positive(Variable(c3_var as u32))
        } else {
            Literal::negative(Variable(c3_var as u32))
        };
        let neg_clause_a = vec![Literal::negative(Variable(0)), c3_lit];

        // Phase 2: Eliminate variable B (var 1).
        // B's clauses may reference A (cascading dependency).
        // Positive clause: (B | d2) where d2 is symbolic over A, C, or D.
        let d2_var: usize = kani::any();
        kani::assume(d2_var == 0 || d2_var == 2 || d2_var == 3);
        let d2_pos: bool = kani::any();
        let d2_lit = if d2_pos {
            Literal::positive(Variable(d2_var as u32))
        } else {
            Literal::negative(Variable(d2_var as u32))
        };
        let pos_clause_b = vec![Literal::positive(Variable(1)), d2_lit];

        // Negative clause: (!B | d3) where d3 is symbolic over A, C, or D.
        let d3_var: usize = kani::any();
        kani::assume(d3_var == 0 || d3_var == 2 || d3_var == 3);
        let d3_pos: bool = kani::any();
        let d3_lit = if d3_pos {
            Literal::positive(Variable(d3_var as u32))
        } else {
            Literal::negative(Variable(d3_var as u32))
        };
        let neg_clause_b = vec![Literal::negative(Variable(1)), d3_lit];

        // Build reconstruction stack: A eliminated first (pushed first),
        // B eliminated second (pushed second). Reconstruction processes
        // in reverse: B first, then A.
        let mut stack = ReconstructionStack::new();

        // Push A's clauses (positive first, then negative — CaDiCaL order).
        stack.push_witness_clause(vec![Literal::positive(Variable(0))], pos_clause_a.clone());
        stack.push_witness_clause(vec![Literal::negative(Variable(0))], neg_clause_a.clone());

        // Push B's clauses.
        stack.push_witness_clause(vec![Literal::positive(Variable(1))], pos_clause_b.clone());
        stack.push_witness_clause(vec![Literal::negative(Variable(1))], neg_clause_b.clone());

        // Reconstruct.
        stack.reconstruct(&mut model);

        // Soundness: every clause on the stack must be satisfied.
        assert!(
            clause_satisfied(&model, &pos_clause_a),
            "A's positive clause must be satisfied after reconstruction"
        );
        assert!(
            clause_satisfied(&model, &neg_clause_a),
            "A's negative clause must be satisfied after reconstruction"
        );
        assert!(
            clause_satisfied(&model, &pos_clause_b),
            "B's positive clause must be satisfied after reconstruction"
        );
        assert!(
            clause_satisfied(&model, &neg_clause_b),
            "B's negative clause must be satisfied after reconstruction"
        );
    }

    /// Proof: reconstruction is idempotent.
    ///
    /// Applying reconstruction twice produces the same model as applying it
    /// once. This proves that reconstruction does not oscillate — a property
    /// critical for correctness (see #6892 repair pass removal).
    #[kani::proof]
    #[kani::unwind(6)]
    fn proof_reconstruction_idempotent() {
        // 3 variables with one BVE elimination.
        let model_init: [bool; 3] = [kani::any(), kani::any(), kani::any()];

        let elim_var: usize = kani::any();
        kani::assume(elim_var < 3);
        let other_var: usize = kani::any();
        kani::assume(other_var < 3 && other_var != elim_var);

        let pos_lit = Literal::positive(Variable(elim_var as u32));
        let neg_lit = Literal::negative(Variable(elim_var as u32));
        let other_pos: bool = kani::any();
        let other_lit = if other_pos {
            Literal::positive(Variable(other_var as u32))
        } else {
            Literal::negative(Variable(other_var as u32))
        };

        let mut stack = ReconstructionStack::new();
        stack.push_witness_clause(vec![pos_lit], vec![pos_lit, other_lit]);
        stack.push_witness_clause(vec![neg_lit], vec![neg_lit, other_lit.negated()]);

        // First reconstruction.
        let mut model1 = model_init.to_vec();
        stack.reconstruct(&mut model1);

        // Second reconstruction (idempotency test).
        let mut model2 = model1.clone();
        stack.reconstruct(&mut model2);

        for i in 0..3 {
            assert_eq!(model1[i], model2[i], "Reconstruction must be idempotent");
        }
    }
}
