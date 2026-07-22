// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Delayed BV operation checking (#7015).
//!
//! Z3's delayed internalization strategy: for expensive operations (mul, div,
//! rem on wide bitvectors with 2+ variable arguments), allocate fresh bit
//! variables without building the circuit. After SAT solving, evaluate the
//! delayed operations against the model. If the model violates the operation
//! semantics, add conflict clauses and re-solve.
//!
//! Cheap axiom checks (zero, one, invertibility, div/rem special cases)
//! are in `checks`.

mod checks;

use super::*;

/// A BV operation whose circuit construction was delayed (#7015).
///
/// Z3's delayed internalization strategy: for expensive operations (mul, div,
/// rem on wide bitvectors with 2+ variable arguments), allocate fresh bit
/// variables without building the circuit. After SAT solving, evaluate the
/// delayed operations against the model. If the model violates the operation
/// semantics, add conflict clauses and re-solve.
///
/// Reference: `reference/z3/src/sat/smt/bv_delay_internalize.cpp`
#[derive(Debug, Clone)]
pub struct DelayedBvOp {
    /// The term representing this operation's result
    pub term: TermId,
    /// The operation name (e.g., "bvmul", "bvudiv", "bvurem")
    pub op: &'static str,
    /// Argument term IDs
    pub args: Vec<TermId>,
    /// The fresh unconstrained bits allocated for the result
    pub result_bits: BvBits,
    /// Whether the full circuit has been built (set after fallback)
    pub circuit_built: bool,
    /// Number of times cheap axioms have been tried for this op.
    /// After `MAX_CHEAP_TRIES`, the next violation triggers full circuit building.
    pub cheap_tries: u8,
}

/// Owned state for checking delayed BV operations after the BvSolver is dropped (#7015).
///
/// This struct holds all data needed to evaluate delayed operations against
/// a SAT model and generate conflict clauses. It is extracted from `BvSolver`
/// before the solver is dropped, allowing the iterative solve loop to run
/// without holding a borrow on the term store.
pub struct DelayedBvState {
    /// The delayed operations to check
    delayed_ops: Vec<DelayedBvOp>,
    /// Mapping from term IDs to their bit representations (needed to evaluate arguments)
    term_to_bits: HashMap<TermId, BvBits>,
}

impl DelayedBvState {
    /// Create a new DelayedBvState from delayed operations and term-to-bits mapping.
    pub fn new(delayed_ops: Vec<DelayedBvOp>, term_to_bits: HashMap<TermId, BvBits>) -> Self {
        Self {
            delayed_ops,
            term_to_bits,
        }
    }

    /// Check if there are any unresolved delayed operations.
    pub fn has_unresolved(&self) -> bool {
        self.delayed_ops.iter().any(|op| !op.circuit_built)
    }

    /// Get the term-to-bits mapping (for restoring into a temporary BvSolver).
    pub fn term_to_bits(&self) -> &HashMap<TermId, BvBits> {
        &self.term_to_bits
    }

    /// Get the delayed operations list (for restoring into a temporary BvSolver).
    pub fn delayed_ops(&self) -> &[DelayedBvOp] {
        &self.delayed_ops
    }

    /// Evaluate a single BV literal's truth value from the SAT model.
    fn eval_lit(&self, lit: CnfLit, model: &[bool], var_offset: i32) -> bool {
        let positive = lit > 0;
        let var_idx = (lit.unsigned_abs() as i32 + var_offset - 1) as usize;
        let assigned = model.get(var_idx).copied().unwrap_or(false);
        positive == assigned
    }

    /// Evaluate a bitvector value from model assignments on bit literals.
    fn eval_bits(&self, bits: &[CnfLit], model: &[bool], var_offset: i32) -> num_bigint::BigInt {
        let mut val = num_bigint::BigInt::from(0);
        for (i, &lit) in bits.iter().enumerate() {
            if self.eval_lit(lit, model, var_offset) {
                val |= num_bigint::BigInt::from(1) << i;
            }
        }
        val
    }

    /// Compute the expected result of a delayed operation from model values.
    fn eval_op(&self, op: &DelayedBvOp, model: &[bool], var_offset: i32) -> num_bigint::BigInt {
        use num_bigint::BigInt;
        let width = op.result_bits.len() as u32;
        let mask = (BigInt::from(1) << width) - 1;

        let a_val = self
            .term_to_bits
            .get(&op.args[0])
            .map(|bits| self.eval_bits(bits, model, var_offset))
            .unwrap_or_default();
        let b_val = if op.args.len() > 1 {
            self.term_to_bits
                .get(&op.args[1])
                .map(|bits| self.eval_bits(bits, model, var_offset))
                .unwrap_or_default()
        } else {
            BigInt::from(0)
        };

        let result = match op.op {
            "bvmul" => (&a_val * &b_val) & &mask,
            "bvadd" => (&a_val + &b_val) & &mask,
            "bvudiv" => {
                if b_val == BigInt::from(0) {
                    mask.clone() // SMT-LIB: div by 0 = all ones
                } else {
                    &a_val / &b_val
                }
            }
            "bvurem" => {
                if b_val == BigInt::from(0) {
                    a_val
                } else {
                    &a_val % &b_val
                }
            }
            "bvsdiv" | "bvsrem" | "bvsmod" => {
                Self::eval_signed_op_static(op.op, &a_val, &b_val, width)
            }
            _ => BigInt::from(0),
        };

        result & &mask
    }

    /// Evaluate a signed BV operation from unsigned BigInt values.
    fn eval_signed_op_static(
        op: &str,
        a: &num_bigint::BigInt,
        b: &num_bigint::BigInt,
        width: u32,
    ) -> num_bigint::BigInt {
        use num_bigint::BigInt;
        let half = BigInt::from(1) << (width - 1);
        let modulus = BigInt::from(1) << width;

        let a_signed = if a >= &half { a - &modulus } else { a.clone() };
        let b_signed = if b >= &half { b - &modulus } else { b.clone() };

        let result = match op {
            "bvsdiv" => {
                if b_signed == BigInt::from(0) {
                    if a_signed < BigInt::from(0) {
                        BigInt::from(1)
                    } else {
                        &modulus - 1
                    }
                } else {
                    &a_signed / &b_signed
                }
            }
            "bvsrem" => {
                if b_signed == BigInt::from(0) {
                    a_signed
                } else {
                    &a_signed % &b_signed
                }
            }
            "bvsmod" => {
                if b_signed == BigInt::from(0) {
                    a_signed
                } else {
                    let r = &a_signed % &b_signed;
                    if r == BigInt::from(0) {
                        BigInt::from(0)
                    } else if (r < BigInt::from(0)) != (b_signed < BigInt::from(0)) {
                        r + &b_signed
                    } else {
                        r
                    }
                }
            }
            _ => BigInt::from(0),
        };

        if result < BigInt::from(0) {
            result + &modulus
        } else {
            result
        }
    }

    /// Check whether all bits for a delayed operation's operands are assigned.
    ///
    /// Returns `true` if every bit literal for every argument AND the result
    /// maps to an assigned variable in the model. `assigned` is indexed by
    /// SAT variable index (0-based after applying `var_offset`).
    fn all_bits_assigned(
        &self,
        op: &DelayedBvOp,
        assigned: &[Option<bool>],
        var_offset: i32,
    ) -> bool {
        // Check result bits
        for &bit in &op.result_bits {
            let var_idx = (bit.unsigned_abs() as i32 + var_offset - 1) as usize;
            if var_idx >= assigned.len() || assigned[var_idx].is_none() {
                return false;
            }
        }
        // Check argument bits
        for &arg in &op.args {
            if let Some(bits) = self.term_to_bits.get(&arg) {
                for &bit in bits {
                    let var_idx = (bit.unsigned_abs() as i32 + var_offset - 1) as usize;
                    if var_idx >= assigned.len() || assigned[var_idx].is_none() {
                        return false;
                    }
                }
            } else {
                return false; // Argument bits not available
            }
        }
        true
    }

    /// Partial-assignment check for BCP-time theory callbacks (#8284).
    ///
    /// Unlike `check()` which requires a complete SAT model, this method
    /// works with partial assignments. For each delayed operation where ALL
    /// operand and result bits are assigned, it evaluates the operation and
    /// runs cheap axiom checks if the result is inconsistent.
    ///
    /// This ports Z3's `bv_solver::unit_propagate()` pattern: instead of
    /// waiting for a complete model, violations are detected as soon as all
    /// relevant bits are assigned, allowing the SAT solver to prune early.
    ///
    /// Only cheap axiom checks are run (no circuit escalation). Full circuit
    /// building is deferred to the complete-model `check()` to avoid expensive
    /// circuit construction on speculative partial assignments that may be
    /// backtracked.
    ///
    /// Returns conflict/axiom clauses in BV literal space.
    pub fn check_partial(&self, assigned: &[Option<bool>], var_offset: i32) -> Vec<CnfClause> {
        let mut clauses = Vec::new();

        // Build a model-like array from the partial assignment for reuse with
        // existing check_* methods. Unassigned vars default to false.
        let model: Vec<bool> = assigned.iter().map(|opt| opt.unwrap_or(false)).collect();

        for idx in 0..self.delayed_ops.len() {
            let op = &self.delayed_ops[idx];
            if op.circuit_built {
                continue;
            }

            // Only check ops where all bits are assigned
            if !self.all_bits_assigned(op, assigned, var_offset) {
                continue;
            }

            let result_val = self.eval_bits(&op.result_bits, &model, var_offset);
            let expected = self.eval_op(op, &model, var_offset);

            if result_val == expected {
                continue; // Consistent under partial assignment
            }

            // Run cheap axiom checks only (no circuit escalation during BCP)
            let cheap = match op.op {
                "bvmul" => {
                    let mut added = Vec::new();
                    if let Some(c) = self.check_mul_zero(idx, &model, var_offset) {
                        added.extend(c);
                    }
                    if added.is_empty() {
                        if let Some(c) = self.check_mul_one(idx, &model, var_offset) {
                            added.extend(c);
                        }
                    }
                    if added.is_empty() {
                        if let Some(c) = self.check_mul_power_of_2(idx, &model, var_offset) {
                            added.extend(c);
                        }
                    }
                    if added.is_empty() {
                        if let Some(c) = self.check_mul_invertibility(idx, &model, var_offset) {
                            added.extend(c);
                        }
                    }
                    added
                }
                "bvudiv" | "bvsdiv" => {
                    let mut added = Vec::new();
                    if let Some(c) = self.check_div_by_one(idx, &model, var_offset) {
                        added.extend(c);
                    } else if op.op == "bvudiv" {
                        if let Some(c) = self.check_udiv_by_zero(idx, &model, var_offset) {
                            added.extend(c);
                        }
                        if added.is_empty() {
                            if let Some(c) = self.check_udiv_self(idx, &model, var_offset) {
                                added.extend(c);
                            }
                        }
                    } else if op.op == "bvsdiv" {
                        if let Some(c) = self.check_sdiv_by_zero(idx, &model, var_offset) {
                            added.extend(c);
                        }
                    }
                    added
                }
                "bvurem" | "bvsrem" => {
                    let mut added = Vec::new();
                    if let Some(c) = self.check_rem_by_one(idx, &model, var_offset) {
                        added.extend(c);
                    } else if op.op == "bvurem" {
                        if let Some(c) = self.check_urem_by_zero(idx, &model, var_offset) {
                            added.extend(c);
                        }
                    } else if op.op == "bvsrem" {
                        if let Some(c) = self.check_srem_by_zero(idx, &model, var_offset) {
                            added.extend(c);
                        }
                    }
                    added
                }
                "bvsmod" => {
                    let mut added = Vec::new();
                    if let Some(c) = self.check_smod_by_one(idx, &model, var_offset) {
                        added.extend(c);
                    } else if let Some(c) = self.check_smod_by_zero(idx, &model, var_offset) {
                        added.extend(c);
                    }
                    added
                }
                "bvadd" => {
                    let mut added = Vec::new();
                    if let Some(c) = self.check_add_zero(idx, &model, var_offset) {
                        added.extend(c);
                    }
                    added
                }
                _ => Vec::new(),
            };

            clauses.extend(cheap);
        }

        clauses
    }

    /// Max cheap axiom attempts per delayed operation before escalating to full circuit.
    /// After this many violations with cheap axioms, the op is marked for circuit building.
    /// Z3 effectively uses 1 (try cheap, then build). We use 2 to give cheap axioms
    /// one extra chance — the first cheap axiom often just blocks the current model,
    /// and the second check may find the op is now consistent.
    const MAX_CHEAP_TRIES: u8 = 2;

    /// Check delayed operations against a SAT model (#7015).
    ///
    /// Per-op escalation strategy (porting Z3's two-phase approach):
    /// - If `cheap_tries < MAX_CHEAP_TRIES`: try cheap axioms (zero/one/invertibility)
    ///   and increment the counter. This gives cheap reasoning a chance to resolve
    ///   the violation without building the full circuit.
    /// - If `cheap_tries >= MAX_CHEAP_TRIES` or no cheap axioms fired: escalate to
    ///   full circuit building for this specific op.
    ///
    /// Returns conflict clauses in BV literal space (caller applies var_offset).
    /// Also returns indices of ops that need full circuit building.
    pub fn check(&mut self, model: &[bool], var_offset: i32) -> (Vec<CnfClause>, Vec<usize>) {
        let mut clauses = Vec::new();
        let mut needs_circuit = Vec::new();

        for idx in 0..self.delayed_ops.len() {
            if self.delayed_ops[idx].circuit_built {
                continue;
            }

            let op = &self.delayed_ops[idx];
            let result_val = self.eval_bits(&op.result_bits, model, var_offset);
            let expected = self.eval_op(op, model, var_offset);
            let op_name: &'static str = op.op;

            if result_val == expected {
                continue; // Consistent
            }

            // Try cheap axioms if we haven't exhausted attempts
            if self.delayed_ops[idx].cheap_tries < Self::MAX_CHEAP_TRIES {
                self.delayed_ops[idx].cheap_tries += 1;

                let cheap = match op_name {
                    "bvmul" => {
                        let mut added = Vec::new();
                        if let Some(c) = self.check_mul_zero(idx, model, var_offset) {
                            added.extend(c);
                        }
                        if added.is_empty() {
                            if let Some(c) = self.check_mul_one(idx, model, var_offset) {
                                added.extend(c);
                            }
                        }
                        if added.is_empty() {
                            if let Some(c) = self.check_mul_power_of_2(idx, model, var_offset) {
                                added.extend(c);
                            }
                        }
                        if added.is_empty() {
                            if let Some(c) = self.check_mul_invertibility(idx, model, var_offset) {
                                added.extend(c);
                            }
                        }
                        added
                    }
                    "bvudiv" | "bvsdiv" => {
                        let mut added = Vec::new();
                        if let Some(c) = self.check_div_by_one(idx, model, var_offset) {
                            added.extend(c);
                        } else if op_name == "bvudiv" {
                            if let Some(c) = self.check_udiv_by_zero(idx, model, var_offset) {
                                added.extend(c);
                            }
                            if added.is_empty() {
                                if let Some(c) = self.check_udiv_self(idx, model, var_offset) {
                                    added.extend(c);
                                }
                            }
                        } else if op_name == "bvsdiv" {
                            if let Some(c) = self.check_sdiv_by_zero(idx, model, var_offset) {
                                added.extend(c);
                            }
                        }
                        added
                    }
                    "bvurem" | "bvsrem" => {
                        let mut added = Vec::new();
                        if let Some(c) = self.check_rem_by_one(idx, model, var_offset) {
                            added.extend(c);
                        } else if op_name == "bvurem" {
                            if let Some(c) = self.check_urem_by_zero(idx, model, var_offset) {
                                added.extend(c);
                            }
                        } else if op_name == "bvsrem" {
                            if let Some(c) = self.check_srem_by_zero(idx, model, var_offset) {
                                added.extend(c);
                            }
                        }
                        added
                    }
                    "bvsmod" => {
                        let mut added = Vec::new();
                        if let Some(c) = self.check_smod_by_one(idx, model, var_offset) {
                            added.extend(c);
                        } else if let Some(c) = self.check_smod_by_zero(idx, model, var_offset) {
                            added.extend(c);
                        }
                        added
                    }
                    "bvadd" => {
                        let mut added = Vec::new();
                        if let Some(c) = self.check_add_zero(idx, model, var_offset) {
                            added.extend(c);
                        }
                        added
                    }
                    _ => Vec::new(),
                };

                if !cheap.is_empty() {
                    clauses.extend(cheap);
                    continue; // Cheap axiom fired — give re-solve a chance
                }
                // No cheap axiom fired for this op — fall through to circuit
            }

            // Escalate: build full circuit for this op
            self.delayed_ops[idx].circuit_built = true;
            needs_circuit.push(idx);
        }

        (clauses, needs_circuit)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Build a simple delayed mul operation for testing.
    ///
    /// Creates a 4-bit bvmul with:
    /// - arg0 bits: [1, 2, 3, 4]  (BV vars)
    /// - arg1 bits: [5, 6, 7, 8]
    /// - result bits: [9, 10, 11, 12]
    fn make_test_mul_state() -> (DelayedBvState, TermId, TermId, TermId) {
        let arg0 = TermId(100);
        let arg1 = TermId(101);
        let result = TermId(102);

        let arg0_bits: BvBits = vec![1, 2, 3, 4];
        let arg1_bits: BvBits = vec![5, 6, 7, 8];
        let result_bits: BvBits = vec![9, 10, 11, 12];

        let op = DelayedBvOp {
            term: result,
            op: "bvmul",
            args: vec![arg0, arg1],
            result_bits: result_bits.clone(),
            circuit_built: false,
            cheap_tries: 0,
        };

        let mut term_to_bits = HashMap::default();
        term_to_bits.insert(arg0, arg0_bits);
        term_to_bits.insert(arg1, arg1_bits);
        term_to_bits.insert(result, result_bits);

        let state = DelayedBvState::new(vec![op], term_to_bits);
        (state, arg0, arg1, result)
    }

    #[test]
    fn test_check_partial_detects_mul_zero_violation() {
        let (state, _arg0, _arg1, _result) = make_test_mul_state();

        // var_offset = 0 for simplicity. BV vars 1..12 map to model indices 0..11.
        let var_offset = 0;

        // Set arg0 = 0 (all bits false), arg1 = 3 (bits 0,1 true),
        // result = 5 (bits 0,2 true). This violates 0 * 3 = 0.
        let mut assigned: Vec<Option<bool>> = vec![None; 12];
        // arg0 bits [1,2,3,4] -> model indices [0,1,2,3]: all false (= 0)
        assigned[0] = Some(false);
        assigned[1] = Some(false);
        assigned[2] = Some(false);
        assigned[3] = Some(false);
        // arg1 bits [5,6,7,8] -> model indices [4,5,6,7]: = 3
        assigned[4] = Some(true); // bit 0
        assigned[5] = Some(true); // bit 1
        assigned[6] = Some(false);
        assigned[7] = Some(false);
        // result bits [9,10,11,12] -> model indices [8,9,10,11]: = 5
        assigned[8] = Some(true); // bit 0
        assigned[9] = Some(false);
        assigned[10] = Some(true); // bit 2
        assigned[11] = Some(false);

        let clauses = state.check_partial(&assigned, var_offset);
        assert!(
            !clauses.is_empty(),
            "check_partial should detect mul-by-zero violation"
        );
    }

    #[test]
    fn test_check_partial_skips_unassigned_ops() {
        let (state, _arg0, _arg1, _result) = make_test_mul_state();
        let var_offset = 0;

        // Only assign arg0 bits, leave arg1 and result unassigned.
        let mut assigned: Vec<Option<bool>> = vec![None; 12];
        assigned[0] = Some(false);
        assigned[1] = Some(false);
        assigned[2] = Some(false);
        assigned[3] = Some(false);

        let clauses = state.check_partial(&assigned, var_offset);
        assert!(
            clauses.is_empty(),
            "check_partial should skip ops with unassigned bits"
        );
    }

    #[test]
    fn test_check_partial_consistent_returns_empty() {
        let (state, _arg0, _arg1, _result) = make_test_mul_state();
        let var_offset = 0;

        // Set arg0 = 0, arg1 = 3, result = 0. This is correct: 0 * 3 = 0.
        let mut assigned: Vec<Option<bool>> = vec![None; 12];
        // arg0 = 0
        for i in 0..4 {
            assigned[i] = Some(false);
        }
        // arg1 = 3
        assigned[4] = Some(true);
        assigned[5] = Some(true);
        assigned[6] = Some(false);
        assigned[7] = Some(false);
        // result = 0
        for i in 8..12 {
            assigned[i] = Some(false);
        }

        let clauses = state.check_partial(&assigned, var_offset);
        assert!(
            clauses.is_empty(),
            "check_partial should return empty for consistent assignment"
        );
    }

    #[test]
    fn test_check_partial_mul_one_violation() {
        let (state, _arg0, _arg1, _result) = make_test_mul_state();
        let var_offset = 0;

        // Set arg0 = 1 (bit 0 true, rest false), arg1 = 5 (bits 0,2),
        // result = 3 (bits 0,1). Violates 1 * 5 = 5.
        let mut assigned: Vec<Option<bool>> = vec![None; 12];
        // arg0 = 1
        assigned[0] = Some(true);
        assigned[1] = Some(false);
        assigned[2] = Some(false);
        assigned[3] = Some(false);
        // arg1 = 5
        assigned[4] = Some(true);
        assigned[5] = Some(false);
        assigned[6] = Some(true);
        assigned[7] = Some(false);
        // result = 3 (should be 5)
        assigned[8] = Some(true);
        assigned[9] = Some(true);
        assigned[10] = Some(false);
        assigned[11] = Some(false);

        let clauses = state.check_partial(&assigned, var_offset);
        assert!(
            !clauses.is_empty(),
            "check_partial should detect mul-by-one violation"
        );
    }
}
