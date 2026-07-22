// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Batch clause emission for BV bit-blasting JIT compilation.
//!
//! BV bit-blasting generates large numbers of short, structurally similar
//! clauses — primarily ternary clauses from AND/OR/XOR/MUX gate encoding.
//! This module collects those clauses and compiles them via JIT in one batch,
//! avoiding the overhead of adding them one-by-one to the watch lists.
//!
//! ## Gate clause patterns
//!
//! | Gate | Clauses | Lengths |
//! |------|---------|---------|
//! | AND  | 3       | 2, 2, 3 |
//! | OR   | 3       | 2, 2, 3 |
//! | XOR  | 4       | 3, 3, 3, 3 |
//! | MUX  | 4       | 3, 3, 3, 3 |
//!
//! The majority are ternary, making them ideal for template stamping.

use std::collections::BTreeMap;
use std::fmt;

/// Classification of BV gate types for statistics.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[non_exhaustive]
pub enum BvGateType {
    /// AND gate: 3 clauses (2 binary + 1 ternary)
    And,
    /// OR gate: 3 clauses (2 binary + 1 ternary)
    Or,
    /// XOR gate: 4 ternary clauses
    Xor,
    /// MUX/ITE gate: 4 ternary clauses
    Mux,
    /// EQUIV/XNOR gate: 4 ternary clauses (output = a <=> b)
    Equiv,
    /// Unit clause (constant propagation)
    Unit,
    /// Other clause type
    Other,
}

impl fmt::Display for BvGateType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::And => write!(f, "AND"),
            Self::Or => write!(f, "OR"),
            Self::Xor => write!(f, "XOR"),
            Self::Mux => write!(f, "MUX"),
            Self::Equiv => write!(f, "EQUIV"),
            Self::Unit => write!(f, "Unit"),
            Self::Other => write!(f, "Other"),
        }
    }
}

/// A batch of clauses from BV bit-blasting, ready for JIT compilation.
///
/// Collects clauses classified by shape (unit, binary, ternary, longer)
/// and gate type. Clauses use the JIT literal encoding: `var * 2 + polarity`
/// where polarity 0 = positive, 1 = negative.
pub struct BvClauseBatch {
    /// All clauses: (clause_id, encoded_literals).
    clauses: Vec<(u32, Vec<u32>)>,
    /// Count of unit clauses (len == 1).
    unit_count: usize,
    /// Count of binary clauses (len == 2).
    binary_count: usize,
    /// Count of ternary clauses (len == 3).
    ternary_count: usize,
    /// Count of longer clauses (len >= 4).
    longer_count: usize,
    /// Gate type statistics.
    gate_counts: BTreeMap<BvGateType, usize>,
}

impl BvClauseBatch {
    /// Create a new empty batch.
    #[must_use]
    pub fn new() -> Self {
        Self {
            clauses: Vec::new(),
            unit_count: 0,
            binary_count: 0,
            ternary_count: 0,
            longer_count: 0,
            gate_counts: BTreeMap::new(),
        }
    }

    /// Create a new batch with pre-allocated capacity.
    #[must_use]
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            clauses: Vec::with_capacity(capacity),
            unit_count: 0,
            binary_count: 0,
            ternary_count: 0,
            longer_count: 0,
            gate_counts: BTreeMap::new(),
        }
    }

    /// Add a clause to the batch.
    ///
    /// `clause_id` is the JIT-internal clause identifier (0-indexed).
    /// `lits` are encoded literals (`var * 2 + polarity`).
    /// `gate_type` classifies the source gate for statistics.
    pub fn add_clause(&mut self, clause_id: u32, lits: &[u32], gate_type: BvGateType) {
        match lits.len() {
            0 => {} // Empty clause — should not happen in BV bitblasting.
            1 => self.unit_count += 1,
            2 => self.binary_count += 1,
            3 => self.ternary_count += 1,
            _ => self.longer_count += 1,
        }
        *self.gate_counts.entry(gate_type).or_insert(0) += 1;
        self.clauses.push((clause_id, lits.to_vec()));
    }

    /// Number of ternary clauses in the batch.
    #[must_use]
    pub fn ternary_count(&self) -> usize {
        self.ternary_count
    }

    /// Total number of clauses in the batch.
    #[must_use]
    pub fn total_count(&self) -> usize {
        self.clauses.len()
    }

    /// Whether the batch is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.clauses.is_empty()
    }

    /// Get statistics for this batch.
    #[must_use]
    pub fn stats(&self) -> BvBatchStats {
        BvBatchStats {
            total_clauses: self.clauses.len(),
            unit_clauses: self.unit_count,
            binary_clauses: self.binary_count,
            ternary_clauses: self.ternary_count,
            longer_clauses: self.longer_count,
            gate_counts: self.gate_counts.clone(),
        }
    }

    /// Consume the batch and return clauses suitable for `crate::compile()`.
    ///
    /// Filters out unit clauses (which should be propagated at preprocessing,
    /// not compiled) and binary clauses (which are more efficient in 2WL, #8261).
    /// Returns only clauses with 3+ literals.
    #[must_use]
    pub fn into_jit_clauses(self) -> Vec<(u32, Vec<u32>)> {
        self.clauses
            .into_iter()
            .filter(|(_, lits)| lits.len() >= 3)
            .collect()
    }

    /// Return a reference to all clauses (including unit/binary).
    pub fn all_clauses(&self) -> &[(u32, Vec<u32>)] {
        &self.clauses
    }
}

impl Default for BvClauseBatch {
    fn default() -> Self {
        Self::new()
    }
}

/// Statistics for a BV clause batch.
#[derive(Debug, Clone)]
pub struct BvBatchStats {
    /// Total number of clauses.
    pub total_clauses: usize,
    /// Number of unit clauses.
    pub unit_clauses: usize,
    /// Number of binary clauses.
    pub binary_clauses: usize,
    /// Number of ternary clauses.
    pub ternary_clauses: usize,
    /// Number of clauses with 4+ literals.
    pub longer_clauses: usize,
    /// Gate type distribution.
    pub gate_counts: BTreeMap<BvGateType, usize>,
}

impl fmt::Display for BvBatchStats {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "BvBatch: {} clauses (unit={}, binary={}, ternary={}, longer={})",
            self.total_clauses,
            self.unit_clauses,
            self.binary_clauses,
            self.ternary_clauses,
            self.longer_clauses,
        )?;
        if !self.gate_counts.is_empty() {
            write!(f, " gates=[")?;
            let mut first = true;
            // Sort by gate type name for deterministic output.
            let mut entries: Vec<_> = self.gate_counts.iter().collect();
            entries.sort_by_key(|(gate, _)| format!("{gate}"));
            for (gate, count) in entries {
                if !first {
                    write!(f, ", ")?;
                }
                write!(f, "{gate}:{count}")?;
                first = false;
            }
            write!(f, "]")?;
        }
        Ok(())
    }
}

/// Description of a single BV gate for batch compilation.
///
/// Each gate has a type, input variable(s), and an output variable.
/// Variables use JIT literal encoding: `var * 2 + polarity`.
/// For template stamping, we store the *variable indices* (not encoded literals),
/// and the template handles polarity internally based on the gate semantics.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BvGateDesc {
    /// The gate type.
    pub gate_type: BvGateType,
    /// First input variable (JIT variable index, 0-based).
    pub input_a: u32,
    /// Second input variable (JIT variable index, 0-based).
    /// For AND/OR/XOR/Equiv: second operand.
    /// For Mux: the "else" (false-branch) operand.
    pub input_b: u32,
    /// Output variable (JIT variable index, 0-based).
    pub output: u32,
    /// Selector variable for MUX gates (JIT variable index, 0-based).
    /// Ignored for non-MUX gate types.
    pub selector: u32,
}

impl BvGateDesc {
    /// Create an AND gate: output = input_a AND input_b.
    #[must_use]
    pub fn and(input_a: u32, input_b: u32, output: u32) -> Self {
        Self {
            gate_type: BvGateType::And,
            input_a,
            input_b,
            output,
            selector: 0,
        }
    }

    /// Create an OR gate: output = input_a OR input_b.
    #[must_use]
    pub fn or(input_a: u32, input_b: u32, output: u32) -> Self {
        Self {
            gate_type: BvGateType::Or,
            input_a,
            input_b,
            output,
            selector: 0,
        }
    }

    /// Create a XOR gate: output = input_a XOR input_b.
    #[must_use]
    pub fn xor(input_a: u32, input_b: u32, output: u32) -> Self {
        Self {
            gate_type: BvGateType::Xor,
            input_a,
            input_b,
            output,
            selector: 0,
        }
    }

    /// Create a MUX/ITE gate: output = if selector then input_a else input_b.
    #[must_use]
    pub fn mux(selector: u32, input_a: u32, input_b: u32, output: u32) -> Self {
        Self {
            gate_type: BvGateType::Mux,
            input_a,
            input_b,
            output,
            selector,
        }
    }

    /// Create an equivalence gate: output = (input_a <=> input_b).
    /// Encoded as XNOR: 4 ternary clauses.
    #[must_use]
    pub fn equiv(input_a: u32, input_b: u32, output: u32) -> Self {
        Self {
            gate_type: BvGateType::Equiv,
            input_a,
            input_b,
            output,
            selector: 0,
        }
    }
}

/// Encode a positive literal for variable `var` in JIT encoding.
#[inline]
fn pos_lit(var: u32) -> u32 {
    var * 2
}

/// Encode a negative literal for variable `var` in JIT encoding.
#[inline]
fn neg_lit(var: u32) -> u32 {
    var * 2 + 1
}

/// Stamp AND gate clauses into the output buffer.
///
/// AND gate: output = a AND b
/// Clauses:
///   (-output, a)         -- output => a
///   (-output, b)         -- output => b
///   (-a, -b, output)     -- a AND b => output
///
/// Returns the number of clauses emitted (always 3).
fn stamp_and_gate(
    a: u32,
    b: u32,
    output: u32,
    clause_id_start: u32,
    buf: &mut Vec<(u32, Vec<u32>)>,
) -> usize {
    // Binary: (-output OR a)
    buf.push((clause_id_start, vec![neg_lit(output), pos_lit(a)]));
    // Binary: (-output OR b)
    buf.push((clause_id_start + 1, vec![neg_lit(output), pos_lit(b)]));
    // Ternary: (-a OR -b OR output)
    buf.push((
        clause_id_start + 2,
        vec![neg_lit(a), neg_lit(b), pos_lit(output)],
    ));
    3
}

/// Stamp OR gate clauses into the output buffer.
///
/// OR gate: output = a OR b
/// Clauses:
///   (-a, output)         -- a => output
///   (-b, output)         -- b => output
///   (-output, a, b)      -- output => a OR b
///
/// Returns the number of clauses emitted (always 3).
fn stamp_or_gate(
    a: u32,
    b: u32,
    output: u32,
    clause_id_start: u32,
    buf: &mut Vec<(u32, Vec<u32>)>,
) -> usize {
    // Binary: (-a OR output)
    buf.push((clause_id_start, vec![neg_lit(a), pos_lit(output)]));
    // Binary: (-b OR output)
    buf.push((clause_id_start + 1, vec![neg_lit(b), pos_lit(output)]));
    // Ternary: (-output OR a OR b)
    buf.push((
        clause_id_start + 2,
        vec![neg_lit(output), pos_lit(a), pos_lit(b)],
    ));
    3
}

/// Stamp XOR gate clauses into the output buffer.
///
/// XOR gate: output = a XOR b
/// Clauses (all ternary):
///   (-a, -b, -output)    -- a=1, b=1 => output=0
///   (-a, b, output)      -- a=0, b=1 => output=1
///   (a, -b, output)      -- a=1, b=0 => output=1
///   (a, b, -output)      -- a=0, b=0 => output=0
///
/// Returns the number of clauses emitted (always 4).
fn stamp_xor_gate(
    a: u32,
    b: u32,
    output: u32,
    clause_id_start: u32,
    buf: &mut Vec<(u32, Vec<u32>)>,
) -> usize {
    buf.push((
        clause_id_start,
        vec![neg_lit(a), neg_lit(b), neg_lit(output)],
    ));
    buf.push((
        clause_id_start + 1,
        vec![neg_lit(a), pos_lit(b), pos_lit(output)],
    ));
    buf.push((
        clause_id_start + 2,
        vec![pos_lit(a), neg_lit(b), pos_lit(output)],
    ));
    buf.push((
        clause_id_start + 3,
        vec![pos_lit(a), pos_lit(b), neg_lit(output)],
    ));
    4
}

/// Stamp MUX/ITE gate clauses into the output buffer.
///
/// MUX gate: output = if sel then a else b
/// Clauses (all ternary):
///   (-sel, -a, output)   -- sel=1, a=1 => output=1
///   (-sel, a, -output)   -- sel=1, a=0 => output=0
///   (sel, -b, output)    -- sel=0, b=1 => output=1
///   (sel, b, -output)    -- sel=0, b=0 => output=0
///
/// Returns the number of clauses emitted (always 4).
fn stamp_mux_gate(
    sel: u32,
    a: u32,
    b: u32,
    output: u32,
    clause_id_start: u32,
    buf: &mut Vec<(u32, Vec<u32>)>,
) -> usize {
    buf.push((
        clause_id_start,
        vec![neg_lit(sel), neg_lit(a), pos_lit(output)],
    ));
    buf.push((
        clause_id_start + 1,
        vec![neg_lit(sel), pos_lit(a), neg_lit(output)],
    ));
    buf.push((
        clause_id_start + 2,
        vec![pos_lit(sel), neg_lit(b), pos_lit(output)],
    ));
    buf.push((
        clause_id_start + 3,
        vec![pos_lit(sel), pos_lit(b), neg_lit(output)],
    ));
    4
}

/// Stamp EQUIV/XNOR gate clauses into the output buffer.
///
/// EQUIV gate: output = (a <=> b) = NOT(a XOR b)
/// This is XOR with negated output polarity.
/// Clauses (all ternary):
///   (-a, -b, output)     -- a=1, b=1 => output=1
///   (-a, b, -output)     -- a=0, b=1 => output=0
///   (a, -b, -output)     -- a=1, b=0 => output=0
///   (a, b, output)       -- a=0, b=0 => output=1
///
/// Returns the number of clauses emitted (always 4).
fn stamp_equiv_gate(
    a: u32,
    b: u32,
    output: u32,
    clause_id_start: u32,
    buf: &mut Vec<(u32, Vec<u32>)>,
) -> usize {
    buf.push((
        clause_id_start,
        vec![neg_lit(a), neg_lit(b), pos_lit(output)],
    ));
    buf.push((
        clause_id_start + 1,
        vec![neg_lit(a), pos_lit(b), neg_lit(output)],
    ));
    buf.push((
        clause_id_start + 2,
        vec![pos_lit(a), neg_lit(b), neg_lit(output)],
    ));
    buf.push((
        clause_id_start + 3,
        vec![pos_lit(a), pos_lit(b), pos_lit(output)],
    ));
    4
}

/// Compiler that takes a batch of BV gate descriptions and emits all clauses
/// for all gates into a flat buffer.
///
/// This amortizes the overhead of clause emission across many gates by:
/// 1. Pre-allocating the output buffer based on known gate clause counts
/// 2. Using template stamping functions that inline the clause patterns
/// 3. Returning all clauses in a single flat buffer ready for `BvClauseBatch`
///
/// ## Usage
///
/// ```rust
/// use ay_jit::batch::{BvGateCompiler, BvGateDesc};
///
/// let gates = vec![
///     BvGateDesc::and(0, 1, 2),
///     BvGateDesc::xor(3, 4, 5),
///     BvGateDesc::mux(6, 7, 8, 9),
/// ];
///
/// let compiler = BvGateCompiler::new(&gates);
/// let batch = compiler.compile();
/// ```
pub struct BvGateCompiler<'a> {
    gates: &'a [BvGateDesc],
}

impl<'a> BvGateCompiler<'a> {
    /// Create a new gate compiler from a slice of gate descriptions.
    #[must_use]
    pub fn new(gates: &'a [BvGateDesc]) -> Self {
        Self { gates }
    }

    /// Count the total number of clauses that will be emitted.
    #[must_use]
    pub fn total_clause_count(&self) -> usize {
        self.gates
            .iter()
            .map(|g| Self::clauses_per_gate(g.gate_type))
            .sum()
    }

    /// Number of clauses emitted for a given gate type.
    #[must_use]
    pub fn clauses_per_gate(gate_type: BvGateType) -> usize {
        match gate_type {
            BvGateType::And | BvGateType::Or => 3,
            BvGateType::Xor | BvGateType::Mux | BvGateType::Equiv => 4,
            BvGateType::Unit => 1,
            BvGateType::Other => 0,
        }
    }

    /// Compute the maximum variable index referenced by any gate.
    /// Returns 0 if there are no gates.
    #[must_use]
    pub fn max_var(&self) -> u32 {
        self.gates.iter().fold(0u32, |acc, g| {
            let mut m = acc.max(g.input_a).max(g.input_b).max(g.output);
            if g.gate_type == BvGateType::Mux {
                m = m.max(g.selector);
            }
            m
        })
    }

    /// Compile all gates into a `BvClauseBatch`.
    ///
    /// Stamps out all clauses for each gate using the appropriate template
    /// function. The returned batch can be passed directly to
    /// the BV batch compilation pipeline.
    #[must_use]
    pub fn compile(&self) -> BvClauseBatch {
        let total_clauses = self.total_clause_count();
        let mut buf: Vec<(u32, Vec<u32>)> = Vec::with_capacity(total_clauses);
        let mut clause_id: u32 = 0;

        for gate in self.gates {
            let emitted = match gate.gate_type {
                BvGateType::And => {
                    stamp_and_gate(gate.input_a, gate.input_b, gate.output, clause_id, &mut buf)
                }
                BvGateType::Or => {
                    stamp_or_gate(gate.input_a, gate.input_b, gate.output, clause_id, &mut buf)
                }
                BvGateType::Xor => {
                    stamp_xor_gate(gate.input_a, gate.input_b, gate.output, clause_id, &mut buf)
                }
                BvGateType::Mux => stamp_mux_gate(
                    gate.selector,
                    gate.input_a,
                    gate.input_b,
                    gate.output,
                    clause_id,
                    &mut buf,
                ),
                BvGateType::Equiv => {
                    stamp_equiv_gate(gate.input_a, gate.input_b, gate.output, clause_id, &mut buf)
                }
                BvGateType::Unit | BvGateType::Other => 0,
            };
            clause_id += emitted as u32;
        }

        // Convert the flat buffer into a BvClauseBatch with proper classification.
        let mut batch = BvClauseBatch::with_capacity(buf.len());
        // We need to re-attribute clauses to their source gates for stats.
        let mut buf_idx = 0;
        for gate in self.gates {
            let count = Self::clauses_per_gate(gate.gate_type);
            for _ in 0..count {
                if buf_idx < buf.len() {
                    let (cid, ref lits) = buf[buf_idx];
                    batch.add_clause(cid, lits, gate.gate_type);
                    buf_idx += 1;
                }
            }
        }

        batch
    }

    /// Compile all gates into a flat clause buffer.
    ///
    /// Returns `(clause_id, encoded_literals)` pairs suitable for passing
    /// to `crate::compile()`. This avoids the intermediate `BvClauseBatch`
    /// when the caller wants raw clause data.
    #[must_use]
    pub fn compile_flat(&self) -> Vec<(u32, Vec<u32>)> {
        let total_clauses = self.total_clause_count();
        let mut buf: Vec<(u32, Vec<u32>)> = Vec::with_capacity(total_clauses);
        let mut clause_id: u32 = 0;

        for gate in self.gates {
            let emitted = match gate.gate_type {
                BvGateType::And => {
                    stamp_and_gate(gate.input_a, gate.input_b, gate.output, clause_id, &mut buf)
                }
                BvGateType::Or => {
                    stamp_or_gate(gate.input_a, gate.input_b, gate.output, clause_id, &mut buf)
                }
                BvGateType::Xor => {
                    stamp_xor_gate(gate.input_a, gate.input_b, gate.output, clause_id, &mut buf)
                }
                BvGateType::Mux => stamp_mux_gate(
                    gate.selector,
                    gate.input_a,
                    gate.input_b,
                    gate.output,
                    clause_id,
                    &mut buf,
                ),
                BvGateType::Equiv => {
                    stamp_equiv_gate(gate.input_a, gate.input_b, gate.output, clause_id, &mut buf)
                }
                BvGateType::Unit | BvGateType::Other => 0,
            };
            clause_id += emitted as u32;
        }

        buf
    }

    /// Compile gates and emit into an existing `BvClauseBatch`.
    ///
    /// Appends clauses to `batch`, using `clause_id_offset` as the starting
    /// clause ID. Returns the number of clauses emitted.
    pub fn compile_into(&self, batch: &mut BvClauseBatch, clause_id_offset: u32) -> u32 {
        let mut clause_id = clause_id_offset;
        let mut buf: Vec<(u32, Vec<u32>)> = Vec::with_capacity(self.total_clause_count());

        for gate in self.gates {
            let count_before = buf.len();
            let emitted = match gate.gate_type {
                BvGateType::And => {
                    stamp_and_gate(gate.input_a, gate.input_b, gate.output, clause_id, &mut buf)
                }
                BvGateType::Or => {
                    stamp_or_gate(gate.input_a, gate.input_b, gate.output, clause_id, &mut buf)
                }
                BvGateType::Xor => {
                    stamp_xor_gate(gate.input_a, gate.input_b, gate.output, clause_id, &mut buf)
                }
                BvGateType::Mux => stamp_mux_gate(
                    gate.selector,
                    gate.input_a,
                    gate.input_b,
                    gate.output,
                    clause_id,
                    &mut buf,
                ),
                BvGateType::Equiv => {
                    stamp_equiv_gate(gate.input_a, gate.input_b, gate.output, clause_id, &mut buf)
                }
                BvGateType::Unit | BvGateType::Other => 0,
            };

            // Add the emitted clauses to the batch with gate type attribution.
            for (cid, lits) in &buf[count_before..] {
                batch.add_clause(*cid, lits, gate.gate_type);
            }

            clause_id += emitted as u32;
        }

        clause_id - clause_id_offset
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bv_clause_batch_empty() {
        let batch = BvClauseBatch::new();
        assert!(batch.is_empty());
        assert_eq!(batch.total_count(), 0);
        assert_eq!(batch.ternary_count(), 0);
    }

    #[test]
    fn test_bv_clause_batch_classification() {
        let mut batch = BvClauseBatch::new();

        // Unit clause
        batch.add_clause(0, &[2], BvGateType::Unit);
        // Binary clause (AND gate forward implication)
        batch.add_clause(1, &[1, 4], BvGateType::And);
        // Ternary clause (AND gate backward implication)
        batch.add_clause(2, &[0, 3, 5], BvGateType::And);
        // XOR ternary clauses
        batch.add_clause(3, &[1, 3, 5], BvGateType::Xor);
        batch.add_clause(4, &[1, 2, 4], BvGateType::Xor);
        batch.add_clause(5, &[0, 3, 4], BvGateType::Xor);
        batch.add_clause(6, &[0, 2, 5], BvGateType::Xor);

        assert_eq!(batch.total_count(), 7);
        assert_eq!(batch.ternary_count(), 5);

        let stats = batch.stats();
        assert_eq!(stats.unit_clauses, 1);
        assert_eq!(stats.binary_clauses, 1);
        assert_eq!(stats.ternary_clauses, 5);
        assert_eq!(stats.longer_clauses, 0);
        assert_eq!(stats.gate_counts[&BvGateType::And], 2);
        assert_eq!(stats.gate_counts[&BvGateType::Xor], 4);
        assert_eq!(stats.gate_counts[&BvGateType::Unit], 1);
    }

    #[test]
    fn test_into_jit_clauses_filters_short() {
        let mut batch = BvClauseBatch::new();

        // Add unit and binary clauses (should be filtered)
        batch.add_clause(0, &[2], BvGateType::Unit);
        batch.add_clause(1, &[1, 4], BvGateType::And);

        // Add ternary clauses (should be kept)
        batch.add_clause(2, &[0, 3, 5], BvGateType::Xor);
        batch.add_clause(3, &[1, 2, 4], BvGateType::Xor);

        let jit_clauses = batch.into_jit_clauses();
        assert_eq!(jit_clauses.len(), 2);
        assert_eq!(jit_clauses[0].0, 2);
        assert_eq!(jit_clauses[1].0, 3);
    }

    // test_compile_bv_batch_too_small and test_compile_bv_batch_sufficient_clauses
    // removed in #8517 (compile_bv_batch was BCP JIT infrastructure).

    #[test]
    fn test_bv_batch_stats_display() {
        let mut batch = BvClauseBatch::new();
        batch.add_clause(0, &[0, 2, 4], BvGateType::And);
        batch.add_clause(1, &[1, 3, 5], BvGateType::Xor);

        let stats = batch.stats();
        let display = format!("{stats}");
        assert!(display.contains("2 clauses"));
        assert!(display.contains("ternary=2"));
    }

    #[test]
    fn test_bv_clause_batch_with_capacity() {
        let batch = BvClauseBatch::with_capacity(1000);
        assert!(batch.is_empty());
        assert_eq!(batch.total_count(), 0);
    }

    // --- Gate template stamping tests ---

    /// Helper: check a clause contains exactly the expected encoded literals.
    fn assert_clause_lits(clauses: &[(u32, Vec<u32>)], idx: usize, expected: &[u32]) {
        let (_, ref lits) = clauses[idx];
        assert_eq!(lits, expected, "clause {idx} mismatch");
    }

    #[test]
    fn test_stamp_and_gate_clauses() {
        // AND gate: output(2) = a(0) AND b(1)
        // Expected clauses:
        //   (-output, a)     = (neg_lit(2), pos_lit(0)) = (5, 0)
        //   (-output, b)     = (neg_lit(2), pos_lit(1)) = (5, 2)
        //   (-a, -b, output) = (neg_lit(0), neg_lit(1), pos_lit(2)) = (1, 3, 4)
        let mut buf = Vec::new();
        let count = stamp_and_gate(0, 1, 2, 0, &mut buf);
        assert_eq!(count, 3);
        assert_eq!(buf.len(), 3);
        assert_clause_lits(&buf, 0, &[5, 0]); // -out, a
        assert_clause_lits(&buf, 1, &[5, 2]); // -out, b
        assert_clause_lits(&buf, 2, &[1, 3, 4]); // -a, -b, out
    }

    #[test]
    fn test_stamp_or_gate_clauses() {
        // OR gate: output(2) = a(0) OR b(1)
        // Expected clauses:
        //   (-a, output)     = (neg_lit(0), pos_lit(2)) = (1, 4)
        //   (-b, output)     = (neg_lit(1), pos_lit(2)) = (3, 4)
        //   (-output, a, b)  = (neg_lit(2), pos_lit(0), pos_lit(1)) = (5, 0, 2)
        let mut buf = Vec::new();
        let count = stamp_or_gate(0, 1, 2, 0, &mut buf);
        assert_eq!(count, 3);
        assert_eq!(buf.len(), 3);
        assert_clause_lits(&buf, 0, &[1, 4]); // -a, out
        assert_clause_lits(&buf, 1, &[3, 4]); // -b, out
        assert_clause_lits(&buf, 2, &[5, 0, 2]); // -out, a, b
    }

    #[test]
    fn test_stamp_xor_gate_clauses() {
        // XOR gate: output(2) = a(0) XOR b(1)
        // Clauses:
        //   (-a, -b, -out)  = (1, 3, 5)
        //   (-a, b, out)    = (1, 2, 4)
        //   (a, -b, out)    = (0, 3, 4)
        //   (a, b, -out)    = (0, 2, 5)
        let mut buf = Vec::new();
        let count = stamp_xor_gate(0, 1, 2, 0, &mut buf);
        assert_eq!(count, 4);
        assert_eq!(buf.len(), 4);
        assert_clause_lits(&buf, 0, &[1, 3, 5]); // -a, -b, -out
        assert_clause_lits(&buf, 1, &[1, 2, 4]); // -a, b, out
        assert_clause_lits(&buf, 2, &[0, 3, 4]); // a, -b, out
        assert_clause_lits(&buf, 3, &[0, 2, 5]); // a, b, -out
    }

    #[test]
    fn test_stamp_mux_gate_clauses() {
        // MUX gate: output(3) = if sel(0) then a(1) else b(2)
        // Clauses:
        //   (-sel, -a, out)  = (1, 3, 6)
        //   (-sel, a, -out)  = (1, 2, 7)
        //   (sel, -b, out)   = (0, 5, 6)
        //   (sel, b, -out)   = (0, 4, 7)
        let mut buf = Vec::new();
        let count = stamp_mux_gate(0, 1, 2, 3, 0, &mut buf);
        assert_eq!(count, 4);
        assert_eq!(buf.len(), 4);
        assert_clause_lits(&buf, 0, &[1, 3, 6]); // -sel, -a, out
        assert_clause_lits(&buf, 1, &[1, 2, 7]); // -sel, a, -out
        assert_clause_lits(&buf, 2, &[0, 5, 6]); // sel, -b, out
        assert_clause_lits(&buf, 3, &[0, 4, 7]); // sel, b, -out
    }

    #[test]
    fn test_stamp_equiv_gate_clauses() {
        // EQUIV gate: output(2) = (a(0) <=> b(1)) = NOT(a XOR b)
        // Clauses (XOR with flipped output polarity):
        //   (-a, -b, out)   = (1, 3, 4)
        //   (-a, b, -out)   = (1, 2, 5)
        //   (a, -b, -out)   = (0, 3, 5)
        //   (a, b, out)     = (0, 2, 4)
        let mut buf = Vec::new();
        let count = stamp_equiv_gate(0, 1, 2, 0, &mut buf);
        assert_eq!(count, 4);
        assert_eq!(buf.len(), 4);
        assert_clause_lits(&buf, 0, &[1, 3, 4]); // -a, -b, out
        assert_clause_lits(&buf, 1, &[1, 2, 5]); // -a, b, -out
        assert_clause_lits(&buf, 2, &[0, 3, 5]); // a, -b, -out
        assert_clause_lits(&buf, 3, &[0, 2, 4]); // a, b, out
    }

    #[test]
    fn test_and_gate_truth_table() {
        // Verify AND gate clauses are satisfiable exactly for the AND truth table.
        // For each (a_val, b_val) assignment, check that the clauses force
        // output to be a AND b.
        for a_val in [false, true] {
            for b_val in [false, true] {
                let expected_out = a_val && b_val;
                let mut buf = Vec::new();
                stamp_and_gate(0, 1, 2, 0, &mut buf);

                // Check: with a=a_val, b=b_val, out=expected_out, all clauses satisfied.
                assert!(
                    all_clauses_satisfied(&buf, 0, a_val, 1, b_val, 2, expected_out),
                    "AND gate unsatisfied for a={a_val}, b={b_val}, out={expected_out}"
                );
                // Check: with a=a_val, b=b_val, out=!expected_out, some clause violated.
                assert!(
                    !all_clauses_satisfied(&buf, 0, a_val, 1, b_val, 2, !expected_out),
                    "AND gate should be violated for a={a_val}, b={b_val}, out={}",
                    !expected_out
                );
            }
        }
    }

    #[test]
    fn test_or_gate_truth_table() {
        for a_val in [false, true] {
            for b_val in [false, true] {
                let expected_out = a_val || b_val;
                let mut buf = Vec::new();
                stamp_or_gate(0, 1, 2, 0, &mut buf);

                assert!(
                    all_clauses_satisfied(&buf, 0, a_val, 1, b_val, 2, expected_out),
                    "OR gate unsatisfied for a={a_val}, b={b_val}, out={expected_out}"
                );
                assert!(
                    !all_clauses_satisfied(&buf, 0, a_val, 1, b_val, 2, !expected_out),
                    "OR gate should be violated for a={a_val}, b={b_val}, out={}",
                    !expected_out
                );
            }
        }
    }

    #[test]
    fn test_xor_gate_truth_table() {
        for a_val in [false, true] {
            for b_val in [false, true] {
                let expected_out = a_val ^ b_val;
                let mut buf = Vec::new();
                stamp_xor_gate(0, 1, 2, 0, &mut buf);

                assert!(
                    all_clauses_satisfied(&buf, 0, a_val, 1, b_val, 2, expected_out),
                    "XOR gate unsatisfied for a={a_val}, b={b_val}, out={expected_out}"
                );
                assert!(
                    !all_clauses_satisfied(&buf, 0, a_val, 1, b_val, 2, !expected_out),
                    "XOR gate should be violated for a={a_val}, b={b_val}, out={}",
                    !expected_out
                );
            }
        }
    }

    #[test]
    fn test_mux_gate_truth_table() {
        // MUX: output = if sel then a else b
        // Uses vars: sel=0, a=1, b=2, output=3
        for sel_val in [false, true] {
            for a_val in [false, true] {
                for b_val in [false, true] {
                    let expected_out = if sel_val { a_val } else { b_val };
                    let mut buf = Vec::new();
                    stamp_mux_gate(0, 1, 2, 3, 0, &mut buf);

                    let satisfied = all_clauses_satisfied_4var(
                        &buf,
                        0,
                        sel_val,
                        1,
                        a_val,
                        2,
                        b_val,
                        3,
                        expected_out,
                    );
                    assert!(
                        satisfied,
                        "MUX gate unsatisfied for sel={sel_val}, a={a_val}, b={b_val}, out={expected_out}"
                    );

                    let violated = all_clauses_satisfied_4var(
                        &buf,
                        0,
                        sel_val,
                        1,
                        a_val,
                        2,
                        b_val,
                        3,
                        !expected_out,
                    );
                    assert!(
                        !violated,
                        "MUX gate should be violated for sel={sel_val}, a={a_val}, b={b_val}, out={}", !expected_out
                    );
                }
            }
        }
    }

    #[test]
    fn test_equiv_gate_truth_table() {
        for a_val in [false, true] {
            for b_val in [false, true] {
                let expected_out = a_val == b_val; // XNOR
                let mut buf = Vec::new();
                stamp_equiv_gate(0, 1, 2, 0, &mut buf);

                assert!(
                    all_clauses_satisfied(&buf, 0, a_val, 1, b_val, 2, expected_out),
                    "EQUIV gate unsatisfied for a={a_val}, b={b_val}, out={expected_out}"
                );
                assert!(
                    !all_clauses_satisfied(&buf, 0, a_val, 1, b_val, 2, !expected_out),
                    "EQUIV gate should be violated for a={a_val}, b={b_val}, out={}",
                    !expected_out
                );
            }
        }
    }

    /// Check if a literal is satisfied by the given variable assignment.
    fn lit_satisfied(lit: u32, var_vals: &[(u32, bool)]) -> bool {
        let var = lit / 2;
        let is_neg = lit % 2 == 1;
        for &(v, val) in var_vals {
            if v == var {
                return if is_neg { !val } else { val };
            }
        }
        // Variable not assigned — treat as satisfiable (partial assignment).
        true
    }

    /// Check if all clauses in a buffer are satisfied by a 3-variable assignment.
    fn all_clauses_satisfied(
        clauses: &[(u32, Vec<u32>)],
        va: u32,
        a_val: bool,
        vb: u32,
        b_val: bool,
        vout: u32,
        out_val: bool,
    ) -> bool {
        let vals = [(va, a_val), (vb, b_val), (vout, out_val)];
        for (_, lits) in clauses {
            let clause_sat = lits.iter().any(|&l| lit_satisfied(l, &vals));
            if !clause_sat {
                return false;
            }
        }
        true
    }

    /// Check if all clauses are satisfied by a 4-variable assignment (for MUX).
    fn all_clauses_satisfied_4var(
        clauses: &[(u32, Vec<u32>)],
        v0: u32,
        val0: bool,
        v1: u32,
        val1: bool,
        v2: u32,
        val2: bool,
        v3: u32,
        val3: bool,
    ) -> bool {
        let vals = [(v0, val0), (v1, val1), (v2, val2), (v3, val3)];
        for (_, lits) in clauses {
            let clause_sat = lits.iter().any(|&l| lit_satisfied(l, &vals));
            if !clause_sat {
                return false;
            }
        }
        true
    }

    // --- BvGateCompiler tests ---

    #[test]
    fn test_gate_compiler_empty() {
        let gates: Vec<BvGateDesc> = vec![];
        let compiler = BvGateCompiler::new(&gates);
        assert_eq!(compiler.total_clause_count(), 0);
        let batch = compiler.compile();
        assert!(batch.is_empty());
    }

    #[test]
    fn test_gate_compiler_single_and() {
        let gates = vec![BvGateDesc::and(0, 1, 2)];
        let compiler = BvGateCompiler::new(&gates);
        assert_eq!(compiler.total_clause_count(), 3);
        assert_eq!(compiler.max_var(), 2);

        let batch = compiler.compile();
        assert_eq!(batch.total_count(), 3);

        let stats = batch.stats();
        assert_eq!(stats.binary_clauses, 2);
        assert_eq!(stats.ternary_clauses, 1);
        assert_eq!(stats.gate_counts[&BvGateType::And], 3);
    }

    #[test]
    fn test_gate_compiler_single_xor() {
        let gates = vec![BvGateDesc::xor(0, 1, 2)];
        let compiler = BvGateCompiler::new(&gates);
        assert_eq!(compiler.total_clause_count(), 4);

        let batch = compiler.compile();
        assert_eq!(batch.total_count(), 4);

        let stats = batch.stats();
        assert_eq!(stats.ternary_clauses, 4);
        assert_eq!(stats.gate_counts[&BvGateType::Xor], 4);
    }

    #[test]
    fn test_gate_compiler_single_mux() {
        let gates = vec![BvGateDesc::mux(0, 1, 2, 3)];
        let compiler = BvGateCompiler::new(&gates);
        assert_eq!(compiler.total_clause_count(), 4);
        assert_eq!(compiler.max_var(), 3);

        let batch = compiler.compile();
        assert_eq!(batch.total_count(), 4);

        let stats = batch.stats();
        assert_eq!(stats.ternary_clauses, 4);
        assert_eq!(stats.gate_counts[&BvGateType::Mux], 4);
    }

    #[test]
    fn test_gate_compiler_mixed_gates() {
        let gates = vec![
            BvGateDesc::and(0, 1, 2),       // 3 clauses
            BvGateDesc::xor(3, 4, 5),       // 4 clauses
            BvGateDesc::or(6, 7, 8),        // 3 clauses
            BvGateDesc::mux(9, 10, 11, 12), // 4 clauses
        ];
        let compiler = BvGateCompiler::new(&gates);
        assert_eq!(compiler.total_clause_count(), 14);
        assert_eq!(compiler.max_var(), 12);

        let batch = compiler.compile();
        assert_eq!(batch.total_count(), 14);

        let stats = batch.stats();
        // AND: 2 binary + 1 ternary, OR: 2 binary + 1 ternary, XOR: 4 ternary, MUX: 4 ternary
        assert_eq!(stats.binary_clauses, 4);
        assert_eq!(stats.ternary_clauses, 10);
    }

    #[test]
    fn test_gate_compiler_clause_ids_sequential() {
        let gates = vec![
            BvGateDesc::and(0, 1, 2), // IDs 0, 1, 2
            BvGateDesc::xor(3, 4, 5), // IDs 3, 4, 5, 6
        ];
        let compiler = BvGateCompiler::new(&gates);
        let flat = compiler.compile_flat();
        assert_eq!(flat.len(), 7);

        // Verify clause IDs are sequential.
        for (i, (cid, _)) in flat.iter().enumerate() {
            assert_eq!(*cid, i as u32, "clause ID mismatch at index {i}");
        }
    }

    #[test]
    fn test_gate_compiler_compile_into() {
        let gates = vec![BvGateDesc::xor(0, 1, 2)];
        let compiler = BvGateCompiler::new(&gates);

        let mut batch = BvClauseBatch::new();
        // Pre-populate with one clause to test offset.
        batch.add_clause(0, &[0, 2, 4], BvGateType::Other);

        let emitted = compiler.compile_into(&mut batch, 1);
        assert_eq!(emitted, 4);
        assert_eq!(batch.total_count(), 5); // 1 pre-existing + 4 from XOR
    }

    #[test]
    fn test_gate_compiler_large_batch() {
        // Simulate 32-bit BV addition: ~100 gates (AND + XOR per bit).
        let mut gates = Vec::with_capacity(64);
        for i in 0..32u32 {
            let a = i * 3;
            let b = i * 3 + 1;
            let out = i * 3 + 2;
            gates.push(BvGateDesc::and(a, b, out));
            gates.push(BvGateDesc::xor(a, b, out + 96));
        }

        let compiler = BvGateCompiler::new(&gates);
        // 32 AND gates (3 each) + 32 XOR gates (4 each) = 96 + 128 = 224
        assert_eq!(compiler.total_clause_count(), 224);

        let batch = compiler.compile();
        assert_eq!(batch.total_count(), 224);
    }

    #[test]
    fn test_gate_desc_constructors() {
        let and = BvGateDesc::and(0, 1, 2);
        assert_eq!(and.gate_type, BvGateType::And);
        assert_eq!(and.input_a, 0);
        assert_eq!(and.input_b, 1);
        assert_eq!(and.output, 2);

        let or = BvGateDesc::or(3, 4, 5);
        assert_eq!(or.gate_type, BvGateType::Or);

        let xor = BvGateDesc::xor(6, 7, 8);
        assert_eq!(xor.gate_type, BvGateType::Xor);

        let mux = BvGateDesc::mux(9, 10, 11, 12);
        assert_eq!(mux.gate_type, BvGateType::Mux);
        assert_eq!(mux.selector, 9);
        assert_eq!(mux.input_a, 10);
        assert_eq!(mux.input_b, 11);
        assert_eq!(mux.output, 12);
    }

    #[test]
    fn test_clauses_per_gate() {
        assert_eq!(BvGateCompiler::clauses_per_gate(BvGateType::And), 3);
        assert_eq!(BvGateCompiler::clauses_per_gate(BvGateType::Or), 3);
        assert_eq!(BvGateCompiler::clauses_per_gate(BvGateType::Xor), 4);
        assert_eq!(BvGateCompiler::clauses_per_gate(BvGateType::Mux), 4);
        assert_eq!(BvGateCompiler::clauses_per_gate(BvGateType::Unit), 1);
        assert_eq!(BvGateCompiler::clauses_per_gate(BvGateType::Other), 0);
    }
}
