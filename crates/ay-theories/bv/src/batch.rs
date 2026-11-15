// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Deterministic BV bit-blast batch and template contract.
//!
//! The live BV bit-blaster still emits through `BvSolver::add_clause`, which
//! appends one [`CnfClause`] at a time. This module is a data-only contract for
//! the external code generation path: callers can extract the emitted CNF into a flat,
//! deterministic buffer or stamp known BV gate templates into that same layout.
//!
//! No code here compiles, installs, or dispatches native code. Runtime solving
//! continues to use the existing SAT clause path until a verified external code generation
//! compiler and install boundary consume this contract.

use super::*;

/// SMT-COMP matrix counter for useful BV batch-template applications.
///
/// The current BV batch/template surface is a deterministic CNF data contract,
/// not an installed external code generation solver-program path. Until that install boundary
/// exists, this counter must remain zero so runner-side gates fail closed.
pub const SMT_BV_BATCH_TEMPLATE_APPLICATION_COUNTER: &str = "smt_bv_batch_template_applications";

/// Return the current useful SMT BV batch-template application count.
///
/// This deliberately reports a zero stub: stamping templates into an in-memory
/// clause batch is not a validated native application.
#[must_use]
pub const fn smt_bv_batch_template_application_count() -> u64 {
    0
}

/// Largest number of entries [`BvClauseBatch::with_capacity`] reserves up
/// front for either buffer. Reservation is a sizing hint: a batch that outgrows
/// it grows on push exactly as an unreserved `Vec` does.
const MAX_RESERVED_ENTRIES: usize = 1 << 24;

/// Complement of a CNF literal: `neg_lit(lit) == -lit` for every literal.
///
/// CNF literals are DIMACS `±var` with `var` in `1..=i32::MAX`, a domain on
/// which negation never overflows, so `wrapping_neg` is total and identical to
/// `-lit` there (the same form as gates.rs and ay-core's `Tseitin::negate`).
/// `i32::MIN` is not a literal of any variable; it is the one value
/// `wrapping_neg` maps to itself.
#[inline]
const fn neg_lit(lit: CnfLit) -> CnfLit {
    lit.wrapping_neg()
}

/// A contiguous range of freshly allocated CNF variables.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BvFreshVarRange {
    first: CnfLit,
    count: u32,
}

impl BvFreshVarRange {
    pub(crate) fn new(first: CnfLit, count: u32) -> Self {
        Self { first, count }
    }

    /// Return the first variable in the range.
    #[must_use]
    pub fn first(&self) -> Option<CnfLit> {
        (self.count > 0).then_some(self.first)
    }

    /// Return the last variable in the range.
    #[must_use]
    pub fn last(&self) -> Option<CnfLit> {
        // `count - 1` fits a `CnfLit` and `first + (count - 1)` does not
        // overflow for every range `BvSolver::batch_fresh_vars` builds: it
        // refuses any range reaching past `i32::MAX`.
        let span = CnfLit::try_from(self.count.checked_sub(1)?).ok()?;
        self.first.checked_add(span)
    }

    /// Return the number of variables in the range.
    #[must_use]
    pub fn count(&self) -> u32 {
        self.count
    }

    /// Return true when the range contains no variables.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.count == 0
    }

    /// Iterate over the variables in ascending allocation order.
    pub fn iter(&self) -> impl Iterator<Item = CnfLit> {
        // `first..=last` is exactly `first + i` for `i` in `0..count`; an
        // empty range has no `last` and yields nothing.
        let first = self.first;
        self.last().into_iter().flat_map(move |last| first..=last)
    }

    /// Materialize the range as bit literals.
    #[must_use]
    pub fn to_vec(&self) -> Vec<CnfLit> {
        self.iter().collect()
    }
}

/// Flat, length-delimited CNF batch emitted by BV bit-blasting.
///
/// Clauses are represented by a single literal buffer plus offsets. For clause
/// `i`, literals live in `literals[offsets[i]..offsets[i + 1]]`. This layout is
/// deterministic, parser-free, and straightforward for a future ExternalCodegenIr emitter to
/// lower into stores.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BvClauseBatch {
    num_vars: u32,
    offsets: Vec<u32>,
    literals: Vec<CnfLit>,
}

impl BvClauseBatch {
    /// Create an empty batch for a formula with `num_vars` CNF variables.
    #[must_use]
    pub fn new(num_vars: u32) -> Self {
        Self {
            num_vars,
            offsets: vec![0],
            literals: Vec::new(),
        }
    }

    /// Create an empty batch with storage reserved.
    ///
    /// Each reservation is capped at an internal bound (2^24 entries); a batch
    /// that outgrows it grows on push, so the capacities stay sizing hints.
    #[must_use]
    pub fn with_capacity(num_vars: u32, clause_capacity: usize, literal_capacity: usize) -> Self {
        let offset_count = clause_capacity.saturating_add(1);
        let offset_reserve = if offset_count <= MAX_RESERVED_ENTRIES {
            offset_count
        } else {
            MAX_RESERVED_ENTRIES
        };
        let literal_reserve = if literal_capacity <= MAX_RESERVED_ENTRIES {
            literal_capacity
        } else {
            MAX_RESERVED_ENTRIES
        };
        let mut offsets = Vec::with_capacity(offset_reserve);
        offsets.push(0);
        Self {
            num_vars,
            offsets,
            literals: Vec::with_capacity(literal_reserve),
        }
    }

    /// Extract a flat batch from existing `CnfClause` emission.
    #[must_use]
    pub fn from_clauses(num_vars: u32, clauses: &[CnfClause]) -> Self {
        let literal_capacity = clauses.iter().map(|c| c.literals().len()).sum();
        let mut batch = Self::with_capacity(num_vars, clauses.len(), literal_capacity);
        for clause in clauses {
            batch.push_clause(clause.literals());
        }
        batch
    }

    /// Append one clause to the batch.
    pub fn push_clause(&mut self, literals: &[CnfLit]) {
        let next_len = self
            .literals
            .len()
            .checked_add(literals.len())
            .expect("BV clause batch literal buffer length overflow");
        let next_offset =
            u32::try_from(next_len).expect("BV clause batch exceeds u32 offset contract");
        self.literals.extend_from_slice(literals);
        self.offsets.push(next_offset);
    }

    /// Append one `CnfClause` to the batch.
    pub fn push_cnf_clause(&mut self, clause: &CnfClause) {
        self.push_clause(clause.literals());
    }

    /// Return the declared number of CNF variables.
    #[must_use]
    pub fn num_vars(&self) -> u32 {
        self.num_vars
    }

    /// Return the number of clauses in the batch.
    #[must_use]
    pub fn clause_count(&self) -> usize {
        self.offsets.len().saturating_sub(1)
    }

    /// Return the number of literals in the flat buffer.
    #[must_use]
    pub fn literal_count(&self) -> usize {
        self.literals.len()
    }

    /// Return true when the batch has no clauses.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.clause_count() == 0
    }

    /// Return the clause offsets buffer.
    #[must_use]
    pub fn offsets(&self) -> &[u32] {
        &self.offsets
    }

    /// Return the flat literal buffer.
    #[must_use]
    pub fn literals(&self) -> &[CnfLit] {
        &self.literals
    }

    /// Return the literals for one clause.
    #[must_use]
    pub fn clause_literals(&self, index: usize) -> Option<&[CnfLit]> {
        if index >= self.clause_count() {
            return None;
        }
        let start = *self.offsets.get(index)? as usize;
        let end = *self.offsets.get(index.checked_add(1)?)? as usize;
        self.literals.get(start..end)
    }

    /// Iterate over clauses in deterministic emission order.
    pub fn iter(&self) -> impl Iterator<Item = &[CnfLit]> {
        (0..self.clause_count()).map(|i| {
            self.clause_literals(i)
                .expect("clause index produced by clause_count must be valid")
        })
    }

    /// Return the maximum variable observed in the literal buffer.
    #[must_use]
    pub fn observed_max_var(&self) -> u32 {
        self.literals
            .iter()
            .map(|lit| lit.unsigned_abs())
            .max()
            .unwrap_or(0)
    }

    /// Rebuild ordinary `CnfClause` values from the flat batch.
    #[must_use]
    pub fn to_clauses(&self) -> Vec<CnfClause> {
        self.iter()
            .map(|lits| CnfClause::new(lits.to_vec()))
            .collect()
    }
}

/// Canonical BV gate template kind.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum BvGateTemplateKind {
    /// Binary AND gate: `out = a AND b`.
    And,
    /// Binary OR gate: `out = a OR b`.
    Or,
    /// Binary XOR gate: `out = a XOR b`.
    Xor,
    /// Bitwise ITE/MUX gate: `out = if selector then then_lit else else_lit`.
    Mux,
}

impl BvGateTemplateKind {
    /// Return the number of CNF clauses stamped by this gate template.
    #[must_use]
    pub fn clause_count(&self) -> u32 {
        match self {
            Self::And | Self::Or => 3,
            Self::Xor | Self::Mux => 4,
        }
    }
}

/// One concrete BV gate template instance.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BvGateTemplate {
    kind: BvGateTemplateKind,
    input_a: CnfLit,
    input_b: CnfLit,
    selector: CnfLit,
    output: CnfLit,
}

impl BvGateTemplate {
    /// Create an AND template instance.
    #[must_use]
    pub fn and(input_a: CnfLit, input_b: CnfLit, output: CnfLit) -> Self {
        Self {
            kind: BvGateTemplateKind::And,
            input_a,
            input_b,
            selector: 0,
            output,
        }
    }

    /// Create an OR template instance.
    #[must_use]
    pub fn or(input_a: CnfLit, input_b: CnfLit, output: CnfLit) -> Self {
        Self {
            kind: BvGateTemplateKind::Or,
            input_a,
            input_b,
            selector: 0,
            output,
        }
    }

    /// Create an XOR template instance.
    #[must_use]
    pub fn xor(input_a: CnfLit, input_b: CnfLit, output: CnfLit) -> Self {
        Self {
            kind: BvGateTemplateKind::Xor,
            input_a,
            input_b,
            selector: 0,
            output,
        }
    }

    /// Create a MUX template instance.
    #[must_use]
    pub fn mux(selector: CnfLit, then_lit: CnfLit, else_lit: CnfLit, output: CnfLit) -> Self {
        Self {
            kind: BvGateTemplateKind::Mux,
            input_a: then_lit,
            input_b: else_lit,
            selector,
            output,
        }
    }

    /// Return the gate kind.
    #[must_use]
    pub fn kind(&self) -> BvGateTemplateKind {
        self.kind
    }

    /// Return the first data input.
    #[must_use]
    pub fn input_a(&self) -> CnfLit {
        self.input_a
    }

    /// Return the second data input.
    #[must_use]
    pub fn input_b(&self) -> CnfLit {
        self.input_b
    }

    /// Return the MUX selector, or zero for non-MUX templates.
    #[must_use]
    pub fn selector(&self) -> CnfLit {
        self.selector
    }

    /// Return the output literal.
    #[must_use]
    pub fn output(&self) -> CnfLit {
        self.output
    }

    /// Return the number of clauses stamped by this template.
    #[must_use]
    pub fn clause_count(&self) -> u32 {
        self.kind.clause_count()
    }

    /// Stamp this gate's canonical clauses into a flat batch.
    pub fn stamp_into(&self, batch: &mut BvClauseBatch) {
        let a = self.input_a;
        let b = self.input_b;
        let out = self.output;
        match self.kind {
            BvGateTemplateKind::And => {
                batch.push_clause(&[neg_lit(out), a]);
                batch.push_clause(&[neg_lit(out), b]);
                batch.push_clause(&[neg_lit(a), neg_lit(b), out]);
            }
            BvGateTemplateKind::Or => {
                batch.push_clause(&[neg_lit(a), out]);
                batch.push_clause(&[neg_lit(b), out]);
                batch.push_clause(&[neg_lit(out), a, b]);
            }
            BvGateTemplateKind::Xor => {
                batch.push_clause(&[neg_lit(a), neg_lit(b), neg_lit(out)]);
                batch.push_clause(&[neg_lit(a), b, out]);
                batch.push_clause(&[a, neg_lit(b), out]);
                batch.push_clause(&[a, b, neg_lit(out)]);
            }
            BvGateTemplateKind::Mux => {
                let sel = self.selector;
                batch.push_clause(&[neg_lit(sel), neg_lit(a), out]);
                batch.push_clause(&[neg_lit(sel), a, neg_lit(out)]);
                batch.push_clause(&[sel, neg_lit(b), out]);
                batch.push_clause(&[sel, b, neg_lit(out)]);
            }
        }
    }

    /// Stamp this gate into ordinary `CnfClause` values.
    #[must_use]
    pub fn to_clauses(&self) -> Vec<CnfClause> {
        let mut batch = BvClauseBatch::with_capacity(
            self.output.unsigned_abs(),
            self.clause_count() as usize,
            self.clause_count() as usize * 3,
        );
        self.stamp_into(&mut batch);
        batch.to_clauses()
    }
}

/// Metadata for one gate stamped into a template batch.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BvStampedGate {
    template: BvGateTemplate,
    first_clause: u32,
    clause_count: u32,
}

impl BvStampedGate {
    /// Return the stamped template instance.
    #[must_use]
    pub fn template(&self) -> BvGateTemplate {
        self.template
    }

    /// Return the first clause index occupied by this gate.
    #[must_use]
    pub fn first_clause(&self) -> u32 {
        self.first_clause
    }

    /// Return the number of clauses occupied by this gate.
    #[must_use]
    pub fn clause_count(&self) -> u32 {
        self.clause_count
    }
}

/// Flat clause batch plus gate-template range metadata.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BvTemplateBatch {
    clauses: BvClauseBatch,
    gates: Vec<BvStampedGate>,
}

impl BvTemplateBatch {
    /// Create an empty template batch.
    #[must_use]
    pub fn new(num_vars: u32) -> Self {
        Self {
            clauses: BvClauseBatch::new(num_vars),
            gates: Vec::new(),
        }
    }

    /// Stamp a gate and record the clause range it occupied.
    pub fn push_gate(&mut self, template: BvGateTemplate) -> BvStampedGate {
        let first_clause = u32::try_from(self.clauses.clause_count())
            .expect("BV template batch exceeds u32 clause index contract");
        template.stamp_into(&mut self.clauses);
        // `stamp_into` appends exactly `template.clause_count()` clauses (3 for
        // AND/OR, 4 for XOR/MUX), so the gate occupies that many from
        // `first_clause` on.
        let clause_count = template.clause_count();
        let stamped = BvStampedGate {
            template,
            first_clause,
            clause_count,
        };
        self.gates.push(stamped);
        stamped
    }

    /// Return the flat clause batch.
    #[must_use]
    pub fn clauses(&self) -> &BvClauseBatch {
        &self.clauses
    }

    /// Return stamped gate metadata in emission order.
    #[must_use]
    pub fn gates(&self) -> &[BvStampedGate] {
        &self.gates
    }
}
