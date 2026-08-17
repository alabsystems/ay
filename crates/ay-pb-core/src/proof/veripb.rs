// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Author: Andrew Yates <andrewyates.name@gmail.com>
//! VeriPB v3 proof writer.

use std::{
    fmt,
    io::{self, Write},
};
use thiserror::Error;

use crate::cutting_planes::CpConstraint;
use crate::types::{PbInstance, PbLit, PbRel};

use super::steps::{ConstraintId, ProofStep};

/// Errors produced by VeriPB proof logging.
#[derive(Debug, Error)]
pub enum ProofError {
    /// An I/O error occurred while emitting the proof stream.
    #[error("failed to write VeriPB proof output")]
    Io(#[from] io::Error),

    /// No more 1-indexed identifiers can be allocated.
    #[error("exhausted the VeriPB constraint ID space")]
    ConstraintIdOverflow,

    /// A multiplication step used a non-positive scalar.
    #[error("VeriPB multiply step requires a strictly positive scalar, got {0}")]
    NonPositiveMultiplier(i128),

    /// A division step used a non-positive divisor.
    #[error("VeriPB divide step requires a strictly positive divisor, got {0}")]
    NonPositiveDivisor(i128),

    /// The optimization proof was concluded without concrete bounds.
    #[error("optimization bounds must be set before concluding an OPT proof")]
    MissingOptimizationBounds,

    /// The optimality proof's lower bound could not be closed by a native
    /// cutting-planes derivation (the structural cut plan was not expressible
    /// as a positive combination of input rows). Fails closed: no
    /// `conclusion BOUNDS` is committed from an unproven lower bound — the
    /// caller routes to the certified OPT-LIN fallback, which re-derives the
    /// bound from a real augmented-instance refutation. This is RECOVERABLE:
    /// unlike the transport errors below, it does not indicate proof
    /// corruption, only that the native shortcut did not apply.
    #[error("optimization lower bound not natively derivable; deferring to certified fallback")]
    UnprovableOptimizationLowerBound,

    /// The supplied optimization bounds were inconsistent.
    #[error("invalid optimization bounds: lower bound {lower} exceeds upper bound {upper}")]
    InvalidOptimizationBounds { lower: i128, upper: i128 },

    /// A solver was asked to CONTINUE an existing proof stream
    /// ([`crate::cdcl::PbCdclSolver::with_appended_proof_tap_interruptible`])
    /// whose id counter does not line up with the instance's input-row count,
    /// so every derived id would be shifted. Fails closed before any step is
    /// emitted against the misaligned stream.
    #[error("appended proof stream id mismatch: writer has allocated {actual} ids, instance expects {expected}")]
    AppendedProofIdMismatch { expected: u64, actual: u64 },

    /// The proof was already concluded and cannot be extended further.
    #[error("VeriPB proof already concluded as {0}")]
    AlreadyConcluded(ProofConclusionKind),

    /// No derivation of the claimed objective lower bound could be produced, so
    /// `conclusion BOUNDS opt opt;` must not be emitted (fail closed).
    #[error(
        "no derivation of the objective lower bound could be produced; \
         refusing to emit an unjustified OPT conclusion"
    )]
    UnjustifiedObjectiveLowerBound,

    /// Proof-tap id reconciliation failed: the solver-side allocator and the
    /// serializer-side writer disagreed on the id of an emitted line. The
    /// proof is void (fail closed) — every later id would be shifted.
    #[error("proof tap id desync: record carried id {expected}, writer allocated {actual}")]
    TapIdDesync { expected: u64, actual: u64 },

    /// Proof-tap transport failure (ring backpressure budget exhausted, dead
    /// serializer, or an unshippable record). The proof is void; the solver
    /// continues unlogged.
    #[error("proof tap transport failed: {0}")]
    TapTransport(&'static str),

    /// Proof-tap frame protocol violation (serializer-side defensive check).
    #[error("proof tap protocol violation: {0}")]
    TapProtocol(&'static str),

    /// The proof-tap serializer thread failed (I/O error detail, panic, or a
    /// missing conclusion handshake).
    #[error("proof tap serializer failed: {0}")]
    TapSerializer(String),

    /// A proof step with no tap encoding was logged while the tap was active.
    /// Fails closed: the proof is void rather than silently incomplete.
    #[error("proof step unsupported under the proof tap: {0}")]
    TapUnsupportedStep(&'static str),

    /// The proof-tap soft byte cap was exceeded. Fails closed: the proof is
    /// void (no conclusion commits) rather than truncated — a truncated proof
    /// is an invalid proof.
    #[error("proof tap soft cap exceeded: {bytes} bytes written past the {cap}-byte cap")]
    TapSoftCapExceeded { bytes: u64, cap: u64 },
}

/// Convenient result type for VeriPB proof logging.
pub type Result<T> = std::result::Result<T, ProofError>;

/// Terminal conclusion kinds supported by VeriPB.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProofConclusionKind {
    Unsat,
    Sat,
    Opt,
}

impl fmt::Display for ProofConclusionKind {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Unsat => formatter.write_str("UNSAT"),
            Self::Sat => formatter.write_str("SAT"),
            Self::Opt => formatter.write_str("OPT"),
        }
    }
}

/// A streaming VeriPB v3 proof writer.
pub struct VeriPbWriter<W> {
    pub(crate) writer: W,
    next_constraint_id: Option<u64>,
    opt_bounds: Option<(i128, i128)>,
    conclusion: Option<ProofConclusionKind>,
}

impl<W: Write> VeriPbWriter<W> {
    /// Creates a new writer and emits the VeriPB v3 header.
    pub fn new(mut writer: W, num_input_constraints: u64) -> Result<Self> {
        writeln!(writer, "pseudo-Boolean proof version 3.0")?;
        writeln!(writer, "f {num_input_constraints} ;")?;

        Ok(Self {
            writer,
            next_constraint_id: num_input_constraints.checked_add(1),
            opt_bounds: None,
            conclusion: None,
        })
    }

    /// Records the final optimization bounds used by [`Self::conclude_opt`].
    pub fn set_opt_bounds(&mut self, lower: i128, upper: i128) -> Result<()> {
        self.ensure_open()?;

        if lower > upper {
            return Err(ProofError::InvalidOptimizationBounds { lower, upper });
        }

        self.opt_bounds = Some((lower, upper));
        Ok(())
    }

    /// Emits a single proof step.
    ///
    /// Steps that derive a new constraint allocate and return the next
    /// constraint identifier. `Delete` does not allocate a new identifier and
    /// returns the deleted ID instead.
    pub fn log_step(&mut self, step: ProofStep) -> Result<ConstraintId> {
        self.ensure_open()?;

        match step {
            ProofStep::Addition(left, right) => {
                let id = self.allocate_constraint_id()?;
                writeln!(self.writer, "pol {left} {right} + ;")?;
                Ok(id)
            }
            ProofStep::Multiply(id, scalar) => {
                if scalar <= 0 {
                    return Err(ProofError::NonPositiveMultiplier(scalar));
                }

                let new_id = self.allocate_constraint_id()?;
                writeln!(self.writer, "pol {id} {scalar} * ;")?;
                Ok(new_id)
            }
            ProofStep::Divide(id, divisor) => {
                if divisor <= 0 {
                    return Err(ProofError::NonPositiveDivisor(divisor));
                }

                let new_id = self.allocate_constraint_id()?;
                writeln!(self.writer, "pol {id} {divisor} d ;")?;
                Ok(new_id)
            }
            ProofStep::Saturate(id) => {
                let new_id = self.allocate_constraint_id()?;
                writeln!(self.writer, "pol {id} s ;")?;
                Ok(new_id)
            }
            ProofStep::Polynomial(expression) => {
                let new_id = self.allocate_constraint_id()?;
                writeln!(self.writer, "pol {expression}")?;
                Ok(new_id)
            }
            ProofStep::Weaken(id, lit) => {
                let new_id = self.allocate_constraint_id()?;
                // VeriPB weakening is VARIABLE-based: the operand must be the
                // bare (unnegated) variable — 3.0.2 hard-rejects `~xN w` with
                // a parse error. The semantics (zero the coefficient, reduce
                // the degree) are polarity-independent, so the variable alone
                // is always the correct spelling.
                writeln!(self.writer, "pol {id} x{} w ;", lit.var)?;
                Ok(new_id)
            }
            ProofStep::Rup(constraint) => {
                let new_id = self.allocate_constraint_id()?;
                writeln!(self.writer, "rup {constraint}")?;
                Ok(new_id)
            }
            ProofStep::Red(constraint, witness) => {
                let new_id = self.allocate_constraint_id()?;
                writeln!(self.writer, "red {constraint}: {witness}")?;
                Ok(new_id)
            }
            ProofStep::Delete(id) => {
                writeln!(self.writer, "del id {id} ;")?;
                Ok(id)
            }
            ProofStep::SolutionImproving(assignment) => {
                let new_id = self.allocate_constraint_id()?;
                writeln!(self.writer, "soli {assignment};")?;
                Ok(new_id)
            }
        }
    }

    /// Emits the VeriPB contradiction conclusion.
    pub fn conclude_unsat(&mut self, id: ConstraintId) -> Result<()> {
        self.ensure_open()?;
        writeln!(self.writer, "output NONE;")?;
        writeln!(self.writer, "conclusion UNSAT : {id};")?;
        writeln!(self.writer, "end pseudo-Boolean proof;")?;
        self.conclusion = Some(ProofConclusionKind::Unsat);
        Ok(())
    }

    /// Emits the VeriPB SAT conclusion for a complete assignment.
    pub fn conclude_sat(&mut self, assignment: &[bool]) -> Result<()> {
        self.ensure_open()?;
        writeln!(self.writer, "output NONE;")?;
        writeln!(
            self.writer,
            "conclusion SAT : {};",
            format_assignment(assignment)
        )?;
        writeln!(self.writer, "end pseudo-Boolean proof;")?;
        self.conclusion = Some(ProofConclusionKind::Sat);
        Ok(())
    }

    /// Emits the VeriPB optimization conclusion without verification hints.
    ///
    /// Prefer [`Self::conclude_opt_hinted`]: an un-hinted `conclusion BOUNDS`
    /// is rejected by VeriPB in unchecked-deletion mode (see there).
    pub fn conclude_opt(&mut self) -> Result<()> {
        self.conclude_opt_hinted(None, None)
    }

    /// Emits the VeriPB optimization conclusion with verification hints:
    /// `conclusion BOUNDS <lower> [: <id>] <upper> [: <witness>];`.
    ///
    /// `lower_bound_hint` is the ID of a constraint that syntactically implies
    /// `obj >= lower`; a derived contradiction (`>= 1` over an empty sum)
    /// implies anything, so the final contradiction row of an augmented-
    /// instance refutation is always a valid hint. `upper_bound_witness` is a
    /// space-separated VeriPB literal list (`x1 ~x2 ...`) for a solution
    /// achieving `upper`, evaluated against the ORIGINAL problem.
    ///
    /// The hints are what make the conclusion verifiable in UNCHECKED-DELETION
    /// mode (VeriPB `-u`): there the checker discounts `soli`-logged solutions
    /// and fails an un-hinted finite upper bound with "No solution has been
    /// logged in the proof and no solution has been given in the conclusion"
    /// (VeriPB 3.0.2). Unchecked mode is entered when the competition entry
    /// declares unchecked deletions AND automatically, mid-proof, whenever a
    /// core-set deletion check fails — so every finite-bound conclusion should
    /// carry both hints to stay verifiable in every deletion mode.
    pub fn conclude_opt_hinted(
        &mut self,
        lower_bound_hint: Option<ConstraintId>,
        upper_bound_witness: Option<&str>,
    ) -> Result<()> {
        self.ensure_open()?;
        let (lower, upper) = self
            .opt_bounds
            .ok_or(ProofError::MissingOptimizationBounds)?;
        write_opt_conclusion_hinted(
            &mut self.writer,
            lower,
            lower_bound_hint,
            upper,
            upper_bound_witness,
        )?;
        self.conclusion = Some(ProofConclusionKind::Opt);
        Ok(())
    }

    /// Emits the VeriPB optimization conclusion for infeasible objectives.
    pub fn conclude_opt_infeasible(&mut self) -> Result<()> {
        self.ensure_open()?;
        writeln!(self.writer, "output NONE;")?;
        writeln!(self.writer, "conclusion BOUNDS INF INF;")?;
        writeln!(self.writer, "end pseudo-Boolean proof;")?;
        self.conclusion = Some(ProofConclusionKind::Opt);
        Ok(())
    }

    /// Flushes the wrapped writer.
    pub fn flush(&mut self) -> Result<()> {
        self.writer.flush()?;
        Ok(())
    }

    /// Consumes the writer and returns the underlying sink (e.g. a `Vec<u8>`
    /// holding the emitted proof text). Used by the certified-solve path to read
    /// back the finished proof for VeriPB validation.
    pub fn into_inner(self) -> W {
        self.writer
    }

    /// Number of constraint ids currently allocated (input rows + every
    /// id-consuming step logged so far); the next derived step receives
    /// `count + 1`. Returns `None` once the id space is exhausted. Used by
    /// [`crate::cdcl::PbCdclSolver::with_appended_proof_tap_interruptible`]
    /// to verify that a resumed proof stream's id counter lines up with the
    /// instance's input-row ids before any step is emitted against it.
    pub(crate) fn allocated_constraint_count(&self) -> Option<u64> {
        // `new()` sets `next_constraint_id = num_input_constraints + 1 >= 1`,
        // so the subtraction cannot underflow.
        self.next_constraint_id.map(|next| next - 1)
    }

    fn allocate_constraint_id(&mut self) -> Result<ConstraintId> {
        let current = self
            .next_constraint_id
            .ok_or(ProofError::ConstraintIdOverflow)?;
        self.next_constraint_id = current.checked_add(1);
        Ok(ConstraintId::from_raw(current))
    }

    fn ensure_open(&self) -> Result<()> {
        match self.conclusion {
            Some(kind) => Err(ProofError::AlreadyConcluded(kind)),
            None => Ok(()),
        }
    }
}

/// Writes the hinted `conclusion BOUNDS` block (`output NONE;` /
/// `conclusion BOUNDS <lower> [: <id>] <upper> [: <witness>];` /
/// `end pseudo-Boolean proof;`) to a raw sink. Backs
/// [`VeriPbWriter::conclude_opt_hinted`]; also used directly by the
/// OPT-LIN-CERT PB-native route, which must append the conclusion AFTER a
/// proof-tap serializer (which owns the writer and has no OPT conclusion
/// record) has drained and flushed the derivation. Keeping one formatter for
/// both paths pins the conclusion syntax in a single place.
pub(crate) fn write_opt_conclusion_hinted<W: Write>(
    writer: &mut W,
    lower: i128,
    lower_bound_hint: Option<ConstraintId>,
    upper: i128,
    upper_bound_witness: Option<&str>,
) -> Result<()> {
    writeln!(writer, "output NONE;")?;
    write!(writer, "conclusion BOUNDS {lower}")?;
    if let Some(id) = lower_bound_hint {
        write!(writer, " : {id}")?;
    }
    write!(writer, " {upper}")?;
    match upper_bound_witness {
        Some(witness) if !witness.is_empty() => {
            write!(writer, " : {witness}")?;
        }
        _ => {}
    }
    writeln!(writer, ";")?;
    writeln!(writer, "end pseudo-Boolean proof;")?;
    Ok(())
}

/// Returns the number of input constraints in VeriPB's imported formula.
///
/// VeriPB expands equality rows into two `>=` constraints, so proof headers
/// must count each equality twice.
pub fn veripb_input_constraint_count(instance: &PbInstance) -> Result<u64> {
    instance
        .constraints
        .iter()
        .try_fold(0u64, |count, constraint| {
            let contribution = if constraint.rel == PbRel::Eq { 2 } else { 1 };
            count.checked_add(contribution)
        })
        .ok_or(ProofError::ConstraintIdOverflow)
}

/// Formats a pseudo-Boolean literal in VeriPB / OPB notation.
pub fn format_lit(lit: PbLit) -> String {
    if lit.negated {
        format!("~x{}", lit.var)
    } else {
        format!("x{}", lit.var)
    }
}

fn format_assignment(assignment: &[bool]) -> String {
    assignment
        .iter()
        .enumerate()
        .map(|(index, &value)| {
            let var = index + 1;
            if value {
                format!("x{var}")
            } else {
                format!("~x{var}")
            }
        })
        .collect::<Vec<_>>()
        .join(" ")
}

/// Formats a sorted linear pseudo-Boolean constraint with a trailing semicolon.
pub fn format_constraint(terms: &[(PbLit, i128)], degree: i128) -> String {
    format!("{} ;", format_constraint_body(terms, degree))
}

/// Formats a cutting-planes constraint in VeriPB / OPB notation.
pub fn format_cp_constraint(constraint: &CpConstraint) -> String {
    let mut terms: Vec<(PbLit, i128)> = constraint
        .coefficients()
        .iter()
        .map(|(lit, coeff)| (*lit, *coeff))
        .collect();
    terms.sort_by_key(|(lit, _)| (lit.var, lit.negated));
    format_constraint_body(&terms, constraint.degree())
}

fn format_constraint_body(terms: &[(PbLit, i128)], degree: i128) -> String {
    let rendered_terms: Vec<String> = terms
        .iter()
        .filter(|(_, coeff)| *coeff != 0)
        .map(|(lit, coeff)| format!("{coeff:+} {}", format_lit(*lit)))
        .collect();

    if rendered_terms.is_empty() {
        format!(">= {degree}")
    } else {
        format!("{} >= {degree}", rendered_terms.join(" "))
    }
}

#[cfg(test)]
mod tests;
