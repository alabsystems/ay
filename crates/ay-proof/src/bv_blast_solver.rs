// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Solver-backed, zero-trust bit-blast refutation for a **non-identical** BV
//! equality obligation (the scalable "path-a" of the verified-codegen loop).
//!
//! # Difference from [`crate::bv_blast_export`]
//!
//! [`crate::bv_blast_export::export_bv_blast_proof`] proves only the
//! *identical-operand* case (`not(op(a,b) == op(a,b))`), and it **constructs**
//! the resolution chain itself: that case is a one-resolution-per-bit shortcut
//! because the two sides share output variables by construction.
//!
//! This module proves a genuinely non-identical obligation — by default
//! `not(bvadd(a,b) == bvadd(b,a))` (commutativity), whose two sides bit-blast to
//! **separate** output variables — and the resolution chain is **derived by the
//! `ay-sat` CDCL engine**, not constructed here. Concretely:
//!
//! 1. Bit-blast both sides into CNF (each side with its own gate cache, so the
//!    operand-swapped sides do *not* fuse), add per-bit `XnorEq` equality vars
//!    and the single disequality clause from `not(lhs == rhs)`.
//! 2. Hand that CNF to [`ay_sat::prove_unsat_resolution_dag`], which solves it
//!    and surfaces the solver's **actual** refutation as an in-memory
//!    [`ay_sat::ResolutionDag`] of RUP steps with positive antecedent ids.
//! 3. Expand each RUP step into a chain of binary [`ResolutionStep`]s (one real,
//!    locally-checkable resolution each), producing a [`Refutation`] whose final
//!    clause is empty.
//! 4. Assemble a [`BvBlastProof`] carrying the bit-blast CNF (with checked gate
//!    provenance) plus that solver-derived refutation. [`BvBlastProof::validate`]
//!    then recomputes every resolution and confirms the empty clause — exactly
//!    the same zero-trust replay the separate proof consumer performs, unchanged.
//!
//! ## Honesty: what is solver-derived vs constructed
//!
//! * **Solver-derived:** the *set of derived clauses* and their *RUP antecedent
//!   chains* (`ay-sat` CDCL → LRAT → [`ay_sat::ResolutionDag`]). The producer
//!   does not choose which clauses to learn or in what order.
//! * **Mechanically expanded (not trusted):** the conversion of each RUP chain
//!   into pairwise resolutions. This is a deterministic, locally-checkable
//!   transformation; every emitted step is re-verified by
//!   [`BvBlastProof::validate`] (and, in tests, independently by `ay-lrat-check`
//!   on the raw LRAT and by replaying the pairwise chain). Nothing is asserted.
//! * **Still gated in `ay-sat` (out of scope):** RAT steps (signed hints) are
//!   refused up front; clause-deletion and theory-lemma materializer provenance
//!   remain behind the authority handshake in `proof_manager.rs`. The BV
//!   bit-blast fragment refutes by pure RUP, so none of those are needed here.

use crate::bv_blast_export::{
    blast_shift_with_cancellation, build_gate, push_gate_cnf, BitLemma, BitLemmaKind, BvBlastProof,
    BvOp, Clause, ClauseProvenance, GateCache, Lit, OperandRef, Refutation, ResRule,
    ResolutionStep, SliceObligation, VarRole, VarTable, FORMAT_VERSION,
};
use ay_core::time::Instant;
use ay_sat::{
    Literal, ResolutionDag, ResolutionDagError, ResolutionProofError, ResolutionProofLimits,
    ResolutionProofResource, ResolutionValidationError, ResolutionValidationResource, RupStep,
    SatUnknownReason, Variable,
};
use std::{mem::size_of, time::Duration};

mod cancellation;
pub(crate) mod cnf;
mod compact;
mod divide;
mod expr_api;
mod node_memo;
mod preflight_sharing;
pub(crate) mod retained;
mod sweep;
mod unsigned_compare;
pub(crate) use compact::{note_uncounted_failure, validate_bv_expr_compact};

#[cfg(test)]
mod cancellation_tests;

mod constant_bitwise;
#[cfg(test)]
mod constant_shift_tests;
#[cfg(test)]
mod product_prefix_tests;
mod topology_bound;

fn poll_export(keep_going: &mut dyn FnMut() -> bool) -> Result<(), BvExprExportError> {
    if keep_going() {
        Ok(())
    } else {
        Err(BvExprExportError::Cancelled)
    }
}

/// Errors from [`export_bv_blast_proof_solved`].
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum BvSolvedExportError {
    /// The caller refused further work; no partial refutation is returned.
    #[error("proof production cancelled")]
    Cancelled,
    /// The width is zero or exceeds the supported solver-backed range.
    #[error("unsupported width {got} (supported: 1..={max})")]
    UnsupportedWidth {
        /// Width seen.
        got: u32,
        /// Maximum supported width.
        max: u32,
    },
    /// The obligation is SAT (a false identity): no refutation is produced.
    #[error("no refutation: obligation is satisfiable")]
    NoRefutation,
    /// The solver returned Unknown.
    #[error("solver returned unknown")]
    SolverUnknown,
    /// The surfaced refutation used a construct this path does not lift (e.g. a
    /// RAT step), or it could not be read back as a resolution DAG.
    #[error("refutation not surfaceable as pure-RUP resolution: {0}")]
    RefutationNotSurfaceable(String),
    /// Internal: the RUP→resolution expansion could not reproduce a derived
    /// clause from its antecedents (should not happen for a valid LRAT proof).
    #[error("RUP expansion failed for derived clause id {id}")]
    RupExpansionFailed {
        /// The LRAT id of the derived clause that failed to expand.
        id: u64,
    },
    /// Bounded RUP expansion exhausted an explicit resource envelope.
    #[error("proof resource `{resource}` exceeds limit {limit} (actual {actual})")]
    ResourceLimit {
        /// Stable resource name.
        resource: &'static str,
        /// Configured maximum.
        limit: usize,
        /// Observed amount.
        actual: usize,
    },
}

#[derive(Clone, Copy)]
struct RupExpansionLimits {
    max_steps: usize,
    max_literals: usize,
    max_work: usize,
    max_bytes: usize,
    deadline: Instant,
}

/// Largest width the solver-backed path accepts. Bounded so the var-id space
/// stays within the `u32` ids the [`BvBlastProof`] format uses with room to
/// spare; in practice tests run at 8..=32. Kept equal to the constructive
/// path's [`crate::bv_blast_export::MAX_WIDTH`] so the two producers accept
/// the same width range.
pub const SOLVED_MAX_WIDTH: u32 = crate::bv_blast_export::MAX_WIDTH;

/// A non-identical BV equality obligation provable by the solver-backed path.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SolvedObligation {
    /// `not(bvadd(a,b) == bvadd(b,a))` at the given width — commutativity of
    /// addition. UNSAT (the two operand-swapped sides are bit-for-bit equal).
    AddCommutes {
        /// Bit width (>= 1, <= [`SOLVED_MAX_WIDTH`]).
        width: u32,
    },
    /// `not(bvsub(a,b) == bvadd(a, bvneg(b)))`-style is out of scope; instead this
    /// variant is the deliberately-SAT control `not(bvsub(a,b) == bvsub(b,a))`,
    /// used to confirm the path returns [`BvSolvedExportError::NoRefutation`].
    SubAntiCommutesFalse {
        /// Bit width.
        width: u32,
    },
    /// `not(bvxor(a,b) == bvxor(b,a))` at the given width — commutativity of the
    /// bitwise XOR the real GVN canonicalizer also applies (`is_commutative` is
    /// true for XOR). UNSAT, and it exercises a DIFFERENT kernel gate-fidelity
    /// (per-bit `Bool.xor`, no carry chain) than the ripple-carry adder.
    XorCommutes {
        /// Bit width (>= 1, <= [`SOLVED_MAX_WIDTH`]).
        width: u32,
    },
    /// `not(bvand(a,b) == bvand(b,a))` at the given width — commutativity of the
    /// bitwise AND the real GVN canonicalizer also applies (`is_commutative` is
    /// true for AND). UNSAT, and it exercises a DIFFERENT kernel gate-fidelity
    /// (per-bit `Bool.and`, no carry chain) than the ripple-carry adder.
    AndCommutes {
        /// Bit width (>= 1, <= [`SOLVED_MAX_WIDTH`]).
        width: u32,
    },
    /// `not(bvor(a,b) == bvor(b,a))` at the given width — commutativity of the
    /// bitwise OR the real GVN canonicalizer also applies (`is_commutative` is
    /// true for OR). UNSAT, and it exercises a DIFFERENT kernel gate-fidelity
    /// (per-bit `Bool.or`, no carry chain) than the ripple-carry adder.
    OrCommutes {
        /// Bit width (>= 1, <= [`SOLVED_MAX_WIDTH`]).
        width: u32,
    },
}

impl SolvedObligation {
    fn width(self) -> u32 {
        match self {
            Self::AddCommutes { width }
            | Self::SubAntiCommutesFalse { width }
            | Self::XorCommutes { width }
            | Self::AndCommutes { width }
            | Self::OrCommutes { width } => width,
        }
    }
}

/// Build a [`BvBlastProof`] for a non-identical obligation whose refutation is
/// produced by the `ay-sat` CDCL solver (not constructed here).
///
/// # Errors
/// See [`BvSolvedExportError`]; in particular a SAT obligation yields
/// [`BvSolvedExportError::NoRefutation`] (no bogus proof is fabricated).
pub fn export_bv_blast_proof_solved(
    obligation: SolvedObligation,
) -> Result<BvBlastProof, BvSolvedExportError> {
    let width = obligation.width();
    if width == 0 || width > SOLVED_MAX_WIDTH {
        return Err(BvSolvedExportError::UnsupportedWidth {
            got: width,
            max: SOLVED_MAX_WIDTH,
        });
    }

    // Both obligations swap operands on the rhs (op(a,b) vs op(b,a)); the
    // distinction is only which op (Add → UNSAT/commutes, Sub → SAT control).
    let op = match obligation {
        SolvedObligation::AddCommutes { .. } => BvOp::Add,
        SolvedObligation::SubAntiCommutesFalse { .. } => BvOp::Sub,
        SolvedObligation::XorCommutes { .. } => BvOp::Xor,
        SolvedObligation::AndCommutes { .. } => BvOp::And,
        SolvedObligation::OrCommutes { .. } => BvOp::Or,
    };

    // ---- Bit-blast both sides into CNF (each side its own gate cache). --------
    let mut vars = VarTable::default();
    let mut bit_lemmas: Vec<BitLemma> = Vec::new();
    let mut clauses: Vec<Clause> = Vec::new();

    let a_bits: Vec<u32> = (0..width)
        .map(|bit| vars.alloc(VarRole::InputA { bit }))
        .collect();
    let b_bits: Vec<u32> = (0..width)
        .map(|bit| vars.alloc(VarRole::InputB { bit }))
        .collect();

    // lhs = op(a, b)
    let mut lhs_cache = GateScratch::default();
    let lhs = blast_side_roles(
        op,
        &a_bits,
        &b_bits,
        Side::Lhs,
        &mut vars,
        &mut bit_lemmas,
        &mut clauses,
        &mut lhs_cache,
    );
    // rhs = op(b, a) — operands swapped, separate cache → separate output vars.
    let mut rhs_cache = GateScratch::default();
    let rhs = blast_side_roles(
        op,
        &b_bits,
        &a_bits,
        Side::Rhs,
        &mut vars,
        &mut bit_lemmas,
        &mut clauses,
        &mut rhs_cache,
    );

    // ---- Per-bit equality vars e_i = XnorEq(lhs_i, rhs_i) + Tseitin CNF. ------
    let mut eq_vars: Vec<u32> = Vec::with_capacity(width as usize);
    for (bit, (&l, &r)) in lhs.iter().zip(rhs.iter()).enumerate() {
        let e = vars.alloc(VarRole::BitEq { bit: bit as u32 });
        eq_vars.push(e);
        let lemma_id = bit_lemmas.len() as u32;
        let ins = vec![l, r];
        bit_lemmas.push(BitLemma {
            id: lemma_id,
            kind: BitLemmaKind::XnorEq,
            out: e,
            ins: ins.clone(),
        });
        push_gate_cnf(&mut clauses, BitLemmaKind::XnorEq, e, &ins, lemma_id);
    }

    // ---- Disequality clause from not(lhs == rhs). ----------------------------
    let diseq_id = clauses.len() as u32;
    clauses.push(Clause {
        id: diseq_id,
        lits: eq_vars.iter().map(|&e| Lit::neg(e)).collect(),
        provenance: ClauseProvenance::Disequality,
    });

    // ---- Hand the CNF to ay-sat and surface the actual refutation. -----------
    let num_vars = vars.len();
    let sat_clauses: Vec<Vec<Literal>> = clauses
        .iter()
        .map(|c| c.lits.iter().map(lit_to_sat).collect())
        .collect();

    let dag = match ay_sat::prove_unsat_resolution_dag(num_vars, &sat_clauses) {
        Ok(dag) => dag,
        Err(ResolutionDagError::Satisfiable) => return Err(BvSolvedExportError::NoRefutation),
        Err(ResolutionDagError::Unknown) => return Err(BvSolvedExportError::SolverUnknown),
        Err(other) => {
            return Err(BvSolvedExportError::RefutationNotSurfaceable(
                other.to_string(),
            ))
        }
    };

    // The LRAT original-clause ids are 1..=clauses.len() in input order, which is
    // exactly our `clauses` Vec index + 1. Map an LRAT id → BvBlast premise id.
    let refutation = expand_dag_to_resolution(&dag, &clauses, None)?;

    let obligation_record = match op {
        // All are operand-swapped `op(a,b)` vs `op(b,a)`; Add/Xor/And/Or are
        // commutative (UNSAT), Sub is the deliberately-SAT control.
        BvOp::Add | BvOp::Sub | BvOp::Xor | BvOp::And | BvOp::Or => SliceObligation {
            width,
            op,
            lhs_args: [OperandRef::A, OperandRef::B],
            rhs_args: [OperandRef::B, OperandRef::A],
        },
        // `op` is derived from `SolvedObligation` above, which has no shift
        // variant — the commutativity demo does not apply to non-commutative
        // shifts, so they cannot reach this path.
        BvOp::Shl | BvOp::Lshr | BvOp::Ashr => {
            unreachable!("solver-backed path is commutativity-only; shifts are unreachable")
        }
    };

    let proof = BvBlastProof {
        format_version: FORMAT_VERSION,
        obligation: obligation_record,
        asserted_smt: obligation_record.render_smt(),
        vars,
        bit_lemmas,
        clauses,
        refutation,
    };
    Ok(proof)
}

// ───────────────────────── RUP → pairwise resolution ─────────────────────────

use rup_expansion::{expand_dag_to_resolution, expand_dag_to_resolution_with_cancellation};
mod rup_expansion;

// ───────────────────────── bit-blast helpers (per-side) ──────────────────────

#[derive(Default)]
struct GateScratch {
    cache: GateCache,
}

#[derive(Clone, Copy)]
enum Side {
    Lhs,
    Rhs,
}

impl Side {
    fn out_role(self, bit: u32) -> VarRole {
        match self {
            Self::Lhs => VarRole::LhsOut { bit },
            Self::Rhs => VarRole::RhsOut { bit },
        }
    }
    fn aux_role(self, bit: u32) -> VarRole {
        match self {
            Self::Lhs => VarRole::LhsAux { bit },
            Self::Rhs => VarRole::RhsAux { bit },
        }
    }
    fn carry_in_role(self) -> VarRole {
        match self {
            Self::Lhs => VarRole::CarryIn,
            Self::Rhs => VarRole::RhsCarryIn,
        }
    }
    fn not_b_role(self, bit: u32) -> VarRole {
        match self {
            Self::Lhs => VarRole::NotB { bit },
            Self::Rhs => VarRole::RhsNotB { bit },
        }
    }
}

/// Bit-blast `op(x, y)` over the given input bit vars with side-specific roles
/// and a dedicated gate cache (so the two sides never fuse). Mirrors
/// `bv_blast_export::blast_side` but with distinct roles per side.
#[allow(clippy::too_many_arguments)]
fn blast_side_roles(
    op: BvOp,
    x_bits: &[u32],
    y_bits: &[u32],
    side: Side,
    vars: &mut VarTable,
    bit_lemmas: &mut Vec<BitLemma>,
    clauses: &mut Vec<Clause>,
    scratch: &mut GateScratch,
) -> Vec<u32> {
    match blast_side_roles_with_cancellation(
        op,
        x_bits,
        y_bits,
        side,
        vars,
        bit_lemmas,
        clauses,
        scratch,
        &mut || true,
    ) {
        Ok(bits) => bits,
        Err(_) => unreachable!("always-accepting gate construction cannot be cancelled"),
    }
}

#[allow(clippy::too_many_arguments)]
fn blast_side_roles_with_cancellation(
    op: BvOp,
    x_bits: &[u32],
    y_bits: &[u32],
    side: Side,
    vars: &mut VarTable,
    bit_lemmas: &mut Vec<BitLemma>,
    clauses: &mut Vec<Clause>,
    scratch: &mut GateScratch,
    keep_going: &mut dyn FnMut() -> bool,
) -> Result<Vec<u32>, BvExprExportError> {
    poll_export(keep_going)?;
    let n = x_bits.len();
    let cache = &mut scratch.cache;

    // Bitwise XOR / AND / OR: per-bit single 2-input gate, NO carry chain — a
    // genuinely different gate-fidelity than the ripple-carry adder. The real GVN
    // canonicalizer applies to commutative XOR/AND/OR too, so `op(a,b) == op(b,a)`
    // is a real lowering identity (UNSAT).
    let bitwise_gate = match op {
        BvOp::Xor => Some(BitLemmaKind::Xor2),
        BvOp::And => Some(BitLemmaKind::And2),
        BvOp::Or => Some(BitLemmaKind::Or2),
        BvOp::Add | BvOp::Sub => None,
        // Unreachable: this path only bit-blasts the commutative ops above plus
        // Add/Sub; `op` comes from a shift-free `SolvedObligation`.
        BvOp::Shl | BvOp::Lshr | BvOp::Ashr => {
            unreachable!("solver-backed path does not bit-blast shifts")
        }
    };
    if let Some(gate) = bitwise_gate {
        return (0..n)
            .map(|bit| {
                poll_export(keep_going)?;
                Ok({
                    build_gate(
                        gate,
                        vec![x_bits[bit], y_bits[bit]],
                        side.out_role(bit as u32),
                        vars,
                        bit_lemmas,
                        clauses,
                        cache,
                    )
                })
            })
            .collect::<Result<Vec<_>, BvExprExportError>>();
    }

    // Arithmetic ripple-carry (Add / Sub): Sub complements `y` and carries in 1.
    let (op2_bits, cin): (Vec<u32>, u32) = if matches!(op, BvOp::Sub) {
        let noty: Vec<u32> = y_bits
            .iter()
            .enumerate()
            .map(|(bit, &y)| {
                poll_export(keep_going)?;
                Ok({
                    build_gate(
                        BitLemmaKind::Not,
                        vec![y],
                        side.not_b_role(bit as u32),
                        vars,
                        bit_lemmas,
                        clauses,
                        cache,
                    )
                })
            })
            .collect::<Result<Vec<_>, BvExprExportError>>()?;
        let t = build_gate(
            BitLemmaKind::ConstTrue,
            vec![],
            side.carry_in_role(),
            vars,
            bit_lemmas,
            clauses,
            cache,
        );
        (noty, t)
    } else {
        let f = build_gate(
            BitLemmaKind::ConstFalse,
            vec![],
            side.carry_in_role(),
            vars,
            bit_lemmas,
            clauses,
            cache,
        );
        let mut copied = Vec::with_capacity(y_bits.len());
        for &bit in y_bits {
            poll_export(keep_going)?;
            copied.push(bit);
        }
        (copied, f)
    };

    let mut out = Vec::with_capacity(n);
    let mut carry = cin;
    for bit in 0..n {
        poll_export(keep_going)?;
        let a = x_bits[bit];
        let b2 = op2_bits[bit];
        let o = build_gate(
            BitLemmaKind::Xor3,
            vec![a, b2, carry],
            side.out_role(bit as u32),
            vars,
            bit_lemmas,
            clauses,
            cache,
        );
        if bit != n - 1 {
            carry = build_gate(
                BitLemmaKind::FullAdderCarry,
                vec![a, b2, carry],
                side.aux_role(bit as u32),
                vars,
                bit_lemmas,
                clauses,
                cache,
            );
        }
        out.push(o);
    }
    poll_export(keep_going)?;
    Ok(out)
}

// ───────────────────────── lit conversions ──────────────────────

fn lit_to_sat(l: &Lit) -> Literal {
    let v = Variable::new(l.var);
    if l.neg {
        Literal::negative(v)
    } else {
        Literal::positive(v)
    }
}

fn lit_from_sat(l: &Literal) -> Lit {
    let var = l.variable().index() as u32;
    if l.is_positive() {
        Lit::pos(var)
    } else {
        Lit::neg(var)
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// Expression-tree path: arbitrary QF_BV equality over a small structural fragment
// ═══════════════════════════════════════════════════════════════════════════
//
// The two paths above accept only *structured* obligations (`SliceObligation` /
// `SolvedObligation`): a single top-level `op` applied to a notional operand pair
// `(a, b)`, optionally operand-swapped. The live external-codegen M-POS gate does not
// discharge that shape. It discharges
//
//     NOT( machine_out == auto_spec )
//
// where (add-leaf)
//     machine_out = BvExtract(BvZeroExt(BvAdd(W0, W1, 32), 32), 31, 0)
//     auto_spec   = BvAdd(W0, W1, 32)
//     W_n         = BvExtract(Var("Xn", BitVec(64)), 31, 0)
//
// i.e. an *arbitrary* BitVec equality between two expression trees that share
// named leaves, with extract/zero-extend wrappers — not a `(op, a, b)` triple.
//
// [`export_bv_blast_proof_expr`] accepts that shape directly. It bit-blasts both
// sides of the equality through ONE shared gate cache (so a sub-term appearing on
// both sides — e.g. the inner `BvAdd(W0,W1,32)` — fuses to the same output vars),
// adds the per-bit `XnorEq` equality vars and the disequality clause, and hands
// the CNF to the SAME `ay-sat` solver the operand-swap path uses. The solver
// returns the actual refutation (UNSAT) or `Satisfiable` (a false identity →
// `NoRefutation`). No proof is ever fabricated: anti-vacuity is enforced by the
// solver, not by a structural shortcut.
//
// `BvExpr` is a small *self-contained* term type covering exactly the gate's
// add-leaf fragment (named leaf vars, BvAdd/BvSub, BvZeroExt, BvExtract). It is
// deliberately NOT trust-types' `Formula`: importing the full verification-contract
// Formula into the solver crate is a heavy cross-crate dependency (see residual
// notes in the rung report). The fragment here is enough to feed the gate's real
// add-leaf disequality to the zero-trust producer, which is this rung's deliverable.

/// A bit-vector expression over the small structural fragment the external-codegen M-POS
/// add-leaf gate emits. Self-contained (no trust-types dependency); the caller
/// lowers its `Formula` into this shape.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BvExpr {
    /// A named free leaf of the given bit width. The SAME `name` on either side of
    /// the equality denotes the SAME free variable (shared input bits).
    Leaf {
        /// Stable leaf name (e.g. `"W0"`).
        name: String,
        /// Bit width of the leaf.
        width: u32,
    },
    /// `bvadd(lhs, rhs)` — both operands and the result share one width.
    Add(Box<BvExpr>, Box<BvExpr>),
    /// `bvsub(lhs, rhs)` — both operands and the result share one width.
    Sub(Box<BvExpr>, Box<BvExpr>),
    /// `(_ zero_extend added) inner` — append `added` zero bits above `inner`.
    ZeroExt(Box<BvExpr>, u32),
    /// `(_ extract high low) inner` — bits `low..=high` of `inner` (LSB = 0).
    Extract {
        /// The expression to slice.
        inner: Box<BvExpr>,
        /// High bit (inclusive).
        high: u32,
        /// Low bit (inclusive).
        low: u32,
    },
    /// `bvor(lhs, rhs)` — bitwise OR; both operands and the result share one width.
    ///
    /// The live M-POS gate's RAW `symbolic_machine_output` emits identity wrappers
    /// such as `BvOr(BitVec{0}, x)` (a no-op OR with a zero constant). Representing
    /// `Or` directly lets the lowering ingest that RAW shape WITHOUT a trusted
    /// normalization step, keeping ay out of the re-check TCB.
    Or(Box<BvExpr>, Box<BvExpr>),
    /// `bvand(lhs, rhs)` — bitwise AND; both operands and the result share one
    /// width. Per-bit `And2` gate, no carry chain — the same gate-fidelity the
    /// operand-swap path's `BvOp::And` uses. Lets the lowering ingest the RAW
    /// `BvAnd` machine-output shape without a trusted normalization step.
    And(Box<BvExpr>, Box<BvExpr>),
    /// `bvxor(lhs, rhs)` — bitwise XOR; both operands and the result share one
    /// width. Per-bit `Xor2` gate, no carry chain — the same gate-fidelity the
    /// operand-swap path's `BvOp::Xor` uses.
    Xor(Box<BvExpr>, Box<BvExpr>),
    /// A fixed bit-vector constant: `value` is the unsigned little-endian bit pattern
    /// (bit `i` = `(value >> i) & 1`), `width` is the bit width. Bits at or above
    /// `width` of `value` must be zero (else the expression is malformed).
    Const {
        /// Unsigned constant value (bit `i` is `(value >> i) & 1`).
        value: u128,
        /// Bit width of the constant.
        width: u32,
    },
    /// `(_ sign_extend added) inner` — append `added` COPIES OF THE SIGN BIT (the
    /// MSB of `inner`) above `inner`. Unlike `ZeroExt` (which pads with a fixed
    /// zero bit), this replicates `inner`'s top bit, so a negative value stays
    /// negative at the wider width. The blast introduces NO new gate kind: it
    /// simply reuses the MSB output var `added` times, so the downstream proof consumer
    /// re-checks it with the SAME gate vocabulary as the rest of the fragment.
    SignExt(Box<BvExpr>, u32),
    /// `bvshl(value, amount)` — logical shift left of `value` by a VARIABLE
    /// `amount` (both operands and the result share one width). Bit-blasted as a
    /// barrel shifter (`ceil(log2(n))` conditional constant-shift layers + an
    /// over-shift saturation mux), reusing the exact `blast_shift` topology the
    /// operand-swap path uses. Every gate is an existing `BitLemmaKind`
    /// (And2/Or2/Not/ConstFalse), so the proof is downstream proof consumer-re-checkable.
    Shl(Box<BvExpr>, Box<BvExpr>),
    /// `bvlshr(value, amount)` — logical (zero-filling) shift right by a variable
    /// `amount`. Barrel shifter; over-shift saturates to zero.
    Lshr(Box<BvExpr>, Box<BvExpr>),
    /// `bvashr(value, amount)` — arithmetic (sign-filling) shift right by a
    /// variable `amount`. Barrel shifter; over-shift saturates to the sign bit.
    /// Distinct gate topology from `Lshr` (the fill is the sign bit, not zero) —
    /// this is the EXACT signed/unsigned distinction the campaign's bug class
    /// turned on, so a `Lshr`-for-`Ashr` substitution is a genuine disequality the
    /// solver refutes (anti-vacuity), never a structural coincidence.
    Ashr(Box<BvExpr>, Box<BvExpr>),
    /// `bvnot(inner)` — bitwise (per-bit) NOT. Result width equals `inner`'s.
    ///
    /// Bit-blasts to one existing `Not` gate per bit — NO new kernel gate KIND, so
    /// the downstream proof consumer's `certify_unsat_by_reflection` re-checks it via the same `Not`
    /// Tseitin reflection the subtraction's one's-complement already uses. This is
    /// the 1-bit `Not` the compare flag-decomposition's predicate combinators need
    /// (e.g. `signed_lt = N != V`, `unsigned_lt = NOT carryOut`).
    Not(Box<BvExpr>),
    /// `(= lhs rhs)` — bit-vector EQUALITY reduced to a 1-bit predicate. Both
    /// operands must bit-blast to the same width; the result is exactly 1 bit
    /// (`true` iff every bit agrees).
    ///
    /// Bit-blasts to one existing `XnorEq` gate per bit (each `out_i <=> lhs_i ==
    /// rhs_i`) AND-reduced to a single bit by a chain of existing `And2` gates —
    /// NO new kernel gate KIND. a downstream proof consumer re-checks both via the existing `XnorEq`/
    /// `And2` reflections. This is the `eq(a,b) = (Sub(a,b) == 0)` predicate the
    /// compare decomposition needs, and the `N == V` flag-equality inside the
    /// signed-lt overflow term.
    Eq(Box<BvExpr>, Box<BvExpr>),
    /// Unsigned less-than, lowered to a shared prefix of existing Boolean gates.
    Ult(Box<BvExpr>, Box<BvExpr>),
    /// The final CARRY-OUT bit of a ripple-carry add/sub of `lhs` and `rhs`.
    /// `is_sub == false`: carry-out of `lhs + rhs` (carry-in 0).
    /// `is_sub == true`: carry-out of `lhs - rhs = lhs + ~rhs + 1` (carry-in 1).
    /// Both operands must bit-blast to the same width; the result is exactly 1 bit.
    ///
    /// This exposes the top carry of the EXISTING ripple-carry chain as a
    /// first-class node: the blast threads the SAME `FullAdderCarry` (MAJ) gates
    /// the `Add`/`Sub` sum already uses, but runs the chain to the MSB and returns
    /// the final carry (which the sum path discards). NO new kernel gate KIND.
    ///
    /// This is the borrow flag the UNSIGNED compares decompose to (g16
    /// `unsigned_lt_equiv`): `unsigned_lt(a, b) = NOT(CarryOut(a, b, is_sub=true))`
    /// — i.e. `a - b` produces a borrow (carry-out 0) exactly when `a <u b`.
    CarryOut {
        /// The left operand (`a` of `a - b` or `a + b`).
        lhs: Box<BvExpr>,
        /// The right operand (`b`).
        rhs: Box<BvExpr>,
        /// Whether this is the carry-out of a subtraction (`a + ~b + 1`).
        is_sub: bool,
    },
    /// `bvmul(lhs, rhs)` — bit-vector multiply; both operands and the result
    /// share one width `n` (the low `n` bits of the `2n`-wide product, matching
    /// SMT-LIB / two's-complement wrapping multiply).
    ///
    /// Bit-blasts to a classic shift-and-add array multiplier built ENTIRELY
    /// from existing gate kinds — NO new kernel gate KIND:
    /// * partial products `pp[i][j] = a[i] ∧ b[j]` via existing `And2` gates;
    /// * the shifted partial-product rows summed by ripple-carry adders reusing
    ///   the SAME `Xor3` (sum) + `FullAdderCarry` (carry) gates the `Add` path
    ///   uses, plus `ConstFalse` zero-pad bits.
    ///
    /// Because only the low `n` result bits are retained, partial-product bits
    /// at position `>= n` are never built (the array is truncated), bounding the
    /// blast. a downstream proof consumer re-checks the whole multiplier through the existing
    /// `And2`/`Xor3`/`FullAdderCarry`/`ConstFalse` reflections. Anti-vacuity is
    /// real: `Mul` is genuinely distinct from `Add` (e.g. `a*b != a+b`), so a
    /// multiply lowered/emitted as an add is refuted, never silently proved.
    Mul(Box<BvExpr>, Box<BvExpr>),
    /// `bvudiv(lhs, rhs)` with SMT-LIB's zero divisor (all ones): the quotient
    /// of a restoring divider over existing gates (`divide.rs`).
    UDiv(Box<BvExpr>, Box<BvExpr>),
    /// `bvurem(lhs, rhs)` with SMT-LIB's zero divisor (`lhs`): the remainder
    /// of the same divider.
    URem(Box<BvExpr>, Box<BvExpr>),
}

// The `add`/`sub`/`mul`/`shl`/`not` constructors are named after the SMT-LIB
// bitvector operators they build (bvadd, bvsub, ...); they take two operands
// and return a `BvExpr` node, so they cannot and should not implement the
// same-named `std::ops` traits.
#[allow(clippy::should_implement_trait)]
/// Errors from [`export_bv_blast_proof_expr`].
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum BvExprExportError {
    /// The caller refused further work; this is not a satisfiability verdict.
    #[error("proof production cancelled")]
    Cancelled,
    /// The two sides of the equality bit-blast to different widths, so a per-bit
    /// equality is not well-formed.
    #[error("width mismatch: lhs is {lhs} bits, rhs is {rhs} bits")]
    WidthMismatch {
        /// Width of the bit-blasted lhs.
        lhs: u32,
        /// Width of the bit-blasted rhs.
        rhs: u32,
    },
    /// An expression is malformed (e.g. an extract range out of bounds, or a
    /// width-0 leaf), so it cannot be bit-blasted.
    #[error("malformed expression: {0}")]
    Malformed(String),
    /// The resulting bit width is zero or exceeds the supported solver range.
    #[error("unsupported width {got} (supported: 1..={max})")]
    UnsupportedWidth {
        /// Width seen.
        got: u32,
        /// Maximum supported width.
        max: u32,
    },
    /// The obligation is SAT (a false identity): `not(lhs == rhs)` has a model, so
    /// no refutation is produced. (Anti-vacuity: never fabricate a proof.)
    #[error("no refutation: obligation is satisfiable (the equality is not valid)")]
    NoRefutation,
    /// The solver returned Unknown.
    #[error("solver returned unknown")]
    SolverUnknown,
    /// The surfaced refutation could not be lifted to pure-RUP resolution.
    #[error("refutation not surfaceable as pure-RUP resolution: {0}")]
    RefutationNotSurfaceable(String),
    /// A bounded proof-producing call exceeded an explicit preflight or
    /// surfaced-proof resource limit.
    #[error("proof resource `{resource}` exceeds limit {limit} (actual {actual})")]
    ResourceLimit {
        /// Stable resource name.
        resource: &'static str,
        /// Configured maximum.
        limit: usize,
        /// Observed or conservatively estimated amount.
        actual: usize,
    },
}

/// Configuration errors from [`BvExprProofBudget::conservative`].
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum BvExprProofBudgetError {
    /// A zero timeout could never admit useful proof work.
    #[error("BV expression proof timeout must be greater than zero")]
    ZeroTimeout,
    /// The requested timeout exceeds the public conservative ceiling.
    #[error("BV expression proof timeout {requested:?} exceeds maximum {maximum:?}")]
    TimeoutTooLong {
        /// Requested relative timeout.
        requested: Duration,
        /// Largest accepted relative timeout.
        maximum: Duration,
    },
    /// A zero step budget could never produce a resolution refutation.
    #[error("BV expression proof resolution-step budget must be greater than zero")]
    ZeroResolutionSteps,
    /// The requested step budget exceeds the public conservative ceiling.
    #[error("BV expression proof resolution-step budget {requested} exceeds maximum {maximum}")]
    TooManyResolutionSteps {
        /// Requested maximum resolution steps.
        requested: usize,
        /// Largest accepted maximum resolution steps.
        maximum: usize,
    },
}

/// Consumer-neutral budget for bounded [`BvExpr`] proof export.
///
/// This type intentionally exposes only a relative timeout and a resolution
/// step ceiling. [`BvExprProofBudget::conservative`] validates those two
/// choices, while AY privately supplies conservative finite bounds for
/// expression preflight, CNF construction/materialization, SAT search, LRAT
/// parsing, and independent replay. There is no `Default` or unlimited mode.
/// These logical and retained-allocation caps are not a hard process-wide
/// peak-RSS guarantee; callers that require one must enforce a process envelope.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub struct BvExprProofBudget {
    timeout: Duration,
    max_resolution_steps: usize,
}

impl BvExprProofBudget {
    /// Largest relative timeout accepted by the public bounded exporter.
    pub const MAX_TIMEOUT: Duration = Duration::from_secs(30);
    /// Largest resolution-step ceiling accepted by the public bounded exporter.
    pub const MAX_RESOLUTION_STEPS: usize = 250_000;

    /// Construct a conservative bounded-export budget.
    ///
    /// A fresh absolute monotonic deadline is derived from `timeout` at each
    /// export call, so retaining or reusing a budget cannot retain a stale
    /// deadline. Zero values and requests above AY's conservative public ceilings
    /// are rejected rather than silently changed.
    ///
    /// # Errors
    /// Returns [`BvExprProofBudgetError`] when either bound is zero or exceeds
    /// its documented ceiling.
    pub fn conservative(
        timeout: Duration,
        max_resolution_steps: usize,
    ) -> Result<Self, BvExprProofBudgetError> {
        if timeout.is_zero() {
            return Err(BvExprProofBudgetError::ZeroTimeout);
        }
        if timeout > Self::MAX_TIMEOUT {
            return Err(BvExprProofBudgetError::TimeoutTooLong {
                requested: timeout,
                maximum: Self::MAX_TIMEOUT,
            });
        }
        if max_resolution_steps == 0 {
            return Err(BvExprProofBudgetError::ZeroResolutionSteps);
        }
        if max_resolution_steps > Self::MAX_RESOLUTION_STEPS {
            return Err(BvExprProofBudgetError::TooManyResolutionSteps {
                requested: max_resolution_steps,
                maximum: Self::MAX_RESOLUTION_STEPS,
            });
        }
        Ok(Self {
            timeout,
            max_resolution_steps,
        })
    }

    /// Relative wall-clock timeout applied freshly to each export call.
    #[must_use]
    pub const fn timeout(&self) -> Duration {
        self.timeout
    }

    /// Maximum solver-surfaced and expanded resolution steps.
    #[must_use]
    pub const fn max_resolution_steps(&self) -> usize {
        self.max_resolution_steps
    }
}

/// Crate-internal bounds for proof-producing [`BvExpr`] validation.
///
/// The expression preflight runs before CNF allocation. The nested resolution
/// limits then bound SAT search, LRAT output/materialization, and independent
/// replay. Every instance passed to the bounded exporter must carry an absolute
/// deadline in `resolution`.
#[derive(Clone, Debug)]
pub(crate) struct BvExprProofLimits {
    /// Maximum DISTINCT expression nodes (structurally identical subtrees are
    /// one node). The encoder blasts each distinct node once, so this, not the
    /// occurrence count, measures encoding work.
    pub(crate) max_expr_nodes: usize,
    /// Maximum source OCCURRENCES: the tree walk of the preflight, and the
    /// constant-time memo lookup the encoder makes at a repeated occurrence.
    pub(crate) max_expr_occurrences: usize,
    pub(crate) max_expr_depth: usize,
    pub(crate) max_leaf_name_bytes: usize,
    /// Maximum width of any internal expression node. This may exceed the
    /// serialized proof's top-level equality width when a source-bound Bool
    /// query contains wide bit-vector terms.
    pub(crate) max_internal_width: u32,
    pub(crate) max_estimated_gate_work: usize,
    pub(crate) max_construction_bytes: usize,
    pub(crate) max_resolution_steps: usize,
    pub(crate) max_expanded_literals: usize,
    pub(crate) max_expansion_work: usize,
    pub(crate) max_expansion_bytes: usize,
    pub(crate) resolution: ResolutionProofLimits,
    /// Past a counted search or proof-size cap, try a swept refutation inside
    /// the same envelope (`sweep.rs`). Only the strict checker's lemma
    /// validation sets it, and only for a clause over no array.
    pub(crate) sweep: bool,
}

const BOUNDED_MAX_EXPR_NODES: usize = 4096;
/// Occurrences of the conservative preset. An occurrence costs one preflight
/// visit, one occurrence-table entry (charged to the construction bytes) and,
/// when it repeats a node, one memo lookup in the encoder; all gate
/// construction is charged per DISTINCT node against `BOUNDED_MAX_EXPR_NODES`.
const BOUNDED_MAX_EXPR_OCCURRENCES: usize = 100_000;
const BOUNDED_MAX_EXPR_DEPTH: usize = 512;
const BOUNDED_MAX_LEAF_NAME_BYTES: usize = 1024 * 1024;
const BOUNDED_MAX_INTERNAL_WIDTH: u32 = 128;
const BOUNDED_MAX_ESTIMATED_GATE_WORK: usize = 100_000;
const BOUNDED_MAX_CONSTRUCTION_BYTES: usize = 128 * 1024 * 1024;
/// Cumulative literal slots allocated while expanding one bounded RUP proof.
///
/// This is allocation-volume accounting, not a retained-memory allowance:
/// every allocation is independently charged to the 128 MiB byte envelope and
/// every traversal to the 50M work envelope below.
const BOUNDED_MAX_EXPANDED_LITERALS: usize = 2_000_000;
const BOUNDED_MAX_EXPANSION_WORK: usize = 50_000_000;
const BOUNDED_MAX_EXPANSION_BYTES: usize = 128 * 1024 * 1024;
const BOUNDED_MAX_REPLAY_WORK: u64 = 50_000_000;
const BOUNDED_MAX_REPLAY_BYTES: usize = 128 * 1024 * 1024;

impl BvExprProofLimits {
    fn conservative_external(deadline: Instant, max_resolution_steps: usize) -> Self {
        let mut resolution = ResolutionProofLimits {
            deadline: Some(deadline),
            // At construction the SAT engine retains about 849 bytes per
            // variable before clauses. This deliberately conservative external
            // preset bounds every retained proof phase; process-wide allocator
            // transients still require a caller-owned RSS envelope.
            max_num_vars: 150_000,
            max_input_clauses: 700_000,
            max_input_literals: 3_000_000,
            max_input_clause_literals: 64,
            max_input_bytes: 64 * 1024 * 1024,
            max_conflicts: Some(250_000),
            max_decisions: Some(2_000_000),
            solver_clause_db_reduction_threshold_bytes: 64 * 1024 * 1024,
            max_proof_output_bytes: 64 * 1024 * 1024,
            max_derived_steps: max_resolution_steps,
            max_derived_literals: 2_000_000,
            max_hints: 4_000_000,
            max_pending_deletions: 250_000,
            max_codec_bytes: 192 * 1024 * 1024,
            max_backward_reconstruction_bytes: 64 * 1024 * 1024,
            ..ResolutionProofLimits::default()
        };
        resolution.validation.deadline = Some(deadline);
        resolution.validation.max_original_clauses = resolution.max_input_clauses;
        resolution.validation.max_original_literals = resolution.max_input_literals;
        resolution.validation.max_derived_steps = max_resolution_steps;
        resolution.validation.max_derived_literals = resolution.max_derived_literals;
        resolution.validation.max_hints = resolution.max_hints;
        resolution.validation.max_work = BOUNDED_MAX_REPLAY_WORK;
        resolution.validation.max_bytes = BOUNDED_MAX_REPLAY_BYTES;

        Self {
            max_expr_nodes: BOUNDED_MAX_EXPR_NODES,
            max_expr_occurrences: BOUNDED_MAX_EXPR_OCCURRENCES,
            max_expr_depth: BOUNDED_MAX_EXPR_DEPTH,
            max_leaf_name_bytes: BOUNDED_MAX_LEAF_NAME_BYTES,
            max_internal_width: BOUNDED_MAX_INTERNAL_WIDTH,
            max_estimated_gate_work: BOUNDED_MAX_ESTIMATED_GATE_WORK,
            max_construction_bytes: BOUNDED_MAX_CONSTRUCTION_BYTES,
            max_resolution_steps,
            max_expanded_literals: BOUNDED_MAX_EXPANDED_LITERALS,
            max_expansion_work: BOUNDED_MAX_EXPANSION_WORK,
            max_expansion_bytes: BOUNDED_MAX_EXPANSION_BYTES,
            resolution,
            sweep: false,
        }
    }
}

/// Scratch state shared across the bit-blast of BOTH sides of the equality: one
/// gate cache (so common sub-terms fuse) and an interning table mapping each named
/// leaf to its (allocated-once) input bit vars.
struct ExprBlaster<'a> {
    cache: GateCache,
    deadline: Option<Instant>,
    keep_going: &'a mut dyn FnMut() -> bool,
    /// Leaf name → input bit vars (LSB-first). First-seen order also assigns the
    /// `InputLeaf { leaf }` index.
    leaves: std::collections::HashMap<String, Vec<u32>>,
    /// A cached `ConstFalse` zero bit (used by zero-extend / `Const` 0 bits), built once.
    zero_bit: Option<u32>,
    /// A cached `ConstTrue` one bit (used by `Const` 1 bits), built once.
    one_bit: Option<u32>,
    /// The preflight's occurrence table: source address -> interned node.
    /// Empty on the unbounded path, which therefore blasts every occurrence.
    shared: std::collections::HashMap<usize, u32>,
    /// Output bits of every interned node already blasted.
    blasted: std::collections::HashMap<u32, Vec<u32>>,
    /// Occurrences actually blasted (not answered from `blasted`).
    #[cfg(test)]
    node_blasts: usize,
}

impl<'a> ExprBlaster<'a> {
    fn new(deadline: Option<Instant>, keep_going: &'a mut dyn FnMut() -> bool) -> Self {
        Self {
            cache: GateCache::default(),
            deadline,
            keep_going,
            leaves: std::collections::HashMap::new(),
            zero_bit: None,
            one_bit: None,
            shared: std::collections::HashMap::new(),
            blasted: std::collections::HashMap::new(),
            #[cfg(test)]
            node_blasts: 0,
        }
    }

    fn check_deadline(&mut self) -> Result<(), BvExprExportError> {
        if self
            .deadline
            .is_some_and(|deadline| Instant::now() >= deadline)
        {
            Err(BvExprExportError::ResourceLimit {
                resource: "expression construction deadline",
                limit: 0,
                actual: 1,
            })
        } else {
            poll_export(self.keep_going)
        }
    }

    /// Get (or allocate, first-seen) the input bit vars for a named leaf.
    fn leaf_bits(
        &mut self,
        name: &str,
        width: u32,
        vars: &mut VarTable,
    ) -> Result<Vec<u32>, BvExprExportError> {
        if let Some(bits) = self.leaves.get(name) {
            if bits.len() != width as usize {
                return Err(BvExprExportError::Malformed(format!(
                    "one leaf name is used at both {} and {width} bits",
                    bits.len()
                )));
            }
            let mut copy = Vec::new();
            copy.try_reserve_exact(bits.len())
                .map_err(|_| BvExprExportError::ResourceLimit {
                    resource: "expression leaf-bit allocation",
                    limit: bits.len(),
                    actual: bits.len().saturating_add(1),
                })?;
            for &bit in bits {
                poll_export(self.keep_going)?;
                copy.push(bit);
            }
            return Ok(copy);
        }
        let leaf_idx =
            u32::try_from(self.leaves.len()).map_err(|_| BvExprExportError::ResourceLimit {
                resource: "expression leaf count",
                limit: u32::MAX as usize,
                actual: self.leaves.len(),
            })?;
        let mut owned_name = String::new();
        owned_name
            .try_reserve_exact(name.len())
            .map_err(|_| BvExprExportError::ResourceLimit {
                resource: "expression leaf-name allocation",
                limit: name.len(),
                actual: name.len().saturating_add(1),
            })?;
        owned_name.push_str(name);
        let width = width as usize;
        let mut bits = Vec::new();
        bits.try_reserve_exact(width)
            .map_err(|_| BvExprExportError::ResourceLimit {
                resource: "expression leaf-bit allocation",
                limit: width,
                actual: width.saturating_add(1),
            })?;
        for bit in 0..width {
            poll_export(self.keep_going)?;
            bits.push(vars.alloc(VarRole::InputLeaf {
                leaf: leaf_idx,
                bit: bit as u32,
            }));
        }
        let mut retained = Vec::new();
        retained
            .try_reserve_exact(width)
            .map_err(|_| BvExprExportError::ResourceLimit {
                resource: "expression leaf-bit allocation",
                limit: width,
                actual: width.saturating_add(1),
            })?;
        for &bit in &bits {
            poll_export(self.keep_going)?;
            retained.push(bit);
        }
        self.leaves.insert(owned_name, retained);
        Ok(bits)
    }

    /// A shared constant-false (zero) bit, for zero-extend padding.
    fn zero(
        &mut self,
        vars: &mut VarTable,
        bit_lemmas: &mut Vec<BitLemma>,
        clauses: &mut Vec<Clause>,
    ) -> u32 {
        if let Some(z) = self.zero_bit {
            return z;
        }
        let z = build_gate(
            BitLemmaKind::ConstFalse,
            vec![],
            VarRole::Aux { bit: 0 },
            vars,
            bit_lemmas,
            clauses,
            &mut self.cache,
        );
        self.zero_bit = Some(z);
        z
    }

    /// A shared constant-true (one) bit, for `Const` set bits.
    fn one(
        &mut self,
        vars: &mut VarTable,
        bit_lemmas: &mut Vec<BitLemma>,
        clauses: &mut Vec<Clause>,
    ) -> u32 {
        if let Some(o) = self.one_bit {
            return o;
        }
        let o = build_gate(
            BitLemmaKind::ConstTrue,
            vec![],
            VarRole::Aux { bit: 0 },
            vars,
            bit_lemmas,
            clauses,
            &mut self.cache,
        );
        self.one_bit = Some(o);
        o
    }

    /// One occurrence's bits, built from its operands' (possibly shared) bits.
    fn blast_node(
        &mut self,
        expr: &BvExpr,
        vars: &mut VarTable,
        bit_lemmas: &mut Vec<BitLemma>,
        clauses: &mut Vec<Clause>,
    ) -> Result<Vec<u32>, BvExprExportError> {
        #[cfg(test)]
        {
            self.node_blasts += 1;
        }
        match expr {
            BvExpr::Leaf { name, width } => {
                if *width == 0 {
                    return Err(BvExprExportError::Malformed(format!(
                        "leaf {name:?} has width 0"
                    )));
                }
                self.leaf_bits(name, *width, vars)
            }
            BvExpr::Add(l, r) | BvExpr::Sub(l, r) => {
                let lb = self.blast(l, vars, bit_lemmas, clauses)?;
                let rb = self.blast(r, vars, bit_lemmas, clauses)?;
                if lb.len() != rb.len() {
                    return Err(BvExprExportError::WidthMismatch {
                        lhs: lb.len() as u32,
                        rhs: rb.len() as u32,
                    });
                }
                let op = if matches!(expr, BvExpr::Sub(..)) {
                    BvOp::Sub
                } else {
                    BvOp::Add
                };
                // Reuse the operand-aware ripple-carry blaster, but through THIS
                // blaster's shared cache (Side::Lhs roles; the cache fuses common
                // sub-trees regardless of side label).
                let mut scratch = GateScratch {
                    cache: std::mem::take(&mut self.cache),
                };
                let out = blast_side_roles_with_cancellation(
                    op,
                    &lb,
                    &rb,
                    Side::Lhs,
                    vars,
                    bit_lemmas,
                    clauses,
                    &mut scratch,
                    self.keep_going,
                );
                self.cache = scratch.cache;
                let out = out?;
                self.check_deadline()?;
                Ok(out)
            }
            BvExpr::ZeroExt(inner, added) => {
                let mut bits = self.blast(inner, vars, bit_lemmas, clauses)?;
                let z = self.zero(vars, bit_lemmas, clauses);
                for _ in 0..*added {
                    self.check_deadline()?;
                    bits.push(z);
                }
                Ok(bits)
            }
            BvExpr::Extract { inner, high, low } => {
                let bits = self.blast(inner, vars, bit_lemmas, clauses)?;
                if low > high || (*high as usize) >= bits.len() {
                    return Err(BvExprExportError::Malformed(format!(
                        "extract [{high}:{low}] out of bounds for {}-bit operand",
                        bits.len()
                    )));
                }
                let mut selected = Vec::with_capacity((high - low + 1) as usize);
                for &bit in &bits[(*low as usize)..=(*high as usize)] {
                    self.check_deadline()?;
                    selected.push(bit);
                }
                Ok(selected)
            }
            BvExpr::Or(l, r) | BvExpr::And(l, r) | BvExpr::Xor(l, r) => {
                let lb = self.blast(l, vars, bit_lemmas, clauses)?;
                let rb = self.blast(r, vars, bit_lemmas, clauses)?;
                if lb.len() != rb.len() {
                    return Err(BvExprExportError::WidthMismatch {
                        lhs: lb.len() as u32,
                        rhs: rb.len() as u32,
                    });
                }
                // Both operands have been completely validated and constructed.
                // Known constant bits can select the exact existing wire; every
                // remaining bit uses the independently replayed Boolean gate.
                let kind = match expr {
                    BvExpr::Or(..) => BitLemmaKind::Or2,
                    BvExpr::And(..) => BitLemmaKind::And2,
                    // The match guard restricts this arm to {Or, And, Xor}.
                    _ => BitLemmaKind::Xor2,
                };
                Ok((0..lb.len())
                    .map(|bit| {
                        self.check_deadline()?;
                        if let Some(output) = self.constant_bitwise(kind, lb[bit], rb[bit]) {
                            return Ok(output);
                        }
                        Ok({
                            build_gate(
                                kind,
                                vec![lb[bit], rb[bit]],
                                VarRole::Aux { bit: bit as u32 },
                                vars,
                                bit_lemmas,
                                clauses,
                                &mut self.cache,
                            )
                        })
                    })
                    .collect::<Result<Vec<_>, BvExprExportError>>()?)
            }
            BvExpr::Const { value, width } => {
                if *width == 0 {
                    return Err(BvExprExportError::Malformed(
                        "constant has width 0".to_string(),
                    ));
                }
                // Bits at or above `width` of `value` must be zero — otherwise the
                // literal cannot be represented in `width` bits (a malformed RAW
                // obligation, never silently truncated).
                if *width < 128 && (*value >> *width) != 0 {
                    return Err(BvExprExportError::Malformed(format!(
                        "constant {value} does not fit in {width} bits"
                    )));
                }
                // Each bit is a fixed `ConstTrue`/`ConstFalse` literal (no input
                // bits). The two cached const bits flow through the shared cache, so
                // every set bit reuses one `ConstTrue` var and every clear bit reuses
                // one `ConstFalse` var.
                Ok((0..*width)
                    .map(|bit| {
                        self.check_deadline()?;
                        Ok({
                            let set = (*value >> bit) & 1 == 1;
                            if set {
                                self.one(vars, bit_lemmas, clauses)
                            } else {
                                self.zero(vars, bit_lemmas, clauses)
                            }
                        })
                    })
                    .collect::<Result<Vec<_>, BvExprExportError>>()?)
            }
            BvExpr::SignExt(inner, added) => {
                let bits = self.blast(inner, vars, bit_lemmas, clauses)?;
                if bits.is_empty() {
                    return Err(BvExprExportError::Malformed(
                        "sign_extend of a zero-width expression".to_string(),
                    ));
                }
                // Replicate the SIGN bit (the existing MSB output var) `added`
                // times above `inner`. No new gate is introduced — the sign bit is
                // an output var the inner blast already defined, so the clean
                // kernel re-checks this with the SAME gate vocabulary.
                let sign = *bits.last().expect("non-empty checked above");
                let mut out = bits;
                for _ in 0..*added {
                    self.check_deadline()?;
                    out.push(sign);
                }
                Ok(out)
            }
            BvExpr::Shl(value, amount)
            | BvExpr::Lshr(value, amount)
            | BvExpr::Ashr(value, amount) => {
                let vb = self.blast(value, vars, bit_lemmas, clauses)?;
                let ab = self.blast(amount, vars, bit_lemmas, clauses)?;
                if vb.len() != ab.len() {
                    return Err(BvExprExportError::WidthMismatch {
                        lhs: vb.len() as u32,
                        rhs: ab.len() as u32,
                    });
                }
                let op = match expr {
                    BvExpr::Shl(..) => BvOp::Shl,
                    BvExpr::Lshr(..) => BvOp::Lshr,
                    // The match guard restricts this arm to {Shl, Lshr, Ashr}.
                    _ => BvOp::Ashr,
                };
                if let BvExpr::Const { value: amount, .. } = amount.as_ref() {
                    // Both operands have already been fully validated and
                    // blasted. A literal amount needs only exact bit wiring,
                    // including the SMT over-shift result, not a barrel mux.
                    let zero = self.zero(vars, bit_lemmas, clauses);
                    let sign = vb[vb.len() - 1];
                    let amount = usize::try_from(*amount).unwrap_or(vb.len()).min(vb.len());
                    let out = crate::bv_blast_export::shift_const_rewire(
                        op,
                        &vb,
                        amount,
                        zero,
                        sign,
                        self.keep_going,
                    )
                    .map_err(|()| BvExprExportError::Cancelled)?;
                    self.check_deadline()?;
                    return Ok(out);
                }
                // Reuse the operand-swap path's barrel-shifter blaster, but through
                // THIS blaster's shared cache (so structurally-identical shifts on
                // the two sides of the equality fuse to one set of output vars).
                // Every gate `blast_shift` emits is an existing `BitLemmaKind`.
                let out = blast_shift_with_cancellation(
                    op,
                    &vb,
                    &ab,
                    vars,
                    bit_lemmas,
                    clauses,
                    &mut self.cache,
                    self.keep_going,
                )
                .map_err(|()| BvExprExportError::Cancelled)?;
                self.check_deadline()?;
                Ok(out)
            }
            BvExpr::Not(inner) => {
                // Per-bit NOT: one existing `Not` gate per bit (same gate the
                // subtraction's one's-complement uses). NO new kernel gate KIND.
                let bits = self.blast(inner, vars, bit_lemmas, clauses)?;
                Ok(bits
                    .into_iter()
                    .map(|b| {
                        self.check_deadline()?;
                        Ok({
                            build_gate(
                                BitLemmaKind::Not,
                                vec![b],
                                VarRole::Aux { bit: 0 },
                                vars,
                                bit_lemmas,
                                clauses,
                                &mut self.cache,
                            )
                        })
                    })
                    .collect::<Result<Vec<_>, BvExprExportError>>()?)
            }
            BvExpr::Ult(l, r) => self.blast_unsigned_compare(l, r, vars, bit_lemmas, clauses),
            BvExpr::Eq(l, r) => {
                // Bit-vector equality -> a SINGLE-bit predicate. Per-bit `XnorEq`
                // (each `e_i <=> l_i == r_i`) AND-reduced to one bit by a chain of
                // existing `And2` gates. NO new kernel gate KIND: a downstream proof consumer re-checks
                // `XnorEq` and `And2` through their existing reflections.
                let lb = self.blast(l, vars, bit_lemmas, clauses)?;
                let rb = self.blast(r, vars, bit_lemmas, clauses)?;
                if lb.len() != rb.len() {
                    return Err(BvExprExportError::WidthMismatch {
                        lhs: lb.len() as u32,
                        rhs: rb.len() as u32,
                    });
                }
                if lb.is_empty() {
                    return Err(BvExprExportError::Malformed(
                        "equality of zero-width expressions".to_string(),
                    ));
                }
                // Per-bit XNOR (bit-equality) vars.
                let bit_eqs: Vec<u32> = (0..lb.len())
                    .map(|bit| {
                        self.check_deadline()?;
                        Ok({
                            build_gate(
                                BitLemmaKind::XnorEq,
                                vec![lb[bit], rb[bit]],
                                VarRole::Aux { bit: bit as u32 },
                                vars,
                                bit_lemmas,
                                clauses,
                                &mut self.cache,
                            )
                        })
                    })
                    .collect::<Result<Vec<_>, BvExprExportError>>()?;
                // AND-reduce the per-bit equalities into one predicate bit.
                let mut acc = bit_eqs[0];
                for &e in &bit_eqs[1..] {
                    self.check_deadline()?;
                    acc = build_gate(
                        BitLemmaKind::And2,
                        vec![acc, e],
                        VarRole::Aux { bit: 0 },
                        vars,
                        bit_lemmas,
                        clauses,
                        &mut self.cache,
                    );
                }
                // A 1-bit-wide result (LSB = the equality predicate).
                Ok(vec![acc])
            }
            BvExpr::CarryOut { lhs, rhs, is_sub } => {
                // The final carry-out of the EXISTING ripple-carry chain, exposed
                // as a 1-bit result. We thread the SAME `FullAdderCarry` (MAJ)
                // gates the `Add`/`Sub` sum uses — but run the chain to the MSB and
                // return the top carry (which the sum path discards). For `Sub`,
                // operand2 = ~rhs and carry-in = 1 (two's complement a + ~b + 1).
                // NO new kernel gate KIND: a downstream proof consumer re-checks `FullAdderCarry`/`Not`/
                // `ConstTrue`/`ConstFalse` through their existing reflections.
                let ab = self.blast(lhs, vars, bit_lemmas, clauses)?;
                let bb = self.blast(rhs, vars, bit_lemmas, clauses)?;
                if ab.len() != bb.len() {
                    return Err(BvExprExportError::WidthMismatch {
                        lhs: ab.len() as u32,
                        rhs: bb.len() as u32,
                    });
                }
                if ab.is_empty() {
                    return Err(BvExprExportError::Malformed(
                        "carry-out of a zero-width expression".to_string(),
                    ));
                }
                let n = ab.len();
                let (op2_bits, cin): (Vec<u32>, u32) = if *is_sub {
                    let notb: Vec<u32> = bb
                        .iter()
                        .map(|&b| {
                            self.check_deadline()?;
                            Ok({
                                build_gate(
                                    BitLemmaKind::Not,
                                    vec![b],
                                    VarRole::Aux { bit: 0 },
                                    vars,
                                    bit_lemmas,
                                    clauses,
                                    &mut self.cache,
                                )
                            })
                        })
                        .collect::<Result<Vec<_>, BvExprExportError>>()?;
                    let t = self.one(vars, bit_lemmas, clauses);
                    (notb, t)
                } else {
                    let f = self.zero(vars, bit_lemmas, clauses);
                    (bb, f)
                };
                // Ripple the carry through ALL n bits (the MSB carry is the result).
                let mut carry = cin;
                for bit in 0..n {
                    self.check_deadline()?;
                    carry = build_gate(
                        BitLemmaKind::FullAdderCarry,
                        vec![ab[bit], op2_bits[bit], carry],
                        VarRole::Aux { bit: bit as u32 },
                        vars,
                        bit_lemmas,
                        clauses,
                        &mut self.cache,
                    );
                }
                // A 1-bit-wide result (LSB = the final carry-out).
                Ok(vec![carry])
            }
            BvExpr::UDiv(l, r) | BvExpr::URem(l, r) => {
                let (quotient, remainder) = self.blast_division(l, r, vars, bit_lemmas, clauses)?;
                Ok(if matches!(expr, BvExpr::UDiv(..)) {
                    quotient
                } else {
                    remainder
                })
            }
            BvExpr::Mul(l, r) => {
                // Shift-and-add ARRAY multiplier, truncated to the low `n` bits
                // (two's-complement wrapping multiply, matching SMT `bvmul`). NO
                // new kernel gate KIND: partial products are existing `And2`
                // gates; the row sums reuse the SAME `Xor3` (sum) +
                // `FullAdderCarry` (carry) gates `Add` uses, plus the shared
                // `ConstFalse` zero bit. Every gate flows through THIS blaster's
                // shared cache, so a `Mul` appearing identically on both sides of
                // the equality fuses to one set of output vars.
                let ab = self.blast(l, vars, bit_lemmas, clauses)?;
                let bb = self.blast(r, vars, bit_lemmas, clauses)?;
                if ab.len() != bb.len() {
                    return Err(BvExprExportError::WidthMismatch {
                        lhs: ab.len() as u32,
                        rhs: bb.len() as u32,
                    });
                }
                if ab.is_empty() {
                    return Err(BvExprExportError::Malformed(
                        "multiply of a zero-width expression".to_string(),
                    ));
                }
                let n = ab.len();
                let zero = self.zero(vars, bit_lemmas, clauses);

                // Accumulator holds the low `n` bits of the running product,
                // LSB-first. Row j contributes `(a & b[j]) << j`; only the low
                // `n` output positions are retained, so partial-product bits
                // above position `n` are never built (the array is truncated).
                //
                // Row 0 (no shift) initializes the accumulator: acc[i] = a[i] ∧ b[0].
                let mut acc: Vec<u32> = (0..n)
                    .map(|i| {
                        self.check_deadline()?;
                        Ok({
                            build_gate(
                                BitLemmaKind::And2,
                                vec![ab[i], bb[0]],
                                VarRole::Aux { bit: i as u32 },
                                vars,
                                bit_lemmas,
                                clauses,
                                &mut self.cache,
                            )
                        })
                    })
                    .collect::<Result<Vec<_>, BvExprExportError>>()?;

                // Add each remaining shifted partial-product row into `acc`.
                for (j, &b_j) in bb.iter().enumerate().take(n).skip(1) {
                    self.check_deadline()?;
                    // Row j shifted left by `j`: positions 0..j are zero, then
                    // pp[i] = a[i] ∧ b[j] occupies position `i + j`. Build only the
                    // positions that land within the retained low `n` bits.
                    let row: Vec<u32> = (0..n)
                        .map(|pos| {
                            self.check_deadline()?;
                            Ok({
                                if pos < j {
                                    zero
                                } else {
                                    let i = pos - j;
                                    build_gate(
                                        BitLemmaKind::And2,
                                        vec![ab[i], b_j],
                                        VarRole::Aux { bit: pos as u32 },
                                        vars,
                                        bit_lemmas,
                                        clauses,
                                        &mut self.cache,
                                    )
                                }
                            })
                        })
                        .collect::<Result<Vec<_>, BvExprExportError>>()?;

                    // Ripple-carry add `row` into `acc` (truncated to `n` bits,
                    // carry-out of the MSB discarded). Same `Xor3`/`FullAdderCarry`
                    // gates the `Add` path uses.
                    let mut carry = zero;
                    let mut next = Vec::with_capacity(n);
                    for bit in 0..n {
                        self.check_deadline()?;
                        // The shifted row is zero below j and no carry can
                        // enter those positions. Preserve the exact lower
                        // product prefix across multiplication widths.
                        if bit < j {
                            next.push(acc[bit]);
                            continue;
                        }
                        let sum = build_gate(
                            BitLemmaKind::Xor3,
                            vec![acc[bit], row[bit], carry],
                            VarRole::Aux { bit: bit as u32 },
                            vars,
                            bit_lemmas,
                            clauses,
                            &mut self.cache,
                        );
                        if bit != n - 1 {
                            carry = build_gate(
                                BitLemmaKind::FullAdderCarry,
                                vec![acc[bit], row[bit], carry],
                                VarRole::Aux { bit: bit as u32 },
                                vars,
                                bit_lemmas,
                                clauses,
                                &mut self.cache,
                            );
                        }
                        next.push(sum);
                    }
                    acc = next;
                }

                Ok(acc)
            }
        }
    }
}

#[derive(Default)]
struct BvExprPreflight {
    /// Distinct (interned) nodes, charged against `max_expr_nodes`.
    nodes: usize,
    /// Source occurrences, charged against `max_expr_occurrences`.
    occurrences: usize,
    leaf_name_bytes: usize,
    leaf_widths: std::collections::HashMap<String, u32>,
    estimated_gate_work: usize,
    /// Output bits of every distinct node, the memo's retained payload.
    output_bits: usize,
    top_width: usize,
    sharing: preflight_sharing::Sharing,
    last_node: u32,
}

#[cfg(test)]
fn preflight_bv_expr(
    expr: &BvExpr,
    limits: &BvExprProofLimits,
    state: &mut BvExprPreflight,
    depth: usize,
) -> Result<u32, BvExprExportError> {
    preflight_bv_expr_with_cancellation(expr, limits, state, depth, &mut || true)
}

fn preflight_bv_expr_with_cancellation(
    expr: &BvExpr,
    limits: &BvExprProofLimits,
    state: &mut BvExprPreflight,
    depth: usize,
    keep_going: &mut dyn FnMut() -> bool,
) -> Result<u32, BvExprExportError> {
    if limits
        .resolution
        .deadline
        .is_some_and(|deadline| Instant::now() >= deadline)
    {
        return Err(BvExprExportError::ResourceLimit {
            resource: "expression preflight deadline",
            limit: 0,
            actual: 1,
        });
    }
    poll_export(keep_going)?;
    if depth > limits.max_expr_depth {
        return Err(BvExprExportError::ResourceLimit {
            resource: "expression depth",
            limit: limits.max_expr_depth,
            actual: depth,
        });
    }
    charge_bv_expr_resource(
        "expression occurrences",
        &mut state.occurrences,
        1,
        limits.max_expr_occurrences,
    )?;
    if let BvExpr::Leaf { name, .. } = expr {
        // Counting repeated references is intentionally conservative and avoids
        // allocating a temporary uniqueness set before the tree is bounded.
        charge_bv_expr_resource(
            "expression leaf-name bytes",
            &mut state.leaf_name_bytes,
            name.len(),
            limits.max_leaf_name_bytes,
        )?;
        if let BvExpr::Leaf { width, .. } = expr {
            if let Some(previous) = state.leaf_widths.get(name) {
                if previous != width {
                    return Err(BvExprExportError::Malformed(format!(
                        "one leaf name is used at both {previous} and {width} bits"
                    )));
                }
            } else {
                let mut owned = String::new();
                owned.try_reserve_exact(name.len()).map_err(|_| {
                    BvExprExportError::ResourceLimit {
                        resource: "expression preflight leaf allocation",
                        limit: limits.max_leaf_name_bytes,
                        actual: limits.max_leaf_name_bytes.saturating_add(1),
                    }
                })?;
                owned.push_str(name);
                state
                    .leaf_widths
                    .try_reserve(1)
                    .map_err(|_| BvExprExportError::ResourceLimit {
                        resource: "expression preflight leaf allocation",
                        limit: limits.max_leaf_name_bytes,
                        actual: limits.max_leaf_name_bytes.saturating_add(1),
                    })?;
                state.leaf_widths.insert(owned, *width);
            }
        }
    }

    let mut children = [u32::MAX; 2];
    let mut next_child = 0;
    let mut child = |inner: &BvExpr| {
        let width =
            preflight_bv_expr_with_cancellation(inner, limits, state, depth + 1, keep_going)?;
        children[next_child] = state.last_node;
        next_child += 1;
        Ok::<_, BvExprExportError>(width)
    };
    // `local_work` bounds the variables this node can ALLOCATE, before any
    // cache credit (`topology_bound`): leaf inputs and gate outputs alike.
    let (width, local_work) = match expr {
        BvExpr::Leaf { width, .. } => (*width, topology_bound::leaf(*width as usize)),
        BvExpr::Const { width, .. } => (*width, topology_bound::constant(*width as usize)),
        BvExpr::ZeroExt(inner, added) | BvExpr::SignExt(inner, added) => {
            let inner_width = child(inner)?;
            let width = inner_width.checked_add(*added).ok_or_else(|| {
                BvExprExportError::Malformed("bit-vector extension width overflow".to_string())
            })?;
            let zero_padded = matches!(expr, BvExpr::ZeroExt(..));
            (width, topology_bound::extension(zero_padded))
        }
        BvExpr::Extract { inner, high, low } => {
            let inner_width = child(inner)?;
            if low > high || *high >= inner_width {
                return Err(BvExprExportError::Malformed(format!(
                    "extract [{high}:{low}] out of bounds for {inner_width}-bit operand"
                )));
            }
            (high - low + 1, topology_bound::EXTRACT)
        }
        BvExpr::Not(inner) => {
            let width = child(inner)?;
            (width, topology_bound::bitwise(width as usize))
        }
        BvExpr::Add(lhs, rhs) | BvExpr::Sub(lhs, rhs) => {
            let lhs_width = child(lhs)?;
            let rhs_width = child(rhs)?;
            require_bv_expr_width_match(lhs_width, rhs_width)?;
            (lhs_width, topology_bound::ripple(lhs_width as usize))
        }
        BvExpr::Or(lhs, rhs) | BvExpr::And(lhs, rhs) | BvExpr::Xor(lhs, rhs) => {
            let lhs_width = child(lhs)?;
            let rhs_width = child(rhs)?;
            require_bv_expr_width_match(lhs_width, rhs_width)?;
            (lhs_width, topology_bound::bitwise(lhs_width as usize))
        }
        BvExpr::Ult(lhs, rhs) => {
            let lhs_width = child(lhs)?;
            let rhs_width = child(rhs)?;
            require_bv_expr_width_match(lhs_width, rhs_width)?;
            (1, topology_bound::compare(lhs_width as usize))
        }
        BvExpr::Eq(lhs, rhs) => {
            let lhs_width = child(lhs)?;
            let rhs_width = child(rhs)?;
            require_bv_expr_width_match(lhs_width, rhs_width)?;
            (1, topology_bound::equality(lhs_width as usize))
        }
        BvExpr::CarryOut { lhs, rhs, .. } => {
            let lhs_width = child(lhs)?;
            let rhs_width = child(rhs)?;
            require_bv_expr_width_match(lhs_width, rhs_width)?;
            (1, topology_bound::ripple(lhs_width as usize))
        }
        BvExpr::Shl(lhs, rhs) | BvExpr::Lshr(lhs, rhs) | BvExpr::Ashr(lhs, rhs)
            if matches!(rhs.as_ref(), BvExpr::Const { .. }) =>
        {
            let lhs_width = child(lhs)?;
            let rhs_width = child(rhs)?;
            require_bv_expr_width_match(lhs_width, rhs_width)?;
            // Literal shifts only rewire width bits and may add one zero
            // gate. Their operands are charged separately above. The actual
            // emitted-gate limit remains enforced after construction.
            (lhs_width, topology_bound::LITERAL_SHIFT)
        }
        BvExpr::Mul(lhs, rhs)
        | BvExpr::UDiv(lhs, rhs)
        | BvExpr::URem(lhs, rhs)
        | BvExpr::Shl(lhs, rhs)
        | BvExpr::Lshr(lhs, rhs)
        | BvExpr::Ashr(lhs, rhs) => {
            let lhs_width = child(lhs)?;
            let rhs_width = child(rhs)?;
            require_bv_expr_width_match(lhs_width, rhs_width)?;
            let width = lhs_width as usize;
            // Count the actual construction topology without cache credit.
            // The existing gate, memory, deadline and replay limits still apply.
            let work = match expr {
                BvExpr::Mul(..) => topology_bound::multiply(width),
                BvExpr::UDiv(..) | BvExpr::URem(..) => topology_bound::divide(width),
                _ => topology_bound::shift(width),
            };
            (lhs_width, work)
        }
    };

    if width == 0 || width > limits.max_internal_width {
        return Err(BvExprExportError::UnsupportedWidth {
            got: width,
            max: limits.max_internal_width,
        });
    }
    let (node, fresh) =
        state
            .sharing
            .intern(expr, width, children, limits.max_construction_bytes)?;
    state.last_node = node;
    if fresh {
        charge_bv_expr_resource(
            "expression nodes",
            &mut state.nodes,
            1,
            limits.max_expr_nodes,
        )?;
        charge_bv_expr_resource(
            "estimated bit-blast gates",
            &mut state.estimated_gate_work,
            local_work,
            limits.max_estimated_gate_work,
        )?;
        // The memo stores every distinct node's output bits (`node_memo`).
        state.output_bits = state.output_bits.saturating_add(width as usize);
    }
    Ok(width)
}

fn require_bv_expr_width_match(lhs: u32, rhs: u32) -> Result<(), BvExprExportError> {
    if lhs == rhs {
        Ok(())
    } else {
        Err(BvExprExportError::WidthMismatch { lhs, rhs })
    }
}

fn charge_bv_expr_resource(
    resource: &'static str,
    total: &mut usize,
    amount: usize,
    limit: usize,
) -> Result<(), BvExprExportError> {
    let actual = total.checked_add(amount).unwrap_or(usize::MAX);
    if actual > limit {
        return Err(BvExprExportError::ResourceLimit {
            resource,
            limit,
            actual,
        });
    }
    *total = actual;
    Ok(())
}

fn reserve_bv_expr_construction(
    vars: &mut VarTable,
    bit_lemmas: &mut Vec<BitLemma>,
    clauses: &mut Vec<Clause>,
    blaster: &mut ExprBlaster,
    limits: &BvExprProofLimits,
    preflight: BvExprPreflight,
) -> Result<(), BvExprExportError> {
    blaster.check_deadline()?;
    // `estimated_gate_work` is a conservative topology estimate, not an exact
    // emitted gate count. Reserve the primary retained stores from that bound;
    // individual fixed-arity gate temporaries remain caller-RSS transients.
    let gate_capacity = preflight.estimated_gate_work;
    let clause_capacity = gate_capacity
        .checked_mul(8)
        .and_then(|clauses| clauses.checked_add(1))
        .ok_or(BvExprExportError::ResourceLimit {
            resource: "expression construction bytes",
            limit: limits.max_construction_bytes,
            actual: usize::MAX,
        })?;
    let literal_capacity = gate_capacity
        .checked_mul(32)
        .and_then(|literals| literals.checked_add(preflight.top_width))
        .ok_or(BvExprExportError::ResourceLimit {
            resource: "expression construction bytes",
            limit: limits.max_construction_bytes,
            actual: usize::MAX,
        })?;
    if gate_capacity > limits.resolution.max_num_vars {
        return Err(BvExprExportError::ResourceLimit {
            resource: "preflight construction variables",
            limit: limits.resolution.max_num_vars,
            actual: gate_capacity,
        });
    }
    if clause_capacity > limits.resolution.max_input_clauses {
        return Err(BvExprExportError::ResourceLimit {
            resource: "preflight construction clauses",
            limit: limits.resolution.max_input_clauses,
            actual: clause_capacity,
        });
    }
    if literal_capacity > limits.resolution.max_input_literals {
        return Err(BvExprExportError::ResourceLimit {
            resource: "preflight construction literals",
            limit: limits.resolution.max_input_literals,
            actual: literal_capacity,
        });
    }
    let leaf_capacity = preflight.leaf_widths.len();
    let leaf_bits = preflight
        .leaf_widths
        .values()
        .try_fold(0_usize, |total, width| total.checked_add(*width as usize))
        .ok_or(BvExprExportError::ResourceLimit {
            resource: "expression construction bytes",
            limit: limits.max_construction_bytes,
            actual: usize::MAX,
        })?;
    let requested = gate_capacity
        .checked_mul(size_of::<VarRole>() + size_of::<BitLemma>())
        .and_then(|bytes| {
            clause_capacity
                .checked_mul(size_of::<Clause>())
                .and_then(|clauses| bytes.checked_add(clauses))
        })
        .and_then(|bytes| {
            literal_capacity
                .checked_mul(size_of::<Lit>())
                .and_then(|literals| bytes.checked_add(literals))
        })
        .and_then(|bytes| {
            gate_capacity
                .checked_mul(6 * size_of::<u32>())
                .and_then(|gate_inputs| bytes.checked_add(gate_inputs))
        })
        .and_then(|bytes| {
            leaf_capacity
                .checked_mul(size_of::<(String, Vec<u32>)>() * 2)
                .and_then(|leaves| bytes.checked_add(leaves))
        })
        .and_then(|bytes| {
            leaf_bits
                .checked_mul(size_of::<u32>())
                .and_then(|bits| bytes.checked_add(bits))
        })
        .and_then(|bytes| bytes.checked_add(preflight.leaf_name_bytes))
        .and_then(|bytes| bytes.checked_add(preflight.sharing.bytes()))
        .and_then(|bytes| {
            node_memo::reserved_bytes(preflight.nodes, preflight.output_bits)
                .and_then(|memo| bytes.checked_add(memo))
        })
        .unwrap_or(usize::MAX);
    if requested > limits.max_construction_bytes {
        return Err(BvExprExportError::ResourceLimit {
            resource: "expression construction bytes",
            limit: limits.max_construction_bytes,
            actual: requested,
        });
    }

    let allocation_failed = || BvExprExportError::ResourceLimit {
        resource: "expression construction allocation",
        limit: limits.max_construction_bytes,
        actual: limits.max_construction_bytes.saturating_add(1),
    };
    vars.roles
        .try_reserve_exact(gate_capacity)
        .map_err(|_| allocation_failed())?;
    bit_lemmas
        .try_reserve_exact(gate_capacity)
        .map_err(|_| allocation_failed())?;
    clauses
        .try_reserve_exact(clause_capacity)
        .map_err(|_| allocation_failed())?;
    blaster
        .cache
        .try_reserve(gate_capacity)
        .map_err(|_| allocation_failed())?;
    blaster
        .leaves
        .try_reserve(leaf_capacity)
        .map_err(|_| allocation_failed())?;
    blaster
        .blasted
        .try_reserve(preflight.nodes)
        .map_err(|_| allocation_failed())?;
    blaster.check_deadline()
}

#[cfg(test)]
fn materialize_sat_clauses_bounded(
    clauses: &[Clause],
    limits: &ResolutionProofLimits,
) -> Result<Vec<Vec<Literal>>, BvExprExportError> {
    materialize_sat_clauses_with_cancellation(clauses, limits, &mut || true)
}

fn materialize_sat_clauses_with_cancellation(
    clauses: &[Clause],
    limits: &ResolutionProofLimits,
    keep_going: &mut dyn FnMut() -> bool,
) -> Result<Vec<Vec<Literal>>, BvExprExportError> {
    let deadline = limits.deadline;
    check_sat_materialization_deadline(deadline)?;
    poll_export(keep_going)?;
    let mut literals = 0_usize;
    for (index, clause) in clauses.iter().enumerate() {
        if index & 0x3ff == 0 {
            check_sat_materialization_deadline(deadline)?;
        }
        poll_export(keep_going)?;
        if clause.lits.len() > limits.max_input_clause_literals {
            return Err(BvExprExportError::ResourceLimit {
                resource: "SAT input clause literals",
                limit: limits.max_input_clause_literals,
                actual: clause.lits.len(),
            });
        }
        literals = literals.saturating_add(clause.lits.len());
    }
    let requested = clauses
        .len()
        .checked_mul(size_of::<Vec<Literal>>())
        .and_then(|records| {
            literals
                .checked_mul(size_of::<Literal>())
                .and_then(|bytes| records.checked_add(bytes))
        })
        .unwrap_or(usize::MAX);
    if clauses.len() > limits.max_input_clauses {
        return Err(BvExprExportError::ResourceLimit {
            resource: "SAT input clauses",
            limit: limits.max_input_clauses,
            actual: clauses.len(),
        });
    }
    if literals > limits.max_input_literals {
        return Err(BvExprExportError::ResourceLimit {
            resource: "SAT input literals",
            limit: limits.max_input_literals,
            actual: literals,
        });
    }
    if requested > limits.max_input_bytes {
        return Err(BvExprExportError::ResourceLimit {
            resource: "SAT input materialization",
            limit: limits.max_input_bytes,
            actual: requested,
        });
    }

    let mut out = Vec::new();
    check_sat_materialization_deadline(deadline)?;
    out.try_reserve_exact(clauses.len())
        .map_err(|_| BvExprExportError::ResourceLimit {
            resource: "SAT clause record allocation",
            limit: limits.max_input_bytes,
            actual: requested,
        })?;
    let mut actual = out.capacity().saturating_mul(size_of::<Vec<Literal>>());
    for (index, clause) in clauses.iter().enumerate() {
        if index & 0x3ff == 0 {
            check_sat_materialization_deadline(deadline)?;
        }
        poll_export(keep_going)?;
        let mut copy = Vec::new();
        copy.try_reserve_exact(clause.lits.len()).map_err(|_| {
            BvExprExportError::ResourceLimit {
                resource: "SAT literal allocation",
                limit: limits.max_input_bytes,
                actual: requested,
            }
        })?;
        actual = actual.saturating_add(copy.capacity().saturating_mul(size_of::<Literal>()));
        if actual > limits.max_input_bytes {
            return Err(BvExprExportError::ResourceLimit {
                resource: "SAT input allocation capacity",
                limit: limits.max_input_bytes,
                actual,
            });
        }
        for literal in &clause.lits {
            poll_export(keep_going)?;
            copy.push(lit_to_sat(literal));
        }
        out.push(copy);
    }
    poll_export(keep_going)?;
    Ok(out)
}

fn check_sat_materialization_deadline(deadline: Option<Instant>) -> Result<(), BvExprExportError> {
    if deadline.is_some_and(|end| Instant::now() >= end) {
        return Err(BvExprExportError::ResourceLimit {
            resource: "SAT clause materialization deadline",
            limit: 0,
            actual: 1,
        });
    }
    Ok(())
}

/// Build a zero-trust [`BvBlastProof`] for an arbitrary BitVec equality `lhs == rhs`
/// over the [`BvExpr`] fragment, refuting `not(lhs == rhs)` via the `ay-sat` solver.
///
/// This is the generalized entry point the external-codegen M-POS gate needs: it accepts the
/// gate's add-leaf disequality
/// `not( BvExtract(BvZeroExt(BvAdd(W0,W1,32),32),31,0) == BvAdd(W0,W1,32) )`
/// directly (the two sides share the named leaves `W0`/`W1` and the inner adder),
/// rather than a structured `(op, a, b)` triple.
///
/// # Behavior
/// * Both sides are bit-blasted through ONE shared gate cache, so common sub-terms
///   fuse to the same output vars (the add-leaf's two sides collapse to identical
///   output bits — the equality is valid for all inputs).
/// * The CNF (`XnorEq` per bit + the single disequality clause) is handed to
///   [`ay_sat::prove_unsat_resolution_dag`]. UNSAT ⇒ the solver's real refutation is
///   surfaced and a validating proof is returned. SAT ⇒ [`BvExprExportError::NoRefutation`]
///   (anti-vacuity: e.g. `BvAdd == BvSub` is a false identity and yields no proof).
///
/// # Errors
/// See [`BvExprExportError`].
pub fn export_bv_blast_proof_expr(
    lhs: &BvExpr,
    rhs: &BvExpr,
) -> Result<BvBlastProof, BvExprExportError> {
    export_bv_blast_proof_expr_impl(lhs, rhs, None, &mut || true)
}

/// Build a zero-trust [`BvBlastProof`] under a conservative finite budget.
///
/// Unlike [`export_bv_blast_proof_expr`], this entry point preflights the full
/// expression tree before CNF allocation, applies finite construction and SAT
/// materialization limits, bounds proof production and independent replay, and
/// shares one freshly computed absolute deadline across every phase.
///
/// # Errors
/// See [`BvExprExportError`]. Resource or deadline exhaustion always rejects;
/// it never falls back to the compatibility exporter.
pub fn export_bv_blast_proof_expr_bounded(
    lhs: &BvExpr,
    rhs: &BvExpr,
    budget: &BvExprProofBudget,
) -> Result<BvBlastProof, BvExprExportError> {
    let deadline =
        Instant::now()
            .checked_add(budget.timeout())
            .ok_or(BvExprExportError::ResourceLimit {
                resource: "absolute proof deadline",
                limit: BvExprProofBudget::MAX_TIMEOUT.as_secs() as usize,
                actual: usize::MAX,
            })?;
    let limits = BvExprProofLimits::conservative_external(deadline, budget.max_resolution_steps());
    export_bv_blast_proof_expr_with_limits(lhs, rhs, &limits)
}

/// Internal bounded sibling used by strict proof recognition and the public
/// consumer-neutral budget API.
pub(crate) fn export_bv_blast_proof_expr_with_limits(
    lhs: &BvExpr,
    rhs: &BvExpr,
    limits: &BvExprProofLimits,
) -> Result<BvBlastProof, BvExprExportError> {
    export_bv_blast_proof_expr_with_limits_and_cancellation(lhs, rhs, limits, &mut || true)
}

/// Thread one caller-owned refusal through bounded expression and proof work.
/// Existing deadlines and numerical limits remain independently enforced.
pub(crate) fn export_bv_blast_proof_expr_with_limits_and_cancellation(
    lhs: &BvExpr,
    rhs: &BvExpr,
    limits: &BvExprProofLimits,
    keep_going: &mut dyn FnMut() -> bool,
) -> Result<BvBlastProof, BvExprExportError> {
    cancellation::run(keep_going, |keep_going| {
        export_bv_blast_proof_expr_controlled(lhs, rhs, limits, keep_going)
    })
}

fn export_bv_blast_proof_expr_controlled(
    lhs: &BvExpr,
    rhs: &BvExpr,
    limits: &BvExprProofLimits,
    keep_going: &mut dyn FnMut() -> bool,
) -> Result<BvBlastProof, BvExprExportError> {
    let preflight = preflight_bv_equality(lhs, rhs, limits, keep_going)?;
    export_bv_blast_proof_expr_impl(lhs, rhs, Some((limits, preflight)), keep_going)
}

fn preflight_bv_equality(
    lhs: &BvExpr,
    rhs: &BvExpr,
    limits: &BvExprProofLimits,
    keep_going: &mut dyn FnMut() -> bool,
) -> Result<BvExprPreflight, BvExprExportError> {
    if limits.resolution.deadline.is_none() {
        return Err(BvExprExportError::ResourceLimit {
            resource: "absolute proof deadline",
            limit: 1,
            actual: 0,
        });
    }
    let mut preflight = BvExprPreflight::default();
    let lhs_width =
        preflight_bv_expr_with_cancellation(lhs, limits, &mut preflight, 1, keep_going)?;
    let rhs_width =
        preflight_bv_expr_with_cancellation(rhs, limits, &mut preflight, 1, keep_going)?;
    require_bv_expr_width_match(lhs_width, rhs_width)?;
    preflight.top_width = lhs_width as usize;
    charge_bv_expr_resource(
        "estimated bit-blast gates",
        &mut preflight.estimated_gate_work,
        preflight.top_width,
        limits.max_estimated_gate_work,
    )?;
    Ok(preflight)
}

fn export_bv_blast_proof_expr_impl(
    lhs: &BvExpr,
    rhs: &BvExpr,
    bounded: Option<(&BvExprProofLimits, BvExprPreflight)>,
    keep_going: &mut dyn FnMut() -> bool,
) -> Result<BvBlastProof, BvExprExportError> {
    let limits = bounded.as_ref().map(|(limits, _)| *limits);
    build_bv_expr_refutation(lhs, rhs, bounded, keep_going)?.expand(limits, keep_going)
}

fn build_bv_expr_refutation(
    lhs: &BvExpr,
    rhs: &BvExpr,
    bounded: Option<(&BvExprProofLimits, BvExprPreflight)>,
    keep_going: &mut dyn FnMut() -> bool,
) -> Result<compact::ExprRefutation, BvExprExportError> {
    build_bv_expr_refutation_reporting(lhs, rhs, bounded, keep_going).map(|(proof, _)| proof)
}

// The optional count is ONLY the bounded producer's independent DAG replay;
// it does not count SAT search or construction. Unbounded compatibility calls
// return None, as does a sweep whose local validation work is not reported.
// Neither can stand in for a measured zero-work validation.
fn build_bv_expr_refutation_reporting(
    lhs: &BvExpr,
    rhs: &BvExpr,
    bounded: Option<(&BvExprProofLimits, BvExprPreflight)>,
    keep_going: &mut dyn FnMut() -> bool,
) -> Result<(compact::ExprRefutation, Option<u64>), BvExprExportError> {
    #[cfg(test)]
    retained::producer_test_counter::record();
    let limits = bounded.as_ref().map(|(limits, _)| *limits);
    let cnf = cnf::build(lhs, rhs, bounded, keep_going)?;

    // Hand the CNF to ay-sat and surface the actual refutation (never fabricated).
    let num_vars = cnf.vars.len();
    let sat_clauses: Vec<Vec<Literal>> = match limits {
        Some(limits) => {
            materialize_sat_clauses_with_cancellation(&cnf.clauses, &limits.resolution, keep_going)?
        }
        None => cnf
            .clauses
            .iter()
            .map(|clause| clause.lits.iter().map(lit_to_sat).collect())
            .collect(),
    };

    let (dag, validation_work) = if let Some(limits) = limits {
        // Preserve the counted sweep, but never mistake its unreported local
        // validation work for a measured zero. Metered capture refuses None.
        sweep::bounded_refutation(&cnf, &sat_clauses, limits, keep_going)?
    } else {
        match ay_sat::prove_unsat_resolution_dag(num_vars, &sat_clauses) {
            Ok(dag) => (dag, None),
            Err(ResolutionDagError::Satisfiable) => return Err(BvExprExportError::NoRefutation),
            Err(ResolutionDagError::Unknown) => return Err(BvExprExportError::SolverUnknown),
            Err(other) => {
                return Err(BvExprExportError::RefutationNotSurfaceable(
                    other.to_string(),
                ))
            }
        }
    };

    let proof = cnf.into_graph();
    // Release retained SAT/codec scratch before the final caller boundary.
    // Individual destructors remain opaque, but cannot run after admission.
    drop(sat_clauses);
    finish_expr_export(limits, keep_going)?;
    Ok((
        compact::ExprRefutation { graph: proof, dag },
        validation_work,
    ))
}

fn finish_expr_export(
    limits: Option<&BvExprProofLimits>,
    keep_going: &mut dyn FnMut() -> bool,
) -> Result<(), BvExprExportError> {
    check_expr_export_deadline(limits)?;
    poll_export(keep_going)?;
    // An accepting callback may itself consume the remaining wall budget.
    check_expr_export_deadline(limits)
}

fn check_expr_export_deadline(limits: Option<&BvExprProofLimits>) -> Result<(), BvExprExportError> {
    if limits.is_some_and(|limits| {
        limits
            .resolution
            .deadline
            .is_some_and(|deadline| Instant::now() >= deadline)
    }) {
        return Err(BvExprExportError::ResourceLimit {
            resource: "proof export deadline",
            limit: 0,
            actual: 1,
        });
    }
    Ok(())
}

fn bounded_amount(value: u128) -> usize {
    usize::try_from(value).unwrap_or(usize::MAX)
}

fn resolution_resource_name(resource: ResolutionProofResource) -> &'static str {
    match resource {
        ResolutionProofResource::Variables => "resolution variables",
        ResolutionProofResource::InputClauses => "resolution input clauses",
        ResolutionProofResource::InputLiterals => "resolution input literals",
        ResolutionProofResource::InputClauseLiterals => "resolution input clause literals",
        ResolutionProofResource::InputBytes => "resolution input bytes",
        ResolutionProofResource::ProofOutputBytes => "resolution proof output bytes",
        ResolutionProofResource::DerivedSteps => "resolution derived steps",
        ResolutionProofResource::DerivedLiterals => "resolution derived literals",
        ResolutionProofResource::Hints => "resolution hints",
        ResolutionProofResource::PendingDeletions => "resolution pending deletions",
        ResolutionProofResource::CodecBytes => "resolution codec bytes",
        ResolutionProofResource::BackwardReconstructionBytes => {
            "resolution backward reconstruction bytes"
        }
        ResolutionProofResource::Conflicts => "resolution conflicts",
        ResolutionProofResource::Decisions => "resolution decisions",
    }
}

fn validation_resource_name(resource: ResolutionValidationResource) -> &'static str {
    match resource {
        ResolutionValidationResource::OriginalClauses => "resolution replay original clauses",
        ResolutionValidationResource::OriginalLiterals => "resolution replay original literals",
        ResolutionValidationResource::DerivedSteps => "resolution replay derived steps",
        ResolutionValidationResource::DerivedLiterals => "resolution replay derived literals",
        ResolutionValidationResource::Hints => "resolution replay hints",
        ResolutionValidationResource::Work => "resolution replay work",
        ResolutionValidationResource::Bytes => "resolution replay bytes",
        ResolutionValidationResource::ClauseDatabase => "resolution replay clause database",
        ResolutionValidationResource::AssignmentScratch => "resolution replay assignment scratch",
    }
}

fn resolution_resource_limit(
    limits: &ResolutionProofLimits,
    resource: ResolutionProofResource,
) -> usize {
    match resource {
        ResolutionProofResource::Variables => limits.max_num_vars,
        ResolutionProofResource::InputClauses => limits.max_input_clauses,
        ResolutionProofResource::InputLiterals => limits.max_input_literals,
        ResolutionProofResource::InputClauseLiterals => limits.max_input_clause_literals,
        ResolutionProofResource::InputBytes => limits.max_input_bytes,
        ResolutionProofResource::ProofOutputBytes => limits.max_proof_output_bytes,
        ResolutionProofResource::DerivedSteps => limits.max_derived_steps,
        ResolutionProofResource::DerivedLiterals => limits.max_derived_literals,
        ResolutionProofResource::Hints => limits.max_hints,
        ResolutionProofResource::PendingDeletions => limits.max_pending_deletions,
        ResolutionProofResource::CodecBytes => limits.max_codec_bytes,
        ResolutionProofResource::BackwardReconstructionBytes => {
            limits.max_backward_reconstruction_bytes
        }
        ResolutionProofResource::Conflicts => limits
            .max_conflicts
            .and_then(|limit| usize::try_from(limit).ok())
            .unwrap_or(usize::MAX),
        ResolutionProofResource::Decisions => limits
            .max_decisions
            .and_then(|limit| usize::try_from(limit).ok())
            .unwrap_or(usize::MAX),
    }
}

fn validation_resource_limit(
    limits: &ResolutionProofLimits,
    resource: ResolutionValidationResource,
) -> usize {
    match resource {
        ResolutionValidationResource::OriginalClauses => limits.validation.max_original_clauses,
        ResolutionValidationResource::OriginalLiterals => limits.validation.max_original_literals,
        ResolutionValidationResource::DerivedSteps => limits.validation.max_derived_steps,
        ResolutionValidationResource::DerivedLiterals => limits.validation.max_derived_literals,
        ResolutionValidationResource::Hints => limits.validation.max_hints,
        ResolutionValidationResource::Work => {
            usize::try_from(limits.validation.max_work).unwrap_or(usize::MAX)
        }
        ResolutionValidationResource::Bytes
        | ResolutionValidationResource::ClauseDatabase
        | ResolutionValidationResource::AssignmentScratch => limits.validation.max_bytes,
    }
}

fn resource_failure(resource: &'static str, limit: usize, overflow: bool) -> BvExprExportError {
    // For allocation failure, `limit + 1` is a stable exhaustion sentinel; it
    // does not claim the allocator reached the configured logical byte cap.
    // Nor is it the input's verdict, so no memo may keep it.
    if !overflow {
        note_uncounted_failure();
    }
    BvExprExportError::ResourceLimit {
        resource,
        limit,
        actual: if overflow {
            usize::MAX
        } else {
            limit.saturating_add(1)
        },
    }
}

fn map_bounded_resolution_error(
    error: ResolutionProofError,
    limits: &ResolutionProofLimits,
) -> BvExprExportError {
    match error {
        ResolutionProofError::Cancelled => BvExprExportError::Cancelled,
        ResolutionProofError::Satisfiable => BvExprExportError::NoRefutation,
        ResolutionProofError::SolverUnknown {
            reason: Some(SatUnknownReason::DeadlineExceeded),
        } => BvExprExportError::ResourceLimit {
            resource: "resolution proof deadline",
            limit: 0,
            actual: 1,
        },
        ResolutionProofError::SolverUnknown {
            reason: Some(SatUnknownReason::ResourceBudget),
        } => BvExprExportError::ResourceLimit {
            resource: "resolution solver resource budget",
            // The fallback reason does not identify conflict vs decision cap;
            // exact counter exhaustion normally arrives as `LimitExceeded`.
            limit: 0,
            actual: 1,
        },
        ResolutionProofError::SolverUnknown { .. } => BvExprExportError::SolverUnknown,
        ResolutionProofError::UnboundedSearch => BvExprExportError::ResourceLimit {
            resource: "absolute proof deadline",
            limit: 1,
            actual: 0,
        },
        ResolutionProofError::DeadlineExceeded { .. } => BvExprExportError::ResourceLimit {
            resource: "resolution proof deadline",
            limit: 0,
            actual: 1,
        },
        ResolutionProofError::LimitExceeded {
            resource,
            limit,
            actual,
        } => BvExprExportError::ResourceLimit {
            resource: resolution_resource_name(resource),
            limit: bounded_amount(limit),
            actual: bounded_amount(actual),
        },
        ResolutionProofError::Validation(validation) => match validation {
            ResolutionValidationError::LimitExceeded {
                resource,
                limit,
                actual,
            } => BvExprExportError::ResourceLimit {
                resource: validation_resource_name(resource),
                limit: bounded_amount(limit),
                actual: bounded_amount(actual),
            },
            ResolutionValidationError::DeadlineExceeded => BvExprExportError::ResourceLimit {
                resource: "resolution proof deadline",
                limit: 0,
                actual: 1,
            },
            ResolutionValidationError::AccountingOverflow { resource } => resource_failure(
                validation_resource_name(resource),
                validation_resource_limit(limits, resource),
                true,
            ),
            ResolutionValidationError::AllocationFailed { resource } => resource_failure(
                validation_resource_name(resource),
                validation_resource_limit(limits, resource),
                false,
            ),
            ResolutionValidationError::Cancelled => BvExprExportError::Cancelled,
            invalid @ ResolutionValidationError::Invalid(_) => bounded_resolution_failure(invalid),
        },
        ResolutionProofError::AccountingOverflow { resource } => resource_failure(
            resolution_resource_name(resource),
            resolution_resource_limit(limits, resource),
            true,
        ),
        ResolutionProofError::AllocationFailed { resource } => resource_failure(
            resolution_resource_name(resource),
            resolution_resource_limit(limits, resource),
            false,
        ),
        failure @ ResolutionProofError::InputLiteralOutOfRange { .. }
        | failure @ ResolutionProofError::DuplicateInputLiteral { .. }
        | failure @ ResolutionProofError::ProofWriterUnavailable
        | failure @ ResolutionProofError::MalformedBinaryProof { .. }
        | failure @ ResolutionProofError::RatStepUnsupported
        | failure @ ResolutionProofError::NoEmptyClause
        | failure @ ResolutionProofError::OriginalClauseMismatch { .. } => {
            bounded_resolution_failure(failure)
        }
    }
}

fn bounded_resolution_failure(error: impl std::fmt::Display) -> BvExprExportError {
    BvExprExportError::RefutationNotSurfaceable(format!("bounded resolution proof failed: {error}"))
}

#[cfg(test)]
#[path = "bv_blast_solver_tests.rs"]
mod tests;

#[cfg(test)]
#[path = "bv_blast_solver_resource_tests.rs"]
mod resource_tests;
