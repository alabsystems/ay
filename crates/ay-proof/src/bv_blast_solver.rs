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
    blast_shift, build_gate, push_gate_cnf, BitLemma, BitLemmaKind, BvBlastProof, BvOp, Clause,
    ClauseProvenance, GateCache, Lit, OperandRef, Refutation, ResRule, ResolutionStep,
    SliceObligation, VarRole, VarTable, FORMAT_VERSION,
};
use ay_core::time::Instant;
use ay_sat::{
    Literal, ResolutionDag, ResolutionDagError, ResolutionProofError, ResolutionProofLimits,
    RupStep, Variable,
};
use std::collections::BTreeSet;

/// Errors from [`export_bv_blast_proof_solved`].
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum BvSolvedExportError {
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
    /// Bounded RUP expansion exhausted its explicit step/deadline envelope.
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

/// Expand the solver's RUP DAG into a [`Refutation`] of binary resolutions.
///
/// Premise-id namespace (matching [`BvBlastProof::validate`]): ids `0..nclauses`
/// name input clauses; ids `>= nclauses` name resolution steps, in order. We map
/// each LRAT id (originals `1..=nclauses`, derived `> nclauses`) onto that space.
fn expand_dag_to_resolution(
    dag: &ResolutionDag,
    clauses: &[Clause],
    limits: Option<RupExpansionLimits>,
) -> Result<Refutation, BvSolvedExportError> {
    let nclauses = clauses.len() as u32;

    // LRAT id → BvBlast premise id (the id usable as a ResolutionStep premise).
    // Originals: LRAT id `k` (1-based) → clause index `k-1`.
    // Derived: filled in as we emit the *final* step that produces each derived
    // clause (the last pairwise step of its RUP expansion).
    let mut lrat_to_premise: std::collections::HashMap<u64, u32> = std::collections::HashMap::new();
    for (lrat_id, _lits) in &dag.original_clauses {
        lrat_to_premise.insert(*lrat_id, (*lrat_id - 1) as u32);
    }
    // Original clause literals by LRAT id, for RUP replay.
    let mut lits_by_lrat: std::collections::HashMap<u64, Vec<Lit>> =
        std::collections::HashMap::new();
    for (lrat_id, lits) in &dag.original_clauses {
        lits_by_lrat.insert(*lrat_id, lits.iter().map(lit_from_sat).collect());
    }

    let mut state = RupExpansionState {
        steps: Vec::new(),
        next_step_id: nclauses,
        work: 0,
    };

    for rup in &dag.derived {
        check_rup_expansion_budget(limits, state.steps.len(), state.work)?;
        let target: Vec<Lit> = rup.clause.iter().map(lit_from_sat).collect();
        let final_premise_id = expand_one_rup_step(
            rup,
            &target,
            &lits_by_lrat,
            &lrat_to_premise,
            &mut state,
            limits,
        )?;
        // Register this derived clause so later steps can cite it.
        lrat_to_premise.insert(rup.id, final_premise_id);
        lits_by_lrat.insert(rup.id, target);
    }

    Ok(Refutation { steps: state.steps })
}

/// Mutable output and accounting shared by each RUP expansion.
struct RupExpansionState {
    steps: Vec<ResolutionStep>,
    next_step_id: u32,
    work: usize,
}

fn check_rup_expansion_budget(
    limits: Option<RupExpansionLimits>,
    steps: usize,
    work: usize,
) -> Result<(), BvSolvedExportError> {
    let Some(limits) = limits else {
        return Ok(());
    };
    if steps > limits.max_steps {
        return Err(BvSolvedExportError::ResourceLimit {
            resource: "expanded resolution steps",
            limit: limits.max_steps,
            actual: steps,
        });
    }
    if work & 1_023 == 0 && Instant::now() >= limits.deadline {
        return Err(BvSolvedExportError::ResourceLimit {
            resource: "RUP expansion deadline",
            limit: 0,
            actual: 1,
        });
    }
    Ok(())
}

/// Expand a single RUP step into binary resolutions and return the BvBlast
/// premise-id of the step that yields (a clause set-equal to) `target`.
///
/// Algorithm (standard RUP → resolution by reverse propagation):
///  1. Replay RUP: assume `¬target`, walk `rup_hints` in order; each hint is
///     unit and propagates one literal, the last hint conflicts. Record, per
///     hint, the unit literal it propagated.
///  2. Walk the *used* hints in reverse, starting from the conflicting clause,
///     resolving on each recorded unit literal whenever the running resolvent
///     contains its negation. Each resolution is one emitted [`ResolutionStep`].
fn expand_one_rup_step(
    rup: &RupStep,
    target: &[Lit],
    lits_by_lrat: &std::collections::HashMap<u64, Vec<Lit>>,
    lrat_to_premise: &std::collections::HashMap<u64, u32>,
    state: &mut RupExpansionState,
    limits: Option<RupExpansionLimits>,
) -> Result<u32, BvSolvedExportError> {
    // ── 1. RUP replay to discover per-hint unit literals. ──
    // Trail value: var → assigned bool. Assume ¬target.
    let mut assign: std::collections::HashMap<u32, bool> = std::collections::HashMap::new();
    for l in target {
        // ¬l is forced true under the assumption.
        assign.insert(l.var, l.neg); // if l = +v then ¬l forces v=false; if l=¬v forces v=true
    }
    // For each hint, the unit literal it adds (None for the final conflict).
    let mut hint_units: Vec<Option<Lit>> = Vec::with_capacity(rup.rup_hints.len());
    let mut conflict_at: Option<usize> = None;
    for (i, &h) in rup.rup_hints.iter().enumerate() {
        state.work = state.work.saturating_add(1);
        check_rup_expansion_budget(limits, state.steps.len(), state.work)?;
        let clause = lits_by_lrat
            .get(&h)
            .ok_or(BvSolvedExportError::RupExpansionFailed { id: rup.id })?;
        let mut unassigned: Vec<Lit> = Vec::new();
        let mut satisfied = false;
        for &lit in clause {
            match assign.get(&lit.var) {
                Some(&val) => {
                    // literal true iff (val == !lit.neg) i.e. var assigned to lit's polarity
                    let lit_true = val != lit.neg;
                    if lit_true {
                        satisfied = true;
                        break;
                    }
                    // else falsified, skip
                }
                None => unassigned.push(lit),
            }
        }
        if satisfied {
            // Already-true hint: contributes nothing; record as no-op.
            hint_units.push(None);
            continue;
        }
        match unassigned.len() {
            0 => {
                // Conflict: all literals falsified.
                hint_units.push(None);
                conflict_at = Some(i);
                break;
            }
            1 => {
                let u = unassigned[0];
                // propagate: assign var so that u becomes true.
                assign.insert(u.var, !u.neg);
                hint_units.push(Some(u));
            }
            _ => {
                // Non-unit hint under RUP: the proof is not a clean unit chain.
                return Err(BvSolvedExportError::RupExpansionFailed { id: rup.id });
            }
        }
    }
    let conflict_idx = conflict_at.ok_or(BvSolvedExportError::RupExpansionFailed { id: rup.id })?;

    // ── 2. Reverse-resolve from the conflicting clause. ──
    let conflict_hint = rup.rup_hints[conflict_idx];
    let mut resolvent: Vec<Lit> = lits_by_lrat
        .get(&conflict_hint)
        .ok_or(BvSolvedExportError::RupExpansionFailed { id: rup.id })?
        .clone();
    let mut last_premise: u32 = *lrat_to_premise
        .get(&conflict_hint)
        .ok_or(BvSolvedExportError::RupExpansionFailed { id: rup.id })?;

    // Walk hints before the conflict, in reverse, resolving on their unit vars.
    for j in (0..conflict_idx).rev() {
        state.work = state.work.saturating_add(1);
        check_rup_expansion_budget(limits, state.steps.len(), state.work)?;
        let Some(unit) = hint_units[j] else {
            continue; // no-op / satisfied hint contributes nothing
        };
        // Resolve only if the resolvent currently contains ¬unit (the pivot).
        if !resolvent.contains(&unit.negated()) {
            continue;
        }
        let hint_id = rup.rup_hints[j];
        let hint_clause = lits_by_lrat
            .get(&hint_id)
            .ok_or(BvSolvedExportError::RupExpansionFailed { id: rup.id })?;
        let pivot = unit.var;
        let new_resolvent = resolve_pair(&resolvent, hint_clause, pivot)
            .ok_or(BvSolvedExportError::RupExpansionFailed { id: rup.id })?;
        let hint_premise = *lrat_to_premise
            .get(&hint_id)
            .ok_or(BvSolvedExportError::RupExpansionFailed { id: rup.id })?;
        if limits.is_some_and(|limits| state.steps.len() >= limits.max_steps) {
            return Err(BvSolvedExportError::ResourceLimit {
                resource: "expanded resolution steps",
                limit: limits.map_or(0, |limits| limits.max_steps),
                actual: state.steps.len().saturating_add(1),
            });
        }
        let step_id = state.next_step_id;
        state.next_step_id =
            state
                .next_step_id
                .checked_add(1)
                .ok_or(BvSolvedExportError::ResourceLimit {
                    resource: "resolution step id space",
                    limit: u32::MAX as usize,
                    actual: usize::MAX,
                })?;
        state.steps.push(ResolutionStep {
            id: step_id,
            clause: new_resolvent.clone(),
            rule: ResRule::Resolution,
            premises: [last_premise, hint_premise],
            pivot,
        });
        resolvent = new_resolvent;
        last_premise = step_id;
    }

    // The reverse-resolution resolvent must be set-equal to the target clause.
    if !clause_set_eq(&resolvent, target) {
        return Err(BvSolvedExportError::RupExpansionFailed { id: rup.id });
    }

    // If the RUP chain produced the target in zero resolutions (a single
    // conflicting clause that already equals the target — e.g. a unit derived
    // directly), `last_premise` already names a clause set-equal to target, but
    // it may be an *original clause* id rather than a fresh step. The downstream
    // validator needs the derived clause to be citable; if no step was emitted,
    // emit a trivial identity is impossible (resolution needs two premises), so
    // require at least one resolution. For our bit-blast obligations every
    // derived clause needs >= 1 resolution, so this is satisfied; guard anyway.
    Ok(last_premise)
}

/// Binary resolution of `a` and `b` on `pivot`, deduplicated; `None` if `pivot`
/// is not a clean opposite-polarity pivot or the resolvent is tautological.
fn resolve_pair(a: &[Lit], b: &[Lit], pivot: u32) -> Option<Vec<Lit>> {
    let a_pos = a.contains(&Lit::pos(pivot));
    let a_neg = a.contains(&Lit::neg(pivot));
    let b_pos = b.contains(&Lit::pos(pivot));
    let b_neg = b.contains(&Lit::neg(pivot));
    let valid = (a_pos && b_neg && !a_neg && !b_pos) || (a_neg && b_pos && !a_pos && !b_neg);
    if !valid {
        return None;
    }
    let mut out: Vec<Lit> = Vec::new();
    let mut seen: BTreeSet<Lit> = BTreeSet::new();
    for &l in a.iter().chain(b.iter()) {
        if l.var == pivot {
            continue;
        }
        if seen.contains(&l.negated()) {
            return None; // tautology
        }
        if seen.insert(l) {
            out.push(l);
        }
    }
    Some(out)
}

fn clause_set_eq(a: &[Lit], b: &[Lit]) -> bool {
    let sa: BTreeSet<Lit> = a.iter().copied().collect();
    let sb: BTreeSet<Lit> = b.iter().copied().collect();
    sa == sb
}

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
            .collect();
    }

    // Arithmetic ripple-carry (Add / Sub): Sub complements `y` and carries in 1.
    let (op2_bits, cin): (Vec<u32>, u32) = if matches!(op, BvOp::Sub) {
        let noty: Vec<u32> = y_bits
            .iter()
            .enumerate()
            .map(|(bit, &y)| {
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
            .collect();
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
        (y_bits.to_vec(), f)
    };

    let mut out = Vec::with_capacity(n);
    let mut carry = cin;
    for bit in 0..n {
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
    out
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
}

// The `add`/`sub`/`mul`/`shl`/`not` constructors are named after the SMT-LIB
// bitvector operators they build (bvadd, bvsub, ...); they take two operands
// and return a `BvExpr` node, so they cannot and should not implement the
// same-named `std::ops` traits.
#[allow(clippy::should_implement_trait)]
impl BvExpr {
    /// Convenience: a named leaf.
    #[must_use]
    pub fn leaf(name: &str, width: u32) -> Self {
        Self::Leaf {
            name: name.to_string(),
            width,
        }
    }
    /// Convenience: `bvadd(lhs, rhs)`. Restored after the workspace-quality
    /// audit removed it as workspace-unused: downstream consumers (proof-replay-consumer's
    /// pcay reconstruction, trust-router's ay_certify, external-codegen-bridge's
    /// verify_output) construct these shapes at many call sites — the boxed
    /// variant spelling is an implementation detail, not the API.
    #[must_use]
    pub fn add(lhs: BvExpr, rhs: BvExpr) -> Self {
        Self::Add(Box::new(lhs), Box::new(rhs))
    }
    /// Convenience: `bvsub(lhs, rhs)`.
    #[must_use]
    pub fn sub(lhs: BvExpr, rhs: BvExpr) -> Self {
        Self::Sub(Box::new(lhs), Box::new(rhs))
    }
    /// Convenience: `bvmul(lhs, rhs)`.
    #[must_use]
    pub fn mul(lhs: BvExpr, rhs: BvExpr) -> Self {
        Self::Mul(Box::new(lhs), Box::new(rhs))
    }
    /// Convenience: `bvshl(value, amount)`.
    #[must_use]
    pub fn shl(value: BvExpr, amount: BvExpr) -> Self {
        Self::Shl(Box::new(value), Box::new(amount))
    }
    /// Convenience: `bvnot(inner)`.
    #[must_use]
    pub fn not(inner: BvExpr) -> Self {
        Self::Not(Box::new(inner))
    }
    /// Convenience: `(_ zero_extend added)`.
    #[must_use]
    pub fn zero_ext(inner: BvExpr, added: u32) -> Self {
        Self::ZeroExt(Box::new(inner), added)
    }
    /// Convenience: `(_ extract high low)`.
    #[must_use]
    pub fn extract(inner: BvExpr, high: u32, low: u32) -> Self {
        Self::Extract {
            inner: Box::new(inner),
            high,
            low,
        }
    }
    /// Convenience: `bvor`.
    #[must_use]
    pub fn or(l: BvExpr, r: BvExpr) -> Self {
        Self::Or(Box::new(l), Box::new(r))
    }
    /// Convenience: `bvand`.
    #[must_use]
    pub fn and(l: BvExpr, r: BvExpr) -> Self {
        Self::And(Box::new(l), Box::new(r))
    }
    /// Convenience: `bvxor`.
    #[must_use]
    pub fn xor(l: BvExpr, r: BvExpr) -> Self {
        Self::Xor(Box::new(l), Box::new(r))
    }
    /// Convenience: a fixed bit-vector constant of the given width.
    #[must_use]
    pub fn const_val(value: u128, width: u32) -> Self {
        Self::Const { value, width }
    }
    /// Convenience: `(_ sign_extend added)`.
    #[must_use]
    pub fn sign_ext(inner: BvExpr, added: u32) -> Self {
        Self::SignExt(Box::new(inner), added)
    }
    /// Convenience: `bvlshr`.
    #[must_use]
    pub fn lshr(value: BvExpr, amount: BvExpr) -> Self {
        Self::Lshr(Box::new(value), Box::new(amount))
    }
    /// Convenience: `bvashr`.
    #[must_use]
    pub fn ashr(value: BvExpr, amount: BvExpr) -> Self {
        Self::Ashr(Box::new(value), Box::new(amount))
    }
    /// Convenience: bit-vector equality (`= lhs rhs`) reduced to a 1-bit predicate.
    #[must_use]
    pub fn eq(lhs: BvExpr, rhs: BvExpr) -> Self {
        Self::Eq(Box::new(lhs), Box::new(rhs))
    }
    /// Convenience: carry-out of the ripple-carry add (`is_sub == false`).
    #[must_use]
    pub fn carry_out_add(lhs: BvExpr, rhs: BvExpr) -> Self {
        Self::CarryOut {
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
            is_sub: false,
        }
    }
    /// Convenience: carry-out of the ripple-carry subtract (`a + ~b + 1`).
    /// `unsigned_lt(a, b) = NOT(carry_out_sub(a, b))`.
    #[must_use]
    pub fn carry_out_sub(lhs: BvExpr, rhs: BvExpr) -> Self {
        Self::CarryOut {
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
            is_sub: true,
        }
    }
}

/// Convenience: `bvadd` (also callable as `BvExpr::add(l, r)`).
impl std::ops::Add for BvExpr {
    type Output = Self;
    fn add(self, rhs: Self) -> Self {
        Self::Add(Box::new(self), Box::new(rhs))
    }
}

/// Convenience: `bvsub` (also callable as `BvExpr::sub(l, r)`).
impl std::ops::Sub for BvExpr {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self {
        Self::Sub(Box::new(self), Box::new(rhs))
    }
}

/// Convenience: `bvmul` (also callable as `BvExpr::mul(l, r)`).
impl std::ops::Mul for BvExpr {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self {
        Self::Mul(Box::new(self), Box::new(rhs))
    }
}

/// Convenience: `bvshl` (also callable as `BvExpr::shl(value, amount)`).
impl std::ops::Shl for BvExpr {
    type Output = Self;
    fn shl(self, amount: Self) -> Self {
        Self::Shl(Box::new(self), Box::new(amount))
    }
}

/// Convenience: `bvnot`, per-bit NOT (also callable as `BvExpr::not(inner)`).
impl std::ops::Not for BvExpr {
    type Output = Self;
    fn not(self) -> Self {
        Self::Not(Box::new(self))
    }
}

/// Errors from [`export_bv_blast_proof_expr`].
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum BvExprExportError {
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

/// Explicit bounds for proof-producing [`BvExpr`] validation.
///
/// The expression preflight runs before CNF allocation. The nested resolution
/// limits then bound SAT search, LRAT output/materialization, and independent
/// replay. Callers must provide an absolute deadline in `resolution`.
#[derive(Clone, Debug)]
pub(crate) struct BvExprProofLimits {
    pub(crate) max_expr_nodes: usize,
    pub(crate) max_expr_depth: usize,
    /// Maximum width of any internal expression node. This may exceed the
    /// serialized proof's top-level equality width when a source-bound Bool
    /// query contains wide bit-vector terms.
    pub(crate) max_internal_width: u32,
    pub(crate) max_estimated_gate_work: usize,
    pub(crate) max_resolution_steps: usize,
    pub(crate) resolution: ResolutionProofLimits,
}

/// Scratch state shared across the bit-blast of BOTH sides of the equality: one
/// gate cache (so common sub-terms fuse) and an interning table mapping each named
/// leaf to its (allocated-once) input bit vars.
struct ExprBlaster {
    cache: GateCache,
    /// Leaf name → input bit vars (LSB-first). First-seen order also assigns the
    /// `InputLeaf { leaf }` index.
    leaves: std::collections::HashMap<String, Vec<u32>>,
    /// Leaf names in first-seen order (index = the `leaf` field of `InputLeaf`).
    leaf_order: Vec<String>,
    /// A cached `ConstFalse` zero bit (used by zero-extend / `Const` 0 bits), built once.
    zero_bit: Option<u32>,
    /// A cached `ConstTrue` one bit (used by `Const` 1 bits), built once.
    one_bit: Option<u32>,
}

impl ExprBlaster {
    fn new() -> Self {
        Self {
            cache: GateCache::default(),
            leaves: std::collections::HashMap::new(),
            leaf_order: Vec::new(),
            zero_bit: None,
            one_bit: None,
        }
    }

    /// Get (or allocate, first-seen) the input bit vars for a named leaf.
    fn leaf_bits(&mut self, name: &str, width: u32, vars: &mut VarTable) -> Vec<u32> {
        if let Some(bits) = self.leaves.get(name) {
            return bits.clone();
        }
        let leaf_idx = self.leaf_order.len() as u32;
        self.leaf_order.push(name.to_string());
        let bits: Vec<u32> = (0..width)
            .map(|bit| {
                vars.alloc(VarRole::InputLeaf {
                    leaf: leaf_idx,
                    bit,
                })
            })
            .collect();
        self.leaves.insert(name.to_string(), bits.clone());
        bits
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

    /// Bit-blast `expr` into its output bit vars (LSB-first). Gates flow through the
    /// shared cache, so structurally-identical sub-terms (even across the two sides
    /// of the equality) reuse one set of output vars.
    fn blast(
        &mut self,
        expr: &BvExpr,
        vars: &mut VarTable,
        bit_lemmas: &mut Vec<BitLemma>,
        clauses: &mut Vec<Clause>,
    ) -> Result<Vec<u32>, BvExprExportError> {
        match expr {
            BvExpr::Leaf { name, width } => {
                if *width == 0 {
                    return Err(BvExprExportError::Malformed(format!(
                        "leaf {name:?} has width 0"
                    )));
                }
                Ok(self.leaf_bits(name, *width, vars))
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
                let out = blast_side_roles(
                    op,
                    &lb,
                    &rb,
                    Side::Lhs,
                    vars,
                    bit_lemmas,
                    clauses,
                    &mut scratch,
                );
                self.cache = scratch.cache;
                Ok(out)
            }
            BvExpr::ZeroExt(inner, added) => {
                let mut bits = self.blast(inner, vars, bit_lemmas, clauses)?;
                let z = self.zero(vars, bit_lemmas, clauses);
                bits.extend(std::iter::repeat_n(z, *added as usize));
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
                Ok(bits[(*low as usize)..=(*high as usize)].to_vec())
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
                // Per-bit bitwise gate, NO carry chain — the same gate-fidelity the
                // operand-swap path's `BvOp::{Or,And,Xor}` uses. Built through THIS
                // blaster's shared cache, so an identity wrapper `Or(Const{0}, x)`
                // whose RHS sub-tree also appears bare on the other side of the
                // equality fuses its inputs, and `Or(0, x)` collapses to the same
                // output bits as a bare `x` only insofar as the solver proves it (no
                // structural shortcut: each per-bit gate is a real gate the solver
                // reasons about).
                let kind = match expr {
                    BvExpr::Or(..) => BitLemmaKind::Or2,
                    BvExpr::And(..) => BitLemmaKind::And2,
                    // The match guard restricts this arm to {Or, And, Xor}.
                    _ => BitLemmaKind::Xor2,
                };
                Ok((0..lb.len())
                    .map(|bit| {
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
                    .collect())
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
                        let set = (*value >> bit) & 1 == 1;
                        if set {
                            self.one(vars, bit_lemmas, clauses)
                        } else {
                            self.zero(vars, bit_lemmas, clauses)
                        }
                    })
                    .collect())
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
                out.extend(std::iter::repeat_n(sign, *added as usize));
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
                // Reuse the operand-swap path's barrel-shifter blaster, but through
                // THIS blaster's shared cache (so structurally-identical shifts on
                // the two sides of the equality fuse to one set of output vars).
                // Every gate `blast_shift` emits is an existing `BitLemmaKind`.
                Ok(blast_shift(
                    op,
                    &vb,
                    &ab,
                    vars,
                    bit_lemmas,
                    clauses,
                    &mut self.cache,
                ))
            }
            BvExpr::Not(inner) => {
                // Per-bit NOT: one existing `Not` gate per bit (same gate the
                // subtraction's one's-complement uses). NO new kernel gate KIND.
                let bits = self.blast(inner, vars, bit_lemmas, clauses)?;
                Ok(bits
                    .into_iter()
                    .map(|b| {
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
                    .collect())
            }
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
                    .collect();
                // AND-reduce the per-bit equalities into one predicate bit.
                let mut acc = bit_eqs[0];
                for &e in &bit_eqs[1..] {
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
                        .collect();
                    let t = self.one(vars, bit_lemmas, clauses);
                    (notb, t)
                } else {
                    let f = self.zero(vars, bit_lemmas, clauses);
                    (bb, f)
                };
                // Ripple the carry through ALL n bits (the MSB carry is the result).
                let mut carry = cin;
                for bit in 0..n {
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
                    .collect();

                // Add each remaining shifted partial-product row into `acc`.
                for (j, &b_j) in bb.iter().enumerate().take(n).skip(1) {
                    // Row j shifted left by `j`: positions 0..j are zero, then
                    // pp[i] = a[i] ∧ b[j] occupies position `i + j`. Build only the
                    // positions that land within the retained low `n` bits.
                    let row: Vec<u32> = (0..n)
                        .map(|pos| {
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
                        .collect();

                    // Ripple-carry add `row` into `acc` (truncated to `n` bits,
                    // carry-out of the MSB discarded). Same `Xor3`/`FullAdderCarry`
                    // gates the `Add` path uses.
                    let mut carry = zero;
                    let mut next = Vec::with_capacity(n);
                    for bit in 0..n {
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
    nodes: usize,
    estimated_gate_work: usize,
}

fn preflight_bv_expr(
    expr: &BvExpr,
    limits: &BvExprProofLimits,
    state: &mut BvExprPreflight,
    depth: usize,
) -> Result<u32, BvExprExportError> {
    if depth > limits.max_expr_depth {
        return Err(BvExprExportError::ResourceLimit {
            resource: "expression depth",
            limit: limits.max_expr_depth,
            actual: depth,
        });
    }
    charge_bv_expr_resource(
        "expression nodes",
        &mut state.nodes,
        1,
        limits.max_expr_nodes,
    )?;

    let mut child = |inner: &BvExpr| preflight_bv_expr(inner, limits, state, depth + 1);
    let (width, local_work) = match expr {
        BvExpr::Leaf { width, .. } | BvExpr::Const { width, .. } => {
            (*width, usize::try_from(*width).unwrap_or(usize::MAX))
        }
        BvExpr::ZeroExt(inner, added) | BvExpr::SignExt(inner, added) => {
            let inner_width = child(inner)?;
            let width = inner_width.checked_add(*added).ok_or_else(|| {
                BvExprExportError::Malformed("bit-vector extension width overflow".to_string())
            })?;
            (width, usize::try_from(width).unwrap_or(usize::MAX))
        }
        BvExpr::Extract { inner, high, low } => {
            let inner_width = child(inner)?;
            if low > high || *high >= inner_width {
                return Err(BvExprExportError::Malformed(format!(
                    "extract [{high}:{low}] out of bounds for {inner_width}-bit operand"
                )));
            }
            let width = high - low + 1;
            (width, usize::try_from(width).unwrap_or(usize::MAX))
        }
        BvExpr::Not(inner) => {
            let width = child(inner)?;
            (width, 2_usize.saturating_mul(width as usize))
        }
        BvExpr::Add(lhs, rhs) | BvExpr::Sub(lhs, rhs) => {
            let lhs_width = child(lhs)?;
            let rhs_width = child(rhs)?;
            require_bv_expr_width_match(lhs_width, rhs_width)?;
            (lhs_width, 8_usize.saturating_mul(lhs_width as usize))
        }
        BvExpr::Or(lhs, rhs) | BvExpr::And(lhs, rhs) | BvExpr::Xor(lhs, rhs) => {
            let lhs_width = child(lhs)?;
            let rhs_width = child(rhs)?;
            require_bv_expr_width_match(lhs_width, rhs_width)?;
            (lhs_width, 4_usize.saturating_mul(lhs_width as usize))
        }
        BvExpr::Eq(lhs, rhs) => {
            let lhs_width = child(lhs)?;
            let rhs_width = child(rhs)?;
            require_bv_expr_width_match(lhs_width, rhs_width)?;
            (1, 4_usize.saturating_mul(lhs_width as usize))
        }
        BvExpr::CarryOut { lhs, rhs, .. } => {
            let lhs_width = child(lhs)?;
            let rhs_width = child(rhs)?;
            require_bv_expr_width_match(lhs_width, rhs_width)?;
            (1, 8_usize.saturating_mul(lhs_width as usize))
        }
        BvExpr::Mul(lhs, rhs)
        | BvExpr::Shl(lhs, rhs)
        | BvExpr::Lshr(lhs, rhs)
        | BvExpr::Ashr(lhs, rhs) => {
            let lhs_width = child(lhs)?;
            let rhs_width = child(rhs)?;
            require_bv_expr_width_match(lhs_width, rhs_width)?;
            let width = lhs_width as usize;
            // Both the truncated array multiplier and variable barrel shifter
            // are O(width^2) in the supported range. The factor 16 strictly
            // dominates their current gate topologies and leaves headroom for
            // saturation/comparison gates without relying on cache sharing.
            let work = 16_usize.saturating_mul(width).saturating_mul(width);
            (lhs_width, work)
        }
    };

    if width == 0 || width > limits.max_internal_width {
        return Err(BvExprExportError::UnsupportedWidth {
            got: width,
            max: limits.max_internal_width,
        });
    }
    charge_bv_expr_resource(
        "estimated bit-blast gates",
        &mut state.estimated_gate_work,
        local_work,
        limits.max_estimated_gate_work,
    )?;
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
    export_bv_blast_proof_expr_impl(lhs, rhs, None)
}

/// Bounded sibling used by strict proof recognition. Unlike the compatibility
/// entry point above, this rejects oversized expression trees before CNF
/// allocation and routes proof search/materialization/replay through ay-sat's
/// explicit finite-limit API.
pub(crate) fn export_bv_blast_proof_expr_with_limits(
    lhs: &BvExpr,
    rhs: &BvExpr,
    limits: &BvExprProofLimits,
) -> Result<BvBlastProof, BvExprExportError> {
    if limits.resolution.deadline.is_none() {
        return Err(BvExprExportError::ResourceLimit {
            resource: "absolute proof deadline",
            limit: 1,
            actual: 0,
        });
    }
    let mut preflight = BvExprPreflight::default();
    let lhs_width = preflight_bv_expr(lhs, limits, &mut preflight, 1)?;
    let rhs_width = preflight_bv_expr(rhs, limits, &mut preflight, 1)?;
    require_bv_expr_width_match(lhs_width, rhs_width)?;
    export_bv_blast_proof_expr_impl(lhs, rhs, Some(limits))
}

fn export_bv_blast_proof_expr_impl(
    lhs: &BvExpr,
    rhs: &BvExpr,
    limits: Option<&BvExprProofLimits>,
) -> Result<BvBlastProof, BvExprExportError> {
    let mut vars = VarTable::default();
    let mut bit_lemmas: Vec<BitLemma> = Vec::new();
    let mut clauses: Vec<Clause> = Vec::new();

    let mut blaster = ExprBlaster::new();
    let lhs_bits = blaster.blast(lhs, &mut vars, &mut bit_lemmas, &mut clauses)?;
    let rhs_bits = blaster.blast(rhs, &mut vars, &mut bit_lemmas, &mut clauses)?;

    if lhs_bits.len() != rhs_bits.len() {
        return Err(BvExprExportError::WidthMismatch {
            lhs: lhs_bits.len() as u32,
            rhs: rhs_bits.len() as u32,
        });
    }
    let width = lhs_bits.len() as u32;
    if width == 0 || width > SOLVED_MAX_WIDTH {
        return Err(BvExprExportError::UnsupportedWidth {
            got: width,
            max: SOLVED_MAX_WIDTH,
        });
    }

    // Per-bit equality vars e_i = XnorEq(lhs_i, rhs_i) + Tseitin CNF.
    let mut eq_vars: Vec<u32> = Vec::with_capacity(width as usize);
    for (bit, (&l, &r)) in lhs_bits.iter().zip(rhs_bits.iter()).enumerate() {
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

    // Disequality clause from not(lhs == rhs): at least one bit differs.
    let diseq_id = clauses.len() as u32;
    clauses.push(Clause {
        id: diseq_id,
        lits: eq_vars.iter().map(|&e| Lit::neg(e)).collect(),
        provenance: ClauseProvenance::Disequality,
    });

    if let Some(limits) = limits {
        if bit_lemmas.len() > limits.max_estimated_gate_work {
            return Err(BvExprExportError::ResourceLimit {
                resource: "actual bit-blast gates",
                limit: limits.max_estimated_gate_work,
                actual: bit_lemmas.len(),
            });
        }
    }

    // Hand the CNF to ay-sat and surface the actual refutation (never fabricated).
    let num_vars = vars.len();
    let sat_clauses: Vec<Vec<Literal>> = clauses
        .iter()
        .map(|c| c.lits.iter().map(lit_to_sat).collect())
        .collect();

    let dag = if let Some(limits) = limits {
        match ay_sat::prove_unsat_resolution_dag_with_limits(
            num_vars,
            &sat_clauses,
            &limits.resolution,
        ) {
            Ok(dag) => dag,
            Err(ResolutionProofError::Satisfiable) => return Err(BvExprExportError::NoRefutation),
            Err(other) => {
                return Err(BvExprExportError::RefutationNotSurfaceable(format!(
                    "bounded resolution proof failed: {other}"
                )))
            }
        }
    } else {
        match ay_sat::prove_unsat_resolution_dag(num_vars, &sat_clauses) {
            Ok(dag) => dag,
            Err(ResolutionDagError::Satisfiable) => return Err(BvExprExportError::NoRefutation),
            Err(ResolutionDagError::Unknown) => return Err(BvExprExportError::SolverUnknown),
            Err(other) => {
                return Err(BvExprExportError::RefutationNotSurfaceable(
                    other.to_string(),
                ))
            }
        }
    };

    let expansion_limits = limits.map(|limits| RupExpansionLimits {
        max_steps: limits.max_resolution_steps,
        // The bounded entry point already rejects a missing deadline.
        deadline: limits
            .resolution
            .deadline
            .expect("bounded proof limits require an absolute deadline"),
    });
    let refutation = expand_dag_to_resolution(&dag, &clauses, expansion_limits).map_err(
        |error| match error {
            BvSolvedExportError::ResourceLimit {
                resource,
                limit,
                actual,
            } => BvExprExportError::ResourceLimit {
                resource,
                limit,
                actual,
            },
            other => BvExprExportError::RefutationNotSurfaceable(other.to_string()),
        },
    )?;
    if let Some(limits) = limits {
        if refutation.steps.len() > limits.max_resolution_steps {
            return Err(BvExprExportError::ResourceLimit {
                resource: "expanded resolution steps",
                limit: limits.max_resolution_steps,
                actual: refutation.steps.len(),
            });
        }
    }

    // Lineage record. The proof's soundness rests ENTIRELY on vars/lemmas/clauses/
    // refutation (all re-checked by `validate()` and the downstream proof consumer); the
    // `obligation` field is human/debug provenance only. We record a representative
    // `SliceObligation` (width + the leaf op) so the format stays unchanged — it is
    // NOT load-bearing and NOT consulted by `validate()`.
    let obligation_record = SliceObligation {
        width,
        op: BvOp::Add,
        lhs_args: [OperandRef::A, OperandRef::B],
        rhs_args: [OperandRef::A, OperandRef::B],
    };

    let proof = BvBlastProof {
        format_version: FORMAT_VERSION,
        obligation: obligation_record,
        asserted_smt: "(not (= <lhs-expr> <rhs-expr>))".to_string(),
        vars,
        bit_lemmas,
        clauses,
        refutation,
    };
    Ok(proof)
}

#[cfg(test)]
#[path = "bv_blast_solver_tests.rs"]
mod tests;
