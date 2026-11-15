// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The shared source-to-CNF encoder, separated from SAT proof search.
//! A CNF is not a certificate: callers must bind a refutation to these exact
//! ordered clauses and independently replay it before accepting an obligation.

use super::*;

/// Owned canonical encoding of `not(lhs == rhs)`, without any refutation.
/// Leaf identities are assigned by the live source traversal, not supplied IDs.
/// This is not a serialized source binding or an admission token.
#[derive(Debug, PartialEq, Eq)]
pub(crate) struct BvExprCnf {
    width: u32,
    pub(crate) vars: VarTable,
    pub(crate) bit_lemmas: Vec<BitLemma>,
    pub(crate) clauses: Vec<Clause>,
}

impl BvExprCnf {
    /// Reuse the legacy graph container only where a separate refutation will
    /// be supplied. Its empty refutation is deliberately not an UNSAT proof.
    pub(super) fn into_graph(self) -> BvBlastProof {
        BvBlastProof {
            format_version: FORMAT_VERSION,
            obligation: SliceObligation {
                width: self.width,
                op: BvOp::Add,
                lhs_args: [OperandRef::A, OperandRef::B],
                rhs_args: [OperandRef::A, OperandRef::B],
            },
            asserted_smt: "(not (= <lhs-expr> <rhs-expr>))".to_string(),
            vars: self.vars,
            bit_lemmas: self.bit_lemmas,
            clauses: self.clauses,
            refutation: Refutation::default(),
        }
    }

    /// The CNF [`Self::into_graph`] put into `graph`, given back.
    pub(super) fn from_graph(graph: BvBlastProof) -> Self {
        Self {
            width: graph.obligation.width,
            vars: graph.vars,
            bit_lemmas: graph.bit_lemmas,
            clauses: graph.clauses,
        }
    }

    /// The width of the equality this CNF negates.
    pub(super) fn width(&self) -> u32 {
        self.width
    }
}

/// Reconstruct ordinary expression CNF under the existing construction limits.
/// Does not materialize solver clauses, search, replay, or establish validity.
/// The caller's cumulative poll and the earliest supplied deadline remain in
/// force; no proof-search or replay allowance is renewed by this operation.
pub(crate) fn build_bv_expr_cnf(
    lhs: &BvExpr,
    rhs: &BvExpr,
    limits: &BvExprProofLimits,
    keep_going: &mut dyn FnMut() -> bool,
) -> Result<BvExprCnf, BvExprExportError> {
    let mut limits = limits.clone();
    if let (Some(production), Some(replay)) = (
        limits.resolution.deadline,
        limits.resolution.validation.deadline,
    ) {
        limits.resolution.deadline = Some(production.min(replay));
    }
    cancellation::run(keep_going, |poll| {
        let preflight = preflight_bv_equality(lhs, rhs, &limits, poll)?;
        let cnf = build(lhs, rhs, Some((&limits, preflight)), poll)?;
        finish_expr_export(Some(&limits), poll)?;
        Ok(cnf)
    })
}

// The producer already owns a successful preflight and a sticky outer poll.
// Sharing this implementation avoids a second census or a second encoder.
pub(super) fn build(
    lhs: &BvExpr,
    rhs: &BvExpr,
    bounded: Option<(&BvExprProofLimits, BvExprPreflight)>,
    keep_going: &mut dyn FnMut() -> bool,
) -> Result<BvExprCnf, BvExprExportError> {
    let limits = bounded.as_ref().map(|(limits, _)| *limits);
    let mut vars = VarTable::default();
    let mut bit_lemmas: Vec<BitLemma> = Vec::new();
    let mut clauses: Vec<Clause> = Vec::new();

    let mut blaster = ExprBlaster::new(
        limits.and_then(|limits| limits.resolution.deadline),
        keep_going,
    );
    if let Some((limits, mut preflight)) = bounded {
        // The preflight interned these exact borrowed trees; its occurrence
        // table lets the encoder blast each distinct node once.
        blaster.shared = preflight.sharing.take_occurrences();
        reserve_bv_expr_construction(
            &mut vars,
            &mut bit_lemmas,
            &mut clauses,
            &mut blaster,
            limits,
            preflight,
        )?;
    }
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
        blaster.check_deadline()?;
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
        admit_shape(&vars, &bit_lemmas, &clauses, &mut blaster, limits)?;
    }

    // The cache and transient output vectors are not part of the surfaced
    // certificate. Release them before duplicating the CNF into ay-sat's
    // literal type so the two bounded representations do not retain scratch
    // alongside one another.
    drop(lhs_bits);
    drop(rhs_bits);
    drop(eq_vars);
    drop(blaster);

    Ok(BvExprCnf {
        width,
        vars,
        bit_lemmas,
        clauses,
    })
}

fn admit_shape(
    vars: &VarTable,
    bit_lemmas: &[BitLemma],
    clauses: &[Clause],
    blaster: &mut ExprBlaster<'_>,
    limits: &BvExprProofLimits,
) -> Result<(), BvExprExportError> {
    blaster.check_deadline()?;
    if bit_lemmas.len() > limits.max_estimated_gate_work {
        return Err(BvExprExportError::ResourceLimit {
            resource: "actual bit-blast gates",
            limit: limits.max_estimated_gate_work,
            actual: bit_lemmas.len(),
        });
    }
    if vars.len() > limits.resolution.max_num_vars {
        return Err(BvExprExportError::ResourceLimit {
            resource: "actual bit-blast variables",
            limit: limits.resolution.max_num_vars,
            actual: vars.len(),
        });
    }
    if clauses.len() > limits.resolution.max_input_clauses {
        return Err(BvExprExportError::ResourceLimit {
            resource: "actual bit-blast clauses",
            limit: limits.resolution.max_input_clauses,
            actual: clauses.len(),
        });
    }
    let mut actual_literals = 0_usize;
    for (index, clause) in clauses.iter().enumerate() {
        if index & 0x3ff == 0 {
            blaster.check_deadline()?;
        }
        poll_export(blaster.keep_going)?;
        if clause.lits.len() > limits.resolution.max_input_clause_literals {
            return Err(BvExprExportError::ResourceLimit {
                resource: "actual bit-blast clause literals",
                limit: limits.resolution.max_input_clause_literals,
                actual: clause.lits.len(),
            });
        }
        actual_literals = actual_literals.checked_add(clause.lits.len()).ok_or(
            BvExprExportError::ResourceLimit {
                resource: "actual bit-blast literals",
                limit: limits.resolution.max_input_literals,
                actual: usize::MAX,
            },
        )?;
    }
    if actual_literals > limits.resolution.max_input_literals {
        return Err(BvExprExportError::ResourceLimit {
            resource: "actual bit-blast literals",
            limit: limits.resolution.max_input_literals,
            actual: actual_literals,
        });
    }
    blaster.check_deadline()?;
    Ok(())
}

#[cfg(test)]
mod tests;
