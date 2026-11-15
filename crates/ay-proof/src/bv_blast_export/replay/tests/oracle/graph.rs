// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;

pub(super) fn definitions(
    proof: &BvBlastProof,
    budget: &mut ReplayBudget<'_>,
) -> Result<Vec<Option<u32>>, BvBlastValidateError> {
    // 1. Bit lemmas: canonical ids, arity, unique definitions, and a
    // topological/inhabitable gate graph. Input-role variables are the only
    // unconstrained leaves; every other variable must be defined exactly
    // once by a total Boolean gate.
    let mut available: Vec<bool> = proof.vars.roles.iter().map(is_input_role).collect();
    let mut defined_by: Vec<Option<u32>> = vec![None; proof.vars.len()];
    for (index, lem) in proof.bit_lemmas.iter().enumerate() {
        budget.add_work(lem.ins.len().saturating_add(1))?;
        if lem.id as usize != index {
            return Err(BvBlastValidateError::NonCanonicalBitLemmaId { index, id: lem.id });
        }
        let expected = lem.kind.arity();
        if lem.ins.len() != expected {
            return Err(BvBlastValidateError::BadLemmaArity {
                id: lem.id,
                kind: lem.kind,
                expected,
                got: lem.ins.len(),
            });
        }
        check_var(proof, lem.out)?;
        if is_input_role(&proof.vars.roles[lem.out as usize]) {
            return Err(BvBlastValidateError::GateDefinesInput {
                lemma: lem.id,
                var: lem.out,
            });
        }
        if let Some(first) = defined_by[lem.out as usize] {
            return Err(BvBlastValidateError::DuplicateGateOutput {
                var: lem.out,
                first,
                second: lem.id,
            });
        }
        for &i in &lem.ins {
            check_var(proof, i)?;
            if !available[i as usize] {
                return Err(BvBlastValidateError::GateInputNotDefined {
                    lemma: lem.id,
                    var: i,
                });
            }
        }
        defined_by[lem.out as usize] = Some(lem.id);
        available[lem.out as usize] = true;
    }

    Ok(defined_by)
}

pub(super) fn equality(
    proof: &BvBlastProof,
    defined_by: &[Option<u32>],
    budget: &mut ReplayBudget<'_>,
) -> Result<Vec<Option<u32>>, BvBlastValidateError> {
    let equality_width = proof.obligation.width;
    let mut bit_eq_vars: Vec<Option<u32>> = vec![None; equality_width as usize];
    for (var, role) in proof.vars.roles.iter().enumerate() {
        budget.add_work(1)?;
        if !is_input_role(role) && defined_by[var].is_none() {
            return Err(BvBlastValidateError::MissingGateDefinition { var: var as u32 });
        }
        let VarRole::BitEq { bit } = *role else {
            continue;
        };
        let Some(slot) = bit_eq_vars.get_mut(bit as usize) else {
            return Err(BvBlastValidateError::MalformedBitEqLayout {
                reason: format!(
                    "variable {var} names out-of-range bit {bit} for width {equality_width}"
                ),
            });
        };
        if let Some(previous) = slot.replace(var as u32) {
            return Err(BvBlastValidateError::MalformedBitEqLayout {
                reason: format!("bit {bit} is assigned to both variables {previous} and {var}"),
            });
        }
        let lemma_id = defined_by[var].expect("non-input definition checked above");
        let lemma = &proof.bit_lemmas[lemma_id as usize];
        if lemma.kind != BitLemmaKind::XnorEq || lemma.out != var as u32 {
            return Err(BvBlastValidateError::MalformedBitEqLayout {
                reason: format!(
                    "variable {var} for bit {bit} is not defined by its own XnorEq lemma"
                ),
            });
        }
    }
    if let Some((bit, _)) = bit_eq_vars
        .iter()
        .enumerate()
        .find(|(_, variable)| variable.is_none())
    {
        return Err(BvBlastValidateError::MalformedBitEqLayout {
            reason: format!("missing BitEq variable for bit {bit}"),
        });
    }

    Ok(bit_eq_vars)
}

pub(super) fn disequality(
    proof: &BvBlastProof,
    bit_eq_vars: &[Option<u32>],
    budget: &mut ReplayBudget<'_>,
) -> Result<(), BvBlastValidateError> {
    // The only non-gate axiom is one exact encoding of `not(lhs = rhs)`:
    // one negative literal for every BitEq variable and nothing else.
    let disequalities: Vec<&Clause> = proof
        .clauses
        .iter()
        .filter(|clause| matches!(clause.provenance, ClauseProvenance::Disequality))
        .collect();
    if disequalities.len() != 1 {
        return Err(BvBlastValidateError::MalformedDisequality {
            reason: format!(
                "expected exactly one disequality clause, found {}",
                disequalities.len()
            ),
        });
    }
    let disequality = disequalities[0];
    budget.add_work(disequality.lits.len().saturating_add(bit_eq_vars.len()))?;
    let expected_disequality: BTreeSet<Lit> = bit_eq_vars
        .iter()
        .map(|variable| Lit::neg(variable.expect("all BitEq slots checked above")))
        .collect();
    let actual_disequality: BTreeSet<Lit> = disequality.lits.iter().copied().collect();
    if disequality.lits.len() != expected_disequality.len()
        || actual_disequality != expected_disequality
    {
        return Err(BvBlastValidateError::MalformedDisequality {
            reason: "literals must be exactly the negative BitEq variables, once each".to_string(),
        });
    }

    Ok(())
}
