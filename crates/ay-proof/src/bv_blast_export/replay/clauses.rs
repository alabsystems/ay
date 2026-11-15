// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

pub(super) fn validate(
    proof: &BvBlastProof,
    budget: &mut ReplayBudget<'_, '_>,
) -> Result<(), BvBlastValidateError> {
    let limits = budget.limits;
    // 2. Clauses: canonical ids, provenance resolves, var references.
    let mut original_literals = 0_usize;
    for (idx, cl) in proof.clauses.iter().enumerate() {
        budget.poll()?;
        budget.count(
            "original clause literals",
            cl.lits.len(),
            limits.max_clause_literals,
        )?;
        original_literals = original_literals.saturating_add(cl.lits.len());
        budget.count(
            "original literals",
            original_literals,
            limits.max_original_literals,
        )?;
        budget.add_work(cl.lits.len().saturating_add(1))?;
        if cl.id as usize != idx {
            return Err(BvBlastValidateError::NonCanonicalClauseId {
                index: idx,
                id: cl.id,
            });
        }
        for lit in &cl.lits {
            budget.poll()?;
            check_var(proof, lit.var)?;
        }
        match cl.provenance {
            ClauseProvenance::BitLemmaCnf { lemma } => {
                let Some(lem) = proof.bit_lemmas.get(lemma as usize) else {
                    return Err(BvBlastValidateError::MissingLemma {
                        clause: cl.id,
                        lemma,
                    });
                };
                // Leaf-clause semantic check: the clause must be one of the
                // Tseitin clauses entailed by this gate over its own out/ins.
                // This re-derives gate semantics from scratch — the provenance
                // tag is verified, not believed. A clause with arbitrary literals
                // that merely cites an in-range lemma is rejected here.
                let generated = tseitin_clauses(lem.kind, lem.out, &lem.ins);
                let mut comparison_work = 0_usize;
                for candidate in &generated {
                    budget.poll()?;
                    comparison_work = comparison_work
                        .saturating_add(candidate.len().saturating_add(cl.lits.len()));
                }
                budget.add_work(comparison_work)?;
                let mut entailed = false;
                let mut actual_clause = None;
                for candidate in &generated {
                    budget.poll()?;
                    let expected = sets::collect(candidate, budget)?;
                    // Normalize THIS immutable clause only when its first
                    // actual comparison occurs. Reuse data, never a verdict:
                    // every candidate attempt is still checked, and every
                    // fresh replay constructs these sets independently. Keep
                    // the original full worst-case comparison debit above.
                    let actual = match actual_clause.take() {
                        Some(actual) => actual,
                        None => sets::collect(&cl.lits, budget)?,
                    };
                    let matches = sets::equal(&expected, &actual, budget)?;
                    actual_clause = Some(actual);
                    if matches {
                        entailed = true;
                        break;
                    }
                }
                if !entailed {
                    return Err(BvBlastValidateError::ClauseNotEntailed {
                        clause: cl.id,
                        lemma,
                        kind: lem.kind,
                    });
                }
            }
            ClauseProvenance::Disequality => {}
        }
    }

    Ok(())
}
