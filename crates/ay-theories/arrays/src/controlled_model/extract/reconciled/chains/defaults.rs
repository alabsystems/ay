// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

pub(in super::super) fn shared(
    solver: &ArraySolver<'_>,
    values: &HashMap<TermId, String>,
    model: &ArrayModel,
    members: &[TermId],
    bases: &[TermId],
    unwritten: &[(String, String)],
    chains: &[Chain<'_>],
    work: &mut WorkBudget<'_>,
) -> Result<(Option<String>, bool), QueryError> {
    let mut result: Option<String> = None;
    let mut conflict = false;
    for &term in members.iter().chain(bases) {
        if let Some(value) = default(solver, values, model, term, work)? {
            if let Some(prior) = &result {
                if !storage::equal(prior, &value, work)? {
                    conflict = true;
                }
                work.charge(16)?;
                drop(value);
            } else {
                result = Some(value);
            }
        }
    }
    if result.is_none() && !conflict {
        let mut free = 0usize;
        for &base in bases {
            if scan::lookup(&solver.const_array_cache, base, work)?.is_none() {
                work.charge(16)?;
                free = owned::checked(free.checked_add(1), work)?;
            }
        }
        // This explicit flat cohort has no opaque array-valued UF/read.
        // Exactly the legacy two-free-base completion rule remains.
        if free >= 2 {
            let value = unwritten.first().map(|(_, v)| v.as_str()).or_else(|| {
                chains
                    .first()
                    .and_then(|c| c.writes.first())
                    .map(|(_, v)| *v)
            });
            result = owned::optional_text(value, work)?;
        }
    }
    Ok((result, conflict))
}

fn default(
    solver: &ArraySolver<'_>,
    values: &HashMap<TermId, String>,
    model: &ArrayModel,
    term: TermId,
    work: &mut WorkBudget<'_>,
) -> Result<Option<String>, QueryError> {
    if let Some(&value) = scan::lookup(&solver.const_array_cache, term, work)? {
        if let Some(text) = scan::value(solver, values, value, work)?.filter(|v| !v.is_empty()) {
            return Ok(Some(owned::text(text, work)?));
        }
        scan::live(solver, value, work)?;
        work.charge(32)?;
        if let TermData::Const(Constant::Bool(value)) = solver.terms.get(value) {
            return Ok(Some(owned::text(
                if *value { "true" } else { "false" },
                work,
            )?));
        }
        // Legacy has no literal BV fallback. Do not invent a BV spelling.
    }
    let value = scan::lookup(&model.array_values, term, work)?.and_then(|v| v.default.as_deref());
    owned::optional_text(value, work)
}
