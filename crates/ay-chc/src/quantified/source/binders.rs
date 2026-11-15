// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Joint lexical groups; no binder escapes into the clause's free variables.

use super::*;

#[cfg(test)]
mod tests;

pub(super) fn preflight(
    premise: &UniversalPremise,
    registry: &Registry,
    functions: &Functions,
    budget: &mut Budget,
) -> ChcResult<()> {
    if premise.binder_count() > MAX_PREMISE_BINDERS {
        return Err(invalid("universal premise binder limit"));
    }
    let mut names = BTreeSet::new();
    for binder in premise.binders() {
        bv_sort(&binder.sort)?;
        // Charge each name before inserting it; the existing allowance also
        // covers binder storage and canonical declaration rendering.
        budget.name(&binder.name)?;
        if !names.insert(binder.name.as_str()) {
            return Err(invalid("duplicate universal premise binder"));
        }
        if registry.contains_term_symbol(&binder.name) || functions.contains(&binder.name) {
            return Err(invalid("binder shadows declared operation"));
        }
    }
    Ok(())
}

pub(super) fn variables<'a>(
    expr: &'a ChcExpr,
    premise: Option<&UniversalPremise>,
    out: &mut Variables<'a>,
) -> ChcResult<()> {
    let mut pending = vec![expr];
    while let Some(expr) = pending.pop() {
        match expr {
            ChcExpr::Var(var) => {
                let bound = premise.and_then(|p| p.binders().find(|b| b.name == var.name));
                if let Some(bound) = bound {
                    if bound.sort != var.sort {
                        return Err(invalid("binder reference sort mismatch"));
                    }
                } else if let Some(old) = out.insert(&var.name, &var.sort) {
                    if old != &var.sort {
                        return Err(invalid("free variable sort conflict"));
                    }
                }
            }
            ChcExpr::Op(_, args) | ChcExpr::FuncApp(_, _, args) => {
                pending.extend(args.iter().rev().map(AsRef::as_ref))
            }
            ChcExpr::ConstArray(_, value) => pending.push(value),
            _ => {}
        }
    }
    Ok(())
}

pub(super) fn render(premise: &UniversalPremise) -> String {
    premise
        .binders()
        .map(|binder| {
            format!(
                "({} {})",
                quote_symbol(&binder.name),
                sort_to_smtlib(&binder.sort)
            )
        })
        .collect::<Vec<_>>()
        .join(" ")
}
