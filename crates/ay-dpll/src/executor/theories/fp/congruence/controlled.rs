// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The legacy algorithm and controlled path share traversal and pair ordering.

use ay_fp::{FpBuildError, FpConstruction};

use super::*;
use crate::executor::theories::fp::bitblast::backend::{Encoder, Predicate};

pub(in crate::executor::theories::fp) fn scan_foreign_controlled(
    terms: &TermStore,
    roots: &[TermId],
    check: &mut dyn FnMut() -> Result<(), FpBuildError>,
) -> Result<ForeignScan, FpBuildError> {
    scan(terms, roots, check)
}

pub(in crate::executor::theories::fp) fn plan_congruence_controlled(
    terms: &TermStore,
    fp: &mut FpConstruction<'_, '_>,
    tseitin: &ay_core::TseitinResult,
    scan: &ForeignScan,
    check: &mut dyn FnMut() -> Result<(), FpBuildError>,
) -> Result<CongruencePlan, FpBuildError> {
    plan(terms, fp, tseitin, scan, check)
}

pub(super) fn scan<E>(
    terms: &TermStore,
    roots: &[TermId],
    check: &mut dyn FnMut() -> Result<(), E>,
) -> Result<ForeignScan, E> {
    check()?;
    let mut grouped: BTreeMap<(String, usize), Vec<Application>> = BTreeMap::new();
    let mut unencodable = false;
    let mut visited: HashSet<TermId> = HashSet::default();
    let mut stack: Vec<TermId> = roots.to_vec();

    while let Some(term) = stack.pop() {
        check()?;
        if !visited.insert(term) {
            continue;
        }
        if !sort_is_representable(terms.sort(term)) {
            unencodable = true;
        }
        match terms.get(term) {
            TermData::App(sym, args) => {
                let name = sym.name();
                // An array leaf has no writes or extensional obligations here.
                // Preserve the legacy exception: walk only its select index.
                if name == "select" && args.len() == 2 && is_array_leaf(terms, args[0]) {
                    check()?;
                    grouped
                        .entry((name.to_string(), 2))
                        .or_default()
                        .push((term, args.clone()));
                    stack.push(args[1]);
                    continue;
                }
                if is_uninterpreted(sym, args) {
                    check()?;
                    grouped
                        .entry((name.to_string(), args.len()))
                        .or_default()
                        .push((term, args.clone()));
                }
                for &arg in args {
                    check()?;
                    stack.push(arg);
                }
            }
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(cond, then_term, else_term) => {
                stack.push(*cond);
                stack.push(*then_term);
                stack.push(*else_term);
            }
            TermData::Let(bindings, body) => {
                for (_, value) in bindings {
                    check()?;
                    stack.push(*value);
                }
                stack.push(*body);
            }
            TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => stack.push(*body),
            _ => {}
        }
    }

    let mut groups = Vec::new();
    for group in grouped.into_values() {
        check()?;
        if group.len() > 1 {
            groups.push(group);
        }
    }
    check()?;
    Ok(ForeignScan {
        groups,
        unencodable,
    })
}

pub(super) fn plan<E: Encoder>(
    terms: &TermStore,
    fp: &mut E,
    tseitin: &ay_core::TseitinResult,
    scan: &ForeignScan,
    check: &mut dyn FnMut() -> Result<(), E::Error>,
) -> Result<CongruencePlan, E::Error> {
    check()?;
    fp.checkpoint()?;
    let mut clauses: Vec<Vec<PlanLit>> = Vec::new();
    let mut incomplete = false;
    let mut forced = forced_outputs::ForcedOutputs::new();
    for group in &scan.groups {
        check()?;
        let residual = if group.len() > MAX_GROUP_APPLICATIONS {
            // Only complete clause-forced admission may omit pairs. Every
            // residual obligation is counted before any pair is encoded.
            let admitted = if scan.unencodable {
                None
            } else {
                forced.residual_pairs(terms, fp, tseitin, group, check)?
            };
            let Some(pairs) = admitted else {
                incomplete = true;
                continue;
            };
            Some(pairs)
        } else {
            None
        };
        let complete_len = if residual.is_some() { 0 } else { group.len() };
        // The small-group order and clauses are unchanged. Uniform oversized
        // groups have an empty residual iterator, never a quadratic scan.
        for (i, j) in (0..complete_len)
            .flat_map(|i| ((i + 1)..complete_len).map(move |j| (i, j)))
            .chain(residual.into_iter().flatten())
        {
            check()?;
            let (term_a, ref args_a) = group[i];
            let (term_b, ref args_b) = group[j];
            let Some(premises) = argument_premises(terms, fp, args_a, args_b, check)? else {
                incomplete = true;
                continue;
            };
            if premises.is_empty() {
                continue;
            }
            check()?;
            let antecedent: Vec<PlanLit> = premises.iter().map(|&lit| PlanLit::Fp(-lit)).collect();
            match terms.sort(term_a).clone() {
                Sort::Bool => {
                    let (Some(var_a), Some(var_b)) =
                        (tseitin.var_for_term(term_a), tseitin.var_for_term(term_b))
                    else {
                        incomplete = true;
                        continue;
                    };
                    let (lit_a, lit_b) = (var_a as i32, var_b as i32);
                    let mut forward = antecedent.clone();
                    forward.push(PlanLit::Tseitin(-lit_a));
                    forward.push(PlanLit::Tseitin(lit_b));
                    let mut backward = antecedent;
                    backward.push(PlanLit::Tseitin(lit_a));
                    backward.push(PlanLit::Tseitin(-lit_b));
                    clauses.push(forward);
                    clauses.push(backward);
                }
                Sort::FloatingPoint(..) | Sort::BitVec(_) => {
                    let request = if matches!(terms.sort(term_a), Sort::FloatingPoint(..)) {
                        Predicate::StructuralEq(term_a, term_b)
                    } else {
                        Predicate::BvEq(term_a, term_b)
                    };
                    let Some(equal) = fp.predicate(request)? else {
                        incomplete = true;
                        continue;
                    };
                    let mut clause = antecedent;
                    clause.push(PlanLit::Fp(equal));
                    clauses.push(clause);
                }
                _ => incomplete = true,
            }
        }
    }
    check()?;
    fp.checkpoint()?;
    Ok(CongruencePlan {
        clauses,
        incomplete,
    })
}

fn argument_premises<E: Encoder>(
    terms: &TermStore,
    fp: &mut E,
    args_a: &[TermId],
    args_b: &[TermId],
    check: &mut dyn FnMut() -> Result<(), E::Error>,
) -> Result<Option<Vec<i32>>, E::Error> {
    check()?;
    let mut premises = Vec::new();
    for (&arg_a, &arg_b) in args_a.iter().zip(args_b.iter()) {
        check()?;
        if arg_a == arg_b {
            continue;
        }
        let sort_a = terms.sort(arg_a).clone();
        if sort_a != *terms.sort(arg_b) {
            return Ok(None);
        }
        let request = match sort_a {
            Sort::FloatingPoint(..) => Predicate::StructuralEq(arg_a, arg_b),
            Sort::BitVec(_) => Predicate::BvEq(arg_a, arg_b),
            ref sort if ay_fp::rewriter::is_rounding_mode_sort(sort) => {
                Predicate::RmEq(arg_a, arg_b)
            }
            _ => return Ok(None),
        };
        let Some(equal) = fp.predicate(request)? else {
            return Ok(None);
        };
        premises.push(equal);
    }
    Ok(Some(premises))
}
