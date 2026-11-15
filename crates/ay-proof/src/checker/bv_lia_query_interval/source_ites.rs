// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact source Int and Bool ITE semantics for interval refutation.
//!
//! The only generated clauses are universally valid implications:
//! `not C or I = then` and `C or I = else`, where I is the exact source ITE.
//! Bool results receive both implications of each guarded branch equality.
//! Complex guards remain one exact opaque Boolean literal. Generated forms
//! share the parent meter and bounded retained atom and integer payloads.

use super::*;

const MAX_ITE_SOURCE_NODES: usize = 4096;
const MAX_SOURCE_ITES: usize = 32;
const MAX_ITE_ATOM_COPIES: usize = 4096;
const MAX_ITE_LIMBS: u64 = 1 << 16;

impl QueryChecker<'_> {
    /// `None` declines the additional lane; `Some(n)` retains all n complete
    /// source-semantic clauses. No term-store mutation or solver input occurs.
    pub(super) fn append_source_ite_clauses(
        &mut self,
        assertions: &[TermId],
        clauses: &mut Vec<Vec<ClauseLiteral>>,
        nodes: &mut u64,
        entry_work: u64,
    ) -> Result<Option<usize>, BvLiaUnsatAuthenticationError> {
        let Some(ites) = self.interval_source_ites(assertions, entry_work)? else {
            return Ok(None);
        };
        let needed: usize = ites
            .iter()
            .map(|&ite| {
                if self.terms.sort(ite) == &Sort::Bool {
                    4
                } else {
                    2
                }
            })
            .sum();
        if clauses
            .len()
            .checked_add(needed)
            .is_none_or(|n| n > MAX_CLAUSES)
        {
            return Ok(None);
        }
        let mut atoms = 0usize;
        let mut limbs = 0u64;
        let mut appended = 0usize;
        for ite in ites {
            let TermData::Ite(condition, then_term, else_term) = self.terms.get(ite) else {
                return Ok(None);
            };
            let (condition, then_term, else_term) = (*condition, *then_term, *else_term);
            for (polarity, branch) in [(false, then_term), (true, else_term)] {
                if self.terms.sort(ite) == &Sort::Bool {
                    for branch_polarity in [false, true] {
                        let guard = self.source_ite_guard(condition, polarity, nodes)?;
                        let branch = self.source_ite_bool_value(branch, branch_polarity, nodes)?;
                        let clause = vec![
                            guard,
                            ClauseLiteral::Opaque {
                                term: ite,
                                polarity: !branch_polarity,
                            },
                            branch,
                        ];
                        if !self.charge_ite_clause(&clause, &mut atoms, &mut limbs, entry_work)? {
                            return Ok(None);
                        }
                        clauses.push(clause);
                        appended += 1;
                    }
                    continue;
                }
                // Never flatten a complex guard: its exact Boolean value is
                // an opaque literal. Only shallow Var/Const comparisons are
                // interpreted, so shared arithmetic DAGs cannot amplify here.
                let guard = self.source_ite_guard(condition, polarity, nodes)?;
                let value = LinearForm::atom(ite);
                let branch = self.source_ite_value(branch)?;
                let mut clause = vec![guard];
                let Some(equality) =
                    self.comparison_literal(value, branch, false, Relation::Equal)?
                else {
                    return Ok(None);
                };
                clause.push(equality);
                if !self.charge_ite_clause(&clause, &mut atoms, &mut limbs, entry_work)? {
                    return Ok(None);
                }
                clauses.push(clause);
                appended += 1;
            }
        }
        Ok(Some(appended))
    }

    /// Interpret only comparisons whose operands cannot expand into a wide
    /// linear form. In particular a whole mod application is one exact atom;
    /// its dividend is never recursively normalized by `linear_form`.
    fn source_ite_bool_value(
        &mut self,
        term: TermId,
        polarity: bool,
        nodes: &mut u64,
    ) -> Result<ClauseLiteral, BvLiaUnsatAuthenticationError> {
        let (term, polarity) = match negation_body(self, term) {
            Some(inner) => (inner, !polarity),
            None => (term, polarity),
        };
        let terms = self.terms;
        let shallow = match terms.get(term) {
            TermData::App(Symbol::Named(name), args)
                if args.len() == 2 && matches!(name.as_str(), "<" | "<=" | ">" | ">=" | "=") =>
            {
                args.iter().all(|&arg| {
                    if terms.sort(arg) != &Sort::Int {
                        return false;
                    }
                    match terms.get(arg) {
                        TermData::Var(..) | TermData::Const(Constant::Int(_)) => true,
                        TermData::App(Symbol::Named(name), operands) => {
                            name == "mod" && operands.len() == 2
                        }
                        _ => false,
                    }
                })
            }
            _ => false,
        };
        if shallow {
            if let TermData::App(_, args) = terms.get(term) {
                for &arg in args {
                    if let TermData::Const(Constant::Int(value)) = terms.get(arg) {
                        self.ensure_integer_magnitude(value)?;
                        self.meter.charge(integer_limb_units(value).max(1))?;
                    }
                }
            }
            if let Some(literal) = self.arithmetic_literal(term, polarity, 0, nodes)? {
                return Ok(literal);
            }
        }
        Ok(ClauseLiteral::Opaque { term, polarity })
    }

    fn source_ite_guard(
        &mut self,
        condition: TermId,
        polarity: bool,
        nodes: &mut u64,
    ) -> Result<ClauseLiteral, BvLiaUnsatAuthenticationError> {
        let terms = self.terms;
        let shallow = match terms.get(condition) {
            TermData::App(Symbol::Named(name), args)
                if args.len() == 2 && matches!(name.as_str(), "<" | "<=" | ">" | ">=" | "=") =>
            {
                args.iter().all(|&term| {
                    terms.sort(term) == &Sort::Int
                        && matches!(
                            terms.get(term),
                            TermData::Var(..) | TermData::Const(Constant::Int(_))
                        )
                })
            }
            _ => false,
        };
        if shallow {
            if let Some(literal) = self.arithmetic_literal(condition, polarity, 0, nodes)? {
                return Ok(literal);
            }
        }
        Ok(ClauseLiteral::Opaque {
            term: condition,
            polarity,
        })
    }

    /// An exact source denotation, without recursively expanding arithmetic.
    fn source_ite_value(
        &mut self,
        term: TermId,
    ) -> Result<LinearForm, BvLiaUnsatAuthenticationError> {
        let terms = self.terms;
        if let TermData::Const(Constant::Int(value)) = terms.get(term) {
            self.ensure_integer_magnitude(value)?;
            self.meter.charge(integer_limb_units(value).max(1))?;
            return Ok(LinearForm::constant(value.clone()));
        }
        Ok(LinearForm::atom(term))
    }

    fn interval_source_ites(
        &mut self,
        assertions: &[TermId],
        entry_work: u64,
    ) -> Result<Option<Vec<TermId>>, BvLiaUnsatAuthenticationError> {
        let mut pending = assertions.to_vec();
        let mut seen = BTreeSet::new();
        let mut ites = BTreeSet::new();
        let terms = self.terms;
        while let Some(term) = pending.pop() {
            self.meter.charge(1)?;
            if self.meter.work.saturating_sub(entry_work) > MAX_INTERVAL_WORK {
                return Ok(None);
            }
            if !seen.insert(term) {
                continue;
            }
            if seen.len() > MAX_ITE_SOURCE_NODES {
                return Ok(None);
            }
            match terms.get(term) {
                TermData::Const(_) | TermData::Var(..) => {}
                TermData::Not(inner) => pending.push(*inner),
                TermData::Ite(condition, then_term, else_term) => {
                    if pending.len().saturating_add(3) > MAX_ITE_SOURCE_NODES {
                        return Ok(None);
                    }
                    if matches!(terms.sort(term), Sort::Int | Sort::Bool) {
                        ites.insert(term);
                        if ites.len() > MAX_SOURCE_ITES {
                            return Ok(None);
                        }
                    }
                    pending.extend([*condition, *then_term, *else_term]);
                }
                TermData::App(_, args) => {
                    if pending.len().saturating_add(args.len()) > MAX_ITE_SOURCE_NODES {
                        return Ok(None);
                    }
                    self.meter
                        .charge(u64::try_from(args.len()).unwrap_or(u64::MAX))?;
                    pending.extend(args.iter().copied());
                }
                _ => return Ok(None),
            }
        }
        Ok(Some(ites.into_iter().collect()))
    }

    fn charge_ite_clause(
        &mut self,
        clause: &[ClauseLiteral],
        atoms: &mut usize,
        limbs: &mut u64,
        entry_work: u64,
    ) -> Result<bool, BvLiaUnsatAuthenticationError> {
        for literal in clause {
            self.meter.charge(1)?;
            let ClauseLiteral::Arithmetic { form, .. } = literal else {
                continue;
            };
            let Some(count) = atoms.checked_add(form.atoms.len()) else {
                return Ok(false);
            };
            *atoms = count;
            let Some(count) = limbs.checked_add(integer_limb_units(&form.constant)) else {
                return Ok(false);
            };
            *limbs = count;
            for coefficient in form.atoms.values() {
                let Some(count) = limbs.checked_add(integer_limb_units(coefficient)) else {
                    return Ok(false);
                };
                *limbs = count;
            }
            if *atoms > MAX_ITE_ATOM_COPIES || *limbs > MAX_ITE_LIMBS {
                return Ok(false);
            }
        }
        // Charge just this clause's retained values before retaining it.
        let mut work = u64::try_from(clause.len()).unwrap_or(u64::MAX);
        for literal in clause {
            if let ClauseLiteral::Arithmetic { form, .. } = literal {
                work = work.saturating_add(integer_limb_units(&form.constant));
                for coefficient in form.atoms.values() {
                    work = work.saturating_add(integer_limb_units(coefficient));
                }
                work = work.saturating_add(u64::try_from(form.atoms.len()).unwrap_or(u64::MAX));
            }
        }
        self.meter.charge(work.max(1))?;
        Ok(self.meter.work.saturating_sub(entry_work) <= MAX_INTERVAL_WORK)
    }
}
