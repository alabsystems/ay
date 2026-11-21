// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Independently re-prove a bounded integer equality chain carried by LIA.
//! The producer's arithmetic annotation remains attached to its original clause.

use super::eq_transitive::printed_eq_transitive_chain_holds;
use super::*;

const MAX_LITERALS: usize = 64;
const SCREEN_WORK: u64 = 4 * 1024 * 1024;

/// Whether the exact native and printed clause both instantiate checked
/// equality transitivity. The proof-wide allowance is spent even on refusal.
#[must_use]
pub fn checked_lia_equality_chain_lowering_supported(
    terms: &TermStore,
    kind: &ay_core::TheoryLemmaKind,
    clause: &[TermId],
    overrides: Option<&HashMap<TermId, String>>,
    remaining_work: &mut u64,
) -> bool {
    if *remaining_work == 0
        || !matches!(kind, ay_core::TheoryLemmaKind::LiaGeneric)
        || !(3..=MAX_LITERALS).contains(&clause.len())
    {
        return false;
    }
    let Ok(stop) = ay_core::resource::current_check_stop() else {
        return false;
    };
    let guard = ay_core::resource::current_guard();
    let mut progress = || {
        !stop.as_ref().is_some_and(|stop| stop())
            && !guard.as_ref().is_some_and(|guard| guard.poll().is_some())
    };
    let printer = AlethePrinter::new_with_overrides_and_budget(
        terms,
        overrides,
        Some((*remaining_work).min(SCREEN_WORK)),
    )
    .with_emission_progress(&mut progress);
    // Every generated premise is local to this rendering. An active empty
    // ledger requires the same printed-surface checks as whole publication.
    printer.printed_clause_ledger_active.set(true);
    if printer
        .format_checked_lia_equality_chain(ProofId(0), kind, clause)
        .is_none()
    {
        *remaining_work = remaining_work.saturating_sub(printer.work_used());
        return false;
    }
    let step = ProofStep::TheoryLemma {
        theory: "arith".into(),
        clause: clause.to_vec(),
        farkas: None,
        kind: *kind,
        lia: None,
    };
    let supported = printer
        .format_step(&step, ProofId(0))
        .is_ok_and(|text| text.contains(":rule eq_transitive") && !text.contains(":rule hole"));
    *remaining_work = remaining_work.saturating_sub(printer.work_used());
    supported && !printer.work_budget_exhausted()
}

pub(super) fn int_equality(terms: &TermStore, atom: TermId) -> Option<(TermId, TermId)> {
    terms.entry_stamp(atom)?;
    let TermData::App(Symbol::Named(name), args) = terms.get(atom) else {
        return None;
    };
    let [left, right] = args.as_slice() else {
        return None;
    };
    terms.entry_stamp(*left)?;
    terms.entry_stamp(*right)?;
    (name == "="
        && terms.sort(atom) == &ay_core::Sort::Bool
        && terms.sort(*left) == &ay_core::Sort::Int
        && terms.sort(*right) == &ay_core::Sort::Int)
        .then_some((*left, *right))
}

fn ordered_chain(terms: &TermStore, clause: &[TermId]) -> Option<Vec<TermId>> {
    let mut premises = Vec::with_capacity(clause.len());
    let mut conclusion = None;
    for &literal in clause {
        terms.entry_stamp(literal)?;
        if terms.sort(literal) != &ay_core::Sort::Bool {
            return None;
        }
        if let TermData::Not(atom) = terms.get(literal) {
            int_equality(terms, *atom)?;
            premises.push(literal);
        } else {
            int_equality(terms, literal)?;
            if conclusion.replace(literal).is_some() {
                return None;
            }
        }
    }
    premises.push(conclusion?);
    crate::recognize_euf_transitive(terms, &premises).then_some(premises)
}

fn printed_reordering_matches_exact_occurrences(
    ordered: &[TermId],
    printed: &[String],
    original: &[TermId],
    rendered: &[String],
) -> bool {
    if ordered.len() > MAX_LITERALS
        || ordered.len() != printed.len()
        || original.len() != rendered.len()
        || original.len() != ordered.len()
    {
        return false;
    }
    let mut used = [false; MAX_LITERALS];
    original.iter().zip(rendered).all(|(literal, text)| {
        let Some(index) =
            ordered
                .iter()
                .zip(printed)
                .enumerate()
                .position(|(index, (source, source_text))| {
                    !used[index] && source == literal && source_text == text
                })
        else {
            return false;
        };
        used[index] = true;
        true
    })
}

impl AlethePrinter<'_> {
    pub(super) fn admit_integer_clause_rendering_dag(&self, roots: &[TermId]) -> bool {
        const MAX_OCCURRENCES: usize = 4096;
        const MAX_DEPTH: usize = 64;
        if !self.admit_emission_work((roots.len() as u64).saturating_mul(32)) {
            return false;
        }
        let mut pending: Vec<_> = roots.iter().map(|&root| (root, 0usize)).collect();
        let mut occurrences = 0usize;
        while let Some((term, depth)) = pending.pop() {
            occurrences += 1;
            if occurrences > MAX_OCCURRENCES
                || depth > MAX_DEPTH
                || !self.admit_emission_work(64)
                || self.terms.entry_stamp(term).is_none()
                || !matches!(
                    self.terms.sort(term),
                    ay_core::Sort::Int | ay_core::Sort::Bool
                )
            {
                return false;
            }
            let children = match self.terms.get(term) {
                TermData::Const(Constant::Bool(_)) => continue,
                TermData::Const(Constant::Int(value)) if value.bits() <= 1024 => continue,
                TermData::Var(name, _) if name.len() <= 256 => continue,
                TermData::Not(inner) => {
                    if self.terms.entry_stamp(*inner).is_none()
                        || self.terms.sort(term) != &ay_core::Sort::Bool
                        || self.terms.sort(*inner) != &ay_core::Sort::Bool
                    {
                        return false;
                    }
                    std::slice::from_ref(inner)
                }
                TermData::App(Symbol::Named(name), children) if name.len() <= 256 => {
                    if children.len() > MAX_OCCURRENCES.saturating_sub(occurrences + pending.len())
                        || !self.admit_emission_work(children.len() as u64)
                    {
                        return false;
                    }
                    if children
                        .iter()
                        .any(|&child| self.terms.entry_stamp(child).is_none())
                    {
                        return false;
                    }
                    let int = |&child| self.terms.sort(child) == &ay_core::Sort::Int;
                    let boolean = |&child| self.terms.sort(child) == &ay_core::Sort::Bool;
                    let root_int = self.terms.sort(term) == &ay_core::Sort::Int;
                    let root_bool = self.terms.sort(term) == &ay_core::Sort::Bool;
                    let typed = match name.as_str() {
                        "+" | "*" | "-" => {
                            root_int && !children.is_empty() && children.iter().all(int)
                        }
                        "div" | "mod" => {
                            root_int && children.len() == 2 && children.iter().all(int)
                        }
                        "abs" => root_int && children.len() == 1 && children.iter().all(int),
                        "<" | "<=" | ">" | ">=" => {
                            root_bool && children.len() == 2 && children.iter().all(int)
                        }
                        "and" | "or" | "xor" | "=>" => {
                            root_bool && children.len() >= 2 && children.iter().all(boolean)
                        }
                        "not" => root_bool && children.len() == 1 && children.iter().all(boolean),
                        "=" | "distinct" => {
                            root_bool
                                && children.len() >= 2
                                && children.iter().all(|&child| {
                                    self.terms.sort(child) == self.terms.sort(children[0])
                                })
                        }
                        "ite" => {
                            children.len() == 3
                                && boolean(&children[0])
                                && self.terms.sort(children[1]) == self.terms.sort(term)
                                && self.terms.sort(children[2]) == self.terms.sort(term)
                        }
                        "true" | "false" => root_bool && children.is_empty(),
                        _ => true,
                    };
                    if !typed {
                        return false;
                    }
                    children.as_slice()
                }
                // Binder, indexed, and other literal payloads stay outside
                // this integer codec rather than entering recursive printing.
                _ => return false,
            };
            if children.len() > MAX_OCCURRENCES.saturating_sub(occurrences + pending.len())
                || !self.admit_emission_work((children.len() as u64).saturating_mul(32))
            {
                return false;
            }
            // Count occurrences, not globally seen nodes. A shared DAG can
            // expand exponentially in text; a forged cycle hits the depth
            // bound before any recursive formatter sees it.
            pending.extend(children.iter().map(|&child| (child, depth + 1)));
        }
        true
    }

    pub(super) fn format_checked_lia_equality_chain(
        &self,
        id: ProofId,
        kind: &ay_core::TheoryLemmaKind,
        clause: &[TermId],
    ) -> Option<String> {
        if !matches!(kind, ay_core::TheoryLemmaKind::LiaGeneric)
            || !(3..=MAX_LITERALS).contains(&clause.len())
            || !self.admit_emission_work((clause.len() as u64).saturating_pow(2))
        {
            return None;
        }
        if !self.admit_integer_clause_rendering_dag(clause) {
            return None;
        }
        let ordered = ordered_chain(self.terms, clause)?;
        let canonical =
            AlethePrinter::new_with_overrides_and_budget(self.terms, None, Some(SCREEN_WORK))
                .with_parent_emission_progress(self);
        let mut printed = Vec::with_capacity(ordered.len());
        for &literal in &ordered {
            if !self.admit_emission_work(1) {
                return None;
            }
            let (atom, negative) = match self.terms.get(literal) {
                TermData::Not(atom) => (*atom, true),
                _ => (literal, false),
            };
            let (left, right) = int_equality(self.terms, atom)?;
            let before = canonical.work_used();
            let left_text = canonical.format_term(left);
            let right_text = canonical.format_term(right);
            self.charge(canonical.work_used().saturating_sub(before));
            if canonical.work_budget_exhausted() || self.work_budget_exhausted() {
                return None;
            }
            // Interior overrides may change typing or operator meaning. Only
            // the native operands' own spelling is admitted by this codec.
            if self.format_term(left) != left_text || self.format_term(right) != right_text {
                return None;
            }
            let text = self.format_derived_literal(literal);
            let expected = |a: &str, b: &str| {
                let eq = format!("(= {a} {b})");
                if negative {
                    format!("(not {eq})")
                } else {
                    eq
                }
            };
            if text != expected(&left_text, &right_text)
                && text != expected(&right_text, &left_text)
            {
                return None;
            }
            printed.push(text);
        }
        if canonical.work_budget_exhausted() || self.work_budget_exhausted() {
            return None;
        }
        let borrowed: Vec<_> = printed.iter().map(String::as_str).collect();
        if !self.admit_emission_work((printed.len() as u64).saturating_pow(2))
            || !printed_eq_transitive_chain_holds(&borrowed)
            || self.work_budget_exhausted()
        {
            return None;
        }
        let chain = format!("(cl {})", printed.join(" "));
        if ordered.as_slice() == clause {
            return Some(format!("(step {id} {chain} :rule eq_transitive)"));
        }
        let original: Vec<_> = clause
            .iter()
            .map(|&literal| self.format_derived_literal(literal))
            .collect();
        let comparison_bytes = original
            .iter()
            .chain(&printed)
            .fold(0u64, |sum, text| sum.saturating_add(text.len() as u64))
            .saturating_mul(clause.len() as u64);
        if !self.admit_emission_work(
            comparison_bytes.saturating_add((clause.len() as u64).saturating_pow(2)),
        ) || !printed_reordering_matches_exact_occurrences(&ordered, &printed, clause, &original)
        {
            return None;
        }
        Some(format!(
            "(step {id}.chain {chain} :rule eq_transitive)\n\
             (step {id} (cl {}) :rule reordering :premises ({id}.chain))",
            original.join(" ")
        ))
    }
}

#[cfg(test)]
mod tests;
