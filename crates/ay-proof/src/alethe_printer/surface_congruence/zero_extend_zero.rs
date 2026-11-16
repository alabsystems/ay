// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Clean reads `((_ zero_extend 0) x)` as `x`. An otherwise ordinary
//! unary native congruence therefore becomes a copy of its earlier unit.
//! Judge that copy on the actual emitted surfaces, never on a re-rendered
//! assumption or a future entry in the native proof-clause table.

use super::*;
use crate::alethe_printer::printed_resolution::PrintedClause;

const MAX_BYTES: usize = 64 * 1024;
const MAX_SHELLS: usize = 64;
const MAX_NATIVE_NODES: usize = 4096;

fn live(terms: &TermStore, term: TermId) -> bool {
    (term.0 as usize) < terms.len()
}

fn equality(terms: &TermStore, term: TermId) -> Option<(TermId, TermId)> {
    if !live(terms, term) || terms.sort(term) != &Sort::Bool {
        return None;
    }
    let TermData::App(Symbol::Named(name), args) = terms.get(term) else {
        return None;
    };
    let [left, right] = args.as_slice() else {
        return None;
    };
    if name.as_ref() != "=" || !live(terms, *left) || !live(terms, *right) {
        return None;
    }
    let Sort::BitVec(width) = terms.sort(*left) else {
        return None;
    };
    (width.width > 0 && terms.sort(*left) == terms.sort(*right)).then_some((*left, *right))
}

fn zero_head(terms: &TermStore, term: TermId) -> bool {
    live(terms, term)
        && matches!(terms.get(term), TermData::App(Symbol::Indexed(name, indices), _)
            if name.as_ref() == "zero_extend" && (indices.first() == Some(&0) || indices.is_empty()))
}

fn native_shell(terms: &TermStore, term: TermId) -> Option<TermId> {
    let TermData::App(Symbol::Indexed(name, indices), args) = terms.get(term) else {
        return None;
    };
    let [operand] = args.as_slice() else {
        return None;
    };
    if name.as_ref() != "zero_extend"
        || indices.as_slice() != [0]
        || !live(terms, *operand)
        || terms.sort(term) != terms.sort(*operand)
        || !matches!(terms.sort(term), Sort::BitVec(width) if width.width > 0)
    {
        return None;
    }
    Some(*operand)
}

fn valid_native_chain(terms: &TermStore, mut term: TermId) -> bool {
    for _ in 0..MAX_SHELLS {
        if !zero_head(terms, term) {
            return true;
        }
        let Some(operand) = native_shell(terms, term) else {
            return false;
        };
        term = operand;
    }
    !zero_head(terms, term)
}

impl AlethePrinter<'_> {
    /// Allocation-free native candidate screen shared with the existing
    /// printed-demand planner. Named/private and nonzero heads keep their
    /// existing export path. Malformed indexed-zero candidates must refuse.
    pub(crate) fn is_zero_extend_zero_cong_candidate(&self, clause: &[TermId]) -> bool {
        if dialect::current() != dialect::AletheDialect::Clean {
            return false;
        }
        clause.iter().take(2).any(|term| {
            if !live(self.terms, *term) {
                return false;
            }
            matches!(self.terms.get(*term), TermData::App(Symbol::Named(name), sides)
                if name.as_ref() == "=" && sides.iter().take(2).any(|side| zero_head(self.terms, *side)))
        })
    }

    pub(crate) fn zero_extend_zero_cong_bridge(
        &self,
        id: ProofId,
        clause: &[TermId],
        premises: &[ProofId],
        args: &[TermId],
    ) -> Result<Option<String>, AlethePrintError> {
        if !self.is_zero_extend_zero_cong_candidate(clause) {
            return Ok(None);
        }
        let invalid = |reason: &str| AlethePrintError::InvalidCongruenceStep {
            id,
            reason: format!("Clean zero-extension congruence: {reason}"),
        };
        // Admit native inspection before any attempted reading or allocation.
        if !self.admit_emission_work(4 * MAX_SHELLS as u64) {
            return Err(self.work_budget_error(id.0));
        }
        let [conclusion] = clause else {
            return Err(invalid("requires one positive unit equality"));
        };
        let [premise] = premises else {
            return Err(invalid("requires exactly one earlier premise"));
        };
        if !args.is_empty() || *premise >= id {
            return Err(invalid("arguments or non-earlier premise"));
        }
        let Some((left, right)) = equality(self.terms, *conclusion) else {
            return Err(invalid("native conclusion is not a typed BV equality"));
        };
        let (Some(left_arg), Some(right_arg)) = (
            native_shell(self.terms, left),
            native_shell(self.terms, right),
        ) else {
            return Err(invalid("native heads are not exact unary zero_extend 0"));
        };
        if !valid_native_chain(self.terms, left) || !valid_native_chain(self.terms, right) {
            return Err(invalid(
                "malformed or over-depth native zero-extension chain",
            ));
        }
        // This table supplies native shape only. Authority comes from the
        // active, generation-tagged emitted clause below, with lexical scope.
        {
            let native = self.proof_clauses.borrow();
            let Some([literal]) = native.get(premise).map(Vec::as_slice) else {
                return Err(invalid("native premise is not a unit equality"));
            };
            let Some((a, b)) = equality(self.terms, *literal) else {
                return Err(invalid("native premise is not a typed BV equality"));
            };
            if !((a == left_arg && b == right_arg) || (a == right_arg && b == left_arg)) {
                return Err(invalid("native premise does not justify unary congruence"));
            }
        }
        if !self.printed_clause_ledger_active.get()
            || self
                .native_zero_cong_scopes
                .borrow()
                .get(premise)
                .is_none_or(|end| id >= *end)
        {
            return Err(invalid(
                "premise is missing or outside its active native scope",
            ));
        }
        let atoms = {
            let ledger = self.printed_step_clauses.borrow();
            let Some(PrintedClause::Literals(atoms)) = ledger.get(premise) else {
                return Err(invalid("earlier printed premise is missing or unreadable"));
            };
            if atoms.len() != 1 {
                return Err(invalid("earlier printed premise is not a unit"));
            }
            self.printed_atom_texts(atoms)
                .ok_or_else(|| invalid("printed premise atoms have retired"))?
        };
        let printed = self.format_clause(clause);
        if printed.len() > MAX_BYTES || atoms[0].len() > MAX_BYTES {
            return Err(invalid("printed equality exceeds its bounded reader"));
        }
        // Charge the bounded balanced reads and literal-spelling comparison
        // before they scan or allocate. Every shell scan is charged below.
        if !self
            .admit_emission_work((printed.len() as u64 + atoms[0].len() as u64).saturating_mul(256))
        {
            return Err(self.work_budget_error(id.0));
        }
        let unit = split_alethe_application_bounded(&printed, "cl", 1, MAX_BYTES)
            .map_err(|_| invalid("printed conclusion is not a bounded unit"))?;
        let [unit] = unit.as_slice() else {
            return Err(invalid("printed conclusion is not a unit"));
        };
        let endpoints = |text| {
            split_alethe_application_bounded(text, "=", 2, MAX_BYTES)
                .ok()
                .filter(|sides| sides.len() == 2)
        };
        let Some(conclusion) = endpoints(unit) else {
            return Err(invalid("printed conclusion is not a positive equality"));
        };
        let Some(premise_sides) = endpoints(atoms[0].as_ref()) else {
            return Err(invalid("printed premise is not a positive equality"));
        };
        // A textual shell is a Clean definition only for a typed BV
        // operand. Do not turn a type-changing authored replacement into an
        // apparent definition by deleting its head. Compare reachable
        // replacements with their native-head rendering in this SAME printer
        // and meter; the underlying native BV expression stays opaque.
        self.require_identity_zero_cong_rendering(id, unit, clause[0])?;
        for position in 0..2 {
            let a = self.erase_printed_zero_shells(id, conclusion[position])?;
            let b = self.erase_printed_zero_shells(id, premise_sides[position])?;
            if !surface_literal::same_printed_term(a, b) {
                return Err(invalid(
                    "Clean-read unit differs from its premise orientation",
                ));
            }
        }
        self.check_emission_progress(id.0)?;
        dialect::note_clean_only(dialect::CleanOnlySpelling::ZeroExtendAsConcat);
        Ok(Some(format!(
            "(step {id} {printed} :rule reordering :premises ({premise}))"
        )))
    }

    fn require_identity_zero_cong_rendering(
        &self,
        id: ProofId,
        printed: &str,
        root: TermId,
    ) -> Result<(), AlethePrintError> {
        let invalid = || AlethePrintError::InvalidCongruenceStep {
            id,
            reason: "zero-extension congruence has a changed or over-bound native rendering"
                .to_string(),
        };
        if !self.admit_emission_work(128) {
            return Err(self.work_budget_error(id.0));
        }
        // Count expanded native syntax before a replacement can hide a huge
        // payload or DAG from the native-head formatter. This is only a
        // borrowed rendering bound, not another SMT parser or evaluator.
        let mut pending = vec![(root, 0usize)];
        let mut nodes = 0usize;
        let mut bytes = 0u64;
        let mut render_work = 0u64;
        while let Some((term, depth)) = pending.pop() {
            if !self.admit_emission_work(128) {
                return Err(self.work_budget_error(id.0));
            }
            if !live(self.terms, term) || nodes == MAX_NATIVE_NODES || depth > 128 {
                return Err(invalid());
            }
            nodes += 1;
            let own = match self.terms.get(term) {
                TermData::Var(name, _) => (name.len() as u64).saturating_mul(2),
                TermData::Const(Constant::Bool(_)) => 5,
                TermData::Const(Constant::Int(value)) => value.bits(),
                TermData::Const(Constant::Rational(value)) => value
                    .0
                    .numer()
                    .bits()
                    .saturating_add(value.0.denom().bits()),
                TermData::Const(Constant::BitVec { value, width }) => {
                    if *width == 0
                        || value.sign() == Sign::Minus
                        || value.bits() > u64::from(*width)
                        || !matches!(self.terms.sort(term), Sort::BitVec(w) if w.width == *width)
                    {
                        return Err(invalid());
                    }
                    value.bits().max(u64::from(*width))
                }
                TermData::Const(Constant::String(text)) => (text.len() as u64).saturating_mul(10),
                TermData::App(symbol, children) => {
                    if symbol.name() == "const-array"
                        || children.len() > MAX_NATIVE_NODES.saturating_sub(nodes + pending.len())
                    {
                        return Err(invalid());
                    }
                    let indices = match symbol {
                        Symbol::Indexed(_, indices) => (indices.len() as u64).saturating_mul(11),
                        _ => 0,
                    };
                    if !self.admit_emission_work((children.len() as u64).saturating_mul(16)) {
                        return Err(self.work_budget_error(id.0));
                    }
                    pending.extend(children.iter().map(|term| (*term, depth + 1)));
                    (symbol.name().len() as u64)
                        .saturating_mul(2)
                        .saturating_add(indices)
                        .saturating_add(children.len() as u64)
                }
                TermData::Not(term) => {
                    pending.push((*term, depth + 1));
                    3
                }
                TermData::Ite(a, b, c) => {
                    pending.extend([*a, *b, *c].map(|term| (term, depth + 1)));
                    3
                }
                _ => return Err(invalid()),
            }
            .saturating_add(32);
            bytes = bytes.saturating_add(own);
            render_work = render_work.saturating_add(own.saturating_mul(depth as u64 + 1));
            if bytes > MAX_BYTES as u64 || pending.len() > MAX_NATIVE_NODES.saturating_sub(nodes) {
                return Err(invalid());
            }
        }
        if !self.admit_emission_work(render_work.saturating_mul(2)) {
            return Err(self.work_budget_error(id.0));
        }
        let mut seen = HashSet::default();
        let mut stack = vec![root];
        while let Some(term) = stack.pop() {
            if !live(self.terms, term) {
                return Err(invalid());
            }
            if seen.contains(&term) {
                continue;
            }
            if seen.len() == MAX_NATIVE_NODES {
                return Err(invalid());
            }
            if !self.admit_emission_work(128) {
                return Err(self.work_budget_error(id.0));
            }
            seen.insert(term);
            let replaced = self
                .wire_term_overrides
                .borrow()
                .as_ref()
                .is_some_and(|map| map.contains_key(&term))
                || self.let_bridge_renderings.borrow().contains_key(&term)
                || self.skolem_overrides.borrow().contains_key(&term);
            if replaced {
                let native_head = self.format_term_data(self.terms.get(term));
                let effective = self.format_term(term);
                if native_head.len() > MAX_BYTES || effective.len() > MAX_BYTES {
                    return Err(invalid());
                }
                if !self.admit_emission_work(
                    (native_head.len() as u64 + effective.len() as u64).saturating_mul(256),
                ) {
                    return Err(self.work_budget_error(id.0));
                }
                if !surface_literal::same_printed_term(&native_head, &effective) {
                    return Err(invalid());
                }
            }
            let mut push = |child| {
                if stack.len().saturating_add(seen.len()) >= MAX_NATIVE_NODES
                    || !self.admit_emission_work(8)
                {
                    return false;
                }
                stack.push(child);
                true
            };
            let bounded = match self.terms.get(term) {
                TermData::App(_, children) => children.iter().all(|child| push(*child)),
                TermData::Not(child) => push(*child),
                TermData::Ite(c, a, b) => push(*c) && push(*a) && push(*b),
                TermData::Const(_) | TermData::Var(..) => true,
                _ => false,
            };
            if !bounded {
                if self.work_budget_exhausted() {
                    return Err(self.work_budget_error(id.0));
                }
                return Err(invalid());
            }
        }
        let effective = self.format_term(root);
        if !surface_literal::same_printed_term(printed, &effective) {
            return Err(invalid());
        }
        self.check_emission_progress(id.0)
    }

    fn erase_printed_zero_shells<'s>(
        &self,
        id: ProofId,
        mut text: &'s str,
    ) -> Result<&'s str, AlethePrintError> {
        for _ in 0..MAX_SHELLS {
            let trimmed = text.trim();
            if !trimmed.starts_with("((_ zero_extend 0)") {
                return Ok(trimmed);
            }
            if !self.admit_emission_work(trimmed.len() as u64) {
                return Err(self.work_budget_error(id.0));
            }
            let shell =
                split_alethe_application_bounded(trimmed, "(_ zero_extend 0)", 1, MAX_BYTES)
                    .map_err(|_| AlethePrintError::InvalidCongruenceStep {
                        id,
                        reason: "malformed printed zero-extension shell".to_string(),
                    })?;
            let [operand] = shell.as_slice() else {
                return Err(AlethePrintError::InvalidCongruenceStep {
                    id,
                    reason: "printed zero-extension shell is not unary".to_string(),
                });
            };
            text = operand;
        }
        if !text.trim().starts_with("((_ zero_extend 0)") {
            Ok(text.trim())
        } else {
            Err(AlethePrintError::InvalidCongruenceStep {
                id,
                reason: "printed zero-extension shell depth exceeded".to_string(),
            })
        }
    }
}

#[cfg(test)]
mod tests;
