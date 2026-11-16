// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Divisions are bit-blasted only where the refutation needs them.
//!
//! The pinned checker's `bitblast_udiv` is a long divider of about a thousand
//! gates per dividend bit, every one of which the document must define and
//! the refutation reason through. A lemma rarely needs all of its divisions:
//! external-codegen's definitional `SDIV` rows spell `bvsdiv` as a four-way `ite` over
//! the operand signs, and with a constant divisor two of the four `bvudiv`s
//! are dead. Measured 2026-09-30 on `(bvsdiv xn 1) = xn` at 64 bits: blasting
//! all four gave 264,472 gates and a 106 MB document that the consumer
//! refused (`over-budget zero-extension normalization`, the work budget of
//! Clean's adapter post-pass over every proof term; `consumer_work`), and the
//! swept refutation leaned on the dead dividers'
//! gates, which the topological sweep met first.
//!
//! So every `bvudiv`/`bvurem` starts OPAQUE — `bitblast_var`, free bits, sound
//! for a refutation whatever the division computes. While the abstraction has
//! a model, the divisions that model actually READS (a justification walk
//! from the root: an `ite` reads its condition and the branch it takes, a
//! decided `and`/`or` one deciding operand) and gets wrong are blasted, and the
//! lemma is planned again. A model no relevant division gets wrong reads every
//! opaque division as wrong, so the loop ends with all of them blasted exactly
//! as before: laziness changes which proof is printed, never whether one is.
//! A solve that decides nothing within its budget KEEPS the abstraction: the
//! model search is CDCL over the whole circuit, and an abstraction it cannot
//! refute in its budget is exactly the kind the sweep refutes by merging the
//! circuit's internal equivalences. Measured 2026-09-30 on external-codegen's 64-bit
//! `IDIV` row 1373: the abstraction with its two dead dividers opaque spends
//! all 2,000 conflicts undecided; blasting them too gave a 100 MB document
//! the consumer's budget refuses (and 168 s of printing), while the kept
//! abstraction sweeps and prints. The abstraction a lemma settles on is
//! remembered across renders ([`settled_key`]), so its search is paid once.
//! If an abstraction still does not print, the caller plans the lemma once
//! more with every division exact, unless its sweep refuted it and only the
//! document's size refused it (`transport/size_refusal.rs`).

use super::*;
use ay_sat::{
    solve_resolution_dag_counted, Literal, ResolutionProofLimits, ResolutionSolveOutcome,
};

mod settled;
use settled::{settled_key, settled_opaque, Candidate};

enum Refinement {
    Keep,
    Blast(DetHashSet<TermId>),
}

/// Conflicts one abstraction's model search may spend. A satisfiable
/// abstraction is found in a handful; an unsatisfiable one is what the sweep
/// is for. Measured 2026-09-30 on external-codegen's 64-bit `SDIV`/`IDIV`
/// definitional rows: every satisfiable abstraction was found with no
/// conflict at all, a case's unsatisfiable one was refuted in 127, and the
/// kept abstraction, left undecided, spent 6 to 24 s of its render on 2,000.
const MODEL_CONFLICTS: u64 = 256;
/// The search's outer wall-clock guard (the solver refuses an unbounded
/// search); the conflict cap is what decides. The cap is spent in about 3 s
/// on the 64-bit dividers on a heavily loaded machine (load average 80 on 18
/// cores); the former 5 s guard, under 2,000 conflicts, let the load decide
/// the abstraction.
const MODEL_WALL: std::time::Duration = std::time::Duration::from_secs(30);

/// A lemma prepared, its root clause planned, ready for [`Blaster::finish`].
pub(super) struct Planned<'a, 'p> {
    pub(super) blaster: Blaster<'a, 'p>,
    pub(super) root: SRef,
    pub(super) cnf: Vec<Vec<Literal>>,
    pub(super) root_clause_id: u64,
    /// Whether some division was left opaque.
    pub(super) abstracted: bool,
    /// Scheduling-only cache candidate, unpublished until the document prints.
    settled: Option<Candidate>,
}

/// How a planned lemma's roots become its one root gate.
pub(super) type Orient<'o, 'a, 'p> = dyn Fn(&mut Blaster<'a, 'p>, &[SRef]) -> Option<SRef> + 'o;

impl<'a, 'p> Blaster<'a, 'p> {
    /// Prepare `roots`, orient them into one root, and plan the lemma, with
    /// as few divisions blasted as its refutation needs; `lazy == false`
    /// blasts every division.
    pub(super) fn plan_lemma(
        printer: &'p AlethePrinter<'a>,
        id: ProofId,
        prefix: &str,
        roots: &[TermId],
        orient: &Orient<'_, 'a, 'p>,
        lazy: bool,
        case: Option<(&str, &case_split::Case)>,
    ) -> Option<Planned<'a, 'p>> {
        printer.check_emission_progress(0).ok()?;
        let mut opaque = if lazy {
            division_terms(printer, roots)?
        } else {
            DetHashSet::default()
        };
        let key = if lazy && !opaque.is_empty() {
            Some(settled_key(printer, roots, case)?)
        } else {
            None
        };
        let settled = match key.as_deref() {
            Some(key) => settled_opaque(printer, key)?,
            None => None,
        };
        if let Some(kept) = &settled {
            opaque = settled::retained_opaque(printer, opaque, kept)?;
        }
        loop {
            printer.check_emission_progress(0).ok()?;
            // Each round re-blasts the whole circuit (see `complete_blast_keeps_going`).
            if !printer.complete_blast_keeps_going() {
                return None;
            }
            let mut blaster = Blaster::new(printer, id, prefix.to_string());
            blaster.opaque_divisions = opaque.clone();
            if let Some((namespace, case)) = case {
                blaster.id = namespace.to_string();
                blaster.case = Some(case.clone());
            }
            printer.check_emission_progress(0).ok()?;
            let mut prepared = Vec::with_capacity(roots.len());
            for (index, &root) in roots.iter().enumerate() {
                printer.check_emission_progress(0).ok()?;
                prepared.push(if index == 0 {
                    blaster.prepare(root)?
                } else {
                    blaster.prepare_more(root)?
                });
                printer.check_emission_progress(0).ok()?;
            }
            let root = orient(&mut blaster, &prepared)?;
            blaster.assume_case()?;
            let (cnf, root_clause_id) = blaster.planned_cnf(root)?;
            printer.check_emission_progress(0).ok()?;
            let refine = if opaque.is_empty() || settled.is_some() {
                Refinement::Keep
            } else {
                blaster.refinement(&cnf, roots)?
            };
            match refine {
                Refinement::Blast(refine) => {
                    let refine = if refine.is_empty() {
                        opaque.clone()
                    } else {
                        refine
                    };
                    opaque.retain(|term| !refine.contains(term));
                    printer.check_emission_progress(0).ok()?;
                }
                Refinement::Keep => {
                    let candidate = match (key, &settled) {
                        (Some(key), None) => Some(Candidate::new(printer, key, &opaque)?),
                        _ => None,
                    };
                    printer.check_emission_progress(0).ok()?;
                    return Some(Planned {
                        blaster,
                        root,
                        cnf,
                        root_clause_id,
                        abstracted: !opaque.is_empty(),
                        settled: candidate,
                    });
                }
            }
        }
    }

    /// The document for `roots` oriented by `orient`, concluding `unit` (the
    /// lemma id by default) as `final_clause`: lazily blasted first, and once
    /// more with every division exact when that abstraction does not print,
    /// unless its sweep refuted it and only the document's size refused it
    /// (`transport/size_refusal.rs`).
    #[expect(
        clippy::too_many_arguments,
        reason = "the complete-blast document schema keeps roots, orientation, unit, and case explicit"
    )]
    pub(super) fn lemma_document(
        printer: &'p AlethePrinter<'a>,
        id: ProofId,
        prefix: &str,
        roots: &[TermId],
        orient: &Orient<'_, 'a, 'p>,
        final_clause: &str,
        unit: Option<&str>,
        case: Option<(&str, &case_split::Case)>,
    ) -> Option<String> {
        printer.check_emission_progress(0).ok()?;
        let unit = unit.map_or_else(|| id.to_string(), str::to_string);
        for lazy in [true, false] {
            printer.check_emission_progress(0).ok()?;
            let Planned {
                mut blaster,
                root,
                cnf,
                root_clause_id,
                abstracted,
                settled,
            } = Self::plan_lemma(printer, id, prefix, roots, orient, lazy, case)?;
            let document = blaster.finish_planned(&cnf, root_clause_id, root, &unit, final_clause);
            printer.check_emission_progress(0).ok()?;
            if document.is_some() || !abstracted || blaster.swept_refused_by_size {
                if document.is_some() {
                    if let Some(candidate) = settled {
                        candidate.commit(printer)?;
                    }
                }
                return document;
            }
        }
        None
    }

    /// The next exact divisions, or `Keep` when no model was found within
    /// budget. `None` is owner refusal, never a settled scheduling choice.
    fn refinement(&self, cnf: &[Vec<Literal>], roots: &[TermId]) -> Option<Refinement> {
        self.printer.check_emission_progress(0).ok()?;
        let limits = ResolutionProofLimits {
            deadline: Some(std::time::Instant::now() + MODEL_WALL),
            max_conflicts: Some(MODEL_CONFLICTS),
            max_decisions: Some(MODEL_CONFLICTS.saturating_mul(64)),
            ..ResolutionProofLimits::default()
        };
        // The solver takes neither a repeated literal nor a tautology, and
        // neither changes the models.
        let clauses = self.model_clauses(cnf)?;
        self.printer.check_emission_progress(0).ok()?;
        let (outcome, _) =
            solve_resolution_dag_counted(self.circuit.len(), &clauses, &limits, &mut || {
                self.printer.check_emission_progress(0).is_ok()
            });
        self.printer.check_emission_progress(0).ok()?;
        let Ok(ResolutionSolveOutcome::Sat(model)) = outcome else {
            return Some(Refinement::Keep);
        };
        let mut wrong = DetHashSet::default();
        for term in self.read_divisions(&model, roots)? {
            self.printer.check_emission_progress(0).ok()?;
            if self.division_is_wrong(term, &model) != Some(false) {
                wrong.insert(term);
            }
            self.printer.check_emission_progress(0).ok()?;
        }
        Some(Refinement::Blast(wrong))
    }

    fn model_clauses(&self, cnf: &[Vec<Literal>]) -> Option<Vec<Vec<Literal>>> {
        let mut clauses = Vec::with_capacity(cnf.len());
        for clause in cnf {
            self.printer.check_emission_progress(0).ok()?;
            let mut out = Vec::with_capacity(clause.len());
            let mut tautology = false;
            for lit in clause {
                self.printer.check_emission_progress(0).ok()?;
                if out.contains(&lit.negated()) {
                    tautology = true;
                    break;
                }
                if !out.contains(lit) {
                    out.push(*lit);
                }
            }
            self.printer.check_emission_progress(0).ok()?;
            if !tautology {
                clauses.push(out);
            }
        }
        self.printer.check_emission_progress(0).ok()?;
        Some(clauses)
    }

    /// The opaque divisions the model's value of `roots` depends on.
    fn read_divisions(&self, model: &[bool], roots: &[TermId]) -> Option<Vec<TermId>> {
        self.printer.check_emission_progress(0).ok()?;
        let terms = self.printer.terms;
        let mut read = Vec::new();
        let mut seen = DetHashSet::default();
        let mut stack = roots.to_vec();
        self.printer.check_emission_progress(0).ok()?;
        while let Some(term) = stack.pop() {
            self.printer.check_emission_progress(0).ok()?;
            if !seen.insert(term) {
                continue;
            }
            if self.opaque_divisions.contains(&term) {
                read.push(term);
                continue;
            }
            let value = |term: TermId| self.bool_value(term, model);
            match terms.get(term) {
                TermData::Ite(condition, then_branch, else_branch) => {
                    stack.push(*condition);
                    match value(*condition) {
                        Some(true) => stack.push(*then_branch),
                        Some(false) => stack.push(*else_branch),
                        None => stack.extend([*then_branch, *else_branch]),
                    }
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::App(Symbol::Named(name), args)
                    if matches!(name.as_str(), "and" | "or") =>
                {
                    // A decided `and` is false through any false operand, a
                    // decided `or` true through any true one.
                    let deciding = name.as_str() == "or";
                    match value(term) {
                        Some(result) if result == deciding => {
                            match args.iter().find(|arg| value(**arg) == Some(deciding)) {
                                Some(arg) => stack.push(*arg),
                                None => stack.extend(args.iter().copied()),
                            }
                        }
                        _ => stack.extend(args.iter().copied()),
                    }
                }
                TermData::App(_, args) => stack.extend(args.iter().copied()),
                _ => {}
            }
        }
        self.printer.check_emission_progress(0).ok()?;
        Some(read)
    }

    fn bool_value(&self, term: TermId, model: &[bool]) -> Option<bool> {
        let reference = self.bool_of.get(&term)?;
        Some(*model.get(reference.gate as usize)? != reference.negative())
    }

    fn word_value(&self, term: TermId, model: &[bool]) -> Option<u128> {
        let word = self.word_of_term(term)?;
        let mut value = 0_u128;
        for (index, bit) in self.words[word].bits.iter().enumerate() {
            self.printer.check_emission_progress(0).ok()?;
            let set = match self.circuit.kind(bit.gate) {
                circuit::GateKind::Const(constant) => *constant,
                _ => *model.get(bit.gate as usize)?,
            } != bit.negative();
            if set {
                value |= 1_u128.checked_shl(u32::try_from(index).ok()?)?;
            }
        }
        self.printer.check_emission_progress(0).ok()?;
        Some(value)
    }

    /// Whether the model's value of the opaque division `term` differs from
    /// what it computes; `None` when that cannot be read.
    fn division_is_wrong(&self, term: TermId, model: &[bool]) -> Option<bool> {
        let TermData::App(Symbol::Named(name), args) = self.printer.terms.get(term) else {
            return None;
        };
        let [dividend, divisor] = args.as_slice() else {
            return None;
        };
        let width = self.printer.terms.sort(term).bitvec_width()?;
        let mask = u128::MAX.checked_shr(128_u32.checked_sub(width)?)?;
        let (x, y) = (
            self.word_value(*dividend, model)?,
            self.word_value(*divisor, model)?,
        );
        let computed = match (name.as_str(), y) {
            ("bvudiv", 0) => mask,
            ("bvurem", 0) => x,
            ("bvudiv", _) => x / y,
            ("bvurem", _) => x % y,
            _ => return None,
        };
        Some(self.word_value(term, model)? != computed)
    }
}

/// Every `bvudiv`/`bvurem` application at most 128 bits wide below `roots`.
fn division_terms(printer: &AlethePrinter<'_>, roots: &[TermId]) -> Option<DetHashSet<TermId>> {
    printer.check_emission_progress(0).ok()?;
    let terms = printer.terms;
    let mut found = DetHashSet::default();
    let mut seen = DetHashSet::default();
    let mut stack = roots.to_vec();
    printer.check_emission_progress(0).ok()?;
    while let Some(term) = stack.pop() {
        printer.check_emission_progress(0).ok()?;
        if !seen.insert(term) || seen.len() > MAX_TERM_NODES {
            continue;
        }
        match terms.get(term) {
            TermData::App(Symbol::Named(name), args) => {
                let narrow = terms
                    .sort(term)
                    .bitvec_width()
                    .is_some_and(|width| width <= 128);
                if matches!(name.as_str(), "bvudiv" | "bvurem") && args.len() == 2 && narrow {
                    found.insert(term);
                }
                stack.extend(args.iter().copied());
            }
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(c, t, e) => stack.extend([*c, *t, *e]),
            _ => {}
        }
    }
    printer.check_emission_progress(0).ok()?;
    Some(found)
}

#[cfg(test)]
mod tests {
    use super::settled::{remember_settled, MAX_SETTLED_BYTES};
    use super::*;

    #[test]
    fn a_settled_abstraction_is_served_by_its_key_and_the_table_stays_bounded() {
        let kept: DetHashSet<String> = ["(bvudiv a b)".to_string()].into_iter().collect();
        remember_settled("true (= b #x01)\n(= a b)".to_string(), kept.clone());
        assert_eq!(
            settled::raw_lookup("true (= b #x01)\n(= a b)"),
            Some(kept.clone())
        );
        assert_eq!(settled::raw_lookup("false (= b #x01)\n(= a b)"), None);
        // An entry past the byte bound is never retained, and evicts nothing.
        let huge = "x".repeat(MAX_SETTLED_BYTES + 1);
        remember_settled(huge.clone(), DetHashSet::default());
        assert_eq!(settled::raw_lookup(&huge), None);
        assert_eq!(settled::raw_lookup("true (= b #x01)\n(= a b)"), Some(kept));
    }
}

#[cfg(test)]
mod cancellation_tests;
