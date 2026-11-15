// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact Bool/BV circuits with checked gate clauses and actual SAT antecedents.
//! Pure definitions share terms; every gate is independently re-derived by
//! Alethe. The solver's RUP references select standard resolution premises.

use super::*;
use ay_sat::{Literal, ResolutionProofLimits};
use std::time::{Duration, Instant};

mod addition;
#[cfg(test)]
mod addition_offset_tests;
mod address;
#[cfg(test)]
mod address_tests;
mod arithmetic;
#[cfg(test)]
mod arithmetic_tests;
mod arrays;
#[cfg(test)]
mod authored_literal_tests;
#[cfg(test)]
mod bitwise_tests;
mod conditional;
#[cfg(test)]
mod congruence_tests;
mod disjoint;
mod gates;
mod indexed;
mod lower;
#[cfg(test)]
mod memory_tests;
mod offset;
mod order;
mod outside_frame;
#[cfg(test)]
mod product_tests;
#[cfg(test)]
mod respell_tests;
#[cfg(test)]
mod signed_tests;
mod source;
#[cfg(test)]
mod tests;
mod words;
mod zero_extend;
#[cfg(test)]
mod zero_extend_shared_tests;
#[cfg(test)]
mod zero_extend_tests;

const MAX_VARIABLES: usize = 16_000;
const MAX_CLAUSES: usize = 80_000;
const MAX_LITERALS: usize = 320_000;
/// Outer hang guard of one circuit refutation, shared by all its parts. NOT a
/// budget: the counted caps in `refute` and the printer's work budget decide
/// whether a checked derivation is printed. It replaces a three-second
/// deadline that refused the 128-bit common-output certificate (0.65 s alone)
/// under 54 busy spinners (measured 2026-09-23). The slowest counted
/// exhaustion measured here, four-operand 128-bit addition reassociation
/// running out its 100,000 conflicts, took 3.3 s in the test profile.
const REFUTATION_HANG_GUARD: Duration = Duration::from_secs(300);

#[derive(Clone)]
struct Word {
    bits: Vec<i32>,
    equality: Equality,
}

struct Circuit<'a, 'p, 't> {
    proof: &'a mut PackedProof<'p, 't>,
    atoms: Vec<String>,
    nodes: DetHashMap<String, i32>,
    clauses: Vec<Vec<Literal>>,
    units: Vec<String>,
    literals: usize,
    words: DetHashMap<TermId, Word>,
    // Closed universal facts only; local to this Circuit's common root scope.
    zero_extend_lemmas: DetHashMap<zero_extend::TemplateKey, zero_extend::Universal>,
    zero_extend_scope: std::rc::Rc<()>,
    addresses: DetHashMap<TermId, address::Address>,
    arrays: DetHashMap<TermId, Vec<arrays::Write>>,
    base_reads: Vec<arrays::BaseRead>,
    base_read_slots: DetHashMap<(TermId, TermId), usize>,
    booleans: DetHashMap<TermId, (i32, Equality)>,
    /// One subtractor word per pair of offset words (`offset.rs`).
    differences: DetHashMap<(TermId, TermId), Word>,
    /// The root's equalities: only a reading that pays is bridged.
    offset_shares: ay_core::BvOffsetShares,
    disjoint: Option<disjoint::Disjoint>,
    deadline: Option<Instant>,
    refutation_parts: usize,
}

impl AlethePrinter<'_> {
    pub(in crate::alethe_printer) fn format_bv_circuit_refutation(
        &self,
        id: ProofId,
        clause: &[TermId],
    ) -> Option<String> {
        let [negative] = clause else { return None };
        self.terms.entry_stamp(*negative)?;
        let TermData::Not(root) = self.terms.get(*negative) else {
            return None;
        };
        if self.terms.sort(*negative) != &Sort::Bool || self.terms.sort(*root) != &Sort::Bool {
            return None;
        }
        source::preflight(self, *root)?;
        let text = self.format_term(*root);
        let goal = format!("(not {text})");
        if self.format_term(*negative) != goal {
            return None;
        }
        let mut proof = PackedProof::new(self, id)?;
        let mut disjoint =
            match crate::checker::bv_bitblast::disjoint::Shape::recognize(self.terms, clause) {
                Some(shape) => Some(disjoint::prove(&mut proof, shape)?),
                None => None,
            };
        let end = proof.fresh();
        let assumption = proof.fresh();
        proof.append(&format!(
            "(anchor :step {end})\n(assume {assumption} {text})\n"
        ))?;
        if let Some(info) = &mut disjoint {
            info.guard_unit = info.collect_guard(&mut proof, *root, &assumption)?;
        }
        let mut circuit = Circuit::new(&mut proof);
        circuit.disjoint = disjoint;
        let mut room = MAX_VARIABLES;
        self.check_emission_progress(id.0).ok()?;
        circuit
            .offset_shares
            .count_reachable(self.terms, [*root], false, &mut || {
                room = room.saturating_sub(1);
                room > 0 && self.check_emission_progress(id.0).is_ok()
            });
        self.check_emission_progress(id.0).ok()?;
        if let Some(shape) =
            crate::checker::bv_bitblast::proof_producing_control::outside_frame_candidate(
                self.terms, clause,
            )
        {
            circuit.prove_local_property(*root, &assumption, shape)?;
        }
        let (bit, equality) = circuit.boolean(*root, 0)?;
        let unit = circuit.proof.transport_unit(&equality, &assumption)?;
        circuit.input(vec![bit], unit)?;
        circuit.assert_read_consistency()?;
        circuit.refute()?;
        proof.named_step(
            &end,
            &format!("{goal} false"),
            "subproof",
            &[],
            &format!(" :discharge ({assumption})"),
        )?;
        let not_false = proof.step("(not false)", "false", &[])?;
        proof.named_step(
            &id.to_string(),
            &goal,
            "resolution",
            &[&end, &not_false],
            "",
        )?;
        proof.definitions.push_str(&proof.out);
        Some(proof.definitions)
    }
}

impl<'a, 'p, 't> Circuit<'a, 'p, 't> {
    fn new(proof: &'a mut PackedProof<'p, 't>) -> Self {
        Self {
            proof,
            atoms: Vec::new(),
            nodes: DetHashMap::default(),
            clauses: Vec::new(),
            units: Vec::new(),
            literals: 0,
            words: DetHashMap::default(),
            zero_extend_lemmas: DetHashMap::default(),
            zero_extend_scope: std::rc::Rc::new(()),
            addresses: DetHashMap::default(),
            arrays: DetHashMap::default(),
            base_reads: Vec::new(),
            base_read_slots: DetHashMap::default(),
            booleans: DetHashMap::default(),
            differences: DetHashMap::default(),
            offset_shares: ay_core::BvOffsetShares::default(),
            disjoint: None,
            deadline: None,
            refutation_parts: 1,
        }
    }

    fn text(&self, literal: i32) -> Option<String> {
        let index = usize::try_from(literal.unsigned_abs())
            .ok()?
            .checked_sub(1)?;
        let atom = self.atoms.get(index)?;
        Some(if literal < 0 {
            format!("(not {atom})")
        } else {
            atom.clone()
        })
    }

    fn input(&mut self, clause: Vec<i32>, step: String) -> Option<()> {
        self.literals = self.literals.checked_add(clause.len())?;
        if self.clauses.len() >= MAX_CLAUSES || self.literals > MAX_LITERALS {
            return None;
        }
        self.clauses
            .push(clause.into_iter().map(Literal::from_dimacs).collect());
        self.units.push(step);
        Some(())
    }

    fn refute(&mut self) -> Option<()> {
        let deadline = *self
            .deadline
            .get_or_insert_with(|| Instant::now() + REFUTATION_HANG_GUARD);
        let parts = self.refutation_parts;
        let mut limits = ResolutionProofLimits {
            deadline: Some(deadline),
            max_num_vars: MAX_VARIABLES,
            max_input_clauses: MAX_CLAUSES,
            max_input_literals: MAX_LITERALS,
            max_input_bytes: 32 * 1024 * 1024,
            max_conflicts: Some(100_000 / parts as u64),
            max_decisions: Some(1_000_000 / parts as u64),
            max_proof_output_bytes: 32 * 1024 * 1024 / parts,
            max_derived_steps: 100_000 / parts,
            max_derived_literals: 1_000_000 / parts,
            max_hints: 4_000_000 / parts,
            max_codec_bytes: 128 * 1024 * 1024 / parts,
            ..ResolutionProofLimits::default()
        };
        limits.validation.max_work /= parts as u64;
        self.proof.printer.charge(self.literals as u64);
        let dag = crate::resolution_dag_memo::prove_unsat_resolution_dag_with_limits_and_cancellation_memoized(
            self.atoms.len(),
            &self.clauses,
            &limits,
            &mut || !self.proof.printer.work_budget_exhausted(),
        )
        .ok()?;
        let mut steps: DetHashMap<u64, String> = self
            .units
            .iter()
            .enumerate()
            .map(|(i, step)| (i as u64 + 1, step.clone()))
            .collect();
        for derived in &dag.derived {
            self.proof.printer.charge(derived.rup_hints.len() as u64);
            if self.proof.printer.work_budget_exhausted() {
                return None;
            }
            let clause = derived
                .clause
                .iter()
                .map(|lit| self.text(lit.to_dimacs()))
                .collect::<Option<Vec<_>>>()?
                .join(" ");
            let premises = derived
                .rup_hints
                .iter()
                .map(|hint| steps.get(hint).cloned())
                .collect::<Option<Vec<_>>>()?;
            let premises = premises.iter().map(String::as_str).collect::<Vec<_>>();
            let step = self.proof.step(&clause, "resolution", &premises)?;
            steps.insert(derived.id, step);
        }
        let last = dag.derived.last()?;
        (last.id == dag.empty_clause_id && last.clause.is_empty()).then_some(())
    }
}

#[cfg(test)]
mod output_memory_tests;
