// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The printer's use of SAT sweeping (`crate::sat_sweep`): one monolithic
//! CDCL refutation of an arithmetic miter is correct but transports to text
//! far past the document budget (the 8-bit divider's printed 46 MB, the
//! 32- and 64-bit ones past 76 MB), so a large circuit is swept into local
//! lemmas instead.
//!
//! This module only describes the circuit to the sweep — each gate's
//! function, a theory atom as the gate its link clauses equate it with — and
//! names the printer's policy. The planned root is a TRANSPORT root: the
//! chain carries it as a literal, so the sweep never makes it a conflicting
//! clause and always leaves the final chain something to resolve.

use super::circuit::{Circuit, GateKind, SRef};
use super::AlethePrinter;
use crate::sat_sweep::{literal, split, Gate};
use ay_core::kani_compat::{DetHashMap, DetHashSet};
use ay_sat::{Literal, ResolutionDag};

/// Circuits at least this large are refuted DIRECTLY ([`refute_directly_planned`])
/// and swept when that fails; a smaller one keeps its monolithic refutation
/// when that prints within [`LIGHT_DOCUMENT_BYTES`].
pub(super) const SWEEP_FIRST_GATES: usize = 2_000;
/// A monolithic document at most this large is kept as it is. A larger one
/// (the 8-bit divider's monolithic refutation printed 46 MB) is swept, and
/// the smaller of the two documents is kept.
pub(super) const LIGHT_DOCUMENT_BYTES: usize = 4 * 1024 * 1024;
/// Largest proof body the DIRECT lane ([`refute_directly_planned`]) prints before it
/// defers to the sweep. Its measured roots print 1.7 to 7.2 MB. EXTERNAL_CODEGEN's
/// replicated byte, `zext(imm8) * 0x0101010101010101` against eight concats
/// (gate row 0667), refutes directly into a DAG whose transport ran to 80 MB
/// before the text budget refused it, at every render of one publication
/// (35-40 s each), while its sweep prints 8.5 MB.
pub(super) const DIRECT_DOCUMENT_BYTES: usize = 16 * 1024 * 1024;
/// Binary LRAT the DIRECT lane's solver call may retain ([`refute_directly`]):
/// the lane is for a root that refutes cheaply, and a proof stream that
/// outgrows twice the document the lane prints within is not one. The sweep
/// after it takes such a root.
///
/// Measured 2026-10-08 over external-codegen's corpus9 (4,087 strict queries): four
/// rows (0110 `Add_Lsr_Shift_I64`, 0289, 0300.def0, 1180), each comparing a
/// 64-bit divider with a shift, wrote the solver's own 256 MiB in 2,135 to
/// 2,617 of the lane's 5,000 conflicts (6.8 s on 0110), then declined, and
/// their sweeps refuted in about 1.5 s; capped here, each row's strict run
/// takes 4.0 to 12.6 CPU-s instead of 15.9 to 36.0. The heaviest direct
/// refutation that printed, row 1146, needs between 12.0 and 14.0 MB, and
/// none of the 592 rows whose direct lane printed changes even at half this
/// cap.
pub(super) const DIRECT_PROOF_BYTES: usize = 2 * DIRECT_DOCUMENT_BYTES;

/// A bit-vector `ite` word as the planned clauses define it (`ite.rs`): its
/// free value bits, the condition, both branches' bits, and the two bit
/// equalities `E_then`/`E_else` of `(cl (not c) E_then)` and `(cl c E_else)`.
pub(super) struct GuardedIte {
    pub(super) condition: SRef,
    pub(super) value: Vec<SRef>,
    pub(super) then_bits: Vec<SRef>,
    pub(super) else_bits: Vec<SRef>,
    pub(super) equalities: [SRef; 2],
    /// Per bit, its conjunct of each equality: `(= value_i then_i)` and
    /// `(= value_i else_i)`.
    pub(super) links: Vec<[SRef; 2]>,
}

/// Compatibility for the existing owner controls over the complete circuit.
#[cfg(test)]
pub(super) fn refute(
    printer: &AlethePrinter<'_>,
    circuit: &Circuit,
    guarded_ites: &[GuardedIte],
    cnf: &[Vec<Literal>],
    root_clause_id: u64,
) -> Option<ResolutionDag> {
    refute_planned(
        printer,
        circuit,
        circuit.len(),
        guarded_ites,
        cnf,
        root_clause_id,
    )
}

/// Sweep `cnf` over exactly the `variables` gates it was planned over.
/// A case split may mint later gates; neither the refutation nor its retained
/// key depends on those gates. Every lane polls both the original printer
/// owner and its `CompleteBlastAsk` stop besides its own narrowing envelope.
pub(super) fn refute_planned(
    printer: &AlethePrinter<'_>,
    circuit: &Circuit,
    variables: usize,
    guarded_ites: &[GuardedIte],
    cnf: &[Vec<Literal>],
    root_clause_id: u64,
) -> Option<ResolutionDag> {
    printer.complete_blast_progress()?;
    let root_index = usize::try_from(root_clause_id.checked_sub(1)?).ok()?;
    let mut gates = circuit_gates(circuit, variables, cnf, root_index)?;
    printer.complete_blast_progress()?;
    guarded_ite_gates(circuit, guarded_ites, &mut gates);
    printer.complete_blast_progress()?;
    let limits = crate::sat_sweep::SweepLimits::standalone();
    let result = crate::sat_sweep::refute(gates, cnf, &[root_index], true, limits, &mut || {
        printer.complete_blast_progress().is_some()
    });
    printer.complete_blast_progress()?;
    result
}

/// Refute `cnf` without sweeping it: the sweep's closing refutation of the
/// root before any lemma, at the price of ONE candidate lemma (the sweep's
/// `LEMMA_CONFLICTS`). It reads the planned clauses exactly as the sweep
/// does, and its chains are replayed like the sweep's before the transport
/// replays them again.
///
/// Measured roots that refute this way: the `(a / b) op c` miters over one
/// shared divider, 129 to 1,712 conflicts at 32 and 64 bits. The divider
/// against a shift (`x / 4 = x >> 2`, 32-bit) needs 7,767 and a transport
/// past the text budget, so it is still swept.
///
/// Within the same allowance it may find a model of the CNF instead
/// ([`crate::sat_sweep::Direct::Satisfiable`]): the lemma is false.
#[cfg(test)]
pub(super) fn refute_directly(
    printer: &AlethePrinter<'_>,
    circuit: &Circuit,
    guarded_ites: &[GuardedIte],
    cnf: &[Vec<Literal>],
    root_clause_id: u64,
) -> Option<ResolutionDag> {
    match refute_directly_planned(
        printer,
        circuit,
        circuit.len(),
        guarded_ites,
        cnf,
        root_clause_id,
    ) {
        crate::sat_sweep::Direct::Refuted(dag) => Some(dag),
        crate::sat_sweep::Direct::Satisfiable | crate::sat_sweep::Direct::Undecided => None,
    }
}

/// The direct lane over the same immutable planned gate count.
pub(super) fn refute_directly_planned(
    printer: &AlethePrinter<'_>,
    circuit: &Circuit,
    variables: usize,
    guarded_ites: &[GuardedIte],
    cnf: &[Vec<Literal>],
    root_clause_id: u64,
) -> crate::sat_sweep::Direct {
    direct_planned(
        printer,
        circuit,
        variables,
        guarded_ites,
        cnf,
        root_clause_id,
    )
    .unwrap_or(crate::sat_sweep::Direct::Undecided)
}

fn direct_planned(
    printer: &AlethePrinter<'_>,
    circuit: &Circuit,
    variables: usize,
    guarded_ites: &[GuardedIte],
    cnf: &[Vec<Literal>],
    root_clause_id: u64,
) -> Option<crate::sat_sweep::Direct> {
    printer.complete_blast_progress()?;
    let root_index = usize::try_from(root_clause_id.checked_sub(1)?).ok()?;
    let mut gates = circuit_gates(circuit, variables, cnf, root_index)?;
    printer.complete_blast_progress()?;
    guarded_ite_gates(circuit, guarded_ites, &mut gates);
    printer.complete_blast_progress()?;
    let limits = crate::sat_sweep::SweepLimits {
        total_conflicts: crate::sat_sweep::LEMMA_CONFLICTS,
        ..crate::sat_sweep::SweepLimits::standalone()
    };
    let result = crate::sat_sweep::refute_directly(
        gates,
        cnf,
        &[root_index],
        true,
        limits,
        DIRECT_PROOF_BYTES,
        &mut || printer.complete_blast_progress().is_some(),
    );
    printer.complete_blast_progress()?;
    Some(result)
}

/// Conflicts a case split may spend ([`refute_by_cases`]): row 1257's
/// spends 14,959.
const SPLIT_CONFLICTS: u64 = 200_000;
/// Wall-clock bound of a case split: row 1257's takes 4.3 s.
const SPLIT_WALL: std::time::Duration = std::time::Duration::from_secs(30);

/// Refute `cnf` by splitting on the guards its root leaves open
/// (`crate::sat_sweep::split`), refuting the cases `leaves` admits; no
/// refutation when it has no guard open or the split does not close within
/// [`SPLIT_CONFLICTS`] and [`SPLIT_WALL`].
pub(super) fn refute_by_cases(
    printer: &AlethePrinter<'_>,
    circuit: &Circuit,
    cnf: &[Vec<Literal>],
    root_clause_id: u64,
    definitions: &[split::Definition],
    implied: &[usize],
    leaves: split::Leaves,
) -> split::Outcome {
    let declined = split::Outcome {
        refutation: None,
        spent: 0,
        worked: 0,
        deferred: false,
    };
    if printer.complete_blast_progress().is_none() {
        return declined;
    }
    let Some(root_index) = root_clause_id
        .checked_sub(1)
        .and_then(|index| usize::try_from(index).ok())
    else {
        return declined;
    };
    let Some(gates) = circuit_gates(circuit, circuit.len(), cnf, root_index) else {
        return declined;
    };
    if printer.complete_blast_progress().is_none() {
        return declined;
    }
    // The local ceiling only narrows the original sticky caller control.
    let limits = crate::sat_sweep::SweepLimits {
        total_conflicts: SPLIT_CONFLICTS,
        deadline: std::time::Instant::now() + SPLIT_WALL,
        ..crate::sat_sweep::SweepLimits::standalone()
    };
    let result = split::refute(
        gates,
        cnf,
        &[root_index],
        true,
        definitions,
        implied,
        leaves,
        limits,
        &mut || printer.complete_blast_progress().is_some(),
    );
    if printer.complete_blast_progress().is_none() {
        return declined;
    }
    result
}

/// Every value bit of a bit-vector `ite` is `ite(c, then_i, else_i)`, defined
/// by the guarded clauses over the two bit equalities rather than by a gate.
///
/// Left an input, a value bit simulated as noise and cut every cone in two:
/// measured 2026-09-30 on external-codegen's 64-bit `SDIV` definitional rows, whose
/// root compares a four-way `ite` of dividers with the dividend, the closing
/// refutation over the root's cone was SATISFIABLE (322 variables), and only
/// the fallback over every clause closed — printing 80 MB, past the budget.
fn guarded_ite_gates(circuit: &Circuit, guarded_ites: &[GuardedIte], gates: &mut [Gate]) {
    for ite in guarded_ites {
        let equalities = [
            ite.equalities[0].gate as usize,
            ite.equalities[1].gate as usize,
        ];
        let bits = ite.value.iter().zip(&ite.then_bits).zip(&ite.else_bits);
        for (((value, then_bit), else_bit), links) in bits.zip(&ite.links) {
            let free = value.nots == 0 && matches!(circuit.kind(value.gate), GateKind::Atom(_));
            let Some(slot) = gates.get_mut(value.gate as usize) else {
                continue;
            };
            if free && matches!(slot, Gate::Input) {
                *slot = Gate::GuardedIte {
                    condition: sref_literal(ite.condition),
                    then_bit: sref_literal(*then_bit),
                    else_bit: sref_literal(*else_bit),
                    equalities,
                    links: [links[0].gate as usize, links[1].gate as usize],
                };
            }
        }
    }
}

fn sref_literal(reference: SRef) -> Literal {
    literal(reference.gate as usize, reference.negative())
}

/// The function of each of the first `variables` gates. A theory atom is an
/// alias of the gate its two binary link clauses equate it with, or an input
/// when it has none. `None` when the circuit has fewer gates.
fn circuit_gates(
    circuit: &Circuit,
    variables: usize,
    cnf: &[Vec<Literal>],
    root_index: usize,
) -> Option<Vec<Gate>> {
    let variables = u32::try_from(variables)
        .ok()
        .filter(|&count| count as usize <= circuit.len())?;
    // Binary clauses by their first literal, both orientations.
    let mut binary: DetHashMap<usize, DetHashSet<usize>> = DetHashMap::default();
    for (index, clause) in cnf.iter().enumerate() {
        if let [a, b] = clause.as_slice() {
            if index != root_index {
                binary.entry(a.index()).or_default().insert(b.index());
                binary.entry(b.index()).or_default().insert(a.index());
            }
        }
    }
    let mut nodes = Vec::with_capacity(variables as usize);
    for gate in 0..variables {
        let lit = |reference: &SRef| sref_literal(*reference);
        nodes.push(match circuit.kind(gate) {
            GateKind::Atom(_) | GateKind::Theory(_) => Gate::Input,
            GateKind::Const(value) => Gate::Const(*value),
            GateKind::And(args) => Gate::And(args.iter().map(lit).collect()),
            GateKind::Or(args) => Gate::Or(args.iter().map(lit).collect()),
            GateKind::Xor(a, b) => Gate::Xor(vec![lit(a), lit(b)]),
            GateKind::Implies(a, b) => Gate::Or(vec![lit(a).negated(), lit(b)]),
            GateKind::Iff(a, b) => Gate::Iff(lit(a), lit(b)),
            GateKind::Ite(c, a, b) => Gate::Ite(lit(c), lit(a), lit(b)),
        });
    }
    // `(cl (not t) x)` and `(cl t (not x))`: `t` is `x`.
    for (gate, node) in nodes.iter_mut().enumerate() {
        if !matches!(circuit.kind(gate as u32), GateKind::Theory(_)) {
            continue;
        }
        let (Some(implied), Some(converse)) = (
            binary.get(&literal(gate, true).index()),
            binary.get(&literal(gate, false).index()),
        ) else {
            continue;
        };
        let mut partners: Vec<usize> = implied.iter().copied().collect();
        partners.sort_unstable();
        let partner = partners
            .into_iter()
            .map(Literal::from_index)
            .filter(|other| other.variable().index() != gate)
            .find(|other| converse.contains(&other.negated().index()));
        if let Some(partner) = partner {
            *node = Gate::Alias(partner);
        }
    }
    Some(nodes)
}
