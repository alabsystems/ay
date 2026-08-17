// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Candidate-space pruning for solver-driven AArch64 superoptimization.
//!
//! This module is intentionally small: it does not claim that a sequence is
//! equivalent to a source hot path. It builds and ranks the finite candidate
//! set that will later be discharged by external code generation proof queries. Keeping this
//! step deterministic lets the verifier spend work on plausible live code
//! instead of dead scratch writes and duplicate commutative forms.
//!
//! ## STATUS (2026-07-14 triage)
//!
//! #8526 foundation whose follow-up lanes never landed; frozen since the
//! 2026-05-24 publish squash, same situation as solver_program_runtime.rs.
//! Zero callers.
//! See the development design notes

use std::cmp::Ordering;
use std::collections::BTreeSet;

/// A compact register universe for short AArch64 hot-path candidates.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SuperoptReg {
    /// ABI input/output register x0.
    X0,
    /// ABI input/output register x1.
    X1,
    /// ABI input/output register x2.
    X2,
    /// ABI input/output register x3.
    X3,
    /// ABI input/output register x4.
    X4,
    /// ABI input/output register x5.
    X5,
    /// Internal scratch register.
    Scratch0,
    /// Internal scratch register.
    Scratch1,
    /// Internal scratch register.
    Scratch2,
    /// Internal scratch register.
    Scratch3,
}

/// A small AArch64 integer-operation subset used by the first synthesis pass.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Aarch64Template {
    /// Register move.
    Mov,
    /// Register-register add.
    Add,
    /// Register-register subtract.
    Sub,
    /// Register-register bitwise and.
    And,
    /// Register-register bitwise or.
    Orr,
    /// Register-register bitwise xor.
    Eor,
}

impl Aarch64Template {
    const fn arity(self) -> u8 {
        match self {
            Self::Mov => 1,
            Self::Add | Self::Sub | Self::And | Self::Orr | Self::Eor => 2,
        }
    }

    const fn is_commutative(self) -> bool {
        matches!(self, Self::Add | Self::And | Self::Orr | Self::Eor)
    }

    const fn latency(self) -> u16 {
        1
    }
}

/// One candidate AArch64 operation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SuperoptInst {
    /// Operation template.
    pub template: Aarch64Template,
    /// Destination register.
    pub dst: SuperoptReg,
    /// First source register.
    pub src0: SuperoptReg,
    /// Optional second source register.
    pub src1: Option<SuperoptReg>,
}

impl SuperoptInst {
    fn reads(self) -> impl Iterator<Item = SuperoptReg> {
        [Some(self.src0), self.src1].into_iter().flatten()
    }

    fn is_canonical(self) -> bool {
        match (self.template.is_commutative(), self.src1) {
            (true, Some(src1)) => self.src0 <= src1,
            _ => true,
        }
    }
}

/// A candidate instruction sequence.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SuperoptCandidate {
    insts: Vec<SuperoptInst>,
}

impl SuperoptCandidate {
    /// Return the sequence instructions.
    pub fn insts(&self) -> &[SuperoptInst] {
        &self.insts
    }

    /// Compute the static sequence cost used before equivalence checking.
    pub fn cost(&self) -> SuperoptCost {
        let latency = self.insts.iter().map(|inst| inst.template.latency()).sum();
        SuperoptCost {
            latency,
            instructions: u16::try_from(self.insts.len()).unwrap_or(u16::MAX),
            code_bytes: u16::try_from(self.insts.len().saturating_mul(4)).unwrap_or(u16::MAX),
        }
    }
}

impl Ord for SuperoptCandidate {
    fn cmp(&self, other: &Self) -> Ordering {
        self.cost()
            .cmp(&other.cost())
            .then_with(|| self.insts.cmp(&other.insts))
    }
}

impl PartialOrd for SuperoptCandidate {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// Static cost for a candidate sequence.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SuperoptCost {
    /// Sum of template latencies.
    pub latency: u16,
    /// Number of instructions.
    pub instructions: u16,
    /// Encoded code size in bytes.
    pub code_bytes: u16,
}

impl Ord for SuperoptCost {
    fn cmp(&self, other: &Self) -> Ordering {
        self.latency
            .cmp(&other.latency)
            .then_with(|| self.instructions.cmp(&other.instructions))
            .then_with(|| self.code_bytes.cmp(&other.code_bytes))
    }
}

impl PartialOrd for SuperoptCost {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// Search-space limits and liveness contract for a short superopt query.
#[derive(Clone, Debug)]
pub struct SuperoptSearch {
    /// Registers holding source values at entry.
    pub live_inputs: Vec<SuperoptReg>,
    /// Registers whose final values are semantically observable.
    pub live_outputs: Vec<SuperoptReg>,
    /// Scratch registers that may be used only when their values feed outputs.
    pub scratch: Vec<SuperoptReg>,
    /// Allowed operation templates.
    pub templates: Vec<Aarch64Template>,
    /// Maximum sequence length.
    pub max_len: usize,
    /// Maximum number of candidates to return after ranking.
    pub max_candidates: usize,
}

/// Equivalence result supplied by the later verifier.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EquivalenceResult {
    /// The verifier proved candidate equivalence and emitted a certificate id.
    Equivalent { certificate_id: String },
    /// The verifier found a concrete counterexample.
    Counterexample,
    /// The verifier timed out or could not decide within budget.
    Unknown,
}

/// A candidate paired with a verifier result.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifiedSuperoptCandidate {
    /// Candidate sequence.
    pub candidate: SuperoptCandidate,
    /// Verifier outcome for the candidate.
    pub result: EquivalenceResult,
}

/// Enumerate liveness-valid candidates, sorted by static cost.
pub fn enumerate_superopt_candidates(search: &SuperoptSearch) -> Vec<SuperoptCandidate> {
    if search.live_outputs.is_empty()
        || search.templates.is_empty()
        || search.max_len == 0
        || search.max_candidates == 0
    {
        return Vec::new();
    }

    let live_inputs = sorted_unique(&search.live_inputs);
    let live_outputs = sorted_unique(&search.live_outputs);
    let scratch = sorted_unique(&search.scratch);
    let templates = sorted_unique(&search.templates);
    let writable = sorted_unique(
        &live_outputs
            .iter()
            .chain(scratch.iter())
            .copied()
            .collect::<Vec<_>>(),
    );
    if writable.is_empty() {
        return Vec::new();
    }

    let protected_inputs: BTreeSet<_> = live_inputs
        .iter()
        .copied()
        .filter(|reg| !live_outputs.contains(reg))
        .collect();

    let mut out = BTreeSet::new();
    let mut current = Vec::new();
    let available: BTreeSet<_> = live_inputs.iter().copied().collect();
    enumerate_depth(
        &templates,
        &writable,
        &protected_inputs,
        &live_outputs,
        search.max_len,
        &available,
        &mut current,
        &mut out,
    );

    out.into_iter().take(search.max_candidates).collect()
}

/// Select the cheapest proven-equivalent candidate.
pub fn choose_cheapest_equivalent(
    verified: impl IntoIterator<Item = VerifiedSuperoptCandidate>,
) -> Option<VerifiedSuperoptCandidate> {
    verified
        .into_iter()
        .filter(|item| matches!(item.result, EquivalenceResult::Equivalent { .. }))
        .min_by(|left, right| left.candidate.cmp(&right.candidate))
}

fn enumerate_depth(
    templates: &[Aarch64Template],
    writable: &[SuperoptReg],
    protected_inputs: &BTreeSet<SuperoptReg>,
    live_outputs: &[SuperoptReg],
    max_len: usize,
    available: &BTreeSet<SuperoptReg>,
    current: &mut Vec<SuperoptInst>,
    out: &mut BTreeSet<SuperoptCandidate>,
) {
    if !current.is_empty() && final_liveness_ok(current, live_outputs) {
        out.insert(SuperoptCandidate {
            insts: current.clone(),
        });
    }
    if current.len() == max_len {
        return;
    }

    for &template in templates {
        for &dst in writable {
            if protected_inputs.contains(&dst) {
                continue;
            }
            for &src0 in available {
                if template.arity() == 1 {
                    push_inst(
                        SuperoptInst {
                            template,
                            dst,
                            src0,
                            src1: None,
                        },
                        available,
                        current,
                        templates,
                        writable,
                        protected_inputs,
                        live_outputs,
                        max_len,
                        out,
                    );
                    continue;
                }

                for &src1 in available {
                    push_inst(
                        SuperoptInst {
                            template,
                            dst,
                            src0,
                            src1: Some(src1),
                        },
                        available,
                        current,
                        templates,
                        writable,
                        protected_inputs,
                        live_outputs,
                        max_len,
                        out,
                    );
                }
            }
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn push_inst(
    inst: SuperoptInst,
    available: &BTreeSet<SuperoptReg>,
    current: &mut Vec<SuperoptInst>,
    templates: &[Aarch64Template],
    writable: &[SuperoptReg],
    protected_inputs: &BTreeSet<SuperoptReg>,
    live_outputs: &[SuperoptReg],
    max_len: usize,
    out: &mut BTreeSet<SuperoptCandidate>,
) {
    if !inst.is_canonical() {
        return;
    }

    let mut next_available = available.clone();
    next_available.insert(inst.dst);
    current.push(inst);
    enumerate_depth(
        templates,
        writable,
        protected_inputs,
        live_outputs,
        max_len,
        &next_available,
        current,
        out,
    );
    current.pop();
}

fn final_liveness_ok(insts: &[SuperoptInst], live_outputs: &[SuperoptReg]) -> bool {
    let mut live: BTreeSet<_> = live_outputs.iter().copied().collect();
    let mut defined_outputs = BTreeSet::new();

    for inst in insts.iter().rev().copied() {
        if !live.remove(&inst.dst) {
            return false;
        }
        if live_outputs.contains(&inst.dst) {
            defined_outputs.insert(inst.dst);
        }
        live.extend(inst.reads());
    }

    live_outputs
        .iter()
        .all(|output| defined_outputs.contains(output))
}

fn sorted_unique<T: Copy + Ord>(items: &[T]) -> Vec<T> {
    items
        .iter()
        .copied()
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect()
}

#[cfg(test)]
mod tests;
