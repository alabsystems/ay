// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Prepare the existing tactic representation before executing SMT `apply`.
//! Boxes/strings and cleanup frontiers are priced against the original owner.
//! Cleanup is iterative even after that owner refuses; it cannot allocate.

use super::tactics::{Tactic, TacticFailure};
use ay_core::term::{reserve_counted, TermConstructionAdmission};
use ay_frontend::{ApplyTactic as A, Probe};

pub(crate) struct PreparedTactic {
    values: Vec<Tactic>,
    probes: Vec<Probe>,
    owned: bool,
}
impl PreparedTactic {
    pub(crate) fn get(&self) -> Option<&Tactic> {
        self.values.first()
    }
    pub(crate) fn requires_owned(&self) -> bool {
        self.owned
    }
}
impl Drop for PreparedTactic {
    fn drop(&mut self) {
        while let Some(tactic) = self.values.pop() {
            match tactic {
                Tactic::Then(a, b) | Tactic::OrElse(a, b) => {
                    self.values.push(*a);
                    self.values.push(*b);
                }
                Tactic::Cond(probe, a, b) => {
                    self.probes.push(probe);
                    self.values.push(*a);
                    self.values.push(*b);
                }
                Tactic::When(probe, body) => {
                    self.probes.push(probe);
                    self.values.push(*body);
                }
                Tactic::FailIf(probe) => self.probes.push(probe),
                Tactic::Repeat(body, _) | Tactic::TryFor(body, _) | Tactic::WithParams(body, _) => {
                    self.values.push(*body)
                }
                _ => {}
            }
        }
        while let Some(probe) = self.probes.pop() {
            match probe {
                Probe::Not(a) => self.probes.push(*a),
                Probe::And(a, b) | Probe::Or(a, b) | Probe::Cmp(_, a, b) => {
                    self.probes.push(*a);
                    self.probes.push(*b);
                }
                _ => {}
            }
        }
    }
}

fn stopped() -> TacticFailure {
    TacticFailure::new("original tactic preparation admission refused")
}
fn reserve<T>(
    v: &mut Vec<T>,
    n: usize,
    owner: &dyn TermConstructionAdmission,
) -> Result<(), TacticFailure> {
    reserve_counted(v, n, owner).map_err(|_| stopped())
}
fn pay(
    owner: &dyn TermConstructionAdmission,
    work: usize,
    bytes: usize,
) -> Result<(), TacticFailure> {
    owner.admit(work, bytes).map_err(|_| stopped())
}

fn children(tactic: &A) -> &[A] {
    match tactic {
        A::Then(a) | A::ParThen(a) | A::OrElse(a) | A::ParOr(a) => a,
        _ => &[],
    }
}
fn probe_count(
    root: &Probe,
    owner: &dyn TermConstructionAdmission,
) -> Result<usize, TacticFailure> {
    let mut todo = Vec::new();
    reserve(&mut todo, 1, owner)?;
    todo.push(root);
    let mut count = 0usize;
    while let Some(probe) = todo.pop() {
        pay(owner, 1, 0)?;
        count = count.checked_add(1).ok_or_else(stopped)?;
        match probe {
            Probe::Not(a) => {
                reserve(&mut todo, 1, owner)?;
                todo.push(a.as_ref());
            }
            Probe::And(a, b) | Probe::Or(a, b) | Probe::Cmp(_, a, b) => {
                reserve(&mut todo, 2, owner)?;
                todo.push(a.as_ref());
                todo.push(b.as_ref());
            }
            _ => {}
        }
    }
    Ok(count)
}

fn copy_probe(
    root: &Probe,
    arena: &mut PreparedTactic,
    owner: &dyn TermConstructionAdmission,
) -> Result<(), TacticFailure> {
    let base = arena.probes.len();
    let mut todo = Vec::new();
    reserve(&mut todo, 1, owner)?;
    todo.push((root, false));
    while let Some((probe, finish)) = todo.pop() {
        pay(owner, 1, 0)?;
        if !finish {
            match probe {
                Probe::Not(a) => {
                    reserve(&mut todo, 2, owner)?;
                    todo.push((probe, true));
                    todo.push((a, false));
                    continue;
                }
                Probe::And(a, b) | Probe::Or(a, b) | Probe::Cmp(_, a, b) => {
                    reserve(&mut todo, 3, owner)?;
                    todo.push((probe, true));
                    todo.push((b, false));
                    todo.push((a, false));
                    continue;
                }
                _ => {}
            }
        }
        // Pay BEFORE popping any owned child: a refusal leaves the whole
        // partial forest in arena's preallocated, iterative cleanup guard.
        let boxed: usize = match probe {
            Probe::Not(_) => 1,
            Probe::And(..) | Probe::Or(..) | Probe::Cmp(..) => 2,
            _ => 0,
        };
        pay(
            owner,
            boxed,
            boxed.checked_mul(size_of::<Probe>()).ok_or_else(stopped)?,
        )?;
        let copied = match probe {
            Probe::Not(_) => Probe::Not(Box::new(arena.probes.pop().ok_or_else(stopped)?)),
            Probe::And(..) | Probe::Or(..) | Probe::Cmp(..) => {
                let b = arena.probes.pop().ok_or_else(stopped)?;
                let a = arena.probes.pop().ok_or_else(stopped)?;
                match probe {
                    Probe::And(..) => Probe::And(Box::new(a), Box::new(b)),
                    Probe::Or(..) => Probe::Or(Box::new(a), Box::new(b)),
                    Probe::Cmp(op, ..) => Probe::Cmp(*op, Box::new(a), Box::new(b)),
                    _ => return Err(stopped()),
                }
            }
            Probe::Const(text) => {
                pay(owner, text.len(), text.len())?;
                Probe::Const(text.clone())
            }
            // Explicit closed scalar vocabulary: a future payload-bearing
            // probe must acquire real copy accounting, not a wildcard clone.
            Probe::NumConsts
            | Probe::NumExprs
            | Probe::Size
            | Probe::Depth
            | Probe::NumBoolConsts
            | Probe::NumArithConsts
            | Probe::NumBvConsts
            | Probe::HasQuantifiers
            | Probe::IsPropositional
            | Probe::IsQfbv
            | Probe::IsQflia
            | Probe::IsQflra
            | Probe::IsQflira
            | Probe::IsLia
            | Probe::IsLra
            | Probe::IsLira
            | Probe::IsQfnia
            | Probe::IsQfnra
            | Probe::IsNia
            | Probe::IsNra
            | Probe::HasPatterns
            | Probe::IsIlp
            | Probe::IsNira
            | Probe::IsPb
            | Probe::IsQuasiPb
            | Probe::IsQfaufbv
            | Probe::IsQfauflia
            | Probe::IsQfbvEq
            | Probe::IsQffp
            | Probe::IsQffpbv
            | Probe::IsQffplra
            | Probe::IsQfufnra
            | Probe::IsUnbounded
            | Probe::AckrBoundProbe
            | Probe::ArithAvgBw
            | Probe::ArithMaxBw
            | Probe::ArithAvgDeg
            | Probe::ArithMaxDeg
            | Probe::Memory
            | Probe::ProduceModel
            | Probe::ProduceProofs
            | Probe::ProduceUnsatCores => probe.clone(),
        };
        arena.probes.push(copied);
        owner.check().map_err(|_| stopped())?;
    }
    if arena.probes.len() != base + 1 {
        return Err(stopped());
    }
    Ok(())
}

impl Tactic {
    pub(crate) fn prepare_apply(
        root: &A,
        owner: &dyn TermConstructionAdmission,
    ) -> Result<PreparedTactic, TacticFailure> {
        let mut pending = Vec::new();
        reserve(&mut pending, 1, owner)?;
        pending.push(root);
        let mut nodes = 0usize;
        let mut probes = 0usize;
        let mut edges = 0usize;
        let mut owned = false;
        while let Some(node) = pending.pop() {
            pay(owner, 1, 0)?;
            nodes = nodes.checked_add(1).ok_or_else(stopped)?;
            let list = children(node);
            reserve(&mut pending, list.len(), owner)?;
            pending.extend(list);
            edges = edges.checked_add(list.len()).ok_or_else(stopped)?;
            match node {
                A::FieldSimplify
                | A::FieldUnique
                | A::FieldSolve
                | A::FieldSat
                | A::FieldToBv
                | A::Simplify
                | A::PropagateValues
                | A::SolveEqs => {
                    owned = true;
                }
                A::Repeat(a, _) | A::TryFor(a, _) | A::UsingParams(a, _) => {
                    if matches!(node, A::TryFor(..) | A::UsingParams(..)) {
                        owned = true;
                    }
                    reserve(&mut pending, 1, owner)?;
                    pending.push(a.as_ref());
                    edges = edges.checked_add(1).ok_or_else(stopped)?;
                }
                A::When(probe, a) => {
                    probes = probes
                        .checked_add(probe_count(probe, owner)?)
                        .ok_or_else(stopped)?;
                    reserve(&mut pending, 1, owner)?;
                    pending.push(a.as_ref());
                    edges = edges.checked_add(1).ok_or_else(stopped)?;
                }
                A::FailIf(probe) => {
                    probes = probes
                        .checked_add(probe_count(probe, owner)?)
                        .ok_or_else(stopped)?
                }
                A::Cond(probe, a, b) => {
                    probes = probes
                        .checked_add(probe_count(probe, owner)?)
                        .ok_or_else(stopped)?;
                    reserve(&mut pending, 2, owner)?;
                    pending.push(a.as_ref());
                    pending.push(b.as_ref());
                    edges = edges.checked_add(2).ok_or_else(stopped)?;
                }
                _ => {}
            }
        }
        let capacity = nodes.checked_add(edges).ok_or_else(stopped)?;
        let mut arena = PreparedTactic {
            values: Vec::new(),
            probes: Vec::new(),
            owned,
        };
        reserve(&mut arena.values, capacity, owner)?;
        reserve(&mut arena.probes, probes, owner)?;
        let mut todo = Vec::new();
        reserve(&mut todo, nodes.checked_mul(2).ok_or_else(stopped)?, owner)?;
        todo.push((root, false));
        while let Some((node, finish)) = todo.pop() {
            pay(owner, 1, 0)?;
            if !finish {
                todo.push((node, true));
                match node {
                    A::Then(a) | A::ParThen(a) | A::OrElse(a) | A::ParOr(a) => {
                        for child in a.iter().rev() {
                            todo.push((child, false));
                        }
                    }
                    A::Repeat(a, _) | A::TryFor(a, _) | A::UsingParams(a, _) | A::When(_, a) => {
                        todo.push((a, false))
                    }
                    A::Cond(_, a, b) => {
                        todo.push((b, false));
                        todo.push((a, false));
                    }
                    _ => {}
                }
                continue;
            }
            let list = children(node);
            if matches!(
                node,
                A::Then(_) | A::ParThen(_) | A::OrElse(_) | A::ParOr(_)
            ) {
                let count = list.len();
                let boxes = count.saturating_sub(1).checked_mul(2).ok_or_else(stopped)?;
                pay(
                    owner,
                    boxes,
                    boxes.checked_mul(size_of::<Tactic>()).ok_or_else(stopped)?,
                )?;
                let start = arena.values.len().checked_sub(count).ok_or_else(stopped)?;
                let mut values = arena.values.drain(start..);
                let first = values.next().unwrap_or(Tactic::Skip);
                let composed = values.fold(first, |a, b| {
                    if matches!(node, A::Then(_) | A::ParThen(_)) {
                        a.then(b)
                    } else {
                        a.or_else(b)
                    }
                });
                arena.values.push(composed);
                continue;
            }
            if let A::When(probe, _) | A::FailIf(probe) | A::Cond(probe, ..) = node {
                copy_probe(probe, &mut arena, owner)?;
            }
            let boxes: usize = match node {
                A::Repeat(..) | A::When(..) => 1,
                A::Cond(..) => 2,
                A::TryFor(..) | A::UsingParams(..) => 1,
                _ => 0,
            };
            pay(
                owner,
                boxes,
                boxes.checked_mul(size_of::<Tactic>()).ok_or_else(stopped)?,
            )?;
            let tactic = match node {
                A::Repeat(_, bound) => {
                    Tactic::Repeat(Box::new(arena.values.pop().ok_or_else(stopped)?), *bound)
                }
                A::When(_, _) => {
                    let body = arena.values.pop().ok_or_else(stopped)?;
                    Tactic::When(arena.probes.pop().ok_or_else(stopped)?, Box::new(body))
                }
                A::FailIf(_) => Tactic::FailIf(arena.probes.pop().ok_or_else(stopped)?),
                A::Cond(..) => {
                    let b = arena.values.pop().ok_or_else(stopped)?;
                    let a = arena.values.pop().ok_or_else(stopped)?;
                    Tactic::Cond(
                        arena.probes.pop().ok_or_else(stopped)?,
                        Box::new(a),
                        Box::new(b),
                    )
                }
                A::TryFor(_, ms) => Tactic::TryFor(
                    Box::new(arena.values.pop().ok_or_else(stopped)?),
                    u32::try_from(*ms)
                        .map_err(|_| TacticFailure::new("tactic timeout exceeds uint32"))?,
                ),
                A::UsingParams(_, params) => {
                    let mut configured = super::tactic_parameters::TacticParameters::default();
                    for (key, value) in params {
                        use super::tactic_parameters::TacticParameterValue as V;
                        use ay_frontend::ParamValue;
                        let bytes = key
                            .len()
                            .checked_add(match value {
                                ParamValue::Sym(text) => text.len(),
                                _ => 0,
                            })
                            .ok_or_else(stopped)?;
                        pay(owner, bytes, 0)?;
                        let value = match value {
                            ParamValue::Bool(v) => V::Bool(*v),
                            ParamValue::Int(n) => {
                                u32::try_from(*n).map(V::UInt).unwrap_or(V::Unsupported)
                            }
                            _ => V::Unsupported,
                        };
                        configured.set(key, value)?;
                    }
                    Tactic::WithParams(
                        Box::new(arena.values.pop().ok_or_else(stopped)?),
                        configured,
                    )
                }
                A::FieldSimplify
                | A::FieldUnique
                | A::FieldSolve
                | A::FieldSat
                | A::FieldToBv
                | A::Skip
                | A::Fail
                | A::Simplify
                | A::ElimAnd
                | A::SolveEqs
                | A::PropagateValues
                | A::PropagateIneqs
                | A::QeLight
                | A::Qe
                | A::Nnf
                | A::TseitinCnf
                | A::BitBlast
                | A::SplitClause
                | A::CtxSolverSimplify
                | A::ElimTermIte
                | A::BlastTermIte
                | A::Der
                | A::DistributeForall
                | A::ReduceArgs
                | A::MaxBvSharing
                | A::Unsupported { .. }
                | A::Bv1Blast
                | A::FailIfUndecided => Tactic::from_apply(node),
                A::Then(_) | A::ParThen(_) | A::OrElse(_) | A::ParOr(_) => return Err(stopped()),
            };
            arena.values.push(tactic);
            owner.check().map_err(|_| stopped())?;
        }
        if arena.values.len() != 1 || !arena.probes.is_empty() {
            return Err(stopped());
        }
        Ok(arena)
    }
}
