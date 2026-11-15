// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Nonrecursive live-source census/lowering. Repeated TermIds share one value;
//! missing slots, cycles, malformed sorts and unsupported forms refuse. Every
//! operand is visited before its parent, even on a Boolean branch later false.

use super::super::graph::{Bits, RefId};
use super::super::{Arithmetic, Format, Progress, Reference, ReferenceError};
use super::{Error, Result};
use ay_core::{Sort, TermData, TermId, TermStore};

#[derive(Clone, Copy)]
pub(super) enum Value {
    Bool(RefId),
    Bv(RefId),
    Rm(RefId),
    Fp { bits: Bits, eb: u32, p: u32 },
}

pub(super) struct Program<'terms, 'owner> {
    pub(super) reference: Reference<'terms, 'owner>,
    pub(super) roots: Vec<RefId>,
    pub(super) domains: Vec<RefId>,
}

pub(super) struct Builder<'terms, 'owner> {
    pub(super) program: Program<'terms, 'owner>,
    states: Vec<u8>,
    values: Vec<Option<Value>>,
}

#[derive(Clone, Copy)]
enum Visit {
    Enter,
    Exit,
}

pub(super) fn build<'terms, 'owner>(
    terms: &'terms TermStore,
    roots: &[TermId],
    max_nodes: usize,
    progress: Progress<'owner>,
) -> Result<Program<'terms, 'owner>> {
    if roots.is_empty() {
        return Err(Error::Source);
    }
    if max_nodes == 0 {
        return Err(ReferenceError::Resource.into());
    }
    let reference = Reference {
        terms,
        source: TermId::SENTINEL,
        operation: Arithmetic::Mul,
        format: Format {
            eb: 0,
            p: 0,
            product_width: 0,
            exponent_width: 0,
        },
        progress,
        refused: false,
        nodes: Vec::new(),
        node_limit: max_nodes,
        allocated_bytes: 0,
        output: None,
    };
    let mut builder = Builder {
        program: Program {
            reference,
            roots: Vec::new(),
            domains: Vec::new(),
        },
        states: Vec::new(),
        values: Vec::new(),
    };
    builder.tables()?;
    for &root in roots {
        builder.visit(root)?;
        let word = builder.boolean(root)?;
        builder.push_root(word)?;
    }
    builder.program.reference.charge(0, 0)?;
    Ok(builder.program)
}

impl<'terms> Builder<'terms, '_> {
    fn tables(&mut self) -> Result<()> {
        let count = self.program.reference.terms.len();
        let bytes = count
            .checked_mul(1 + std::mem::size_of::<Option<Value>>())
            .ok_or(ReferenceError::Width)?;
        self.program.reference.storage(count, bytes)?;
        self.states
            .try_reserve_exact(count)
            .map_err(|_| ReferenceError::Allocation)?;
        self.values
            .try_reserve_exact(count)
            .map_err(|_| ReferenceError::Allocation)?;
        self.states.resize(count, 0);
        self.values.resize(count, None);
        Ok(())
    }

    pub(super) fn term(&mut self, id: TermId) -> Result<(&'terms TermData, &'terms Sort)> {
        Ok(self.program.reference.term(id)?)
    }

    fn task(&mut self, tasks: &mut Vec<(TermId, Visit)>, id: TermId, phase: Visit) -> Result<()> {
        let bytes = std::mem::size_of::<(TermId, Visit)>();
        self.program.reference.storage(1, bytes)?;
        tasks
            .try_reserve_exact(1)
            .map_err(|_| ReferenceError::Allocation)?;
        tasks.push((id, phase));
        Ok(())
    }

    fn visit(&mut self, root: TermId) -> Result<()> {
        let mut tasks = Vec::new();
        self.task(&mut tasks, root, Visit::Enter)?;
        while let Some((id, phase)) = tasks.pop() {
            let (data, sort) = self.term(id)?;
            let state = *self.states.get(id.index()).ok_or(Error::Source)?;
            if matches!(phase, Visit::Exit) {
                let value = self.lower(id, data, sort)?;
                self.validate_sort(value, sort)?;
                self.values[id.index()] = Some(value);
                self.states[id.index()] = 2;
                continue;
            }
            if state == 2 {
                continue;
            }
            if state != 0 {
                return Err(Error::Source);
            }
            self.states[id.index()] = 1;
            self.task(&mut tasks, id, Visit::Exit)?;
            match data {
                TermData::App(_, args) => {
                    for &child in args.iter().rev() {
                        self.task(&mut tasks, child, Visit::Enter)?;
                    }
                }
                TermData::Not(child) => self.task(&mut tasks, *child, Visit::Enter)?,
                TermData::Ite(c, y, n) => {
                    for child in [*n, *y, *c] {
                        self.task(&mut tasks, child, Visit::Enter)?;
                    }
                }
                TermData::Var(_, _) | TermData::Const(_) => {}
                _ => return Err(Error::Source),
            }
        }
        drop(tasks);
        self.program.reference.charge(0, 0)?;
        Ok(())
    }

    fn validate_sort(&mut self, value: Value, sort: &Sort) -> Result<()> {
        let valid = match (value, sort) {
            (Value::Bool(id), Sort::Bool) => self.program.reference.width(id)? == 1,
            (Value::Bv(id), Sort::BitVec(bv)) => {
                bv.width > 0 && self.program.reference.width(id)? == bv.width
            }
            (Value::Rm(id), Sort::Uninterpreted(name)) => {
                name == "RoundingMode" && self.program.reference.width(id)? == 3
            }
            (Value::Fp { bits, eb, p }, Sort::FloatingPoint(e, s)) => {
                eb == *e
                    && p == *s
                    && self.program.reference.width(bits.sign)? == 1
                    && self.program.reference.width(bits.exponent)? == eb
                    && self.program.reference.width(bits.fraction)? == p - 1
            }
            _ => false,
        };
        if !valid {
            return Err(Error::Source);
        }
        Ok(())
    }

    pub(super) fn value(&mut self, id: TermId) -> Result<Value> {
        self.program.reference.charge(1, 0)?;
        self.values
            .get(id.index())
            .copied()
            .flatten()
            .ok_or(Error::Source)
    }

    pub(super) fn boolean(&mut self, id: TermId) -> Result<RefId> {
        match self.value(id)? {
            Value::Bool(value) => Ok(value),
            _ => Err(Error::Source),
        }
    }

    pub(super) fn bv(&mut self, id: TermId) -> Result<RefId> {
        match self.value(id)? {
            Value::Bv(value) => Ok(value),
            _ => Err(Error::Source),
        }
    }

    pub(super) fn fp(&mut self, id: TermId) -> Result<(Bits, u32, u32)> {
        match self.value(id)? {
            Value::Fp { bits, eb, p } => Ok((bits, eb, p)),
            _ => Err(Error::Source),
        }
    }

    fn push_root(&mut self, word: RefId) -> Result<()> {
        self.program
            .reference
            .storage(1, std::mem::size_of::<RefId>())?;
        self.program
            .roots
            .try_reserve_exact(1)
            .map_err(|_| ReferenceError::Allocation)?;
        self.program.roots.push(word);
        Ok(())
    }

    pub(super) fn domain(&mut self, word: RefId) -> Result<()> {
        let five = self.program.reference.small(5, 3)?;
        let domain = self
            .program
            .reference
            .binary(super::super::graph::Binary::Ult, word, five)?;
        self.program
            .reference
            .storage(1, std::mem::size_of::<RefId>())?;
        self.program
            .domains
            .try_reserve_exact(1)
            .map_err(|_| ReferenceError::Allocation)?;
        self.program.domains.push(domain);
        Ok(())
    }
}
