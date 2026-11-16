// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Total gate extension, not implication-only validation. Every non-input bit
//! is a constant or a complete AND/XOR definition; NOT is literal polarity and
//! ITE is a composition of total gates. There are NO producer clauses here.
//! Only roots and the actual SMT RM carrier domain add nondefinitional units.

use super::super::graph::{Node, Operation, RefId};
use super::super::{Reference, ReferenceError};
use super::source::Program;
use super::{Error, Result};
use ay_core::{Constant, Sort, TermData};
use ay_sat::{Literal, ResolutionProofLimits};

pub(super) struct Cnf {
    pub(super) num_vars: usize,
    pub(super) clauses: Vec<Vec<Literal>>,
}

pub(super) struct Compiler<'program, 'terms, 'owner> {
    pub(super) reference: &'program mut Reference<'terms, 'owner>,
    pub(super) cnf: Cnf,
    words: Vec<Vec<Literal>>,
    zero: Option<Literal>,
    one: Option<Literal>,
    limits: &'program ResolutionProofLimits,
    literals: usize,
    input_bytes: usize,
}

pub(super) fn compile(
    program: &mut Program<'_, '_>,
    limits: &ResolutionProofLimits,
    mode: super::RootMode,
) -> Result<Cnf> {
    let mut compiler = Compiler {
        reference: &mut program.reference,
        cnf: Cnf {
            num_vars: 0,
            clauses: Vec::new(),
        },
        words: Vec::new(),
        zero: None,
        one: None,
        limits,
        literals: 0,
        input_bytes: 0,
    };
    let count = compiler.reference.nodes.len();
    let bytes = count
        .checked_mul(size_of::<Vec<Literal>>())
        .ok_or(ReferenceError::Width)?;
    compiler.reference.storage(count, bytes)?;
    compiler
        .words
        .try_reserve_exact(count)
        .map_err(|_| ReferenceError::Allocation)?;
    for index in 0..count {
        compiler.reference.charge(1, 0)?;
        let node = compiler.reference.nodes[index];
        let bits = compiler.word(node)?;
        if bits.len() != node.width as usize {
            return Err(Error::Source);
        }
        compiler.words.push(bits);
    }
    for &root in &program.domains {
        let bits = compiler.copy(root)?;
        if bits.len() != 1 {
            return Err(Error::Source);
        }
        compiler.clause(&bits)?;
    }
    for &root in &program.roots {
        let bits = compiler.copy(root)?;
        if bits.len() != 1 {
            return Err(Error::Source);
        }
        let literal = match mode {
            #[cfg(test)]
            super::RootMode::Assertions => bits[0],
            super::RootMode::NegatedClause => bits[0].negated(),
        };
        compiler.clause(&[literal])?;
    }
    drop(compiler.words);
    compiler.reference.charge(0, 0)?;
    Ok(compiler.cnf)
}

impl Compiler<'_, '_, '_> {
    pub(super) fn reserve(&mut self, count: usize) -> Result<Vec<Literal>> {
        let bytes = count
            .checked_mul(size_of::<Literal>())
            .ok_or(ReferenceError::Width)?;
        self.reference.storage(count, bytes)?;
        let mut result = Vec::new();
        result
            .try_reserve_exact(count)
            .map_err(|_| ReferenceError::Allocation)?;
        Ok(result)
    }

    pub(super) fn copy(&mut self, id: RefId) -> Result<Vec<Literal>> {
        let count = self.words.get(id.0).ok_or(Error::Source)?.len();
        let mut result = self.reserve(count)?;
        for index in 0..count {
            self.reference.charge(1, 0)?;
            result.push(self.words[id.0][index]);
        }
        Ok(result)
    }

    fn fresh(&mut self) -> Result<Literal> {
        self.reference.charge(1, 0)?;
        let id = self.cnf.num_vars;
        if id >= self.limits.max_num_vars || id >= i32::MAX as usize {
            return Err(ReferenceError::Resource.into());
        }
        let raw = id.checked_mul(2).ok_or(ReferenceError::Width)?;
        self.cnf.num_vars += 1;
        Ok(Literal::from_index(raw))
    }

    pub(super) fn clause(&mut self, literals: &[Literal]) -> Result<()> {
        let count = self
            .cnf
            .clauses
            .len()
            .checked_add(1)
            .ok_or(ReferenceError::Width)?;
        let total = self
            .literals
            .checked_add(literals.len())
            .ok_or(ReferenceError::Width)?;
        let bytes = literals
            .len()
            .checked_mul(size_of::<Literal>())
            .and_then(|n| n.checked_add(size_of::<Vec<Literal>>()))
            .ok_or(ReferenceError::Width)?;
        let input_bytes = self
            .input_bytes
            .checked_add(bytes)
            .ok_or(ReferenceError::Width)?;
        if count > self.limits.max_input_clauses
            || total > self.limits.max_input_literals
            || literals.len() > self.limits.max_input_clause_literals
            || input_bytes > self.limits.max_input_bytes
        {
            return Err(ReferenceError::Resource.into());
        }
        let mut row = self.reserve(literals.len())?;
        for &literal in literals {
            self.reference.charge(1, 0)?;
            // Gate simplifications ensure no duplicate literals; source root
            // rows are single units. Refuse rather than relying on SAT cleanup.
            if row.contains(&literal) {
                return Err(Error::Source);
            }
            row.push(literal);
        }
        self.reference.storage(1, size_of::<Vec<Literal>>())?;
        self.cnf
            .clauses
            .try_reserve_exact(1)
            .map_err(|_| ReferenceError::Allocation)?;
        self.cnf.clauses.push(row);
        self.literals = total;
        self.input_bytes = input_bytes;
        Ok(())
    }

    pub(super) fn constant(&mut self, value: super::words::BitConstant) -> Result<Literal> {
        let old = match value {
            super::words::BitConstant::Zero => self.zero,
            super::words::BitConstant::One => self.one,
        };
        if let Some(old) = old {
            return Ok(old);
        }
        let output = self.fresh()?;
        let literal = match value {
            super::words::BitConstant::Zero => output.negated(),
            super::words::BitConstant::One => output,
        };
        self.clause(&[literal])?;
        match value {
            super::words::BitConstant::Zero => self.zero = Some(output),
            super::words::BitConstant::One => self.one = Some(output),
        }
        Ok(output)
    }

    pub(super) fn and(&mut self, a: Literal, b: Literal) -> Result<Literal> {
        self.reference.charge(1, 0)?;
        if a == b {
            return Ok(a);
        }
        if a == b.negated() {
            return self.constant(super::words::BitConstant::Zero);
        }
        let out = self.fresh()?;
        self.clause(&[out.negated(), a])?;
        self.clause(&[out.negated(), b])?;
        self.clause(&[out, a.negated(), b.negated()])?;
        Ok(out)
    }

    pub(super) fn or(&mut self, a: Literal, b: Literal) -> Result<Literal> {
        Ok(self.and(a.negated(), b.negated())?.negated())
    }

    pub(super) fn xor(&mut self, a: Literal, b: Literal) -> Result<Literal> {
        self.reference.charge(1, 0)?;
        if a == b {
            return self.constant(super::words::BitConstant::Zero);
        }
        if a == b.negated() {
            return self.constant(super::words::BitConstant::One);
        }
        let out = self.fresh()?;
        self.clause(&[out.negated(), a, b])?;
        self.clause(&[out.negated(), a.negated(), b.negated()])?;
        self.clause(&[out, a.negated(), b])?;
        self.clause(&[out, a, b.negated()])?;
        Ok(out)
    }

    pub(super) fn mux(&mut self, c: Literal, y: Literal, n: Literal) -> Result<Literal> {
        if y == n {
            return Ok(y);
        }
        let delta = self.xor(y, n)?;
        let selected = self.and(c, delta)?;
        self.xor(n, selected)
    }

    pub(super) fn input(&mut self, id: ay_core::TermId, width: usize) -> Result<Vec<Literal>> {
        let (data, sort) = self.reference.term(id)?;
        let expected = match sort {
            Sort::Bool => Some(1usize),
            Sort::BitVec(bv) if bv.width > 0 => Some(bv.width as usize),
            Sort::FloatingPoint(eb, p) if *eb >= 2 && *p >= 2 => {
                eb.checked_add(*p).and_then(|n| usize::try_from(n).ok())
            }
            Sort::Uninterpreted(name) if name == "RoundingMode" => Some(3),
            _ => None,
        };
        if expected != Some(width) {
            return Err(Error::Source);
        }
        let mut result = self.reserve(width)?;
        match data {
            TermData::Var(_, _)
                if matches!(
                    sort,
                    Sort::Bool | Sort::BitVec(_) | Sort::FloatingPoint(_, _)
                ) || matches!(sort, Sort::Uninterpreted(name) if name == "RoundingMode") =>
            {
                for _ in 0..width {
                    result.push(self.fresh()?);
                }
            }
            TermData::Const(Constant::BitVec {
                value,
                width: actual,
            }) if *actual as usize == width => {
                for index in 0..width {
                    self.reference.charge(1, 0)?;
                    let bit = if value.bit(index as u64) {
                        super::words::BitConstant::One
                    } else {
                        super::words::BitConstant::Zero
                    };
                    result.push(self.constant(bit)?);
                }
            }
            _ => return Err(Error::Source),
        }
        Ok(result)
    }

    fn word(&mut self, node: Node) -> Result<Vec<Literal>> {
        use super::words::BitConstant;
        let width = node.width as usize;
        match node.operation {
            Operation::Input(id) => self.input(id, width),
            Operation::Small(value) => {
                let mut bits = self.reserve(width)?;
                for index in 0..width {
                    self.reference.charge(1, 0)?;
                    let bit = if index < 64 && (value >> index) & 1 != 0 {
                        BitConstant::One
                    } else {
                        BitConstant::Zero
                    };
                    bits.push(self.constant(bit)?);
                }
                Ok(bits)
            }
            Operation::Ones => {
                let mut bits = self.reserve(width)?;
                let one = self.constant(BitConstant::One)?;
                for _ in 0..width {
                    self.reference.charge(1, 0)?;
                    bits.push(one);
                }
                Ok(bits)
            }
            Operation::Not(id) => {
                let mut bits = self.copy(id)?;
                for bit in &mut bits {
                    self.reference.charge(1, 0)?;
                    *bit = bit.negated();
                }
                Ok(bits)
            }
            Operation::Resize(id) => {
                let mut bits = self.copy(id)?;
                if width < bits.len() {
                    bits.truncate(width);
                }
                if width > bits.len() {
                    let zero = self.constant(BitConstant::Zero)?;
                    let added = width - bits.len();
                    self.reference.storage(
                        added,
                        added
                            .checked_mul(size_of::<Literal>())
                            .ok_or(ReferenceError::Width)?,
                    )?;
                    bits.try_reserve_exact(added)
                        .map_err(|_| ReferenceError::Allocation)?;
                    for _ in 0..added {
                        self.reference.charge(1, 0)?;
                        bits.push(zero);
                    }
                }
                Ok(bits)
            }
            Operation::Extract(id, high, low) => {
                let source = self.copy(id)?;
                if low > high || high as usize >= source.len() {
                    return Err(Error::Source);
                }
                let mut bits = self.reserve(width)?;
                for index in low..=high {
                    self.reference.charge(1, 0)?;
                    bits.push(source[index as usize]);
                }
                Ok(bits)
            }
            Operation::Binary(op, a, b) => {
                let a = self.copy(a)?;
                let b = self.copy(b)?;
                self.binary(op, &a, &b)
            }
            Operation::Select(c, y, n) => {
                let c = self.copy(c)?;
                let y = self.copy(y)?;
                let n = self.copy(n)?;
                if c.len() != 1 || y.len() != n.len() {
                    return Err(Error::Source);
                }
                let mut bits = self.reserve(width)?;
                for (&y, &n) in y.iter().zip(&n) {
                    bits.push(self.mux(c[0], y, n)?);
                }
                Ok(bits)
            }
        }
    }
}
