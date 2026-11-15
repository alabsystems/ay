// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Functional dependency propagation over prime-field affine equations.
//! Z3 5.3.3 tactic/ff/ff_unique_tactic.cpp motivates solved-RHS matching.
//! Only certified conflicts replace a goal; stalling retains every root and
//! free variable. This provides no tactic proof/core or SAT-model transport.
use super::tactics::TacticFailure;
use ay_core::term::{
    reserve_counted, Constant, CountedTermBuilder, Symbol, TermConstructionAdmission, TermData,
};
use ay_core::{FiniteFieldSort, Sort, TermId, TermStore};

fn failure() -> TacticFailure {
    TacticFailure::new("ff-unique original admission or typed source refused")
}
fn pay(owner: &dyn TermConstructionAdmission, work: usize) -> Result<(), TacticFailure> {
    owner.admit(work, 0).map_err(|_| failure())
}
fn reserve<T>(
    out: &mut Vec<T>,
    n: usize,
    owner: &dyn TermConstructionAdmission,
) -> Result<(), TacticFailure> {
    reserve_counted(out, n, owner).map_err(|_| failure())
}
struct Borrowed<'a>(&'a dyn TermConstructionAdmission);
impl TermConstructionAdmission for Borrowed<'_> {
    fn admit(
        &self,
        work: usize,
        bytes: usize,
    ) -> Result<(), ay_core::original_query::CountedAdmissionError> {
        self.0.admit(work, bytes)
    }
    fn refuse(
        &self,
        error: ay_core::original_query::CountedAdmissionError,
    ) -> ay_core::original_query::CountedAdmissionError {
        self.0.refuse(error)
    }
}
#[derive(Clone, Copy, PartialEq, Eq)]
enum Kind {
    Add,
    Mul,
    Neg,
    Bitsum,
}
fn kind(store: &TermStore, symbol: &Symbol) -> Option<Kind> {
    let Symbol::Named(name) = symbol else {
        return None;
    };
    if store.is_declared_function(name) {
        return None;
    }
    match name.as_str() {
        "ff.add" => Some(Kind::Add),
        "ff.mul" => Some(Kind::Mul),
        "ff.neg" => Some(Kind::Neg),
        "ff.bitsum" => Some(Kind::Bitsum),
        _ => None,
    }
}
#[derive(Clone, Copy)]
struct Literal {
    left: TermId,
    right: TermId,
    equal: bool,
}
#[derive(Default)]
struct Row {
    terms: Vec<(usize, u32)>,
    constant: u32,
}
struct Definition {
    output: usize,
    row: Row,
}
struct Application {
    id: usize,
    kind: Kind,
    args: Vec<usize>,
}
enum Change {
    Same,
    Changed,
    Conflict,
}
struct Propagation<'a> {
    store: &'a TermStore,
    owner: &'a dyn TermConstructionAdmission,
    field: FiniteFieldSort,
    parent: Vec<usize>,
    values: Vec<Option<u32>>,
    active: Vec<TermId>,
    literals: Vec<Literal>,
}
impl Propagation<'_> {
    fn add(&self, a: u32, b: u32) -> u32 {
        ((u64::from(a) + u64::from(b)) % u64::from(self.field.modulus())) as u32
    }
    fn mul(&self, a: u32, b: u32) -> Result<u32, TacticFailure> {
        pay(self.owner, 1)?;
        Ok((u64::from(a) * u64::from(b) % u64::from(self.field.modulus())) as u32)
    }
    fn neg(&self, a: u32) -> u32 {
        if a == 0 {
            0
        } else {
            self.field.modulus() - a
        }
    }
    fn inverse(&self, mut a: u32) -> Result<u32, TacticFailure> {
        if a == 0 {
            return Err(failure());
        }
        let mut out = 1;
        let mut exponent = self.field.modulus() - 2;
        while exponent != 0 {
            pay(self.owner, 1)?;
            if exponent & 1 != 0 {
                out = self.mul(out, a)?;
            }
            exponent >>= 1;
            if exponent != 0 {
                a = self.mul(a, a)?;
            }
        }
        Ok(out)
    }
    fn find(&self, mut id: usize) -> Result<usize, TacticFailure> {
        loop {
            pay(self.owner, 1)?;
            let next = *self.parent.get(id).ok_or_else(failure)?;
            if next == id {
                return Ok(id);
            }
            id = next;
        }
    }
    fn value(&self, id: usize) -> Result<Option<u32>, TacticFailure> {
        Ok(self.values[self.find(id)?])
    }
    fn merge(&mut self, a: usize, b: usize) -> Result<Change, TacticFailure> {
        let a = self.find(a)?;
        let b = self.find(b)?;
        if a == b {
            return Ok(Change::Same);
        }
        if matches!((self.values[a],self.values[b]),(Some(x),Some(y)) if x!=y) {
            return Ok(Change::Conflict);
        }
        let (a, b) = if a < b { (a, b) } else { (b, a) };
        self.parent[b] = a;
        self.values[a] = self.values[a].or(self.values[b]);
        Ok(Change::Changed)
    }
    fn set_value(&mut self, id: usize, value: u32) -> Result<Change, TacticFailure> {
        let id = self.find(id)?;
        Ok(match self.values[id] {
            Some(old) if old != value => Change::Conflict,
            Some(_) => Change::Same,
            None => {
                self.values[id] = Some(value);
                Change::Changed
            }
        })
    }
    fn atom(&self, row: &mut Row, id: usize, coefficient: u32) -> Result<(), TacticFailure> {
        pay(self.owner, 1)?;
        if coefficient == 0 {
            return Ok(());
        }
        let id = self.find(id)?;
        if let Some(value) = self.values[id] {
            row.constant = self.add(row.constant, self.mul(value, coefficient)?);
            return Ok(());
        }
        let mut at = 0;
        while at < row.terms.len() {
            pay(self.owner, 1)?;
            if row.terms[at].0 >= id {
                break;
            }
            at += 1;
        }
        if at < row.terms.len() && row.terms[at].0 == id {
            row.terms[at].1 = self.add(row.terms[at].1, coefficient);
            if row.terms[at].1 == 0 {
                pay(self.owner, row.terms.len() - at)?;
                row.terms.remove(at);
            }
        } else {
            reserve(&mut row.terms, 1, self.owner)?;
            pay(self.owner, row.terms.len() - at)?;
            row.terms.insert(at, (id, coefficient));
        }
        Ok(())
    }
    fn affine(&self, left: TermId, right: TermId) -> Result<Row, TacticFailure> {
        let mut row = Row::default();
        let mut pending = Vec::new();
        reserve(&mut pending, 2, self.owner)?;
        pending.push((left, 1));
        pending.push((right, self.field.modulus() - 1));
        while let Some((id, coefficient)) = pending.pop() {
            pay(self.owner, 1)?;
            if let Some(value) = self.value(id.index())? {
                row.constant = self.add(row.constant, self.mul(value, coefficient)?);
                continue;
            }
            if let TermData::App(symbol, args) = self.store.get(id) {
                match kind(self.store, symbol) {
                    Some(Kind::Add) | Some(Kind::Neg) | Some(Kind::Bitsum) => {
                        reserve(&mut pending, args.len(), self.owner)?;
                        let mut weight = if kind(self.store, symbol) == Some(Kind::Neg) {
                            self.neg(coefficient)
                        } else {
                            coefficient
                        };
                        for &arg in args {
                            pay(self.owner, 1)?;
                            pending.push((arg, weight));
                            if kind(self.store, symbol) == Some(Kind::Bitsum) {
                                weight = self.mul(weight, 2 % self.field.modulus())?;
                            }
                        }
                        continue;
                    }
                    Some(Kind::Mul) => {
                        let mut factor = coefficient;
                        let mut unknown = None;
                        let mut multiple = false;
                        for &arg in args {
                            pay(self.owner, 1)?;
                            if let Some(value) = self.value(arg.index())? {
                                factor = self.mul(factor, value)?;
                            } else if unknown.replace(arg).is_some() {
                                multiple = true;
                            }
                        }
                        if factor == 0 {
                            continue;
                        }
                        if !multiple {
                            if let Some(arg) = unknown {
                                reserve(&mut pending, 1, self.owner)?;
                                pending.push((arg, factor));
                            } else {
                                row.constant = self.add(row.constant, factor);
                            }
                            continue;
                        }
                    }
                    None => {}
                }
            }
            self.atom(&mut row, id.index(), coefficient)?;
        }
        Ok(row)
    }
    fn same_row(&self, a: &Row, b: &Row) -> Result<bool, TacticFailure> {
        pay(
            self.owner,
            a.terms
                .len()
                .checked_add(b.terms.len())
                .and_then(|n| n.checked_add(1))
                .ok_or_else(failure)?,
        )?;
        Ok(a.constant == b.constant && a.terms == b.terms)
    }
    fn definitions(
        &self,
        row: &Row,
        output: usize,
        coefficient: u32,
    ) -> Result<Row, TacticFailure> {
        let factor = self.neg(self.inverse(coefficient)?);
        let mut out = Row::default();
        out.constant = self.mul(row.constant, factor)?;
        reserve(
            &mut out.terms,
            row.terms.len().saturating_sub(1),
            self.owner,
        )?;
        for &(id, value) in &row.terms {
            pay(self.owner, 1)?;
            if id != output {
                out.terms.push((id, self.mul(value, factor)?));
            }
        }
        Ok(out)
    }
    fn run(&mut self) -> Result<bool, TacticFailure> {
        'fixpoint: loop {
            pay(self.owner, 1)?;
            let mut applications: Vec<Application> = Vec::new();
            for position in 0..self.active.len() {
                pay(self.owner, 1)?;
                let id = self.active[position];
                let index = id.index();
                let TermData::App(symbol, args) = self.store.get(id) else {
                    continue;
                };
                let Some(operation) = kind(self.store, symbol) else {
                    continue;
                };
                let mut key = Vec::new();
                reserve(&mut key, args.len(), self.owner)?;
                let mut value = Some(if operation == Kind::Mul { 1 } else { 0 });
                let mut weight = 1;
                for &arg in args {
                    pay(self.owner, 1)?;
                    key.push(self.find(arg.index())?);
                    value = match (value, self.value(arg.index())?) {
                        (Some(old), Some(v)) => Some(match operation {
                            Kind::Mul => self.mul(old, v)?,
                            Kind::Neg => self.neg(v),
                            Kind::Add => self.add(old, v),
                            Kind::Bitsum => self.add(old, self.mul(weight, v)?),
                        }),
                        _ => None,
                    };
                    if operation == Kind::Bitsum {
                        weight = self.mul(weight, 2 % self.field.modulus())?;
                    }
                }
                if let Some(value) = value {
                    match self.set_value(index, value)? {
                        Change::Conflict => return Ok(true),
                        Change::Changed => continue 'fixpoint,
                        Change::Same => {}
                    }
                }
                if matches!(operation, Kind::Add | Kind::Mul) {
                    // Counted insertion sort avoids an opaque unpriced sort.
                    for i in 1..key.len() {
                        let mut j = i;
                        while j > 0 {
                            pay(self.owner, 1)?;
                            if key[j - 1] <= key[j] {
                                break;
                            }
                            key.swap(j - 1, j);
                            j -= 1;
                        }
                    }
                }
                for previous in &applications {
                    pay(
                        self.owner,
                        key.len()
                            .checked_add(previous.args.len())
                            .and_then(|n| n.checked_add(1))
                            .ok_or_else(failure)?,
                    )?;
                    if operation == previous.kind && key == previous.args {
                        match self.merge(index, previous.id)? {
                            Change::Conflict => return Ok(true),
                            Change::Changed => continue 'fixpoint,
                            Change::Same => {}
                        }
                    }
                }
                reserve(&mut applications, 1, self.owner)?;
                applications.push(Application {
                    id: index,
                    kind: operation,
                    args: key,
                });
            }
            let mut definitions: Vec<Definition> = Vec::new();
            for at in 0..self.literals.len() {
                pay(self.owner, 1)?;
                let literal = self.literals[at];
                let row = self.affine(literal.left, literal.right)?;
                if !literal.equal {
                    if row.terms.is_empty() && row.constant == 0 {
                        return Ok(true);
                    }
                    continue;
                }
                if row.terms.is_empty() {
                    if row.constant != 0 {
                        return Ok(true);
                    }
                    continue;
                }
                if row.terms.len() == 1 {
                    let (id, coefficient) = row.terms[0];
                    let inverse = self.inverse(coefficient)?;
                    let value = self.mul(self.neg(row.constant), inverse)?;
                    match self.set_value(id, value)? {
                        Change::Conflict => return Ok(true),
                        Change::Changed => continue 'fixpoint,
                        Change::Same => {}
                    }
                }
                if row.terms.len() == 2
                    && row.constant == 0
                    && row.terms[0].1 == self.neg(row.terms[1].1)
                {
                    match self.merge(row.terms[0].0, row.terms[1].0)? {
                        Change::Conflict => return Ok(true),
                        Change::Changed => continue 'fixpoint,
                        Change::Same => {}
                    }
                }
                for &(output, coefficient) in &row.terms {
                    pay(self.owner, 1)?;
                    let rhs = self.definitions(&row, output, coefficient)?;
                    for previous in &definitions {
                        if self.same_row(&rhs, &previous.row)? {
                            match self.merge(output, previous.output)? {
                                Change::Conflict => return Ok(true),
                                Change::Changed => continue 'fixpoint,
                                Change::Same => {}
                            }
                        }
                    }
                    reserve(&mut definitions, 1, self.owner)?;
                    definitions.push(Definition { output, row: rhs });
                }
            }
            return Ok(false);
        }
    }
}

pub(super) fn apply(
    store: &mut TermStore,
    roots: &[TermId],
    owner: &dyn TermConstructionAdmission,
) -> Result<Vec<TermId>, TacticFailure> {
    let n = store.len();
    pay(owner, n)?;
    let mut parent = Vec::new();
    let mut values = Vec::new();
    let mut reachable = Vec::new();
    let mut literals = Vec::new();
    let mut pending = Vec::new();
    reserve(&mut parent, n, owner)?;
    reserve(&mut values, n, owner)?;
    reserve(&mut reachable, n, owner)?;
    parent.extend(0..n);
    values.resize(n, None);
    reachable.resize(n, 0u8);
    reserve(&mut pending, roots.len(), owner)?;
    pending.extend_from_slice(roots);
    let mut field = None;
    let mut mixed = false;
    while let Some(mut id) = pending.pop() {
        pay(owner, 1)?;
        if id.index() >= n || store.sort(id) != &Sort::Bool {
            return Err(failure());
        }
        if reachable[id.index()] != 0 {
            continue;
        }
        reachable[id.index()] = 2;
        if let TermData::App(Symbol::Named(name), args) = store.get(id) {
            if name == "and" && !store.is_declared_function(name) {
                reserve(&mut pending, args.len(), owner)?;
                for &child in args {
                    pay(owner, 1)?;
                    if child.index() >= id.index() {
                        return Err(failure());
                    }
                    pending.push(child);
                }
                continue;
            }
        }
        let mut equal = true;
        while let TermData::Not(child) = store.get(id) {
            pay(owner, 1)?;
            if child.index() >= id.index() || store.sort(*child) != &Sort::Bool {
                return Err(failure());
            }
            id = *child;
            equal = !equal;
        }
        let TermData::App(Symbol::Named(name), args) = store.get(id) else {
            continue;
        };
        if name != "=" || store.is_declared_function(name) || args.len() != 2 {
            continue;
        }
        if args.iter().any(|child| child.index() >= id.index()) {
            return Err(failure());
        }
        let Sort::FiniteField(actual) = store.sort(args[0]) else {
            continue;
        };
        if store.sort(args[1]) != &Sort::FiniteField(*actual) {
            return Err(failure());
        }
        if field.is_some_and(|old| old != *actual) {
            mixed = true;
        }
        field = Some(*actual);
        reserve(&mut literals, 1, owner)?;
        literals.push(Literal {
            left: args[0],
            right: args[1],
            equal,
        });
    }
    if let Some(field) = field.filter(|_| !mixed) {
        let mut active = Vec::new();
        let mut todo = Vec::new();
        reserve(
            &mut todo,
            literals.len().checked_mul(2).ok_or_else(failure)?,
            owner,
        )?;
        for literal in &literals {
            todo.push(literal.left);
            todo.push(literal.right);
        }
        while let Some(id) = todo.pop() {
            pay(owner, 1)?;
            if id.index() >= n || store.sort(id) != &Sort::FiniteField(field) {
                return Err(failure());
            }
            if reachable[id.index()] != 0 {
                continue;
            }
            reachable[id.index()] = 1;
            reserve(&mut active, 1, owner)?;
            active.push(id);
            match store.get(id) {
                TermData::Const(Constant::FiniteField {
                    value,
                    field: actual,
                }) if *actual == field && *value < field.modulus() => {
                    values[id.index()] = Some(*value)
                }
                TermData::Var(..) => {}
                TermData::App(symbol, args) => {
                    if let Some(operation) = kind(store, symbol) {
                        if (operation == Kind::Neg && args.len() != 1) || args.is_empty() {
                            return Err(failure());
                        }
                        reserve(&mut todo, args.len(), owner)?;
                        for &child in args {
                            pay(owner, 1)?;
                            if child.index() >= id.index() {
                                return Err(failure());
                            }
                            todo.push(child);
                        }
                    }
                }
                _ => return Err(failure()),
            }
        }
        let conflict = Propagation {
            store,
            owner,
            field,
            parent,
            values,
            active,
            literals,
        }
        .run()?;
        if conflict {
            let borrowed = Borrowed(owner);
            let mut builder =
                CountedTermBuilder::with_admission(store, &borrowed).map_err(|_| failure())?;
            let no = builder.boolean(false).map_err(|_| failure())?;
            let mut out = Vec::new();
            reserve(&mut out, 1, owner)?;
            out.push(no);
            owner.check().map_err(|_| failure())?;
            return Ok(out);
        }
    }
    let mut out = Vec::new();
    reserve(&mut out, roots.len(), owner)?;
    pay(owner, roots.len())?;
    out.extend_from_slice(roots);
    owner.check().map_err(|_| failure())?;
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::executor::Executor;
    use ay_frontend::{parse, Command};
    fn setup(body: &str) -> Executor {
        let mut exec = Executor::new();
        let commands = parse(body)
            .unwrap()
            .into_iter()
            .filter(|command| !matches!(command, Command::Apply(..) | Command::CheckSat))
            .collect::<Vec<_>>();
        exec.execute_all(&commands).unwrap();
        exec
    }
    #[test]
    fn field_unique_conflicts_match_independent_small_field_assignments() {
        for p in [2u32, 3, 5, 7] {
            for c in 0..p {
                for d in 0..p {
                    let body = format!("(set-logic QF_FF) (declare-const x (_ FiniteField {p})) (declare-const a (_ FiniteField {p})) (declare-const b (_ FiniteField {p})) (assert (= (ff.mul #f{c}m{p} a) (ff.mul x x))) (assert (= (ff.mul #f{d}m{p} b) (ff.mul x x))) (assert (not (= a b)))");
                    let mut exec = setup(&body);
                    let roots = exec.ctx.assertions.clone();
                    let _read = exec.begin_external_evaluation_read();
                    let scope = exec.capture_tactic_construction().unwrap();
                    let out = apply(&mut exec.ctx.terms, &roots, scope.admission()).unwrap();
                    let conflict = out.len() == 1
                        && matches!(
                            exec.ctx.terms.get(out[0]),
                            TermData::Const(Constant::Bool(false))
                        );
                    let satisfiable = (0..p).any(|x| {
                        (0..p).any(|a| {
                            (0..p)
                                .any(|b| c * a % p == x * x % p && d * b % p == x * x % p && a != b)
                        })
                    });
                    assert_eq!(conflict, !satisfiable, "p={p} c={c} d={d}");
                    assert!(scope.validate(&exec));
                }
            }
        }
    }
    #[test]
    fn field_unique_infers_scaled_functional_outputs_and_preserves_a_sat_near_miss() {
        let input = include_str!("../../../tests/fixtures/finite_field/unique_tactic.smt2");
        for (index, body) in input.split("(reset)").enumerate() {
            let mut exec = setup(body);
            let roots = exec.ctx.assertions.clone();
            let stamp = exec.ctx.terms.snapshot_stamp();
            let _read = exec.begin_external_evaluation_read();
            let scope = exec.capture_tactic_construction().unwrap();
            let out = apply(&mut exec.ctx.terms, &roots, scope.admission()).unwrap();
            assert!(scope.validate(&exec));
            if index == 1 {
                assert_eq!(out, roots);
            } else {
                assert_eq!(out.len(), 1);
                assert!(matches!(
                    exec.ctx.terms.get(out[0]),
                    TermData::Const(Constant::Bool(false))
                ));
            }
            assert_eq!(exec.ctx.assertions, roots);
            assert_eq!(
                exec.ctx.terms.snapshot_stamp(),
                stamp,
                "no speculative namespace enters source"
            );
        }
    }
    #[test]
    fn field_unique_retains_original_native_interrupt_memory_and_fresh_request() {
        let body = include_str!("../../../tests/fixtures/finite_field/unique_tactic.smt2")
            .split("(reset)")
            .next()
            .unwrap();
        let mut exec = setup(body);
        let roots = exec.ctx.assertions.clone();
        let stamp = exec.ctx.terms.snapshot_stamp();
        let flag = std::sync::Arc::new(std::sync::atomic::AtomicBool::new(false));
        exec.set_interrupt(std::sync::Arc::clone(&flag));
        let read =
            exec.begin_native_evaluation_read(std::sync::Arc::clone(&flag), None, None, None);
        let scope = exec.capture_tactic_construction().unwrap();
        flag.store(true, std::sync::atomic::Ordering::Release);
        assert!(apply(&mut exec.ctx.terms, &roots, scope.admission()).is_err());
        flag.store(false, std::sync::atomic::Ordering::Release);
        assert!(apply(&mut exec.ctx.terms, &roots, scope.admission()).is_err());
        assert_eq!(
            exec.tactic_refusal_origin(),
            Some(crate::UnknownOrigin::InterruptFlag)
        );
        drop(scope);
        drop(read);
        assert_eq!(exec.ctx.terms.snapshot_stamp(), stamp);
        let read =
            exec.begin_native_evaluation_read(std::sync::Arc::clone(&flag), None, None, None);
        let scope = exec.capture_tactic_construction().unwrap();
        assert!(apply(&mut exec.ctx.terms, &roots, scope.admission()).is_ok());
        drop(scope);
        drop(read);
        exec.set_term_memory_limit(Some(exec.ctx.terms.true_memory_bytes() + 1024));
        let read =
            exec.begin_native_evaluation_read(std::sync::Arc::clone(&flag), None, None, None);
        match exec.capture_tactic_construction() {
            Ok(scope) => assert!(apply(&mut exec.ctx.terms, &roots, scope.admission()).is_err()),
            Err(origin) => assert_eq!(origin, crate::UnknownOrigin::MemoryBudget),
        }
        assert_eq!(
            exec.tactic_refusal_origin(),
            Some(crate::UnknownOrigin::MemoryBudget)
        );
        drop(read);
        assert_eq!(exec.ctx.assertions, roots);
    }
}
