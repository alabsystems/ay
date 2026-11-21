// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! One cumulative owner for source admission, closure and owned-cycle checking.

use ay_core::proof_validation::OwnedSubvalueBudget;
use ay_core::{Constant, Sort, Symbol, TermData, TermId, TermStore};

use super::super::datatype_axiom::{DatatypeDecls, SelectorDecls};

pub(super) struct Control<'a> {
    pub(super) budget: OwnedSubvalueBudget,
    pub(super) progress: &'a mut dyn FnMut(usize, usize) -> bool,
    nodes: usize,
    edges: usize,
    payload: usize,
    registry: usize,
}

impl<'a> Control<'a> {
    pub(super) fn new(progress: &'a mut dyn FnMut(usize, usize) -> bool) -> Self {
        Self {
            budget: OwnedSubvalueBudget::new(64 << 20, 64 << 20),
            progress,
            nodes: 0,
            edges: 0,
            payload: 0,
            registry: 0,
        }
    }

    pub(super) fn pay(&mut self, work: usize, bytes: usize) -> bool {
        self.budget
            .charge_with_progress(work, bytes, self.progress)
            .is_ok()
    }

    pub(super) fn poll(&mut self) -> bool {
        self.pay(0, 0)
    }

    pub(super) fn stopped(&self) -> bool {
        self.budget.refusal().is_some()
    }

    fn payload(&mut self, bytes: usize) -> Result<(), ()> {
        self.payload = self.payload.checked_add(bytes).ok_or(())?;
        self.pay(bytes, bytes).then_some(()).ok_or(())
    }

    fn push<T>(&mut self, values: &mut Vec<T>, value: T) -> Result<(), ()> {
        if values.len() == values.capacity() {
            let capacity = values.capacity().saturating_mul(2).max(4);
            if !self.pay(
                values.len(),
                capacity.saturating_mul(std::mem::size_of::<T>()),
            ) {
                return Err(());
            }
            values
                .try_reserve_exact(capacity.saturating_sub(values.len()))
                .map_err(|_| ())?;
        }
        values.push(value);
        Ok(())
    }

    fn sort(&mut self, sort: &Sort) -> Result<(), ()> {
        let mut pending = Vec::new();
        self.push(&mut pending, (sort, 0usize))?;
        while let Some((sort, depth)) = pending.pop() {
            if depth >= 128 || !self.pay(1, 0) {
                return Err(());
            }
            match sort {
                Sort::Array(array) => {
                    self.push(&mut pending, (&array.index_sort, depth + 1))?;
                    self.push(&mut pending, (&array.element_sort, depth + 1))?;
                }
                Sort::Seq(element) => self.push(&mut pending, (element, depth + 1))?,
                Sort::Uninterpreted(name) | Sort::TypeVar(name) | Sort::FiniteDomain(name, _) => {
                    self.payload(name.len())?
                }
                Sort::Datatype(datatype) => {
                    self.payload(datatype.name.len())?;
                    if !self.pay(datatype.constructors.len(), 0) {
                        return Err(());
                    }
                    for constructor in &datatype.constructors {
                        self.payload(constructor.name.len())?;
                        if !self.pay(constructor.fields.len(), 0) {
                            return Err(());
                        }
                        for field in &constructor.fields {
                            self.payload(field.name.len())?;
                            self.push(&mut pending, (&field.sort, depth + 1))?;
                        }
                    }
                }
                Sort::Bool
                | Sort::Int
                | Sort::Real
                | Sort::BitVec(_)
                | Sort::String
                | Sort::RegLan
                | Sort::FloatingPoint(..)
                | Sort::Char
                | Sort::Complex
                | Sort::FiniteField(_) => {}
                _ => return Err(()),
            }
        }
        Ok(())
    }

    /// Admit every physical edge and payload before legacy preparation can
    /// copy it. Repeated edges cost work even when their child was seen before.
    pub(super) fn source(
        &mut self,
        terms: &TermStore,
        clause: &[TermId],
        datatypes: DatatypeDecls<'_>,
        selectors: SelectorDecls<'_>,
    ) -> Result<(), ()> {
        if !self.pay(clause.len(), 0) || clause.len() > 4096 {
            return Err(());
        }
        for registry in [datatypes, selectors] {
            self.registry = self.registry.checked_add(registry.len()).ok_or(())?;
            if !self.pay(registry.len(), 0) {
                return Err(());
            }
            for (owner, members) in registry {
                self.registry = self
                    .registry
                    .checked_add(owner.len())
                    .and_then(|n| n.checked_add(members.len()))
                    .ok_or(())?;
                self.payload(owner.len())?;
                if !self.pay(members.len(), 0) {
                    return Err(());
                }
                for member in members {
                    self.registry = self.registry.checked_add(member.len()).ok_or(())?;
                    self.payload(member.len())?;
                }
            }
        }
        let mut pending = Vec::new();
        let mut seen = Vec::new();
        for &root in clause {
            if terms.entry_stamp(root).is_none() || terms.sort(root) != &Sort::Bool {
                return Err(());
            }
            self.push(&mut pending, root)?;
        }
        while let Some(term) = pending.pop() {
            if terms.entry_stamp(term).is_none() || !self.pay(seen.len() + 1, 0) {
                return Err(());
            }
            if seen.contains(&term) {
                continue;
            }
            if seen.len() >= 4096 {
                return Err(());
            }
            self.push(&mut seen, term)?;
            self.sort(terms.sort(term))?;
            let mut child = |control: &mut Self, value: TermId| {
                // A real native ground DAG has only earlier children. This
                // also excludes forged cyclic handles before legacy walking.
                if value.index() >= term.index() || terms.entry_stamp(value).is_none() {
                    return Err(());
                }
                control.edges = control.edges.checked_add(1).ok_or(())?;
                if !control.pay(1, std::mem::size_of::<TermId>()) {
                    return Err(());
                }
                control.push(&mut pending, value)
            };
            match terms.get(term) {
                TermData::Const(value) => match value {
                    Constant::Bool(_) | Constant::FiniteField { .. } => {}
                    Constant::Int(value) | Constant::BitVec { value, .. } => {
                        self.payload(usize::try_from(value.bits()).map_err(|_| ())?)?;
                    }
                    Constant::Rational(value) => {
                        self.payload(usize::try_from(value.0.numer().bits()).map_err(|_| ())?)?;
                        self.payload(usize::try_from(value.0.denom().bits()).map_err(|_| ())?)?;
                    }
                    Constant::String(value) => self.payload(value.len())?,
                    _ => return Err(()),
                },
                TermData::Var(name, _) => self.payload(name.len())?,
                TermData::App(symbol, args) => {
                    self.payload(symbol.name().len())?;
                    if let Symbol::Indexed(_, indices) = symbol {
                        self.payload(
                            indices
                                .len()
                                .checked_mul(std::mem::size_of::<u32>())
                                .ok_or(())?,
                        )?;
                    }
                    // Admission precedes the scan and any pending copy.
                    if !self.pay(args.len(), 0) {
                        return Err(());
                    }
                    for &value in args {
                        child(self, value)?;
                    }
                }
                TermData::Not(value) => child(self, *value)?,
                TermData::Ite(a, b, c) => {
                    child(self, *a)?;
                    child(self, *b)?;
                    child(self, *c)?;
                }
                _ => return Err(()),
            }
        }
        self.nodes = seen.len();
        // Hash buckets, polarity vectors, the flattened clause and initial
        // universe are admitted before any legacy allocation is entered.
        self.pay(
            self.nodes.saturating_add(self.edges),
            self.nodes
                .saturating_mul(1024)
                .saturating_add(self.edges.saturating_mul(32)),
        )
        .then_some(())
        .ok_or(())
    }

    /// Conservative upper bounds cover each old closure phase's pair scans,
    /// class/signature maps, string copies, union/find paths and argument
    /// copies before any of them runs. Polls inside phases observe stops.
    pub(super) fn round(&mut self) -> bool {
        let work = self
            .nodes
            .saturating_mul(self.nodes)
            .saturating_mul(self.registry.saturating_add(64))
            .saturating_add(
                self.nodes.saturating_mul(
                    self.edges
                        .saturating_mul(32)
                        .saturating_add(self.payload.saturating_mul(8)),
                ),
            );
        let bytes = self.nodes.saturating_mul(
            1024usize
                .saturating_add(self.edges.saturating_mul(16))
                .saturating_add(self.payload.saturating_mul(8)),
        );
        self.pay(work, bytes)
    }
}
