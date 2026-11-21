// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Caller-owned sequence construction. Length normalization is an API
//! construction equivalence, not a certificate for an earlier raw assertion.

use super::{declaration_budget::Meter, sort_inspection::admit_shape};
use crate::api::{
    NativeDeclarationBudget as Budget, NativeDeclarationError as Error,
    NativeDeclarationRefusal as Refusal, Solver, Sort, Term,
};
use ay_core::{Constant, Symbol, TermData, TermId};
use std::{mem::size_of, sync::Arc};

fn unsupported<T>(meter: &mut Meter<'_>, shape: &'static str) -> Result<T, Error> {
    meter.fail(Refusal::UnsupportedSource { shape })
}

fn core_result(
    value: Result<TermId, ay_core::term::ControlledTermInternError>,
    precise: Option<Error>,
    meter: &mut Meter<'_>,
) -> Result<TermId, Error> {
    if let Some(error) = precise {
        return Err(error);
    }
    match value {
        Ok(id) => Ok(id),
        Err(ay_core::term::ControlledTermInternError::ResourceLimit) => {
            meter.fail(Refusal::Allocation)
        }
        Err(_) => unsupported(
            meter,
            "controlled sequence construction rejected its actual typed input",
        ),
    }
}

#[derive(Clone, Copy)]
enum Builder {
    Sequence,
    Scalar,
}

fn intern(
    solver: &mut Solver,
    data: &TermData,
    sort: &Sort,
    builder: Builder,
    meter: &mut Meter<'_>,
) -> Result<TermId, Error> {
    let mut precise = None;
    let mut progress = |work, bytes| match meter.pay(work, bytes, 0) {
        Ok(()) => true,
        Err(error) => {
            precise.get_or_insert(error);
            false
        }
    };
    let value = if matches!(builder, Builder::Sequence) {
        solver
            .terms_mut()
            .try_intern_sequence_with_progress(data, sort, &mut progress)
    } else {
        solver
            .terms_mut()
            .try_intern_with_progress(data, sort, &mut progress)
    };
    core_result(value, precise, meter)
}

fn application(
    solver: &mut Solver,
    name: &'static str,
    args: &[TermId],
    sort: &Sort,
    builder: Builder,
    meter: &mut Meter<'_>,
) -> Result<TermId, Error> {
    meter.pay(
        name.len().saturating_add(args.len()),
        name.len()
            .saturating_add(args.len().saturating_mul(size_of::<TermId>()))
            .saturating_add(size_of::<TermData>()),
        0,
    )?;
    let mut children = Vec::new();
    if children.try_reserve_exact(args.len()).is_err() {
        return meter.fail(Refusal::Allocation);
    }
    children.extend_from_slice(args);
    let data = TermData::App(Symbol::named(name), children);
    intern(solver, &data, sort, builder, meter)
}

fn integer(solver: &mut Solver, value: u8, meter: &mut Meter<'_>) -> Result<TermId, Error> {
    meter.pay(8, 16, 0)?;
    intern(
        solver,
        &TermData::Const(Constant::Int(value.into())),
        &Sort::Int,
        Builder::Scalar,
        meter,
    )
}

#[derive(Clone, Copy)]
enum Frame {
    Visit(TermId, usize),
    Concat(TermId, TermId, TermId),
}

#[derive(Clone, Copy)]
enum Node {
    Empty,
    Unit,
    Concat(TermId, TermId),
    Opaque,
}

#[derive(Clone, Copy)]
struct Entry {
    source: TermId,
    length: TermId,
    height: usize,
}

fn lookup(memo: &[Entry], id: TermId, meter: &mut Meter<'_>) -> Result<Option<Entry>, Error> {
    // A prepaid linear memo avoids an unaccounted auxiliary hash table. Every
    // shared DAG node is normalized once; repeated edges reuse its exact term.
    meter.pay(memo.len().saturating_add(1), 0, 0)?;
    Ok(memo.iter().find(|entry| entry.source == id).copied())
}

fn sort_height(sort: &Sort, meter: &mut Meter<'_>, depth: usize) -> Result<usize, Error> {
    meter.pay(1, 0, depth)?;
    let height =
        match sort {
            Sort::Array(array) => sort_height(&array.index_sort, meter, depth + 1)?
                .max(sort_height(&array.element_sort, meter, depth + 1)?),
            Sort::Seq(element) => sort_height(element, meter, depth + 1)?,
            _ => 0,
        };
    Ok(height + 1)
}

fn builtin_head(solver: &Solver, name: &str, meter: &mut Meter<'_>) -> Result<bool, Error> {
    let mut precise = None;
    let result =
        solver
            .terms()
            .try_sequence_head_is_builtin_with_progress(name, &mut |work, bytes| match meter
                .pay(work, bytes, 0)
            {
                Ok(()) => true,
                Err(error) => {
                    precise.get_or_insert(error);
                    false
                }
            });
    if let Some(error) = precise {
        return Err(error);
    }
    match result {
        Ok(value) => Ok(value),
        Err(_) => meter.fail(Refusal::Allocation),
    }
}

fn node(solver: &Solver, id: TermId, depth: usize, meter: &mut Meter<'_>) -> Result<Node, Error> {
    meter.pay(1, 0, depth)?;
    if solver.terms().entry_stamp(id).is_none() {
        return unsupported(meter, "sequence length encountered a non-live child");
    }
    let sort = solver.terms().sort(id);
    admit_shape(sort, meter, depth)?;
    let Sort::Seq(element) = sort else {
        return unsupported(meter, "sequence length encountered a non-sequence child");
    };
    let TermData::App(Symbol::Named(name), args) = solver.terms().get(id) else {
        return Ok(Node::Opaque);
    };
    meter.pay(name.len().saturating_add(args.len()), 0, depth)?;
    // Exact declaration provenance takes precedence over a familiar spelling.
    // The core query prices its complete retained namespace before lookup.
    if !builtin_head(solver, name, meter)? {
        return Ok(Node::Opaque);
    }
    match name.as_str() {
        "seq.empty" if args.is_empty() => Ok(Node::Empty),
        "seq.unit" if args.len() == 1 => {
            if solver.terms().entry_stamp(args[0]).is_none() {
                return unsupported(meter, "sequence unit has a non-live element");
            }
            admit_shape(solver.terms().sort(args[0]), meter, depth)?;
            if solver.terms().sort(args[0]) != element.as_ref() {
                return unsupported(
                    meter,
                    "sequence unit element disagrees with its actual carrier",
                );
            }
            Ok(Node::Unit)
        }
        "seq.++" if args.len() == 2 => {
            for &child in args {
                if solver.terms().entry_stamp(child).is_none() {
                    return unsupported(meter, "sequence concat has a non-live child");
                }
                admit_shape(solver.terms().sort(child), meter, depth)?;
                admit_shape(sort, meter, depth)?;
                if solver.terms().sort(child) != sort {
                    return unsupported(
                        meter,
                        "sequence concat children disagree with its actual carrier",
                    );
                }
            }
            Ok(Node::Concat(args[0], args[1]))
        }
        "seq.empty" | "seq.unit" | "seq.++" => {
            unsupported(meter, "sequence constructor has malformed arity")
        }
        _ => Ok(Node::Opaque),
    }
}

fn add(
    solver: &mut Solver,
    left: TermId,
    right: TermId,
    meter: &mut Meter<'_>,
) -> Result<TermId, Error> {
    if let (TermData::Const(Constant::Int(a)), TermData::Const(Constant::Int(b))) =
        (solver.terms().get(left), solver.terms().get(right))
    {
        let bytes = usize::try_from(a.bits().max(b.bits()))
            .ok()
            .and_then(|bits| bits.checked_add(64))
            .and_then(|bits| (bits / 64).max(1).checked_mul(8));
        let Some(bytes) = bytes else {
            return meter.fail(Refusal::Allocation);
        };
        // Borrowed magnitude is priced before addition allocates or copies.
        meter.pay(bytes.saturating_mul(4), bytes.saturating_mul(2), 0)?;
        let sum = a + b;
        intern(
            solver,
            &TermData::Const(Constant::Int(sum)),
            &Sort::Int,
            Builder::Scalar,
            meter,
        )
    } else {
        if !builtin_head(solver, "+", meter)? {
            return unsupported(
                meter,
                "sequence length addition head is owned by a user declaration",
            );
        }
        application(
            solver,
            "+",
            &[left, right],
            &Sort::Int,
            Builder::Scalar,
            meter,
        )
    }
}

fn normalize_length(
    solver: &mut Solver,
    root: TermId,
    meter: &mut Meter<'_>,
) -> Result<TermId, Error> {
    let physical_sort_height = sort_height(solver.terms().sort(root), meter, 1)?;
    let mut frames = Vec::new();
    let mut memo = Vec::new();
    meter.push(&mut frames, Frame::Visit(root, 1))?;
    while let Some(frame) = frames.pop() {
        meter.pay(1, 0, 0)?;
        match frame {
            Frame::Visit(id, depth) => {
                meter.pay(1, 0, depth)?;
                if let Some(entry) = lookup(&memo, id, meter)? {
                    // Include the entire cached subtree and the physical
                    // sort at its deepest node, not merely the cached root.
                    meter.pay(
                        0,
                        0,
                        depth
                            .saturating_add(entry.height - 1)
                            .saturating_add(physical_sort_height - 1),
                    )?;
                    continue;
                }
                let length = match node(solver, id, depth, meter)? {
                    Node::Empty => integer(solver, 0, meter)?,
                    Node::Unit => integer(solver, 1, meter)?,
                    Node::Opaque => application(
                        solver,
                        "seq.len",
                        &[id],
                        &Sort::Int,
                        Builder::Sequence,
                        meter,
                    )?,
                    Node::Concat(left, right) => {
                        meter.push(&mut frames, Frame::Concat(id, left, right))?;
                        meter.push(&mut frames, Frame::Visit(right, depth.saturating_add(1)))?;
                        meter.push(&mut frames, Frame::Visit(left, depth.saturating_add(1)))?;
                        continue;
                    }
                };
                meter.push(
                    &mut memo,
                    Entry {
                        source: id,
                        length,
                        height: 1,
                    },
                )?;
            }
            Frame::Concat(id, left, right) => {
                let (Some(left), Some(right)) =
                    (lookup(&memo, left, meter)?, lookup(&memo, right, meter)?)
                else {
                    return unsupported(meter, "sequence length traversal lost a completed child");
                };
                let length = add(solver, left.length, right.length, meter)?;
                let height = left.height.max(right.height).saturating_add(1);
                meter.push(
                    &mut memo,
                    Entry {
                        source: id,
                        length,
                        height,
                    },
                )?;
            }
        }
    }
    match lookup(&memo, root, meter)? {
        Some(entry) => Ok(entry.length),
        None => unsupported(meter, "sequence length traversal produced no root"),
    }
}

impl Solver {
    fn bounded_sequence_input(
        &self,
        term: Term,
        budget: &mut Budget,
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> Result<(TermId, Sort), Error> {
        let actual = self.try_engine_term_sort_with_progress(term, budget, progress)?;
        let current = self.try_live_sort_with_progress(&actual, budget, progress)?;
        let mut meter = Meter {
            budget,
            progress,
            interrupt: Arc::clone(&self.interrupt),
            deadline: self.executor.current_solve_deadline(),
        };
        // Both complete physical descriptions were prepaid before this Eq.
        if actual != current {
            return unsupported(&mut meter, "sequence operation has a stale nominal carrier");
        }
        let id = self.resolve_term("bounded sequence operation", term)?;
        meter.pay(0, 0, 0)?;
        Ok((id, actual))
    }

    /// Construct a singleton from the authenticated element and its current
    /// exact carrier through the caller's original cumulative owner.
    pub fn try_seq_unit_with_progress(
        &mut self,
        element: Term,
        budget: &mut Budget,
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> Result<Term, Error> {
        let (id, element_sort) = self.bounded_sequence_input(element, budget, progress)?;
        let mut meter = Meter {
            budget,
            progress,
            interrupt: Arc::clone(&self.interrupt),
            deadline: self.executor.current_solve_deadline(),
        };
        meter.pay(1, size_of::<Sort>(), 0)?;
        let sort = Sort::seq(element_sort);
        let id = application(
            self,
            "seq.unit",
            &[id],
            &sort,
            Builder::Sequence,
            &mut meter,
        )?;
        meter.pay(0, 0, 0)?;
        Ok(self.wrap_term(id))
    }

    /// Construct a binary concat after authenticating BOTH complete inputs.
    /// No empty-side rewrite skips handle, sort, depth or resource validation.
    pub fn try_seq_concat_with_progress(
        &mut self,
        left: Term,
        right: Term,
        budget: &mut Budget,
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> Result<Term, Error> {
        let (left, sort) = self.bounded_sequence_input(left, budget, progress)?;
        let (right, right_sort) = self.bounded_sequence_input(right, budget, progress)?;
        let mut meter = Meter {
            budget,
            progress,
            interrupt: Arc::clone(&self.interrupt),
            deadline: self.executor.current_solve_deadline(),
        };
        if !matches!(sort, Sort::Seq(_)) || sort != right_sort {
            return unsupported(
                &mut meter,
                "sequence concat requires identical actual sequence carriers",
            );
        }
        let id = application(
            self,
            "seq.++",
            &[left, right],
            &sort,
            Builder::Sequence,
            &mut meter,
        )?;
        meter.pay(0, 0, 0)?;
        Ok(self.wrap_term(id))
    }

    /// Construct length using exactly |empty|=0, |unit(x)|=1 and
    /// |a++b|=|a|+|b|. An iterative, memoized, paid DAG walk retains a raw
    /// length application on every opaque leaf. No assertion, membership fact,
    /// declaration or source event is added. This does not certify previously
    /// issued raw input; those inputs still require checked proof transport.
    pub fn try_seq_len_with_progress(
        &mut self,
        sequence: Term,
        budget: &mut Budget,
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> Result<Term, Error> {
        let (root, sort) = self.bounded_sequence_input(sequence, budget, progress)?;
        let mut meter = Meter {
            budget,
            progress,
            interrupt: Arc::clone(&self.interrupt),
            deadline: self.executor.current_solve_deadline(),
        };
        if !matches!(sort, Sort::Seq(_)) {
            return unsupported(
                &mut meter,
                "sequence length requires an actual sequence carrier",
            );
        }
        // The operation itself can be a user identity even when its input is
        // a genuine ground sequence. No fold bypasses this exact-name guard.
        if !builtin_head(self, "seq.len", &mut meter)? {
            return unsupported(
                &mut meter,
                "sequence length head is owned by a user declaration",
            );
        }
        let id = normalize_length(self, root, &mut meter)?;
        meter.pay(0, 0, 0)?;
        Ok(self.wrap_term(id))
    }
}
