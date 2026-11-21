// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded encoding of live typed input. No decoder can mint scope authority.

use super::*;
use ay_core::term::TermData;
use ay_frontend::{DeclarationKind, PublicSort};
use sha2::{Digest, Sha256};
use std::collections::BTreeSet;
use std::io::{self, Write};

pub(super) struct Control<'a> {
    progress: &'a mut dyn FnMut(usize, usize) -> bool,
    work: usize,
    bytes: usize,
    stopped: bool,
}

impl<'a> Control<'a> {
    pub(super) fn new(progress: &'a mut dyn FnMut(usize, usize) -> bool) -> Self {
        Self {
            progress,
            work: 0,
            bytes: 0,
            stopped: false,
        }
    }

    pub(super) fn charge(&mut self, work: usize, bytes: usize) -> Option<()> {
        if self.stopped {
            return None;
        }
        let Some((work_total, byte_total)) = self
            .work
            .checked_add(work)
            .zip(self.bytes.checked_add(bytes))
        else {
            self.stopped = true;
            return None;
        };
        self.work = work_total;
        self.bytes = byte_total;
        self.stopped = self.work > MAX_SOURCE_WORK
            || self.bytes > MAX_SOURCE_BYTES
            || !(self.progress)(work, bytes);
        (!self.stopped).then_some(())
    }
}

struct HashWriter<'a, 'b> {
    hash: Sha256,
    control: &'a mut Control<'b>,
}

impl<'a, 'b> HashWriter<'a, 'b> {
    fn new(domain: &[u8], control: &'a mut Control<'b>) -> Option<Self> {
        let mut writer = Self {
            hash: Sha256::new(),
            control,
        };
        writer.write_all(domain).ok()?;
        Some(writer)
    }

    fn finish(self) -> Option<[u8; 32]> {
        self.control.charge(0, 0)?;
        Some(self.hash.finalize().into())
    }
}

// Keep typed borrowed serialization at each call site: serde_json supplies
// the serializer without allocating an intermediate JSON value or requiring
// the solver crate to expose a second serialization API.
macro_rules! hash_value {
    ($writer:ident, $value:expr) => {{
        serde_json::to_writer(&mut $writer, $value).ok()?;
        $writer.write_all(&[0]).ok()?;
    }};
}

impl Write for HashWriter<'_, '_> {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        self.control
            .charge(1, bytes.len())
            .ok_or_else(|| io::Error::other("native source capture stopped"))?;
        self.hash.update(bytes);
        Ok(bytes.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

pub(super) fn validate_sort(
    sort: &Sort,
    depth: usize,
    copy: bool,
    control: &mut Control<'_>,
) -> Option<()> {
    control.charge(1, if copy { std::mem::size_of::<Sort>() } else { 0 })?;
    if depth == 0 {
        return None;
    }
    match sort {
        Sort::Bool
        | Sort::Int
        | Sort::Real
        | Sort::BitVec(_)
        | Sort::String
        | Sort::RegLan
        | Sort::FloatingPoint(..)
        | Sort::Char => Some(()),
        Sort::Array(array) => {
            validate_sort(&array.index_sort, depth - 1, copy, control)?;
            validate_sort(&array.element_sort, depth - 1, copy, control)
        }
        Sort::Seq(element) => validate_sort(element, depth - 1, copy, control),
        Sort::Uninterpreted(name) => {
            if name.len() > 4096 {
                return None;
            }
            control.charge(name.len(), if copy { name.len() } else { 0 })
        }
        _ => None,
    }
}

fn public_sort_matches(public: &PublicSort, core: &Sort) -> bool {
    match (public, core) {
        (PublicSort::Array(index, element), Sort::Array(array)) => {
            public_sort_matches(index, &array.index_sort)
                && public_sort_matches(element, &array.element_sort)
        }
        (PublicSort::Seq(element), Sort::Seq(core_element)) => {
            public_sort_matches(element, core_element)
        }
        (PublicSort::Core(actual), core) if !matches!(core, Sort::Array(_) | Sort::Seq(_)) => {
            actual == core
        }
        _ => false,
    }
}

pub(super) fn declarations(
    executor: &Executor,
    datatypes: &datatype_context::NativeDatatypeContext,
    control: &mut Control<'_>,
) -> Option<(Vec<NativeDeclarationBinding>, [u8; 32])> {
    let mut bindings = Vec::new();
    for (name, info) in executor.ctx.symbols_iter() {
        control.charge(1, 0)?;
        if executor.ctx.is_defined_fun(name) {
            return None;
        }
        if executor.ctx.is_internal_symbol(name) {
            continue;
        }
        control.charge(datatypes.signatures().len(), 0)?;
        if datatypes.contains_binding(executor, name, info) {
            continue;
        }
        if bindings.len() >= MAX_SOURCE_DECLARATIONS
            || name.len() > 4096
            || info.arg_sorts.len() > MAX_SOURCE_DECLARATIONS
            || executor
                .ctx
                .effective_declaration_kind(info.declaration_identity())
                != Some(DeclarationKind::Uninterpreted)
        {
            return None;
        }
        validate_sort(&info.sort, 32, true, control)?;
        datatypes.admits_sort(&info.sort, control)?;
        for sort in &info.arg_sorts {
            validate_sort(sort, 32, true, control)?;
            datatypes.admits_sort(sort, control)?;
        }
        if !public_sort_matches(&info.public_sort, &info.sort)
            || info.public_arg_sorts.len() != info.arg_sorts.len()
            || info
                .public_arg_sorts
                .iter()
                .zip(&info.arg_sorts)
                .any(|(public, core)| !public_sort_matches(public, core))
        {
            return None;
        }
        let identity_name = executor.ctx.symbol_identity_name(name, info);
        if identity_name.len() > 4096 {
            return None;
        }
        control.charge(
            info.arg_sorts.len(),
            name.len()
                .checked_add(identity_name.len())?
                .checked_add(std::mem::size_of::<NativeDeclarationBinding>())?,
        )?;
        let constant = match info.term {
            Some(term) => {
                if term.index() >= executor.ctx.terms.len()
                    || !info.arg_sorts.is_empty()
                    || executor.ctx.terms.sort(term) != &info.sort
                    || !matches!(executor.ctx.terms.get(term), TermData::Var(actual, _) if actual == identity_name)
                {
                    return None;
                }
                Some((term, executor.ctx.terms.entry_stamp(term)?))
            }
            None => None,
        };
        bindings.push(NativeDeclarationBinding {
            name: name.clone(),
            symbol: Symbol::named(identity_name),
            identity: info.declaration_identity().clone(),
            domain: info.arg_sorts.clone().into_boxed_slice(),
            range: info.sort.clone(),
            constant,
        });
    }
    bindings.sort_by(|a, b| a.symbol.name().cmp(b.symbol.name()));
    if bindings
        .windows(2)
        .any(|pair| pair[0].symbol == pair[1].symbol)
    {
        return None;
    }
    let mut writer = HashWriter::new(
        if datatypes.declarations().is_empty() {
            b"ay.native-source.declarations.v1\0"
        } else {
            b"ay.native-source.declarations.v2\0"
        },
        control,
    )?;
    if !datatypes.declarations().is_empty() {
        hash_value!(writer, &datatypes.declarations());
        hash_value!(writer, &datatypes.selectors());
        hash_value!(writer, &datatypes.signatures());
        hash_value!(writer, &datatypes.live_bindings());
    }
    hash_value!(writer, &bindings.len());
    for binding in &bindings {
        hash_value!(
            writer,
            &(
                &binding.name,
                &binding.symbol,
                &binding.domain,
                &binding.range,
            )
        );
        let constant = binding.constant.map(|(term, _)| {
            (
                term,
                executor.ctx.terms.get(term),
                executor.ctx.terms.sort(term),
            )
        });
        hash_value!(writer, &constant);
    }
    Some((bindings, writer.finish()?))
}

pub(super) fn declarations_are_current(
    executor: &Executor,
    bindings: &[NativeDeclarationBinding],
    datatypes: &datatype_context::NativeDatatypeContext,
) -> bool {
    let mut count = 0;
    for (name, info) in executor.ctx.symbols_iter() {
        if executor.ctx.is_internal_symbol(name) {
            continue;
        }
        if datatypes.contains_binding(executor, name, info) {
            continue;
        }
        count += 1;
        let Some(binding) = bindings.iter().find(|binding| {
            &binding.identity == info.declaration_identity()
                && binding.name == *name
                && binding.symbol.name() == executor.ctx.symbol_identity_name(name, info)
        }) else {
            return false;
        };
        if binding.domain.as_ref() != info.arg_sorts.as_slice()
            || binding.range != info.sort
            || binding.constant.map(|(term, _)| term) != info.term
            || binding
                .constant
                .is_some_and(|(term, entry)| executor.ctx.terms.entry_stamp(term) != Some(entry))
            || executor.ctx.effective_declaration_kind(&binding.identity)
                != Some(DeclarationKind::Uninterpreted)
        {
            return false;
        }
    }
    count == bindings.len()
}

pub(super) fn query_digest(
    executor: &Executor,
    roots: &[TermId],
    declarations: [u8; 32],
    datatypes: &datatype_context::NativeDatatypeContext,
    control: &mut Control<'_>,
) -> Option<([u8; 32], Vec<(TermId, TermEntryStamp)>)> {
    let terms = &executor.ctx.terms;
    let mut seen = BTreeSet::new();
    control.charge(
        roots.len(),
        roots.len().checked_mul(std::mem::size_of::<TermId>())?,
    )?;
    let mut pending = roots.to_vec();
    while let Some(term) = pending.pop() {
        control.charge(1, 0)?;
        if term.index() >= terms.len() {
            return None;
        }
        control.charge(0, std::mem::size_of::<TermId>() * 4)?;
        if !seen.insert(term) {
            continue;
        }
        if seen.len() > MAX_SOURCE_TERMS {
            return None;
        }
        validate_sort(terms.sort(term), 32, false, control)?;
        datatypes.admits_sort(terms.sort(term), control)?;
        match terms.get(term) {
            TermData::Const(_) => {}
            TermData::Var(name, _) => {
                if terms.is_skolem_symbol(name) || terms.skolem_choice(term).is_some() {
                    return None;
                }
            }
            TermData::App(symbol, args) => {
                if terms.is_skolem_symbol(symbol.name()) {
                    return None;
                }
                control.charge(
                    args.len(),
                    args.len().checked_mul(std::mem::size_of::<TermId>())?,
                )?;
                pending.extend(args);
            }
            TermData::Not(inner) => {
                control.charge(1, std::mem::size_of::<TermId>())?;
                pending.push(*inner);
            }
            TermData::Ite(a, b, c) => {
                control.charge(3, std::mem::size_of::<TermId>() * 3)?;
                pending.extend([*a, *b, *c]);
            }
            TermData::Let(bindings, body) => {
                control.charge(
                    bindings.len(),
                    bindings.len().checked_mul(std::mem::size_of::<TermId>())?,
                )?;
                pending.extend(bindings.iter().map(|(_, term)| *term));
                pending.push(*body);
            }
            TermData::Forall(vars, body, triggers) | TermData::Exists(vars, body, triggers) => {
                control.charge(vars.len(), 0)?;
                for (_, sort) in vars {
                    validate_sort(sort, 32, false, control)?;
                    datatypes.admits_sort(sort, control)?;
                }
                pending.push(*body);
                for trigger in triggers {
                    control.charge(
                        trigger.len(),
                        trigger.len().checked_mul(std::mem::size_of::<TermId>())?,
                    )?;
                    pending.extend(trigger);
                }
            }
            _ => return None,
        }
        if pending.len() > MAX_SOURCE_TERMS {
            return None;
        }
    }
    let mut writer = HashWriter::new(b"ay.native-source.query.v1\0", control)?;
    hash_value!(writer, &executor.ctx.scope_depth());
    hash_value!(writer, &executor.logic());
    hash_value!(writer, &terms.checker_visible_metadata_generation());
    hash_value!(
        writer,
        &(terms.to_real_is_shadowed(), terms.is_int_is_shadowed())
    );
    hash_value!(writer, &roots);
    hash_value!(writer, &declarations);
    hash_value!(writer, &seen.len());
    for &term in &seen {
        hash_value!(writer, &(term, terms.get(term), terms.sort(term)));
    }
    let digest = writer.finish()?;
    control.charge(
        seen.len(),
        seen.len()
            .checked_mul(std::mem::size_of::<(TermId, TermEntryStamp)>())?,
    )?;
    let entries: Option<Vec<_>> = seen
        .into_iter()
        .map(|term| Some((term, terms.entry_stamp(term)?)))
        .collect();
    Some((digest, entries?))
}
