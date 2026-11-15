// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Borrowed exact-carrier datatype decoding. Recursive declarations are not
//! expanded into recursive Sort trees: only finite constructor values recurse.
//! Parametric carriers are deliberately refused in this first seam because
//! their hidden argument metadata needs a separately bounded output resolver.

use super::*;
use ay_frontend::Context;

impl Decoder<'_> {
    /// Caller charges the carrier spelling before the borrowed registry lookup.
    pub(super) fn registered_sort(&self, carrier: &str) -> Option<()> {
        let context = self.context?;
        if carrier.is_empty()
            || carrier == "RoundingMode"
            || context.is_parametric_datatype_instance(carrier)
        {
            return None;
        }
        match context.datatype_constructors(carrier) {
            Some(constructors) => (!constructors.is_empty()).then_some(()),
            None => Some(()),
        }
    }

    pub(super) fn registered(
        &mut self,
        value: &SExpr,
        carrier: &str,
        depth: usize,
    ) -> Option<ModelValue> {
        self.charge(carrier.len().checked_add(1)?)?;
        self.registered_sort(carrier)?;
        let context = self.context?;
        if context.datatype_constructors(carrier).is_none() {
            return self.abstract_value(value, carrier);
        }
        let (name, arguments) = constructor_parts(value, carrier)?;
        self.charge(name.len().checked_add(arguments.len())?)?;
        let output_work = self.output_name_work(context)?;
        let mut chosen = None;
        for identity in context.datatype_constructors(carrier)? {
            self.charge(identity.len().checked_add(1)?)?;
            // output_symbol_name may scan all sticky declaration members.
            // The complete borrowed census is charged before each such call.
            self.charge(output_work)?;
            let printed = context.output_symbol_name(identity);
            if printed != name {
                continue;
            }
            if chosen.is_some() {
                return None;
            }
            let signature = context.exact_datatype_member_info(identity)?;
            let Sort::Uninterpreted(result) = &signature.sort else {
                return None;
            };
            if result != carrier {
                return None;
            }
            let fields = context.constructor_selector_info(identity)?;
            if fields.len() != arguments.len() || fields.len() != signature.arg_sorts.len() {
                return None;
            }
            for ((_, field), declared) in fields.iter().zip(&signature.arg_sorts) {
                self.same_engine_sort(field, declared, 0)?;
                self.sort(field, depth.checked_add(1)?)?;
            }
            chosen = Some((printed, fields));
        }
        let (constructor, fields) = chosen?;
        self.copy(constructor.len())?;
        self.copy(
            fields
                .len()
                .checked_mul(std::mem::size_of::<ModelValue>())?,
        )?;
        let mut values = Vec::new();
        values.try_reserve_exact(fields.len()).ok()?;
        for (argument, (_, sort)) in arguments.iter().zip(fields) {
            values.push(self.value(argument, sort, depth.checked_add(1)?)?);
        }
        Some(ModelValue::Datatype {
            constructor: constructor.to_owned(),
            args: values,
        })
    }

    fn abstract_value(&mut self, value: &SExpr, carrier: &str) -> Option<ModelValue> {
        let atom = match value {
            SExpr::Symbol(atom) => atom.as_str(),
            _ => qualified_head(value, carrier)?,
        };
        self.charge(atom.len())?;
        let digits = atom
            .strip_prefix('@')?
            .strip_prefix(carrier)?
            .strip_prefix('!')?;
        if digits.is_empty()
            || !digits.bytes().all(|byte| byte.is_ascii_digit())
            || (digits.len() > 1 && digits.starts_with('0'))
        {
            return None;
        }
        self.copy(atom.len())?;
        Some(ModelValue::Uninterpreted(atom.to_owned()))
    }

    /// Account all retained carriers and constructor/selector/tester identities
    /// before the frontend's existing output-name scan. The requested carrier
    /// is monomorphic, so comparisons against parametric descriptors stop at
    /// their distinct descriptor variant, not recursively expanded arguments.
    /// This is deterministic work accounting, not an allocator/RSS guarantee.
    fn output_name_work(&mut self, context: &Context) -> Option<usize> {
        let mut work = 1usize;
        for (carrier, constructors) in context.datatype_iter() {
            let names = carrier
                .len()
                .checked_add(context.sort_surface_name(carrier).len())?;
            self.charge(names.checked_add(1)?)?;
            for identity in constructors {
                let names = names
                    .checked_add(identity.len())?
                    .checked_add(context.dt_surface_name(identity).unwrap_or(identity).len())?;
                self.charge(names.checked_add(1)?)?;
                // Constructor and tester; the latter adds the fixed "is-".
                work = work.checked_add(names.checked_add(8)?.checked_mul(2)?)?;
                for (selector, _) in context.constructor_selector_info(identity)? {
                    let names = names
                        .checked_add(selector.len())?
                        .checked_add(context.dt_surface_name(selector).unwrap_or(selector).len())?;
                    self.charge(names.checked_add(1)?)?;
                    work = work.checked_add(names.checked_add(8)?)?;
                }
            }
        }
        Some(work)
    }

    /// Compare exact engine metadata without recursive derived Sort equality.
    /// Nominal fields are references to sticky carriers, not schema expansion.
    fn same_engine_sort(&mut self, left: &Sort, right: &Sort, depth: usize) -> Option<()> {
        self.charge(1)?;
        if depth > MAX_DEPTH {
            return None;
        }
        match (left, right) {
            (Sort::Bool, Sort::Bool)
            | (Sort::Int, Sort::Int)
            | (Sort::Real, Sort::Real)
            | (Sort::Complex, Sort::Complex)
            | (Sort::String, Sort::String) => Some(()),
            (Sort::BitVec(a), Sort::BitVec(b)) => (a.width == b.width).then_some(()),
            (Sort::FloatingPoint(a, b), Sort::FloatingPoint(c, d)) => {
                (a == c && b == d).then_some(())
            }
            (Sort::Uninterpreted(a), Sort::Uninterpreted(b)) => {
                self.charge(a.len().checked_add(b.len())?)?;
                (a == b).then_some(())
            }
            (Sort::Array(a), Sort::Array(b)) => {
                self.same_engine_sort(&a.index_sort, &b.index_sort, depth + 1)?;
                self.same_engine_sort(&a.element_sort, &b.element_sort, depth + 1)
            }
            (Sort::Seq(a), Sort::Seq(b)) => self.same_engine_sort(a, b, depth + 1),
            _ => None,
        }
    }
}

fn constructor_parts<'a>(value: &'a SExpr, carrier: &str) -> Option<(&'a str, &'a [SExpr])> {
    match value {
        SExpr::Symbol(name) => Some((name, &[])),
        SExpr::List(items) if items.first().is_some_and(|head| head.is_symbol("as")) => {
            Some((qualified_head(value, carrier)?, &[]))
        }
        SExpr::List(items) => {
            let (head, arguments) = items.split_first()?;
            let name = match head {
                SExpr::Symbol(name) => name.as_str(),
                _ => qualified_head(head, carrier)?,
            };
            Some((name, arguments))
        }
        _ => None,
    }
}

fn qualified_head<'a>(head: &'a SExpr, carrier: &str) -> Option<&'a str> {
    let [marker, name, sort] = head.as_list()? else {
        return None;
    };
    // Never resolve an old carrier through the current live surface namespace.
    // More elaborate/parametric ascriptions conservatively remain unsupported.
    (marker.is_symbol("as") && sort.is_symbol(carrier)).then_some(name.as_symbol()?)
}

#[cfg(test)]
mod tests;
