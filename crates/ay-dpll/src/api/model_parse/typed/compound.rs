// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::{ArraySort, DatatypeSort};

mod floating_point;

impl Decoder<'_> {
    pub(super) fn array(
        &mut self,
        value: &SExpr,
        sort: &ArraySort,
        depth: usize,
    ) -> Option<ModelValue> {
        let mut cursor = value;
        let mut count = 0usize;
        while let Some([head, base, _, _]) = cursor.as_list() {
            self.charge(1)?;
            if !head.is_symbol("store") {
                break;
            }
            count = count.checked_add(1)?;
            cursor = base;
        }
        self.copy(count.checked_mul(std::mem::size_of::<(ModelValue, ModelValue)>())?)?;
        let mut stores = Vec::new();
        stores.try_reserve_exact(count).ok()?;
        cursor = value;
        for _ in 0..count {
            self.charge(1)?;
            let [_, base, index, element] = cursor.as_list()? else {
                return None;
            };
            stores.push((
                self.value(index, &sort.index_sort, depth + 1)?,
                self.value(element, &sort.element_sort, depth + 1)?,
            ));
            cursor = base;
        }
        let [head, default] = cursor.as_list()? else {
            return None;
        };
        let [as_word, const_word, ascription] = head.as_list()? else {
            return None;
        };
        if !as_word.is_symbol("as") || !const_word.is_symbol("const") {
            return None;
        }
        let [array_word, index, element] = ascription.as_list()? else {
            return None;
        };
        if !array_word.is_symbol("Array") {
            return None;
        }
        self.ascribed(index, &sort.index_sort, depth + 1)?;
        self.ascribed(element, &sort.element_sort, depth + 1)?;
        let default = Box::new(self.value(default, &sort.element_sort, depth + 1)?);
        stores.reverse();
        Some(ModelValue::Array { default, stores })
    }

    pub(super) fn datatype(
        &mut self,
        value: &SExpr,
        sort: &DatatypeSort,
        depth: usize,
    ) -> Option<ModelValue> {
        let (name, arguments) = match value {
            SExpr::Symbol(name) => (name.as_str(), &[][..]),
            SExpr::List(items) => match items.as_slice() {
                [head, constructor, ascription] if head.is_symbol("as") => {
                    self.charge(sort.name.len())?;
                    if !ascription.is_symbol(&sort.name) {
                        return None;
                    }
                    (constructor.as_symbol()?, &[][..])
                }
                [head, arguments @ ..] => {
                    let name = match head {
                        SExpr::Symbol(name) => name.as_str(),
                        SExpr::List(qualified) => {
                            let [as_word, constructor, ascription] = qualified.as_slice() else {
                                return None;
                            };
                            self.charge(sort.name.len())?;
                            if !as_word.is_symbol("as") || !ascription.is_symbol(&sort.name) {
                                return None;
                            }
                            constructor.as_symbol()?
                        }
                        _ => return None,
                    };
                    (name, arguments)
                }
                _ => return None,
            },
            _ => return None,
        };
        let mut found = None;
        for constructor in &sort.constructors {
            self.charge(
                constructor
                    .name
                    .len()
                    .checked_add(name.len())?
                    .checked_add(1)?,
            )?;
            if constructor.name == name {
                if found.is_some() {
                    return None;
                }
                found = Some(constructor);
            }
        }
        let constructor = found?;
        if constructor.fields.len() != arguments.len() {
            return None;
        }
        self.copy(
            name.len().checked_add(
                arguments
                    .len()
                    .checked_mul(std::mem::size_of::<ModelValue>())?,
            )?,
        )?;
        let mut args = Vec::new();
        args.try_reserve_exact(arguments.len()).ok()?;
        for (argument, field) in arguments.iter().zip(&constructor.fields) {
            args.push(self.value(argument, &field.sort, depth + 1)?);
        }
        Some(ModelValue::Datatype {
            constructor: name.to_owned(),
            args,
        })
    }

    pub(super) fn sequence(
        &mut self,
        value: &SExpr,
        sort: &Sort,
        depth: usize,
    ) -> Option<ModelValue> {
        self.copy(std::mem::size_of::<&SExpr>())?;
        let mut pending = vec![value];
        let mut values = Vec::new();
        while let Some(value) = pending.pop() {
            self.charge(1)?;
            if value.is_symbol("seq.empty") {
                continue;
            }
            match value.as_list()? {
                [as_word, empty, ascription]
                    if as_word.is_symbol("as") && empty.is_symbol("seq.empty") =>
                {
                    let [seq_word, element] = ascription.as_list()? else {
                        return None;
                    };
                    if !seq_word.is_symbol("Seq") {
                        return None;
                    }
                    self.ascribed(element, sort, depth + 1)?;
                }
                [head, element] if head.is_symbol("seq.unit") => {
                    self.copy(std::mem::size_of::<ModelValue>().checked_mul(2)?)?;
                    values.try_reserve(1).ok()?;
                    values.push(self.value(element, sort, depth + 1)?);
                }
                [head, parts @ ..] if head.is_symbol("seq.++") && parts.len() >= 2 => {
                    self.charge(parts.len())?;
                    self.copy(parts.len().checked_mul(std::mem::size_of::<&SExpr>())?)?;
                    pending.try_reserve_exact(parts.len()).ok()?;
                    pending.extend(parts.iter().rev());
                }
                _ => return None,
            }
        }
        Some(ModelValue::Seq(values))
    }
}
