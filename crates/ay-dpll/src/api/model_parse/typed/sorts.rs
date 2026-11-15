// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::collections::BTreeSet;

impl Decoder<'_> {
    pub(super) fn sort(&mut self, sort: &Sort, depth: usize) -> Option<()> {
        self.charge(1)?;
        if depth > MAX_DEPTH {
            return None;
        }
        match sort {
            Sort::Bool
            | Sort::Int
            | Sort::Real
            | Sort::Complex
            | Sort::String
            | Sort::FiniteField(_) => Some(()),
            Sort::BitVec(width) => (width.width > 0).then_some(()),
            Sort::FloatingPoint(eb, sb) => (*eb >= 2 && *sb >= 2).then_some(()),
            Sort::Array(array) => {
                self.sort(&array.index_sort, depth + 1)?;
                self.sort(&array.element_sort, depth + 1)
            }
            Sort::Seq(element) => self.sort(element, depth + 1),
            Sort::Uninterpreted(carrier) => {
                self.charge(carrier.len().checked_add(1)?)?;
                self.registered_sort(carrier)
            }
            Sort::Datatype(datatype) => {
                self.charge(datatype.name.len())?;
                if datatype.name.is_empty() || datatype.constructors.is_empty() {
                    return None;
                }
                let mut names = BTreeSet::new();
                for constructor in &datatype.constructors {
                    self.charge(constructor.name.len().checked_add(1)?)?;
                    self.copy(512)?;
                    if constructor.name.is_empty() || !names.insert(constructor.name.as_str()) {
                        return None;
                    }
                    let mut fields = BTreeSet::new();
                    for field in &constructor.fields {
                        self.charge(field.name.len().checked_add(1)?)?;
                        self.copy(512)?;
                        if field.name.is_empty() || !fields.insert(field.name.as_str()) {
                            return None;
                        }
                        self.sort(&field.sort, depth + 1)?;
                    }
                }
                Some(())
            }
            _ => None,
        }
    }

    pub(super) fn ascribed(&mut self, text: &SExpr, expected: &Sort, depth: usize) -> Option<()> {
        self.charge(1)?;
        if depth > MAX_DEPTH {
            return None;
        }
        match expected {
            Sort::Bool if text.is_symbol("Bool") => Some(()),
            Sort::Int if text.is_symbol("Int") => Some(()),
            Sort::Real if text.is_symbol("Real") => Some(()),
            Sort::Complex if text.is_symbol("Complex") => Some(()),
            Sort::FiniteField(field) => {
                let [underscore, name, p] = text.as_list()? else {
                    return None;
                };
                (underscore.is_symbol("_")
                    && name.is_symbol("FiniteField")
                    && p.to_string() == field.modulus().to_string())
                .then_some(())
            }
            Sort::String if text.is_symbol("String") => Some(()),
            Sort::Datatype(datatype) => {
                self.charge(datatype.name.len())?;
                text.is_symbol(&datatype.name).then_some(())
            }
            Sort::Uninterpreted(carrier) if self.context.is_some() => {
                self.charge(carrier.len().checked_add(1)?)?;
                self.registered_sort(carrier)?;
                text.is_symbol(carrier).then_some(())
            }
            Sort::BitVec(width) => {
                let [head, kind, size] = text.as_list()? else {
                    return None;
                };
                (head.is_symbol("_") && kind.is_symbol("BitVec") && numeral(size)? == width.width)
                    .then_some(())
            }
            Sort::FloatingPoint(eb, sb) => {
                let [head, kind, exponent, significand] = text.as_list()? else {
                    return None;
                };
                (head.is_symbol("_")
                    && kind.is_symbol("FloatingPoint")
                    && numeral(exponent)? == *eb
                    && numeral(significand)? == *sb)
                    .then_some(())
            }
            Sort::Array(array) => {
                let [head, index, element] = text.as_list()? else {
                    return None;
                };
                if !head.is_symbol("Array") {
                    return None;
                }
                self.ascribed(index, &array.index_sort, depth + 1)?;
                self.ascribed(element, &array.element_sort, depth + 1)
            }
            Sort::Seq(element) => {
                let [head, item] = text.as_list()? else {
                    return None;
                };
                if !head.is_symbol("Seq") {
                    return None;
                }
                self.ascribed(item, element, depth + 1)
            }
            _ => None,
        }
    }
}

pub(super) fn numeral(value: &SExpr) -> Option<u32> {
    let SExpr::Numeral(text) = value else {
        return None;
    };
    if text.is_empty() || !text.bytes().all(|byte| byte.is_ascii_digit()) {
        return None;
    }
    text.parse().ok()
}
