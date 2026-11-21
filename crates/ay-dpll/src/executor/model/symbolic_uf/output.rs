// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Physical symbolic-definition output, separate from source lookup work.

use super::{Executor, SymbolicUfDefinition, SymbolicUfModel};
use ay_core::{Sort, TermData};
use std::mem::size_of;

#[cfg(test)]
mod tests;

fn quoted_bytes(name: &str) -> Option<usize> {
    name.len().checked_mul(2)?.checked_add(2)
}

impl SymbolicUfModel {
    fn output_sort_bytes(&self, exec: &Executor, sort: &Sort, depth: usize) -> Option<usize> {
        if depth > 64 || !self.pay_for(exec, 1, 0) {
            return None;
        }
        match sort {
            Sort::Bool => Some(4),
            Sort::Int => Some(3),
            Sort::Real => Some(4),
            Sort::Array(array) => self
                .output_sort_bytes(exec, &array.index_sort, depth + 1)?
                .checked_add(self.output_sort_bytes(exec, &array.element_sort, depth + 1)?)?
                .checked_add(9),
            _ => None,
        }
    }

    /// Full source currency was checked once under the caller's immutable
    /// Executor/Model borrows. This additionally prices and checks the exact
    /// selected signature before copying any output. Namespace/probe work is
    /// deliberately NOT an output-byte count.
    pub(in crate::executor::model) fn render_definition(
        &self,
        exec: &Executor,
        name: &str,
        actual_domain: &[Sort],
        actual_range: &Sort,
        definition: &SymbolicUfDefinition,
        output_len: usize,
        output_capacity: usize,
    ) -> Option<String> {
        let prepared = (|| {
            let mut bytes = 64usize
                .checked_add(quoted_bytes(name)?)?
                .checked_add(definition.rendered_body.len())?;
            let mut quote_bytes = quoted_bytes(name)?;
            let range_bytes = self.output_sort_bytes(exec, actual_range, 0)?;
            // Walk BOTH actual and retained metadata before structural Eq.
            self.output_sort_bytes(exec, definition.binding.result_sort(), 0)?;
            bytes = bytes.checked_add(range_bytes)?;
            if actual_domain.len() != definition.parameters.len()
                || actual_domain.len() != definition.binding.parameter_sorts().len()
            {
                return None;
            }
            for ((&parameter, actual), retained) in definition
                .parameters
                .iter()
                .zip(actual_domain)
                .zip(definition.binding.parameter_sorts())
            {
                self.pay_for(exec, 1, 0).then_some(())?;
                let TermData::Var(parameter, _) = exec.ctx.terms.get(parameter) else {
                    return None;
                };
                let quoted = quoted_bytes(parameter)?;
                quote_bytes = quote_bytes.checked_add(quoted)?;
                bytes = bytes
                    .checked_add(quoted)?
                    .checked_add(self.output_sort_bytes(exec, actual, 0)?)?
                    .checked_add(4)?;
                self.output_sort_bytes(exec, retained, 0)?;
            }
            // Source signature comparison, quoting scans, direct rendering,
            // and later join/model copies. Symbols use the fixed reserved
            // vocabulary plus linear UTF-8 escaping; 256 per byte bounds it.
            let work = bytes.checked_mul(256)?.checked_add(quote_bytes)?;
            // Four copies cover the retained definition, final definition
            // join and whole model formatting; quoted symbols are separate
            // temporary allocations. Vector backing is moved, not deep copied.
            let storage = bytes
                .checked_mul(4)?
                // quote_symbol may geometrically grow an escaped symbol;
                // include old/new backing and cumulative temporary copies.
                .checked_add(quote_bytes.checked_mul(4)?)?
                .checked_add(
                    output_len
                        .checked_add(1)?
                        .checked_mul(2)?
                        .checked_add(output_capacity)?
                        .checked_mul(size_of::<String>())?,
                )?;
            self.pay_for(exec, work, storage).then_some(())?;
            if actual_domain != definition.binding.parameter_sorts()
                || actual_range != definition.binding.result_sort()
            {
                return None;
            }
            let mut text = String::new();
            text.try_reserve_exact(bytes).ok()?;
            text.push_str("  (define-fun ");
            text.push_str(&ay_core::quote_symbol(name));
            text.push_str(" (");
            for (index, (&parameter, sort)) in
                definition.parameters.iter().zip(actual_domain).enumerate()
            {
                let TermData::Var(parameter, _) = exec.ctx.terms.get(parameter) else {
                    return None;
                };
                if index != 0 {
                    text.push(' ');
                }
                text.push('(');
                text.push_str(&ay_core::quote_symbol(parameter));
                text.push(' ');
                append_sort(&mut text, sort)?;
                text.push(')');
            }
            text.push_str(") ");
            append_sort(&mut text, actual_range)?;
            text.push_str("\n    ");
            text.push_str(&definition.rendered_body);
            text.push(')');
            debug_assert!(text.len() <= bytes);
            Some(text)
        })();
        if prepared.is_none() {
            self.refuse();
        }
        prepared
    }
}

// Only the admitted closed Bool/Int/Real/Array signature fragment reaches
// this renderer. It writes canonical sorts directly into one prepaid buffer,
// avoiding an owned ParsedSort and temporary recursive render strings.
fn append_sort(text: &mut String, sort: &Sort) -> Option<()> {
    match sort {
        Sort::Bool => text.push_str("Bool"),
        Sort::Int => text.push_str("Int"),
        Sort::Real => text.push_str("Real"),
        Sort::Array(array) => {
            text.push_str("(Array ");
            append_sort(text, &array.index_sort)?;
            text.push(' ');
            append_sort(text, &array.element_sort)?;
            text.push(')');
        }
        _ => return None,
    }
    Some(())
}
