// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Metered text output; all recursive renderers are preceded by admission.

use super::*;
use crate::quantified::records::sort_bytes;
use crate::smt::executor_adapter::sort_to_smtlib;
use crate::{ChcSort, InvariantModel};
use ay_core::quote_symbol;

pub(super) struct Output<'a, 'token> {
    control: &'a SourceControl<'token>,
    text: String,
}

impl<'a, 'token> Output<'a, 'token> {
    pub(super) fn new(control: &'a SourceControl<'token>) -> Self {
        Self {
            control,
            text: String::new(),
        }
    }

    pub(super) fn push(&mut self, text: &str) -> Result<()> {
        self.control.charge(1).ok_or_else(refused)?;
        self.text
            .len()
            .checked_add(text.len())
            .filter(|bytes| *bytes <= MAX_OUTPUT_BYTES)
            .ok_or_else(refused)?;
        // Charge retained bytes and capacity slack before reserving/copying.
        self.control
            .bytes(text.len().checked_mul(2).ok_or_else(refused)?)
            .ok_or_else(refused)?;
        self.text.try_reserve(text.len()).map_err(|_| refused())?;
        self.text.push_str(text);
        Ok(())
    }

    pub(super) fn symbol(&mut self, name: &str) -> Result<()> {
        self.control
            .bytes(
                name.len()
                    .checked_mul(2)
                    .and_then(|bytes| bytes.checked_add(4))
                    .ok_or_else(refused)?,
            )
            .ok_or_else(refused)?;
        self.push(&quote_symbol(name))
    }

    pub(super) fn sort(&mut self, sort: &ChcSort) -> Result<()> {
        self.control
            .bytes(sort_bytes(sort).ok_or_else(refused)?)
            .ok_or_else(refused)?;
        self.push(&sort_to_smtlib(sort))
    }

    pub(super) fn expression(&mut self, expression: &ChcExpr) -> Result<()> {
        let bound = census::expression_cost(expression, self.control)?;
        let text = InvariantModel::expr_to_smtlib(expression);
        if text.len() > bound {
            return Err(refused());
        }
        self.push(&text)
    }

    pub(super) fn finish(self) -> String {
        self.text
    }

    pub(super) fn len(&self) -> usize {
        self.text.len()
    }
}
