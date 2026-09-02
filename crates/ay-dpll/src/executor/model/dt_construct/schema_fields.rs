// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Borrowed constructor-schema preflight before retained field clones.

use ay_core::Sort;

use super::super::rendered_dt_limits::SchemaSourceBudget;
use super::DtBuilder;

impl DtBuilder<'_> {
    pub(super) fn bounded_constructor_fields(&self, ctor: &str) -> Option<Vec<(String, Sort)>> {
        let fields = self.exec.ctx.constructor_selector_info(ctor)?;
        let mut source = SchemaSourceBudget::new();
        if !source.charge_identifier(ctor)
            || fields.iter().any(|(selector, sort)| {
                !source.charge_identifier(selector) || !source.charge_sort(sort)
            })
        {
            return None;
        }
        Some(fields.to_vec())
    }
}
