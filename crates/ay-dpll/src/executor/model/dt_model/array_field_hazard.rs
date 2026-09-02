// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded recursive detection of datatypes carrying array-valued fields.

use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::{DatatypeSort, Sort};

use super::super::rendered_dt_limits::{SchemaSourceBudget, MAX_RENDERED_DT_DEPTH};
use super::super::Executor;

const MAX_HAZARD_WORK: usize = 4 * 1024;

pub(super) fn bounded_sort_carries_array_field_datatype(
    exec: &Executor,
    sort: &Sort,
) -> Result<bool, ()> {
    HazardWalk {
        exec,
        visited_registry: HashSet::default(),
        visited_inline: HashSet::default(),
        source: SchemaSourceBudget::new(),
        work: 0,
    }
    .walk(sort, 0)
}

struct HazardWalk<'a> {
    exec: &'a Executor,
    visited_registry: HashSet<String>,
    visited_inline: HashSet<String>,
    source: SchemaSourceBudget,
    work: usize,
}

impl HazardWalk<'_> {
    fn walk(&mut self, sort: &Sort, depth: usize) -> Result<bool, ()> {
        if depth > MAX_RENDERED_DT_DEPTH {
            return Err(());
        }
        charge_node(&mut self.work)?;
        match sort {
            Sort::Array(array) => Ok(self.walk(&array.index_sort, depth + 1)?
                || self.walk(&array.element_sort, depth + 1)?),
            Sort::Datatype(datatype) => self.walk_inline(datatype, depth),
            Sort::Uninterpreted(name) => self.walk_registered(name, depth),
            _ => Ok(false),
        }
    }

    fn walk_inline(&mut self, datatype: &DatatypeSort, depth: usize) -> Result<bool, ()> {
        if !self.source.charge_identifier(&datatype.name)
            || !self.visited_inline.insert(datatype.name.clone())
        {
            return Err(());
        }
        for constructor in &datatype.constructors {
            charge_node(&mut self.work)?;
            if !self.source.charge_identifier(&constructor.name) {
                return Err(());
            }
            for field in &constructor.fields {
                charge_node(&mut self.work)?;
                if !self.source.charge_identifier(&field.name) {
                    return Err(());
                }
                if matches!(field.sort, Sort::Array(_)) || self.walk(&field.sort, depth + 1)? {
                    return Ok(true);
                }
            }
        }
        self.visited_inline.remove(&datatype.name);
        // A raw API sort can carry an inline schema whose name also resolves
        // through the declaration registry. Treat either schema as hazardous;
        // divergence/resource failure must never create a raw-value bypass.
        if self
            .exec
            .ctx
            .datatype_constructors(&datatype.name)
            .is_some()
        {
            return self.walk_registered(&datatype.name, depth);
        }
        Ok(false)
    }

    fn walk_registered(&mut self, name: &str, depth: usize) -> Result<bool, ()> {
        if !self.source.charge_identifier(name) {
            return Err(());
        }
        let Some(constructors) = self.exec.ctx.datatype_constructors(name) else {
            return Ok(false);
        };
        if !self.visited_registry.insert(name.to_string()) {
            return Ok(false);
        }
        for constructor in constructors {
            charge_node(&mut self.work)?;
            if !self.source.charge_identifier(constructor) {
                return Err(());
            }
            let fields = self
                .exec
                .ctx
                .constructor_selector_info(constructor)
                .ok_or(())?;
            for (field, sort) in fields {
                charge_node(&mut self.work)?;
                if !self.source.charge_identifier(field) {
                    return Err(());
                }
                if matches!(sort, Sort::Array(_)) || self.walk(sort, depth + 1)? {
                    return Ok(true);
                }
            }
        }
        self.visited_registry.remove(name);
        Ok(false)
    }
}

fn charge_node(work: &mut usize) -> Result<(), ()> {
    *work = work
        .checked_add(1)
        .filter(|&next| next <= MAX_HAZARD_WORK)
        .ok_or(())?;
    Ok(())
}
