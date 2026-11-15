// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! A declaration group's sort heads are simultaneous, but recursive records
//! are not admitted. Borrow source names until the dependency DAG is resolved;
//! never put an uninterpreted placeholder in the authenticated source problem.

use super::*;
use crate::{ChcDtConstructor, ChcDtSelector};

enum FieldValue<'a> {
    Leaf(ChcSort),
    Record(&'a str),
}

struct Field<'a> {
    indices: Vec<u32>,
    value: FieldValue<'a>,
}

/// A field's innermost sort: its own, a record of this group once resolved, or a
/// record the source registry already holds.
fn field_leaf<'s>(
    field: &'s Field<'_>,
    heads: &BTreeMap<&str, usize>,
    resolved: &'s [Option<ChcSort>],
    registry: Option<&'s Registry>,
) -> ChcResult<&'s ChcSort> {
    match &field.value {
        FieldValue::Leaf(sort) => Some(sort),
        FieldValue::Record(name) => match heads.get(name) {
            Some(index) => resolved[*index].as_ref(),
            None => registry.and_then(|r| r.lookup(name)),
        },
    }
    .ok_or_else(|| invalid("unresolved record field"))
}

struct Definition<'a> {
    name: &'a str,
    constructor: &'a str,
    fields: Vec<(&'a str, Field<'a>)>,
}

#[derive(Clone, Copy)]
enum State {
    New,
    Active,
    Done,
}

enum Frame {
    Enter(usize, usize),
    Finish(usize),
}

impl Parser<'_> {
    pub(super) fn record_group(&mut self, group: &[(&SExpr, &SExpr)]) -> ChcResult<()> {
        if self.phase != Phase::Declarations
            || group.is_empty()
            || group.len() > MAX_RECORDS.saturating_sub(self.records.count)
        {
            return Err(invalid("record declaration phase or count limit"));
        }
        self.budget
            .charge(group.len(), group.len().saturating_mul(256))?;
        let mut heads = BTreeMap::new();
        for (index, (name, _)) in group.iter().enumerate() {
            let name = symbol(name)?;
            self.record_name(name)?;
            if self.declarations.datatype_defs().contains_key(name)
                || heads.insert(name, index).is_some()
            {
                return Err(invalid("duplicate record declaration"));
            }
        }
        let mut definitions = Vec::new();
        for (name, definition) in group {
            definitions.push(self.record_definition(symbol(name)?, definition, &heads)?);
        }
        let resolved = self.resolve_records(&definitions, &heads)?;
        // All dependencies succeeded before installing any member of this
        // group. The following copies are separately charged before cloning.
        for (definition, sort) in definitions.iter().zip(&resolved) {
            let sort = sort.as_ref().ok_or_else(|| invalid("unresolved record"))?;
            self.budget.sort_copy(sort)?;
            let ChcSort::Datatype { constructors, .. } = sort else {
                return Err(invalid("resolved record sort"));
            };
            let [constructor] = constructors.as_slice() else {
                return Err(invalid("resolved record constructor"));
            };
            let fields = constructor
                .selectors
                .iter()
                .map(|field| (field.name.clone(), field.sort.clone()))
                .collect();
            self.declarations.add_datatype_def(
                definition.name.to_owned(),
                vec![(definition.constructor.to_owned(), fields)],
            );
        }
        self.records.count += group.len();
        Ok(())
    }

    fn record_definition<'a>(
        &mut self,
        name: &'a str,
        definition: &'a SExpr,
        heads: &BTreeMap<&str, usize>,
    ) -> ChcResult<Definition<'a>> {
        let [constructor] = list(definition)? else {
            return Err(invalid("record requires exactly one constructor"));
        };
        let Some((constructor, fields)) = list(constructor)?.split_first() else {
            return Err(invalid("record constructor is empty"));
        };
        let constructor = symbol(constructor)?;
        if fields.is_empty() || fields.len() > MAX_FIELDS {
            return Err(invalid("record field count limit"));
        }
        self.record_name(constructor)?;
        self.budget
            .charge(fields.len(), fields.len().saturating_mul(256))?;
        let mut output = Vec::new();
        let mut names = BTreeSet::new();
        for field in fields {
            let [field, sort] = list(field)? else {
                return Err(invalid("record field requires name and sort"));
            };
            let field = symbol(field)?;
            self.record_name(field)?;
            if field == constructor || !names.insert(field) {
                return Err(invalid("duplicate record field or constructor name"));
            }
            if let Ok(sort) = value::sort(sort) {
                output.push((
                    field,
                    Field {
                        indices: Vec::new(),
                        value: FieldValue::Leaf(sort),
                    },
                ));
                continue;
            }
            let (indices, sort) = self.array_indices(sort)?;
            let value = match sort.as_symbol().filter(|name| {
                heads.contains_key(name)
                    || self
                        .records
                        .registry
                        .as_ref()
                        .is_some_and(|r| r.lookup(name).is_some())
            }) {
                Some(name) => {
                    self.budget.name(name)?;
                    FieldValue::Record(name)
                }
                None => FieldValue::Leaf(value::sort(sort)?),
            };
            output.push((field, Field { indices, value }));
        }
        Ok(Definition {
            name,
            constructor,
            fields: output,
        })
    }

    fn resolve_records(
        &mut self,
        definitions: &[Definition<'_>],
        heads: &BTreeMap<&str, usize>,
    ) -> ChcResult<Vec<Option<ChcSort>>> {
        self.budget
            .charge(definitions.len(), definitions.len().saturating_mul(128))?;
        let mut states = vec![State::New; definitions.len()];
        let mut resolved = vec![None; definitions.len()];
        let mut pending = Vec::new();
        for root in 0..definitions.len() {
            pending.push(Frame::Enter(root, 0));
            while let Some(frame) = pending.pop() {
                self.budget.charge(1, 64)?;
                match frame {
                    Frame::Enter(index, depth) => {
                        if depth > crate::quantified::records::MAX_RECORD_DEPTH {
                            return Err(invalid("record dependency depth limit"));
                        }
                        match states[index] {
                            State::Done => continue,
                            State::Active => return Err(invalid("recursive record dependency")),
                            State::New => states[index] = State::Active,
                        }
                        let definition = &definitions[index];
                        self.budget.charge(
                            definition.fields.len() + 1,
                            (definition.fields.len() + 1).saturating_mul(64),
                        )?;
                        pending.push(Frame::Finish(index));
                        for (_, field) in definition.fields.iter().rev() {
                            if let FieldValue::Record(name) = &field.value {
                                if let Some(child) = heads.get(name) {
                                    pending.push(Frame::Enter(
                                        *child,
                                        depth + 1 + field.indices.len(),
                                    ));
                                }
                            }
                        }
                    }
                    Frame::Finish(index) => {
                        resolved[index] =
                            Some(self.resolve_record(&definitions[index], heads, &resolved)?);
                        states[index] = State::Done;
                    }
                }
            }
        }
        Ok(resolved)
    }

    fn resolve_record(
        &mut self,
        definition: &Definition<'_>,
        heads: &BTreeMap<&str, usize>,
        resolved: &[Option<ChcSort>],
    ) -> ChcResult<ChcSort> {
        self.budget.charge(
            definition.fields.len(),
            definition.fields.len().saturating_mul(128),
        )?;
        let mut selectors = Vec::new();
        for (name, field) in &definition.fields {
            let registry = self.records.registry.as_ref();
            let bytes = sort_bytes(field_leaf(field, heads, resolved, registry)?)
                .and_then(|bytes| bytes.checked_add(field.indices.len() * 128))
                .ok_or_else(|| invalid("record field metadata limit"))?;
            // The metadata charge borrows the record state mutably, so the
            // registry borrow ends first and the sort is looked up again:
            // both charges still precede the clone.
            self.records.charge_metadata(0, bytes)?;
            let sort = field_leaf(field, heads, resolved, self.records.registry.as_ref())?;
            self.budget.sort_copy(sort)?;
            self.budget
                .charge(field.indices.len(), field.indices.len() * 128)?;
            let mut sort = sort.clone();
            for width in field.indices.iter().rev() {
                sort = ChcSort::Array(Box::new(ChcSort::BitVec(*width)), Box::new(sort));
            }
            // The array rank continues through this resolved record's fields.
            sort_bytes(&sort).ok_or_else(|| invalid("array-wrapped record field limit"))?;
            selectors.push(ChcDtSelector {
                name: (*name).to_owned(),
                sort,
            });
        }
        let sort = ChcSort::Datatype {
            name: definition.name.to_owned(),
            constructors: crate::ChcDtConstructors::new(vec![ChcDtConstructor {
                name: definition.constructor.to_owned(),
                selectors,
            }]),
        };
        let bytes = sort_bytes(&sort).ok_or_else(|| invalid("record closure metadata limit"))?;
        self.records.max_sort_bytes = self.records.max_sort_bytes.max(bytes);
        Ok(sort)
    }
}
