// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Authenticated, bounded single-constructor record declarations.
//! Structural sort admission alone is not declaration authority. All uses must
//! additionally agree with this registry's complete ordered metadata.

use crate::{ChcDtConstructor, ChcDtSelector, ChcError, ChcProblem, ChcResult, ChcSort};
use std::collections::{BTreeMap, BTreeSet};

mod scan;
mod shape;
mod validation;
pub(crate) use shape::field_sort as scalar_array_sort;
pub(crate) use shape::small_copy_sort;
pub(crate) use shape::sort_bytes;
#[cfg(test)]
pub(crate) use shape::supported_sort;

pub(crate) const MAX_RECORDS: usize = 256;
pub(crate) const MAX_FIELDS: usize = 64;
pub(crate) const MAX_NAME_BYTES: usize = 16_384;
pub(crate) const MAX_REGISTRY_NAME_BYTES: usize = 1024 * 1024;
pub(crate) const MAX_REGISTRY_COPY_BYTES: usize = 8 * 1024 * 1024;
pub(crate) const MAX_RECORD_DEPTH: usize = 64;
pub(crate) const MAX_SORT_OCCURRENCES: usize = 65_536;
pub(crate) const MAX_FLATTENED_LEAVES: usize = 256;
pub(crate) const MAX_ARRAY_RANK: usize = 2;

fn invalid(message: &str) -> ChcError {
    ChcError::Verification(format!("quantified record source: {message}"))
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Signature {
    record: usize,
    field: Option<usize>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum OperationKind {
    Constructor,
    Selector { field: usize },
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct ResolvedApplication<'a> {
    pub(crate) sort: &'a ChcSort,
    pub(crate) kind: OperationKind,
}

#[derive(Debug)]
pub(crate) struct Registry {
    records: Vec<ChcSort>,
    names: BTreeMap<String, usize>,
    functions: BTreeMap<String, Vec<Signature>>,
}

impl Registry {
    pub(crate) fn new(problem: &ChcProblem) -> ChcResult<Self> {
        admit_definitions(problem)?;
        // Every name/field/sort was admitted before collecting, sorting or
        // cloning. Ordering records never reorders their constructor fields.
        let mut definitions: Vec<_> = problem.datatype_defs().iter().collect();
        definitions.sort_by(|left, right| left.0.cmp(right.0));
        let mut out = Self {
            records: Vec::new(),
            names: BTreeMap::new(),
            functions: BTreeMap::new(),
        };
        for (name, constructors) in definitions {
            let [(constructor, fields)] = constructors.as_slice() else {
                return Err(invalid("expected one constructor"));
            };
            let index = out.records.len();
            let selectors = fields
                .iter()
                .map(|(name, sort)| ChcDtSelector {
                    name: name.clone(),
                    sort: sort.clone(),
                })
                .collect();
            out.records.push(ChcSort::Datatype {
                name: name.clone(),
                constructors: crate::ChcDtConstructors::new(vec![ChcDtConstructor {
                    name: constructor.clone(),
                    selectors,
                }]),
            });
            out.names.insert(name.clone(), index);
            out.functions
                .entry(constructor.clone())
                .or_default()
                .push(Signature {
                    record: index,
                    field: None,
                });
            for (field, (name, _)) in fields.iter().enumerate() {
                out.functions
                    .entry(name.clone())
                    .or_default()
                    .push(Signature {
                        record: index,
                        field: Some(field),
                    });
            }
        }
        out.validate_definitions()?;
        Ok(out)
    }

    pub(crate) fn lookup(&self, name: &str) -> Option<&ChcSort> {
        if name.len() > MAX_NAME_BYTES {
            return None;
        }
        self.records.get(*self.names.get(name)?)
    }

    pub(crate) fn contains_term_symbol(&self, name: &str) -> bool {
        name.len() <= MAX_NAME_BYTES && self.functions.contains_key(name)
    }

    pub(crate) fn term_names(&self) -> impl Iterator<Item = &str> {
        self.functions.keys().map(String::as_str)
    }

    pub(crate) fn record_sorts(&self) -> impl Iterator<Item = &ChcSort> {
        self.records.iter()
    }

    /// Retain already admitted metadata in canonical declaration order.
    /// Moves the registry's vector; no sort or name is cloned here.
    pub(super) fn into_record_sorts(self) -> Vec<ChcSort> {
        self.records
    }

    pub(crate) fn application(&self, name: &str, args: &[ChcSort]) -> ChcResult<ChcSort> {
        Ok(self.resolve_application(name, args)?.sort.clone())
    }

    pub(crate) fn resolve_application(
        &self,
        name: &str,
        args: &[ChcSort],
    ) -> ChcResult<ResolvedApplication<'_>> {
        if name.len() > MAX_NAME_BYTES || args.len() > MAX_FIELDS {
            return Err(invalid("application size limit"));
        }
        let mut meter = scan::Meter::default();
        for sort in args {
            meter.sort(sort, 0)?;
        }
        for sort in args {
            self.validate_sort(sort)?;
        }
        let signatures = self
            .functions
            .get(name)
            .ok_or_else(|| invalid("not a declared record operation"))?;
        let mut result = None;
        for signature in signatures {
            let record = self
                .records
                .get(signature.record)
                .ok_or_else(|| invalid("registry index"))?;
            let ChcSort::Datatype { constructors, .. } = record else {
                return Err(invalid("registry record"));
            };
            let [constructor] = constructors.as_slice() else {
                return Err(invalid("registry constructor"));
            };
            let candidate = match signature.field {
                None if constructor.selectors.len() == args.len()
                    && constructor
                        .selectors
                        .iter()
                        .zip(args)
                        .all(|(field, arg)| validation::same_sort(&field.sort, arg)) =>
                {
                    Some(ResolvedApplication {
                        sort: record,
                        kind: OperationKind::Constructor,
                    })
                }
                Some(index) if args.len() == 1 && validation::same_sort(&args[0], record) => {
                    Some(ResolvedApplication {
                        sort: &constructor
                            .selectors
                            .get(index)
                            .ok_or_else(|| invalid("registry field"))?
                            .sort,
                        kind: OperationKind::Selector { field: index },
                    })
                }
                _ => None,
            };
            if let Some(candidate) = candidate {
                if result.is_some() {
                    return Err(invalid("ambiguous record operation signature"));
                }
                result = Some(candidate);
            }
        }
        result.ok_or_else(|| invalid("record operation arity or sort mismatch"))
    }

    pub(crate) fn declarations_smtlib(&self) -> ChcResult<String> {
        let declarations = self
            .records
            .iter()
            .map(|sort| match sort {
                ChcSort::Datatype { name, constructors } => {
                    Ok((name.as_str(), constructors.as_slice()))
                }
                _ => Err(invalid("registry record")),
            })
            .collect::<ChcResult<Vec<_>>>()?;
        crate::smt::executor_adapter::emit_declare_datatypes(&declarations)
            .map_err(|_| invalid("datatype declaration emission refused"))
    }
}

/// Complete borrowed structural admission and conservative allocation charge.
/// No record metadata is cloned before this succeeds. Cross-declaration identity
/// and dependency validation remain Registry::new's responsibility.
pub(crate) fn registry_bytes(problem: &ChcProblem) -> Option<usize> {
    admit_definitions(problem).ok()
}

fn admit_definitions(problem: &ChcProblem) -> ChcResult<usize> {
    if problem.datatype_defs().len() > MAX_RECORDS {
        return Err(invalid("record count limit"));
    }
    let mut meter = scan::Meter::default();
    for (name, constructors) in problem.datatype_defs() {
        meter.name(name)?;
        let [(constructor, fields)] = constructors.as_slice() else {
            return Err(invalid("expected one constructor"));
        };
        meter.name(constructor)?;
        if fields.is_empty() || fields.len() > MAX_FIELDS {
            return Err(invalid("record field count limit"));
        }
        let mut field_names = BTreeSet::new();
        let mut leaves = 0usize;
        for (field, sort) in fields {
            meter.name(field)?;
            if field == constructor || !field_names.insert(field.as_str()) {
                return Err(invalid("duplicate record operation name"));
            }
            leaves = leaves
                .checked_add(meter.sort(sort, 1)?)
                .ok_or_else(|| invalid("record leaf limit"))?;
            if leaves > MAX_FLATTENED_LEAVES {
                return Err(invalid("record leaf limit"));
            }
        }
    }
    Ok(meter.bytes())
}

#[cfg(test)]
mod tests;
