// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The sort grammar of pinned Carcara's problem parser (`make_sort`,
//! `make_indexed_sort` and `parse_sort` in `carcara/src/parser/mod.rs` at
//! 9a352ee), and the sort matching its parametric-datatype applications use
//! (`Sort::match_with`).

use std::fmt;

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_frontend::command::{Index, Sort as ParsedSort};

/// A sort as pinned Carcara reads it from the problem.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum CarcaraSort {
    Bool,
    Int,
    Real,
    Str,
    RegLan,
    BitVec(u64),
    Array(Box<Self>, Box<Self>),
    /// A declared sort or datatype applied to exactly its arity of arguments.
    Named(String, Vec<Self>),
    /// A sort parameter: of a parametric datatype inside its constructor and
    /// selector signatures, or of a `define-sort` inside its body.
    Param(String),
}

impl CarcaraSort {
    pub(super) fn is_numeric(&self) -> bool {
        matches!(self, Self::Int | Self::Real)
    }

    fn has_param(&self) -> bool {
        match self {
            Self::Param(_) => true,
            Self::Array(index, element) => index.has_param() || element.has_param(),
            Self::Named(_, arguments) => arguments.iter().any(Self::has_param),
            _ => false,
        }
    }

    /// `self` with every parameter bound in `binding` replaced.
    pub(super) fn substitute(&self, binding: &HashMap<String, Self>) -> Self {
        match self {
            Self::Param(name) => binding.get(name).cloned().unwrap_or_else(|| self.clone()),
            Self::Array(index, element) => Self::Array(
                Box::new(index.substitute(binding)),
                Box::new(element.substitute(binding)),
            ),
            Self::Named(name, arguments) => Self::Named(
                name.clone(),
                arguments
                    .iter()
                    .map(|argument| argument.substitute(binding))
                    .collect(),
            ),
            _ => self.clone(),
        }
    }

    /// Extend `binding` so that `self`, a signature sort that may name
    /// parameters, becomes exactly `actual`. A concrete `actual` only: an
    /// argument whose own sort still names a parameter is not matched.
    pub(super) fn matches(&self, actual: &Self, binding: &mut HashMap<String, Self>) -> bool {
        if actual.has_param() {
            return false;
        }
        match (self, actual) {
            (Self::Param(name), _) => match binding.get(name) {
                Some(bound) => bound == actual,
                None => {
                    binding.insert(name.clone(), actual.clone());
                    true
                }
            },
            (Self::Array(index, element), Self::Array(actual_index, actual_element)) => {
                index.matches(actual_index, binding) && element.matches(actual_element, binding)
            }
            (Self::Named(name, arguments), Self::Named(actual_name, actual_arguments)) => {
                name == actual_name
                    && arguments.len() == actual_arguments.len()
                    && arguments
                        .iter()
                        .zip(actual_arguments)
                        .all(|(pattern, actual)| pattern.matches(actual, binding))
            }
            _ => self == actual,
        }
    }
}

impl fmt::Display for CarcaraSort {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Bool => f.write_str("Bool"),
            Self::Int => f.write_str("Int"),
            Self::Real => f.write_str("Real"),
            Self::Str => f.write_str("String"),
            Self::RegLan => f.write_str("RegLan"),
            Self::BitVec(width) => write!(f, "(_ BitVec {width})"),
            Self::Array(index, element) => write!(f, "(Array {index} {element})"),
            Self::Named(name, arguments) if arguments.is_empty() => f.write_str(name),
            Self::Named(name, arguments) => {
                write!(f, "({name}")?;
                for argument in arguments {
                    write!(f, " {argument}")?;
                }
                f.write_str(")")
            }
            Self::Param(name) => f.write_str(name),
        }
    }
}

/// One sort symbol the problem introduced.
#[derive(Clone)]
pub(super) enum SortEntry {
    /// `declare-sort`, or a datatype of `declare-datatype(s)`, with its arity.
    Declared(usize),
    /// `define-sort`: its parameters and its body over them.
    Defined {
        params: Vec<String>,
        body: CarcaraSort,
    },
}

/// Whether `sort` spells an indexed sort (`(_ BitVec n)`) anywhere.
pub(super) fn has_indexed(sort: &ParsedSort) -> bool {
    match sort {
        ParsedSort::Indexed(..) => true,
        ParsedSort::Parameterized(_, arguments) => arguments.iter().any(has_indexed),
        _ => false,
    }
}

/// Pinned Carcara's reading of `sort`, where `params` are the sort parameters
/// in scope (a parametric datatype's or a `define-sort`'s), or why it cannot
/// read it.
pub(super) fn resolve(
    sorts: &HashMap<String, SortEntry>,
    params: &[String],
    sort: &ParsedSort,
) -> Result<CarcaraSort, String> {
    match sort {
        ParsedSort::Simple(name) if params.contains(name) => Ok(CarcaraSort::Param(name.clone())),
        ParsedSort::Simple(name) => apply(sorts, name, Vec::new()),
        ParsedSort::Parameterized(name, arguments) => {
            let arguments = arguments
                .iter()
                .map(|argument| resolve(sorts, params, argument))
                .collect::<Result<Vec<_>, _>>()?;
            apply(sorts, name, arguments)
        }
        ParsedSort::Indexed(name, indices) => match (name.as_str(), indices.as_slice()) {
            ("BitVec", [Index::Numeral(width)]) => width
                .parse::<u64>()
                .ok()
                .filter(|width| *width > 0)
                .map(CarcaraSort::BitVec)
                .ok_or_else(|| outside_grammar(&format!("(_ BitVec {width})"))),
            _ => Err(outside_grammar(&format!("(_ {name} ...)"))),
        },
        _ => Err(outside_grammar("an unrecognized sort form")),
    }
}

fn apply(
    sorts: &HashMap<String, SortEntry>,
    name: &str,
    arguments: Vec<CarcaraSort>,
) -> Result<CarcaraSort, String> {
    let builtin = match name {
        "Bool" => Some(CarcaraSort::Bool),
        "Int" => Some(CarcaraSort::Int),
        "Real" => Some(CarcaraSort::Real),
        "String" => Some(CarcaraSort::Str),
        "RegLan" => Some(CarcaraSort::RegLan),
        _ => None,
    };
    if let Some(builtin) = builtin {
        return if arguments.is_empty() {
            Ok(builtin)
        } else {
            Err(outside_grammar(&format!("({name} ...)")))
        };
    }
    match (name, sorts.get(name)) {
        ("Array", _) => match <[CarcaraSort; 2]>::try_from(arguments) {
            Ok([index, element]) => Ok(CarcaraSort::Array(Box::new(index), Box::new(element))),
            Err(_) => Err(outside_grammar(
                "an Array sort without exactly two arguments",
            )),
        },
        (_, Some(SortEntry::Declared(arity))) if *arity == arguments.len() => {
            Ok(CarcaraSort::Named(name.to_string(), arguments))
        }
        (_, Some(SortEntry::Defined { params, body })) if params.len() == arguments.len() => {
            let binding = params.iter().cloned().zip(arguments).collect();
            Ok(body.substitute(&binding))
        }
        (_, Some(_)) => Err(format!(
            "sort `{name}` is applied to {} argument(s), not its arity",
            arguments.len()
        )),
        (_, None) => Err(outside_grammar(name)),
    }
}

fn outside_grammar(sort: &str) -> String {
    format!(
        "sort `{sort}` is not in pinned Carcara 1.1.0's sort grammar (Bool, Int, Real, String, \
         RegLan, (_ BitVec n), Array, and declared, datatype and defined sorts)"
    )
}
