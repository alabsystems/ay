// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// Search annotation types and parsing for FlatZinc search strategies.
//
// FlatZinc search annotations specify how a CP solver should explore
// the search space. These are critical for the FD Search track of the
// MiniZinc Challenge, which requires the solver to follow the
// prescribed branching strategy.
//
// Annotation forms:
//   int_search(<vars>, <var_choice>, <val_choice>, <strategy>)
//   bool_search(<vars>, <var_choice>, <val_choice>, <strategy>)
//   seq_search([<search1>, <search2>, ...])

use ay_flatzinc_parser::ast::{Annotation, Expr};

/// A parsed search annotation from the FlatZinc solve item.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SearchAnnotation {
    /// int_search(\<vars\>, \<var_choice\>, \<val_choice\>, \<strategy\>)
    IntSearch {
        vars: Vec<String>,
        var_choice: VarChoice,
        val_choice: ValChoice,
        strategy: SearchStrategy,
    },
    /// bool_search(\<vars\>, \<var_choice\>, \<val_choice\>, \<strategy\>)
    BoolSearch {
        vars: Vec<String>,
        var_choice: VarChoice,
        val_choice: ValChoice,
        strategy: SearchStrategy,
    },
    /// seq_search([\<search1\>, \<search2\>, ...])
    SeqSearch(Vec<Self>),
}

/// Variable choice heuristic: which variable to branch on next.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VarChoice {
    /// Follow the order given in the variable array.
    InputOrder,
    /// Choose the variable with the smallest current domain.
    FirstFail,
    /// Choose the variable with the largest current domain.
    AntiFirstFail,
    /// Choose the variable with the smallest lower bound.
    Smallest,
    /// Choose the variable with the largest upper bound.
    Largest,
    /// Choose the variable involved in the most constraints.
    MostConstrained,
    /// Choose the variable with the smallest domain/degree ratio.
    DomWDeg,
    /// Unknown heuristic (treat as input_order for robustness).
    Unknown,
}

/// Value choice heuristic: which value to try first for a variable.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ValChoice {
    /// Try the smallest value in the domain first.
    IndomainMin,
    /// Try the largest value in the domain first.
    IndomainMax,
    /// Try the median value in the domain first.
    IndomainMedian,
    /// Try a random value.
    IndomainRandom,
    /// Binary split: try lower half of domain first.
    IndomainSplit,
    /// Binary split: try upper half of domain first.
    IndomainReverseSplit,
    /// Unknown (treat as indomain_min for robustness).
    Unknown,
}

/// Search strategy: how to explore the tree.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SearchStrategy {
    /// Complete tree search.
    Complete,
    /// Restart-based search.
    Restart,
    /// Unknown (treat as complete).
    Unknown,
}

impl VarChoice {
    fn parse(s: &str) -> Self {
        match s {
            "input_order" => Self::InputOrder,
            "first_fail" => Self::FirstFail,
            "anti_first_fail" => Self::AntiFirstFail,
            "smallest" => Self::Smallest,
            "largest" => Self::Largest,
            "most_constrained" => Self::MostConstrained,
            "dom_w_deg" => Self::DomWDeg,
            _ => Self::Unknown,
        }
    }
}

impl ValChoice {
    fn parse(s: &str) -> Self {
        match s {
            "indomain_min" => Self::IndomainMin,
            "indomain_max" => Self::IndomainMax,
            "indomain_median" => Self::IndomainMedian,
            "indomain_random" => Self::IndomainRandom,
            "indomain_split" => Self::IndomainSplit,
            "indomain_reverse_split" => Self::IndomainReverseSplit,
            _ => Self::Unknown,
        }
    }
}

impl SearchStrategy {
    fn parse(s: &str) -> Self {
        match s {
            "complete" => Self::Complete,
            "restart" => Self::Restart,
            _ => Self::Unknown,
        }
    }
}

/// Extract the identifier string from an Expr.
fn expr_to_ident(expr: &Expr) -> Option<&str> {
    match expr {
        Expr::Ident(s) => Some(s.as_str()),
        _ => None,
    }
}

/// Extract variable names from an array expression.
///
/// Handles both `[x, y, z]` (ArrayLit) and bare identifier
/// references to array parameters.
fn extract_var_names(expr: &Expr) -> Vec<String> {
    match expr {
        Expr::ArrayLit(elems) => elems
            .iter()
            .filter_map(|e| match e {
                Expr::Ident(s) => Some(s.clone()),
                _ => None,
            })
            .collect(),
        Expr::Ident(s) => vec![s.clone()],
        _ => Vec::new(),
    }
}

/// Parse a single search annotation (int_search, bool_search, or seq_search).
fn parse_one(ann: &Annotation) -> Option<SearchAnnotation> {
    match ann {
        Annotation::Call(name, args) => match name.as_str() {
            "int_search" if args.len() >= 4 => {
                let vars = extract_var_names(&args[0]);
                let var_choice = expr_to_ident(&args[1])
                    .map(VarChoice::parse)
                    .unwrap_or(VarChoice::Unknown);
                let val_choice = expr_to_ident(&args[2])
                    .map(ValChoice::parse)
                    .unwrap_or(ValChoice::Unknown);
                let strategy = expr_to_ident(&args[3])
                    .map(SearchStrategy::parse)
                    .unwrap_or(SearchStrategy::Unknown);
                Some(SearchAnnotation::IntSearch {
                    vars,
                    var_choice,
                    val_choice,
                    strategy,
                })
            }
            "bool_search" if args.len() >= 4 => {
                let vars = extract_var_names(&args[0]);
                let var_choice = expr_to_ident(&args[1])
                    .map(VarChoice::parse)
                    .unwrap_or(VarChoice::Unknown);
                let val_choice = expr_to_ident(&args[2])
                    .map(ValChoice::parse)
                    .unwrap_or(ValChoice::Unknown);
                let strategy = expr_to_ident(&args[3])
                    .map(SearchStrategy::parse)
                    .unwrap_or(SearchStrategy::Unknown);
                Some(SearchAnnotation::BoolSearch {
                    vars,
                    var_choice,
                    val_choice,
                    strategy,
                })
            }
            "seq_search" if !args.is_empty() => {
                // seq_search takes an array of search annotations
                let inner = match &args[0] {
                    Expr::ArrayLit(elems) => elems
                        .iter()
                        .filter_map(|e| match e {
                            Expr::Annotation(ann) => parse_one(ann),
                            _ => None,
                        })
                        .collect(),
                    _ => Vec::new(),
                };
                if inner.is_empty() {
                    None
                } else {
                    Some(SearchAnnotation::SeqSearch(inner))
                }
            }
            _ => None,
        },
        Annotation::Atom(_) => None,
    }
}

/// Parse all search annotations from a solve item's annotation list.
///
/// Returns the search annotations in order. Non-search annotations
/// (like `output_var`) are ignored.
pub fn parse_search_annotations(annotations: &[Annotation]) -> Vec<SearchAnnotation> {
    annotations.iter().filter_map(parse_one).collect()
}

/// Flatten a list of search annotations into an ordered sequence of
/// (variable_name, is_bool) pairs for the branching search.
///
/// `seq_search` is recursively flattened. Variables appear in the order
/// specified by the annotations.
pub fn flatten_search_vars(annotations: &[SearchAnnotation]) -> Vec<(String, bool)> {
    let mut result = Vec::new();
    for ann in annotations {
        match ann {
            SearchAnnotation::IntSearch { vars, .. } => {
                result.extend(vars.iter().map(|v| (v.clone(), false)));
            }
            SearchAnnotation::BoolSearch { vars, .. } => {
                result.extend(vars.iter().map(|v| (v.clone(), true)));
            }
            SearchAnnotation::SeqSearch(inner) => {
                result.extend(flatten_search_vars(inner));
            }
        }
    }
    result
}

#[cfg(test)]
#[path = "search_tests.rs"]
mod tests;
