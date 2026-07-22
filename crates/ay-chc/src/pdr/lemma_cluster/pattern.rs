// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// Result of pattern extraction from a blocking cube.
#[derive(Debug, Clone)]
pub(crate) struct PatternExtractionResult {
    /// Pattern with numeric constants replaced by pattern variables
    pub(crate) pattern: ChcExpr,
    /// Pattern variables created (parallel to substitution values)
    pub(crate) pattern_vars: Vec<ChcVar>,
    /// Numeric values extracted (substitution for this lemma)
    pub(crate) subst_values: Vec<i128>,
}

/// Extract a pattern from a blocking cube by abstracting numeric constants.
pub(crate) fn extract_pattern(blocking_cube: &ChcExpr) -> PatternExtractionResult {
    let blocking_cube = normalize_cube(blocking_cube);
    let existing_names: FxHashSet<String> = expr_var_names(&blocking_cube);
    let mut extractor = PatternExtractor::new(existing_names);
    let pattern = extractor.extract(&blocking_cube);
    PatternExtractionResult {
        pattern,
        pattern_vars: extractor.pattern_vars,
        subst_values: extractor.subst_values,
    }
}

/// Normalize a cube to make clustering stable.
pub(crate) fn normalize_cube(expr: &ChcExpr) -> ChcExpr {
    let mut lits = Vec::new();
    expr.collect_conjuncts_into(&mut lits);

    let mut normalized: Vec<ChcExpr> = lits
        .into_iter()
        .filter(|lit| *lit != ChcExpr::Bool(true))
        .map(normalize_literal)
        .collect();

    if normalized.contains(&ChcExpr::Bool(false)) {
        return ChcExpr::Bool(false);
    }

    normalized.sort_by_key(ToString::to_string);

    match normalized.len() {
        0 => ChcExpr::Bool(true),
        1 => normalized.pop().expect("len == 1"),
        _ => ChcExpr::Op(ChcOp::And, normalized.into_iter().map(Arc::new).collect()),
    }
}

fn normalize_literal(lit: ChcExpr) -> ChcExpr {
    match &lit {
        ChcExpr::Op(op, args) if args.len() == 2 => {
            if let (ChcExpr::Int(n), ChcExpr::Var(v)) = (args[0].as_ref(), args[1].as_ref()) {
                let swapped_op = match op {
                    ChcOp::Eq => Some(ChcOp::Eq),
                    ChcOp::Lt => Some(ChcOp::Gt),
                    ChcOp::Le => Some(ChcOp::Ge),
                    ChcOp::Gt => Some(ChcOp::Lt),
                    ChcOp::Ge => Some(ChcOp::Le),
                    _ => None,
                };

                if let Some(swapped_op) = swapped_op {
                    return ChcExpr::Op(
                        swapped_op,
                        vec![
                            Arc::new(ChcExpr::Var(v.clone())),
                            Arc::new(ChcExpr::Int(*n)),
                        ],
                    );
                }
            }
        }
        _ => {}
    }
    lit
}

/// Internal helper for pattern extraction.
struct PatternExtractor {
    pattern_vars: Vec<ChcVar>,
    subst_values: Vec<i128>,
    existing_names: FxHashSet<String>,
}

impl PatternExtractor {
    fn new(existing_names: FxHashSet<String>) -> Self {
        Self {
            pattern_vars: Vec::new(),
            subst_values: Vec::new(),
            existing_names,
        }
    }

    fn extract(&mut self, expr: &ChcExpr) -> ChcExpr {
        crate::expr::maybe_grow_expr_stack(|| match expr {
            ChcExpr::Int(n) => {
                let var = self.fresh_pattern_var();
                self.subst_values.push(*n);
                ChcExpr::Var(var)
            }
            ChcExpr::Op(op, args) => {
                let new_args: Vec<Arc<ChcExpr>> =
                    args.iter().map(|a| Arc::new(self.extract(a))).collect();
                ChcExpr::Op(*op, new_args)
            }
            _ => expr.clone(),
        })
    }

    fn fresh_pattern_var(&mut self) -> ChcVar {
        let mut idx = self.pattern_vars.len();
        let mut name = format!("__gg_k{idx}");
        while self.existing_names.contains(&name) {
            idx += 1;
            name = format!("__gg_k{idx}");
        }
        self.existing_names.insert(name.clone());
        let var = ChcVar::new(name, ChcSort::Int);
        self.pattern_vars.push(var.clone());
        var
    }
}

/// Try to match a blocking cube against a pattern.
pub(crate) fn match_pattern(
    pattern: &ChcExpr,
    pattern_vars: &[ChcVar],
    cube: &ChcExpr,
) -> Option<Vec<i128>> {
    let mut matcher = SemanticMatcher::new();
    matcher.matches(pattern, pattern_vars, cube)
}

pub(crate) fn instantiate_pattern_int(
    pattern: &ChcExpr,
    vars: &[ChcVar],
    values: &[i128],
) -> ChcExpr {
    debug_assert_eq!(
        vars.len(),
        values.len(),
        "pattern vars and subst values must align"
    );
    let subst: Vec<(ChcVar, ChcExpr)> = vars
        .iter()
        .cloned()
        .zip(values.iter().copied().map(ChcExpr::Int))
        .collect();
    pattern.substitute(&subst)
}
