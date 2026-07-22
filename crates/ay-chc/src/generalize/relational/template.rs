// Copyright 2026 Andrew Yates
// Author: Andrew Yates
//
// Licensed under the Apache License, Version 2.0

//! Template-based generalizer: uses predicate templates extracted from the CHC problem.

use ay_core::kani_compat::DetHashMap as HashMap;

use crate::expr::{ChcExpr, ChcOp, ChcSort, ChcVar};
use crate::generalize::{InitBounds, LemmaGeneralizer, TransitionSystemRef};

/// Template-based generalizer: uses predicate templates extracted from the CHC problem.
///
/// When given a weak lemma like `x != k`, this generalizer tries stronger templates
/// such as `x >= init(x)` or `x <= y` that are also inductive.
///
/// # Algorithm (inspired by PCSat/CEGIS)
///
/// 1. Extract templates from the CHC problem:
///    - Variable bounds: `v >= 0`, `v >= init(v)`, `v <= init(v)`
///    - Relational constraints: `v1 <= v2`, `v1 = v2`
///    - Constants from the problem: bounds, arithmetic in transitions
///
/// 2. For each variable in the lemma:
///    - Generate candidate templates using that variable
///    - Check if template is inductive
///    - Return strongest inductive template
///
/// # When to Use
///
/// Use when Farkas interpolation produces point-specific lemmas (e.g., `x != 5`
/// instead of `x >= 0`). Template generalization can recover range lemmas when
/// interpolation-based approaches fail.
///
/// # Reference
///
/// Based on PCSat's template-based synthesis from CoAR:
/// - `reference/coar/lib/PCSat/synthesis/solutionTemplate.ml`
/// - the development design notes
///
/// Part of #1081, #1049
pub(crate) struct TemplateGeneralizer {
    /// Whether to try relational templates (e.g., x <= y)
    use_relational: bool,
    /// Whether to try bound templates relative to init
    use_init_bounds: bool,
}

impl Default for TemplateGeneralizer {
    fn default() -> Self {
        Self::new()
    }
}

impl TemplateGeneralizer {
    /// Create a new template generalizer with default settings.
    pub(crate) fn new() -> Self {
        Self {
            use_relational: true,
            use_init_bounds: true,
        }
    }

    /// Check if a lemma is a point-blocking constraint (candidates for template upgrade).
    pub(crate) fn is_point_constraint(expr: &ChcExpr) -> bool {
        crate::expr::maybe_grow_expr_stack(|| match expr {
            ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
                matches!(
                    (args[0].as_ref(), args[1].as_ref()),
                    (ChcExpr::Var(_), ChcExpr::Int(_)) | (ChcExpr::Int(_), ChcExpr::Var(_))
                )
            }
            ChcExpr::Op(ChcOp::Ne, args) if args.len() == 2 => {
                matches!(
                    (args[0].as_ref(), args[1].as_ref()),
                    (ChcExpr::Var(_), ChcExpr::Int(_)) | (ChcExpr::Int(_), ChcExpr::Var(_))
                )
            }
            ChcExpr::Op(ChcOp::And, args) => args.iter().all(|a| Self::is_point_constraint(a)),
            _ => false,
        })
    }

    /// Extract point values from a point constraint.
    pub(crate) fn extract_point_values(expr: &ChcExpr) -> Option<HashMap<String, i128>> {
        let mut values = HashMap::default();

        fn collect_equalities(expr: &ChcExpr, values: &mut HashMap<String, i128>) -> bool {
            crate::expr::maybe_grow_expr_stack(|| match expr {
                ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
                    match (args[0].as_ref(), args[1].as_ref()) {
                        (ChcExpr::Var(v), ChcExpr::Int(n)) => {
                            values.insert(v.name.clone(), *n);
                            true
                        }
                        (ChcExpr::Int(n), ChcExpr::Var(v)) => {
                            values.insert(v.name.clone(), *n);
                            true
                        }
                        _ => false,
                    }
                }
                ChcExpr::Op(ChcOp::Ne, _) => true,
                ChcExpr::Op(ChcOp::And, args) => args.iter().all(|a| collect_equalities(a, values)),
                _ => false,
            })
        }

        if collect_equalities(expr, &mut values) && !values.is_empty() {
            Some(values)
        } else {
            None
        }
    }

    /// Check if a template evaluates to TRUE at a given point.
    ///
    /// This is critical for soundness: a template generalization must actually
    /// contain the original point being blocked. Without this check, we might
    /// return a template that is inductive but doesn't block the bad state.
    ///
    /// Fix for issue #966.
    pub(crate) fn template_covers_point(
        template: &ChcExpr,
        point_values: &HashMap<String, i128>,
    ) -> bool {
        let subst: Vec<(ChcVar, ChcExpr)> = point_values
            .iter()
            .map(|(name, val)| (ChcVar::new(name, ChcSort::Int), ChcExpr::Int(*val)))
            .collect();

        let evaluated = template.substitute(&subst).simplify_constants();

        match evaluated {
            ChcExpr::Bool(true) => true,
            ChcExpr::Bool(false) => false,
            ChcExpr::Op(ChcOp::Le, ref args) if args.len() == 2 => {
                match (args[0].as_ref(), args[1].as_ref()) {
                    (ChcExpr::Int(a), ChcExpr::Int(b)) => *a <= *b,
                    _ => true,
                }
            }
            ChcExpr::Op(ChcOp::Lt, ref args) if args.len() == 2 => {
                match (args[0].as_ref(), args[1].as_ref()) {
                    (ChcExpr::Int(a), ChcExpr::Int(b)) => *a < *b,
                    _ => true,
                }
            }
            ChcExpr::Op(ChcOp::Ge, ref args) if args.len() == 2 => {
                match (args[0].as_ref(), args[1].as_ref()) {
                    (ChcExpr::Int(a), ChcExpr::Int(b)) => *a >= *b,
                    _ => true,
                }
            }
            ChcExpr::Op(ChcOp::Gt, ref args) if args.len() == 2 => {
                match (args[0].as_ref(), args[1].as_ref()) {
                    (ChcExpr::Int(a), ChcExpr::Int(b)) => *a > *b,
                    _ => true,
                }
            }
            ChcExpr::Op(ChcOp::Eq, ref args) if args.len() == 2 => {
                match (args[0].as_ref(), args[1].as_ref()) {
                    (ChcExpr::Int(a), ChcExpr::Int(b)) => *a == *b,
                    _ => true,
                }
            }
            ChcExpr::Op(ChcOp::Ne, ref args) if args.len() == 2 => {
                match (args[0].as_ref(), args[1].as_ref()) {
                    (ChcExpr::Int(a), ChcExpr::Int(b)) => *a != *b,
                    _ => true,
                }
            }
            _ => true,
        }
    }

    /// Generate init-bound templates for a variable.
    pub(crate) fn generate_init_bound_templates(var: &ChcVar, bounds: &InitBounds) -> Vec<ChcExpr> {
        let mut templates = Vec::new();
        let v = ChcExpr::var(ChcVar::new(&var.name, var.sort.clone()));

        if bounds.min != i64::MIN {
            templates.push(ChcExpr::ge(v.clone(), ChcExpr::int(bounds.min)));
        }

        if bounds.max != i64::MAX {
            templates.push(ChcExpr::le(v.clone(), ChcExpr::int(bounds.max)));
        }

        if bounds.is_exact() {
            templates.push(ChcExpr::eq(v.clone(), ChcExpr::int(bounds.min)));
        }

        if bounds.is_exact() {
            templates.push(ChcExpr::gt(v.clone(), ChcExpr::int(bounds.min)));
            templates.push(ChcExpr::lt(v, ChcExpr::int(bounds.min)));
        }

        templates
    }

    /// Generate relational templates between two variables.
    pub(crate) fn generate_relational_templates(var1: &ChcVar, var2: &ChcVar) -> Vec<ChcExpr> {
        if var1.name == var2.name {
            return Vec::new();
        }

        if var1.sort != var2.sort {
            return Vec::new();
        }

        let v1 = ChcExpr::var(ChcVar::new(&var1.name, var1.sort.clone()));
        let v2 = ChcExpr::var(ChcVar::new(&var2.name, var2.sort.clone()));

        let mut templates = vec![
            ChcExpr::le(v1.clone(), v2.clone()),
            ChcExpr::ge(v1.clone(), v2.clone()),
            ChcExpr::eq(v1.clone(), v2.clone()),
        ];

        if matches!(var1.sort, ChcSort::Int) {
            let sum = ChcExpr::add(v1, v2);
            templates.push(ChcExpr::ge(sum.clone(), ChcExpr::Int(0)));
            templates.push(ChcExpr::le(sum, ChcExpr::Int(0)));
        }

        templates
    }
}

impl LemmaGeneralizer for TemplateGeneralizer {
    fn generalize(&self, lemma: &ChcExpr, level: u32, ts: &mut dyn TransitionSystemRef) -> ChcExpr {
        if !Self::is_point_constraint(lemma) {
            return lemma.clone();
        }

        let lemma_vars = lemma.vars();
        if lemma_vars.is_empty() {
            return lemma.clone();
        }

        let point_values = Self::extract_point_values(lemma);

        let init_bounds = ts.init_bounds();

        let mut candidates: Vec<ChcExpr> = Vec::new();

        if self.use_init_bounds {
            for var in &lemma_vars {
                if let Some(bounds) = init_bounds.get(&var.name) {
                    let templates = Self::generate_init_bound_templates(var, bounds);
                    candidates.extend(templates);
                }
            }
        }

        if self.use_relational && lemma_vars.len() >= 2 {
            for (i, var1) in lemma_vars.iter().enumerate() {
                for var2 in lemma_vars.iter().skip(i + 1) {
                    let templates = Self::generate_relational_templates(var1, var2);
                    candidates.extend(templates);
                }
            }
        }

        for candidate in candidates {
            if let Some(ref pv) = point_values {
                if !Self::template_covers_point(&candidate, pv) {
                    continue;
                }
            }

            if ts.check_inductive(&candidate, level) {
                return candidate;
            }
        }

        lemma.clone()
    }

    fn name(&self) -> &'static str {
        "template"
    }
}
