// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
// FlatZinc to SMT-LIB2 main translation logic

mod variable_declarations;

use ay_core::kani_compat::DetHashMap as HashMap;

use ay_flatzinc_parser::ast::*;

use crate::builtins;
use crate::error::TranslateError;
use crate::globals;
use crate::logic;
use crate::search::{self, SearchAnnotation};

/// Maximum number of scalar items a single FlatZinc range may materialize.
///
/// Array declarations, set decompositions, and range literals all expand one
/// Rust/SMT item per value. Reject larger user-provided ranges before they can
/// overflow integer arithmetic or exhaust memory.
pub(crate) const MAX_MATERIALIZED_ITEMS: usize = 1 << 20;

pub(crate) fn materialized_range_len(
    lo: i64,
    hi: i64,
    context: &str,
) -> Result<usize, TranslateError> {
    if hi < lo {
        return Ok(0);
    }
    let len = i128::from(hi) - i128::from(lo) + 1;
    if len > MAX_MATERIALIZED_ITEMS as i128 {
        return Err(TranslateError::UnsupportedType(format!(
            "{context} range {lo}..{hi} materializes {len} items, exceeding the maximum supported {MAX_MATERIALIZED_ITEMS}"
        )));
    }
    usize::try_from(len).map_err(|_| {
        TranslateError::UnsupportedType(format!(
            "{context} range {lo}..{hi} is too large to materialize"
        ))
    })
}

/// Reject product-shaped encodings before they allocate auxiliary terms or
/// append a partial SMT script.
///
/// `terms_per_cell` accounts for encodings that emit several declarations or
/// assertions for every pair. Keeping the aggregate under the same budget as
/// scalar range materialization prevents individually bounded arrays from
/// multiplying into an unbounded quadratic translation.
pub(crate) fn ensure_quadratic_work(
    context: &str,
    left: usize,
    right: usize,
    terms_per_cell: usize,
) -> Result<(), TranslateError> {
    let work = (left as u128)
        .checked_mul(right as u128)
        .and_then(|cells| cells.checked_mul(terms_per_cell as u128))
        .ok_or_else(|| {
            TranslateError::UnsupportedType(format!(
                "{context}: quadratic encoding work exceeds the representable range"
            ))
        })?;
    if work > MAX_MATERIALIZED_ITEMS as u128 {
        return Err(TranslateError::UnsupportedType(format!(
            "{context}: quadratic encoding materializes {work} work items, exceeding the maximum supported {MAX_MATERIALIZED_ITEMS}"
        )));
    }
    Ok(())
}

/// Domain of an SMT variable, used by branching search to enumerate values.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum VarDomain {
    Bool,
    IntRange(i64, i64),
    IntSet(Vec<i64>),
    IntUnbounded,
}

/// Result of translating a FlatZinc model to SMT-LIB2.
#[derive(Debug)]
pub struct TranslationResult {
    pub smtlib: String,
    pub declarations: String,
    pub output_vars: Vec<OutputVarInfo>,
    pub objective: Option<ObjectiveInfo>,
    pub smt_var_names: Vec<String>,
    /// Only the SMT variable names needed for DZN output (subset of `smt_var_names`).
    pub output_smt_names: Vec<String>,
    pub search_annotations: Vec<SearchAnnotation>,
    pub var_domains: HashMap<String, VarDomain>,
}

/// Info about an output variable for DZN formatting.
#[derive(Debug, Clone)]
pub struct OutputVarInfo {
    pub fzn_name: String,
    pub smt_names: Vec<String>,
    pub is_array: bool,
    pub array_range: Option<(i64, i64)>,
    pub is_bool: bool,
    /// True if this is a set variable (boolean decomposition bits).
    pub is_set: bool,
    /// Domain range `(lo, hi)` for set variables, used to reconstruct element values.
    pub set_range: Option<(i64, i64)>,
}

/// Objective info for optimization problems.
#[derive(Debug, Clone)]
pub struct ObjectiveInfo {
    pub minimize: bool,
    pub smt_expr: String,
}

/// SMT sort for translated variables.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Sort {
    Bool,
    Int,
}

impl Sort {
    pub(crate) fn smt_name(self) -> &'static str {
        match self {
            Self::Bool => "Bool",
            Self::Int => "Int",
        }
    }
}

/// Construct the SMT name for a boolean bit variable in a decomposed set.
/// `var set of lo..hi` is decomposed into Bool variables `name__bit__0..name__bit__(width-1)`.
pub(crate) fn set_bit_name(set_name: &str, bit: u32) -> String {
    format!("{set_name}__bit__{bit}")
}

/// Scalar parameter value.
#[derive(Debug, Clone)]
pub(crate) enum ScalarValue {
    Bool(bool),
    Int(i64),
    Float(f64),
}

impl ScalarValue {
    pub(crate) fn to_smt(&self) -> String {
        match self {
            Self::Bool(b) => b.to_string(),
            Self::Int(n) => smt_int(*n),
            Self::Float(f) => format!("{f}"),
        }
    }
}

/// Translation context accumulating SMT-LIB output.
pub(crate) struct Context {
    pub(crate) output: String,
    pub(crate) scalar_params: HashMap<String, ScalarValue>,
    pub(crate) array_params: HashMap<String, (i64, i64, Vec<ScalarValue>)>,
    pub(crate) set_params: HashMap<String, Vec<i64>>,
    pub(crate) scalar_vars: HashMap<String, (String, Sort)>,
    pub(crate) array_vars: HashMap<String, (i64, i64, Sort)>,
    pub(crate) set_vars: HashMap<String, (i64, i64)>,
    pub(crate) array_set_params: HashMap<String, (i64, i64, Vec<Vec<i64>>)>,
    pub(crate) array_set_vars: HashMap<String, (i64, i64, Vec<String>)>,
    pub(crate) output_vars: Vec<OutputVarInfo>,
    pub(crate) all_smt_vars: Vec<String>,
    /// Domain info for each SMT variable.
    pub(crate) var_domains: HashMap<String, VarDomain>,
    aux_counter: usize,
    /// Deferred bounds: avoids ay hang from interleaved declare/assert.
    deferred_bounds: Vec<String>,
}

impl Context {
    pub(crate) fn new() -> Self {
        Self {
            output: String::with_capacity(4096),
            scalar_params: HashMap::default(),
            array_params: HashMap::default(),
            set_params: HashMap::default(),
            scalar_vars: HashMap::default(),
            array_vars: HashMap::default(),
            set_vars: HashMap::default(),
            array_set_params: HashMap::default(),
            array_set_vars: HashMap::default(),
            output_vars: Vec::new(),
            all_smt_vars: Vec::new(),
            var_domains: HashMap::default(),
            aux_counter: 0,
            deferred_bounds: Vec::new(),
        }
    }

    /// Flush deferred bound assertions into the output stream.
    /// Called after all variable declarations to avoid interleaving
    /// declare/assert that triggers ay hangs.
    pub(crate) fn flush_deferred_bounds(&mut self) {
        for bound in self.deferred_bounds.drain(..) {
            self.output.push_str(&bound);
            self.output.push('\n');
        }
    }

    /// Get a unique auxiliary ID for generated variable names.
    pub(crate) fn next_aux_id(&mut self) -> usize {
        let id = self.aux_counter;
        self.aux_counter += 1;
        id
    }

    pub(crate) fn emit(&mut self, line: &str) {
        self.output.push_str(line);
        self.output.push('\n');
    }

    /// Emit a formatted line, avoiding a temporary `String` allocation.
    pub(crate) fn emit_fmt(&mut self, args: std::fmt::Arguments<'_>) {
        use std::fmt::Write;
        self.output
            .write_fmt(args)
            .expect("invariant: String write is infallible");
        self.output.push('\n');
    }

    pub(crate) fn process_parameter(&mut self, par: &ParDecl) -> Result<(), TranslateError> {
        match &par.ty {
            FznType::Bool
            | FznType::Int
            | FznType::Float
            | FznType::IntRange(_, _)
            | FznType::FloatRange(_, _)
            | FznType::IntSet(_) => {
                let val = self.resolve_scalar_value(&par.value)?;
                self.scalar_params.insert(par.id.clone(), val);
            }
            FznType::SetOfInt | FznType::SetOfIntRange(_, _) | FznType::SetOfIntSet(_) => {
                let vals = self.resolve_set_literal(&par.value)?;
                self.set_params.insert(par.id.clone(), vals);
            }
            FznType::ArrayOf { index, elem } => {
                let (lo, hi) = index_range(index)?;
                if is_set_type(elem) {
                    let sets = self.resolve_array_of_sets(&par.value)?;
                    validate_array_len(&par.id, lo, hi, sets.len())?;
                    self.array_set_params.insert(par.id.clone(), (lo, hi, sets));
                } else {
                    let values = self.resolve_array_values(&par.value)?;
                    validate_array_len(&par.id, lo, hi, values.len())?;
                    self.array_params.insert(par.id.clone(), (lo, hi, values));
                }
            }
        }
        Ok(())
    }

    pub(crate) fn translate_constraint(
        &mut self,
        constraint: &ConstraintItem,
    ) -> Result<(), TranslateError> {
        if builtins::translate_builtin(self, constraint)? {
            return Ok(());
        }
        if globals::translate_global(self, constraint)? {
            return Ok(());
        }
        Err(TranslateError::UnsupportedConstraint(constraint.id.clone()))
    }
}

/// SMT-LIB integer formatter: negative values use `(- n)` syntax.
pub(crate) struct SmtInt(pub i64);

impl std::fmt::Display for SmtInt {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.0 < 0 {
            write!(f, "(- {})", self.0.unsigned_abs())
        } else {
            write!(f, "{}", self.0)
        }
    }
}

/// Convenience wrapper returning owned `String`. Prefer `SmtInt` in `format_args!`.
pub(crate) fn smt_int(n: i64) -> String {
    SmtInt(n).to_string()
}

fn index_range(index: &IndexSet) -> Result<(i64, i64), TranslateError> {
    match index {
        IndexSet::Range(lo, hi) => {
            materialized_range_len(*lo, *hi, "array index")?;
            Ok((*lo, *hi))
        }
        IndexSet::Int => Err(TranslateError::UnsupportedType(
            "unbounded array index".into(),
        )),
    }
}

fn validate_array_len(name: &str, lo: i64, hi: i64, actual: usize) -> Result<(), TranslateError> {
    let expected = materialized_range_len(lo, hi, "array index")?;
    if actual != expected {
        return Err(TranslateError::UnsupportedType(format!(
            "array {name} declares index range {lo}..{hi} ({expected} elements) but has {actual} initializer elements"
        )));
    }
    Ok(())
}

fn elem_sort(ty: &FznType) -> Result<(Sort, bool), TranslateError> {
    match ty {
        FznType::Bool => Ok((Sort::Bool, true)),
        FznType::Int | FznType::IntRange(_, _) | FznType::IntSet(_) => Ok((Sort::Int, false)),
        _ => Err(TranslateError::UnsupportedType(format!("{ty:?}"))),
    }
}

fn is_set_type(ty: &FznType) -> bool {
    matches!(
        ty,
        FznType::SetOfInt | FznType::SetOfIntRange(_, _) | FznType::SetOfIntSet(_)
    )
}

/// Convert an array element type to a domain for branching search.
fn elem_to_domain(elem: &FznType, is_bool: bool) -> VarDomain {
    if is_bool {
        return VarDomain::Bool;
    }
    match elem {
        FznType::IntRange(lo, hi) => VarDomain::IntRange(*lo, *hi),
        FznType::IntSet(values) => VarDomain::IntSet(values.clone()),
        _ => VarDomain::IntUnbounded,
    }
}

fn has_output_annotation(annotations: &[Annotation]) -> bool {
    annotations.iter().any(|a| match a {
        Annotation::Atom(s) => s == "output_var",
        Annotation::Call(s, _) => s == "output_array",
    })
}

/// Translate a FlatZinc model to SMT-LIB2.
pub fn translate(model: &FznModel) -> Result<TranslationResult, TranslateError> {
    let mut ctx = Context::new();

    let logic = logic::detect_logic(model);
    ctx.emit("; Generated by flatzinc-smt");
    ctx.emit_fmt(format_args!("(set-logic {logic})"));

    for par in &model.parameters {
        ctx.process_parameter(par)?;
    }
    for var in &model.variables {
        ctx.declare_variable(var)?;
    }
    ctx.flush_deferred_bounds(); // after all declarations (#324)
    for constraint in &model.constraints {
        ctx.translate_constraint(constraint)?;
    }

    let objective = match &model.solve.kind {
        SolveKind::Satisfy => None,
        SolveKind::Minimize(expr) => Some(ObjectiveInfo {
            minimize: true,
            smt_expr: ctx.expr_to_smt(expr)?,
        }),
        SolveKind::Maximize(expr) => Some(ObjectiveInfo {
            minimize: false,
            smt_expr: ctx.expr_to_smt(expr)?,
        }),
    };

    let search_annotations = search::parse_search_annotations(&model.solve.annotations);
    let declarations = ctx.output.clone();
    let smt_var_names = ctx.all_smt_vars.clone();

    // Collect only the SMT names needed for DZN output formatting.
    let output_smt_names: Vec<String> = ctx
        .output_vars
        .iter()
        .flat_map(|v| v.smt_names.iter().cloned())
        .collect();

    ctx.emit("(check-sat)");
    if !ctx.all_smt_vars.is_empty() {
        let vars = ctx.all_smt_vars.join(" ");
        ctx.emit_fmt(format_args!("(get-value ({vars}))"));
    }

    Ok(TranslationResult {
        smtlib: ctx.output,
        declarations,
        output_vars: ctx.output_vars,
        objective,
        smt_var_names,
        output_smt_names,
        search_annotations,
        var_domains: ctx.var_domains,
    })
}
