// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
// FlatZinc to SMT-LIB2 main translation logic

use ay_core::kani_compat::DetHashMap as HashMap;

use ay_flatzinc_parser::ast::*;

use crate::builtins;
use crate::error::TranslateError;
use crate::globals;
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

    pub(crate) fn declare_variable(&mut self, var: &VarDecl) -> Result<(), TranslateError> {
        let is_output = has_output_annotation(&var.annotations);

        match &var.ty {
            FznType::Bool => {
                self.emit_scalar_var(&var.id, Sort::Bool);
                self.var_domains.insert(var.id.clone(), VarDomain::Bool);
                if is_output {
                    self.push_output(&var.id, false, true);
                }
            }
            FznType::Int => {
                self.emit_scalar_var(&var.id, Sort::Int);
                self.var_domains
                    .insert(var.id.clone(), VarDomain::IntUnbounded);
                if is_output {
                    self.push_output(&var.id, false, false);
                }
            }
            FznType::IntRange(lo, hi) => {
                self.emit_scalar_var(&var.id, Sort::Int);
                self.emit_bounds(&var.id, *lo, *hi);
                self.var_domains
                    .insert(var.id.clone(), VarDomain::IntRange(*lo, *hi));
                if is_output {
                    self.push_output(&var.id, false, false);
                }
            }
            FznType::IntSet(values) => {
                self.emit_scalar_var(&var.id, Sort::Int);
                self.emit_domain(&var.id, values);
                self.var_domains
                    .insert(var.id.clone(), VarDomain::IntSet(values.clone()));
                if is_output {
                    self.push_output(&var.id, false, false);
                }
            }
            FznType::ArrayOf { index, elem } => {
                if is_set_type(elem) {
                    self.declare_set_array_var(&var.id, index, &var.value)?;
                } else {
                    self.declare_array_var(&var.id, index, elem, is_output)?;
                }
            }
            FznType::SetOfIntRange(lo, hi) => {
                let width = materialized_range_len(*lo, *hi, "set-of-int")?;
                self.emit_set_var(&var.id, *lo, *hi, width);
                if is_output {
                    self.push_set_output(&var.id, *lo, *hi, width);
                }
            }
            ty => return Err(TranslateError::UnsupportedType(format!("{ty:?}"))),
        }

        // Handle variable assignment (alias or fixed value)
        if let Some(ref val) = var.value {
            if !matches!(&var.ty, FznType::ArrayOf { elem, .. } if is_set_type(elem)) {
                self.emit_var_assignment(&var.id, &var.ty, val)?;
            }
        }
        Ok(())
    }

    fn emit_var_assignment(
        &mut self,
        name: &str,
        ty: &FznType,
        val: &Expr,
    ) -> Result<(), TranslateError> {
        // Defer assignments to after all declarations (same as bounds).
        if let FznType::ArrayOf { index, .. } = ty {
            let (lo, hi) = index_range(index)?;
            let val_elems = self.expr_to_smt_array(val)?;
            validate_array_len(name, lo, hi, val_elems.len())?;
            for (i, smt_val) in val_elems.iter().enumerate() {
                let offset = i64::try_from(i).map_err(|_| {
                    TranslateError::UnsupportedType(format!(
                        "array {name} has too many initializer elements"
                    ))
                })?;
                let index = lo.checked_add(offset).ok_or_else(|| {
                    TranslateError::UnsupportedType(format!("array {name} index overflows i64"))
                })?;
                let smt_var = format!("{name}_{index}");
                self.deferred_bounds
                    .push(format!("(assert (= {smt_var} {smt_val}))"));
            }
        } else {
            let smt_val = self.expr_to_smt(val)?;
            self.deferred_bounds
                .push(format!("(assert (= {name} {smt_val}))"));
        }
        Ok(())
    }

    fn emit_scalar_var(&mut self, name: &str, sort: Sort) {
        self.emit_fmt(format_args!("(declare-const {} {})", name, sort.smt_name()));
        self.scalar_vars
            .insert(name.to_string(), (name.to_string(), sort));
        self.all_smt_vars.push(name.to_string());
    }

    fn emit_set_var(&mut self, name: &str, lo: i64, hi: i64, width: usize) {
        for i in 0..width {
            let bit_name = set_bit_name(name, i as u32);
            self.emit_fmt(format_args!("(declare-const {bit_name} Bool)"));
            self.all_smt_vars.push(bit_name);
        }
        self.set_vars.insert(name.to_string(), (lo, hi));
    }

    fn declare_set_array_var(
        &mut self,
        name: &str,
        index: &IndexSet,
        value: &Option<Expr>,
    ) -> Result<(), TranslateError> {
        let (lo, hi) = index_range(index)?;
        let elems = match value {
            Some(Expr::ArrayLit(elems)) => elems,
            Some(other) => {
                return Err(TranslateError::UnsupportedType(format!(
                    "array set variable {name}: expected array initializer, got {other:?}"
                )))
            }
            None => {
                validate_array_len(name, lo, hi, 0)?;
                self.array_set_vars
                    .insert(name.to_string(), (lo, hi, Vec::new()));
                return Ok(());
            }
        };
        validate_array_len(name, lo, hi, elems.len())?;

        let mut set_names = Vec::with_capacity(elems.len());
        for elem in elems {
            match elem {
                Expr::Ident(set_name) if self.set_vars.contains_key(set_name) => {
                    set_names.push(set_name.clone());
                }
                Expr::Ident(set_name) => {
                    return Err(TranslateError::UnknownIdentifier(format!(
                        "array set variable {name}: {set_name} is not a set var"
                    )));
                }
                other => {
                    return Err(TranslateError::UnsupportedType(format!(
                        "array set variable {name}: expected set variable identifier, got {other:?}"
                    )));
                }
            }
        }

        self.array_set_vars
            .insert(name.to_string(), (lo, hi, set_names));
        Ok(())
    }

    fn emit_bounds(&mut self, name: &str, lo: i64, hi: i64) {
        // Defer bounds to after all declarations to work around a ay bug
        // where interleaved declare/assert patterns cause hangs (#324).
        self.deferred_bounds
            .push(format!("(assert (>= {} {}))", name, smt_int(lo)));
        self.deferred_bounds
            .push(format!("(assert (<= {} {}))", name, smt_int(hi)));
    }

    fn emit_domain(&mut self, name: &str, values: &[i64]) {
        // Defer domain constraints to after all declarations.
        if values.is_empty() {
            self.deferred_bounds.push("(assert false)".to_string());
        } else if values.len() == 1 {
            self.deferred_bounds
                .push(format!("(assert (= {} {}))", name, smt_int(values[0])));
        } else {
            let disjuncts: Vec<String> = values
                .iter()
                .map(|v| format!("(= {} {})", name, smt_int(*v)))
                .collect();
            self.deferred_bounds
                .push(format!("(assert (or {}))", disjuncts.join(" ")));
        }
    }

    fn emit_elem_bounds(&mut self, smt_name: &str, elem: &FznType) {
        match elem {
            FznType::IntRange(lo, hi) => self.emit_bounds(smt_name, *lo, *hi),
            FznType::IntSet(values) => self.emit_domain(smt_name, values),
            _ => {}
        }
    }

    fn declare_array_var(
        &mut self,
        name: &str,
        index: &IndexSet,
        elem: &FznType,
        is_output: bool,
    ) -> Result<(), TranslateError> {
        let (lo, hi) = index_range(index)?;
        let (sort, is_bool) = elem_sort(elem)?;
        self.array_vars.insert(name.to_string(), (lo, hi, sort));
        let mut smt_names = Vec::new();
        for i in lo..=hi {
            let smt_name = format!("{name}_{i}");
            self.emit_fmt(format_args!(
                "(declare-const {} {})",
                smt_name,
                sort.smt_name()
            ));
            self.all_smt_vars.push(smt_name.clone());
            self.emit_elem_bounds(&smt_name, elem);
            let elem_domain = elem_to_domain(elem, is_bool);
            self.var_domains.insert(smt_name.clone(), elem_domain);
            smt_names.push(smt_name);
        }
        if is_output {
            self.output_vars.push(OutputVarInfo {
                fzn_name: name.to_string(),
                smt_names,
                is_array: true,
                array_range: Some((lo, hi)),
                is_bool,
                is_set: false,
                set_range: None,
            });
        }
        Ok(())
    }

    fn push_output(&mut self, name: &str, is_array: bool, is_bool: bool) {
        self.output_vars.push(OutputVarInfo {
            fzn_name: name.to_string(),
            smt_names: vec![name.to_string()],
            is_array,
            array_range: None,
            is_bool,
            is_set: false,
            set_range: None,
        });
    }

    fn push_set_output(&mut self, name: &str, lo: i64, hi: i64, width: usize) {
        let smt_names: Vec<String> = (0..width).map(|i| set_bit_name(name, i as u32)).collect();
        self.output_vars.push(OutputVarInfo {
            fzn_name: name.to_string(),
            smt_names,
            is_array: false,
            array_range: None,
            is_bool: false,
            is_set: true,
            set_range: Some((lo, hi)),
        });
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

/// Check if an expression is a constant (integer literal or parameter reference).
///
/// Used by `detect_logic` to distinguish truly nonlinear constraints
/// (variable * variable) from linear ones (constant * variable).
fn is_constant_expr(param_names: &ay_core::kani_compat::DetHashSet<&str>, expr: &Expr) -> bool {
    match expr {
        Expr::Bool(_) | Expr::Int(_) | Expr::Float(_) => true,
        Expr::Ident(name) => param_names.contains(name.as_str()),
        _ => false,
    }
}

/// Detect the appropriate SMT-LIB logic for the model.
///
/// Set variables use boolean decomposition (no bitvectors), so they are
/// compatible with QF_LIA. Returns `QF_NIA` only if genuinely nonlinear
/// operations are detected (both operands are variables), `QF_LIA` otherwise.
///
/// `int_times(a, b, r)` where one of a/b is a constant is just linear
/// multiplication (e.g., `r = 3 * x`). Only `variable * variable` requires
/// QF_NIA. Similarly, `int_mod(constant, constant, r)` is a constant
/// computation — not nonlinear.
/// Maximum domain size considered for linearization in logic detection.
/// Must match LINEARIZE_DOMAIN_LIMIT in builtins.rs.
const DETECT_LOGIC_LINEARIZE_LIMIT: i64 = 32;

fn detect_logic(model: &FznModel) -> &'static str {
    // Build a set of parameter names for constant detection.
    let param_names: ay_core::kani_compat::DetHashSet<&str> =
        model.parameters.iter().map(|p| p.id.as_str()).collect();

    // Build a map of variable domain sizes for linearization detection.
    let var_domain_size: HashMap<&str, i64> = model
        .variables
        .iter()
        .filter_map(|v| {
            let size = match &v.ty {
                FznType::Bool => 2,
                FznType::IntRange(lo, hi) => hi - lo + 1,
                FznType::IntSet(vals) => vals.len() as i64,
                _ => return None,
            };
            Some((v.id.as_str(), size))
        })
        .collect();

    let has_nonlinear = model.constraints.iter().any(|c| {
        match c.id.as_str() {
            "int_times" => {
                // Nonlinear only if both operands are variables AND neither has a
                // small enough domain for ITE-chain linearization.
                if c.args.len() < 2 {
                    return false;
                }
                if is_constant_expr(&param_names, &c.args[0])
                    || is_constant_expr(&param_names, &c.args[1])
                {
                    return false;
                }
                // If either operand is a variable with a small domain, it will be
                // linearized by the builtins handler — not truly nonlinear.
                let a_small = expr_has_small_domain(&c.args[0], &var_domain_size);
                let b_small = expr_has_small_domain(&c.args[1], &var_domain_size);
                !a_small && !b_small
            }
            "int_div" | "int_mod" => {
                c.args.len() >= 2
                    && !is_constant_expr(&param_names, &c.args[0])
                    && !is_constant_expr(&param_names, &c.args[1])
            }
            "int_pow" => {
                c.args.len() >= 2
                    && !is_constant_expr(&param_names, &c.args[0])
                    && !is_constant_expr(&param_names, &c.args[1])
            }
            _ => false,
        }
    });
    if has_nonlinear {
        "QF_NIA"
    } else {
        "QF_LIA"
    }
}

/// Check if a FlatZinc expression refers to a variable with a small enough domain
/// for linearization.
fn expr_has_small_domain(expr: &Expr, var_domain_size: &HashMap<&str, i64>) -> bool {
    match expr {
        Expr::Ident(name) => var_domain_size
            .get(name.as_str())
            .is_some_and(|&size| size > 0 && size <= DETECT_LOGIC_LINEARIZE_LIMIT),
        _ => false,
    }
}

/// Translate a FlatZinc model to SMT-LIB2.
pub fn translate(model: &FznModel) -> Result<TranslationResult, TranslateError> {
    let mut ctx = Context::new();

    let logic = detect_logic(model);
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
