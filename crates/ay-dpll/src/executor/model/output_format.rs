// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model output formatting helpers: function tables, array values, eval-value formatting.
//!
//! Extracted from `output.rs` for code health. The main `get-model`/`get-value`/
//! `get-objectives` methods remain in `output.rs`; this module has the formatting
//! and placeholder-resolution methods they call.

use std::collections::HashMap;

use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::term::{Symbol, TermData};
use ay_core::{quote_symbol, string_literal, Sort, TermId};
use num_bigint::BigInt;

use crate::executor_format::{
    format_bigint, format_bitvec, format_model_atom_surface, format_rational, format_real,
    format_sort_surface,
};

use super::datatype_array_fields::AuthenticatedDatatypeArrayMembers;
use super::Executor;
use super::{EvalValue, Model};

mod datatype_array_selectors;
mod rendered_array_value;

/// Typed failure from the exact row pipeline shared by model output and the
/// independent gate.  Coverage failures remain distinct from a semantic
/// refutation that proves the candidate table is not a function.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::executor) enum PrintedUfTableRowsError {
    /// A placeholder or provenance value could not be resolved exactly.
    Coverage(String),
    /// One argument point resolves to two different results.
    InconsistentFunctionTable {
        name: String,
        point: Vec<String>,
        first: String,
        second: String,
    },
}

impl std::fmt::Display for PrintedUfTableRowsError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Coverage(detail) => formatter.write_str(detail),
            Self::InconsistentFunctionTable {
                name,
                point,
                first,
                second,
            } => write!(
                formatter,
                "inconsistent function table for {}: point ({}) resolves to both {} and {}",
                quote_symbol(name),
                point.join(" "),
                first,
                second
            ),
        }
    }
}

/// Explicit non-value marker for an internal invariant violation: a formatting
/// path asked for the printed form of a value the evaluator does not have
/// (`EvalValue::Unknown`), on a path whose callers are contracted to guard
/// against that. It is deliberately NOT a parseable SMT-LIB value, so any
/// consumer — including the external z3 model pin — fails loudly instead of
/// accepting a fabricated default (#no-fabricated-model-values). User-facing
/// output paths use [`Executor::try_format_eval_value`] and surface a command
/// `(error ...)` instead of ever printing this marker.
pub(super) fn value_unavailable_marker(detail: &str) -> String {
    tracing::error!(
        detail,
        "internal invariant violation: formatting a model value that does not exist"
    );
    format!("(_ ay.value-unavailable {detail})")
}

/// The z3-exact USER-FACING spelling of a rational-valued Real `EvalValue`
/// (`5.0`, `(- 5.0)`, `(/ 7.0 2.0)`, `(- (/ 7.0 2.0))`), or `None` when the
/// value is not an exact rational (Unknown, irrational algebraic,
/// non-numeric). Callers gate on the Real SORT; this only inspects the value
/// (#real-fmt).
fn eval_value_real_string(value: &EvalValue) -> Option<String> {
    match value {
        EvalValue::Rational(r) => Some(format_real(r)),
        EvalValue::Algebraic(v) => match v.to_number_for_output() {
            Some(ay_nra::RealScalar::Rational(r)) => Some(format_real(&r)),
            _ => None,
        },
        _ => None,
    }
}

/// The SMT-LIB USER-FACING spelling of a rational-valued non-Real
/// `EvalValue`: an integer as `n` / `(- n)`, a non-integer as `(/ n d)` /
/// `(- (/ n d))`. `None` when the value is not an exact rational. The
/// internal comparison-key spelling (`-n`) stays in
/// [`Executor::try_format_eval_value`].
fn eval_value_rational_string(value: &EvalValue) -> Option<String> {
    let format = |r: &num_rational::BigRational| {
        if r.is_integer() {
            format_bigint(r.numer())
        } else {
            format_rational(r)
        }
    };
    match value {
        EvalValue::Rational(r) => Some(format(r)),
        EvalValue::Algebraic(v) => match v.to_number_for_output() {
            Some(ay_nra::RealScalar::Rational(r)) => Some(format(&r)),
            _ => None,
        },
        _ => None,
    }
}

/// Red zone size for `stacker::maybe_grow` in array model formatting (#4602).
const ARRAY_FMT_STACK_RED_ZONE: usize = if cfg!(debug_assertions) {
    128 * 1024
} else {
    32 * 1024
};

/// Stack segment size allocated by stacker for array model formatting recursion.
const ARRAY_FMT_STACK_SIZE: usize = 2 * 1024 * 1024;

/// How the array-witness interpreter treats model gaps.
///
/// `Strict` is the OUTPUT path: an absent base default and an Unknown ACTIVE
/// `select` read both fail closed (`None`) — the printer is never a completion
/// authority (#no-fabricated-model-values). The two completion modes build
/// CANDIDATES for the model-completion passes in `completion.rs`, which must
/// commit them into the model and re-validate before any output reads them:
///
/// * `CompleteDefault` may choose the element sort's canonical value for a
///   genuinely missing, non-conflicted base default (first-pass completion).
/// * `CompleteSkipUnknownReads` additionally SKIPS an active `select` read
///   whose VALUE evaluates to Unknown (the guarded-vacuous-read shape: the
///   read only occurs under an implication/disjunct the SAT assignment
///   satisfies without it, so no theory ever assigned the cell) instead of
///   failing the whole array. It is reachable ONLY from the gate-verified,
///   retracting second completion pass: a skipped read that actually
///   constrains the cell falsifies re-validation and the whole candidate is
///   retracted, so the skip can never ship an invalid witness.
///
/// An Unknown INDEX fails closed in EVERY mode — a read whose cell cannot be
/// named must not let a completed default claim authority at that cell.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum ArrayInterpMode {
    Strict,
    CompleteDefault,
    CompleteSkipUnknownReads,
}

impl ArrayInterpMode {
    /// Whether a genuinely missing, non-conflicted base default may be
    /// completed with the element sort's canonical value.
    fn completes_missing_default(self) -> bool {
        !matches!(self, Self::Strict)
    }

    /// Whether an ACTIVE `select` read whose value is Unknown is skipped
    /// (candidate-building only) instead of failing the array closed.
    fn skips_unknown_active_reads(self) -> bool {
        matches!(self, Self::CompleteSkipUnknownReads)
    }
}

/// Fold authoritative/newest-first interpretation entries into an SMT store
/// chain. SMT stores are applied from the base outward, so the oldest entry
/// must be emitted first and the authoritative entry last.
fn format_newest_first_store_chain(mut base: String, stores: &[(String, String)]) -> String {
    for (index, value) in stores.iter().rev() {
        base = format!("(store {base} {index} {value})");
    }
    base
}

impl Executor {
    /// Pick a simple SMT-LIB symbol for a generated model parameter. Each
    /// slot has its own base and fallback family, so names are also distinct
    /// within the definition. The frontend decodes quoted source symbols.
    pub(in crate::executor) fn model_formal_name(
        &self,
        prefix: &str,
        index: usize,
        owner: ay_core::render_admission::Owner<'_>,
    ) -> String {
        use ay_core::render_admission as output;
        let mut candidate = output::format(owner, format_args!("{prefix}{index}"));
        let mut suffix = 0usize;
        while !candidate.is_empty() && self.ctx.has_symbol_binding(&candidate) {
            candidate = output::format(owner, format_args!("{prefix}{index}!{suffix}"));
            suffix += 1;
        }
        candidate
    }

    pub(super) fn model_formal_names(&self, prefix: &str, arity: usize) -> Vec<String> {
        (0..arity)
            .map(|index| self.model_formal_name(prefix, index, None))
            .collect()
    }

    pub(super) fn format_model_parameters(&self, names: &[String], sorts: &[Sort]) -> String {
        names
            .iter()
            .zip(sorts)
            .map(|(name, sort)| format!("({name} {})", format_sort_surface(&self.ctx, sort)))
            .collect::<Vec<_>>()
            .join(" ")
    }

    /// Format an exact total projection as an SMT-LIB `define-fun`.
    pub(super) fn format_projection_function(
        &self,
        name: &str,
        argument_sorts: &[Sort],
        result_sort: &Sort,
        projected_argument: usize,
    ) -> Result<String, String> {
        let Some(projected_sort) = argument_sorts.get(projected_argument) else {
            return Err(format!(
                "selected argument {projected_argument} is outside arity {}",
                argument_sorts.len()
            ));
        };
        if projected_sort != result_sort {
            return Err(format!(
                "selected argument {projected_argument} has sort {}, not result sort {}",
                format_sort_surface(&self.ctx, projected_sort),
                format_sort_surface(&self.ctx, result_sort)
            ));
        }
        let parameter_names = self.model_formal_names("__ay_projection_arg_", argument_sorts.len());
        let parameters = self.format_model_parameters(&parameter_names, argument_sorts);
        Ok(format!(
            "  (define-fun {} ({}) {}\n    {})",
            quote_symbol(name),
            parameters,
            format_sort_surface(&self.ctx, result_sort),
            quote_symbol(&parameter_names[projected_argument]),
        ))
    }

    /// Replace opaque EUF cells in Seq-typed function-table positions with
    /// placeholders for the aligned source application's actual terms. The
    /// ordinary placeholder resolver can then read the concrete sequence
    /// witness from `Model::completed_values`.
    ///
    /// `function_tables` and `function_table_terms` are positionally aligned by
    /// extraction and model combination. Missing/misaligned provenance is not
    /// enough authority to reinterpret an opaque class as a public sequence,
    /// so every such case fails closed.
    pub(super) fn sequence_table_provenance_placeholders(
        &self,
        expected_symbol: &str,
        arg_sorts: &[Sort],
        result_sort: &Sort,
        table: &[(Vec<String>, String)],
        source_terms: Option<&[TermId]>,
    ) -> Result<Vec<(Vec<String>, String)>, String> {
        let has_sequence_position = arg_sorts.iter().any(|sort| matches!(sort, Sort::Seq(_)))
            || matches!(result_sort, Sort::Seq(_));
        if !has_sequence_position {
            return Ok(table.to_vec());
        }
        let sources = source_terms.ok_or_else(|| {
            "sequence-typed function table has no aligned source-term provenance".to_string()
        })?;
        if sources.len() != table.len() {
            return Err(format!(
                "sequence-typed function table/source length mismatch: {} rows, {} sources",
                table.len(),
                sources.len()
            ));
        }

        let mut out = Vec::with_capacity(table.len());
        for ((row_args, row_result), &source) in table.iter().zip(sources) {
            let TermData::App(source_symbol, source_args) = self.ctx.terms.get(source) else {
                return Err(format!(
                    "sequence-typed function-table source t{} is not an application",
                    source.0
                ));
            };
            if source_symbol.name() != expected_symbol {
                return Err(format!(
                    "sequence-typed function-table source t{} belongs to {}, not {}",
                    source.0,
                    source_symbol.name(),
                    expected_symbol
                ));
            }
            if source_args.len() != row_args.len() || source_args.len() != arg_sorts.len() {
                return Err(format!(
                    "sequence-typed function-table source t{} has inconsistent arity",
                    source.0
                ));
            }
            if self.ctx.terms.sort(source) != result_sort
                || source_args
                    .iter()
                    .zip(arg_sorts)
                    .any(|(&term, sort)| self.ctx.terms.sort(term) != sort)
            {
                return Err(format!(
                    "sequence-typed function-table source t{} has inconsistent signature",
                    source.0
                ));
            }
            let args = row_args
                .iter()
                .zip(source_args)
                .zip(arg_sorts)
                .map(|((raw, &term), sort)| {
                    if matches!(sort, Sort::Seq(_)) {
                        format!("@?{}", term.0)
                    } else {
                        raw.clone()
                    }
                })
                .collect();
            let result = if matches!(result_sort, Sort::Seq(_)) {
                format!("@?{}", source.0)
            } else {
                row_result.clone()
            };
            out.push((args, result));
        }
        Ok(out)
    }

    /// Format a function table as an SMT-LIB define-fun.
    ///
    /// Resolves `@?N` placeholder values (from EUF model extraction) to concrete
    /// theory values using the full model (#5452). Returns `Err` when a
    /// placeholder resolves to no value at all — printing a fabricated default
    /// in its place would be a lie, so the caller surfaces a command-level
    /// error instead (#no-fabricated-model-values).
    pub(super) fn format_function_table(
        &self,
        name: &str,
        arg_sorts: &[Sort],
        result_sort: &Sort,
        table: &[(Vec<String>, String)],
        model: &Model,
        overloaded: &super::overloaded_ctor_surface::OverloadedCtors,
    ) -> Result<String, String> {
        let names = self.model_formal_names("x", arg_sorts.len());
        let params_str = self.format_model_parameters(&names, arg_sorts);
        let result_sort_str = format_sort_surface(&self.ctx, result_sort);

        let mut resolved_table = self
            .printed_uf_table_rows(name, arg_sorts, result_sort, table, model)
            .map_err(|error| error.to_string())?;
        // Each cell takes the name `Self::table_cell_surface` gives it, if
        // any, and then goes through `Self::ascribe_overloaded_ctors` with its
        // column's sort (#overloaded-nil-surface), as z3 ascribes a table cell.
        for (args, value) in &mut resolved_table {
            if args.len() != names.len() {
                return Err(format!(
                    "function {} has a row with mismatched arity",
                    quote_symbol(name)
                ));
            }
            let cells = args
                .iter_mut()
                .zip(arg_sorts)
                .chain(std::iter::once((value, result_sort)));
            for (cell, sort) in cells {
                if let Some(named) = self.table_cell_surface(cell, sort, overloaded) {
                    *cell = named;
                }
                if !overloaded.is_empty() {
                    *cell = self.ascribe_overloaded_ctors(cell, sort, overloaded);
                }
            }
        }

        // Build nested ite expression from resolved table.
        let body = if resolved_table.is_empty() {
            // Empty table: no application of this function is constrained by
            // the formula, so ANY total function is a valid witness — complete
            // it with the canonical constant body (legitimate model
            // completion of an unconstrained function, not a fabricated value
            // for a missing one).
            self.ascribe_overloaded_ctors(
                &self.default_value_surface(result_sort),
                result_sort,
                overloaded,
            )
        } else {
            self.format_function_body(&names, result_sort, &resolved_table)
        };

        Ok(format!(
            "  (define-fun {} ({}) {}\n    {})",
            quote_symbol(name),
            params_str,
            result_sort_str,
            body
        ))
    }

    /// Constant-body instance of the native function-definition renderer.
    /// The actual immutable DATA owner pays every parameter/body copy.
    pub(super) fn format_retained_constant_function(
        &self,
        name: &str,
        arguments: &[Sort],
        result_sort: &Sort,
        value: &ay_model_check::ModelValue,
        admission: &dyn ay_core::term::TermConstructionAdmission,
    ) -> Result<String, String> {
        use ay_core::render_admission as output;
        if !super::evaluation_copies::active() || !super::evaluation_copies::validate(self) {
            return Err("retained function has no live read owner".to_owned());
        }
        let owner = Some(admission);
        let mut text = output::Buffer::new(owner);
        let name = output::quote(owner, name);
        if !text.push("  (define-fun ") || !text.push(&name) || !text.push(" (") {
            return Err("retained function output refused".to_owned());
        }
        for (index, sort) in arguments.iter().enumerate() {
            if index != 0 && !text.character(' ') {
                return Err("retained function output refused".to_owned());
            }
            let sort = crate::executor_format::format_sort_surface_owned(&self.ctx, sort, owner);
            let formal = self.model_formal_name("x", index, owner);
            if formal.is_empty()
                || !text.format(format_args!("({formal} "))
                || !text.push(&sort)
                || !text.character(')')
            {
                return Err("retained function output refused".to_owned());
            }
        }
        let result =
            crate::executor_format::format_sort_surface_owned(&self.ctx, result_sort, owner);
        let body = self
            .retained_array_render_value(value, result_sort, admission)
            .map_err(|error| error.to_string())?;
        if !text.push(") ")
            || !text.push(&result)
            || !text.push("\n    ")
            || !text.push(&body)
            || !text.character(')')
        {
            return Err("retained function output refused".to_owned());
        }
        admission.check().map_err(|e| e.to_string())?;
        Ok(text.finish())
    }

    /// Authored ground UF applications by (symbol, arity), memoized
    /// against the exact (assertions, finitely-expanded roots) snapshot:
    /// the census traversal is O(assertions x term size) and both the
    /// printer and the gate ask per symbol per round (#dt-uf-table-
    /// authored-points; the uncached walk cost ~8 s on vlsat3's 23k
    /// assertions). Any snapshot difference rebuilds, so a stale census
    /// is never served.
    fn uf_authored_applications(
        &self,
    ) -> std::sync::Arc<ay_core::kani_compat::DetHashMap<(String, usize), Vec<(TermId, Vec<TermId>)>>>
    {
        let roots = self.finitely_expanded_ground_roots();
        if let Some((assertions, cached_roots, map, _quantifier_memo)) =
            self.uf_authored_apps_cache.borrow().as_ref()
        {
            if assertions.as_slice() == self.ctx.assertions.as_slice() && *cached_roots == roots {
                return map.clone();
            }
        }
        let mut applications: ay_core::kani_compat::DetHashMap<
            (String, usize),
            Vec<(TermId, Vec<TermId>)>,
        > = ay_core::kani_compat::DetHashMap::default();
        let mut visited = HashSet::default();
        for &assertion in &self.ctx.assertions {
            self.collect_uf_applications(assertion, &mut applications, &mut visited);
        }
        for &root in &roots {
            self.collect_uf_applications(root, &mut applications, &mut visited);
        }
        let map = std::sync::Arc::new(applications);
        *self.uf_authored_apps_cache.borrow_mut() = Some((
            self.ctx.assertions.clone(),
            roots,
            map.clone(),
            HashMap::default(),
        ));
        map
    }

    /// `symbol_occurs_under_quantifier` memoized against the same
    /// snapshot as the authored-application census: the walk is
    /// O(assertions x term size) per call and the completion trigger
    /// asks once per printed-table call.
    fn uf_symbol_occurs_under_quantifier(&self, name: &str) -> bool {
        // Populate / validate the snapshot first (also builds the memo).
        let _ = self.uf_authored_applications();
        if let Some(hit) = self
            .uf_authored_apps_cache
            .borrow()
            .as_ref()
            .and_then(|(_, _, _, memo)| memo.get(name).copied())
        {
            return hit;
        }
        // The walk does not touch this cache, so no borrow is held across
        // it; insert under a fresh borrow afterwards. This shape also keeps
        // `Executor: Send`: the memo used to be an `Rc<RefCell<_>>` cloned
        // out of the cache borrow, which broke ay-milp's session contract.
        let occurs = self.symbol_occurs_under_quantifier(name);
        if let Some((_, _, _, memo)) = self.uf_authored_apps_cache.borrow_mut().as_mut() {
            memo.insert(name.to_string(), occurs);
        }
        occurs
    }

    /// Structural rendering of a datatype-sorted term for UF-table keys:
    /// `ite` follows the model's branch, a constructor application renders
    /// over its parts (datatype parts recursively, scalar parts by model
    /// evaluation), and anything else reads the dt-egraph assignment (which
    /// itself resolves selector projections structurally) or the model's
    /// term value. This mirrors how the independent gate evaluates the
    /// same term when it looks an application up in the printed body, so a
    /// completed row is keyed at the point the gate actually queries.
    fn structural_dt_table_key(&self, model: &Model, term: TermId, depth: u32) -> Option<String> {
        if depth == 0 {
            return None;
        }
        match self.ctx.terms.get(term) {
            TermData::Ite(cond, then_t, else_t) => {
                match self.term_value_string(model, *cond).ok()?.as_str() {
                    "true" => self.structural_dt_table_key(model, *then_t, depth - 1),
                    "false" => self.structural_dt_table_key(model, *else_t, depth - 1),
                    _ => None,
                }
            }
            TermData::App(sym, args) => {
                if self.ctx.is_constructor(sym.name()).is_none() {
                    // Selector application: project from the operand's
                    // STRUCTURAL rendering, exactly as the gate evaluates
                    // it. The class value of a selector application can be
                    // an abstract completion unrelated to the operand's
                    // constructor fields, which is the divergence this
                    // keying exists to avoid.
                    if args.len() == 1 {
                        if let Some(projected) = self.structural_dt_selector_projection(
                            model,
                            sym.name(),
                            args[0],
                            depth,
                        ) {
                            return Some(projected);
                        }
                    }
                    return self
                        .dt_egraph_value(model, term)
                        .or_else(|| self.term_value_string(model, term).ok());
                }
                let (_dt, ctor) = self.ctx.is_constructor(sym.name())?;
                let mut parts = Vec::with_capacity(args.len());
                for &arg in args {
                    let sort = self.ctx.terms.sort(arg).clone();
                    let part = if self.datatype_sort_name(&sort).is_some() {
                        self.structural_dt_table_key(model, arg, depth - 1)?
                    } else {
                        self.term_value_string(model, arg).ok()?
                    };
                    parts.push(part);
                }
                let surface = self.dt_value_head(&ctor);
                Some(if parts.is_empty() {
                    surface.into_owned()
                } else {
                    format!("({} {})", surface, parts.join(" "))
                })
            }
            _ => self
                .dt_egraph_value(model, term)
                .or_else(|| self.term_value_string(model, term).ok()),
        }
    }

    /// Project selector `sel` from the structural rendering of `operand`:
    /// when that rendering is a constructor application of the ctor owning
    /// `sel`, return its corresponding top-level field rendering verbatim,
    /// the fields as `ay_core::smtlib_application_parts` splits them.
    fn structural_dt_selector_projection(
        &self,
        model: &Model,
        sel: &str,
        operand: TermId,
        depth: u32,
    ) -> Option<String> {
        let (owner, idx) = self
            .ctx
            .ctor_selectors_iter()
            .find_map(|(ctor, selectors)| {
                selectors
                    .iter()
                    .position(|candidate| candidate == sel)
                    .map(|idx| (ctor.clone(), idx))
            })?;
        let rendered = self.structural_dt_table_key(model, operand, depth.checked_sub(1)?)?;
        let (head, args) = ay_core::smtlib_application_parts(&rendered)?;
        if self.dt_value_head(&owner) != head && owner.as_str() != head {
            return None;
        }
        args.get(idx).map(|field| (*field).to_string())
    }

    /// The EXACT row list `format_function_table` turns into the printed
    /// `(define-fun f ...)` body: phantom rows dropped, `@?N` placeholders
    /// resolved, first-match duplicates removed. Split out of
    /// `format_function_table` (which is its only former body) so the
    /// independent model gate can evaluate the SAME total interpretation the
    /// printer emits instead of re-deriving one — see
    /// `IndependentModelView::printed_uf_interpretation_value`
    /// (#g3-gate-reads-printed-uf).
    ///
    /// The emitted body is a FIRST-MATCH `ite` chain over these rows with the
    /// LAST row's value as the `else` branch (see `format_function_body`), so
    /// this list plus that rule is the whole printed interpretation.
    pub(in crate::executor) fn printed_uf_table_rows(
        &self,
        name: &str,
        arg_sorts: &[Sort],
        result_sort: &Sort,
        table: &[(Vec<String>, String)],
        model: &Model,
    ) -> Result<Vec<(Vec<String>, String)>, PrintedUfTableRowsError> {
        // Resolve @?N placeholders in table entries (#5452).
        let mut resolved_table: Vec<(Vec<String>, String)> = Vec::with_capacity(table.len());
        for (args, result) in table {
            // Quantifier-PHANTOM row skip: EUF model extraction sweeps every
            // e-graph application into the table, including NON-GROUND ones
            // from inside a quantifier body (e.g. `f(x_0)` for binder `x_0`).
            // Such a row denotes the function at a SYMBOLIC point, not a
            // concrete one — it is not part of any model — and, because the
            // ground lane only ever constrains the renamed instantiation
            // copies (`f(__ce_x_0)`, `f(3)`, ...), it is also the one row
            // that can have no theory value at all (first user-visible with
            // Real codomains, where no LIA blanket assignment covers it).
            // Dropping it is NOT value fabrication (#no-fabricated-model-
            // values): the row never corresponded to a committed model point.
            // Deliberately narrow — the row is skipped ONLY when an entry
            // (result OR argument: for a REAL-sorted binder the ARG `x_0`
            // itself is the unresolvable placeholder, since no blanket
            // theory assignment covers a Real bound variable) BOTH resolves
            // to no value anywhere AND mentions a quantifier-bound variable;
            // every other unresolvable placeholder still surfaces the
            // command-level error exactly as before.
            if self.table_entry_is_quantifier_phantom(result, model)
                || args
                    .iter()
                    .any(|a| self.table_entry_is_quantifier_phantom(a, model))
            {
                continue;
            }
            let mut resolved_args: Vec<String> = Vec::with_capacity(args.len());
            for (i, arg) in args.iter().enumerate() {
                let sort = arg_sorts.get(i).cloned().unwrap_or(Sort::Bool);
                resolved_args.push(
                    self.resolve_table_value(arg, &sort, model)
                        .map_err(PrintedUfTableRowsError::Coverage)?,
                );
            }
            let resolved_result = self
                .resolve_table_value(result, result_sort, model)
                .map_err(PrintedUfTableRowsError::Coverage)?;
            resolved_table.push((resolved_args, resolved_result));
        }

        // Authored-point completion (#dt-uf-table-authored-points): an EUF
        // extraction table keys only the applications its own round saw, so
        // a datatype-sorted application the authored assertions apply the
        // function at — typically under a composite argument (`(f (ite
        // ...))`, `(f (sel x))`) whose point the round's residual never
        // registered — can be missing from the table entirely. The printed
        // body then answers its `else` there while the model's pin for
        // that application says otherwise: an incoherent published
        // witness (Certora `65782_..._6_QF_UFDTBV`, assertion on
        // `(x76 (ite ...))`, validated against the printed body in z3).
        // Complete the table from the same authored-application census
        // the no-table fallback uses, keyed and valued by the model's own
        // term evaluation, so printer and gate read one coherent body.
        // Scoped and fail-soft: only datatype-argument tables (the
        // measured class), only when an `else` row already exists, only
        // points not already present (the `else` row's ignored key
        // included — that point already reads as the `else` value), and
        // any point that does not resolve is skipped, leaving today's
        // adjudication untouched. The backstop below still rejects a
        // completed table that is not a function.
        if !resolved_table.is_empty()
            && arg_sorts
                .iter()
                .any(|sort| self.datatype_sort_name(sort).is_some())
            && !self.uf_symbol_occurs_under_quantifier(name)
        {
            let applications = self.uf_authored_applications();
            if let Some(apps) = applications.get(&(name.to_string(), arg_sorts.len())) {
                // Coverage short-circuits: when the table already carries
                // at least as many points as there are authored
                // applications, every authored point is already present
                // up to rendering; and when no authored argument is
                // composite (an `ite`/constructor/selector-headed term —
                // the only shape whose point an extraction round can
                // miss, since plain variable/constant arguments are
                // keyed by extraction itself), there is nothing to
                // complete. Either way the per-application key
                // evaluations below (the hot path on assertion-heavy
                // files) cannot add anything.
                let any_composite_arg = apps.iter().any(|(_, args)| {
                    args.iter().any(|&arg| {
                        self.datatype_sort_name(self.ctx.terms.sort(arg)).is_some()
                            && matches!(
                                self.ctx.terms.get(arg),
                                TermData::App(..) | TermData::Ite(..)
                            )
                    })
                });
                let additions: Vec<(Vec<String>, String)> = if !any_composite_arg
                    || resolved_table.len().saturating_sub(1) >= apps.len()
                {
                    Vec::new()
                } else {
                    let present: HashSet<&Vec<String>> =
                        resolved_table.iter().map(|(args, _)| args).collect();
                    let mut additions: Vec<(Vec<String>, String)> = Vec::new();
                    // Applications share argument terms heavily; memoize
                    // each term's key rendering within this call.
                    let mut key_memo: HashMap<TermId, Option<String>> = HashMap::default();
                    for (app, args) in apps {
                        let mut key = Vec::with_capacity(args.len());
                        let mut resolvable = true;
                        for &arg in args {
                            // Datatype arguments key by their STRUCTURAL
                            // value (the value the gate's evaluator
                            // computes for the same term), not by the
                            // producer's class rendering: for a composite
                            // argument (`(ite ...)`, a constructor over
                            // selector applications) the class rendering
                            // is an abstract tree the gate never looks
                            // up, which is exactly how the `65782` points
                            // went missing.
                            let rendered = key_memo
                                .entry(arg)
                                .or_insert_with(|| {
                                    if self.datatype_sort_name(self.ctx.terms.sort(arg)).is_some() {
                                        self.structural_dt_table_key(model, arg, 64)
                                    } else {
                                        None
                                    }
                                    .or_else(|| self.term_value_string(model, arg).ok())
                                })
                                .clone();
                            match rendered {
                                Some(rendered) => key.push(rendered),
                                None => {
                                    resolvable = false;
                                    break;
                                }
                            }
                        }
                        if resolvable && !present.contains(&key) {
                            if let Ok(value) = self.term_value_string(model, *app) {
                                additions.push((key, value));
                            }
                        }
                    }
                    additions
                };
                if !additions.is_empty() {
                    let else_row = resolved_table.pop().expect("non-empty table checked above");
                    resolved_table.extend(additions);
                    resolved_table.push(else_row);
                }
            }
        }

        // Print backstop (#uf-one-int-lane): the emitted body is a FIRST-MATCH
        // ite chain, so a later row whose argument point was already seen is
        // dead code. Two rows can land on one point when distinct source
        // applications share final argument values (congruent applications).
        // Equal results: the duplicate is harmless — drop it. CONFLICTING
        // results: the resolved table is not a function, and printing it would
        // emit a model whose first-match value contradicts the interpretation
        // the solver validated (the U4_rand_24 wrong-printed-model class). The
        // upstream lane-unification (combined_solvers/models.rs) makes this
        // never trigger on a validated model; if it ever does, fail closed with
        // an explicit error rather than emit a falsifying witness.
        let mut seen_points: HashMap<Vec<String>, String> = HashMap::new();
        let mut deduped: Vec<(Vec<String>, String)> = Vec::with_capacity(resolved_table.len());
        for (args, result) in resolved_table {
            match seen_points.get(&args) {
                Some(prev) if *prev == result => continue,
                Some(prev) => {
                    return Err(PrintedUfTableRowsError::InconsistentFunctionTable {
                        name: name.to_string(),
                        point: args,
                        first: prev.clone(),
                        second: result,
                    });
                }
                None => {
                    seen_points.insert(args.clone(), result.clone());
                    deduped.push((args, result));
                }
            }
        }
        // CONSTANT ABSORPTION. The rows above have pairwise-distinct argument
        // points and the printed body is a first-match `ite` chain whose LAST
        // row supplies the `else` branch, so when every row resolves to the
        // same value the chain IS that constant: keeping one row prints the
        // bare value (`format_function_body`'s single-entry case) and denotes
        // exactly the same total function. This is not a simplification for
        // looks. A guarded binder expands to one row per point — 65 of them for
        // `(forall ((i (_ BitVec 64))) (=> (bvult i (_ bv65 64)) (= (f i) #b1)))`
        // — and the resulting 64-deep `ite` puts its innermost condition
        // arguments at depth 65, past the `MAX_DEPTH` of 64 that the typed
        // scalar-function decoder enforces, so the honest total interpretation
        // would be published and then refused on read-back.
        if deduped.len() > 1 {
            let (_, first) = &deduped[0];
            if deduped.iter().all(|(_, result)| result == first) {
                deduped.truncate(1);
            }
        }
        Ok(deduped)
    }

    /// Format an exact certificate-constructed total function whose default
    /// is stored explicitly rather than encoded as the last raw EUF row.
    ///
    /// `rows` and `default` were type-checked and rendered atomically when the
    /// typed interpretation was installed.  Preserve every exception row and
    /// use the proved default directly; choosing one row as an implicit else
    /// would publish a different function on unlisted points.
    pub(super) fn format_certified_total_function(
        &self,
        name: &str,
        arg_sorts: &[Sort],
        result_sort: &Sort,
        rows: &[(Vec<String>, String)],
        default: &str,
    ) -> Result<String, String> {
        let names = self.model_formal_names("x", arg_sorts.len());
        let parameters = self.format_model_parameters(&names, arg_sorts);
        let mut seen: HashMap<Vec<String>, String> = HashMap::new();
        let mut deduped: Vec<(Vec<String>, String)> = Vec::with_capacity(rows.len());
        for (args, value) in rows {
            if args.len() != arg_sorts.len() {
                return Err(format!(
                    "certified total function {} has row arity {}, expected {}",
                    quote_symbol(name),
                    args.len(),
                    arg_sorts.len()
                ));
            }
            match seen.get(args) {
                Some(previous) if previous == value => continue,
                Some(previous) => {
                    return Err(format!(
                        "inconsistent certified total function {} at ({}) resolves to both {} and {}",
                        quote_symbol(name),
                        args.join(" "),
                        previous,
                        value
                    ));
                }
                None => {
                    seen.insert(args.clone(), value.clone());
                    deduped.push((args.clone(), value.clone()));
                }
            }
        }

        let mut body = default.to_string();
        // A row equal to the default adds no branch to the printed function.
        // Validate every row above so an inconsistent key still fails.
        for (args, value) in deduped.iter().rev().filter(|(_, value)| value != default) {
            let conditions: Vec<String> = args
                .iter()
                .zip(&names)
                .map(|(arg, name)| format!("(= {name} {arg})"))
                .collect();
            let condition = if conditions.len() == 1 {
                conditions[0].clone()
            } else {
                format!("(and {})", conditions.join(" "))
            };
            body = format!("(ite {condition} {value} {body})");
        }
        Ok(format!(
            "  (define-fun {} ({}) {}\n    {})",
            quote_symbol(name),
            parameters,
            format_sort_surface(&self.ctx, result_sort),
            body
        ))
    }

    /// Resolve a raw function table value, replacing `@?N` placeholders with
    /// concrete values from theory models (#5452).
    ///
    /// EUF model extraction generates `@?N` for Int/Real/BV-sorted terms that
    /// are not in `term_values` (which only covers Uninterpreted sorts). This
    /// method parses the term ID and evaluates it against the full model.
    /// A placeholder whose term has NO value in the model is an `Err` — the
    /// former sort-default fallback fabricated user-visible values
    /// (#no-fabricated-model-values).
    pub(super) fn resolve_table_value(
        &self,
        raw: &str,
        sort: &Sort,
        model: &Model,
    ) -> Result<String, String> {
        if let Some(id_str) = raw.strip_prefix("@?") {
            if let Ok(id) = id_str.parse::<u32>() {
                let term_id = TermId(id);
                // Array-sorted function-table entries (e.g. the argument of an
                // uninterpreted function over a collection domain — choose/pick
                // over a Set/Map/Multiset, whose value is `(Array elem cnt)`)
                // cannot be rendered by the scalar evaluator: `EvalValue` has no
                // Array variant, so `evaluate_term` returns `Unknown` and the
                // whole `(get-model)` errors. Route them through the SAME
                // store-chain witness renderer `(define-fun a ...)` and
                // `(get-value (a))` already use for array-sorted terms — a
                // model-derived interpretation consistent with the asserted
                // `(select a i)=v` constraints (legitimate completion of the
                // unconstrained cells, NOT a fabricated value; the array
                // *variable* path already renders this way, so this only closes
                // the function-table-argument asymmetry). Purely model OUTPUT —
                // cannot affect any SAT/UNSAT decision.
                if matches!(sort, Sort::Array(_)) {
                    return self
                        .format_array_witness_value(model, term_id, sort)
                        .ok_or_else(|| {
                            format!(
                                "no complete array model value for function-table entry of sort {}",
                                format_sort_surface(&self.ctx, sort)
                            )
                        });
                }
                // An application the solved formula no longer contains (a
                // preprocessing substitution eliminated it) keeps the value a
                // top-level asserted equality gives it: `(= (h x) (- x 3))`
                // with `h` Real-ranged had no theory value, and the whole
                // `(get-model)` failed ("no model value for function-table
                // entry of sort Real") although the gates validated the model.
                let eval = match self.evaluate_term(model, term_id) {
                    EvalValue::Unknown => self
                        .extract_value_from_asserted_equalities(model, term_id)
                        .unwrap_or(EvalValue::Unknown),
                    value => value,
                };
                if !matches!(eval, EvalValue::Unknown) {
                    // USER-FACING table position (#real-fmt): the DECLARED
                    // param/result sort is authoritative — an Int-sorted
                    // numeral argument at a Real-sorted parameter still
                    // prints in the Real spelling, exactly like z3.
                    if matches!(sort, Sort::Real) {
                        if let Some(s) = eval_value_real_string(&eval) {
                            return Ok(s);
                        }
                    }
                    return self.try_format_eval_value_user(&eval, term_id);
                }
                return Err(format!(
                    "no model value for function-table entry of sort {}",
                    format_sort_surface(&self.ctx, sort)
                ));
            }
        }
        if raw.starts_with('@') {
            if matches!(sort, Sort::Seq(_)) {
                return Err(format!(
                    "opaque internal equality-class value {raw} is not a concrete sequence"
                ));
            }
            // RoundingMode has five values; `rm_concrete.rs` replaces every
            // minted element before completion, so one here is a gap.
            if crate::executor::rm_domain::is_rm_sort(sort) {
                return Err(format!("internal element {raw} is not a rounding mode"));
            }
            // Abstract element token (`@Sort!n`) of an uninterpreted sort:
            // sort-ascribe it exactly like every other printed occurrence
            // (#mv-abstract-value-ascription). Scalar sorts pass through
            // unchanged.
            return Ok(format_model_atom_surface(&self.ctx, sort, raw));
        }
        Ok(smtlib_arith_table_literal(raw, sort).unwrap_or_else(|| raw.to_string()))
    }

    /// True when a raw function-table entry (RESULT or ARGUMENT) marks a
    /// quantifier-phantom row: an `@?N` placeholder whose term (a) has no
    /// value in any theory model and (b) mentions a variable that is not a
    /// user-visible model point — either one bound by a quantifier in the
    /// current assertion set (a NON-GROUND body occurrence swept into the
    /// EUF table, e.g. the result `f(x_0)` or the bound variable `x_0`
    /// itself as an argument) or a solver-internal UNDECLARED variable (a
    /// refinement-machinery skolem such as the CEGQI counterexample constant
    /// `__ce_x_0`, whose theory assignment was rolled back with its CE
    /// round). Neither denotes a committed model point. See the caller in
    /// [`Self::format_function_table`] for why dropping such a row is not
    /// value fabrication.
    pub(super) fn table_entry_is_quantifier_phantom(&self, raw_entry: &str, model: &Model) -> bool {
        let Some(id_str) = raw_entry.strip_prefix("@?") else {
            return false;
        };
        let Ok(id) = id_str.parse::<u32>() else {
            return false;
        };
        let term_id = TermId(id);
        // An entry that resolves to a value NEVER drops its row.
        if !matches!(self.evaluate_term(model, term_id), EvalValue::Unknown) {
            return false;
        }
        if self.term_mentions_undeclared_var(term_id) {
            return true;
        }
        let binders = self.quantifier_binder_names();
        if !binders.is_empty() && self.term_mentions_named_var(term_id, &binders) {
            return true;
        }
        // A term that occurs in no current assertion and no assumption of the
        // last check constrains nothing: the e-graph can hold it because the
        // term store does (a Z3 C API context builds terms it never asserts,
        // e.g. `h(a)` for a Real-ranged `h`, and a `(= (h a) (h a))` folds to
        // `true` while `(h a)` stays registered). Its row is not a model point
        // either; without this the whole model failed to print ("no model
        // value for function-table entry of sort Real") and the API published
        // `sat` with an EMPTY model.
        !self.term_occurs_in_current_query(term_id)
    }

    /// True when `t` is a subterm of a current assertion or of an assumption
    /// of the last check. Cold path: only consulted for table entries that
    /// already resolve to no model value.
    fn term_occurs_in_current_query(&self, t: TermId) -> bool {
        let mut visited: HashSet<TermId> = HashSet::default();
        let mut stack: Vec<TermId> = self.ctx.assertions.clone();
        stack.extend(self.last_assumptions.iter().flatten().copied());
        while let Some(u) = stack.pop() {
            if u == t {
                return true;
            }
            if !visited.insert(u) {
                continue;
            }
            match self.ctx.terms.get(u) {
                TermData::App(_, args) => stack.extend(args.iter().copied()),
                TermData::Not(i) => stack.push(*i),
                TermData::Ite(c, a, b) => {
                    stack.push(*c);
                    stack.push(*a);
                    stack.push(*b);
                }
                TermData::Let(bindings, b) => {
                    for (_, v) in bindings {
                        stack.push(*v);
                    }
                    stack.push(*b);
                }
                TermData::Forall(_, b, triggers) | TermData::Exists(_, b, triggers) => {
                    stack.push(*b);
                    stack.extend(triggers.iter().flatten().copied());
                }
                _ => {}
            }
        }
        false
    }

    /// True when `t` mentions a `Var` whose name is not a declared symbol —
    /// a solver-internal variable (quantifier binder copy, CEGQI skolem,
    /// probe constant). Cold path: only consulted for entries that already
    /// resolve to no model value.
    fn term_mentions_undeclared_var(&self, t: TermId) -> bool {
        let mut visited: HashSet<TermId> = HashSet::default();
        let mut stack = vec![t];
        while let Some(u) = stack.pop() {
            if !visited.insert(u) {
                continue;
            }
            match self.ctx.terms.get(u) {
                TermData::Var(n, _) => {
                    if self.ctx.symbol_info_by_identity(n).is_none()
                        && self.ctx.exact_datatype_member_info(n).is_none()
                    {
                        return true;
                    }
                }
                TermData::App(_, args) => stack.extend(args.iter().copied()),
                TermData::Not(i) => stack.push(*i),
                TermData::Ite(c, a, b) => {
                    stack.push(*c);
                    stack.push(*a);
                    stack.push(*b);
                }
                TermData::Let(bindings, b) => {
                    for (_, v) in bindings {
                        stack.push(*v);
                    }
                    stack.push(*b);
                }
                TermData::Forall(_, b, _) | TermData::Exists(_, b, _) => stack.push(*b),
                _ => {}
            }
        }
        false
    }

    /// Collect every variable name bound by a quantifier anywhere in the TERM
    /// STORE. The store (not just the current assertion set) is scanned
    /// because the quantifier pipeline alpha-renames binder copies per round
    /// (`x_0`, `x_2`, ...): the restored original assertions only bind the
    /// first name, while the phantom table rows reference the renamed copies.
    /// Only reached when a table row is already unresolvable (rare), so the
    /// linear store scan is not on any hot path.
    fn quantifier_binder_names(&self) -> HashSet<String> {
        let mut names: HashSet<String> = HashSet::default();
        for t in self.ctx.terms.term_ids() {
            if let TermData::Forall(vars, _, _) | TermData::Exists(vars, _, _) =
                self.ctx.terms.get(t)
            {
                for (n, _) in vars {
                    names.insert(n.clone());
                }
            }
        }
        names
    }

    /// True when `t` mentions a `Var` whose name is in `names`.
    fn term_mentions_named_var(&self, t: TermId, names: &HashSet<String>) -> bool {
        let mut visited: HashSet<TermId> = HashSet::default();
        let mut stack = vec![t];
        while let Some(u) = stack.pop() {
            if !visited.insert(u) {
                continue;
            }
            match self.ctx.terms.get(u) {
                TermData::Var(n, _) => {
                    if names.contains(n) {
                        return true;
                    }
                }
                TermData::App(_, args) => stack.extend(args.iter().copied()),
                TermData::Not(i) => stack.push(*i),
                TermData::Ite(c, a, b) => {
                    stack.push(*c);
                    stack.push(*a);
                    stack.push(*b);
                }
                TermData::Let(bindings, b) => {
                    for (_, v) in bindings {
                        stack.push(*v);
                    }
                    stack.push(*b);
                }
                TermData::Forall(_, b, _) | TermData::Exists(_, b, _) => stack.push(*b),
                _ => {}
            }
        }
        false
    }

    /// Build nested ite expression for function table.
    fn format_function_body(
        &self,
        names: &[String],
        result_sort: &Sort,
        table: &[(Vec<String>, String)],
    ) -> String {
        if table.is_empty() {
            // Unreachable in practice (the caller special-cases the empty
            // table); kept total with the same unconstrained-function body.
            return self.default_value_surface(result_sort);
        }

        // Use last entry as the default (else branch).
        let (_, default_result) = table.last().expect("non-empty checked above");

        if table.len() == 1 {
            // Single entry - just return the result.
            return default_result.clone();
        }

        // Build nested ite from all entries except last (which becomes the else).
        let mut result = default_result.clone();

        for (args, value) in table.iter().rev().skip(1) {
            // Build condition: (and (= x0 arg0) (= x1 arg1) ...).
            let conditions: Vec<String> = args
                .iter()
                .zip(names)
                .map(|(arg, name)| format!("(= {name} {arg})"))
                .collect();

            let condition = if conditions.len() == 1 {
                conditions[0].clone()
            } else {
                format!("(and {})", conditions.join(" "))
            };

            result = format!("(ite {condition} {value} {result})");
        }

        result
    }

    /// Format an array value from `ArrayInterpretation` for model output.
    pub(super) fn format_array_value(
        &self,
        sort: &Sort,
        interp: &ay_arrays::ArrayInterpretation,
    ) -> Option<String> {
        let sort_str = format_sort_surface(&self.ctx, sort);

        // A partial interpretation has no honest total SMT value.  Completion
        // must commit an else value to `ArrayModel` before output; inventing one
        // here would let `(get-model)` disagree with validation and scalar
        // `select` evaluation.
        let default = interp.default.as_deref()?;
        // The interpretation holds datatype values in either spelling of
        // `dt_value_respelled`; each prints as its constructors' tokens.
        let printed = |text: &str, sort: &Sort| self.dt_value_printed(text, sort);
        let Sort::Array(array_sort) = sort else {
            let base = format!("((as const {sort_str}) {default})");
            return Some(format_newest_first_store_chain(base, &interp.stores));
        };
        let base = format!(
            "((as const {sort_str}) {})",
            printed(default, &array_sort.element_sort)
        );
        let stores: Vec<(String, String)> = interp
            .stores
            .iter()
            .map(|(index, value)| {
                (
                    printed(index, &array_sort.index_sort),
                    printed(value, &array_sort.element_sort),
                )
            })
            .collect();
        Some(format_newest_first_store_chain(base, &stores))
    }

    /// Format an evaluated array index/element value at `term_id`'s declared
    /// sort for use as a `store` index/value in a model witness.
    ///
    /// Unlike [`Self::format_eval_value`], which renders an integer-valued
    /// `Rational` as a bare numeral (e.g. `-18`) regardless of sort, this
    /// respects the term's sort so the literal round-trips: a Real-sorted point
    /// prints as a Real literal (`18.0`, `(- 18.0)`, `(/ a b)`) and a negative
    /// Int as `(- 18)`. Without this, a Real-element store value reparses at the
    /// wrong sort (or as invalid syntax) when the model is fed back (#model-array-witness).
    fn format_array_point_value(&self, value: &EvalValue, term_id: TermId) -> String {
        match value {
            EvalValue::Rational(r) => match self.ctx.terms.sort(term_id) {
                Sort::Real => format_rational(r),
                _ => format_bigint(r.numer()),
            },
            _ => self.format_eval_value(value, term_id),
        }
    }

    /// Printer spelling of an internal `@Sort!n` abstract atom when — and only
    /// when — it denotes a universe element of the given UNINTERPRETED sort:
    /// `@E!1` (bare internal dialect) or `(as @E!1 E)` (already ascribed) maps
    /// to the sort-ascribed output form `(as @E!1 E)`. Returns `None` for any
    /// other sort (datatype representatives, nested-array `@Arr!n` names,
    /// `RoundingMode`'s fixed domain) or any token that is not exactly an atom
    /// of THIS sort — callers then keep their skolem-free fallback
    /// (#model-witness-no-skolem, #qfax-universe-collapse).
    fn printable_uninterpreted_atom(&self, raw: &str, sort: &Sort) -> Option<String> {
        let Sort::Uninterpreted(sort_name) = sort else {
            return None;
        };
        // Declared datatypes use `Sort::Uninterpreted` internally too, but their
        // representatives are not values. `RoundingMode` likewise has a fixed domain.
        if self.datatype_sort_name(sort).is_some() || sort_name == "RoundingMode" {
            return None;
        }
        let bare = crate::executor_format::canonical_internal_atom(raw);
        // The QF_AX witness passes (cross-base chain completion, nested and
        // guard witnesses) mint `@ay!wit!<kind>!<n>` elements of the index and
        // element sorts. They are first-class model values exactly like
        // `@Sort!n`: the scalar printer already ascribes them (`(as
        // @ay!wit!xidx!1 I)`). Refusing them here dropped every such cell from
        // the printed array, and replaced a witness default by `@Sort!0`, so
        // the printed model was not the validated one (AY-N9: Dolmen
        // `bad-model` on a QF_AX swap instance).
        if crate::executor_format::is_internal_witness_atom(&bare) {
            return Some(format_model_atom_surface(&self.ctx, sort, &bare));
        }
        let index = bare.strip_prefix('@')?.strip_prefix(sort_name.as_str())?;
        let digits = index.strip_prefix('!')?;
        if digits.is_empty() || !digits.bytes().all(|b| b.is_ascii_digit()) {
            return None;
        }
        Some(format_model_atom_surface(&self.ctx, sort, &bare))
    }

    /// Upsert `(idx, val)` into an ordered store list: overwrite an existing
    /// entry at `idx`, else append. Keeps a single value per index.
    fn upsert_store(stores: &mut Vec<(String, String)>, idx: String, val: String) {
        // `array_witness_interp` uses oldest-first order so callers can fold
        // the vector directly into a store chain.  An overwrite is a NEWEST
        // write: remove the shadowed entry and append the replacement instead
        // of changing the value in its old chronological position.
        if let Some(position) = stores.iter().position(|(key, _)| *key == idx) {
            stores.remove(position);
        }
        stores.push((idx, val));
    }

    /// Whether a ground term occurs in the assertions/assumptions that own the
    /// last model.  The global term interner also contains popped, generated,
    /// and query-only select terms; those are not constraints and must not make
    /// otherwise-free array completion fail.
    ///
    /// Served from `required_terms_index`: the reachability closure is computed
    /// once and revalidated by a BYTE-EXACT `(assertions, assumptions)`
    /// snapshot compare per query — any change rebuilds, so a stale closure can
    /// never be consulted. Previously the full-forest DFS ran PER CANDIDATE
    /// READ during array completion (O(reads × forest), fresh hash-set churn
    /// each call — the dominant completion cost on the pairwise-expanded
    /// `distinct` family).
    pub(super) fn term_is_required_by_last_query(&self, needle: TermId) -> bool {
        let mut cache = self.required_terms_index.borrow_mut();
        let valid = cache.as_ref().is_some_and(|(asnap, usnap, _)| {
            *asnap == self.ctx.assertions && *usnap == self.last_assumptions
        });
        if !valid {
            // Reachability closure with the SAME traversal cutoffs as the
            // original per-call DFS: App/Not/Ite descend; Let/Forall/Exists do
            // not (bound observations do not name ground model cells). The set
            // holds every VISITED term — exactly the terms the original walk
            // compared against `needle`.
            let mut seen = HashSet::default();
            let mut stack = self.ctx.assertions.clone();
            stack.extend(self.last_assumptions.iter().flatten().copied());
            while let Some(term) = stack.pop() {
                if !seen.insert(term) {
                    continue;
                }
                match self.ctx.terms.get(term) {
                    TermData::App(_, args) => stack.extend(args.iter().copied()),
                    TermData::Not(inner) => stack.push(*inner),
                    TermData::Ite(condition, then_term, else_term) => {
                        stack.extend([*condition, *then_term, *else_term]);
                    }
                    TermData::Let(_, _) | TermData::Forall(_, _, _) | TermData::Exists(_, _, _) => {
                    }
                    _ => {}
                }
            }
            *cache = Some((
                self.ctx.assertions.clone(),
                self.last_assumptions.clone(),
                seen,
            ));
        }
        cache
            .as_ref()
            .expect("required_terms_index populated above")
            .2
            .contains(&needle)
    }

    /// Store-axiom-consistent witness interpretation of an array-sorted term:
    /// `(default_element, ordered (index, element) stores)`, where each element
    /// string is fully rendered (recursively a `store`-chain for nested array
    /// element sorts).
    ///
    /// Backs BOTH `(get-model)` array rendering and the `(get-value)`/`(eval)`
    /// `select` read, so the two never diverge (#model-array-witness). The store
    /// axiom is applied structurally: `store(base, i, v)` INHERITS `base`'s
    /// default (NOT `v`) with `i -> v` overridden — fixing the wrong-default
    /// witness where a store-equality-dependent array `b = (store a i v)` adopted
    /// the stored value (or a stale don't-care `select(b, j)`) instead of `a`'s
    /// default. A nested array element is itself rendered through this same
    /// interpretation, so the outer default reflects the inner constraints.
    fn array_witness_interp(
        &self,
        model: &Model,
        array_term: TermId,
        elem_sort: &Sort,
        def_visited: &mut HashSet<TermId>,
    ) -> Option<(String, Vec<(String, String)>)> {
        self.array_witness_interp_inner(
            model,
            array_term,
            elem_sort,
            def_visited,
            ArrayInterpMode::Strict,
            None,
        )
    }

    /// Build a candidate interpretation for model completion.  Unlike the
    /// strict output wrapper above, this may choose the element sort's
    /// canonical value for a genuinely missing, non-conflicted base default
    /// (and, in `CompleteSkipUnknownReads` mode, skip Unknown-valued active
    /// reads — see [`ArrayInterpMode`]).  The caller must commit the candidate
    /// before validation or output uses it; this keeps completion policy out
    /// of the printer.
    pub(super) fn array_completion_candidate_interp(
        &self,
        model: &Model,
        array_term: TermId,
        elem_sort: &Sort,
        mode: ArrayInterpMode,
        authenticated_dt_cells: Option<&AuthenticatedDatatypeArrayMembers>,
    ) -> Option<(String, Vec<(String, String)>)> {
        debug_assert!(
            mode.completes_missing_default(),
            "completion candidates must use a completion mode"
        );
        let mut def_visited = HashSet::default();
        let (default, stores) = self.array_witness_interp_inner(
            model,
            array_term,
            elem_sort,
            &mut def_visited,
            mode,
            authenticated_dt_cells,
        )?;
        // INTERNAL-DIALECT NORMALIZATION (#qfax-atom-spelling): this candidate
        // is installed into the model that internal evaluators, the completion
        // merge, and the independent gate all consume by STRING identity. The
        // witness builder formats cells with the PRINTER's sort-ascribed
        // abstract-atom spelling (`(as @Sort!n S)`), while extraction / the
        // cross-base witness pass write the bare `@Sort!n` token — the same
        // logical value under two spellings then merges as TWO distinct cells,
        // and the phantom cell falsifies a genuinely-valid witness at the
        // independent gate (QF_AX storeinv/storecomm fail-close). Map to the
        // bare internal dialect at this single write boundary; printing
        // re-ascribes at the output boundary as before.
        let default = crate::executor_format::canonical_internal_atom(&default);
        let stores = stores
            .into_iter()
            .map(|(k, v)| {
                (
                    crate::executor_format::canonical_internal_atom(&k),
                    crate::executor_format::canonical_internal_atom(&v),
                )
            })
            .collect();
        Some((default, stores))
    }

    fn array_witness_interp_inner(
        &self,
        model: &Model,
        array_term: TermId,
        elem_sort: &Sort,
        def_visited: &mut HashSet<TermId>,
        mode: ArrayInterpMode,
        authenticated_dt_cells: Option<&AuthenticatedDatatypeArrayMembers>,
    ) -> Option<(String, Vec<(String, String)>)> {
        stacker::maybe_grow(ARRAY_FMT_STACK_RED_ZONE, ARRAY_FMT_STACK_SIZE, || {
            if model
                .array_model
                .as_ref()
                .is_some_and(|arrays| arrays.is_withheld(&array_term))
            {
                return None;
            }
            match self.ctx.terms.get(array_term) {
                TermData::App(sym, args) if sym.name() == "store" && args.len() == 3 => {
                    let (default, mut stores) = self.array_witness_interp_inner(
                        model,
                        args[0],
                        elem_sort,
                        def_visited,
                        mode,
                        authenticated_dt_cells,
                    )?;
                    let idx_str =
                        self.format_array_index_value(model, args[1], def_visited, mode)?;
                    let val_str = self.format_array_element_value(
                        model,
                        args[2],
                        elem_sort,
                        def_visited,
                        mode,
                    )?;
                    Self::upsert_store(&mut stores, idx_str, val_str);
                    Some((default, stores))
                }
                TermData::App(sym, args) if sym.name() == "const-array" && args.len() == 1 => {
                    Some((
                        self.format_array_element_value(
                            model,
                            args[0],
                            elem_sort,
                            def_visited,
                            mode,
                        )?,
                        Vec::new(),
                    ))
                }
                TermData::Let(bindings, body) if bindings.is_empty() => self
                    .array_witness_interp_inner(
                        model,
                        *body,
                        elem_sort,
                        def_visited,
                        mode,
                        authenticated_dt_cells,
                    ),
                TermData::Let(_, _) if mode.completes_missing_default() => None,
                TermData::Let(_, _) => self.array_witness_base_interp(
                    model,
                    array_term,
                    elem_sort,
                    def_visited,
                    mode,
                    authenticated_dt_cells,
                ),
                TermData::Ite(cond, then_br, else_br) => match self.evaluate_term(model, *cond) {
                    EvalValue::Bool(true) => self.array_witness_interp_inner(
                        model,
                        *then_br,
                        elem_sort,
                        def_visited,
                        mode,
                        authenticated_dt_cells,
                    ),
                    EvalValue::Bool(false) => self.array_witness_interp_inner(
                        model,
                        *else_br,
                        elem_sort,
                        def_visited,
                        mode,
                        authenticated_dt_cells,
                    ),
                    // An unresolved branch condition does not identify one
                    // array value.  In particular, model completion must not
                    // replace an unknown ITE with a canonical base array.
                    _ if mode.completes_missing_default() => None,
                    _ => self.array_witness_base_interp(
                        model,
                        array_term,
                        elem_sort,
                        def_visited,
                        mode,
                        authenticated_dt_cells,
                    ),
                },
                // An array-valued read is itself a base array value.  Its
                // scalar/nested observations (for example
                // `select(select(a, 0), 0) = 1`) are collected recursively by
                // `array_witness_base_interp`.  Treating every `select` as an
                // unsupported array constructor made all nested-array models
                // permanently partial even when every observed cell was
                // concrete.  This holds in every `ArrayInterpMode`: completion
                // candidates (including the gate-verified skip pass) are only
                // committed if re-validation confirms the whole model, and an
                // inner cell that actually matters falsifies that check and
                // retracts (see `ArrayInterpMode`).
                TermData::App(sym, args)
                    if sym.name() == "select"
                        && args.len() == 2
                        && matches!(self.ctx.terms.sort(array_term), Sort::Array(_)) =>
                {
                    self.array_witness_base_interp(
                        model,
                        array_term,
                        elem_sort,
                        def_visited,
                        mode,
                        authenticated_dt_cells,
                    )
                }
                TermData::Var(_, _) => {
                    // Reached again through its own definition (`(= a (store a
                    // i v))`): the inner occurrence denotes the array's own
                    // value, which is its model interpretation. Refusing here
                    // left a self-referential array without a printable value
                    // on a validated `sat` (`(error "model value for array a0
                    // is not available")`). The expansion is checked against
                    // the validated value by the printed-array-witness gate.
                    // Completion keeps refusing: it must not build a candidate
                    // from the interpretation it is about to replace.
                    if def_visited.contains(&array_term) {
                        if mode.completes_missing_default() {
                            return None;
                        }
                        return self.array_witness_base_interp(
                            model,
                            array_term,
                            elem_sort,
                            def_visited,
                            mode,
                            authenticated_dt_cells,
                        );
                    }
                    // A store/const definitional equality `(= a <store-chain>)` is
                    // authoritative and store-axiom-correct, so resolve it first
                    // — this gives the correct default for a derived array. The
                    // `def_visited` insert breaks definitional cycles.
                    if let Some(def) =
                        self.array_variable_definition_excluding(array_term, def_visited)
                    {
                        if def != array_term && def_visited.insert(array_term) {
                            return self.array_witness_interp_inner(
                                model,
                                def,
                                elem_sort,
                                def_visited,
                                mode,
                                authenticated_dt_cells,
                            );
                        }
                    }
                    self.array_witness_base_interp(
                        model,
                        array_term,
                        elem_sort,
                        def_visited,
                        mode,
                        authenticated_dt_cells,
                    )
                }
                TermData::App(sym, args)
                    if mode.completes_missing_default()
                        && self.array_completion_application_is_base_leaf(
                            sym,
                            args,
                            array_term,
                            elem_sort,
                            authenticated_dt_cells,
                        ) =>
                {
                    self.array_witness_base_interp(
                        model,
                        array_term,
                        elem_sort,
                        def_visited,
                        mode,
                        authenticated_dt_cells,
                    )
                }
                _ if mode.completes_missing_default() => None,
                _ => self.array_witness_base_interp(
                    model,
                    array_term,
                    elem_sort,
                    def_visited,
                    mode,
                    authenticated_dt_cells,
                ),
            }
        })
    }

    /// Whether an array-valued application may be completed as a free base leaf.
    ///
    /// A user-declared function application is a leaf, unlike lambda, as-array,
    /// map, and future array constructors. This distinction is needed for values
    /// such as `(seq_array current)`: refusing a default made the independent gate
    /// unevaluable even though the declaration leaves the array unconstrained.
    ///
    /// Datatype selectors are not normally free leaves. Their result is fixed by
    /// the subject value, and completing congruent reads independently can invent
    /// incompatible field arrays. The sole exception is an exact selector whose W6
    /// capability proves the relevant datatype-cell set is empty; then the field is
    /// genuinely unobserved completion slack. A nonempty or withheld capability
    /// remains fail closed.
    fn array_completion_application_is_base_leaf(
        &self,
        symbol: &Symbol,
        args: &[TermId],
        result: TermId,
        element_sort: &Sort,
        authenticated_dt_cells: Option<&AuthenticatedDatatypeArrayMembers>,
    ) -> bool {
        self.ctx.symbol_info_by_identity(symbol.name()).is_some()
            && (!self.is_datatype_selector_symbol(symbol.name())
                || (self.is_exact_datatype_selector_application(symbol, args, result)
                    && self.datatype_sort_carries_array_field(element_sort)
                    && authenticated_dt_cells.is_some_and(|cells| cells.is_empty())))
    }

    /// Base (non-`store`-chain) interpretation of an array term: the
    /// reconstructed `ArrayInterpretation` default plus every directly
    /// constrained `select(array_term, i)` point (element-rendered, recursing for
    /// nested arrays). Constrained selects win; interpretation stores fill the
    /// remaining indices.
    fn array_witness_base_interp(
        &self,
        model: &Model,
        array_term: TermId,
        elem_sort: &Sort,
        def_visited: &mut HashSet<TermId>,
        mode: ArrayInterpMode,
        authenticated_dt_cells: Option<&AuthenticatedDatatypeArrayMembers>,
    ) -> Option<(String, Vec<(String, String)>)> {
        let interp = model
            .array_model
            .as_ref()
            .and_then(|am| am.array_values.get(&array_term));
        let read_conflicted = model
            .array_model
            .as_ref()
            .is_some_and(|am| am.is_withheld(&array_term));
        if read_conflicted {
            return None;
        }
        // The reconstructed default for a datatype (or datatype-nested) element
        // is an internal `@Sort!n` skolem — not a valid term. Drop any such
        // `@`-bearing default and fall back to a concrete canonical default,
        // recursing into element sorts (#model-witness-no-skolem).
        //
        // A genuinely ABSENT default (`None`) with `complete_missing_default`
        // is model completion of free slack; the choice is deferred until the
        // observed cells are collected below so a SCALAR-element array can
        // reuse an observed cell's value (folding a single-point array into a
        // plain const-array witness, #model-array-witness) instead of
        // inventing the canonical zero.
        // The interpretation holds datatype values in either spelling of
        // `dt_value_respelled`; the witness prints its constructors' tokens,
        // the spelling of the direct reads it merges below.
        let printed = |text: String, sort: &Sort| {
            self.dt_value_respelled(&text, sort, super::dt_model::DtSpelling::Printed)
                .unwrap_or(text)
        };
        let default = match interp.and_then(|i| i.default.clone()) {
            Some(default) if !default.contains('@') => Some(printed(default, elem_sort)),
            // An `@Sort!n` atom of an UNINTERPRETED sort is a first-class
            // model value: the printer sort-ascribes it (`(as @E!k E)`) and
            // the output header declares it, so it must be KEPT — collapsing
            // it to the canonical `@Sort!0` default silently rewrites the
            // committed model (#qfax-universe-collapse). Only a datatype (or
            // otherwise non-printable) representative falls back to the
            // concrete canonical repair below (#model-witness-no-skolem).
            Some(default) => Some(
                self.printable_uninterpreted_atom(&default, elem_sort)
                    .or_else(|| self.printable_rendered_array_value(&default, elem_sort))
                    .unwrap_or_else(|| self.canonical_default_value(elem_sort)),
            ),
            None if mode.completes_missing_default() => None,
            None => return None,
        };

        let mut stores: Vec<(String, String)> = Vec::new();
        // Directly constrained `select(array_term, i)` reads are authoritative.
        // Served by the prefix-extended reverse index (ascending id order,
        // identical to the former whole-term-store scan — which was
        // O(arrays × terms) across the completion pass).
        for tid in self.selects_of_array(array_term) {
            let TermData::App(_, args) = self.ctx.terms.get(tid) else {
                continue;
            };
            // The global interner also retains popped assertions, generated
            // terms, and prior get-value reads.  Once completion installs a
            // default those inactive reads become evaluable; treating them as
            // fresh store evidence makes a second completion pass grow new
            // default-valued points.  Only reads owned by the active solve are
            // semantic observations.  Existing solver stores are merged below.
            if !self.array_read_is_active(tid, authenticated_dt_cells) {
                continue;
            }
            // Datatype/array index keys are concretized to constructor terms
            // (never a skolem); a scalar key whose value is Unknown is skipped.
            let idx_sort = self.ctx.terms.sort(args[1]);
            let idx_str = if matches!(idx_sort, Sort::Array(_))
                || self.datatype_sort_name(idx_sort).is_some()
            {
                self.format_array_element_value(model, args[1], idx_sort, def_visited, mode)?
            } else {
                let idx_val = self.evaluate_term(model, args[1]);
                if matches!(idx_val, EvalValue::Unknown) {
                    // This term was discovered as a direct observation of the
                    // candidate array.  Dropping an ACTIVE unknown key silently
                    // can make the completed default claim authority at the
                    // very cell whose identity is unresolved.  An inactive
                    // interner entry is not model evidence.
                    return None;
                }
                self.format_array_point_value(&idx_val, args[1])
            };
            let val_str = if matches!(elem_sort, Sort::Array(_))
                || self.datatype_sort_name(elem_sort).is_some()
            {
                // Array- or datatype-valued select: render the element value
                // through the element renderer. A datatype `evaluate_term` is not
                // a scalar `EvalValue`, so the scalar path would (wrongly) drop
                // the constraint (e.g. `(select a 0) = (som 7)`, #model-array-witness).
                match self.format_array_element_value(model, tid, elem_sort, def_visited, mode) {
                    Some(value) => value,
                    // Unknown-valued active read at a NAMED cell: skip it in the
                    // gate-verified candidate pass (guarded-vacuous-read shape);
                    // the committed default is only accepted if re-validation
                    // confirms the completed model (see `ArrayInterpMode`).
                    None if mode.skips_unknown_active_reads() => continue,
                    None => return None,
                }
            } else {
                let value_val = match self.evaluate_term(model, tid) {
                    EvalValue::Unknown => self
                        .extract_value_from_asserted_equalities(model, tid)
                        .unwrap_or(EvalValue::Unknown),
                    value => value,
                };
                if matches!(value_val, EvalValue::Unknown) {
                    // Unknown-valued active read at a NAMED cell: the
                    // gate-verified candidate pass may skip it — a skipped read
                    // that actually constrains the cell falsifies re-validation
                    // and the whole candidate is retracted (see `ArrayInterpMode`).
                    //
                    // Pure QF_AX additionally has an authoritative fail-closed
                    // model gate, so ANY completion candidate may skip there:
                    // for a still-unpinned scalar read, use the candidate
                    // array's committed default and let that gate validate the
                    // completed model.  This is needed for positive read
                    // equalities such as `select b j = select a j`, where no
                    // scalar leaf supplies a value but one canonical choice is
                    // a genuine model.  Other logics retain the conservative
                    // partial-witness behavior below.
                    if mode.skips_unknown_active_reads()
                        || (mode.completes_missing_default() && self.ctx.logic() == Some("QF_AX"))
                    {
                        continue;
                    }
                    // A query-owned read that is no longer semantically
                    // observed — every containing conjunct already evaluates
                    // to true (e.g. a falsified ground-instantiation guard) —
                    // is not model evidence either: any element value keeps
                    // those conjuncts true, so skipping it lets the candidate
                    // claim only genuinely unconstrained cells
                    // (#array-decl-default-witness).  Strict output
                    // (`completes_missing_default()` false) keeps failing
                    // closed; completion commits the candidate first, after
                    // which the read resolves through the committed
                    // interpretation.
                    if mode.completes_missing_default()
                        && !self.array_read_is_semantic_observation(model, tid, &[])
                    {
                        continue;
                    }
                    // A direct read is model evidence, not an optional output
                    // decoration when it belongs to the current query.  If its
                    // active value is unknown, the array remains partial and
                    // cannot be safely totalized or printed as an exact witness.
                    return None;
                }
                self.format_array_point_value(&value_val, tid)
            };
            Self::upsert_store(&mut stores, idx_str, val_str);
        }
        // Reconstructed interpretation stores fill indices the selects missed.
        //
        // `@Sort!n` cells (#qfax-universe-collapse): an atom of an
        // UNINTERPRETED index/element sort is a legal, declared model value —
        // the printer spells it sort-ascribed (`(as @I!k I)`), matching the
        // dialect of the direct-read cells collected above. Dropping these
        // entries (the former blanket `contains('@')` skip) erased every
        // select-derived point of a pure-QF_AX array, collapsing the printed
        // witness to a bare const-array that FALSIFIES the asserted reads —
        // an invalid printed model on a correctly-gated sat (the gate reads
        // the internal interpretation, which kept the cells). Only a
        // NON-printable skolem — a datatype representative the select scan
        // already captured concretely, or a nested-array `@Arr!n` name — is
        // still skipped (#model-witness-no-skolem).
        if let Some(interp) = interp {
            let index_sort = match self.ctx.terms.sort(array_term) {
                Sort::Array(array_sort) => Some(array_sort.index_sort.clone()),
                _ => None,
            };
            // ArrayInterpretation is authoritative/newest-first; the witness
            // builder is chronological/oldest-first.  Convert at this single
            // boundary and use `upsert_store` to collapse shadowed duplicates.
            // Direct reads collected above remain the stronger authority.
            let mut reconstructed = Vec::new();
            for (idx_str, val_str) in interp.stores.iter().rev() {
                let idx_str = if idx_str.contains('@') {
                    match index_sort
                        .as_ref()
                        .and_then(|sort| self.printable_uninterpreted_atom(idx_str, sort))
                    {
                        Some(spelled) => spelled,
                        None => continue,
                    }
                } else {
                    match index_sort.as_ref() {
                        Some(sort) => printed(idx_str.clone(), sort),
                        None => idx_str.clone(),
                    }
                };
                let val_str = match self.printable_reconstructed_cell(val_str, elem_sort) {
                    Ok(Some(spelled)) => printed(spelled, elem_sort),
                    Ok(None) => continue,
                    Err(()) => return None,
                };
                Self::upsert_store(&mut reconstructed, idx_str, val_str);
            }
            for (idx_str, val_str) in reconstructed {
                if !stores.iter().any(|(key, _)| key == &idx_str) {
                    stores.push((idx_str, val_str));
                }
            }
        }
        // Resolve a deferred (completed) default. When every collected cell of
        // a SCALAR element sort carries ONE shared value, reuse that value —
        // an equally free completion choice that folds the whole array into a
        // bare const-array witness instead of fabricating the const-0 base the
        // #model-array-witness tests guard against. Mixed cell values keep the
        // canonical default (so observed cells stay explicit store points),
        // and datatype/array element sorts keep the canonical recursive
        // default (`non`-style constructor values), matching the documented
        // array-of-datatype witness shape.
        let default = match default {
            Some(d) => d,
            None => {
                let scalar_elem = !matches!(elem_sort, Sort::Array(_))
                    && self.datatype_sort_name(elem_sort).is_none();
                let shared: Option<&String> = match stores.as_slice() {
                    [] => None,
                    [(_, first), rest @ ..] => (scalar_elem
                        && !first.contains('@')
                        && rest.iter().all(|(_, v)| v == first))
                    .then_some(first),
                };
                shared
                    .cloned()
                    .unwrap_or_else(|| self.canonical_default_value(elem_sort))
            }
        };
        Some((default, stores))
    }

    fn array_read_is_active(
        &self,
        read: TermId,
        authenticated_dt_cells: Option<&AuthenticatedDatatypeArrayMembers>,
    ) -> bool {
        self.term_is_required_by_last_query(read)
            || authenticated_dt_cells.is_some_and(|cells| cells.contains(read))
    }

    /// Render an array element value at `elem_sort`, recursing into nested array
    /// elements (so an `(Array X (Array Y Z))` default/store value is itself a
    /// fully rendered array).
    fn format_array_element_value(
        &self,
        model: &Model,
        elem_term: TermId,
        elem_sort: &Sort,
        def_visited: &mut HashSet<TermId>,
        mode: ArrayInterpMode,
    ) -> Option<String> {
        if matches!(elem_sort, Sort::Array(_)) {
            self.format_array_witness_value_inner(model, elem_term, elem_sort, def_visited, mode)
        } else if let Some(dt_name) = self.datatype_sort_name(elem_sort) {
            // Datatype element: render the per-element constructor value.
            // `resolve_dt_value` returns a concrete canonical default (no skolem)
            // when the value is undetermined (#model-witness-no-skolem).
            Some(
                self.resolve_dt_value(&dt_name, elem_term, model)
                    .unwrap_or_else(|| self.canonical_default_value(elem_sort)),
            )
        } else {
            let value_val = self.evaluate_term(model, elem_term);
            if matches!(value_val, EvalValue::Unknown) {
                None
            } else {
                Some(self.format_array_point_value(&value_val, elem_term))
            }
        }
    }

    /// Render an array store/select INDEX (key) value.
    ///
    /// When the array's INDEX sort is a datatype, the key's model value is an
    /// internal `@Sort!n` skolem that is equal — in the model's equivalence
    /// classes — to a concrete constructor (`(select a red)` puts `red` and the
    /// skolem key in one class). The key MUST be concretized to that constructor
    /// term (z3 rejects the skolem as an unknown constant). A datatype or array
    /// index reuses the element renderer (`resolve_dt_value` with a canonical
    /// fallback — never a skolem); any other sort uses its scalar rendering
    /// (#model-witness-no-skolem).
    fn format_array_index_value(
        &self,
        model: &Model,
        index_term: TermId,
        def_visited: &mut HashSet<TermId>,
        mode: ArrayInterpMode,
    ) -> Option<String> {
        let index_sort = self.ctx.terms.sort(index_term);
        if matches!(index_sort, Sort::Array(_)) || self.datatype_sort_name(index_sort).is_some() {
            self.format_array_element_value(model, index_term, index_sort, def_visited, mode)
        } else {
            let index_val = self.evaluate_term(model, index_term);
            if matches!(index_val, EvalValue::Unknown) {
                None
            } else {
                Some(self.format_array_point_value(&index_val, index_term))
            }
        }
    }

    /// Render an array-sorted term's whole-array model value as a `store`-chain
    /// that satisfies the model's known `(select array_term i) = v` constraints.
    ///
    /// The bare `((as const ...) default)` rendering drops every constrained
    /// index and prints an array that VIOLATES the assertions — an invalid
    /// witness. This builds the store-axiom-consistent interpretation
    /// ([`Self::array_witness_interp`]) and folds it into a `store`-chain over the
    /// (recursively rendered) default, so the printed model reads back the
    /// asserted values (#model-array-witness).
    ///
    /// Used for `(define-fun a ...)` in `(get-model)`, the value in
    /// `(get-value (a))`, and array-typed datatype constructor fields.
    pub(super) fn format_array_witness_value(
        &self,
        model: &Model,
        array_term: TermId,
        sort: &Sort,
    ) -> Option<String> {
        match self.functional_array_render(model, array_term) {
            Ok(Some(value)) => return Some(value),
            Ok(None) => {}
            Err(_) => return None,
        }
        let mut def_visited = HashSet::default();
        self.format_array_witness_value_inner(
            model,
            array_term,
            sort,
            &mut def_visited,
            ArrayInterpMode::Strict,
        )
    }

    /// Inner implementation of [`Self::format_array_witness_value`] threading the
    /// definitional-cycle / nesting guard.
    fn format_array_witness_value_inner(
        &self,
        model: &Model,
        array_term: TermId,
        sort: &Sort,
        def_visited: &mut HashSet<TermId>,
        mode: ArrayInterpMode,
    ) -> Option<String> {
        match self.functional_array_render(model, array_term) {
            Ok(Some(value)) => return Some(value),
            Ok(None) => {}
            Err(_) => return None,
        }
        let Sort::Array(arr_sort) = sort else {
            return None;
        };
        if mode == ArrayInterpMode::Strict {
            if self.last_model_validated {
                if let Some((projected_sort, value)) =
                    self.authenticated_unobserved_array_field(model, array_term)
                {
                    if &projected_sort != arr_sort.as_ref() {
                        return None;
                    }
                    return self.format_gate_model_value(
                        &ay_model_check::ModelValue::Array(Box::new(value)),
                        sort,
                    );
                }
            }
            if self.unobserved_array_field_authority_claim(model, array_term) {
                return None;
            }
        }
        let sort_str = format_sort_surface(&self.ctx, sort);
        let (default, stores) = self.array_witness_interp_inner(
            model,
            array_term,
            &arr_sort.element_sort,
            def_visited,
            mode,
            None,
        )?;
        let mut result = format!("((as const {sort_str}) {default})");
        for (idx, val) in stores {
            // The const base already yields `default` everywhere, so a point
            // equal to it is redundant — skip to keep the witness minimal.
            if val == default {
                continue;
            }
            result = format!("(store {result} {idx} {val})");
        }
        Some(result)
    }

    /// Store-axiom-consistent value of a scalar `(select array_term idx_term)`
    /// for the `(get-value)`/`(eval)` OUTPUT path, derived from the SAME witness
    /// interpretation `(get-model)` prints — so a cell query never diverges from
    /// the printed array (#model-array-witness).
    ///
    /// Returns `Some` only when `array_term` is store-equality dependent (a
    /// `store` expression, or a variable defined by one); for a plain free array
    /// the raw evaluator already agrees with the printed witness, so `None` lets
    /// the caller keep its existing evaluation path (smaller blast radius).
    pub(super) fn array_witness_scalar_select(
        &self,
        model: &Model,
        term_id: TermId,
    ) -> Option<String> {
        let TermData::App(sym, args) = self.ctx.terms.get(term_id) else {
            return None;
        };
        if sym.name() != "select" || args.len() != 2 {
            return None;
        }
        if !self.array_term_is_store_dependent(args[0]) {
            return None;
        }
        let elem_sort = self.ctx.terms.sort(term_id).clone();
        let mut def_visited = HashSet::default();
        let (default, stores) =
            self.array_witness_interp(model, args[0], &elem_sort, &mut def_visited)?;
        let idx_str = self.format_array_index_value(
            model,
            args[1],
            &mut def_visited,
            ArrayInterpMode::Strict,
        )?;
        Some(
            stores
                .into_iter()
                .find(|(k, _)| *k == idx_str)
                .map(|(_, v)| v)
                .unwrap_or(default),
        )
    }

    /// True when `array_term` is store-equality dependent: a `store` application,
    /// or an array variable with a definitional equality `(= v <store/const>)`
    /// (possibly through a variable chain). Such arrays are the ones whose raw
    /// `select` evaluation can diverge from the printed `store`-chain witness.
    fn array_term_is_store_dependent(&self, array_term: TermId) -> bool {
        match self.ctx.terms.get(array_term) {
            TermData::App(sym, args) if sym.name() == "store" && args.len() == 3 => true,
            TermData::Var(_, _) => self.array_variable_definition(array_term).is_some(),
            _ => false,
        }
    }

    /// Format an array term's value for get-value output.
    ///
    /// This prefers using `ArrayModel` when available (QF_AX / QF_AUFL*), and otherwise
    /// falls back to rebuilding a value for common array constructors (`store`, `const-array`).
    /// Uses `stacker::maybe_grow` for stack safety on deeply nested store chains (#4602).
    pub(super) fn format_array_term_value(&self, model: &Model, term_id: TermId) -> Option<String> {
        match self.functional_array_render(model, term_id) {
            Ok(Some(value)) => return Some(value),
            Ok(None) => {}
            Err(_) => return None,
        }
        // A fresh definition-cycle guard per top-level format request. Resolving
        // an array variable through its definitional equality below recurses,
        // and `array_variable_definition` reads `(= a b)` in BOTH directions, so
        // a mutual array equality (e.g. `(= a b)`) is a definitional cycle that
        // would otherwise recurse forever (allocating stacker segments until the
        // process is OOM-killed). See `evaluate_select` for the analogous guard.
        let mut def_visited = HashSet::default();
        self.format_array_term_value_resolving_defs(model, term_id, &mut def_visited)
    }

    /// Inner implementation of [`Self::format_array_term_value`] threading a
    /// definition-cycle guard (`def_visited`) through the array-variable
    /// definitional-equality recursion.
    fn format_array_term_value_resolving_defs(
        &self,
        model: &Model,
        term_id: TermId,
        def_visited: &mut HashSet<TermId>,
    ) -> Option<String> {
        stacker::maybe_grow(ARRAY_FMT_STACK_RED_ZONE, ARRAY_FMT_STACK_SIZE, || {
            match self.functional_array_render(model, term_id) {
                Ok(Some(value)) => return Some(value),
                Ok(None) => {}
                Err(_) => return None,
            }
            let sort = self.ctx.terms.sort(term_id);
            if !matches!(sort, Sort::Array(_)) {
                return None;
            }
            if model
                .array_model
                .as_ref()
                .is_some_and(|arrays| arrays.is_withheld(&term_id))
            {
                return None;
            }

            match self.ctx.terms.get(term_id) {
                TermData::Var(_, _) => {
                    if let Some(array_model) = model.array_model.as_ref() {
                        if let Some(interp) = array_model.array_values.get(&term_id) {
                            if array_model.is_withheld(&term_id) {
                                return None;
                            }
                            return self.format_array_value(sort, interp);
                        }
                    }
                    // No reconstructed array-model entry: resolve the array
                    // variable through its definitional equality
                    // `(= a <array-expr>)` in the assertions and format that
                    // expression. In pure QF_(A)LIA the array's value lives only
                    // in the committed assertion (#5450). The exclusion set and
                    // the `def_visited.insert` below break a mutual/cyclic
                    // definition chain (returning `None`, which callers treat as
                    // "no value" and degrade soundly).
                    let def = self.array_variable_definition_excluding(term_id, def_visited)?;
                    if def == term_id || !def_visited.insert(term_id) {
                        return None;
                    }
                    self.format_array_term_value_resolving_defs(model, def, def_visited)
                }
                TermData::Let(_, body) => {
                    self.format_array_term_value_resolving_defs(model, *body, def_visited)
                }
                TermData::Ite(cond, then_br, else_br) => match self.evaluate_term(model, *cond) {
                    EvalValue::Bool(true) => {
                        self.format_array_term_value_resolving_defs(model, *then_br, def_visited)
                    }
                    EvalValue::Bool(false) => {
                        self.format_array_term_value_resolving_defs(model, *else_br, def_visited)
                    }
                    _ => None,
                },
                TermData::App(sym, args) => match sym.name() {
                    "store" if args.len() == 3 => {
                        let base = self.format_array_term_value_resolving_defs(
                            model,
                            args[0],
                            def_visited,
                        )?;

                        let index_val = self.evaluate_term(model, args[1]);
                        let index_str = self.try_format_eval_value(&index_val, args[1]).ok()?;

                        let value_val = self.evaluate_term(model, args[2]);
                        let value_str = self.try_format_eval_value(&value_val, args[2]).ok()?;

                        Some(format!("(store {base} {index_str} {value_str})"))
                    }
                    "const-array" if args.len() == 1 => {
                        let default_val = self.evaluate_term(model, args[0]);
                        let default_str = self.try_format_eval_value(&default_val, args[0]).ok()?;
                        Some(format!(
                            "((as const {}) {})",
                            format_sort_surface(&self.ctx, sort),
                            default_str
                        ))
                    }
                    _ => None,
                },
                _ => None,
            }
        })
    }

    /// Format an evaluated value for SMT-LIB output.
    ///
    /// Total over values that EXIST: `Err` for `EvalValue::Unknown` (and for
    /// an algebraic value with no derivable defining polynomial — refinement
    /// cap, practically unreachable). The former behavior — printing a
    /// fabricated sort default for Unknown — is removed
    /// (#no-fabricated-model-values); user-facing paths surface the `Err` as a
    /// command-level `(error ...)`.
    pub(super) fn try_format_eval_value(
        &self,
        value: &EvalValue,
        term_id: TermId,
    ) -> Result<String, String> {
        match value {
            EvalValue::Bool(true) => Ok("true".to_string()),
            EvalValue::Bool(false) => Ok("false".to_string()),
            EvalValue::Complex { real, imaginary } => Ok(format!(
                "(complex.make {} {})",
                Self::format_complex_component(real)?,
                Self::format_complex_component(imaginary)?
            )),
            EvalValue::Element(elem) => {
                let sort = self.ctx.terms.sort(term_id);
                if matches!(sort, Sort::Seq(_)) {
                    return Err(format!(
                        "opaque internal equality-class value {elem} is not a concrete sequence"
                    ));
                }
                Ok(format_model_atom_surface(&self.ctx, sort, elem))
            }
            EvalValue::Rational(r) => {
                if r.is_integer() {
                    Ok(r.numer().to_string())
                } else {
                    Ok(format!("(/ {} {})", r.numer(), r.denom()))
                }
            }
            // Exact real algebraic value: rational-valued expressions print as
            // plain rationals; irrational ones in z3 `root-obj` syntax, e.g.
            // `(root-obj (+ (^ x 2) (- 2)) 2)` for `√2`.
            EvalValue::Algebraic(v) => match v.to_number_for_output() {
                Some(ay_nra::RealScalar::Rational(r)) => {
                    if r.is_integer() {
                        Ok(r.numer().to_string())
                    } else {
                        Ok(format!("(/ {} {})", r.numer(), r.denom()))
                    }
                }
                Some(ay_nra::RealScalar::Algebraic(n)) => Ok(n.alpha().to_smtlib()),
                None => Err(format!(
                    "no defining polynomial for algebraic model value of sort {}",
                    format_sort_surface(&self.ctx, self.ctx.terms.sort(term_id))
                )),
            },
            EvalValue::BitVec { value, width } => {
                // Use format_bitvec for SMT-LIB compliant output (#1793).
                Ok(format_bitvec(value, *width))
            }
            EvalValue::FiniteField { value, field } => self
                .format_field_literal_checked(*value, *field)
                .ok_or_else(|| "finite-field numeral rendering refused".into()),
            EvalValue::Fp(fp_val) => Ok(fp_val.to_smtlib()),
            EvalValue::String(s) => Ok(string_literal(s)),
            EvalValue::Seq(elems) => {
                // Element sort drives per-element rendering (Int `(- n)`, BV
                // `#x..`, datatype constructor, …); fall back to the carrier
                // sort itself if `term_id` is somehow not Seq-sorted.
                let elem_sort = self
                    .ctx
                    .terms
                    .sort(term_id)
                    .seq_element()
                    .cloned()
                    .unwrap_or_else(|| self.ctx.terms.sort(term_id).clone());
                Ok(self.format_seq_value(elems, &elem_sort))
            }
            EvalValue::Unknown => Err(format!(
                "no model value available for term of sort {}",
                format_sort_surface(&self.ctx, self.ctx.terms.sort(term_id))
            )),
        }
    }

    /// USER-FACING variant of [`Self::try_format_eval_value`]: byte-identical
    /// on every input EXCEPT an exact-rational value, which prints in SMT-LIB
    /// syntax instead of the legacy internal spelling (`-5`, `(/ -7 2)`):
    ///
    /// * Real-sorted: the z3-exact spelling (`5.0`, `(- 5.0)`, `(/ 7.0 2.0)`,
    ///   `(- (/ 7.0 2.0))`).
    /// * any other sort (Int): an integer as a numeral or `(- n)`, which is the
    ///   only negative spelling the strict typed decoder accepts (a bare `-5`
    ///   lexes as a symbol); a non-integer as `(/ n d)` or `(- (/ n d))`.
    ///
    /// CONTRACT (#real-fmt): stdout boundary ONLY — get-value/eval, get-model
    /// scalars, get-objectives, and resolved function tables route through
    /// here. Internal comparison-key producers (`eval_value_to_model_atom`,
    /// [`Self::format_eval_value`], `format_rational`, the euf `term_values`
    /// built in combined_solvers/models.rs) must keep the legacy spelling:
    /// their strings are equality-compared across producers and re-parsed by
    /// `parse_real_string`.
    pub(super) fn try_format_eval_value_user(
        &self,
        value: &EvalValue,
        term_id: TermId,
    ) -> Result<String, String> {
        if matches!(self.ctx.terms.sort(term_id), Sort::Real) {
            if let Some(s) = eval_value_real_string(value) {
                return Ok(s);
            }
        }
        if let Some(s) = eval_value_rational_string(value) {
            return Ok(s);
        }
        self.try_format_eval_value(value, term_id)
    }

    /// Format an evaluated value for SMT-LIB output (guarded-caller variant).
    ///
    /// CONTRACT: callers must have checked the value is not
    /// `EvalValue::Unknown`. Internal evaluation paths (array normal forms,
    /// dt materialization, set materialization) hold that guard; if it is ever
    /// violated the result is the explicit, unparseable
    /// [`value_unavailable_marker`] — never a fabricated sort default
    /// (#no-fabricated-model-values).
    pub(super) fn format_eval_value(&self, value: &EvalValue, term_id: TermId) -> String {
        self.try_format_eval_value(value, term_id)
            .unwrap_or_else(|_| value_unavailable_marker(&format!("t{}", term_id.0)))
    }

    /// Render an INDEPENDENT-GATE-reconstructed [`ay_model_check::ModelValue`] as
    /// a round-trippable SMT-LIB term, guided by the declared `sort` (which
    /// supplies the array index/element sorts and the datatype field sorts the
    /// value itself does not carry).
    ///
    /// This is the emission-side twin of the gate's entailed-alias
    /// reconstruction: the gate resolves a datatype/array leaf to a fully
    /// COMMITTED/ENTAILED `ModelValue` (constructor + concrete fields, or a
    /// finite store-chain over a concrete default) via its `def_index` of
    /// asserted definitional equalities, and this turns that value back into the
    /// SMT-LIB witness a solver can re-check. Every leaf of a `ModelValue` is a
    /// concrete, committed value by construction — never a completion default —
    /// so nothing here fabricates.
    ///
    /// Returns `None` (fail-closed, NEVER a fabricated default) if any leaf is
    /// genuinely non-round-trippable: an OPAQUE uninterpreted skolem token
    /// (`@Sort!n` / a mangled `!`-token), an algebraic real the gate does not
    /// carry, or a value/sort SHAPE mismatch (a datatype value whose arity or
    /// field sorts do not line up, an array value under a non-array sort). The
    /// caller then keeps its existing behavior — including the explicit
    /// unavailable marker — so a real gap is surfaced, not papered over
    /// (#no-fabricated-model-values).
    pub(in crate::executor) fn format_gate_model_value(
        &self,
        value: &ay_model_check::ModelValue,
        sort: &Sort,
    ) -> Option<String> {
        use ay_model_check::ModelValue as MV;
        match value {
            MV::Bool(b) => Some(if *b {
                "true".to_string()
            } else {
                "false".to_string()
            }),
            // Printing a root object in z3's `(root-obj p k)` form needs the
            // ROOT INDEX, which this representation stores as an isolating
            // interval instead. Declining to print is fail-closed: a caller
            // gets no value rather than a wrong one. Converting the interval
            // to an index is part of the ordering work documented in
            // `ay-model-check::algebraic`).
            MV::Algebraic(_) => None,
            MV::Int(i) => Some(format_bigint(i)),
            MV::Real(r) => Some(format_rational(r)),
            MV::BitVec { width, value } => Some(format_bitvec(value, *width)),
            MV::FloatingPointExact {
                sign,
                exponent,
                significand,
                exponent_bits,
                significand_bits,
            } => {
                let Sort::FloatingPoint(eb, sb) = sort else {
                    return None;
                };
                if exponent_bits != eb || significand_bits != sb {
                    return None;
                }
                if !(2..=ay_fp::MAX_ENCODING_EXPONENT_BITS).contains(eb)
                    || !(2..=ay_fp::MAX_ENCODING_SIGNIFICAND_BITS).contains(sb)
                {
                    return None;
                }
                self.poll_evaluation_stop().ok()?;
                let fields = ay_fp::FpFields::from_shared(
                    *sign,
                    std::sync::Arc::clone(exponent),
                    std::sync::Arc::clone(significand),
                    *eb,
                    *sb,
                )?;
                let value = ay_fp::FpModelValue::Exact(fields);
                let output_bytes = if value.is_nan() || value.is_zero() || value.is_infinite() {
                    128
                } else {
                    usize::try_from(eb.checked_add(*sb)?)
                        .ok()?
                        .checked_mul(2)?
                        .checked_add(128)?
                };
                let _arena = self.admit_evaluation_scratch(output_bytes).ok()?;
                let output = value.to_smtlib();
                self.poll_evaluation_stop().ok()?;
                Some(output)
            }
            MV::FloatingPoint {
                sign,
                exponent,
                significand,
                exponent_bits,
                significand_bits,
            } => {
                let Sort::FloatingPoint(sort_eb, sort_sb) = sort else {
                    return None;
                };
                if exponent_bits != sort_eb || significand_bits != sort_sb {
                    return None;
                }
                ay_fp::FpModelValue::from_fields(
                    *sign,
                    *exponent,
                    *significand,
                    *exponent_bits,
                    *significand_bits,
                )?;
                let stored_bits = *significand_bits - 1;
                Some(format!(
                    "(fp {} {} {})",
                    format_bitvec(&BigInt::from(u8::from(*sign)), 1),
                    format_bitvec(&BigInt::from(*exponent), *exponent_bits),
                    format_bitvec(&BigInt::from(*significand), stored_bits)
                ))
            }
            MV::Str(s) => Some(string_literal(s)),
            MV::Uninterpreted(tok) => {
                // An INTERNAL representative token (`@Sort!n`) or an
                // instance-mangled `!`-token is not a valid SMT-LIB constant, so
                // it cannot round-trip: fail closed rather than leak a skolem
                // (mirrors the printer's existing `@`-skolem avoidance,
                // #model-witness-no-skolem).
                //
                // Except an abstract element of an UNINTERPRETED sort
                // (`@Sort!n`, `@ay!wit!<kind>!<n>`): that is a model value,
                // printed sort-ascribed exactly as the scalar printer prints
                // it. Refusing it sent every QF_AX array to the separate
                // witness builder instead of printing the value this gate
                // validated (AY-N9).
                if tok.starts_with('@') || tok.contains('!') {
                    return self.printable_uninterpreted_atom(tok, sort);
                }
                Some(format_model_atom_surface(&self.ctx, sort, tok))
            }
            MV::Seq(elems) => {
                let elem_sort = sort.seq_element()?;
                let mut vals = Vec::with_capacity(elems.len());
                for e in elems {
                    // Reuse the sequence renderer's element formatting by
                    // reconstructing an EvalValue is unnecessary — render each
                    // element directly through this same value formatter.
                    vals.push(self.format_gate_model_value(e, elem_sort)?);
                }
                if vals.is_empty() {
                    return Some(format!(
                        "(as seq.empty {})",
                        format_sort_surface(&self.ctx, sort)
                    ));
                }
                let mut acc = format!("(seq.unit {})", vals[0]);
                for v in &vals[1..] {
                    acc = format!("(seq.++ {acc} (seq.unit {v}))");
                }
                Some(acc)
            }
            MV::Array(av) => {
                let Sort::Array(arr) = sort else {
                    return None;
                };
                let idx_sort = &arr.index_sort;
                let elem_sort = &arr.element_sort;
                let default = self.format_gate_model_value(&av.default, elem_sort)?;
                let mut out = format!(
                    "((as const {}) {})",
                    format_sort_surface(&self.ctx, sort),
                    default
                );
                for (idx, val) in &av.store {
                    let idx_str = self.format_gate_model_value(idx, idx_sort)?;
                    let val_str = self.format_gate_model_value(val, elem_sort)?;
                    out = format!("(store {out} {idx_str} {val_str})");
                }
                Some(out)
            }
            MV::Datatype { ctor, args } if sort == &Sort::Complex => {
                let [real, imaginary] = args.as_slice() else {
                    return None;
                };
                if ctor != "complex.make" {
                    return None;
                }
                Some(format!(
                    "(complex.make {} {})",
                    self.format_gate_model_value(real, &Sort::Real)?,
                    self.format_gate_model_value(imaginary, &Sort::Real)?
                ))
            }
            MV::Datatype { ctor, args } => {
                // Field sorts come from THIS constructor's own declaration (a
                // selector name can be shared across datatypes, so a global
                // symbol-sort lookup could pick a sibling's field sort —
                // #dt-shared-selector-field-sort).
                let fields = self.ctx.constructor_selector_info(ctor)?;
                if fields.len() != args.len() {
                    return None;
                }
                let surface = self.dt_value_head(ctor).into_owned();
                if args.is_empty() {
                    return Some(surface);
                }
                let mut parts = Vec::with_capacity(args.len());
                for (arg, (_fname, fsort)) in args.iter().zip(fields.iter()) {
                    parts.push(self.format_gate_model_value(arg, fsort)?);
                }
                Some(format!("({} {})", surface, parts.join(" ")))
            }
        }
    }

    /// Render a sequence model value (`EvalValue::Seq`) as a round-trippable
    /// SMT-LIB term (#model-seq-witness).
    ///
    /// SMT-LIB 2.6 `seq.++` is BINARY, so an `N >= 2` element sequence is emitted
    /// as a LEFT-ASSOCIATIVE binary tree
    /// `(seq.++ (seq.++ (seq.unit e0) (seq.unit e1)) (seq.unit e2))`; an n-ary
    /// `(seq.++ e0 e1 e2)` is unparseable and would not re-feed to a solver.
    /// Length 1 is `(seq.unit e0)` and length 0 is `(as seq.empty (Seq E))`. Each
    /// element is rendered in its element sort so the literal round-trips.
    pub(super) fn format_seq_value(&self, elems: &[EvalValue], elem_sort: &Sort) -> String {
        if elems.is_empty() {
            let seq_sort = Sort::Seq(Box::new(elem_sort.clone()));
            return format!(
                "(as seq.empty {})",
                format_sort_surface(&self.ctx, &seq_sort)
            );
        }
        let mut acc = format!(
            "(seq.unit {})",
            self.format_seq_element(&elems[0], elem_sort)
        );
        for e in &elems[1..] {
            acc = format!(
                "(seq.++ {acc} (seq.unit {}))",
                self.format_seq_element(e, elem_sort)
            );
        }
        acc
    }

    /// Render a single sequence element value in its declared element sort so it
    /// round-trips as SMT-LIB: a negative Int as `(- n)` (a bare `-n` is not a
    /// numeral), a BitVec as `#x..`/`#b..`, a Bool as `true`/`false`, a datatype/
    /// uninterpreted element through `format_model_atom`, and a nested `(Seq E)`
    /// element recursively (#model-seq-witness).
    fn format_seq_element(&self, value: &EvalValue, elem_sort: &Sort) -> String {
        match value {
            EvalValue::Complex { real, imaginary } => {
                match (
                    Self::format_complex_component(real),
                    Self::format_complex_component(imaginary),
                ) {
                    (Ok(real), Ok(imaginary)) if elem_sort == &Sort::Complex => {
                        format!("(complex.make {real} {imaginary})")
                    }
                    _ => value_unavailable_marker("Complex sequence element"),
                }
            }
            EvalValue::Bool(true) => "true".to_string(),
            EvalValue::Bool(false) => "false".to_string(),
            EvalValue::Rational(r) => match elem_sort {
                Sort::Real => format_rational(r),
                // Int (and any other numeric carrier): unary-minus for negatives.
                _ => format_bigint(r.numer()),
            },
            EvalValue::BitVec { value, width } => format_bitvec(value, *width),
            EvalValue::FiniteField { value, field } => self.format_field_literal(*value, *field),
            EvalValue::Fp(fp_val) => fp_val.to_smtlib(),
            EvalValue::String(s) => string_literal(s),
            EvalValue::Element(elem) => format_model_atom_surface(&self.ctx, elem_sort, elem),
            EvalValue::Seq(inner) => {
                let inner_sort = elem_sort
                    .seq_element()
                    .cloned()
                    .unwrap_or_else(|| elem_sort.clone());
                self.format_seq_value(inner, &inner_sort)
            }
            // Algebraic reals cannot appear as sequence elements (no NRA/seq
            // combination), and every `EvalValue::Seq` producer filters Unknown
            // elements before constructing the sequence — both arms are
            // internal invariant violations, surfaced as the explicit
            // unparseable marker, never a fabricated element default
            // (#no-fabricated-model-values).
            EvalValue::Algebraic(_) => value_unavailable_marker(&format!(
                "seq-elem {}",
                format_sort_surface(&self.ctx, elem_sort)
            )),
            EvalValue::Unknown => value_unavailable_marker(&format!(
                "seq-elem {}",
                format_sort_surface(&self.ctx, elem_sort)
            )),
        }
    }

    /// Resolve `@?N` placeholder values in a function table using the full model (#5452).
    ///
    /// The EUF model builds function tables before LIA/LRA/BV theory values are
    /// merged into `term_values`. Int/Real/BV-returning functions get `@?{term_id}`
    /// placeholders for their result values (and sometimes arguments). This method
    /// resolves those placeholders using `evaluate_term`, which consults all theory
    /// models including `func_app_const_terms`, `lia_model`, `lra_model`, and `bv_model`.
    pub(super) fn resolve_function_table(
        &self,
        model: &Model,
        table: &[(Vec<String>, String)],
    ) -> Vec<(Vec<String>, String)> {
        table
            .iter()
            .map(|(args, result)| {
                let resolved_args: Vec<String> = args
                    .iter()
                    .map(|a| self.resolve_placeholder(model, a))
                    .collect();
                let resolved_result = self.resolve_placeholder(model, result);
                (resolved_args, resolved_result)
            })
            .collect()
    }

    /// Resolve a single `@?N` placeholder string to a concrete value.
    ///
    /// If the string matches `@?N` where N is a valid term ID, evaluate that term
    /// using the full model and return the formatted value. Otherwise return the
    /// original string unchanged.
    fn resolve_placeholder(&self, model: &Model, value: &str) -> String {
        // Check if this is an @?N placeholder
        let term_id = match value.strip_prefix("@?") {
            Some(id_str) => match id_str.parse::<u32>() {
                Ok(id) if (id as usize) < self.ctx.terms.len() => TermId(id),
                _ => return value.to_string(),
            },
            None => return value.to_string(),
        };

        // Evaluate the term using the full model (which has all theory values)
        let eval = self.evaluate_term(model, term_id);
        // USER-FACING Real gate (#real-fmt): resolved tables are consumed
        // only by the printed `(get-model)` define-funs (the
        // `resolve_function_table` call in output.rs) and
        // `uf_unlisted_point_value` — both stdout surfaces — so a Real-sorted
        // rational prints in the z3-exact spelling here. An Unknown eval MUST
        // still fall through and keep the raw `@?N` placeholder:
        // `table_entry_is_quantifier_phantom` and the fail-closed
        // `resolve_table_value` error path key off the surviving `@?` prefix.
        if matches!(self.ctx.terms.sort(term_id), Sort::Real) {
            if let Some(resolved) = eval_value_real_string(&eval) {
                return resolved;
            }
        }
        match self.eval_value_to_model_atom(&eval) {
            Some(resolved) => resolved,
            None => value.to_string(), // Keep placeholder if evaluation fails
        }
    }
}

#[cfg(test)]
mod array_store_order_tests {
    use super::format_newest_first_store_chain;

    #[test]
    fn newest_first_duplicate_index_is_emitted_outermost() {
        let stores = vec![
            ("7".to_string(), "2".to_string()),
            ("7".to_string(), "1".to_string()),
        ];
        let rendered =
            format_newest_first_store_chain("((as const (Array Int Int)) 0)".to_string(), &stores);
        assert_eq!(
            rendered,
            "(store (store ((as const (Array Int Int)) 0) 7 1) 7 2)"
        );
    }
}

#[cfg(test)]
mod gate_fp_format_tests;

#[cfg(test)]
mod sequence_table_provenance_tests;

/// The SMT-LIB spelling of a raw arithmetic function-table entry at `sort`.
///
/// Function-table rows can carry an already-concrete value text from model
/// extraction, and an extracted negative integer arrives as the bare token
/// `-1`. That token is a SYMBOL in SMT-LIB, not a numeral, so the printed row
/// `(ite (= x0 -1) true ...)` is ill-formed: a reader either rejects it or (the
/// Z3 C API's table reader) loses the row, publishing a function that violates
/// the assertions it was validated against. A negative numeral or decimal is
/// re-spelled at the declared sort (`(- 1)`, `(- 1.0)`); any other text is `None`.
fn smtlib_arith_table_literal(raw: &str, sort: &Sort) -> Option<String> {
    if !matches!(sort, Sort::Int | Sort::Real) {
        return None;
    }
    // Only a leading `-` makes the bare text a non-numeral; every other
    // numeral or decimal is already valid SMT-LIB and is printed unchanged.
    let magnitude = raw.strip_prefix('-')?;
    let (int_part, frac_part) = magnitude.split_once('.').unwrap_or((magnitude, ""));
    let digits_ok = !int_part.is_empty()
        && int_part.bytes().all(|b| b.is_ascii_digit())
        && frac_part.bytes().all(|b| b.is_ascii_digit());
    if !digits_ok {
        return None;
    }
    let numer: BigInt = format!("{int_part}{frac_part}").parse().ok()?;
    let denom = BigInt::from(10u32).pow(u32::try_from(frac_part.len()).ok()?);
    let value = num_rational::BigRational::new(-numer, denom);
    match sort {
        Sort::Int if value.is_integer() => Some(format_bigint(value.numer())),
        Sort::Real => Some(format_real(&value)),
        _ => None,
    }
}
