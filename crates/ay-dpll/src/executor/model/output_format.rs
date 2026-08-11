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
use ay_core::term::TermData;
use ay_core::{quote_symbol, string_literal, Sort, TermId};
use num_bigint::BigInt;

use crate::executor_format::{
    format_bigint, format_bitvec, format_default_value_surface, format_model_atom_surface,
    format_rational, format_real, format_sort_surface,
};

use super::Executor;
use super::{EvalValue, Model};

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
        EvalValue::Algebraic(v) => match v.to_number() {
            Some(ay_nra::RealScalar::Rational(r)) => Some(format_real(&r)),
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
        let parameter_names: Vec<String> = (0..argument_sorts.len())
            .map(|index| format!("__ay_projection_arg_{index}"))
            .collect();
        let parameters = parameter_names
            .iter()
            .zip(argument_sorts)
            .map(|(parameter, sort)| {
                format!(
                    "({} {})",
                    quote_symbol(parameter),
                    format_sort_surface(&self.ctx, sort)
                )
            })
            .collect::<Vec<_>>()
            .join(" ");
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
    ) -> Result<String, String> {
        // Generate parameter names: x0, x1, ...
        let params: Vec<String> = arg_sorts
            .iter()
            .enumerate()
            .map(|(i, s)| format!("(x{} {})", i, format_sort_surface(&self.ctx, s)))
            .collect();

        let params_str = params.join(" ");
        let result_sort_str = format_sort_surface(&self.ctx, result_sort);

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
                resolved_args.push(self.resolve_table_value(arg, &sort, model)?);
            }
            let resolved_result = self.resolve_table_value(result, result_sort, model)?;
            resolved_table.push((resolved_args, resolved_result));
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
                    return Err(format!(
                        "inconsistent function table for {}: point ({}) resolves to both {} and {}",
                        quote_symbol(name),
                        args.join(" "),
                        prev,
                        result
                    ));
                }
                None => {
                    seen_points.insert(args.clone(), result.clone());
                    deduped.push((args, result));
                }
            }
        }
        let resolved_table = deduped;

        // Build nested ite expression from resolved table.
        let body = if resolved_table.is_empty() {
            // Empty table: no application of this function is constrained by
            // the formula, so ANY total function is a valid witness — complete
            // it with the canonical constant body (legitimate model
            // completion of an unconstrained function, not a fabricated value
            // for a missing one).
            format_default_value_surface(&self.ctx, result_sort)
        } else {
            self.format_function_body(arg_sorts, result_sort, &resolved_table)
        };

        Ok(format!(
            "  (define-fun {} ({}) {}\n    {})",
            quote_symbol(name),
            params_str,
            result_sort_str,
            body
        ))
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
        let params: Vec<String> = arg_sorts
            .iter()
            .enumerate()
            .map(|(i, sort)| format!("(x{} {})", i, format_sort_surface(&self.ctx, sort)))
            .collect();
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
        for (args, value) in deduped.iter().rev() {
            let conditions: Vec<String> = args
                .iter()
                .enumerate()
                .map(|(i, arg)| format!("(= x{i} {arg})"))
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
            params.join(" "),
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
                let eval = self.evaluate_term(model, term_id);
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
            // Abstract element token (`@Sort!n`) of an uninterpreted sort:
            // sort-ascribe it exactly like every other printed occurrence
            // (#mv-abstract-value-ascription). Scalar sorts pass through
            // unchanged.
            return Ok(format_model_atom_surface(&self.ctx, sort, raw));
        }
        Ok(raw.to_string())
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
        if binders.is_empty() {
            return false;
        }
        self.term_mentions_named_var(term_id, &binders)
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
        _arg_sorts: &[Sort],
        result_sort: &Sort,
        table: &[(Vec<String>, String)],
    ) -> String {
        if table.is_empty() {
            // Unreachable in practice (the caller special-cases the empty
            // table); kept total with the same unconstrained-function body.
            return format_default_value_surface(&self.ctx, result_sort);
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
                .enumerate()
                .map(|(i, arg)| format!("(= x{i} {arg})"))
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
        let base = format!("((as const {sort_str}) {default})");

        Some(format_newest_first_store_chain(base, &interp.stores))
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
    fn term_is_required_by_last_query(&self, needle: TermId) -> bool {
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
    ) -> Option<(String, Vec<(String, String)>)> {
        debug_assert!(
            mode.completes_missing_default(),
            "completion candidates must use a completion mode"
        );
        let mut def_visited = HashSet::default();
        let (default, stores) =
            self.array_witness_interp_inner(model, array_term, elem_sort, &mut def_visited, mode)?;
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
    ) -> Option<(String, Vec<(String, String)>)> {
        stacker::maybe_grow(ARRAY_FMT_STACK_RED_ZONE, ARRAY_FMT_STACK_SIZE, || {
            if model
                .array_model
                .as_ref()
                .is_some_and(|arrays| arrays.read_conflicted.contains(&array_term))
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
                TermData::Let(bindings, body) if bindings.is_empty() => {
                    self.array_witness_interp_inner(model, *body, elem_sort, def_visited, mode)
                }
                TermData::Let(_, _) if mode.completes_missing_default() => None,
                TermData::Let(_, _) => {
                    self.array_witness_base_interp(model, array_term, elem_sort, def_visited, mode)
                }
                TermData::Ite(cond, then_br, else_br) => match self.evaluate_term(model, *cond) {
                    EvalValue::Bool(true) => self.array_witness_interp_inner(
                        model,
                        *then_br,
                        elem_sort,
                        def_visited,
                        mode,
                    ),
                    EvalValue::Bool(false) => self.array_witness_interp_inner(
                        model,
                        *else_br,
                        elem_sort,
                        def_visited,
                        mode,
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
                    self.array_witness_base_interp(model, array_term, elem_sort, def_visited, mode)
                }
                TermData::Var(_, _) => {
                    if def_visited.contains(&array_term) {
                        return None;
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
                            );
                        }
                    }
                    self.array_witness_base_interp(model, array_term, elem_sort, def_visited, mode)
                }
                // An APPLICATION of a user-declared function whose result sort
                // is an array is a free array LEAF, exactly like the `Var` arm
                // above -- not an array CONSTRUCTOR. The exclusion below was
                // written for lambda / as-array / map, where treating a
                // constrained RHS as a free base would change the definition
                // rather than complete it. A declared `f : S -> (Array I E)`
                // constrains nothing: `(seq_array current)` is as free as a
                // declared `(Array I E)` constant.
                //
                // Excluding it cost real verdicts. In `CompleteDefault` mode this
                // returned `None`, so completion produced no candidate, so the
                // array got no `default`, so `array_witness_base_interp` returned
                // `None` in Strict mode, so the gate's `array_from_model` bailed
                // at `interp.default.as_ref()?`, so `uf_app_value` was `None` and
                // the assertion came back `Unevaluable`:
                //
                //   cannot_confirm_reason "model commits no value for this
                //                          application of `seq_array`"
                //
                // Isolated by controlled variant, not by reading: the same
                // formula with a DECLARED `(Array Int Int)` constant answers
                // `sat` with a full store-chain model; reached through
                // `(seq_array current)` it answers `unknown`; and adding
                // `(= (seq_array current) ((as const (Array Int Int)) 0))` makes
                // it `sat` again -- so the sole missing ingredient is `default`.
                //
                // It also let a `sat` escape that could not be RENDERED at all:
                // `(select (seq_array current) (+ (seq_offset current) 1)) = 0`
                // publishes `sat` and then `(error "model value for function
                // seq_array is not available")`, because the `select` path
                // resolves through `array_select_value` so the gate confirms
                // while the printer cannot build the witness.
                //
                // Restricted to a USER-DECLARED symbol head so lambda,
                // as-array, map and every future array constructor keep the
                // original exclusion.
                TermData::App(sym, _)
                    if mode.completes_missing_default()
                        && self.ctx.symbol_info_by_identity(sym.name()).is_some() =>
                {
                    self.array_witness_base_interp(model, array_term, elem_sort, def_visited, mode)
                }
                _ if mode.completes_missing_default() => None,
                _ => {
                    self.array_witness_base_interp(model, array_term, elem_sort, def_visited, mode)
                }
            }
        })
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
    ) -> Option<(String, Vec<(String, String)>)> {
        let interp = model
            .array_model
            .as_ref()
            .and_then(|am| am.array_values.get(&array_term));
        let read_conflicted = model
            .array_model
            .as_ref()
            .is_some_and(|am| am.read_conflicted.contains(&array_term));
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
        let default = match interp.and_then(|i| i.default.clone()) {
            Some(default) if !default.contains('@') => Some(default),
            // An `@Sort!n` atom of an UNINTERPRETED sort is a first-class
            // model value: the printer sort-ascribes it (`(as @E!k E)`) and
            // the output header declares it, so it must be KEPT — collapsing
            // it to the canonical `@Sort!0` default silently rewrites the
            // committed model (#qfax-universe-collapse). Only a datatype (or
            // otherwise non-printable) representative falls back to the
            // concrete canonical repair below (#model-witness-no-skolem).
            Some(default) => Some(
                self.printable_uninterpreted_atom(&default, elem_sort)
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
            if !self.term_is_required_by_last_query(tid) {
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
                    idx_str.clone()
                };
                let val_str = if val_str.contains('@') {
                    match self.printable_uninterpreted_atom(val_str, elem_sort) {
                        Some(spelled) => spelled,
                        None => continue,
                    }
                } else {
                    val_str.clone()
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
        let Sort::Array(arr_sort) = sort else {
            return None;
        };
        let sort_str = format_sort_surface(&self.ctx, sort);
        let (default, stores) = self.array_witness_interp_inner(
            model,
            array_term,
            &arr_sort.element_sort,
            def_visited,
            mode,
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
            let sort = self.ctx.terms.sort(term_id);
            if !matches!(sort, Sort::Array(_)) {
                return None;
            }
            if model
                .array_model
                .as_ref()
                .is_some_and(|arrays| arrays.read_conflicted.contains(&term_id))
            {
                return None;
            }

            match self.ctx.terms.get(term_id) {
                TermData::Var(_, _) => {
                    if let Some(array_model) = model.array_model.as_ref() {
                        if let Some(interp) = array_model.array_values.get(&term_id) {
                            if array_model.read_conflicted.contains(&term_id) {
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
            EvalValue::Algebraic(v) => match v.to_number() {
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
    /// on every input EXCEPT a Real-SORTED exact-rational value, which prints
    /// in the z3-exact spelling (`5.0`, `(- 5.0)`, `(/ 7.0 2.0)`,
    /// `(- (/ 7.0 2.0))`) instead of the legacy internal one (`5`, `-5`,
    /// `(/ 7 2)`).
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
            // to an index is part of the ordering work (see the A1 TODO in
            // `ay-model-check::algebraic`).
            MV::Algebraic(_) => None,
            MV::Int(i) => Some(format_bigint(i)),
            MV::Real(r) => Some(format_rational(r)),
            MV::BitVec { width, value } => Some(format_bitvec(value, *width)),
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
                if exponent_bits != sort_eb
                    || significand_bits != sort_sb
                    || !(2..64).contains(exponent_bits)
                    || !(2..=64).contains(significand_bits)
                {
                    return None;
                }
                let stored_bits = *significand_bits - 1;
                let max_exponent = (1u64 << *exponent_bits) - 1;
                let significand_limit = 1u64 << stored_bits;
                if *exponent > max_exponent || *significand >= significand_limit {
                    return None;
                }
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
                if tok.starts_with('@') || tok.contains('!') {
                    return None;
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
            MV::Datatype { ctor, args } => {
                // Field sorts come from THIS constructor's own declaration (a
                // selector name can be shared across datatypes, so a global
                // symbol-sort lookup could pick a sibling's field sort —
                // #dt-shared-selector-field-sort).
                let fields = self.ctx.constructor_selector_info(ctor)?;
                if fields.len() != args.len() {
                    return None;
                }
                let surface = self.dt_surface(ctor).to_string();
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
            EvalValue::Bool(true) => "true".to_string(),
            EvalValue::Bool(false) => "false".to_string(),
            EvalValue::Rational(r) => match elem_sort {
                Sort::Real => format_rational(r),
                // Int (and any other numeric carrier): unary-minus for negatives.
                _ => format_bigint(r.numer()),
            },
            EvalValue::BitVec { value, width } => format_bitvec(value, *width),
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
mod gate_fp_format_tests {
    use ay_core::Sort;
    use ay_model_check::ModelValue;

    use super::Executor;

    #[test]
    fn exact_fp_gate_value_round_trips_as_an_smt_fp_literal() {
        let exec = Executor::new();
        let value = ModelValue::FloatingPoint {
            sign: false,
            exponent: 16,
            significand: 256,
            exponent_bits: 5,
            significand_bits: 11,
        };
        assert_eq!(
            exec.format_gate_model_value(&value, &Sort::FloatingPoint(5, 11)),
            Some("(fp #b0 #b10000 #b0100000000)".to_string())
        );
        assert_eq!(
            exec.format_gate_model_value(&value, &Sort::FloatingPoint(8, 24)),
            None,
            "a mismatched carrier sort must fail closed"
        );
    }
}

#[cfg(test)]
mod sequence_table_provenance_tests {
    use ay_core::kani_compat::DetHashMap;
    use ay_core::term::Symbol;
    use ay_core::Sort;
    use ay_frontend::parse;

    use super::{Executor, Model};
    use crate::executor_types::SolveResult;

    #[test]
    fn seq_argument_and_result_cells_use_aligned_source_terms() {
        let mut exec = Executor::new();
        let seq = Sort::Seq(Box::new(Sort::Int));
        let arg = exec.ctx.terms.mk_var("seq-table-arg", seq.clone());
        let app = exec.ctx.terms.mk_app(
            Symbol::Named("seq_table_f".to_string()),
            vec![arg],
            seq.clone(),
        );
        let table = vec![(
            vec!["@ay-seq!arg".to_string()],
            "@ay-seq!result".to_string(),
        )];

        let rewritten = exec
            .sequence_table_provenance_placeholders(
                "seq_table_f",
                std::slice::from_ref(&seq),
                &seq,
                &table,
                Some(std::slice::from_ref(&app)),
            )
            .expect("aligned provenance rewrites");
        assert_eq!(rewritten[0].0, vec![format!("@?{}", arg.0)]);
        assert_eq!(rewritten[0].1, format!("@?{}", app.0));
    }

    #[test]
    fn missing_misaligned_or_wrong_source_provenance_fails_closed() {
        let mut exec = Executor::new();
        let seq = Sort::Seq(Box::new(Sort::Int));
        let arg = exec.ctx.terms.mk_var("seq-table-bad-arg", seq.clone());
        let wrong_app = exec.ctx.terms.mk_app(
            Symbol::Named("other_seq_table_f".to_string()),
            vec![arg],
            seq.clone(),
        );
        let table = vec![(vec!["opaque".to_string()], "opaque".to_string())];

        assert!(exec
            .sequence_table_provenance_placeholders(
                "seq_table_f",
                std::slice::from_ref(&seq),
                &seq,
                &table,
                None,
            )
            .is_err());
        assert!(exec
            .sequence_table_provenance_placeholders(
                "seq_table_f",
                std::slice::from_ref(&seq),
                &seq,
                &table,
                Some(&[]),
            )
            .is_err());
        assert!(exec
            .sequence_table_provenance_placeholders(
                "seq_table_f",
                std::slice::from_ref(&seq),
                &seq,
                &table,
                Some(std::slice::from_ref(&wrong_app)),
            )
            .is_err());
    }

    #[test]
    fn get_model_with_missing_sequence_table_provenance_errors_without_opaque_output() {
        let commands = parse(
            "(set-logic ALL)\n\
             (declare-fun f ((Seq Int)) (Seq Int))",
        )
        .expect("valid declaration");
        let mut exec = Executor::new();
        exec.execute_all(&commands).expect("declaration executes");

        let mut euf = ay_euf::EufModel::default();
        euf.function_tables.insert(
            "f".to_string(),
            vec![(
                vec!["@ay-seq!arg".to_string()],
                "@ay-seq!result".to_string(),
            )],
        );
        // Deliberately omit function_table_terms: no source application means
        // no authority to reinterpret either opaque class as a concrete Seq.
        exec.last_result = Some(SolveResult::Sat);
        exec.last_model = Some(Model {
            quantified_confirmation_seal: Default::default(),
            quantified_grant_model_seal: Default::default(),
            sat_model: Vec::new(),
            term_to_var: DetHashMap::default(),
            bool_overrides: DetHashMap::default(),
            euf_model: Some(euf),
            array_model: None,
            lra_model: None,
            lia_model: None,
            bv_model: None,
            fp_model: None,
            string_model: None,
            seq_model: None,
            projection_ufs: Default::default(),
            certified_total_ufs: Default::default(),
            certified_const_interps: Default::default(),
            formula_neutral_function_defaults: Default::default(),
            completed_values: DetHashMap::default(),
            dt_ground: DetHashMap::default(),
            dt_pins: DetHashMap::default(),
        });

        let output = exec.model();
        assert!(output.starts_with("(error \"model value for function f is not available:"));
        assert!(output.contains("no aligned source-term provenance"));
        assert!(
            !output.contains("@ay-seq"),
            "an error must not echo an opaque sequence token: {output}"
        );
    }
}
