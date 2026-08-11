// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SMT-LIB command handlers for the executor.
//!
//! This module contains implementations for SMT-LIB query commands:
//! - `get-info`: Return solver metadata and statistics
//! - `get-option`: Return option values
//! - `get-assertions`: Return current assertions
//! - `simplify`: Simplify and format a term
//! - `get-assignment`: Return truth values of named formulas
//! - `get-unsat-core`: Return unsatisfiable core
//! - `get-unsat-assumptions`: Return unsat subset from check-sat-assuming

use ay_core::term::{Constant, Symbol, TermData};
use ay_core::{quote_symbol, string_literal, Sort, TermId};
use ay_frontend::{AuthoredAssertionRef, OptionValue};

use crate::executor::model::EvalValue;
use crate::executor_format::{format_bigint, format_rational, format_sort, format_symbol};
use crate::executor_types::{SolveResult, StatValue, UnknownReason};

use super::Executor;

mod apply;

#[allow(clippy::panic)]
#[cfg(test)]
mod tests;

const SMTLIB_VERSION_INFO: &str = concat!(
    "build.version=",
    env!("CARGO_PKG_VERSION"),
    " build.increment=",
    env!("AY_BUILD_INCREMENT"),
    " build.commit=",
    env!("AY_BUILD_COMMIT"),
    " build.datetime_utc=",
    env!("AY_BUILD_DATETIME_UTC"),
    " build.stamp=",
    env!("AY_BUILD_STAMP"),
);

impl Executor {
    /// Generate output for get-info command
    pub(super) fn get_info(&self, keyword: &str) -> String {
        // Keywords may come with or without the colon prefix
        let key = keyword.trim_start_matches(':');
        match key {
            "name" => "(:name \"ay\")".to_string(),
            "version" => format!("(:version {})", string_literal(SMTLIB_VERSION_INFO)),
            "authors" => "(:authors \"AY Authors\")".to_string(),
            "error-behavior" => "(:error-behavior immediate-exit)".to_string(),
            "reason-unknown" => {
                // Return reason for 'unknown' result if applicable
                match self.last_result {
                    Some(SolveResult::Unknown) => {
                        let reason = self.last_unknown_reason.unwrap_or(UnknownReason::Unknown);
                        format!("(:reason-unknown {reason})")
                    }
                    _ => "(error \"no unknown result to explain\")".to_string(),
                }
            }
            "all-statistics" => {
                // Return solver statistics in SMT-LIB format (Z3-compatible)
                self.format_statistics_smt2()
            }
            "assertion-stack-levels" => {
                format!("(:assertion-stack-levels {})", self.assertion_count())
            }
            _ => format!("(error \"unsupported info keyword: {keyword}\")"),
        }
    }

    /// Format statistics as an SMT-LIB s-expression (Z3-compatible format)
    ///
    /// Outputs keyword-value pairs sorted alphabetically:
    /// ```text
    /// (:conflicts        42
    ///  :decisions        100
    ///  :propagations     512
    ///  ...)
    /// ```
    fn format_statistics_smt2(&self) -> String {
        let stats = &self.last_statistics;
        // Fixed fields
        let mut entries: Vec<(String, String)> = vec![
            ("conflicts".to_string(), stats.conflicts.to_string()),
            ("decisions".to_string(), stats.decisions.to_string()),
            (
                "deleted-clauses".to_string(),
                stats.deleted_clauses.to_string(),
            ),
            (
                "learned-clauses".to_string(),
                stats.learned_clauses.to_string(),
            ),
            (
                "max-memory".to_string(),
                format!("{:.2}", stats.max_memory_mb),
            ),
            ("memory".to_string(), format!("{:.2}", stats.memory_mb)),
            (
                "num-assertions".to_string(),
                stats.num_assertions.to_string(),
            ),
            ("num-clauses".to_string(), stats.num_clauses.to_string()),
            ("num-vars".to_string(), stats.num_vars.to_string()),
            ("propagations".to_string(), stats.propagations.to_string()),
            ("restarts".to_string(), stats.restarts.to_string()),
            ("rlimit-count".to_string(), stats.rlimit_count.to_string()),
            (
                "theory-conflicts".to_string(),
                stats.theory_conflicts.to_string(),
            ),
            (
                "theory-propagations".to_string(),
                stats.theory_propagations.to_string(),
            ),
            ("time".to_string(), format!("{:.2}", stats.time_seconds)),
        ];

        // Extra fields (BTreeMap iterates in sorted key order)
        for (key, value) in &stats.extra {
            let formatted_value = match value {
                StatValue::Int(n) => n.to_string(),
                StatValue::Float(f) => format!("{f:.2}"),
                StatValue::String(s) => string_literal(s),
            };
            // Convert underscores to dashes for SMT-LIB style
            let smt_key = key.replace('_', "-");
            entries.push((smt_key, formatted_value));
        }

        // Sort alphabetically by key
        entries.sort_by(|a, b| a.0.cmp(&b.0));

        // Calculate max key length for column alignment
        let max_len = entries.iter().map(|(k, _)| k.len()).max().unwrap_or(0);

        // Format as SMT-LIB s-expression
        let lines: Vec<String> = entries
            .iter()
            .map(|(k, v)| {
                let padding = " ".repeat(max_len.saturating_sub(k.len()) + 1);
                format!(":{k}{padding}{v}")
            })
            .collect();

        format!("({})", lines.join("\n "))
    }

    /// Get an option value for get-option command
    pub(super) fn get_option_value(&self, keyword: &str) -> String {
        let key = keyword.trim_start_matches(':');
        match self.ctx.get_option(key) {
            Some(OptionValue::Bool(b)) => format!("(:{key} {b})"),
            Some(OptionValue::String(s)) => format!("(:{} {})", key, string_literal(s)),
            Some(OptionValue::Numeral(n)) => format!("(:{key} {n})"),
            #[allow(unreachable_patterns)]
            Some(_) => format!("(:{key} unsupported)"),
            None => format!("(error \"unknown option: {keyword}\")"),
        }
    }

    /// Get current assertions for get-assertions command
    pub(super) fn assertions(&self) -> String {
        let authored = self.ctx.authored_assertions_for_display();
        if authored.is_empty() {
            return "()".to_string();
        }

        let formatted: Vec<String> = authored
            .into_iter()
            .map(|assertion| match assertion {
                AuthoredAssertionRef::Parsed(parsed) => {
                    super::proof_surface_syntax::format_authored_frontend_term(parsed)
                }
                AuthoredAssertionRef::Elaborated(term_id) => self.format_term(term_id),
            })
            .collect();

        format!("({})", formatted.join("\n "))
    }

    /// Return the Simplify-style labels attached to the last solver result.
    ///
    /// AY does not currently mint Simplify labels, so the available result is
    /// the empty label list. Matching Z3's availability rule still matters:
    /// the query is valid only after `sat` or `unknown`, never before a check
    /// or after `unsat`.
    pub(super) fn labels(&self) -> String {
        match self.last_result {
            Some(SolveResult::Sat | SolveResult::Unknown) => "(labels)".to_string(),
            _ => "(error \"labels are not available\")".to_string(),
        }
    }

    /// Serialize the CURRENT assertion stack as a self-contained SMT-LIB2
    /// script. (#transpose)
    pub(crate) fn to_smtlib2(&self) -> String {
        self.to_smtlib2_for(&self.ctx.assertions)
    }

    /// Serialize an explicit assertion list as a self-contained SMT-LIB2 script
    /// (declarations + named assertions + `(check-sat)`), self-contained and
    /// re-parsable. For native datatypes, "self-contained" is syntactic only:
    /// the emitted script is a fail-visible UF over-approximation, not an
    /// oracle-equivalent datatype encoding. Used to re-solve a captured
    /// assertion set in a fresh batch solver. (#transpose)
    pub(crate) fn to_smtlib2_for(&self, assertions: &[TermId]) -> String {
        let mut out = String::new();
        let (plain_sorts, datatype_sorts) = self.referenced_uninterpreted_sorts(assertions);
        if !datatype_sorts.is_empty() {
            // Fail-visible header (#dump-self-contained): the carrier sorts of
            // native datatypes are serialized below as PLAIN uninterpreted
            // sorts and their member operations as plain functions, so an
            // external solver sees a UF over-abstraction of the original
            // query (constructor/selector/tester axioms are NOT included).
            out.push_str(
                "; WARNING: NOT oracle-equivalent for external solvers (e.g. z3).\n\
                 ; The following sorts are native DATATYPE sorts whose constructor/\n\
                 ; selector/tester semantics are NOT captured by this script; they are\n\
                 ; declared below as uninterpreted sorts, so this script is a UF\n\
                 ; over-abstraction of the original query: `unsat` here implies the\n\
                 ; original is unsat, but `sat` here is INCONCLUSIVE.\n",
            );
            for name in &datatype_sorts {
                out.push_str(&format!(";   datatype sort: {}\n", quote_symbol(name)));
            }
        }
        out.push_str("(set-option :produce-unsat-cores true)\n(set-logic ALL)\n");
        // Self-containment (#dump-self-contained): every uninterpreted sort
        // referenced by a declaration or an assertion term must be declared,
        // or the script is unusable as a standalone repro (neither ay's own
        // parser nor z3 accepts an undeclared sort name).
        for name in plain_sorts.iter().chain(datatype_sorts.iter()) {
            out.push_str(&format!("(declare-sort {} 0)\n", quote_symbol(name)));
        }
        let mut declared: std::collections::HashSet<String> = std::collections::HashSet::new();
        for (name, info) in self.ctx.symbols_iter() {
            // A native theory constructor is an App(Named(..)) in the core
            // DAG, but it is not a user declaration.  Public declaration
            // paths reject these names; keep the serializer fail-closed if a
            // trusted/internal path nevertheless registered one.
            if ay_frontend::is_reserved_op_name(name) {
                continue;
            }
            declared.insert(name.to_string());
            if info.arg_sorts.is_empty() {
                out.push_str(&format!(
                    "(declare-const {} {})\n",
                    quote_symbol(name),
                    format_sort(&info.sort)
                ));
            } else {
                let args: Vec<String> = info.arg_sorts.iter().map(format_sort).collect();
                out.push_str(&format!(
                    "(declare-fun {} ({}) {})\n",
                    quote_symbol(name),
                    args.join(" "),
                    format_sort(&info.sort)
                ));
            }
        }
        let mut extra: Vec<String> = Vec::new();
        for &a in assertions {
            self.collect_undeclared_symbol_decls(a, &mut declared, &mut extra);
        }
        for decl in extra {
            out.push_str(&decl);
        }
        for (i, &a) in assertions.iter().enumerate() {
            out.push_str(&format!(
                "(assert (! {} :named dn{}))\n",
                self.format_term(a),
                i
            ));
        }
        out.push_str("(check-sat)\n");
        out
    }

    /// Serialize an explicit assertion list in the shape Z3's
    /// `Z3_solver_to_string` (and z3py's `Solver.sexpr()`) prints: one
    /// `(declare-fun NAME (ARGSORTS) RANGE)` line per declared symbol followed
    /// by one `(assert TERM)` line per assertion — with no
    /// `set-option`/`set-logic`/`check-sat` wrapper and no `:named`
    /// annotations. This is a faithful dump of the given assertions (never
    /// fabricated); see [`Self::to_smtlib2_for`] for the self-contained,
    /// re-parseable variant used by the transpose path.
    ///
    /// The caller supplies the assertion list because the Z3-compat FFI holds
    /// its live assertions on the per-solver handle, not on the executor's
    /// internal stack (which is only populated transiently at check time).
    pub(crate) fn assertions_sexpr_for(&self, assertions: &[TermId]) -> String {
        let mut out = String::new();
        let mut declared: std::collections::HashSet<String> = std::collections::HashSet::new();
        // Z3 declares every symbol — including 0-arity constants — with
        // `declare-fun` (e.g. `(declare-fun x () Int)`), so match that shape.
        for (name, info) in self.ctx.symbols_iter() {
            if ay_frontend::is_reserved_op_name(name) {
                continue;
            }
            declared.insert(name.to_string());
            let args: Vec<String> = info.arg_sorts.iter().map(format_sort).collect();
            out.push_str(&format!(
                "(declare-fun {} ({}) {})\n",
                quote_symbol(name),
                args.join(" "),
                format_sort(&info.sort)
            ));
        }
        let mut extra: Vec<String> = Vec::new();
        for &a in assertions {
            self.collect_undeclared_symbol_decls(a, &mut declared, &mut extra);
        }
        for decl in extra {
            out.push_str(&decl);
        }
        for &a in assertions {
            out.push_str(&format!("(assert {})\n", self.format_term(a)));
        }
        out
    }

    fn collect_undeclared_symbol_decls(
        &self,
        term_id: TermId,
        declared: &mut std::collections::HashSet<String>,
        out: &mut Vec<String>,
    ) {
        self.collect_undeclared_symbol_decls_with_bindings(
            term_id,
            declared,
            out,
            &std::collections::HashSet::new(),
        );
    }

    fn collect_undeclared_symbol_decls_with_bindings(
        &self,
        term_id: TermId,
        declared: &mut std::collections::HashSet<String>,
        out: &mut Vec<String>,
        bound: &std::collections::HashSet<String>,
    ) {
        use ay_core::term::Symbol;
        match self.ctx.terms.get(term_id) {
            TermData::App(Symbol::Named(name), args) => {
                let surface_name = self.ctx.dt_surface_name(name).unwrap_or(name);
                if !declared.contains(surface_name) && !is_builtin_operator(name) {
                    declared.insert(surface_name.to_string());
                    let res_sort = format_sort(self.ctx.terms.sort(term_id));
                    if args.is_empty() {
                        out.push(format!(
                            "(declare-const {} {})\n",
                            quote_symbol(surface_name),
                            res_sort
                        ));
                    } else {
                        let arg_sorts: Vec<String> = args
                            .iter()
                            .map(|&a| format_sort(self.ctx.terms.sort(a)))
                            .collect();
                        out.push(format!(
                            "(declare-fun {} ({}) {})\n",
                            quote_symbol(surface_name),
                            arg_sorts.join(" "),
                            res_sort
                        ));
                    }
                }
                for &a in args {
                    self.collect_undeclared_symbol_decls_with_bindings(a, declared, out, bound);
                }
            }
            TermData::App(_, args) => {
                for &a in args {
                    self.collect_undeclared_symbol_decls_with_bindings(a, declared, out, bound);
                }
            }
            TermData::Not(inner) => {
                self.collect_undeclared_symbol_decls_with_bindings(*inner, declared, out, bound)
            }
            TermData::Ite(c, t, e) => {
                self.collect_undeclared_symbol_decls_with_bindings(*c, declared, out, bound);
                self.collect_undeclared_symbol_decls_with_bindings(*t, declared, out, bound);
                self.collect_undeclared_symbol_decls_with_bindings(*e, declared, out, bound);
            }
            TermData::Forall(vars, body, triggers) | TermData::Exists(vars, body, triggers) => {
                let mut nested_bound = bound.clone();
                nested_bound.extend(vars.iter().map(|(name, _)| name.clone()));
                self.collect_undeclared_symbol_decls_with_bindings(
                    *body,
                    declared,
                    out,
                    &nested_bound,
                );
                for trig_set in triggers {
                    for &t in trig_set {
                        self.collect_undeclared_symbol_decls_with_bindings(
                            t,
                            declared,
                            out,
                            &nested_bound,
                        );
                    }
                }
            }
            TermData::Let(bindings, body) => {
                for (_, t) in bindings {
                    // SMT-LIB `let` bindings are simultaneous: each right-hand
                    // side is evaluated outside the new binder scope.
                    self.collect_undeclared_symbol_decls_with_bindings(*t, declared, out, bound);
                }
                let mut nested_bound = bound.clone();
                nested_bound.extend(bindings.iter().map(|(name, _)| name.clone()));
                self.collect_undeclared_symbol_decls_with_bindings(
                    *body,
                    declared,
                    out,
                    &nested_bound,
                );
            }
            TermData::Var(name, _) => {
                // Programmatic callers can intentionally create a free
                // `fresh_var` without registering it for model extraction.
                // It is still a free constant in the formula and must be
                // declared in a self-contained dump. Quantifier/let binders
                // are tracked lexically above and must not leak out as global
                // declarations.
                if !bound.contains(name)
                    && !declared.contains(name)
                    && !ay_frontend::is_reserved_symbol(name)
                {
                    declared.insert(name.clone());
                    out.push(format!(
                        "(declare-const {} {})\n",
                        quote_symbol(name),
                        format_sort(self.ctx.terms.sort(term_id))
                    ));
                }
            }
            TermData::Const(_) => {}
            _ => {}
        }
    }

    /// Collect the names of every uninterpreted sort referenced by the current
    /// declarations or by the given assertion terms (including quantifier
    /// bound-variable sorts and sorts nested inside `Array`/`Seq`), split into
    /// (plain uninterpreted, datatype-backed) name sets. Datatype-backed names
    /// are the term-level `Sort::Uninterpreted` carriers of declared datatypes
    /// (`as_term_sort` lowers `Sort::Datatype(dt)` to `Uninterpreted(dt.name)`);
    /// serializing them as `declare-sort` loses constructor semantics, so the
    /// caller marks those scripts fail-visible. (#dump-self-contained)
    fn referenced_uninterpreted_sorts(
        &self,
        assertions: &[TermId],
    ) -> (
        std::collections::BTreeSet<String>,
        std::collections::BTreeSet<String>,
    ) {
        let mut names = std::collections::BTreeSet::new();
        for (_, info) in self.ctx.symbols_iter() {
            collect_uninterpreted_sort_names(&info.sort, &mut names);
            for s in &info.arg_sorts {
                collect_uninterpreted_sort_names(s, &mut names);
            }
        }
        let mut visited = std::collections::HashSet::new();
        for &a in assertions {
            self.collect_term_sort_names(a, &mut visited, &mut names);
        }
        let datatype_names: std::collections::HashSet<&str> =
            self.ctx.datatype_iter().map(|(name, _)| name).collect();
        let (datatype_backed, plain) = names
            .into_iter()
            .partition(|n| datatype_names.contains(n.as_str()));
        (plain, datatype_backed)
    }

    /// Walk a term DAG and collect uninterpreted-sort names from every
    /// subterm's sort (plus quantifier binder sorts). The visited set keys on
    /// `TermId` (terms are hash-consed), keeping the walk linear in DAG size.
    fn collect_term_sort_names(
        &self,
        term_id: TermId,
        visited: &mut std::collections::HashSet<TermId>,
        out: &mut std::collections::BTreeSet<String>,
    ) {
        if !visited.insert(term_id) {
            return;
        }
        collect_uninterpreted_sort_names(self.ctx.terms.sort(term_id), out);
        match self.ctx.terms.get(term_id) {
            TermData::App(_, args) => {
                for &a in args {
                    self.collect_term_sort_names(a, visited, out);
                }
            }
            TermData::Not(inner) => self.collect_term_sort_names(*inner, visited, out),
            TermData::Ite(c, t, e) => {
                self.collect_term_sort_names(*c, visited, out);
                self.collect_term_sort_names(*t, visited, out);
                self.collect_term_sort_names(*e, visited, out);
            }
            TermData::Forall(vars, body, triggers) | TermData::Exists(vars, body, triggers) => {
                for (_, sort) in vars {
                    collect_uninterpreted_sort_names(sort, out);
                }
                self.collect_term_sort_names(*body, visited, out);
                for trig_set in triggers {
                    for &t in trig_set {
                        self.collect_term_sort_names(t, visited, out);
                    }
                }
            }
            TermData::Let(bindings, body) => {
                for (_, t) in bindings {
                    self.collect_term_sort_names(*t, visited, out);
                }
                self.collect_term_sort_names(*body, visited, out);
            }
            TermData::Const(_) | TermData::Var(_, _) => {}
            _ => {}
        }
    }

    /// Simplify a term and return its SMT-LIB representation
    ///
    /// The term is already simplified during elaboration (by the TermStore),
    /// so this just formats the already-simplified term.
    pub(super) fn simplify(&self, term_id: TermId) -> String {
        self.format_term(term_id)
    }

    /// Format a term for SMT-LIB output (reconstructs the expression)
    pub(crate) fn format_term(&self, term_id: TermId) -> String {
        let term = self.ctx.terms.get(term_id);
        match term {
            // Un-mangle instance-specific datatype member names (e.g.
            // `osome@Opt!{Int}` -> `osome`) for user-facing `(get-value ...)`/`eval`
            // echo; non-datatype symbols are returned unchanged.
            TermData::Var(name, _) => {
                self.format_declared_symbol_identity(name, self.ctx.terms.sort(term_id))
            }
            TermData::Const(Constant::Bool(true)) => "true".to_string(),
            TermData::Const(Constant::Bool(false)) => "false".to_string(),
            TermData::Const(Constant::Int(n)) => format_bigint(n),
            TermData::Const(Constant::Rational(r)) => format_rational(&r.0),
            TermData::Const(Constant::String(s)) => string_literal(s),
            // A BV numeral's printed form encodes its width, so this MUST go
            // through the canonical printer: `#x` is well-formed only at widths
            // that are a multiple of 4. Open-coding hex here (with a
            // `div_ceil(4)` digit count) printed e.g. a `(_ BitVec 5)` value 17
            // as `#x11`, which reparses as `(_ BitVec 8)`. This is the printer
            // behind the Z3-compat C API's `Z3_ast_to_string`.
            TermData::Const(Constant::BitVec { value, width }) => {
                crate::executor_format::format_bitvec(value, *width)
            }
            TermData::Not(inner) => format!("(not {})", self.format_term(*inner)),
            TermData::Ite(cond, then_br, else_br) => format!(
                "(ite {} {} {})",
                self.format_term(*cond),
                self.format_term(*then_br),
                self.format_term(*else_br)
            ),
            TermData::App(sym, args) => {
                // Constant arrays have a named internal application node so
                // the array theory can match them structurally.  SMT-LIB's
                // portable surface form is a qualified `const` identifier,
                // not `(const-array value)` and never a declared user
                // function.  Include the result sort to make the index sort
                // explicit and keep dumps accepted by AY and external SMT-LIB
                // consumers.
                if let (Symbol::Named(n), [value]) = (sym, args.as_slice()) {
                    if n == "const-array" && matches!(self.ctx.terms.sort(term_id), Sort::Array(_))
                    {
                        return format!(
                            "((as const {}) {})",
                            format_sort(self.ctx.terms.sort(term_id)),
                            self.format_term(*value)
                        );
                    }
                }
                // Lambda arrays are stored internally as
                // `App("lambda-array", [var, body])`; print the SMT-LIB/z3
                // standard binder shape `(lambda ((x S)) body)` (multi-arg
                // lambdas are curried, so they print as nested binders).
                if let (Symbol::Named(n), [var, body]) = (sym, args.as_slice()) {
                    if n == "lambda-array" {
                        if let TermData::Var(vname, _) = self.ctx.terms.get(*var) {
                            return format!(
                                "(lambda (({} {})) {})",
                                quote_symbol(vname),
                                format_sort(self.ctx.terms.sort(*var)),
                                self.format_term(*body)
                            );
                        }
                    }
                }
                let name = match sym {
                    Symbol::Named(n) => {
                        self.format_declared_symbol_identity(n, self.ctx.terms.sort(term_id))
                    }
                    _ => format_symbol(sym),
                };
                if args.is_empty() {
                    name
                } else {
                    let args_str: Vec<String> = args.iter().map(|&a| self.format_term(a)).collect();
                    format!("({} {})", name, args_str.join(" "))
                }
            }
            TermData::Let(bindings, body) => {
                // Let bindings should normally be expanded, but format just in case
                let bindings_str: Vec<String> = bindings
                    .iter()
                    .map(|(name, term)| {
                        format!("({} {})", quote_symbol(name), self.format_term(*term))
                    })
                    .collect();
                format!(
                    "(let ({}) {})",
                    bindings_str.join(" "),
                    self.format_term(*body)
                )
            }
            TermData::Forall(vars, body, _triggers) => {
                let vars_str: Vec<String> = vars
                    .iter()
                    .map(|(name, sort)| format!("({} {})", quote_symbol(name), format_sort(sort)))
                    .collect();
                format!(
                    "(forall ({}) {})",
                    vars_str.join(" "),
                    self.format_term(*body)
                )
            }
            TermData::Exists(vars, body, _triggers) => {
                let vars_str: Vec<String> = vars
                    .iter()
                    .map(|(name, sort)| format!("({} {})", quote_symbol(name), format_sort(sort)))
                    .collect();
                format!(
                    "(exists ({}) {})",
                    vars_str.join(" "),
                    self.format_term(*body)
                )
            }
            // All current TermData variants are handled above.
            // This arm is required by #[non_exhaustive] and catches future variants.
            other => unreachable!("unhandled TermData variant in format_term(): {other:?}"),
        }
    }

    /// Check if produce-assignments option is enabled
    pub(super) fn produce_assignments_enabled(&self) -> bool {
        matches!(
            self.ctx.get_option("produce-assignments"),
            Some(OptionValue::Bool(true))
        )
    }

    /// Check if produce-unsat-cores option is enabled
    pub(super) fn produce_unsat_cores_enabled(&self) -> bool {
        matches!(
            self.ctx.get_option("produce-unsat-cores"),
            Some(OptionValue::Bool(true))
        )
    }

    /// Get assignment of named formulas (get-assignment command)
    ///
    /// Returns the truth values of all named Boolean formulas.
    pub(super) fn get_assignment(&self) -> String {
        // Check that produce-assignments is enabled
        if !self.produce_assignments_enabled() {
            return "(error \"assignment generation is not enabled, set :produce-assignments to true\")".to_string();
        }

        // Check if we have a model
        let model = match (&self.last_result, &self.last_model) {
            (Some(SolveResult::Sat), Some(m)) => m,
            (Some(SolveResult::Sat), None) => {
                // SAT with no model (trivially satisfiable, no named terms to evaluate)
                return "()".to_string();
            }
            (Some(SolveResult::Unknown), _) => {
                // Unknown - still allowed, return assignment if available
                if let Some(m) = &self.last_model {
                    m
                } else {
                    return "()".to_string();
                }
            }
            _ => {
                return "(error \"assignment is not available\")".to_string();
            }
        };

        // Collect assignments for named terms
        let mut assignments = Vec::new();
        for (name, term_id) in self.ctx.named_terms_iter() {
            let value = self.evaluate_term(model, term_id);
            if let EvalValue::Bool(b) = value {
                assignments.push(format!("({} {})", quote_symbol(name), b));
            }
        }

        if assignments.is_empty() {
            "()".to_string()
        } else {
            format!("({})", assignments.join("\n "))
        }
    }

    /// Compute implied consequences (`get-consequences` command).
    ///
    /// Given background `assumptions` and a list of candidate literals
    /// (`variables`), returns the subset of candidates entailed by
    /// `assertions /\ assumptions`. A literal `L` is reported as a consequence
    /// exactly when `assertions /\ assumptions /\ ~L` is UNSAT — proven here by
    /// a `check-sat-assuming` of the assumptions plus `~L`.
    ///
    /// Soundness: a literal is emitted **only** when that entailment check is
    /// genuinely UNSAT. If the check is SAT (a counter-model exists) or
    /// `unknown` (undetermined), the literal is omitted. This is a sound
    /// under-approximation — every emitted literal is a true consequence, and
    /// no non-consequence is ever reported.
    ///
    /// Output format follows Z3: `(<status> (<consequence>+))`, where `status`
    /// is the satisfiability of `assertions /\ assumptions` and each
    /// consequence is rendered as `(=> (and <assumptions>) <literal>)` (or
    /// simply `<literal>` when there are no assumptions). If the base context is
    /// already unsatisfiable the result is `(unsat ())`.
    pub(crate) fn get_consequences(
        &mut self,
        assumptions: &[TermId],
        variables: &[TermId],
    ) -> crate::executor_types::Result<String> {
        // Preserve the post-check-sat state so a following get-value/get-model
        // still observes the original model. The repeated check-sat-assuming
        // calls below overwrite last_result/last_model/last_assumptions.
        //
        // SOUNDNESS (#unsat-core-staleness): the core provenance fields
        // (`last_assumption_core`, `last_core_term_to_name`) MUST be part of
        // this snapshot. The internal probes below run against the FULL base
        // (named assertions included) and overwrite the harvest; restoring
        // `last_result`/`last_assumptions` without them let a later
        // (get-unsat-core) print the PROBE's harvest against the ORIGINAL
        // check's name snapshot — a satisfiable set passed the membership
        // authentication because staleness, not membership, was the defect.
        let saved_result = self.last_result.clone();
        let saved_model = self.last_model.clone();
        let saved_assumptions = self.last_assumptions.clone();
        let saved_validated = self.last_model_validated;
        let saved_assumption_core = self.last_assumption_core.clone();
        let saved_core_term_to_name = self.last_core_term_to_name.clone();
        // Proof artifacts are one coherent snapshot: a probe proof must never
        // be paired with the restored result/assumption scope from the public
        // query. `check_sat_assuming` clears or replaces every field below.
        let saved_proof = self.last_proof.take();
        let saved_lrat_certificate = self.last_lrat_certificate.take();
        let saved_proof_term_overrides = self.last_proof_term_overrides.take();
        let saved_proof_quality = self.last_proof_quality.take();
        let saved_proof_rebuild_originals = std::mem::take(&mut self.last_proof_rebuild_originals);
        let saved_clause_trace = self.last_clause_trace.take();
        let saved_var_to_term = self.last_var_to_term.take();
        let saved_trail_provenance = self.last_trail_provenance.take();
        let saved_clausification_proofs = self.last_clausification_proofs.take();
        let saved_original_clause_theory_proofs = self.last_original_clause_theory_proofs.take();
        let saved_quant_expansion_records = std::mem::take(&mut self.quant_expansion_records);
        let saved_ematching_proof_records = std::mem::take(&mut self.ematching_proof_records);
        let saved_proof_check_result = self.proof_check_result.take();
        let saved_proof_check_ok = self.proof_check_ok;
        let saved_proof_problem_assertion_provenance =
            self.proof_problem_assertion_provenance.clone();

        let outcome = self.get_consequences_inner(assumptions, variables);

        // Restore regardless of success/failure.
        self.last_result = saved_result;
        self.last_model = saved_model;
        self.last_assumptions = saved_assumptions;
        self.last_model_validated = saved_validated;
        self.last_assumption_core = saved_assumption_core;
        self.last_core_term_to_name = saved_core_term_to_name;
        self.last_proof = saved_proof;
        self.last_lrat_certificate = saved_lrat_certificate;
        self.last_proof_term_overrides = saved_proof_term_overrides;
        self.last_proof_quality = saved_proof_quality;
        self.last_proof_rebuild_originals = saved_proof_rebuild_originals;
        self.last_clause_trace = saved_clause_trace;
        self.last_var_to_term = saved_var_to_term;
        self.last_trail_provenance = saved_trail_provenance;
        self.last_clausification_proofs = saved_clausification_proofs;
        self.last_original_clause_theory_proofs = saved_original_clause_theory_proofs;
        self.quant_expansion_records = saved_quant_expansion_records;
        self.ematching_proof_records = saved_ematching_proof_records;
        self.proof_check_result = saved_proof_check_result;
        self.proof_check_ok = saved_proof_check_ok;
        self.proof_problem_assertion_provenance = saved_proof_problem_assertion_provenance;

        outcome
    }

    fn get_consequences_inner(
        &mut self,
        assumptions: &[TermId],
        variables: &[TermId],
    ) -> crate::executor_types::Result<String> {
        // Establish the base status: is `assertions /\ assumptions` satisfiable?
        let base = self.check_sat_assuming(assumptions)?;
        let status = match base {
            SolveResult::Sat => "sat",
            SolveResult::Unsat(_) => {
                // An unsatisfiable base entails everything, but Z3 reports an
                // empty consequence list in this case.
                return Ok("(unsat ())".to_string());
            }
            SolveResult::Unknown => "unknown",
        };

        // Render the antecedent `(and <assumptions>)` once, reused per literal.
        let antecedent = if assumptions.is_empty() {
            None
        } else if assumptions.len() == 1 {
            Some(self.format_term(assumptions[0]))
        } else {
            let parts: Vec<String> = assumptions.iter().map(|&a| self.format_term(a)).collect();
            Some(format!("(and {})", parts.join(" ")))
        };

        let mut consequences = Vec::new();
        for &lit in variables {
            // Build `~lit` and test `assertions /\ assumptions /\ ~lit`.
            // UNSAT means `lit` is entailed; SAT/Unknown means it is not
            // (soundly) provable, so it is omitted.
            let neg = self.ctx.terms.mk_not(lit);
            let mut combined: Vec<TermId> = assumptions.to_vec();
            combined.push(neg);
            let entailment = self.check_sat_assuming(&combined)?;
            if matches!(entailment, SolveResult::Unsat(_)) {
                let lit_str = self.format_term(lit);
                let rendered = match &antecedent {
                    Some(ante) => format!("(=> {ante} {lit_str})"),
                    None => lit_str,
                };
                consequences.push(rendered);
            }
        }

        if consequences.is_empty() {
            Ok(format!("({status} ())"))
        } else {
            Ok(format!("({status} ({}))", consequences.join(" ")))
        }
    }

    /// Synthesize an abduct for `(get-abduct <name> <goal>)`.
    ///
    /// Given the current background assertions `A` (the executor's asserted
    /// formulas) and a Boolean goal `G`, find a formula `C` such that:
    ///   1. `A /\ C` is satisfiable, AND
    ///   2. `A /\ C => G`   (equivalently `A /\ C /\ not G` is unsatisfiable).
    ///
    /// SOUNDNESS: every emitted abduct is *validated* with AY's own solver
    /// before it is printed — both conditions above are checked by sub-solves.
    /// If no candidate from the internal grammar validates, AY prints the
    /// SMT-LIB-standard `none` failure rather than an unsound abduct
    /// (fail-closed). Candidates are drawn from a fixed grammar over the atoms
    /// already appearing in `A` and `G`, their negations, the goal itself, and
    /// pairwise conjunctions — never invented vocabulary.
    ///
    /// Output format matches cvc5 / the SMT-LIB abduction extension:
    /// `(define-fun <name> () Bool <C>)`, or `none` on failure.
    pub(crate) fn get_abduct(
        &mut self,
        name: &str,
        goal: TermId,
    ) -> crate::executor_types::Result<String> {
        // Preserve post-check-sat state: the validating sub-solves below call
        // check_sat_assuming repeatedly and would otherwise clobber the model a
        // following get-value / get-model expects.
        //
        // SOUNDNESS (#unsat-core-staleness): the core provenance fields are
        // part of the snapshot for the same reason as in `get_consequences`
        // — an internal probe's harvest must never be printable as the
        // original check's core.
        let saved_result = self.last_result.clone();
        let saved_model = self.last_model.clone();
        let saved_assumptions = self.last_assumptions.clone();
        let saved_validated = self.last_model_validated;
        let saved_assumption_core = self.last_assumption_core.clone();
        let saved_core_term_to_name = self.last_core_term_to_name.clone();
        let saved_proof = self.last_proof.take();
        let saved_lrat_certificate = self.last_lrat_certificate.take();
        let saved_proof_term_overrides = self.last_proof_term_overrides.take();
        let saved_proof_quality = self.last_proof_quality.take();
        let saved_proof_rebuild_originals = std::mem::take(&mut self.last_proof_rebuild_originals);
        let saved_clause_trace = self.last_clause_trace.take();
        let saved_var_to_term = self.last_var_to_term.take();
        let saved_trail_provenance = self.last_trail_provenance.take();
        let saved_clausification_proofs = self.last_clausification_proofs.take();
        let saved_original_clause_theory_proofs = self.last_original_clause_theory_proofs.take();
        let saved_quant_expansion_records = std::mem::take(&mut self.quant_expansion_records);
        let saved_ematching_proof_records = std::mem::take(&mut self.ematching_proof_records);
        let saved_proof_check_result = self.proof_check_result.take();
        let saved_proof_check_ok = self.proof_check_ok;
        let saved_proof_problem_assertion_provenance =
            self.proof_problem_assertion_provenance.clone();

        let outcome = self.get_abduct_inner(name, goal);

        self.last_result = saved_result;
        self.last_model = saved_model;
        self.last_assumptions = saved_assumptions;
        self.last_model_validated = saved_validated;
        self.last_assumption_core = saved_assumption_core;
        self.last_core_term_to_name = saved_core_term_to_name;
        self.last_proof = saved_proof;
        self.last_lrat_certificate = saved_lrat_certificate;
        self.last_proof_term_overrides = saved_proof_term_overrides;
        self.last_proof_quality = saved_proof_quality;
        self.last_proof_rebuild_originals = saved_proof_rebuild_originals;
        self.last_clause_trace = saved_clause_trace;
        self.last_var_to_term = saved_var_to_term;
        self.last_trail_provenance = saved_trail_provenance;
        self.last_clausification_proofs = saved_clausification_proofs;
        self.last_original_clause_theory_proofs = saved_original_clause_theory_proofs;
        self.quant_expansion_records = saved_quant_expansion_records;
        self.ematching_proof_records = saved_ematching_proof_records;
        self.proof_check_result = saved_proof_check_result;
        self.proof_check_ok = saved_proof_check_ok;
        self.proof_problem_assertion_provenance = saved_proof_problem_assertion_provenance;

        outcome
    }

    fn get_abduct_inner(
        &mut self,
        name: &str,
        goal: TermId,
    ) -> crate::executor_types::Result<String> {
        // The goal must be Bool — otherwise the request is malformed and we
        // fail closed.
        if !matches!(self.ctx.terms.sort(goal), Sort::Bool) {
            return Ok("none".to_string());
        }

        let not_goal = self.ctx.terms.mk_not(goal);

        // Build the ordered list of candidate abducts C. Candidates are
        // PROPOSED here but only ACCEPTED after validation below, so an overly
        // generous grammar can never produce an unsound result.
        let candidates = self.abduct_candidates(goal);

        for cand in candidates {
            // Reject the degenerate `false` candidate up front: `A /\ false` is
            // always UNSAT, so it can never be a valid abduct (it would fail the
            // SAT check anyway, but skipping avoids a wasted solve).
            if matches!(
                self.ctx.terms.get(cand),
                TermData::Const(Constant::Bool(false))
            ) {
                continue;
            }

            // Condition 1: A /\ C must be SATISFIABLE.
            let sat_ac = self.check_sat_assuming(&[cand])?;
            if !matches!(sat_ac, SolveResult::Sat) {
                // Not SAT (unsat or unknown) — cannot soundly accept.
                continue;
            }

            // Condition 2: A /\ C /\ not G must be UNSATISFIABLE
            // (i.e. A /\ C => G).
            let entail = self.check_sat_assuming(&[cand, not_goal])?;
            if !matches!(entail, SolveResult::Unsat(_)) {
                continue;
            }

            // Both conditions VALIDATED by AY's own solver — emit the abduct.
            let body = self.format_term(cand);
            return Ok(format!(
                "(define-fun {} () Bool {})",
                quote_symbol(name),
                body
            ));
        }

        // No candidate validated — fail closed with the standard failure token.
        Ok("none".to_string())
    }

    /// Build the ordered candidate-abduct grammar for `goal`.
    ///
    /// Ordering favors *weaker* / simpler candidates first (single atoms before
    /// the whole goal before conjunctions), mirroring abduction tools that
    /// prefer the least-committing explanation. Every candidate is over symbols
    /// already present in the assertions / goal; none are validated here (the
    /// caller validates each before emitting).
    fn abduct_candidates(&mut self, goal: TermId) -> Vec<TermId> {
        // Collect Boolean theory atoms from the goal and current assertions.
        let mut atoms: Vec<TermId> = Vec::new();
        let mut seen: std::collections::HashSet<TermId> = std::collections::HashSet::new();
        self.collect_bool_atoms(goal, &mut atoms, &mut seen);
        let assertion_roots: Vec<TermId> = self.ctx.assertions.clone();
        for root in assertion_roots {
            self.collect_bool_atoms(root, &mut atoms, &mut seen);
        }

        let mut candidates: Vec<TermId> = Vec::new();
        let mut cand_seen: std::collections::HashSet<TermId> = std::collections::HashSet::new();
        let mut push = |c: TermId, candidates: &mut Vec<TermId>| {
            if cand_seen.insert(c) {
                candidates.push(c);
            }
        };

        // 1. Each collected atom, then its negation.
        for &a in &atoms {
            push(a, &mut candidates);
            let neg = self.ctx.terms.mk_not(a);
            push(neg, &mut candidates);
        }

        // 2. The goal itself (always a SOUND abduct when A /\ G is SAT, since
        //    G => G trivially). This guarantees we find *some* abduct whenever
        //    one over the goal's vocabulary exists.
        push(goal, &mut candidates);

        // 3. Pairwise conjunctions of distinct atoms (bounded to keep the search
        //    small). Useful when no single atom suffices.
        const MAX_PAIR_ATOMS: usize = 8;
        let n = atoms.len().min(MAX_PAIR_ATOMS);
        for i in 0..n {
            for j in (i + 1)..n {
                let conj = self.ctx.terms.mk_and(vec![atoms[i], atoms[j]]);
                push(conj, &mut candidates);
            }
        }

        candidates
    }

    /// Collect Boolean *atoms* reachable from `term` into `out`.
    ///
    /// An atom is a Bool-sorted sub-term that is NOT a top-level Boolean
    /// connective (not / and / or / => / xor / ite-over-Bool / quantifier) —
    /// i.e. a theory predicate (`(> x 0)`, `(= a b)`) or a Boolean variable.
    /// Connectives are recursed into so their leaf atoms are gathered. This is a
    /// purely syntactic harvest; soundness comes from validating each derived
    /// candidate, so over- or under-collecting only affects completeness.
    fn collect_bool_atoms(
        &self,
        term: TermId,
        out: &mut Vec<TermId>,
        seen: &mut std::collections::HashSet<TermId>,
    ) {
        if !seen.insert(term) {
            return;
        }
        // Only Bool-sorted terms can be atoms or connectives we care about.
        if !matches!(self.ctx.terms.sort(term), Sort::Bool) {
            return;
        }
        match self.ctx.terms.get(term) {
            TermData::Not(inner) => {
                let inner = *inner;
                self.collect_bool_atoms(inner, out, seen);
            }
            TermData::Ite(c, t, e) => {
                let (c, t, e) = (*c, *t, *e);
                self.collect_bool_atoms(c, out, seen);
                self.collect_bool_atoms(t, out, seen);
                self.collect_bool_atoms(e, out, seen);
            }
            TermData::App(sym, args) => {
                let is_connective = matches!(sym.name(), "and" | "or" | "=>" | "xor" | "not")
                    || (sym.name() == "="
                        && args
                            .iter()
                            .all(|&a| matches!(self.ctx.terms.sort(a), Sort::Bool)));
                if is_connective {
                    let args = args.clone();
                    for a in args {
                        self.collect_bool_atoms(a, out, seen);
                    }
                } else {
                    // Theory predicate or Boolean variable/constant — an atom.
                    // Skip the literal constants true/false; they are useless as
                    // standalone abducts.
                    out.push(term);
                }
            }
            TermData::Var(_, _) => {
                out.push(term);
            }
            TermData::Const(Constant::Bool(_)) => {
                // true / false: not useful standalone atoms; ignore.
            }
            _ => {}
        }
    }

    /// Compute the printable UNSAT-core entries as `(optional-name, term)`
    /// pairs (#unsat-core-assumptions).
    ///
    /// SOUNDNESS CONTRACT: the printed core, conjoined with the UNNAMED
    /// asserted formulas alone, must be unsatisfiable. Two rules enforce it:
    ///
    /// 1. AUTHENTICATE-OR-PAD. Every harvested core member must be a term the
    ///    check actually assumption-tracked: a named assertion (check-time
    ///    snapshot in `last_core_term_to_name`) or an assumption literal of
    ///    the last check (`last_assumptions`). If any member is unknown (a
    ///    contract violation that debug builds assert away, but which must
    ///    never print an internal/rewritten term in release), or the
    ///    harvested core is empty or absent, fall back to the conservative
    ///    padded superset: all currently named assertions plus all assumption
    ///    literals of the last check, deduplicated by `TermId`. The padded
    ///    set is always sound -- it is exactly the checked set minus the
    ///    unnamed assertions. Members are never silently dropped.
    ///
    ///    An EMPTY harvested core is padded too: theory paths can prove UNSAT
    ///    while failing to surface failed assumptions (e.g. a theory-level
    ///    conflict that never registers assumption participation -- the EUF
    ///    a=b,b=c,a!=c refutation carries an EMPTY SAT-level core even though
    ///    every named premise is load-bearing), and `Some([])` carries no
    ///    origin tag distinguishing that lost-provenance case from a genuine
    ///    "the unnamed assertions alone are unsat" core. z3 prints `()` for
    ///    the genuine case; AY deliberately prints the sound superset instead
    ///    (a deliberate parity exception: soundness first). CONSUMER WARNING:
    ///    this padding means name-in-core is NOT evidence the assertion was
    ///    load-bearing; verifier vacuity detection MUST NOT trust the core
    ///    alone and must base-recheck (assert the base without the negated
    ///    goal and check SAT) before accepting a proof as non-vacuous.
    ///    verification-consumer does this on its solve paths. An honest empty core would
    ///    need origin-tagged authority (SAT-level failed-assumption harvest
    ///    vs theory-level conflict) -- future work.
    ///
    /// 2. NAME-OR-VERBATIM (applied by the callers). An entry with a `:named`
    ///    label (check-time snapshot first, live named map as fallback)
    ///    prints as the label; any other entry prints as the verbatim term
    ///    text -- matching z3, which mixes labels and assumption terms in one
    ///    flat list.
    fn unsat_core_entries(&self) -> Vec<(Option<String>, TermId)> {
        let snapshot = self.last_core_term_to_name.as_ref();
        let assumptions: &[TermId] = self.last_assumptions.as_deref().unwrap_or(&[]);

        // Name lookup: check-time snapshot first (popped names must not leak
        // into a still-valid core), live named map as fallback (covers an
        // assumption literal that happens to coincide with a named assertion
        // when no snapshot was taken).
        let name_of = |tid: TermId| -> Option<String> {
            if let Some(map) = snapshot {
                if let Some(name) = map.get(&tid) {
                    return Some(name.clone());
                }
            }
            self.ctx
                .named_terms_iter()
                .find(|(_, t)| *t == tid)
                .map(|(name, _)| name.to_string())
        };

        if let Some(core_terms) = &self.last_assumption_core {
            // Print-time authentication (release-mode guard, mirrors the
            // authenticate-or-bail pattern of the MaxSMT disjoint-core loop):
            // only terms the check assumption-tracked may be printed.
            let authenticated = core_terms.iter().all(|tid| {
                snapshot.is_some_and(|map| map.contains_key(tid)) || assumptions.contains(tid)
            });
            if authenticated && !core_terms.is_empty() {
                // TermId dedup (#uc-core-dedup): hash-consed duplicate assert
                // bodies share one TermId, and the harvest can surface that
                // TermId more than once (duplicate asserted formulas encode to
                // the same SAT literal). `term_to_name` keeps one label per
                // TermId, so without dedup the SAME label printed N times —
                // inflating |core| under 2025 UC scoring and printing a
                // malformed duplicate-entry core. First occurrence wins
                // (deterministic: core order is solver-derived, itself
                // deterministic).
                let mut seen: std::collections::HashSet<TermId> = std::collections::HashSet::new();
                return core_terms
                    .iter()
                    .filter(|&&tid| seen.insert(tid))
                    .map(|&tid| (name_of(tid), tid))
                    .collect();
            }
        }

        // Conservative padded superset (rule 1 above): all named assertions
        // plus all assumption literals of the last check. On the plain
        // check-sat redirect `last_assumptions` IS the named set, so the
        // dedup keeps this byte-identical to the historical all-named
        // fallback; after a plain check-sat without assumptions it reduces
        // to exactly the historical all-named fallback.
        //
        // TermId dedup applies to the named entries too (#uc-core-dedup): two
        // `:named` labels on hash-consed-identical assert bodies share one
        // TermId; printing one label suffices (the printed core denotes the
        // same conjunction) and keeps |core| honest. First label wins.
        let mut seen: std::collections::HashSet<TermId> = std::collections::HashSet::new();
        let mut seen_names: std::collections::HashSet<String> = std::collections::HashSet::new();
        let mut entries: Vec<(Option<String>, TermId)> = Vec::new();
        for (name, tid) in self.ctx.named_terms_iter() {
            if seen.insert(tid) {
                seen_names.insert(name.to_string());
                entries.push((Some(name.to_string()), tid));
            }
        }
        for &tid in assumptions {
            if !seen.insert(tid) {
                continue;
            }
            // A rewritten named assert (#uc-rewrite-provenance) carries its
            // parse label on a DIFFERENT TermId than the parse root already
            // emitted above — dedup by printed label too, or the padded core
            // prints that label twice.
            let name = name_of(tid);
            if let Some(n) = &name {
                if !seen_names.insert(n.clone()) {
                    continue;
                }
            }
            entries.push((name, tid));
        }
        entries
    }

    /// Get unsatisfiable core (get-unsat-core command)
    ///
    /// Returns the printable UNSAT core: named assertions print as their
    /// `:named` labels, `check-sat-assuming` assumption literals print as
    /// verbatim term text (z3-parity, one flat list). See
    /// [`Self::unsat_core_entries`] for the soundness contract.
    pub(crate) fn unsat_core(&self) -> String {
        // Check that produce-unsat-cores is enabled
        if !self.produce_unsat_cores_enabled() {
            return "(error \"unsat core generation is not enabled, set :produce-unsat-cores to true\")".to_string();
        }

        // Check that last result was unsat
        match self.last_result {
            Some(SolveResult::Unsat(_)) => {
                let entries = self.unsat_core_entries();
                if entries.is_empty() {
                    return "()".to_string();
                }
                let parts: Vec<String> = entries
                    .iter()
                    .map(|(name, tid)| match name {
                        Some(name) => quote_symbol(name),
                        None => self.format_term(*tid),
                    })
                    .collect();
                format!("({})", parts.join(" "))
            }
            _ => "(error \"unsat core is not available, last result was not unsat\")".to_string(),
        }
    }

    /// Look up the TermId for a named assertion by name.
    ///
    /// Named assertions are stored in the context from `(assert (! expr :named foo))`.
    pub(crate) fn named_assertion_term_id(&self, name: &str) -> Option<TermId> {
        self.ctx
            .named_terms_iter()
            .find(|(n, _)| n == &name)
            .map(|(_, tid)| tid)
    }

    /// Get unsatisfiable core with Farkas coefficients
    /// (`(get-unsat-core :farkas)` -- AY extension, #8769).
    ///
    /// Returns an s-expression listing each named core assertion alongside
    /// its Farkas coefficients when the contribution came from the linear
    /// arithmetic (LRA or LIA) theory. Entries without Farkas data are
    /// emitted as plain names so the output is a strict extension of
    /// `(get-unsat-core)`. Format per entry:
    ///
    /// - `name` -- no Farkas data available
    /// - `(name (:farkas-coeffs <c1> <c2> ...))` -- Farkas coefficients
    ///   produced by an LRA/LIA theory lemma referencing this assertion.
    ///
    /// When proof production is disabled or no proof is available, falls
    /// back to the plain `unsat_core()` output so downstream consumers
    /// always receive a well-formed s-expression.
    pub(crate) fn unsat_core_with_farkas(&self) -> String {
        use ay_core::ProofStep;
        use num_rational::Rational64;
        use std::collections::BTreeMap;

        // Check that produce-unsat-cores is enabled (reuse the existing gate).
        if !self.produce_unsat_cores_enabled() {
            return "(error \"unsat core generation is not enabled, set :produce-unsat-cores to true\")".to_string();
        }

        // Must be UNSAT.
        if !matches!(self.last_result, Some(SolveResult::Unsat(_))) {
            return "(error \"unsat core is not available, last result was not unsat\")"
                .to_string();
        }

        // Without a proof we can only fall back to plain names.
        let Some(proof) = self.last_proof() else {
            return self.unsat_core();
        };

        // Use the same authenticated/padded entries as `unsat_core()` so both
        // commands agree on membership and ordering (see the soundness
        // contract on `unsat_core_entries`). Assumption-literal entries
        // (no `:named` label) print as bare verbatim terms without
        // `:farkas-coeffs`.
        let core_entries = self.unsat_core_entries();

        if core_entries.is_empty() {
            return "()".to_string();
        }

        // Walk the proof DAG: for every LRA/LIA theory lemma, accumulate
        // Farkas coefficients indexed by the TermIds the lemma references.
        // We take the first Farkas annotation we see for a given TermId; a
        // single literal can in principle participate in multiple lemmas,
        // but the first one is sufficient evidence for model-checker-consumer/VerifierConsumer consumers.
        let mut farkas_by_term: BTreeMap<TermId, Vec<Rational64>> = BTreeMap::new();
        for step in &proof.steps {
            if let ProofStep::TheoryLemma { clause, farkas, .. } = step {
                // `FarkasAnnotation` is the sole carrier of Farkas
                // coefficients on a theory lemma; LIA lemmas either carry
                // their Farkas coefficients on this same field (for cutting
                // planes and bounds-gap proofs) or have none at all (for
                // pure divisibility proofs).
                if let Some(f) = farkas.as_ref() {
                    let coeffs: &Vec<Rational64> = &f.coefficients;
                    for term_id in clause {
                        // Strip negation to reach the underlying atom so the
                        // lookup matches the stored named-assertion TermId.
                        let base = match self.terms().get(*term_id) {
                            TermData::Not(inner) => *inner,
                            _ => *term_id,
                        };
                        farkas_by_term.entry(base).or_insert_with(|| coeffs.clone());
                    }
                }
            }
        }

        // Format: one entry per core member.
        let mut parts: Vec<String> = Vec::with_capacity(core_entries.len());
        for (name, tid) in &core_entries {
            let Some(name) = name else {
                // Assumption literal without a `:named` label: bare verbatim
                // term, no Farkas annotation (same rendering as unsat_core()).
                parts.push(self.format_term(*tid));
                continue;
            };
            let entry = match farkas_by_term.get(tid) {
                Some(coeffs) if !coeffs.is_empty() => {
                    use num_bigint::BigInt;
                    use num_rational::BigRational;
                    let rendered: Vec<String> = coeffs
                        .iter()
                        .map(|c| {
                            let big = BigRational::new(
                                BigInt::from(*c.numer()),
                                BigInt::from(*c.denom()),
                            );
                            format_rational(&big)
                        })
                        .collect();
                    format!(
                        "({} (:farkas-coeffs {}))",
                        quote_symbol(name),
                        rendered.join(" ")
                    )
                }
                _ => quote_symbol(name),
            };
            parts.push(entry);
        }
        format!("({})", parts.join(" "))
    }

    /// Get unsatisfiable assumptions (get-unsat-assumptions command)
    ///
    /// Returns the subset of assumptions from check-sat-assuming that contributed
    /// to unsatisfiability. Per SMT-LIB 2.6, this returns a subset of the literals
    /// from the most recent check-sat-assuming call that was unsatisfiable.
    pub(super) fn unsat_assumptions(&self) -> String {
        // Check that last result was unsat and we have assumptions
        match (&self.last_result, &self.last_assumptions) {
            (Some(SolveResult::Unsat(_)), Some(assumptions)) => {
                if assumptions.is_empty() {
                    return "()".to_string();
                }

                // Use the minimal core if available (from SAT assumption-based solving)
                // Otherwise fall back to all assumptions.
                //
                // SMT-LIB 2.6 contract: the result is a SUBSET of the literals
                // passed to check-sat-assuming. With `:produce-unsat-cores`,
                // named assertions are assumption-tracked alongside the user's
                // literals (#unsat-core-assumptions), so the harvested core can
                // contain named-assertion terms — intersect with the user's
                // assumption literals before printing. (Deliberate non-parity
                // with z3, which also lists named labels here in deviation
                // from the standard.)
                let core_assumptions: Vec<TermId> = match &self.last_assumption_core {
                    Some(core) => core
                        .iter()
                        .copied()
                        .filter(|tid| assumptions.contains(tid))
                        .collect(),
                    None => assumptions.clone(),
                };

                if core_assumptions.is_empty() {
                    return "()".to_string();
                }

                let literals: Vec<String> = core_assumptions
                    .iter()
                    .map(|&term_id| self.format_term(term_id))
                    .collect();

                format!("({})", literals.join(" "))
            }
            (Some(SolveResult::Unsat(_)), None) => {
                // Unsat but no assumptions (regular check-sat, not check-sat-assuming)
                "(error \"no check-sat-assuming has been performed\")".to_string()
            }
            (Some(SolveResult::Sat), _) => {
                "(error \"unsat assumptions not available, last result was sat\")".to_string()
            }
            (Some(SolveResult::Unknown), _) => {
                "(error \"unsat assumptions not available, last result was unknown\")".to_string()
            }
            (None, _) => {
                "(error \"unsat assumptions not available, no check-sat has been performed\")"
                    .to_string()
            }
        }
    }

    /// Render a core symbol identity using its public SMT-LIB spelling. An
    /// overloaded identifier must carry its result-sort ascription so replay
    /// resolves the same full signature instead of depending on declaration
    /// order (or becoming ambiguous for equal domains).
    fn format_declared_symbol_identity(&self, identity: &str, result_sort: &Sort) -> String {
        if let Some(surface_name) = self.ctx.overloaded_surface_name(identity) {
            format!(
                "(as {} {})",
                quote_symbol(surface_name),
                format_sort(result_sort)
            )
        } else {
            quote_symbol(self.ctx.dt_surface_name(identity).unwrap_or(identity))
        }
    }
}

/// Collect uninterpreted-sort names referenced by `sort`, recursing through
/// compound sorts (`Array`, `Seq`, datatype fields). `RoundingMode` is the
/// FP theory's built-in sort spelled as `Sort::Uninterpreted` internally; it
/// must not be re-declared in a serialized script. (#dump-self-contained)
fn collect_uninterpreted_sort_names(sort: &Sort, out: &mut std::collections::BTreeSet<String>) {
    match sort {
        Sort::Uninterpreted(name) | Sort::TypeVar(name) => {
            if name != "RoundingMode" {
                out.insert(name.clone());
            }
        }
        Sort::Array(arr) => {
            collect_uninterpreted_sort_names(&arr.index_sort, out);
            collect_uninterpreted_sort_names(&arr.element_sort, out);
        }
        Sort::Seq(elem) => collect_uninterpreted_sort_names(elem, out),
        // Term-level sorts are `as_term_sort`-lowered (`Datatype` ->
        // `Uninterpreted`), but declaration metadata can still carry the full
        // definition; record the carrier name and any field sorts.
        Sort::Datatype(dt) => {
            out.insert(dt.name.clone());
            for ctor in &dt.constructors {
                for field in &ctor.fields {
                    collect_uninterpreted_sort_names(&field.sort, out);
                }
            }
        }
        _ => {}
    }
}

/// Conservative classifier: is `name` a built-in SMT-LIB operator stored as
/// `App(Symbol::Named)` that must NOT be re-declared in a serialized script?
/// (#transpose)
fn is_builtin_operator(name: &str) -> bool {
    // Keep the dump classifier tied to the frontend's drift-checked list of
    // operators whose semantics are selected structurally by name.  A stale
    // local list used to fabricate `(declare-fun const-array ...)`, which the
    // frontend correctly rejects as a reserved-symbol forgery.
    if ay_frontend::is_reserved_op_name(name) || name.starts_with("(_ ") {
        return true;
    }
    matches!(
        name,
        "=" | "distinct"
            | "=>"
            | "and"
            | "or"
            | "xor"
            | "not"
            | "ite"
            | "true"
            | "false"
            | "+"
            | "-"
            | "*"
            | "/"
            | "div"
            | "mod"
            | "rem"
            | "abs"
            | "<"
            | "<="
            | ">"
            | ">="
            | "to_int"
            | "to_real"
            | "is_int"
            | "divisible"
            | "select"
            | "store"
            | "concat"
            | "bvnot"
            | "bvneg"
            | "bvand"
            | "bvor"
            | "bvxor"
            | "bvnand"
            | "bvnor"
            | "bvxnor"
            | "bvadd"
            | "bvsub"
            | "bvmul"
            | "bvudiv"
            | "bvurem"
            | "bvsdiv"
            | "bvsrem"
            | "bvsmod"
            | "bvshl"
            | "bvlshr"
            | "bvashr"
            | "bvult"
            | "bvule"
            | "bvugt"
            | "bvuge"
            | "bvslt"
            | "bvsle"
            | "bvsgt"
            | "bvsge"
    )
}
