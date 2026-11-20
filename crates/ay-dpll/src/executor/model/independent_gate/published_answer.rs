// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The answer route (#get-value-published-model): `(get-value)`, `(eval)` and
//! the Rust `values()` answer a term that mentions an application of an
//! ordinary declared function from the model `(get-model)` publishes, or with
//! an error. [`Executor::published_answer`] states the rule.

use std::cell::{OnceCell, RefCell};

use ay_core::quote_symbol;

use super::super::overloaded_ctor_surface::OverloadedCtors;
use super::published_carriers::CellCarriers;
use super::*;

/// The answer route's verdict for one requested term.
pub(in crate::executor::model) enum PublishedAnswer {
    /// The term's value in the published model, as text.
    Value(String),
    /// The term mentions no application of an ordinary declared function; the
    /// caller answers it as before.
    NotApplicable,
    /// The term mentions such an application and the published model gives it
    /// no value the route can read; the reason, for the batch error.
    Error(String),
}

/// One ordinary declared function: the declaration `(get-model)` prints it
/// under.
struct Declaration {
    surface: String,
    arg_sorts: Vec<Sort>,
    sort: Sort,
}

/// The state one value batch shares across its terms: the view caches of the
/// fixed `(assertions, model)` pair, the published tables already read, and
/// the per-term memo of [`Executor::published_answer`]'s applicability test.
pub(in crate::executor::model) struct PublishedAnswerSession<'a> {
    model: &'a Model,
    caches: SharedViewCaches,
    tables: Rc<PublishedTables>,
    /// Ordinary declared functions by core identity.
    functions: OnceCell<HashMap<String, Declaration>>,
    /// Whether a term mentions an application of an ordinary declared
    /// function.
    mentions: RefCell<HashMap<TermId, bool>>,
    /// The constructors whose printed names the batch's spelling gives table
    /// cells (`Executor::table_cell_surface`).
    overloaded: OverloadedCtors,
}

impl<'a> PublishedAnswerSession<'a> {
    /// A session over `model`, the model the batch reads; `overloaded` is what
    /// the batch's spelling names in table cells, as the printer names them.
    pub(in crate::executor::model) fn new(model: &'a Model, overloaded: OverloadedCtors) -> Self {
        Self {
            model,
            caches: SharedViewCaches::fresh(),
            tables: Rc::default(),
            functions: OnceCell::new(),
            mentions: RefCell::new(HashMap::new()),
            overloaded,
        }
    }

    /// The ordinary declared functions: every declared symbol with at least
    /// one argument except datatype constructors, selectors and testers,
    /// solver-internal symbols, problem-defined functions and adopted macros.
    /// These are the heads `IndependentModelView::printed_uf_rows` can print
    /// as a table, plus those it publishes through another channel.
    fn functions(&self, exec: &Executor) -> &HashMap<String, Declaration> {
        self.functions.get_or_init(|| {
            let ctx = &exec.ctx;
            let mut functions = HashMap::new();
            for (surface, info) in ctx.symbol_iter() {
                if info.arg_sorts.is_empty() {
                    continue;
                }
                let identity = ctx.symbol_identity_name(surface, info);
                if exec.is_exact_dt_internal_symbol(identity)
                    || ctx.is_internal_symbol(surface)
                    || ctx.is_defined_fun(surface)
                    || ctx.adopted_macro_interp(surface).is_some()
                {
                    continue;
                }
                functions
                    .entry(identity.to_owned())
                    .or_insert_with(|| Declaration {
                        surface: surface.clone(),
                        arg_sorts: info.arg_sorts.clone(),
                        sort: info.sort.clone(),
                    });
            }
            functions
        })
    }

    /// Whether `root` or a subterm is an application, with arguments, of an
    /// ordinary declared function: an iterative post-order walk over the term
    /// DAG, memoized for the batch.
    fn mentions_ordinary_application(&self, exec: &Executor, root: TermId) -> bool {
        if let Some(&known) = self.mentions.borrow().get(&root) {
            return known;
        }
        let functions = self.functions(exec);
        let terms = &exec.ctx.terms;
        let mut stack = vec![(root, false)];
        while let Some((term, children_done)) = stack.pop() {
            if self.mentions.borrow().contains_key(&term) {
                continue;
            }
            let children = terms.children(term);
            if !children_done {
                stack.push((term, true));
                stack.extend(children.into_iter().map(|child| (child, false)));
                continue;
            }
            let own = matches!(
                terms.get(term),
                TermData::App(sym, args) if !args.is_empty() && functions.contains_key(sym.name())
            );
            let mentions = own || {
                let memo = self.mentions.borrow();
                children
                    .iter()
                    .any(|child| memo.get(child).copied().unwrap_or(false))
            };
            self.mentions.borrow_mut().insert(term, mentions);
        }
        self.mentions.borrow().get(&root).copied().unwrap_or(false)
    }
}

/// What rule 1 of [`Executor::published_answer`] found for a direct
/// application.
enum CellRead {
    /// The text of the printed cell the application selects.
    Text(String),
    /// The function is not printed as a table; the evaluator reads its channel.
    NotTable,
    /// The printed table does not give the application a cell; the reason.
    Undecided(String),
}

/// `surface` as it may appear inside an SMT-LIB `(error "...")` string: a
/// quoted symbol whose `"` characters are doubled.
fn error_symbol(surface: &str) -> String {
    quote_symbol(surface).replace('"', "\"\"")
}

/// The batch error reason for a cell of the printed interpretation of `name`
/// (already an [`error_symbol`]) that holds the unbacked abstract value
/// `carrier` of a datatype sort.
fn unbacked_reason(name: &str, carrier: &str) -> String {
    format!(
        "the printed interpretation of {name} gives this point the abstract value {}, \
         which is not a value of its datatype sort and which the published model backs \
         with no constructor value",
        carrier.replace('"', "\"\"")
    )
}

impl Executor {
    /// The value `(get-value)`, `(eval)` and the Rust `values()` give `term`
    /// when it mentions an application, with arguments, of an ordinary declared
    /// function (#get-value-published-model). Every other term is
    /// [`PublishedAnswer::NotApplicable`]. The rules, in order:
    ///
    /// 1. `term` is such an application `(f a..)` and `(get-model)` prints `f`
    ///    as a table whose keys decode: each argument is evaluated over the
    ///    published model, the first row whose key is decided equal to the
    ///    point is selected (the else cell only when every key is decided
    ///    unequal; `PublishedUfCells::cell_at`), and the answer is that
    ///    cell's printed text. A table with no keyed row answers its one cell
    ///    without evaluating the arguments.
    /// 2. Otherwise the independent evaluator evaluates `term` over the
    ///    published model through an answer view: an application of a
    ///    function printed as a table reads that table as rule 1 does, a
    ///    selector applied to a value of another constructor reads the
    ///    printed selector table
    ///    ([`IndependentModelView::published_selector_value`]), an
    ///    application of a function printed through another definition
    ///    channel reads that definition at its evaluated argument point
    ///    ([`IndependentModelView::published_definition_value`]; a projection
    ///    and a certified linear body are evaluated by the gate's own reads),
    ///    and no per-term pin is read for a term that mentions an application
    ///    of a function printed as a table; every other read is the gate's. A
    ///    value is rendered as the printer renders it.
    /// 3. Otherwise, when `term` is the source application of a row of the
    ///    table the printer prints for its head (the EUF table, or the
    ///    ground-application table when the model has none), the answer is
    ///    that row's printed cell ([`Self::listed_row_text`]).
    /// 4. Otherwise the answer is [`PublishedAnswer::Error`].
    ///
    /// The route does not hand the term to the per-term chain
    /// (`Executor::term_value_string_unstopped_in_read`); inside rule 2 a pin
    /// is read only for a term that mentions no application of a function
    /// printed as a table. The tables are derived as the printer derives
    /// them, outside the residual-output reentrancy guard: this route is not
    /// entered from `Executor::completed_model_value`, and a completed-model
    /// evaluation a callback starts holds that guard itself.
    pub(in crate::executor::model) fn published_answer(
        &self,
        session: &PublishedAnswerSession<'_>,
        term: TermId,
    ) -> PublishedAnswer {
        if !session.mentions_ordinary_application(self, term) {
            return PublishedAnswer::NotApplicable;
        }
        if !self.materialized_scalar_functions_current(session.model) {
            return PublishedAnswer::Error(
                "materialized scalar function model is stale".to_owned(),
            );
        }
        let _caches = GateViewCacheSession::resume(session.caches.clone());
        let view = IndependentModelView::for_published_answers(
            self,
            session.model,
            Rc::clone(&session.tables),
        );
        if view.ensure_def_index().is_err() {
            return PublishedAnswer::Error("the published model cannot be read".to_owned());
        }
        self.published_answer_in_view(session, &view, term)
    }

    fn published_answer_in_view(
        &self,
        session: &PublishedAnswerSession<'_>,
        view: &IndependentModelView<'_>,
        term: TermId,
    ) -> PublishedAnswer {
        let mut reason = None;
        if let TermData::App(sym, args) = self.ctx.terms.get(term) {
            if let Some(declaration) = session.functions(self).get(sym.name()) {
                match self.printed_cell_text(session, view, sym.name(), declaration, args) {
                    CellRead::Text(text) => return PublishedAnswer::Value(text),
                    CellRead::NotTable => {}
                    CellRead::Undecided(why) => reason = Some(why),
                }
            }
        }
        if let EvalOutcome::Value(value) =
            ay_model_check::evaluate_term(&self.ctx.terms, view, term)
        {
            if let Some(text) =
                self.render_published_value(&value, self.ctx.terms.sort(term), session.model)
            {
                return PublishedAnswer::Value(text);
            }
        }
        if let Some(text) = self.listed_row_text(session, view, term) {
            return PublishedAnswer::Value(text);
        }
        PublishedAnswer::Error(reason.unwrap_or_else(|| {
            "the answer route cannot evaluate this term from the published model".to_owned()
        }))
    }

    /// Rule 1 of [`Self::published_answer`] for the application
    /// `(identity args..)`.
    fn printed_cell_text(
        &self,
        session: &PublishedAnswerSession<'_>,
        view: &IndependentModelView<'_>,
        identity: &str,
        declaration: &Declaration,
        args: &[TermId],
    ) -> CellRead {
        // A retained constant-array function prints through its own channel
        // ahead of any table (`Executor::model_from_selected`).
        match session.model.constant_array_function_for_output(
            self,
            identity,
            &declaration.arg_sorts,
            &declaration.sort,
        ) {
            Ok(Some(_)) => return CellRead::NotTable,
            Ok(None) => {}
            Err(()) => {
                return CellRead::Undecided("the retained array function source changed".to_owned())
            }
        }
        let name = error_symbol(&declaration.surface);
        let table = view.published_uf_table(identity);
        let cells = match table.as_deref() {
            None | Some(PublishedUfTable::NotPrinted) => return CellRead::NotTable,
            Some(PublishedUfTable::RowsFailed | PublishedUfTable::KeysUndecoded) => {
                return CellRead::Undecided(format!(
                    "the printed interpretation of {name} cannot be read"
                ))
            }
            Some(PublishedUfTable::Readable(cells)) => cells,
        };
        // A body with no keyed row is one cell for every point, so the
        // arguments need no value.
        if cells.rows.is_empty() {
            return self.cell_read(session, &name, declaration, cells, &cells.else_cell);
        }
        let mut point = Vec::with_capacity(args.len());
        for &arg in args {
            match ay_model_check::evaluate_term(&self.ctx.terms, view, arg) {
                EvalOutcome::Value(value) => point.push(value),
                EvalOutcome::Unevaluable(_) => {
                    return CellRead::Undecided(format!(
                        "an argument of {name} has no value in the published model"
                    ))
                }
            }
        }
        let Some(cell) = cells.cell_at(&point) else {
            return CellRead::Undecided(format!(
                "the answer route cannot decide which row of the printed interpretation of \
                 {name} this argument point selects"
            ));
        };
        self.cell_read(session, &name, declaration, cells, cell)
    }

    /// Rule 1's answer for the selected `cell` of the printed table `cells`
    /// of the function `name`: its [`CellAnswer`]. A printed cell is named as
    /// the printer names it ([`Self::printed_cell_surface`]); a cell whose
    /// abstract values of a datatype sort are backed answers the replaced
    /// text; a cell with an unbacked one gives no answer.
    fn cell_read(
        &self,
        session: &PublishedAnswerSession<'_>,
        name: &str,
        declaration: &Declaration,
        cells: &PublishedUfCells,
        cell: &PrintedCell,
    ) -> CellRead {
        match &cell.answer {
            CellAnswer::Printed => CellRead::Text(self.printed_cell_surface(
                &cell.text,
                &declaration.sort,
                cells.default_body,
                &session.overloaded,
            )),
            CellAnswer::Backed(text) => CellRead::Text(text.clone()),
            CellAnswer::Unbacked(carrier) => CellRead::Undecided(unbacked_reason(name, carrier)),
        }
    }

    /// The text the printer emits for a table cell `text` of `sort`: the name
    /// `Self::table_cell_surface` gives it, except in the default body of an
    /// empty table, which the printer does not name. The caller applies the
    /// overloaded-constructor ascription, as `(get-model)` does after naming.
    fn printed_cell_surface(
        &self,
        text: &str,
        sort: &Sort,
        default_body: bool,
        overloaded: &OverloadedCtors,
    ) -> String {
        if default_body {
            return text.to_owned();
        }
        self.table_cell_surface(text, sort, overloaded)
            .unwrap_or_else(|| text.to_owned())
    }

    /// Rule 2's rendering of an evaluated `value` of `sort`: a declare-sort
    /// abstract value `@S!n` renders as `(as @S!n S)` through the printer's
    /// cell renderer, which [`Self::format_gate_model_value`] refuses; a Real
    /// renders as the user-facing printers render one (`format_real`, #real-fmt),
    /// not in `format_gate_model_value`'s internal `(/ n d)` spelling; a
    /// floating-point value of `sort`'s format whose fields
    /// [`FpModelValue::from_fields`] holds renders through
    /// [`FpModelValue::to_smtlib`], the printer's spelling (`(_ +zero 5 11)`,
    /// not `(fp #b0 #b00000 #b0000000000)`); every other value through
    /// [`Self::format_gate_model_value`]. `None` when the value has no exact
    /// rendering.
    fn render_published_value(
        &self,
        value: &ModelValue,
        sort: &Sort,
        model: &Model,
    ) -> Option<String> {
        match (value, sort) {
            (ModelValue::Uninterpreted(token), Sort::Uninterpreted(_))
                if token.starts_with('@') && self.datatype_sort_name(sort).is_none() =>
            {
                self.resolve_table_value(token, sort, model).ok()
            }
            (ModelValue::Real(value), Sort::Real) => {
                Some(crate::executor_format::format_real(value))
            }
            (
                ModelValue::FloatingPoint {
                    sign,
                    exponent,
                    significand,
                    exponent_bits,
                    significand_bits,
                },
                Sort::FloatingPoint(eb, sb),
            ) => {
                if (exponent_bits, significand_bits) != (eb, sb) {
                    return None;
                }
                FpModelValue::from_fields(*sign, *exponent, *significand, *eb, *sb)
                    .map(|value| value.to_smtlib())
            }
            _ => self.format_gate_model_value(value, sort),
        }
    }

    /// Rule 3 of [`Self::published_answer`]: when `term` is the source
    /// application of a row of the table the printer prints for its head, the
    /// text the printer emits for that row's cell. The table is the head's EUF
    /// table, or, when the model carries none, the ground-application table
    /// ([`IndependentModelView::ground_fallback_applications`]). Applies only
    /// when that table printed without failure and no position of the head's
    /// signature is a selector-bearing datatype; elsewhere
    /// `Self::dt_egraph_rewrite_uf_table` rewrites cells, and `None` results.
    fn listed_row_text(
        &self,
        session: &PublishedAnswerSession<'_>,
        view: &IndependentModelView<'_>,
        term: TermId,
    ) -> Option<String> {
        let TermData::App(sym, args) = self.ctx.terms.get(term) else {
            return None;
        };
        if args.is_empty() {
            return None;
        }
        let identity = sym.name();
        let declaration = session.functions(self).get(identity)?;
        if declaration
            .arg_sorts
            .iter()
            .chain(std::iter::once(&declaration.sort))
            .any(|sort| self.selector_bearing_datatype(sort))
        {
            return None;
        }
        if !matches!(
            session.model.constant_array_function_for_output(
                self,
                identity,
                &declaration.arg_sorts,
                &declaration.sort,
            ),
            Ok(None)
        ) {
            return None;
        }
        if !matches!(
            view.published_uf_table(identity).as_deref(),
            Some(PublishedUfTable::Readable(_) | PublishedUfTable::KeysUndecoded)
        ) {
            return None;
        }
        // The raw row for `term`, as the printer's table holds it before
        // `Executor::printed_uf_table_rows` resolves it.
        let euf_table = session.model.euf_model.as_ref().and_then(|euf| {
            euf.function_tables
                .get(identity)
                .map(|raw| (raw, euf.function_table_terms.get(identity)))
        });
        let (row_args, row_result) = match euf_table {
            Some((raw_table, sources)) => {
                let sources = sources?;
                if sources.len() != raw_table.len() {
                    return None;
                }
                let row = sources.iter().position(|&source| source == term)?;
                // Provenance placeholders and `@?N` resolution, row by row as
                // `IndependentModelView::printed_uf_rows` applies them.
                let table = self
                    .sequence_table_provenance_placeholders(
                        identity,
                        &declaration.arg_sorts,
                        &declaration.sort,
                        raw_table,
                        Some(sources),
                    )
                    .ok()?;
                let resolved = self.resolve_function_table(session.model, table.get(row..=row)?);
                resolved.into_iter().next()?
            }
            None => {
                let applications = view.ground_fallback_applications(
                    &declaration.surface,
                    declaration.arg_sorts.len(),
                )?;
                let application = applications.into_iter().find(|(app, _)| *app == term)?;
                let rows = self.uf_table_from_ground_applications(session.model, &[application])?;
                rows.into_iter().next()?
            }
        };
        // The printer's remaining per-row steps up to the cell text: the
        // quantifier-phantom skip, then the cell renderer. Deduplication and
        // constant absorption keep this cell's text, and the table printed
        // without failure.
        if self.table_entry_is_quantifier_phantom(&row_result, session.model)
            || row_args
                .iter()
                .any(|arg| self.table_entry_is_quantifier_phantom(arg, session.model))
        {
            return None;
        }
        let text = self
            .resolve_table_value(&row_result, &declaration.sort, session.model)
            .ok()?;
        match view.resolve_datatype_carriers(&text, &declaration.sort) {
            CellCarriers::None => Some(self.printed_cell_surface(
                &text,
                &declaration.sort,
                false,
                &session.overloaded,
            )),
            CellCarriers::Backed { text, .. } => Some(text),
            CellCarriers::Unbacked(_) => None,
        }
    }
}
