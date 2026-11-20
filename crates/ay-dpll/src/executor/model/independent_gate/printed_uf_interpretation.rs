// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Construction of reconciled printed-UF interpretations.

use ay_core::kani_compat::DetHashSet;
use ay_core::unescape_string_contents;

use super::published_carriers::CellCarriers;
use super::*;

/// Where the texts at the String-sorted positions of a printed definition
/// come from, which fixes how
/// [`IndependentModelView::read_published_atom`] decodes one
/// ([`published_string_value`]).
#[derive(Clone, Copy)]
pub(super) enum StringTexts<'t> {
    /// Every text is the output of a value renderer.
    Rendered,
    /// The texts are rows printed from an EUF function table; the set holds
    /// the entries at the same positions of the table the row pipeline
    /// started from ([`PrintedUfSource::table`]).
    EufTable(&'t HashSet<&'t str>),
}

/// What the printer's row pipeline starts from for one function identity
/// ([`IndependentModelView::printed_uf_source`]).
struct PrintedUfSource {
    /// The name `(get-model)` prints the function under.
    surface: String,
    /// The declared argument sorts.
    arg_sorts: Vec<Sort>,
    /// The declared result sort.
    result_sort: Sort,
    /// The table [`Executor::printed_uf_table_rows`] prints.
    table: Vec<(Vec<String>, String)>,
    /// Whether `table` is the model's EUF function table for the identity,
    /// after `Executor::resolve_function_table`; otherwise it is the
    /// ground-application table.
    from_euf_table: bool,
}

/// The entries of `table` at its String-sorted key positions and, when
/// `result_sort` is String, at its result position, as
/// `(key entries, result entries)`.
fn string_entries<'t>(
    table: &'t [(Vec<String>, String)],
    arg_sorts: &[Sort],
    result_sort: &Sort,
) -> (HashSet<&'t str>, HashSet<&'t str>) {
    let mut keys = HashSet::new();
    let mut results = HashSet::new();
    for (row_args, row_result) in table {
        for (entry, sort) in row_args.iter().zip(arg_sorts) {
            if matches!(sort, Sort::String) {
                keys.insert(entry.as_str());
            }
        }
        if matches!(result_sort, Sort::String) {
            results.insert(row_result.as_str());
        }
    }
    (keys, results)
}

/// The contents of `text` when it is spelled as an SMT-LIB string literal: it
/// starts and ends with `"` and every `"` between them is one of a pair `""`.
fn string_literal_contents(text: &str) -> Option<&str> {
    let contents = text.strip_prefix('"')?.strip_suffix('"')?;
    let mut chars = contents.chars();
    while let Some(c) = chars.next() {
        if c == '"' && chars.next() != Some('"') {
            return None;
        }
    }
    Some(contents)
}

/// The String value the printed text `text` denotes, when `texts` decides it:
///
/// - a text spelled as a string literal ([`string_literal_contents`]) that is
///   not an entry of the EUF table denotes the literal's value
///   ([`unescape_string_contents`]);
/// - a text that is an entry of the EUF table and is not spelled as a literal
///   is the string's own characters, as `Executor::eval_value_to_model_atom`
///   writes a String value;
/// - any other text is `None`: a table entry spelled as a literal may be
///   either, and a rendered text that is not a literal is not a String value.
fn published_string_value(text: &str, texts: StringTexts<'_>) -> Option<ModelValue> {
    let table_entry = match texts {
        StringTexts::Rendered => false,
        StringTexts::EufTable(entries) => entries.contains(text),
    };
    match (string_literal_contents(text), table_entry) {
        (Some(contents), false) => Some(ModelValue::Str(unescape_string_contents(contents))),
        (None, true) => Some(ModelValue::Str(text.to_owned())),
        _ => None,
    }
}

/// Whether every string literal inside `text` spells its value's own
/// characters: it has no `""` pair and [`unescape_string_contents`] leaves its
/// contents unchanged. `false` also when a `"` in `text` opens a literal that
/// does not close. `Executor::parse_model_value_string` reads a quoted String
/// text as the characters between its quotes, which is the literal's value
/// only under this condition; [`IndependentModelView::read_published_atom`]
/// checks an atom that fails it.
fn nested_string_literals_are_verbatim(text: &str) -> bool {
    let mut rest = text;
    while let Some(open) = rest.find('"') {
        let body = &rest[open + 1..];
        let mut end = None;
        let mut chars = body.char_indices().peekable();
        while let Some((at, c)) = chars.next() {
            if c != '"' {
                continue;
            }
            if matches!(chars.peek(), Some((_, '"'))) {
                return false;
            }
            end = Some(at);
            break;
        }
        let Some(end) = end else {
            return false;
        };
        let contents = &body[..end];
        if unescape_string_contents(contents) != contents {
            return false;
        }
        rest = &body[end + 1..];
    }
    true
}

impl IndependentModelView<'_> {
    /// Uncached body of [`Self::printed_uf_interpretation`]: the printer's own
    /// pipeline, in the printer's order, over the model's extracted table.
    pub(super) fn build_printed_uf_interpretation(
        &self,
        identity: &str,
    ) -> Option<PrintedUfInterpretation> {
        let (arg_sorts, result_sort, rows) = self.printed_uf_rows(identity)?;
        let rows = rows.ok()?;
        self.read_printed_uf_rows(&arg_sorts, &result_sort, &rows)
    }

    /// The printer's row pipeline for `identity`, stopping one step short of
    /// decoding: `None` when `(get-model)` would not print this symbol at all,
    /// otherwise the declared signature plus [`Executor::printed_uf_table_rows`]'
    /// own typed `Result`.
    ///
    /// Split out so the gate can see the ERROR that
    /// [`Self::build_printed_uf_interpretation`] discards. Coverage gaps remain
    /// distinct from the typed inconsistent-table refutation, which means two
    /// rows land on the same argument point with different results. See
    /// [`Self::non_functional_uf_interpretation`].
    pub(super) fn printed_uf_rows(
        &self,
        identity: &str,
    ) -> Option<(
        Vec<Sort>,
        Sort,
        Result<Vec<(Vec<String>, String)>, super::super::output_format::PrintedUfTableRowsError>,
    )> {
        let source = self.printed_uf_source(identity)?;
        let rows = self.printed_uf_source_rows(&source);
        Some((source.arg_sorts, source.result_sort, rows))
    }

    /// [`Executor::printed_uf_table_rows`] over `source`: the rows
    /// `(get-model)` prints for it, or the printer's error.
    fn printed_uf_source_rows(
        &self,
        source: &PrintedUfSource,
    ) -> Result<Vec<(Vec<String>, String)>, super::super::output_format::PrintedUfTableRowsError>
    {
        self.exec.printed_uf_table_rows(
            &source.surface,
            &source.arg_sorts,
            &source.result_sort,
            &source.table,
            self.model,
        )
    }

    /// The declared signature and the table the printer's row pipeline starts
    /// from for `identity`; `None` when `(get-model)` would not print this
    /// symbol as a table.
    fn printed_uf_source(&self, identity: &str) -> Option<PrintedUfSource> {
        // Locate the DECLARED signature `(get-model)` would print this table
        // under, and reproduce the printer's suppression / other-channel
        // rules (`Executor::format_model`, same order).
        let ctx = &self.exec.ctx;
        let (surface, info) = ctx
            .symbol_iter()
            .find(|(name, info)| ctx.symbol_identity_name(name, info) == identity)?;
        if self.exec.is_exact_dt_internal_symbol(identity) || ctx.is_internal_symbol(surface) {
            return None;
        }
        let symbol = Symbol::named(identity);
        if !matches!(
            self.model.projection_ufs.projected_argument_for_signature(
                &symbol,
                &info.arg_sorts,
                &info.sort,
            ),
            Ok(None)
        ) {
            return None;
        }
        if self
            .model
            .certified_total_ufs
            .by_symbol
            .contains_key(identity)
            || self
                .exec
                .const_interp_cert_witness_entries(self.model)
                .iter()
                .any(|entry| entry.name() == Some(surface.as_str()))
            || self
                .model
                .has_formula_neutral_function_default_symbol(&symbol)
            || ctx.adopted_macro_interp(surface).is_some()
            || ctx.is_defined_fun(surface)
        {
            return None;
        }
        let arg_sorts: &[Sort] = &info.arg_sorts;
        let result_sort = &info.sort;
        if arg_sorts.is_empty() {
            return None;
        }

        let euf_table = self
            .model
            .euf_model
            .as_ref()
            .and_then(|euf| euf.function_tables.get(identity).map(|raw| (euf, raw)));
        let from_euf_table = euf_table.is_some();
        let table = if let Some((euf, raw)) = euf_table {
            let table = self
                .exec
                .sequence_table_provenance_placeholders(
                    identity,
                    arg_sorts,
                    result_sort,
                    raw,
                    euf.function_table_terms.get(identity).map(Vec::as_slice),
                )
                .ok()?;
            let table = self.exec.resolve_function_table(self.model, &table);
            match self
                .exec
                .dt_egraph_rewrite_uf_table(self.model, arg_sorts, result_sort, &table)
            {
                super::super::dt_egraph_values::DtUfTableRewrite::NotApplicable => table,
                super::super::dt_egraph_values::DtUfTableRewrite::Rewritten(t) => t,
                // The printer OMITS this definition, leaving the model partial here.
                super::super::dt_egraph_values::DtUfTableRewrite::Drop => return None,
            }
        } else {
            // #gate-reads-ground-uf-fallback: BV/AUFBV lanes Ackermannize
            // declared UFs and therefore publish no EufModel table.  The model
            // printer still emits a total interpretation reconstructed from
            // every ground application in the authored assertions.  Read that
            // exact fallback here as well; otherwise the independent gate sees
            // a datatype-valued application only as an opaque carrier token
            // while the public witness prints a concrete constructor value.
            let applications = self.ground_fallback_applications(surface, arg_sorts.len())?;
            self.exec
                .uf_table_from_ground_applications(self.model, &applications)?
        };
        Some(PrintedUfSource {
            surface: surface.clone(),
            arg_sorts: arg_sorts.to_vec(),
            result_sort: result_sort.clone(),
            table,
            from_euf_table,
        })
    }

    /// The ground applications of the declared function `surface` with
    /// `arity` arguments, in the order the printer's ground-application
    /// fallback table lists their rows (`Executor::model_from_selected` builds
    /// that table when the model carries no EUF table for the symbol). `None`
    /// when the printer omits that table: the symbol occurs under a
    /// quantifier, or no ground application of it exists.
    pub(super) fn ground_fallback_applications(
        &self,
        surface: &str,
        arity: usize,
    ) -> Option<Vec<(TermId, Vec<TermId>)>> {
        // Mirror the printer's quantifier guard and collection root.  A
        // quantified occurrence leaves the interpretation omitted rather
        // than inventing an else branch, and any unreadable application or
        // non-function table remains `None` through the helpers below.
        if self.exec.symbol_occurs_under_quantifier(surface) {
            return None;
        }
        let mut applications: DetHashMap<(String, usize), Vec<(TermId, Vec<TermId>)>> =
            DetHashMap::default();
        let mut visited = DetHashSet::default();
        for &assertion in &self.exec.ctx.assertions {
            self.exec
                .collect_uf_applications(assertion, &mut applications, &mut visited);
        }
        // Mirror the printer's census root, not just its guard: an exact
        // finite-domain expansion carries the ground applications of the
        // authored binder it replaced.
        for root in self.exec.finitely_expanded_ground_roots() {
            self.exec
                .collect_uf_applications(root, &mut applications, &mut visited);
        }
        applications.remove(&(surface.to_string(), arity))
    }

    /// A published model must be a FUNCTION. Report the first uninterpreted
    /// symbol whose extracted table is not one (#bv2nat-subst-recover, follow-on).
    ///
    /// `printed_uf_table_rows` already detects this — two rows resolving to the
    /// same argument point with different results — and the printer fails the
    /// `(get-model)` command on it rather than emitting a falsifying witness.
    /// The VERDICT path did not look: the gate swallowed the error with `.ok()?`
    /// and fell back to a pin-only, TermId-keyed read of the same table, which
    /// happily reads `f(v) = 1` for the pinned application while the table also
    /// carries `f(0) = 101` and the model says `v = 0`.
    ///
    /// That gap is only reachable when the conflicting row is invisible to the
    /// compositional evaluator — e.g. `f(0)` comes from a QUANTIFIER
    /// instantiation whose assertion model validation skipped, so no single
    /// conjunct is false and cross-conjunct single-valuedness never sees the
    /// pair. Measured shape:
    ///
    /// ```smt2
    /// (assert (and (<= 0 a) (< a 4)))
    /// (assert (= v (bv2nat (bvand ((_ int2bv 64) a) ((_ int2bv 64) 1)))))
    /// (assert (forall ((x Int)) (=> (and (<= 0 x) (<= x 1)) (> (f x) 100))))
    /// (assert (< (f v) 50))          ; UNSAT: v in {0,1}
    /// ```
    ///
    /// which reported `sat` with `((a 2) (v 0) ((f v) 1) ((f 0) 101))` — a model
    /// that contradicts itself, and a WRONG SAT. Before the `bv2nat` recovery
    /// fix the same query was `unknown` only because `v` had no value at all and
    /// the round-trip assertion tripped the gate first; the hole was masked, not
    /// absent.
    ///
    /// SOUNDNESS DIRECTION: this can only turn a `sat` into `unknown`. It never
    /// admits a model, never touches an UNSAT derivation, and never suppresses a
    /// report — it ADDS a refusal the printer was already making one command
    /// later.
    pub(in crate::executor) fn non_functional_uf_interpretation(&self) -> Option<String> {
        // Check both sources used by `printed_uf_rows`: extracted EUF tables
        // and the exact authored-ground fallback used when BV/AUFBV
        // Ackermannization publishes no EUF table.
        let mut identities = DetHashSet::default();
        if let Some(euf) = self.model.euf_model.as_ref() {
            identities.extend(euf.function_tables.keys().cloned());
        }
        let mut ground_applications: DetHashMap<(String, usize), Vec<(TermId, Vec<TermId>)>> =
            DetHashMap::default();
        let mut visited = DetHashSet::default();
        for &assertion in &self.exec.ctx.assertions {
            self.exec
                .collect_uf_applications(assertion, &mut ground_applications, &mut visited);
        }
        for root in self.exec.finitely_expanded_ground_roots() {
            self.exec
                .collect_uf_applications(root, &mut ground_applications, &mut visited);
        }
        for (surface, info) in self.exec.ctx.symbol_iter() {
            if ground_applications.contains_key(&(surface.to_string(), info.arg_sorts.len())) {
                identities.insert(
                    self.exec
                        .ctx
                        .symbol_identity_name(surface, info)
                        .to_string(),
                );
            }
        }
        // Deterministic order: the first offender must not depend on hash
        // iteration, or the reason string flaps between otherwise identical runs.
        let mut identities: Vec<String> = identities.into_iter().collect();
        identities.sort();
        for identity in identities {
            if let Some((_, _, Err(error))) = self.printed_uf_rows(&identity) {
                if matches!(
                    error,
                    super::super::output_format::PrintedUfTableRowsError::InconsistentFunctionTable { .. }
                ) {
                    return Some(error.to_string());
                }
            }
        }
        None
    }

    /// Read one printed table atom of `sort` into the gate's canonical value
    /// encoding; `None` when it does not parse into that encoding.
    fn read_printed_atom(&self, atom: &str, sort: &Sort) -> Option<ModelValue> {
        // Authenticated readings win: `parse_leaf` resolves exact-cell
        // class values (the model's own structured values, in the same
        // representation the gate's leaf path builds) before any
        // syntactic re-parse. Only when it yields nothing in the gate
        // encoding may the fallback below read the atom directly.
        if let Some(value) = self.parse_leaf(atom, sort) {
            if self.printed_atom_in_gate_encoding(&value, sort) {
                return Some(value);
            }
        }
        // A printed UF body can carry a concrete constructor tree for a
        // branching recursive datatype outside the narrower exact
        // array-cell fragment. Parse that bounded syntax through the
        // same schema-checked rendered-datatype reader used for datatype
        // UF pins; opaque carriers still fail here and stay unreadable.
        if self.datatype_guard().datatype_name(sort).is_some()
            && !self.exec.datatype_sort_carries_array_field(sort)
        {
            if let Some(value) =
                self.exec
                    .parse_rendered_dt_value_cached(atom, sort, self.datatype_guard())
            {
                if self.printed_atom_in_gate_encoding(&value, sort) {
                    return Some(value);
                }
            }
        }
        None
    }

    /// Decode the printer's ordered rows into the gate's canonical value
    /// encoding, refusing the whole interpretation if any atom is unreadable.
    pub(super) fn read_printed_uf_rows(
        &self,
        arg_sorts: &[Sort],
        result_sort: &Sort,
        rows: &[(Vec<String>, String)],
    ) -> Option<PrintedUfInterpretation> {
        let ctx = &self.exec.ctx;
        // Read the printed body back into gate values ONCE. An atom this view
        // cannot parse — or parses into anything but the gate's canonical
        // encoding for its sort — leaves the whole interpretation unreadable
        // (`None`): a partially readable body could match the wrong `ite` arm.
        // MEASURED instance of the encoding case: for a QF_UFDT enum
        // `(declare-datatype Unit ((u0) (u1)))` the EUF table of `f : Unit ->
        // Unit` is keyed by the class tokens `@Unit!N`, and `(get-model)`
        // prints `(ite (= x0 (as @Unit!1 Unit)) (as @Unit!0 Unit) ..)` while
        // the gate (and the printed constant `x`) hold the value as the
        // CONSTRUCTOR `u1` (#dt-element-canon). Those tokens would never match
        // a constructor-valued argument, so every read would fall to the
        // `else` arm; the table is therefore declared unreadable and the
        // application keeps today's pin-only read
        // (`test_enum_sat_lane_gate_excludes_uf_at_variable_args` pins that).
        let read_atom = |atom: &str, sort: &Sort| self.read_printed_atom(atom, sort);
        let Some((_, else_atom)) = rows.last() else {
            // Empty table => the printer emits the canonical constant body.
            let else_value = read_atom(
                &format_default_value_surface(ctx, result_sort)?,
                result_sort,
            )?;
            return Some(PrintedUfInterpretation {
                arity: arg_sorts.len(),
                rows: Vec::new(),
                else_value,
            });
        };
        let else_value = read_atom(else_atom, result_sort)?;
        let mut parsed_rows = Vec::with_capacity(rows.len() - 1);
        for (row_args, row_value) in rows.iter().take(rows.len() - 1) {
            if row_args.len() != arg_sorts.len() {
                return None;
            }
            let mut point = Vec::with_capacity(row_args.len());
            for (atom, sort) in row_args.iter().zip(arg_sorts) {
                point.push(read_atom(atom, sort)?);
            }
            parsed_rows.push((point, read_atom(row_value, result_sort)?));
        }
        Some(PrintedUfInterpretation {
            arity: arg_sorts.len(),
            rows: parsed_rows,
            else_value,
        })
    }

    /// Read one printed atom of `sort` for the answer route
    /// (#get-value-published-model):
    ///
    /// - a floating-point atom through [`printed_fp_value`], whose result is
    ///   encoded as the gate encodes a floating-point leaf
    ///   (`fp_value_to_independent_model`);
    /// - a String atom through [`published_string_value`] under `strings`;
    /// - every other atom through [`Self::read_printed_atom`], the gate's own
    ///   reader; when a string literal inside the atom does not spell its own
    ///   characters ([`nested_string_literals_are_verbatim`]), the value is
    ///   kept only if `Executor::format_gate_model_value` renders it back to
    ///   the atom.
    ///
    /// `None` when the atom does not decode.
    fn read_published_atom(
        &self,
        atom: &str,
        sort: &Sort,
        strings: StringTexts<'_>,
    ) -> Option<ModelValue> {
        match sort {
            Sort::FloatingPoint(eb, sb) => {
                fp_value_to_independent_model(&printed_fp_value(atom, *eb, *sb)?, sort)
            }
            Sort::String => published_string_value(atom, strings),
            _ => {
                let value = self.read_printed_atom(atom, sort)?;
                (nested_string_literals_are_verbatim(atom)
                    || self.exec.format_gate_model_value(&value, sort).as_deref() == Some(atom))
                .then_some(value)
            }
        }
    }

    /// Read the printer's ordered rows for the answer route
    /// (#get-value-published-model). Every key must decode
    /// ([`Self::read_published_atom`]), or the result is `None`. A cell keeps
    /// its printed text. A cell that mentions an abstract value of a datatype
    /// sort ([`Self::resolve_datatype_carriers`]) answers the cell with each
    /// such value replaced by its backing value, or nothing when one has no
    /// backing; any other cell answers its printed text. A cell carries a
    /// value only when its answer decodes. `rows` are
    /// the rows of a printed definition, the last one its else branch, and for
    /// an empty table the result is the canonical default body the printer
    /// emits. `euf_table` is the EUF function table `rows` were printed from
    /// ([`PrintedUfSource::table`]), when there is one; it fixes how
    /// String-sorted texts decode ([`StringTexts`]).
    pub(super) fn read_published_uf_cells(
        &self,
        arg_sorts: &[Sort],
        result_sort: &Sort,
        rows: &[(Vec<String>, String)],
        euf_table: Option<&[(Vec<String>, String)]>,
    ) -> Option<PublishedUfCells> {
        let entries = euf_table.map(|table| string_entries(table, arg_sorts, result_sort));
        let (key_texts, cell_texts) = match &entries {
            Some((keys, results)) => (StringTexts::EufTable(keys), StringTexts::EufTable(results)),
            None => (StringTexts::Rendered, StringTexts::Rendered),
        };
        let cell = |text: &str, texts: StringTexts<'_>| {
            let (answer, value) = match self.resolve_datatype_carriers(text, result_sort) {
                CellCarriers::None => (
                    CellAnswer::Printed,
                    self.read_published_atom(text, result_sort, texts),
                ),
                CellCarriers::Backed {
                    text: backed,
                    value,
                } => {
                    let value =
                        value.or_else(|| self.read_published_atom(&backed, result_sort, texts));
                    (CellAnswer::Backed(backed), value)
                }
                CellCarriers::Unbacked(carrier) => (CellAnswer::Unbacked(carrier), None),
            };
            PrintedCell {
                text: text.to_owned(),
                answer,
                value,
            }
        };
        let Some(((_, else_text), keyed)) = rows.split_last() else {
            let text = format_default_value_surface(&self.exec.ctx, result_sort)?;
            return Some(PublishedUfCells {
                arg_sorts: arg_sorts.to_vec(),
                rows: Vec::new(),
                else_cell: cell(&text, StringTexts::Rendered),
                default_body: true,
            });
        };
        let mut read_rows = Vec::with_capacity(keyed.len());
        for (row_args, row_value) in keyed {
            if row_args.len() != arg_sorts.len() {
                return None;
            }
            let mut point = Vec::with_capacity(row_args.len());
            for (atom, sort) in row_args.iter().zip(arg_sorts) {
                point.push(self.read_published_atom(atom, sort, key_texts)?);
            }
            read_rows.push((point, cell(row_value, cell_texts)));
        }
        Some(PublishedUfCells {
            arg_sorts: arg_sorts.to_vec(),
            rows: read_rows,
            else_cell: cell(else_text, cell_texts),
            default_body: false,
        })
    }

    /// The answer route's read of a datatype selector application `t` whose
    /// argument evaluated to `arg_values` (#get-value-published-model). `None`
    /// unless this is an answer view, `t` is a unary selector application, the
    /// argument's value is built by a constructor that does not own the
    /// selector, and `(get-model)` prints the selector's definition
    /// (`Executor::total_selector_definitions`: a table exists, the selector
    /// is not skipped, withheld or held under another surface name, and the
    /// argument has the selector's datatype). Otherwise `Some` of the value
    /// that printed definition gives at the argument: the first committed case
    /// whose key is decided equal to it, else the canonical default when every
    /// key is decided unequal; `Some(None)` when a key does not decode, a
    /// comparison is undecided first, or the selected text does not decode.
    pub(super) fn published_selector_value(
        &self,
        t: TermId,
        arg_values: &[ModelValue],
    ) -> Option<Option<ModelValue>> {
        let UfReadPolicy::Published(tables) = &self.uf_reads else {
            return None;
        };
        let TermData::App(sym, args) = self.exec.ctx.terms.get(t) else {
            return None;
        };
        let ([arg], [point @ ModelValue::Datatype { ctor, .. }]) = (args.as_slice(), arg_values)
        else {
            return None;
        };
        let selector = sym.name();
        let selector_tables = tables
            .selectors
            .get_or_init(|| self.exec.selector_tables(self.model).map(Rc::new))
            .clone()?;
        let (_, info) = selector_tables
            .infos
            .iter()
            .find(|(name, _)| name == selector)?;
        let arg_sort = self.exec.ctx.terms.sort(*arg);
        if info.ctors.iter().any(|owner| owner == ctor)
            || info.skip
            || selector_tables.dropped.contains(selector)
            || self
                .exec
                .ctx
                .overloaded_surface_name(selector)
                .is_some_and(|surface| surface != selector)
            || self.exec.datatype_sort_name(arg_sort).as_deref() != Some(info.dt_name.as_str())
        {
            return None;
        }
        for (key, value) in selector_tables
            .cases
            .get(selector)
            .map_or(&[][..], Vec::as_slice)
        {
            let Some(key) = self.read_published_atom(key, arg_sort, StringTexts::Rendered) else {
                return Some(None);
            };
            match decided_equal(&key, point, Some(arg_sort)) {
                Some(true) => {
                    return Some(self.read_published_atom(
                        value,
                        &info.ret_sort,
                        StringTexts::Rendered,
                    ))
                }
                Some(false) => {}
                None => return Some(None),
            }
        }
        Some(self.read_published_atom(
            &self.exec.canonical_default_value(&info.ret_sort),
            &info.ret_sort,
            StringTexts::Rendered,
        ))
    }

    /// The answer route's reading of the table `(get-model)` prints for
    /// `identity` (#get-value-published-model), derived once per answer
    /// session. `None` for a gate view, which reads printed tables through
    /// [`Self::printed_uf_interpretation`] instead.
    pub(super) fn published_uf_table(&self, identity: &str) -> Option<Rc<PublishedUfTable>> {
        let UfReadPolicy::Published(tables) = &self.uf_reads else {
            return None;
        };
        if let Some(hit) = tables.tables.borrow().get(identity) {
            return Some(Rc::clone(hit));
        }
        // No borrow is held while the table is derived: deriving it runs the
        // printer's row pipeline and the atom readers.
        let built = Rc::new(match self.printed_uf_source(identity) {
            None => PublishedUfTable::NotPrinted,
            Some(source) => match self.printed_uf_source_rows(&source) {
                Err(_) => PublishedUfTable::RowsFailed,
                Ok(rows) => {
                    let euf_table = source.from_euf_table.then_some(source.table.as_slice());
                    match self.read_published_uf_cells(
                        &source.arg_sorts,
                        &source.result_sort,
                        &rows,
                        euf_table,
                    ) {
                        Some(cells) => PublishedUfTable::Readable(cells),
                        None => PublishedUfTable::KeysUndecoded,
                    }
                }
            },
        });
        tables
            .tables
            .borrow_mut()
            .insert(identity.to_owned(), Rc::clone(&built));
        Some(built)
    }

    /// The answer route's reading of the certified total table `(get-model)`
    /// prints for `identity` (`Executor::format_certified_total_function` over
    /// the rendered rows and default of `Model::certified_total_ufs`), derived
    /// once per answer session. `None` when the model carries none for
    /// `identity`, when the printer would refuse the rows (a row of another
    /// arity, or one key rendered with two different cells), or when a key
    /// does not decode ([`Self::read_published_uf_cells`]).
    fn published_certified_total(
        &self,
        tables: &PublishedTables,
        identity: &str,
    ) -> Option<Rc<PublishedUfCells>> {
        if let Some(hit) = tables.certified.borrow().get(identity) {
            return hit.clone();
        }
        let built = self
            .model
            .certified_total_ufs
            .by_symbol
            .get(identity)
            .and_then(|total| {
                let mut printed: HashMap<&[String], &str> = HashMap::new();
                for (key, cell) in &total.rendered_rows {
                    if key.len() != total.arg_sorts.len()
                        || *printed.entry(key.as_slice()).or_insert(cell.as_str()) != cell.as_str()
                    {
                        return None;
                    }
                }
                let rows: Vec<(Vec<String>, String)> = total
                    .rendered_rows
                    .iter()
                    .cloned()
                    .chain(std::iter::once((
                        Vec::new(),
                        total.rendered_default.clone(),
                    )))
                    .collect();
                self.read_published_uf_cells(&total.arg_sorts, &total.result_sort, &rows, None)
            })
            .map(Rc::new);
        tables
            .certified
            .borrow_mut()
            .insert(identity.to_owned(), built.clone());
        built
    }

    /// The answer route's read, at the evaluated argument point `arg_values`,
    /// of an application `t` of a function `(get-model)` defines without a
    /// table (#get-value-published-model). `None` unless this is an answer
    /// view and one of these gives a value:
    ///
    /// - a certified total table whose signature is `t`'s: the value of the
    ///   cell [`PublishedUfCells::cell_at`] selects in
    ///   [`Self::published_certified_total`];
    /// - a formula-neutral function default: that default
    ///   (`Model::formula_neutral_function_default_for_application`).
    ///
    /// A constant-interpretation certificate is read by
    /// [`Self::certified_const_interp_value_at`] and
    /// [`Self::uf_app_value`], and a projection by the evaluator
    /// ([`ModelView::projection_argument`]); neither is read here.
    pub(super) fn published_definition_value(
        &self,
        t: TermId,
        arg_values: &[ModelValue],
    ) -> Option<ModelValue> {
        let UfReadPolicy::Published(tables) = &self.uf_reads else {
            return None;
        };
        let terms = &self.exec.ctx.terms;
        let TermData::App(symbol, args) = terms.get(t) else {
            return None;
        };
        let sort = terms.sort(t);
        if let Some(total) = self.model.certified_total_ufs.by_symbol.get(symbol.name()) {
            if &total.result_sort != sort
                || total.arg_sorts.len() != args.len()
                || args
                    .iter()
                    .zip(&total.arg_sorts)
                    .any(|(&arg, arg_sort)| terms.sort(arg) != arg_sort)
            {
                return None;
            }
            let cells = self.published_certified_total(tables, symbol.name())?;
            let value = cells.cell_at(arg_values)?.value.as_ref()?;
            if !super::super::recovery_admission::pay_model_value_copy(value) {
                return None;
            }
            return Some(value.clone());
        }
        match self.model.formula_neutral_function_default_for_application(
            &self.exec.ctx,
            symbol,
            args,
            sort,
        ) {
            Ok(Some(value)) => self.model_value_for(&value, sort),
            Ok(None) | Err(_) => None,
        }
    }

    /// [`Self::published_uf_table`] for the head of the application `t`;
    /// `None` when `t` is not an application with arguments.
    pub(super) fn published_uf_table_for_app(&self, t: TermId) -> Option<Rc<PublishedUfTable>> {
        let TermData::App(sym, args) = self.exec.ctx.terms.get(t) else {
            return None;
        };
        if args.is_empty() {
            return None;
        }
        self.published_uf_table(sym.name())
    }

    /// Whether this view must not read a per-term pin for `t`: true only for
    /// an answer view, and only when `t` mentions an application of a function
    /// whose table `(get-model)` prints. Such a term's value comes from the
    /// printed tables through the evaluator, or it has none.
    pub(super) fn pin_refused(&self, t: TermId) -> bool {
        match &self.uf_reads {
            UfReadPolicy::Gate => false,
            UfReadPolicy::Published(tables) => self.mentions_printed_table_application(tables, t),
        }
    }

    /// Whether `root` or any subterm is an application, with arguments, of a
    /// function whose [`Self::published_uf_table`] is not
    /// [`PublishedUfTable::NotPrinted`]. An iterative post-order walk over the
    /// term DAG, memoized in the session's `tables`.
    fn mentions_printed_table_application(&self, tables: &PublishedTables, root: TermId) -> bool {
        if let Some(&known) = tables.mentions.borrow().get(&root) {
            return known;
        }
        let terms = &self.exec.ctx.terms;
        let mut stack = vec![(root, false)];
        while let Some((term, children_done)) = stack.pop() {
            if tables.mentions.borrow().contains_key(&term) {
                continue;
            }
            let children = terms.children(term);
            if !children_done {
                stack.push((term, true));
                stack.extend(children.into_iter().map(|child| (child, false)));
                continue;
            }
            let own = match terms.get(term) {
                TermData::App(sym, args) if !args.is_empty() => !matches!(
                    self.published_uf_table(sym.name()).as_deref(),
                    None | Some(PublishedUfTable::NotPrinted)
                ),
                _ => false,
            };
            let mentions = own || {
                let memo = tables.mentions.borrow();
                children
                    .iter()
                    .any(|child| memo.get(child).copied().unwrap_or(false))
            };
            tables.mentions.borrow_mut().insert(term, mentions);
        }
        tables
            .mentions
            .borrow()
            .get(&root)
            .copied()
            .unwrap_or(false)
    }
}

/// The floating-point value of format `(eb, sb)` the printer spells `text`:
/// `(_ +zero eb sb)`, `(_ -zero eb sb)`, `(_ +oo eb sb)`, `(_ -oo eb sb)`,
/// `(_ NaN eb sb)` with the format's own indices, or `(fp s e m)` with `s`,
/// `e` and `m` bit-vector literals (`#b` or `#x`) of exactly 1, `eb` and
/// `sb - 1` bits. `None` for any other text, and for a format
/// [`FpModelValue::from_fields`] does not hold (an exponent wider than 63 bits
/// or a significand wider than 129 bits).
fn printed_fp_value(text: &str, eb: u32, sb: u32) -> Option<FpModelValue> {
    let inner = text.trim().strip_prefix('(')?.strip_suffix(')')?;
    let parts: Vec<&str> = inner.split_whitespace().collect();
    let (sign, exponent, significand) = match parts.as_slice() {
        ["_", special, e, s] => {
            if e.parse::<u32>().ok()? != eb
                || s.parse::<u32>().ok()? != sb
                || !(1..64).contains(&eb)
            {
                return None;
            }
            let all_ones = (1u64 << eb) - 1;
            match *special {
                "+zero" => (false, 0, 0),
                "-zero" => (true, 0, 0),
                "+oo" => (false, all_ones, 0),
                "-oo" => (true, all_ones, 0),
                "NaN" => (false, all_ones, 1),
                _ => return None,
            }
        }
        ["fp", s, e, m] => (
            printed_bits(s, 1)? == 1,
            u64::try_from(printed_bits(e, eb)?).ok()?,
            printed_bits(m, sb.checked_sub(1)?)?,
        ),
        _ => return None,
    };
    FpModelValue::from_fields(sign, exponent, significand, eb, sb)
}

/// The value of the bit-vector literal `text` (`#b` with exactly `width`
/// digits, or `#x` with exactly `width / 4` digits); `None` for any other
/// text or a width above 128 bits.
fn printed_bits(text: &str, width: u32) -> Option<u128> {
    if width == 0 || width > 128 {
        return None;
    }
    let (digits, radix, digit_bits) = text
        .strip_prefix("#b")
        .map(|digits| (digits, 2, 1))
        .or_else(|| text.strip_prefix("#x").map(|digits| (digits, 16, 4)))?;
    if u32::try_from(digits.len()).ok()?.checked_mul(digit_bits)? != width {
        return None;
    }
    u128::from_str_radix(digits, radix).ok()
}
