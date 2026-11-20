// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Abstract values of datatype sorts in the printed cells the answer route
//! reads (#get-value-published-model).
//!
//! The EUF tables `(get-model)` prints can hold, at a datatype sort, the
//! extractor's class token (`(as @B!0 B)`) instead of a constructor value. A
//! datatype sort has no values other than its constructor terms, so such a
//! cell is not a value of its sort, and repeating it can contradict the
//! assertions: under `(assert (= f (g u)))` and `(assert (= (g u) |a b|))` the
//! printed `g` is `(as @B!0 B)` while `f` prints `|a b|`.
//! [`IndependentModelView::resolve_datatype_carriers`] states what the answer
//! route reads in place of such a cell.

use super::super::datatype_array_fields::sexpr_items;
use super::super::rendered_dt_limits::MAX_RENDERED_DT_DEPTH;
use super::*;

/// What [`IndependentModelView::resolve_datatype_carriers`] found in a cell.
pub(super) enum CellCarriers {
    /// The cell mentions no abstract value of a datatype sort.
    None,
    /// Every such abstract value is backed; the cell with each replaced by
    /// its backing value, and that cell's value when the whole cell was one
    /// abstract value.
    Backed {
        text: String,
        value: Option<ModelValue>,
    },
    /// The printed text of an abstract value of a datatype sort that has no
    /// backing value.
    Unbacked(String),
}

/// `token` without the `|..|` quoting `ay_core::quote_symbol` gives it, when
/// `quote_symbol` writes the result back as `token`.
fn unquoted_symbol(token: &str) -> Option<String> {
    let bare = match token
        .strip_prefix('|')
        .and_then(|inner| inner.strip_suffix('|'))
    {
        Some(inner) => {
            let mut out = String::with_capacity(inner.len());
            let mut chars = inner.chars();
            while let Some(character) = chars.next() {
                if character == '\\' {
                    out.push(chars.next()?);
                } else {
                    out.push(character);
                }
            }
            out
        }
        None => token.to_owned(),
    };
    (ay_core::quote_symbol(&bare) == token).then_some(bare)
}

/// The datatype name of an extractor carrier token `@<name>!<n>`, `<n>` a
/// canonical decimal counter.
fn carrier_name(token: &str) -> Option<&str> {
    let (name, counter) = token.strip_prefix('@')?.rsplit_once('!')?;
    let canonical = counter.parse::<usize>().ok()?.to_string() == counter;
    (canonical && !name.is_empty()).then_some(name)
}

impl IndependentModelView<'_> {
    /// The answer route's reading of a printed cell `text` of `sort` that
    /// mentions an abstract value of a datatype sort (#get-value-published-model).
    ///
    /// An abstract value of a datatype sort is a subterm `(as A S)` where `A`
    /// is spelled as an extractor carrier token `@<name>!<n>` (with or without
    /// `|..|` quoting) whose `<name>` is a declared datatype
    /// ([`Self::datatype_carrier`]). It names an EUF class of the model, and
    /// it is backed when the model gives that class one constructor value
    /// ([`Self::backed_carrier`]). Each backed abstract value is replaced by
    /// that value, rendered by `Executor::format_gate_model_value`, and the
    /// result is [`CellCarriers::Backed`]; when one is not backed the result
    /// is [`CellCarriers::Unbacked`]; a cell with none is
    /// [`CellCarriers::None`].
    pub(super) fn resolve_datatype_carriers(&self, text: &str, sort: &Sort) -> CellCarriers {
        if !text.contains('@') {
            return CellCarriers::None;
        }
        match self.resolve_carriers_at(text, Some(sort), 0) {
            Ok(None) => CellCarriers::None,
            Ok(Some((text, value))) => CellCarriers::Backed { text, value },
            Err(carrier) => CellCarriers::Unbacked(carrier),
        }
    }

    /// [`Self::resolve_datatype_carriers`] at nesting `depth`: `Ok(None)` when
    /// `text` mentions no abstract value of a datatype sort, `Ok(Some)` of the
    /// replaced text (with the value when `text` is one abstract value), and
    /// `Err` of an unbacked abstract value, or of `text` when it nests past
    /// `MAX_RENDERED_DT_DEPTH`.
    fn resolve_carriers_at(
        &self,
        text: &str,
        sort: Option<&Sort>,
        depth: usize,
    ) -> Result<Option<(String, Option<ModelValue>)>, String> {
        if !text.contains('@') {
            return Ok(None);
        }
        if depth > MAX_RENDERED_DT_DEPTH {
            return Err(text.to_owned());
        }
        let Some(items) = sexpr_items(text) else {
            return Ok(None);
        };
        if let [head, token, sort_text] = items.as_slice() {
            if head == "as" {
                if let Some(carrier) = self.datatype_carrier(token) {
                    return self
                        .backed_carrier(&carrier, sort_text, sort)
                        .map(|(rendered, value)| Some((rendered, Some(value))))
                        .ok_or_else(|| text.trim().to_owned());
                }
            }
        }
        let mut changed = false;
        let mut parts = Vec::with_capacity(items.len());
        for item in &items {
            match self.resolve_carriers_at(item, None, depth + 1)? {
                Some((replaced, _)) => {
                    changed = true;
                    parts.push(replaced);
                }
                None => parts.push(item.clone()),
            }
        }
        Ok(changed.then(|| (format!("({})", parts.join(" ")), None)))
    }

    /// The unquoted `token` when it is spelled as an extractor carrier token
    /// of a declared datatype. A constructor of that datatype can have the
    /// same spelling (`|@E!0|`); the cell's text does not say which of the
    /// two it holds, so it is read through the class the model gives that
    /// token, whose constructor terms then include that constructor when the
    /// cell holds it.
    fn datatype_carrier(&self, token: &str) -> Option<String> {
        let bare = unquoted_symbol(token)?;
        let name = carrier_name(&bare)?;
        self.exec
            .ctx
            .datatype_iter()
            .any(|(datatype, _)| datatype == name)
            .then_some(bare)
    }

    /// The rendered backing value of the abstract value `carrier` at the sort
    /// spelled `sort_text`, and that value; `None` when it has none. The
    /// sort is `known` when that is the sort spelled `sort_text`, and
    /// otherwise the sort, spelled `sort_text`, of an index entry or a
    /// constructor term of `carrier`'s class.
    ///
    /// The candidates are the value the exact datatype cell index holds for
    /// `carrier` at that sort ([`Self::exact_datatype_cell_value`]) and the
    /// value of each constructor term of that sort in `carrier`'s EUF class
    /// ([`Self::class_constructor_terms`], [`Self::constructor_term_value`]).
    /// The value is backed when there is at least one candidate, every
    /// constructor term has a value, the index does not hold `carrier` as
    /// conflicting, and [`decided_equal`] decides every candidate equal to
    /// the first. Memoized per answer session.
    fn backed_carrier(
        &self,
        carrier: &str,
        sort_text: &str,
        known: Option<&Sort>,
    ) -> Option<(String, ModelValue)> {
        let UfReadPolicy::Published(tables) = &self.uf_reads else {
            return self.derive_backed_carrier(carrier, sort_text, known);
        };
        let key = (carrier.to_owned(), sort_text.to_owned());
        if let Some(hit) = tables.carrier_values.borrow().get(&key) {
            let (_, value) = hit.as_ref()?;
            if !super::super::recovery_admission::pay_model_value_copy(value) {
                return None;
            }
            return hit.clone();
        }
        // No borrow is held while the value is derived: deriving it runs the
        // evaluator.
        let derived = self.derive_backed_carrier(carrier, sort_text, known);
        tables
            .carrier_values
            .borrow_mut()
            .insert(key, derived.clone());
        derived
    }

    /// [`Self::backed_carrier`] without the answer session's memo.
    fn derive_backed_carrier(
        &self,
        carrier: &str,
        sort_text: &str,
        known: Option<&Sort>,
    ) -> Option<(String, ModelValue)> {
        let ctx = &self.exec.ctx;
        let terms = &ctx.terms;
        let spelled =
            |sort: &Sort| crate::executor_format::format_sort_surface(ctx, sort) == sort_text;
        let index = self
            .exact_datatype_cells
            .get_or_init(|| self.build_exact_datatype_cell_values());
        let members = self.class_constructor_terms(carrier);
        let sort = match known.filter(|sort| spelled(sort)) {
            Some(sort) => sort.clone(),
            None => index
                .keys()
                .find(|sort| spelled(sort))
                .or_else(|| {
                    members
                        .iter()
                        .map(|&member| terms.sort(member))
                        .find(|sort| spelled(sort))
                })?
                .clone(),
        };
        let name = carrier_name(carrier)?;
        if self.exec.datatype_sort_name(&sort).as_deref() != Some(name) {
            return None;
        }
        let mut candidates = Vec::new();
        match index.get(&sort).and_then(|entries| entries.get(carrier)) {
            Some(None) => return None,
            Some(Some(_)) => candidates.push(self.exact_datatype_cell_value(carrier, &sort)?),
            None => {}
        }
        for &member in members
            .iter()
            .filter(|&&member| terms.sort(member) == &sort)
        {
            candidates.push(self.constructor_term_value(member, &sort)?);
        }
        let (first, rest) = candidates.split_first()?;
        if !rest
            .iter()
            .all(|other| decided_equal(first, other, Some(&sort)) == Some(true))
        {
            return None;
        }
        let rendered = self.exec.format_gate_model_value(first, &sort)?;
        Some((rendered, first.clone()))
    }

    /// The constructor terms whose EUF class the model names `carrier`
    /// (`EufModel::term_values`, [`Self::is_constructor_term`]), at most
    /// `MAX_CONSTRUCTOR_TERM_NODES` nodes each. Their values need no read of
    /// a declared function. Indexed once per answer session; empty for a gate
    /// view.
    fn class_constructor_terms(&self, carrier: &str) -> Vec<TermId> {
        let UfReadPolicy::Published(tables) = &self.uf_reads else {
            return Vec::new();
        };
        tables
            .constructor_members
            .get_or_init(|| {
                let mut members: HashMap<String, Vec<TermId>> = HashMap::new();
                let Some(euf) = self.model.euf_model.as_ref() else {
                    return members;
                };
                let constructors: HashSet<&str> = self
                    .exec
                    .ctx
                    .datatype_iter()
                    .flat_map(|(_, constructors)| constructors.iter().map(String::as_str))
                    .collect();
                for (&term, token) in &euf.term_values {
                    if token.starts_with('@') && self.is_constructor_term(term, &constructors) {
                        members.entry(token.clone()).or_default().push(term);
                    }
                }
                for terms in members.values_mut() {
                    terms.sort_unstable();
                }
                members
            })
            .get(carrier)
            .cloned()
            .unwrap_or_default()
    }

    /// Whether `root` is a constructor term: a nullary constructor of its
    /// datatype sort written as a constant (`TermData::Var`, the form the
    /// enumerated-datatype lanes give it; [`Self::nullary_constructor_leaf`]),
    /// or a datatype constructor application whose arguments are constructor
    /// terms or literal constants, in at most `MAX_CONSTRUCTOR_TERM_NODES`
    /// nodes. `constructors` holds the name of every declared constructor.
    fn is_constructor_term(&self, root: TermId, constructors: &HashSet<&str>) -> bool {
        let ctx = &self.exec.ctx;
        let mut stack = vec![root];
        let mut nodes = 0usize;
        while let Some(term) = stack.pop() {
            nodes += 1;
            if nodes > MAX_CONSTRUCTOR_TERM_NODES {
                return false;
            }
            match ctx.terms.get(term) {
                TermData::Const(_) if term != root => {}
                TermData::Var(name, _) => {
                    if !constructors.contains(name.as_str())
                        || self
                            .nullary_constructor_leaf(term, ctx.terms.sort(term))
                            .is_none()
                    {
                        return false;
                    }
                }
                TermData::App(symbol, args) if ctx.is_constructor(symbol.name()).is_some() => {
                    stack.extend(args.iter().copied());
                }
                _ => return false,
            }
        }
        true
    }

    /// The value of the constructor term `term` of `sort`
    /// ([`Self::is_constructor_term`]): the nullary constructor a constant
    /// names, or the evaluator's value of an application.
    fn constructor_term_value(&self, term: TermId, sort: &Sort) -> Option<ModelValue> {
        if let TermData::Var(..) = self.exec.ctx.terms.get(term) {
            return self.nullary_constructor_leaf(term, sort);
        }
        match ay_model_check::evaluate_term(&self.exec.ctx.terms, self, term) {
            EvalOutcome::Value(value) => Some(value),
            EvalOutcome::Unevaluable(_) => None,
        }
    }
}

/// The most nodes [`IndependentModelView::is_constructor_term`] walks in one
/// term.
const MAX_CONSTRUCTOR_TERM_NODES: usize = 1_024;
