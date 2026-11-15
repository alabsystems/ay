// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The labels of an authored assertion that z3 surely reaches.
//!
//! z3 binds a `:named` label as soon as it reads it and stops a command at its
//! first error, so the labels after that error stay unbound. Whether a label
//! of an assertion is bound in z3's session therefore depends on z3 accepting
//! every subterm it reads before the label. Elaborating the assertion does
//! not answer that: this frontend accepts constructs some z3 versions reject
//! (outside `--z3-mode`, a Bool beside an Int in `=`, `distinct` or `ite`,
//! which z3 4.12.5 rejects and z3 5 coerces) and raises errors z3 does not.
//!
//! The walk reads the assertion in z3's order: an application's arguments
//! before its head, a `let`'s values before its body, a quantifier's binders
//! before its body and its body before its attributes, an annotated term
//! before its attributes. It stops at the first construct it cannot vouch
//! for; the labels read before that point are the ones z3 surely reaches.
//!
//! Under `--z3-mode` ([`Context::set_z3_mode`]) it vouches only for the
//! read-only sort check's fragment (`skipped_subterms::sort_check`), with
//! quantifiers over Bool, Int, Real, bit-vector and declared sorts whose
//! patterns apply declared functions, `:qid`, `:skolemid` and `:weight`
//! attributes, and labels z3 binds as fresh definitions. Outside it this
//! frontend's own reading stands, except at the constructs every z3 rejects
//! and this frontend accepts: a quantifier with no bound variable, and a
//! pattern that is a variable or a quantifier. The sort-dependent ones (a
//! non-numeric operand of arithmetic, an operator z3 does not know, a Bool
//! beside a number) are noted as elaboration meets them
//! ([`Context::note_construct_z3_may_reject`]).

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{Sort, TermId};

use super::{free_term_names, is_label_sort, node_address, LabelBinding, LabelSlot, NAMED};
use crate::command::{ParsedConstant, ParsedSort, Term as ParsedTerm};
use crate::elaborate::Context;
use crate::sexp::{SExpr, PARSE_STACK_RED_ZONE, PARSE_STACK_SIZE};

/// The walk met a construct it cannot vouch for: z3 may reject the command
/// there.
struct Stop;

impl Context {
    /// Record that a construct some z3 rejects was accepted at this point,
    /// outside `--z3-mode`, which rejects it: a Bool beside a number in `=`,
    /// `distinct` or `ite` or an SMT-LIB 2.7 conversion (z3 4.12.5 rejects
    /// them, z3 5 reads on), a non-numeric operand of arithmetic, or an
    /// operator no z3 knows. z3 stops the command there, so a label reached
    /// after it may be bound here and not in z3.
    pub(in crate::elaborate) fn note_construct_z3_may_reject(&mut self) {
        if let Some(journal) = self.label_journal.as_mut() {
            let reached = journal.visited.len();
            journal.z3_may_reject_from.get_or_insert(reached);
        }
    }

    /// Whether the current authored assertion has accepted a construct some
    /// z3 rejects.
    pub(in crate::elaborate) fn saw_construct_z3_may_reject(&self) -> bool {
        self.label_journal
            .as_ref()
            .is_some_and(|journal| journal.z3_may_reject_from.is_some())
    }

    /// The `:named` attributes of `root` that z3 reads with every subterm
    /// before them accepted, and whether z3 surely accepts all of `root`:
    /// only under `--z3-mode`, when the vouched walk reads it to the end.
    pub(super) fn labels_z3_surely_reaches(&self, root: &ParsedTerm) -> (HashSet<LabelSlot>, bool) {
        let mut reached = HashSet::default();
        let vouched_whole = if self.z3_mode {
            let mut walk = VouchedWalk {
                context: self,
                env: HashMap::default(),
                scope: Vec::new(),
                labels: Vec::new(),
                in_pattern: false,
                reached: &mut reached,
            };
            matches!(walk.term(root), Ok(Sort::Bool))
        } else {
            let _ = known_rejection_walk(root, &mut Vec::new(), &mut reached);
            false
        };
        (reached, vouched_whole)
    }
}

/// The `--z3-mode` walk: every construct must be one z3 4.12.5 and z3 5
/// accept, at the sorts the read-only sort check computes.
struct VouchedWalk<'a> {
    context: &'a Context,
    /// Always empty: an authored assertion is read with no outer bindings.
    env: HashMap<String, TermId>,
    /// `let` and quantifier variables in scope, innermost last.
    scope: Vec<(String, Sort)>,
    /// Labels z3 has bound earlier in the assertion.
    labels: Vec<(String, Sort)>,
    /// Set while a pattern term is read: the walk vouches there only for
    /// applications and symbols.
    in_pattern: bool,
    reached: &'a mut HashSet<LabelSlot>,
}

impl VouchedWalk<'_> {
    fn term(&mut self, term: &ParsedTerm) -> Result<Sort, Stop> {
        stacker::maybe_grow(PARSE_STACK_RED_ZONE, PARSE_STACK_SIZE, || match term {
            // z3 reads a numeral as an Int and coerces it where a Real is
            // wanted; that coercion is not modeled here.
            ParsedTerm::Const(ParsedConstant::Numeral(_)) if self.context.numeral_as_real => {
                Err(Stop)
            }
            ParsedTerm::Const(constant) => self.context.checked_constant_sort(constant).ok_or(Stop),
            ParsedTerm::Symbol(name) => self.symbol(name),
            ParsedTerm::App(name, args) if !args.is_empty() => {
                let mut sorts = Vec::with_capacity(args.len());
                for arg in args {
                    sorts.push(self.term(arg)?);
                }
                self.application(name, &sorts)
            }
            ParsedTerm::Let(..)
            | ParsedTerm::Forall(..)
            | ParsedTerm::Exists(..)
            | ParsedTerm::Annotated(..)
                if self.in_pattern =>
            {
                Err(Stop)
            }
            ParsedTerm::Let(bindings, body) if !bindings.is_empty() => {
                // The values are read before any of the let's own names is
                // bound.
                let mut values: Vec<(String, Sort)> = Vec::with_capacity(bindings.len());
                for (name, value) in bindings {
                    if values.iter().any(|(bound, _)| bound == name) {
                        return Err(Stop);
                    }
                    values.push((name.clone(), self.term(value)?));
                }
                self.scoped(values, |walk| walk.term(body))
            }
            ParsedTerm::Forall(vars, body) | ParsedTerm::Exists(vars, body) if !vars.is_empty() => {
                self.quantifier(vars, body)
            }
            ParsedTerm::Annotated(inner, attributes) => {
                let sort = self.term(inner)?;
                for (index, (keyword, value)) in attributes.iter().enumerate() {
                    if keyword != NAMED {
                        return Err(Stop);
                    }
                    self.label((node_address(term), index), inner, &sort, value)?;
                }
                Ok(sort)
            }
            _ => Err(Stop),
        })
    }

    fn in_scope(&self, name: &str) -> bool {
        self.scope.iter().any(|(bound, _)| bound == name)
    }

    fn label_sort(&self, name: &str) -> Option<&Sort> {
        self.labels
            .iter()
            .rev()
            .find(|(label, _)| label == name)
            .map(|(_, sort)| sort)
    }

    /// A bare symbol: a variable, then a label bound earlier in the
    /// assertion (a fresh name, so no other global shares it), then the
    /// context's definitions and declarations.
    fn symbol(&self, name: &str) -> Result<Sort, Stop> {
        if !self.in_scope(name) {
            if let Some(sort) = self.label_sort(name) {
                return Ok(sort.clone());
            }
        }
        self.context
            .skipped_symbol_sort(name, &self.env, &self.scope)
            .ok_or(Stop)
    }

    fn application(&self, name: &str, sorts: &[Sort]) -> Result<Sort, Stop> {
        // A label is a nullary definition and cannot be applied.
        if self.label_sort(name).is_some() {
            return Err(Stop);
        }
        self.context
            .skipped_application_sort(name, sorts, &self.env, &self.scope)
            .ok_or(Stop)
    }

    fn scoped<T>(&mut self, bound: Vec<(String, Sort)>, f: impl FnOnce(&mut Self) -> T) -> T {
        let mark = self.scope.len();
        self.scope.extend(bound);
        let out = f(self);
        self.scope.truncate(mark);
        out
    }

    /// z3 resolves the binders, reads the body and its attributes, and then
    /// requires a Boolean body.
    fn quantifier(
        &mut self,
        vars: &[(String, ParsedSort)],
        body: &ParsedTerm,
    ) -> Result<Sort, Stop> {
        let mut binders: Vec<(String, Sort)> = Vec::with_capacity(vars.len());
        for (name, sort) in vars {
            if binders.iter().any(|(bound, _)| bound == name) {
                return Err(Stop);
            }
            let sort = self.context.checked_declared_sort(sort).ok_or(Stop)?;
            binders.push((name.clone(), sort));
        }
        match self.scoped(binders, |walk| walk.quantifier_body(body))? {
            Sort::Bool => Ok(Sort::Bool),
            _ => Err(Stop),
        }
    }

    fn quantifier_body(&mut self, body: &ParsedTerm) -> Result<Sort, Stop> {
        let ParsedTerm::Annotated(inner, attributes) = body else {
            return self.term(body);
        };
        let sort = self.term(inner)?;
        for (index, (keyword, value)) in attributes.iter().enumerate() {
            match (keyword.as_str(), value) {
                (":pattern", SExpr::List(items)) if !items.is_empty() => {
                    for item in items {
                        self.pattern_term(item)?;
                    }
                }
                (":qid" | ":skolemid", SExpr::Symbol(_)) | (":weight", SExpr::Numeral(_)) => {}
                (NAMED, _) => {
                    self.label((node_address(body), index), inner, &sort, value)?;
                }
                _ => return Err(Stop),
            }
        }
        Ok(sort)
    }

    /// A pattern term z3 accepts: an application of a declared function. z3
    /// rejects a variable or a quantifier, and reads a list headed by a
    /// symbol in ways the walk does not model.
    fn pattern_term(&mut self, item: &SExpr) -> Result<(), Stop> {
        let term = ParsedTerm::from_sexp(item).map_err(|_| Stop)?;
        let ParsedTerm::App(head, args) = &term else {
            return Err(Stop);
        };
        let declared_function = !args.is_empty()
            && !self.in_scope(head)
            && self.context.symbols.contains_key(head)
            && !self.context.fun_defs.contains_key(head);
        if !declared_function {
            return Err(Stop);
        }
        self.in_pattern = true;
        let sort = self.term(&term);
        self.in_pattern = false;
        sort.map(drop)
    }

    /// z3 reaches the label. The walk reads on only past a label z3 binds as
    /// a fresh nullary definition, over a term with no `let` or quantifier
    /// variable in it: z3 rejects a label over a quantifier variable ("the
    /// expression contains free variables") and binds one over a `let` name
    /// to the expanded term, which this frontend leaves unbound.
    fn label(
        &mut self,
        slot: LabelSlot,
        inner: &ParsedTerm,
        sort: &Sort,
        value: &SExpr,
    ) -> Result<(), Stop> {
        self.reached.insert(slot);
        let SExpr::Symbol(name) = value else {
            return Err(Stop);
        };
        let mentions_variable = free_term_names(inner)
            .iter()
            .any(|free| self.in_scope(free));
        let fresh = matches!(self.context.classify_label(name, sort), LabelBinding::Fresh)
            && self.label_sort(name).is_none();
        if mentions_variable || !fresh || !is_label_sort(sort) {
            return Err(Stop);
        }
        self.labels.push((name.clone(), sort.clone()));
        Ok(())
    }
}

/// The walk outside `--z3-mode`: it stops only at a construct every z3
/// rejects and this frontend accepts. `bound` holds the variables in scope.
fn known_rejection_walk(
    term: &ParsedTerm,
    bound: &mut Vec<String>,
    reached: &mut HashSet<LabelSlot>,
) -> Result<(), Stop> {
    stacker::maybe_grow(PARSE_STACK_RED_ZONE, PARSE_STACK_SIZE, || match term {
        ParsedTerm::Const(_) | ParsedTerm::Symbol(_) => Ok(()),
        ParsedTerm::App(_, args)
        | ParsedTerm::IndexedApp(_, _, args)
        | ParsedTerm::QualifiedApp(_, _, args) => args
            .iter()
            .try_for_each(|arg| known_rejection_walk(arg, bound, reached)),
        ParsedTerm::Let(bindings, body) => {
            for (_, value) in bindings {
                known_rejection_walk(value, bound, reached)?;
            }
            let names = bindings.iter().map(|(name, _)| name.clone()).collect();
            with_bound(bound, names, |bound| {
                known_rejection_walk(body, bound, reached)
            })
        }
        ParsedTerm::Forall(vars, body) | ParsedTerm::Exists(vars, body) => {
            // "invalid quantifier, list of sorted variables is empty", raised
            // before the body is read.
            if vars.is_empty() {
                return Err(Stop);
            }
            let names = vars.iter().map(|(name, _)| name.clone()).collect();
            with_bound(bound, names, |bound| {
                let ParsedTerm::Annotated(inner, attributes) = body.as_ref() else {
                    return known_rejection_walk(body, bound, reached);
                };
                known_rejection_walk(inner, bound, reached)?;
                for (index, (keyword, value)) in attributes.iter().enumerate() {
                    if keyword == NAMED {
                        reached.insert((node_address(body), index));
                    } else if keyword == ":pattern" && pattern_is_rejected(value, bound) {
                        return Err(Stop);
                    }
                }
                Ok(())
            })
        }
        ParsedTerm::Lambda(vars, body) => {
            let names = vars.iter().map(|(name, _)| name.clone()).collect();
            with_bound(bound, names, |bound| {
                known_rejection_walk(body, bound, reached)
            })
        }
        ParsedTerm::Annotated(inner, attributes) => {
            known_rejection_walk(inner, bound, reached)?;
            for (index, (keyword, _)) in attributes.iter().enumerate() {
                if keyword == NAMED {
                    reached.insert((node_address(term), index));
                }
            }
            Ok(())
        }
        ParsedTerm::Match(scrutinee, cases) => {
            known_rejection_walk(scrutinee, bound, reached)?;
            for (pattern, body) in cases {
                let names = match pattern {
                    crate::command::MatchPattern::Symbol(name) => vec![name.clone()],
                    crate::command::MatchPattern::Constructor(_, fields) => fields.clone(),
                };
                with_bound(bound, names, |bound| {
                    known_rejection_walk(body, bound, reached)
                })?;
            }
            Ok(())
        }
    })
}

fn with_bound<T>(
    bound: &mut Vec<String>,
    names: Vec<String>,
    f: impl FnOnce(&mut Vec<String>) -> T,
) -> T {
    let mark = bound.len();
    bound.extend(names);
    let out = f(bound);
    bound.truncate(mark);
    out
}

/// Whether every z3 rejects a `:pattern` with this value: one of its terms
/// is a variable in scope or a quantifier ("patterns cannot be variables or
/// quantifiers"). A `let` name counts as a variable, which can only stop the
/// walk early.
fn pattern_is_rejected(value: &SExpr, bound: &[String]) -> bool {
    let SExpr::List(items) = value else {
        return false;
    };
    items.iter().any(|item| match item {
        SExpr::Symbol(name) => bound.contains(name),
        SExpr::List(parts) => matches!(
            parts.first().and_then(SExpr::as_symbol),
            Some("forall" | "exists" | "lambda")
        ),
        _ => false,
    })
}
