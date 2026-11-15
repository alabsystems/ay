// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `:named` labels in authored assertions.
//!
//! SMT-LIB 2.6 (section 3.6.5) and z3 make `(! t :named a)` define `a` as a
//! nullary macro for `t`, exactly as `(define-fun a () S t)` would: the name
//! lives in the ordinary function namespace, follows the scoping of
//! definitions (removed by `pop` unless `:global-declarations` is set, kept by
//! `reset-assertions`), collides with other definitions and declarations, and
//! can be used as a term once its `!` has closed.
//!
//! Proofs are the one place a label differs from a `define-fun`: a checker
//! such as carcara expands the label instead of holding `(= a t)` as a
//! premise, so the label gets no `define-fun` proof authority
//! ([`Context::source_nullary_definition_for_proof`]).
//!
//! Only the labels written in an authored `assert` are bound this way. The
//! assertion's labels are collected by node address before elaboration, so a
//! label reached through a macro body or a re-elaboration of a retained
//! assertion never binds a second time. Labels are held pending while the
//! assertion elaborates, and become definitions only when the assertion is
//! accepted.
//!
//! A command that z3 rejects at a label (the name is already a nullary
//! definition, or a nullary declaration of the same sort, the value is not a
//! symbol, or the labeled term has free variables) is rejected here with z3's
//! message, keeping the labels accepted before that one as z3 does. That
//! relies on z3 accepting every subterm it reads before the label, which
//! [`z3_reach`] establishes or not; the subterms elaboration passes over are
//! read here too (`skipped_subterms`). Any other error leaves the labels in
//! an unknown state: z3 may not raise it, or raise it at another point, and
//! go on to bind labels this context does not. A label z3
//! accepts but this frontend cannot bind the same way (an overload of an
//! existing name, a builtin name, a label over a `let`-bound name, a sort
//! without a plain surface spelling) is left unbound, as every label was
//! before labels became definitions: the assertion is accepted with its full
//! meaning, which a label does not change, and the outcome is reported as
//! [`LabelFailure::Unbound`], with the names in
//! [`Context::unbound_label_names`]. z3 defines those names and this context
//! does not, so a later command that mentions one may mean something else
//! here.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{Sort, TermId};

use crate::command::Term as ParsedTerm;
use crate::sexp::SExpr;

use super::{
    Context, DeclarationKind, ElaborateError, PublicSort, Result, SymbolBindingOrigin, SymbolInfo,
};

mod syntax;
mod z3_reach;
pub(super) use syntax::free_term_names;
pub use syntax::term_has_named_label;
use syntax::{authored_label_slots, is_builtin_bare_symbol, strip_named};

const NAMED: &str = ":named";

/// How the last authored assertion carrying `:named` labels ended, when it did
/// not simply bind all of them.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum LabelFailure {
    /// The assertion was rejected at a label for the reason z3 rejects it,
    /// and z3 surely reaches that label. The labels before that one are
    /// bound, as z3 binds them, so the context is in the state z3 is in after
    /// the failed command.
    Exact,
    /// The context may no longer match z3's: the assertion was rejected by
    /// an error other than a label's, or at a label z3 may not reach; a
    /// label was reached out of z3's order or not at all; or a subterm z3
    /// reads could not be checked.
    Diverged,
    /// The assertion was accepted with its full meaning, as z3 accepts it,
    /// and every label was reached in z3's order, but some labels z3 binds
    /// were left unbound here ([`Context::unbound_label_names`]). The context
    /// matches z3's except for those names.
    Unbound,
    /// Under `--z3-mode`: the assertion was accepted and its labels bound as
    /// this frontend reads it, but z3 may stop before some of them, at a
    /// subterm before a label whose acceptance the read-only walk does not
    /// establish (`z3_reach`). z3 mode rejects every construct this frontend
    /// is known to accept and z3 to reject, so z3 is taken to keep the
    /// assertion; the context may differ from z3's in the assertion's label
    /// names, and only there. Outside z3 mode the same outcome is
    /// [`LabelFailure::Diverged`]: there the subterm may be one this
    /// frontend's dialect accepts and every z3 rejects.
    Unvouched,
}

/// A label accepted during the current assertion, not yet a definition.
#[derive(Debug, Clone)]
struct PendingLabel {
    name: String,
    body: ParsedTerm,
    sort: Sort,
}

/// One `:named` attribute of the authored assertion: the address of its
/// annotation node and the attribute's position in that node.
pub(in crate::elaborate) type LabelSlot = (usize, usize);

/// Label state for one authored assertion.
#[derive(Debug, Clone, Default)]
pub(super) struct LabelJournal {
    /// The assertion's own `:named` attributes.
    authored: HashSet<LabelSlot>,
    /// Authored attributes that have been processed.
    visited: HashSet<LabelSlot>,
    /// Whether elaboration reaches the labels in z3's parse order. A label
    /// in a `let` binding, a `match` or another attribute's value may be
    /// reached out of order or not at all.
    in_parse_order: bool,
    pending: Vec<PendingLabel>,
    /// Quantifier and lambda binder variables open at the current point.
    binders: Vec<TermId>,
    /// The label that rejected the assertion, as z3 rejects it.
    rejected: Option<LabelSlot>,
    /// Labels z3 would bind that were left unbound.
    unbound: Vec<String>,
    /// Set when a subterm z3 reads could not be checked, so the labels z3
    /// binds in it are not known.
    unchecked: bool,
    /// How many labels had been reached when the first construct some z3
    /// rejects was accepted (`note_construct_z3_may_reject`).
    z3_may_reject_from: Option<usize>,
    /// Set when a subterm elaboration passes over held a label, which was
    /// read in a scratch copy (`skipped_subterms`).
    skipped_labels: bool,
}

fn node_address(term: &ParsedTerm) -> usize {
    std::ptr::from_ref(term) as usize
}

/// Sorts a label can have here: those whose public sort is the engine sort.
fn is_label_sort(sort: &Sort) -> bool {
    matches!(sort, Sort::Bool | Sort::Int | Sort::Real | Sort::BitVec(_))
}

/// What binding a new label would make, by z3's rules.
enum LabelBinding {
    Fresh,
    /// z3 rejects the command with this message.
    Rejected(String),
    /// z3 accepts the label (an overload of an existing name or a builtin
    /// name); this frontend cannot represent it as a definition.
    Unsupported,
}

impl Context {
    /// Assert an authored term, binding its `:named` labels as definitions.
    pub(super) fn assert_authored_with_labels(&mut self, term: &ParsedTerm) -> Result<()> {
        self.label_failure = None;
        self.unbound_label_names.clear();
        let (authored, in_parse_order) = authored_label_slots(term);
        if authored.is_empty() && in_parse_order {
            return self.with_skip_journal(term, |ctx| ctx.assert_authored(term));
        }
        let label_count = authored.len();
        // Read before the journal is installed: the walk classifies label
        // names as the empty journal leaves them.
        let (reached, vouched_whole) = self.labels_z3_surely_reaches(term);
        let all_reached = authored.iter().all(|slot| reached.contains(slot));
        let outer = self.label_journal.replace(LabelJournal {
            authored,
            in_parse_order,
            ..LabelJournal::default()
        });
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            self.with_skip_journal(term, |ctx| ctx.assert_authored(term))
        }));
        let journal = std::mem::replace(&mut self.label_journal, outer).unwrap_or_default();
        let result = match result {
            Ok(result) => result,
            Err(payload) => {
                self.label_failure = Some(LabelFailure::Diverged);
                std::panic::resume_unwind(payload)
            }
        };
        // A label in a subterm elaboration passes over counts as bound as z3
        // binds it only under `--z3-mode`: in an accepted assertion when z3
        // surely accepts all of it, since z3 may otherwise reject the
        // assertion at a construct this frontend accepts and keep the label
        // without the assertion; in a rejected one when the walk vouches for
        // every subterm before the rejecting label, as for any label. Plain
        // mode's dialect leaves both unknown.
        let skipped_label_accepted_unvouched =
            journal.skipped_labels && !(self.z3_mode && vouched_whole);
        let skipped_label_rejected_unvouched = journal.skipped_labels && !self.z3_mode;
        match result {
            Ok(()) => {
                let label_after_z3_may_reject = journal
                    .z3_may_reject_from
                    .is_some_and(|reached_before| journal.visited.len() > reached_before);
                self.commit_labels(journal.pending);
                if journal.unchecked
                    || skipped_label_accepted_unvouched
                    || journal.visited.len() != label_count
                    || !journal.in_parse_order
                {
                    self.label_failure = Some(LabelFailure::Diverged);
                } else if !journal.unbound.is_empty() {
                    self.label_failure = Some(LabelFailure::Unbound);
                    self.unbound_label_names = journal.unbound;
                } else if !all_reached || label_after_z3_may_reject {
                    // Outside z3 mode the assertion itself may be one every
                    // z3 rejects (this frontend's dialect accepts it), so not
                    // only the label names may differ from z3's session.
                    self.label_failure = Some(if self.z3_mode {
                        LabelFailure::Unvouched
                    } else {
                        LabelFailure::Diverged
                    });
                }
                Ok(())
            }
            Err(error) => {
                let exact = journal.in_parse_order
                    && journal.unbound.is_empty()
                    && !journal.unchecked
                    && !skipped_label_rejected_unvouched
                    && journal.z3_may_reject_from.is_none()
                    && journal.rejected.is_some_and(|slot| reached.contains(&slot));
                if exact {
                    // z3 reaches this label with every subterm before it
                    // accepted, rejects the assertion there and keeps the
                    // labels it bound before it.
                    self.commit_labels(journal.pending);
                    self.label_failure = Some(LabelFailure::Exact);
                } else {
                    // Any other error: z3 may not raise it, or raise it at
                    // another point, and bind labels this context does not.
                    self.label_failure = Some(LabelFailure::Diverged);
                }
                Err(error)
            }
        }
    }

    /// Define each accepted label as a nullary macro, registered as
    /// `define-fun` registers one except for its binding origin, which keeps
    /// the label out of `define-fun` proof authority. The body is not
    /// elaborated again: it was elaborated, closed, as part of the assertion,
    /// and a second elaboration is not free of side effects on the term store.
    fn commit_labels(&mut self, pending: Vec<PendingLabel>) {
        for PendingLabel { name, body, sort } in pending {
            let public_sort = PublicSort::from_engine(&sort);
            self.fun_defs
                .insert(name.clone(), (Vec::new(), sort.clone(), body));
            let internal_name = self.ordinary_source_binding_internal_name(&name);
            self.track_scoped_symbol(&name);
            self.symbols.insert(
                name.clone(),
                SymbolInfo::fresh_with_binding_origin(
                    None,
                    sort,
                    Vec::new(),
                    public_sort,
                    Vec::new(),
                    internal_name,
                    DeclarationKind::Defined,
                    SymbolBindingOrigin::NamedLabel,
                ),
            );
            self.track_scoped_fun_def(name.clone());
            self.advance_source_revision_introducing(&name);
        }
    }

    /// How the last authored assertion with `:named` labels ended, if it did
    /// not simply bind all of them. Reading it clears it.
    pub fn take_label_failure(&mut self) -> Option<LabelFailure> {
        self.label_failure.take()
    }

    /// The labels the last authored assertion left unbound when it ended as
    /// [`LabelFailure::Unbound`].
    #[must_use]
    pub fn unbound_label_names(&self) -> &[String] {
        &self.unbound_label_names
    }

    /// Record that a subterm z3 reads could not be checked, so the labels z3
    /// binds in it are not known.
    pub(super) fn note_unchecked_label_subterm(&mut self) {
        if let Some(journal) = self.label_journal.as_mut() {
            journal.unchecked = true;
        }
    }

    /// Record that a subterm elaboration passes over, holding a label, was
    /// read in a scratch copy and its labels carried back.
    pub(super) fn note_skipped_label_subterm(&mut self) {
        if let Some(journal) = self.label_journal.as_mut() {
            journal.skipped_labels = true;
        }
    }

    /// Run `f` with `vars` recorded as open binders for label checks.
    pub(super) fn with_label_binders<T>(
        &mut self,
        vars: &[TermId],
        f: impl FnOnce(&mut Self) -> T,
    ) -> T {
        let Some(journal) = self.label_journal.as_mut() else {
            return f(self);
        };
        let mark = journal.binders.len();
        journal.binders.extend_from_slice(vars);
        let out = f(self);
        if let Some(journal) = self.label_journal.as_mut() {
            journal.binders.truncate(mark);
        }
        out
    }

    /// The body of a label accepted earlier in the current assertion.
    pub(super) fn pending_label_body(&self, name: &str) -> Option<ParsedTerm> {
        let journal = self.label_journal.as_ref()?;
        journal
            .pending
            .iter()
            .rev()
            .find(|label| label.name == name)
            .map(|label| label.body.clone())
    }

    /// The sort of a label accepted earlier in the current assertion.
    pub(super) fn pending_label_sort(&self, name: &str) -> Option<Sort> {
        let journal = self.label_journal.as_ref()?;
        journal
            .pending
            .iter()
            .rev()
            .find(|label| label.name == name)
            .map(|label| label.sort.clone())
    }

    /// Handle one `:named` attribute. `node` is the annotation node, `inner`
    /// the labeled term and `term_id` its elaboration under `env`.
    pub(super) fn record_label(
        &mut self,
        node: &ParsedTerm,
        index: usize,
        inner: &ParsedTerm,
        term_id: TermId,
        value: &SExpr,
        env: &HashMap<String, TermId>,
    ) -> Result<()> {
        let slot = (node_address(node), index);
        let authored = self.label_journal.as_ref().is_some_and(|journal| {
            journal.authored.contains(&slot) && !journal.visited.contains(&slot)
        });
        if !authored {
            self.record_named_term(term_id, value);
            return Ok(());
        }
        let name = match value {
            SExpr::Symbol(name) => name.clone(),
            SExpr::True => "true".to_string(),
            SExpr::False => "false".to_string(),
            _ => return self.reject_label(slot, "invalid attribute value, symbol expected"),
        };
        // z3's order: free variables, then the name.
        let free: Vec<String> = free_term_names(inner)
            .into_iter()
            .filter(|name| env.contains_key(name))
            .collect();
        if !free.is_empty() && self.label_mentions_open_binder(&free, env) {
            return self.reject_label(
                slot,
                "invalid named expression, expression contains free variables",
            );
        }
        let sort = self.terms.sort(term_id).clone();
        match self.classify_label(&name, &sort) {
            LabelBinding::Fresh => {}
            LabelBinding::Rejected(message) => return self.reject_label(slot, &message),
            LabelBinding::Unsupported => {
                self.leave_label_unbound(slot, name, term_id, value);
                return Ok(());
            }
        }
        // z3 binds a label over a `let`- or `match`-bound name, and one of any
        // sort; this frontend binds neither as a definition.
        if !free.is_empty() || !is_label_sort(&sort) {
            self.leave_label_unbound(slot, name, term_id, value);
            return Ok(());
        }
        let body = strip_named(inner);
        self.record_named_term(term_id, value);
        if let Some(journal) = self.label_journal.as_mut() {
            journal.visited.insert(slot);
            journal.pending.push(PendingLabel { name, body, sort });
        }
        Ok(())
    }

    fn reject_label(&mut self, slot: LabelSlot, message: &str) -> Result<()> {
        if let Some(journal) = self.label_journal.as_mut() {
            journal.rejected = Some(slot);
        }
        Err(ElaborateError::Redefinition(message.to_string()))
    }

    /// Keep a label z3 would bind as a plain name for the labeled term, the
    /// way every label was kept before labels became definitions. The term is
    /// elaborated in full either way; only the definition is missing.
    fn leave_label_unbound(
        &mut self,
        slot: LabelSlot,
        name: String,
        term_id: TermId,
        value: &SExpr,
    ) {
        self.record_named_term(term_id, value);
        if let Some(journal) = self.label_journal.as_mut() {
            journal.visited.insert(slot);
            journal.unbound.push(name);
        }
    }

    /// Whether any of `names` is bound in `env` to a term that mentions an
    /// open quantifier or lambda binder.
    fn label_mentions_open_binder(&self, names: &[String], env: &HashMap<String, TermId>) -> bool {
        let Some(journal) = self.label_journal.as_ref() else {
            return false;
        };
        if journal.binders.is_empty() {
            return false;
        }
        let binders: HashSet<TermId> = journal.binders.iter().copied().collect();
        let mut seen: HashSet<TermId> = HashSet::default();
        let mut stack: Vec<TermId> = names
            .iter()
            .filter_map(|name| env.get(name))
            .copied()
            .collect();
        while let Some(id) = stack.pop() {
            if !seen.insert(id) {
                continue;
            }
            if binders.contains(&id) {
                return true;
            }
            stack.extend(self.terms.children(id));
        }
        false
    }

    fn classify_label(&self, name: &str, sort: &Sort) -> LabelBinding {
        // A label of this assertion that z3 binds, whether this frontend
        // bound it or left it unbound, is already a definition for z3.
        let pending = self.label_journal.as_ref().is_some_and(|journal| {
            journal.pending.iter().any(|label| label.name == name)
                || journal.unbound.iter().any(|unbound| unbound == name)
        });
        let nullary_macro = self
            .fun_defs
            .get(name)
            .is_some_and(|(params, _, _)| params.is_empty())
            && !self.recursive_fun_names.contains(name);
        if pending || nullary_macro {
            return LabelBinding::Rejected("named expression already defined".to_string());
        }
        if self.has_symbol_with_signature(name, &[], sort) {
            return LabelBinding::Rejected(format!(
                "invalid named expression, declaration already defined with this name {name}"
            ));
        }
        let builtin = is_builtin_bare_symbol(name)
            || super::excluded_declarable_op_class(name).is_some()
            || self.is_reserved_symbol_on_this_route(name)
            || super::is_declaration_activated_op_name(name)
            || self.is_datatype_member_name(name);
        let bound = self.has_symbol_binding(name)
            || self.internal_symbols.contains(name)
            || self
                .polymorphic_declarations
                .iter()
                .any(|declaration| declaration.name == name);
        if builtin || bound {
            return LabelBinding::Unsupported;
        }
        LabelBinding::Fresh
    }
}
