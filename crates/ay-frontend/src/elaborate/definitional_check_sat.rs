// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #defmacro-named-preuse: check-sat-time adoption of definitional foralls.
//!
//! [`Context::try_adopt_definitional_forall`] is the assert-time macro finder:
//! `(assert (forall X. (= (f X) body)))` over a never-yet-used declared `f`
//! registers `f := λX. body` and every LATER application expands. z3's
//! `macro_finder` differs in one way that matters to verifier embedders: it
//! runs over the COMPLETE assertion set at solve time, so a definition that
//! arrives after a use of `f` (`(assert (= out (f i)))` then the defining
//! forall — the shape deductive-checks emits for every spec function, where the call
//! is lowered before the callee's axiom) is still a macro there, while the
//! assert-time rule here had to refuse it: a raw pre-macro occurrence would
//! constrain a DIFFERENT, disconnected `f`. Refused, the definition stays a
//! quantifier, and the obligation that is ground LIA after expansion instead
//! fails closed through the quantifier engines (`quantifier-cegqi` unknown on
//! the captured deductive-checks `proof_in_spec` query; z3 answers `sat` on it).
//!
//! This pass closes that gap at the first `check-sat` of a session, in the
//! outermost scope: every retained definitional forall whose head passes
//! every assert-time guard EXCEPT the hard-assertion pre-use rule is adopted,
//! and then EVERY retained parsed assertion is re-elaborated with the new
//! macros registered, so the earlier raw occurrences expand too. That is
//! exactly why the pre-use hazard cannot arise here: after the pass no raw
//! occurrence of `f` survives anywhere on the stack (the definition itself
//! re-elaborates to the reflexive tautology). The soundness argument is the
//! assert-time one unchanged (a definitional extension, Shoenfield §4.6:
//! `ψ ∧ ∀x. f(x) = t` with `f` not in `t` is conservative over `ψ[f := λx. t]`
//! in both polarities); re-elaboration merely applies the substitution to
//! the assertions that were already there.
//!
//! Fail-closed conditions, each keeping the byte-identical status quo:
//!
//! * outermost scope, first satisfiability-check command of the session,
//!   `check-sat` or `check-sat-assuming` (a later check may already have
//!   encoded the raw assertions into
//!   persistent incremental theory state, and adopting then would only add a
//!   second, expanded copy), and not while a schematic instance is being
//!   elaborated;
//! * the `check-sat` COMMAND route only (the native API's `check_sat` does
//!   not run it, and `parse_smtlib2` skips a script's own `check-sat`): a
//!   native caller may hold a raw, not-yet-asserted application of the head
//!   that no parsed stack can see, and asserting it after adoption would
//!   strand a disconnected symbol — the native adopter guards that by
//!   scanning and pinning the arena, which this pass cannot; accordingly
//!   every hard assertion must retain its parsed AST — in `assertions_parsed`
//!   when the session retains the proof surface, else in the pass's own
//!   budgeted copy ([`Context::set_definitional_pass_parsed_budget`], the
//!   CLI's no-proof posture) — with the parallel stacks fully aligned, and
//!   none may be the native API's opaque placeholder;
//! * the retained ASTs stay under [`CHECK_SAT_ADOPTION_MAX_RETAINED_NODES`],
//!   which bounds the re-elaboration to one linear walk of a bounded input;
//! * a soft assertion or objective mentioning the head refuses that head
//!   (they retain no AST to re-elaborate — see
//!   [`Context::unretained_constraints_mention_symbol`]);
//! * any re-elaboration failure rolls back every macro this pass adopted and
//!   restores the named-term map, leaving the assertion stack untouched.
//!
//! Unsat cores: after expansion a harvested core over the expanded assertions
//! is a core of the authored problem only together with the definition, so
//! the adopted definition's `:named` label is recorded
//! ([`Context::adopted_definition_labels`]) for the core reporter to append.
//!
//! # The fallback chain the executor owes the other stacks
//!
//! Measured on a random definitional-forall family (800 scripts under
//! `:produce-proofs true`, so the pass ran) against the pre-pass solver,
//! thirteen scripts that were `unsat` before came back `unknown` after, and
//! the reasons make one stack never enough:
//!
//! * The certification funnel does not always accept a refutation of the
//!   EXPANDED problem where it accepts the instantiation refutation of the
//!   raw one (`step t0 uses unsupported hole rule`, `assumes term t1
//!   outside the supplied problem obligation`, a `Generic` theory lemma in
//!   strict mode) — a pre-existing gap of assert-time adoption under a
//!   proof-producing session that this pass would otherwise widen to every
//!   post-use and `:named` definition.
//! * A head with MORE THAN ONE candidate definition on the stack
//!   (`forall x y. g(x,y) = f(f(x))` beside `forall x y. g(x,y) = a`) is
//!   a consistency question as much as a definition: adopting the first
//!   turns the second into a raw quantified fact over the expansion and can
//!   make a third definition recursive (`f(x) = 2·g(x,d)` becomes
//!   `f(x) = 2·f(f(x))`), which the quantifier engines then fail to refute
//!   where the raw stack was refuted by instantiation in milliseconds. The
//!   assert-time finder adopts the first because it cannot see the second.
//! * The opposite also happens: two CONSISTENT definitions of one head
//!   (`f(x) = c` beside `f(x) = -5`) expand to a decidable residual
//!   `c = -5`, while the raw pair is a quantifier problem the engines do
//!   not decide.
//!
//! So the pass adopts as much as it can — every candidate whose head is not
//! yet defined, the first definition of a head winning — and leaves the
//! executor a FALLBACK CHAIN of [`DefinitionalAdoptionSnapshot`]s
//! ([`Context::take_definitional_adoption_retry`]): first the RAW stack
//! (every adopted macro, the assert-time finder's included, rolled back and
//! the retained assertions re-elaborated), then the stack exactly as the
//! assert-time finder left it (what the solver decided before this pass
//! existed). The executor takes the chain before solving and, on an
//! `unknown` with budget still in hand, restores the next stack and solves
//! again, giving every attempt but the last half of the remaining budget so
//! a fallback is never starved. A verdict decided on any of the stacks is
//! final (they are all equisatisfiable with the authored problem — every
//! step is a definitional extension or its removal); only an `unknown` —
//! never a wrong answer — is traded for a further solve, and both the raw
//! and the assert-time stacks are always in the chain, so no verdict the
//! solver reached before this pass is lost to it.

use std::panic::{catch_unwind, resume_unwind, AssertUnwindSafe};

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::Sort;

use super::{AuthoredAssertion, Context, ElaborateError, Result, NATIVE_API_ASSERTION_PLACEHOLDER};
use crate::command::Term as ParsedTerm;
use crate::sexp::SExpr;

/// When a definitional forall is being considered for macro adoption, which
/// decides the pre-use rule (see [`Context::try_adopt_definitional_forall`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum DefinitionalAdoptionTiming {
    /// At `assert`: an earlier constraint mentioning the head refuses.
    AtAssert,
    /// At the first `check-sat`: every retained hard assertion is
    /// re-elaborated after adoption, so only soft assertions and objectives
    /// mentioning the head refuse.
    AtCheckSat,
}

/// Upper bound on the retained parsed-AST nodes the check-sat-time pass will
/// re-elaborate. Above it the pass declines (status quo) rather than spend an
/// unbounded second elaboration of a huge problem on one candidate macro.
pub const CHECK_SAT_ADOPTION_MAX_RETAINED_NODES: usize = 200_000;

/// Strip the annotation wrappers a definitional assertion may carry, returning
/// the inner term and its `:named` labels.
///
/// Accepts only `:named` and the label-only `:lblpos`/`:lblneg` (SMT-LIB 2.6
/// §3.6.5: annotations carry no meaning). Any other attribute — `:pattern`,
/// `:no-pattern`, `:weight`, `:qid` — is a quantifier hint that asks for
/// E-matching semantics and refuses the whole candidate (`None`).
pub(super) fn peel_definitional_annotations(
    term: &ParsedTerm,
) -> Option<(&ParsedTerm, Vec<String>)> {
    let mut term = term;
    let mut labels = Vec::new();
    while let ParsedTerm::Annotated(inner, attributes) = term {
        for (keyword, value) in attributes {
            match keyword.as_str() {
                ":named" => {
                    if let SExpr::Symbol(label) = value {
                        labels.push(label.clone());
                    }
                }
                ":lblpos" | ":lblneg" => {}
                _ => return None,
            }
        }
        term = inner;
    }
    Some((term, labels))
}

/// Does the retained parsed stack fit under `budget` nodes? One linear walk
/// with early exit, so the check itself never costs more than the budget.
fn retained_ast_within_budget(assertions: &[ParsedTerm], budget: usize) -> bool {
    parsed_terms_node_count_within(assertions.iter(), budget).is_some()
}

/// The node count of `terms` if it is at most `budget`, else `None`. One
/// linear walk with early exit, so the count never costs more than the
/// budget it is checked against.
pub(super) fn parsed_terms_node_count_within<'a>(
    terms: impl Iterator<Item = &'a ParsedTerm>,
    budget: usize,
) -> Option<usize> {
    let mut remaining = budget;
    let mut stack: Vec<&ParsedTerm> = terms.collect();
    while let Some(term) = stack.pop() {
        if remaining == 0 {
            return None;
        }
        remaining -= 1;
        match term {
            ParsedTerm::Const(_) | ParsedTerm::Symbol(_) => {}
            ParsedTerm::App(_, args)
            | ParsedTerm::IndexedApp(_, _, args)
            | ParsedTerm::QualifiedApp(_, _, args) => stack.extend(args.iter()),
            ParsedTerm::Let(bindings, body) => {
                stack.extend(bindings.iter().map(|(_, value)| value));
                stack.push(body);
            }
            ParsedTerm::Forall(_, body)
            | ParsedTerm::Exists(_, body)
            | ParsedTerm::Lambda(_, body)
            | ParsedTerm::Annotated(body, _) => stack.push(body),
            ParsedTerm::Match(scrutinee, cases) => {
                stack.push(scrutinee);
                stack.extend(cases.iter().map(|(_, body)| body));
            }
        }
    }
    Some(budget - remaining)
}

/// The stack the check-sat-time pass replaced, so the executor can restore
/// it for a second solve when the expanded problem decides `unknown` (see
/// the module docs). Everything here is what
/// [`Context::reelaborate_retained_assertions`] and the adoption itself
/// move: the elaborated stack with its public-sort metadata, the authored
/// assertion records, the named-term map, and the macros the pass
/// registered (names only — rollback is by name).
#[derive(Clone, Debug)]
pub struct DefinitionalAdoptionSnapshot {
    pub(super) assertions: Vec<ay_core::TermId>,
    pub(super) assertion_finite_set_metadata: Vec<super::PublicAssertionMetadata>,
    pub(super) authored_assertions: Vec<AuthoredAssertion>,
    pub(super) named_terms: HashMap<String, ay_core::TermId>,
    /// Every head whose macro state the pass may have changed since this
    /// snapshot: restoring rolls each of them back, then reinstates those
    /// recorded in `macros` exactly as they were.
    pub(super) touched: Vec<String>,
    pub(super) macros: Vec<AdoptedMacroRecord>,
}

/// One adopted definitional macro as registered in the context, so a
/// snapshot can reinstate it byte-for-byte.
#[derive(Clone, Debug)]
pub(super) struct AdoptedMacroRecord {
    pub(super) head: String,
    pub(super) definition: super::FunctionDefinition,
    pub(super) interp: (Vec<(String, Sort)>, ay_core::TermId),
    pub(super) declaration_id: super::DeclarationId,
    pub(super) labels: Vec<String>,
}

/// One candidate definitional forall on the retained stack and the head it
/// would define.
struct Candidate {
    head: String,
    parsed: ParsedTerm,
}

fn is_native_api_placeholder(term: &ParsedTerm) -> bool {
    matches!(term, ParsedTerm::Symbol(name) if name == NATIVE_API_ASSERTION_PLACEHOLDER)
}

impl Context {
    /// #defmacro-named-preuse: adopt every retained definitional forall the
    /// assert-time finder refused only for pre-use, then re-elaborate the
    /// retained hard assertions so the earlier occurrences expand too. See
    /// the module docs for the fail-closed conditions; every refusal leaves
    /// the context byte-identical.
    pub(super) fn adopt_definitional_foralls_at_check_sat(&mut self) {
        let Some((candidates, parsed_stack)) = self.check_sat_adoption_candidates() else {
            return;
        };
        // Every macro the assert-time finder adopted: rolled back for the
        // raw stack, re-adopted (first definition of each head winning)
        // for the live one, reinstated by the assert-time fallback.
        let mut assert_time_adopted: Vec<String> =
            self.adopted_macro_interps.keys().cloned().collect();
        assert_time_adopted.sort();
        let mut assert_time_stack = self.definitional_adoption_snapshot(&assert_time_adopted);

        // The raw stack: nothing adopted, the retained assertions
        // re-elaborated without any macro.
        if !assert_time_adopted.is_empty() {
            for head in &assert_time_adopted {
                self.rollback_adopted_macro(head);
            }
            if !self.reelaborate_retained_assertions_or_restore(
                &parsed_stack,
                assert_time_stack.clone(),
            ) {
                return;
            }
        }
        let mut raw_stack = self.definitional_adoption_snapshot(&assert_time_adopted);

        // The live stack: adopt every candidate whose head is not yet
        // defined, sequentially, so a later candidate is validated with the
        // earlier macros registered (a cycle `f := g(x)`, `g := f(x)` is
        // refused by the elaborated-body guards exactly as at assert time,
        // and a second definition of a head becomes a residual constraint
        // over the first).
        let mut adopted: Vec<String> = Vec::new();
        for candidate in &candidates {
            if self.fun_defs.contains_key(&candidate.head) {
                continue;
            }
            if let Some(name) = self.try_adopt_definitional_forall(
                &candidate.parsed,
                DefinitionalAdoptionTiming::AtCheckSat,
            ) {
                adopted.push(name);
            }
        }
        if adopted.is_empty() && assert_time_adopted.is_empty() {
            return;
        }
        for snapshot in [&mut assert_time_stack, &mut raw_stack] {
            for head in &adopted {
                if !snapshot.touched.contains(head) {
                    snapshot.touched.push(head.clone());
                }
            }
        }
        let mut chain: Vec<DefinitionalAdoptionSnapshot> = Vec::new();
        if adopted.is_empty()
            || self.reelaborate_retained_assertions_or_restore(&parsed_stack, raw_stack.clone())
        {
            // The live stack is the expanded one (or, with nothing new
            // adopted, the raw one): fall back to raw, then to assert-time.
            if !adopted.is_empty() {
                chain.push(raw_stack);
            }
        }
        // A failed re-elaboration left the raw stack live; the assert-time
        // stack is still worth its solve.
        if !assert_time_adopted.is_empty() {
            chain.push(assert_time_stack);
        }
        self.definitional_pass.retry = chain;
    }

    /// The pass's entry guards (module docs), its candidate list and the
    /// fully aligned parsed stack it will re-elaborate (`assertions_parsed`
    /// when that is complete, else the pass's own budgeted copy); `None`
    /// declines the pass, leaving the context byte-identical.
    fn check_sat_adoption_candidates(&mut self) -> Option<(Vec<Candidate>, Vec<ParsedTerm>)> {
        // First satisfiability-check COMMAND of the session only, whichever
        // of `check-sat` / `check-sat-assuming` reaches it first; every
        // refusal below still counts as the one entry.
        if std::mem::replace(&mut self.definitional_check_sat_pass_entered, true)
            || !self.scopes.is_empty()
            || self.elaborating_polymorphic_instance
        {
            return None;
        }
        // The pass sees the authored stack only: query-local schematic
        // instances of an earlier check (none, at the first check-sat, but
        // the invariant is cheap to keep explicit) are re-materialized by
        // the caller after the pass.
        self.clear_materialized_polymorphic_assertions();
        let parsed_stack = if self.retains_parsed_assertions()
            && self.assertions_parsed.len() == self.assertions.len()
        {
            &self.assertions_parsed
        } else if self.definitional_pass.budget.is_some()
            && self.definitional_pass.parsed.len() == self.assertions.len()
        {
            &self.definitional_pass.parsed
        } else {
            return None;
        };
        let candidates: Vec<Candidate> = parsed_stack
            .iter()
            .filter_map(|parsed| {
                let head = self.definitional_forall_candidate_head(parsed)?;
                Some(Candidate {
                    head,
                    parsed: parsed.clone(),
                })
            })
            .collect();
        if candidates.is_empty()
            || parsed_stack.iter().any(is_native_api_placeholder)
            || !retained_ast_within_budget(parsed_stack, CHECK_SAT_ADOPTION_MAX_RETAINED_NODES)
        {
            return None;
        }
        Some((candidates, parsed_stack.clone()))
    }

    /// Cheap structural pre-filter for the pass: a (possibly `:named`)
    /// `forall` whose body is a binary `=` with a user-declared application
    /// head on some side that is either not yet defined or was adopted by
    /// the assert-time finder (a plain `define-fun` head is never a
    /// candidate). The full guard chain runs in
    /// [`Self::try_adopt_definitional_forall`]; this only keeps the common
    /// check-sat from paying for a walk it cannot use.
    fn definitional_forall_candidate_head(&self, parsed: &ParsedTerm) -> Option<String> {
        let (inner, _) = peel_definitional_annotations(parsed)?;
        let ParsedTerm::Forall(binders, body) = inner else {
            return None;
        };
        if binders.is_empty() {
            return None;
        }
        let ParsedTerm::App(eq, sides) = body.as_ref() else {
            return None;
        };
        if eq != "=" || sides.len() != 2 {
            return None;
        }
        // A defining side is the head applied to exactly the binders, in
        // order — the adopter's own shape test (`side_f`). Anything else on
        // that side (`f(f(x))`, `2 * g(x, d)`) is body, not head.
        let binder_exact = |side: &ParsedTerm| -> Option<String> {
            let ParsedTerm::App(head, args) = side else {
                return None;
            };
            if !self.symbols.contains_key(head)
                || (self.fun_defs.contains_key(head)
                    && !self.adopted_macro_interps.contains_key(head))
                || args.len() != binders.len()
            {
                return None;
            }
            args.iter()
                .zip(binders.iter())
                .all(|(arg, (binder, _))| matches!(arg, ParsedTerm::Symbol(s) if s == binder))
                .then(|| head.clone())
        };
        match (binder_exact(&sides[0]), binder_exact(&sides[1])) {
            (Some(head), None) | (None, Some(head)) => Some(head),
            // `f(a,b) = g(a,b)` names two heads: genuinely ambiguous, refused
            // by the adopter, and not a definition of either for counting.
            _ => None,
        }
    }

    /// The pass's transaction boundary: re-elaborate the retained stack, or
    /// put everything back the way `snapshot` recorded it. A panic inside
    /// elaboration also restores before propagating.
    fn reelaborate_retained_assertions_or_restore(
        &mut self,
        parsed_stack: &[ParsedTerm],
        snapshot: DefinitionalAdoptionSnapshot,
    ) -> bool {
        let outcome = catch_unwind(AssertUnwindSafe(|| {
            self.reelaborate_retained_assertions(parsed_stack)
        }));
        match outcome {
            Ok(Ok(())) => true,
            Ok(Err(_)) => {
                self.restore_definitional_adoption_snapshot(snapshot);
                false
            }
            Err(payload) => {
                self.restore_definitional_adoption_snapshot(snapshot);
                resume_unwind(payload);
            }
        }
    }

    /// The current stack, with the macro state of `touched` heads recorded
    /// so [`Self::restore_definitional_adoption_snapshot`] can reinstate it.
    fn definitional_adoption_snapshot(&self, touched: &[String]) -> DefinitionalAdoptionSnapshot {
        let macros = touched
            .iter()
            .filter_map(|head| {
                let definition = self.fun_defs.get(head)?.clone();
                let interp = self.adopted_macro_interps.get(head)?.clone();
                let declaration_id = self.adopted_macro_declaration_ids.get(head)?.clone();
                let labels = self
                    .adopted_definition_labels
                    .iter()
                    .filter(|(adopted, _)| adopted == head)
                    .map(|(_, label)| label.clone())
                    .collect();
                Some(AdoptedMacroRecord {
                    head: head.clone(),
                    definition,
                    interp,
                    declaration_id,
                    labels,
                })
            })
            .collect();
        DefinitionalAdoptionSnapshot {
            assertions: self.assertions.clone(),
            assertion_finite_set_metadata: self.assertion_finite_set_metadata.clone(),
            authored_assertions: self.authored_assertions.clone(),
            named_terms: self.named_terms.clone(),
            touched: touched.to_vec(),
            macros,
        }
    }

    /// Put the stack back to what `snapshot` recorded: every touched head's
    /// macro is rolled back (its labels with it), the macros the snapshot
    /// recorded are reinstated, and the elaborated stack, its metadata, the
    /// authored records and the named-term map are reinstated. The parsed
    /// stack was never touched. Any fallback chain still pending is dropped:
    /// the caller owns the chain it took.
    pub fn restore_definitional_adoption_snapshot(
        &mut self,
        snapshot: DefinitionalAdoptionSnapshot,
    ) {
        self.advance_source_revision();
        let DefinitionalAdoptionSnapshot {
            assertions,
            assertion_finite_set_metadata,
            authored_assertions,
            named_terms,
            touched,
            macros,
        } = snapshot;
        for head in &touched {
            self.rollback_adopted_macro(head);
        }
        for record in macros {
            self.fun_defs.insert(record.head.clone(), record.definition);
            self.adopted_macro_interps
                .insert(record.head.clone(), record.interp);
            self.adopted_macro_declaration_ids
                .insert(record.head.clone(), record.declaration_id);
            for label in record.labels {
                self.note_adopted_definition_label(&record.head, label);
            }
        }
        self.assertions = assertions;
        self.assertion_finite_set_metadata = assertion_finite_set_metadata;
        self.authored_assertions = authored_assertions;
        self.named_terms = named_terms;
        self.definitional_pass.retry.clear();
    }

    /// Run `f` with the check-sat-time pass held off.
    ///
    /// The executor's proof reconstruction elaborates a retained parsed
    /// assertion by feeding it to a `check-sat-assuming` COMMAND on the live
    /// context (`collect_hidden_problem_equality_assertions`): an elaboration
    /// vehicle, not a satisfiability check, and it runs in the MIDDLE of a
    /// public decision — after the solver decided, before the certification
    /// funnel confirmed. The pass must not fire there. On a native-API
    /// session, whose `check_sat` never takes the command route (so the
    /// pass has never been entered), it would roll the assert-time macros
    /// back, re-elaborate every retained assertion and advance the source
    /// revision under a pending UNSAT, and the funnel then rightly withdraws
    /// the verdict as decided over a source context that is no longer
    /// current (measured: an adopted closed bit-vector definition plus
    /// `(assert false)` answered `unknown` instead of `unsat`). The pass's
    /// once-per-session entry is put back exactly as it was, so the next
    /// REAL check still runs it; a panic inside `f` leaves the pass marked
    /// entered, i.e. fails closed to the status quo of no adoption.
    #[doc(hidden)]
    pub fn with_definitional_check_sat_pass_held<T>(
        &mut self,
        f: impl FnOnce(&mut Self) -> T,
    ) -> T {
        let entered = std::mem::replace(&mut self.definitional_check_sat_pass_entered, true);
        let result = f(self);
        self.definitional_check_sat_pass_entered = entered;
        result
    }

    /// The fallback chain the check-sat-time pass left at THIS check, in the
    /// order the executor should try the stacks (module docs) — taken by the
    /// executor before it solves, so a derived context never carries it and
    /// a later check never finds a stale one. Empty when the pass changed
    /// nothing.
    #[doc(hidden)]
    pub fn take_definitional_adoption_retry(&mut self) -> Vec<DefinitionalAdoptionSnapshot> {
        std::mem::take(&mut self.definitional_pass.retry)
    }

    /// Hand the rest of a fallback chain back for the executor's re-entered
    /// check to take (see [`Self::take_definitional_adoption_retry`]).
    #[doc(hidden)]
    pub fn set_definitional_adoption_retry(&mut self, chain: Vec<DefinitionalAdoptionSnapshot>) {
        self.definitional_pass.retry = chain;
    }

    /// A `check-sat` the executor re-runs on the restored raw stack is the
    /// SAME query, not a second one: keep the single-shot accounting
    /// ([`Self::is_single_shot_query`]) honest.
    #[doc(hidden)]
    pub fn uncount_check_sat_for_retry(&mut self) {
        self.check_sat_commands = self.check_sat_commands.saturating_sub(1);
    }

    /// Re-elaborate every retained parsed assertion (`parsed_stack`, aligned
    /// with `assertions`) with the currently registered macros and swap the
    /// results in atomically: the elaborated stack, its public-sort
    /// metadata, and the authored-assertion terms move together, or nothing
    /// moves. The authored records are re-pointed by TERM (old elaboration
    /// to new), which does not depend on their `parsed_index` — absent when
    /// the session retains no proof surface.
    fn reelaborate_retained_assertions(&mut self, parsed_stack: &[ParsedTerm]) -> Result<()> {
        #[cfg(test)]
        if std::mem::take(&mut self.fail_next_check_sat_reelaboration) {
            return Err(ElaborateError::Unsupported(
                "test-injected failure during check-sat re-elaboration".to_string(),
            ));
        }
        if parsed_stack.len() != self.assertions.len() {
            return Err(ElaborateError::Unsupported(
                "check-sat re-elaboration needs a fully aligned parsed stack".to_string(),
            ));
        }
        let parsed_all = parsed_stack;
        let mut fresh_terms = Vec::with_capacity(parsed_all.len());
        let mut fresh_metadata = Vec::with_capacity(parsed_all.len());
        for parsed in parsed_all {
            let id = self.elaborate_term(parsed, &HashMap::default())?;
            let sort = self.terms.sort(id).clone();
            if sort != Sort::Bool {
                return Err(ElaborateError::SortMismatch {
                    expected: "Bool".to_string(),
                    actual: format!("{sort:?}"),
                });
            }
            fresh_metadata.push(self.validate_public_assertion(parsed, id)?);
            fresh_terms.push(id);
        }
        let renamed: HashMap<ay_core::TermId, ay_core::TermId> = self
            .assertions
            .iter()
            .copied()
            .zip(fresh_terms.iter().copied())
            .collect();
        for authored in &mut self.authored_assertions {
            if let AuthoredAssertion::Concrete { term, .. } = authored {
                if let Some(&fresh) = renamed.get(term) {
                    *term = fresh;
                }
            }
        }
        self.assertions = fresh_terms;
        self.assertion_finite_set_metadata = fresh_metadata;
        Ok(())
    }

    #[cfg(test)]
    pub(crate) fn fail_next_check_sat_reelaboration(&mut self) {
        self.fail_next_check_sat_reelaboration = true;
    }
}

// A restoration of identical declaration bytes is still a new source epoch.
#[cfg(test)]
mod projection_lease_tests {
    use super::*;

    #[test]
    fn projection_binding_lease_snapshot_restore_does_not_restore_revision() {
        let mut context = Context::new();
        for command in crate::parse("(declare-fun f (Int) Int)").unwrap() {
            context.process_command(&command).unwrap();
        }
        let checked = context
            .check_projection_declaration(&super::super::ProjectionBindingRequest {
                symbol: ay_core::Symbol::named("f"),
                parameter_sorts: vec![ay_core::Sort::Int],
                result_sort: ay_core::Sort::Int,
            })
            .unwrap();
        let snapshot = context.definitional_adoption_snapshot(&[]);
        context.restore_definitional_adoption_snapshot(snapshot);
        assert!(!context.projection_binding_lease_still_current(&checked));
        assert!(!context.projection_binding_still_current(&checked));
        assert!(context
            .check_projection_declaration(&super::super::ProjectionBindingRequest {
                symbol: ay_core::Symbol::named("f"),
                parameter_sorts: vec![ay_core::Sort::Int],
                result_sort: ay_core::Sort::Int,
            })
            .is_ok());
    }
}
