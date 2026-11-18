// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Authored subterms that elaboration passes over.
//!
//! z3 parses a whole command before it simplifies anything: it resolves the
//! names, checks the sorts and binds the `:named` labels of every subterm,
//! including the branch of an `ite` whose condition is constant, a `let` value
//! the body never uses and a `match` case that cannot be taken. The elaborator
//! does not elaborate those subterms into the term store: an untaken branch
//! may hold a recursive call that never stops expanding, and a dead term in
//! the store can drive the lazy array combiner to a spurious `unsat`.
//!
//! So each such subterm of an authored command is checked where z3 reads it,
//! in z3's order. A read-only sort check (`sort_check`) vouches for a small
//! fragment (core Boolean, arithmetic and bit-vector operators, `select` and
//! `store`, declared functions and definitions applied to arguments of
//! exactly their sorts, `let`, and quantifiers over Bool, Int and Real) with
//! no label in it. Anything else is elaborated in a scratch copy of the
//! context, so nothing it creates reaches the real term store. An error there
//! rejects the command at that point, as z3 rejects it. The labels the
//! subterm binds are carried back from the scratch copy, so the labels of an
//! assertion z3 rejects at a later label are the ones z3 keeps (see
//! `assert_authored_with_labels`).
//!
//! Only the authored command's own subterms are checked. A macro body was
//! checked when it was defined, and its untaken branches are what the
//! elaborator must not expand.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::TermStoreSnapshotStamp;
use ay_core::{Sort, TermId};

use crate::command::{MatchPattern, Term as ParsedTerm};

use super::{term_has_named_label, Context, ElaborateError, Result};

mod names;
mod sort_check;

use names::{binders_named_in, mentioned_names};

/// Skipped-subterm state for one authored command.
#[derive(Clone, Default)]
pub(super) struct SkipJournal {
    /// Addresses of the command's subterms that elaboration may pass over:
    /// `ite` branches, `let` values and `match` case bodies.
    skippable: HashSet<usize>,
    /// Set in a scratch copy, where a skipped subterm is elaborated in place.
    in_scratch: bool,
}

/// A scratch copy of the context that label-free skipped subterms share, so
/// the context is copied once rather than once per subterm. It is made when
/// one is first needed and dropped with the macro expansion memo, which
/// everything that changes how a term resolves or types drops (a
/// declaration, a definition, `push`, `pop`, `set-logic`, `set-option`,
/// `reset`), and before a query is solved. The terms below `shared_len` are
/// the same in both stores while `stamp` still describes an append-only
/// prefix of the context's store. A term the context made after the copy is
/// stood in for in the copy by a fresh variable of its sort: a label-free
/// subterm's errors and sort depend only on the sorts of the names it uses.
pub(super) struct SharedScratch {
    context: Context,
    stamp: TermStoreSnapshotStamp,
    shared_len: usize,
}

/// The context's [`SharedScratch`], if any. A copy of the context starts
/// without one.
#[derive(Default)]
pub(super) struct SharedScratchSlot(Option<Box<SharedScratch>>);

impl Clone for SharedScratchSlot {
    fn clone(&self) -> Self {
        Self(None)
    }
}

impl SharedScratchSlot {
    pub(super) fn clear(&mut self) {
        self.0 = None;
    }
}

fn node_address(term: &ParsedTerm) -> usize {
    std::ptr::from_ref(term) as usize
}

/// The spellings of `ite` whose constant condition the elaborator folds
/// before it elaborates the branches.
fn is_ite_spelling(name: &str) -> bool {
    matches!(name, "ite" | "if" | "if_then_else")
}

/// Every subterm of `root` that elaboration may pass over.
fn skippable_subterms(root: &ParsedTerm) -> HashSet<usize> {
    let mut skippable = HashSet::default();
    let mut stack = vec![root];
    while let Some(term) = stack.pop() {
        match term {
            ParsedTerm::Const(_) | ParsedTerm::Symbol(_) => {}
            ParsedTerm::App(name, args) => {
                if is_ite_spelling(name) && args.len() == 3 {
                    skippable.insert(node_address(&args[1]));
                    skippable.insert(node_address(&args[2]));
                }
                stack.extend(args.iter());
            }
            ParsedTerm::IndexedApp(_, _, args) | ParsedTerm::QualifiedApp(_, _, args) => {
                stack.extend(args.iter());
            }
            ParsedTerm::Let(bindings, body) => {
                for (_, value) in bindings {
                    skippable.insert(node_address(value));
                    stack.push(value);
                }
                stack.push(body);
            }
            ParsedTerm::Forall(_, body)
            | ParsedTerm::Exists(_, body)
            | ParsedTerm::Lambda(_, body) => stack.push(body),
            ParsedTerm::Annotated(inner, _) => stack.push(inner),
            ParsedTerm::Match(scrutinee, cases) => {
                stack.push(scrutinee);
                for (_, body) in cases {
                    skippable.insert(node_address(body));
                    stack.push(body);
                }
            }
        }
    }
    skippable
}

impl Context {
    /// Drop the shared scratch copy before a query is solved: it is a full
    /// copy of the context, and holding it while the solver runs would double
    /// the frontend's share of memory. The next skipped subterm makes it again.
    pub(super) fn drop_shared_scratch(&mut self) {
        self.shared_scratch.clear();
    }

    /// The number of terms in the shared scratch copy, if there is one.
    #[cfg(test)]
    pub(super) fn shared_scratch_term_count(&self) -> Option<usize> {
        self.shared_scratch
            .0
            .as_ref()
            .map(|shared| shared.context.terms.len())
    }

    /// Run `f` while the subterms of `root` that elaboration may pass over
    /// are checked where they are passed over.
    pub(super) fn with_skip_journal<T>(
        &mut self,
        root: &ParsedTerm,
        f: impl FnOnce(&mut Self) -> T,
    ) -> T {
        let skippable = skippable_subterms(root);
        if skippable.is_empty() && self.skip_journal.is_none() {
            return f(self);
        }
        let in_scratch = self
            .skip_journal
            .as_ref()
            .is_some_and(|journal| journal.in_scratch);
        let outer = self.skip_journal.replace(SkipJournal {
            skippable,
            in_scratch,
        });
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| f(self)));
        self.skip_journal = outer;
        match result {
            Ok(value) => value,
            Err(payload) => std::panic::resume_unwind(payload),
        }
    }

    /// Check `skipped`, a subterm elaboration passes over, as z3 reads it in
    /// `env` with `binders` (names bound around it that `env` does not hold,
    /// by sort) shadowing `env`, and return its sort. An error is the
    /// command's error at this point, as it is z3's. `None` means the subterm
    /// is not the authored command's own and is not checked here.
    pub(super) fn check_skipped_subterm(
        &mut self,
        skipped: &ParsedTerm,
        env: &HashMap<String, TermId>,
        binders: &HashMap<String, Sort>,
    ) -> Result<Option<Sort>> {
        if let Some(sort) = self.shared_surface_skipped_sort(skipped)? {
            return Ok(Some(sort));
        }
        let Some(journal) = self.skip_journal.as_ref() else {
            return Ok(None);
        };
        if !journal.skippable.contains(&node_address(skipped)) {
            return Ok(None);
        }
        let in_scratch = journal.in_scratch;
        let binders = binders_named_in(skipped, binders);
        if in_scratch {
            // Already in a scratch copy, whose term store is thrown away.
            let env = self.env_with_binders(env, &binders);
            let id = self.elaborate_term(skipped, &env)?;
            return Ok(Some(self.terms.sort(id).clone()));
        }
        let mut scope = binders.clone();
        if let Some(sort) = self.skipped_term_sort(skipped, env, &mut scope) {
            return Ok(Some(sort));
        }
        if term_has_named_label(skipped) {
            self.elaborate_skipped_in_scratch(skipped, env, &binders)
        } else {
            self.elaborate_skipped_in_shared_scratch(skipped, env, &binders)
        }
        .map(Some)
    }

    /// Elaborate a label-free `skipped` in the shared scratch copy and return
    /// its sort.
    fn elaborate_skipped_in_shared_scratch(
        &mut self,
        skipped: &ParsedTerm,
        env: &HashMap<String, TermId>,
        binders: &[(String, Sort)],
    ) -> Result<Sort> {
        let reusable = self
            .shared_scratch
            .0
            .take()
            .filter(|shared| shared.stamp.is_append_only_prefix_of(&self.terms));
        let mut shared = match reusable {
            Some(shared) => shared,
            None => {
                // The journal is lent to the copy below, not copied.
                let journal = self.skip_journal.take();
                let context = self.clone();
                self.skip_journal = journal;
                Box::new(SharedScratch {
                    context,
                    stamp: self.terms.snapshot_stamp(),
                    shared_len: self.terms.len(),
                })
            }
        };
        let skippable = self
            .skip_journal
            .as_mut()
            .map(|journal| std::mem::take(&mut journal.skippable))
            .unwrap_or_default();
        let shared_len = shared.shared_len;
        let scratch = &mut shared.context;
        scratch.skip_journal = Some(SkipJournal {
            skippable,
            in_scratch: true,
        });
        // Labels bound earlier in the command may be used in the subterm.
        scratch.label_journal = self.label_journal.clone();
        let terms = &self.terms;
        let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let mut scratch_env = HashMap::default();
            for name in mentioned_names(skipped) {
                if let Some(&id) = env.get(&name) {
                    let id = if id.index() < shared_len {
                        id
                    } else {
                        scratch.terms.mk_fresh_var(&name, terms.sort(id).clone())
                    };
                    scratch_env.insert(name, id);
                }
            }
            let scratch_env = scratch.env_with_binders(&scratch_env, binders);
            let id = scratch.elaborate_term(skipped, &scratch_env)?;
            Ok(scratch.terms.sort(id).clone())
        }));
        let lent = shared.context.skip_journal.take();
        // A construct some z3 rejects, accepted in the subterm, decides
        // whether z3 reaches the labels after it.
        if shared.context.saw_construct_z3_may_reject() {
            self.note_construct_z3_may_reject();
        }
        shared.context.label_journal = None;
        if let (Some(journal), Some(lent)) = (self.skip_journal.as_mut(), lent) {
            journal.skippable = lent.skippable;
        }
        match outcome {
            Ok(result) => {
                self.shared_scratch.0 = Some(shared);
                result
            }
            Err(_) => Err(ElaborateError::Unsupported(
                "a subterm z3 reads could not be checked".to_string(),
            )),
        }
    }

    /// Elaborate `skipped`, which holds a label, in a fresh scratch copy of
    /// this context, carry its labels back and return its sort.
    fn elaborate_skipped_in_scratch(
        &mut self,
        skipped: &ParsedTerm,
        env: &HashMap<String, TermId>,
        binders: &[(String, Sort)],
    ) -> Result<Sort> {
        let mut scratch = self.clone();
        if let Some(journal) = scratch.skip_journal.as_mut() {
            journal.in_scratch = true;
        }
        let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let env = scratch.env_with_binders(env, binders);
            let id = scratch.elaborate_term(skipped, &env)?;
            Ok(scratch.terms.sort(id).clone())
        }));
        match outcome {
            Ok(result) => {
                // Labels are held as authored spellings and sorts, not term
                // ids, so the scratch copy's journal is valid here.
                self.label_journal = scratch.label_journal.take();
                self.note_skipped_label_subterm();
                result
            }
            Err(_) => {
                self.note_unchecked_label_subterm();
                Err(ElaborateError::Unsupported(
                    "a subterm z3 reads could not be checked".to_string(),
                ))
            }
        }
    }

    /// The value of an `ite` whose condition is constant: the branch the
    /// elaborator took, at the sort z3 gives the `ite` from both branches. An
    /// Int and a Real branch join at Real, as in the elaborator's `ite`. A
    /// Bool branch beside a numeric one is left unsupported, since z3 4.12.5
    /// rejects that pair and z3 4.16 joins it; any other differing pair is
    /// z3's sort error.
    pub(super) fn join_skipped_branch(
        &mut self,
        taken: TermId,
        skipped: Option<Sort>,
    ) -> Result<TermId> {
        let taken_sort = self.terms.sort(taken).clone();
        let Some(skipped) = skipped.filter(|sort| *sort != taken_sort) else {
            return Ok(taken);
        };
        match (&taken_sort, &skipped) {
            (Sort::Int | Sort::Real, Sort::Complex) if self.int_real_coercions() => {
                let zero = self.terms.mk_int(0.into());
                self.terms.mk_complex(taken, zero).ok_or_else(|| {
                    ElaborateError::Unsupported("Complex promotion unavailable".to_string())
                })
            }
            (Sort::Complex, Sort::Int | Sort::Real) if self.int_real_coercions() => Ok(taken),
            (Sort::Int, Sort::Real) if self.int_real_coercions() => {
                Ok(self.coerce_int_to_real(taken))
            }
            (Sort::Real, Sort::Int) if self.int_real_coercions() => Ok(taken),
            (taken_sort, skipped)
                if super::term::arith_coercible(taken_sort)
                    && super::term::arith_coercible(skipped) =>
            {
                Err(ElaborateError::Unsupported(format!(
                    "an ite with a constant condition has branches of sorts {taken_sort} and {skipped}"
                )))
            }
            (taken_sort, skipped) => Err(ElaborateError::SortMismatch {
                expected: taken_sort.to_string(),
                actual: skipped.to_string(),
            }),
        }
    }

    fn env_with_binders(
        &mut self,
        env: &HashMap<String, TermId>,
        binders: &[(String, Sort)],
    ) -> HashMap<String, TermId> {
        let mut env = env.clone();
        for (name, sort) in binders {
            let var = self.mint_fresh_var(name, sort.clone());
            env.insert(name.clone(), var);
        }
        env
    }

    /// The variables a `match` case pattern binds, checked as the elaborator
    /// checks the pattern of a case it takes. Used for the cases after a
    /// catch-all, which z3 still reads.
    pub(super) fn match_case_binders(
        &self,
        ctor_internals: &[String],
        dt_name: &str,
        scrutinee_sort: &Sort,
        pattern: &MatchPattern,
    ) -> Result<Vec<(String, Sort)>> {
        let selectors = |ctor_internal: &String| {
            self.ctor_selector_info
                .get(ctor_internal)
                .cloned()
                .unwrap_or_default()
        };
        match pattern {
            MatchPattern::Symbol(symbol) if symbol == "_" => Ok(Vec::new()),
            MatchPattern::Symbol(symbol) => {
                match self.datatype_ctor_internal(ctor_internals, symbol) {
                    Some(ctor_internal) => {
                        let fields = selectors(&ctor_internal).len();
                        if fields == 0 {
                            Ok(Vec::new())
                        } else {
                            Err(ElaborateError::Unsupported(format!(
                                "constructor '{symbol}' in match pattern needs {fields} field binder(s)"
                            )))
                        }
                    }
                    None => Ok(vec![(symbol.clone(), scrutinee_sort.clone())]),
                }
            }
            MatchPattern::Constructor(ctor, vars) => {
                let ctor_internal = self
                    .datatype_ctor_internal(ctor_internals, ctor)
                    .ok_or_else(|| {
                        ElaborateError::Unsupported(format!(
                            "'{ctor}' is not a constructor of datatype '{dt_name}' in a match pattern"
                        ))
                    })?;
                let fields = selectors(&ctor_internal);
                if fields.len() != vars.len() {
                    return Err(ElaborateError::Unsupported(format!(
                        "constructor '{ctor}' in match pattern expects {} field(s), got {}",
                        fields.len(),
                        vars.len()
                    )));
                }
                Ok(vars
                    .iter()
                    .zip(fields)
                    .filter(|(var, _)| var.as_str() != "_")
                    .map(|(var, (_, sort))| (var.clone(), sort))
                    .collect())
            }
        }
    }
}
