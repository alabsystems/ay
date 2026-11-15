// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! One render per bit-vector lemma for the support question, instead of one
//! per ask.
//!
//! [`super::checked_bv_bitblast_lowering_supported`] answers "can the printer
//! spell this lemma?" by rendering the lemma and discarding the text, and one
//! publication asks it about the same lemma several times over: the
//! publication screen runs once per guard, retry and re-ask
//! (`resolution_dag_memo.rs` lists them). The refutation memo spares every
//! render after the first its SAT work, but each still plans the blast,
//! transports the refutation into text, replays that text (`selfcheck`) and
//! counts the consumer's work over it. Measured 2026-10-01 on external-codegen's
//! 64-bit `SDIV` definitional row 0300 (load average ~100 on 18 cores): the
//! support question rendered its one lemma seven times and the export twice,
//! every render after the first 1.1 to 1.4 s for a 73 MB document — 8.6 s
//! of the query's 75 s.
//!
//! So a lemma the printer has ALREADY spelled is answered `true` here without
//! a render: the same query renders it three times (the first ask, the strict
//! document scan, the export).
//!
//! # Why a remembered `true` is the answer a render would give
//!
//! * The key is what the render reads of the lemma: its kind, its clause,
//!   the dialect it is spelled for, and the override spelling of every term
//!   below the clause. The terms themselves are immutable while the store
//!   only grows ([`TermStoreSnapshotStamp::is_append_only_prefix_of`]): an
//!   entry is served only while the store it was rendered from is still that
//!   store, unreplaced and never rolled back. The one thing a render reads
//!   beyond the lemma, the collision scan that picks a proof-local name
//!   prefix, chooses names, never structure.
//! * Only `true` is stored. A decline — a budget, a deadline, a satisfiable
//!   blast — is never made sticky: the next ask renders again, as before.
//! * A remembered `true` decides nothing about the document. The export
//!   renders the lemma itself (under its own step id), replays its own text
//!   before printing it, and leaves the honest `hole` if it cannot; the
//!   strict certification then refuses that document as it would have. The
//!   memo removes a timing-dependent flip between the asks of one
//!   publication, in the same direction as `resolution_dag_memo.rs`, and
//!   adds none.
//!
//! A decline is kept only by the one solve that asked (`within_solve.rs`).

use super::dialect::{self, AletheDialect};
use super::HashMap;
use ay_core::kani_compat::{DetHashMap, DetHashSet};
use ay_core::term::TermStoreSnapshotStamp;
use ay_core::{TermData, TermId, TermStore, TheoryLemmaKind};
use std::cell::RefCell;

/// Terms below one clause walked at most: a larger lemma is answered by
/// rendering it, every time.
const MAX_KEY_TERMS: usize = 65_536;
/// Override bytes one key may carry; a lemma spelled with more is rendered.
const MAX_KEY_BYTES: usize = 1024 * 1024;
/// Entries retained before the table is dropped wholesale.
const MAX_ENTRIES: usize = 4_096;
/// Key bytes retained before the table is dropped wholesale.
const MAX_RETAINED_BYTES: usize = 32 * 1024 * 1024;

mod within_solve;
pub use within_solve::{
    checked_bv_bitblast_lowering_supported_within_solve,
    theory_lemma_bv_arithmetic_lowering_supported_within_solve, BvSupportDeclines,
};

#[derive(Clone, PartialEq, Eq, Hash)]
struct Key {
    kind: TheoryLemmaKind,
    clause: Vec<TermId>,
    dialect: AletheDialect,
    /// The override of every term below the clause, in term order.
    spellings: Vec<(TermId, String)>,
}

impl Key {
    fn of(
        terms: &TermStore,
        kind: TheoryLemmaKind,
        clause: &[TermId],
        overrides: Option<&HashMap<TermId, String>>,
    ) -> Option<(Self, usize)> {
        let spelled = |term: TermId| overrides.and_then(|overrides| overrides.get(&term).cloned());
        let spelling: &dyn Fn(TermId) -> Option<String> = &spelled;
        let walked = overrides.is_some_and(|overrides| !overrides.is_empty());
        Self::spelled(terms, kind, clause, walked.then_some(spelling))
    }

    /// The key of the lemma whose terms below the clause `spelling` spells,
    /// where it has an override for them; `None` when no term has one.
    fn spelled(
        terms: &TermStore,
        kind: TheoryLemmaKind,
        clause: &[TermId],
        spelling: Option<&dyn Fn(TermId) -> Option<String>>,
    ) -> Option<(Self, usize)> {
        let mut spellings = Vec::new();
        let mut bytes = size_of_val(clause);
        if let Some(spelling) = spelling {
            let mut seen: DetHashSet<TermId> = DetHashSet::default();
            let mut stack = clause.to_vec();
            while let Some(term) = stack.pop() {
                if !seen.insert(term) {
                    continue;
                }
                if seen.len() > MAX_KEY_TERMS {
                    return None;
                }
                if let Some(spelling) = spelling(term) {
                    bytes += spelling.len();
                    if bytes > MAX_KEY_BYTES {
                        return None;
                    }
                    spellings.push((term, spelling));
                }
                push_children(terms, term, &mut stack)?;
            }
            spellings.sort_unstable_by_key(|(term, _)| *term);
        }
        let key = Self {
            kind,
            clause: clause.to_vec(),
            dialect: dialect::current(),
            spellings,
        };
        Some((key, bytes))
    }
}

/// Every term the printer may format below `term`; `None` for a term this
/// walk does not know the children of, which is then never keyed.
fn push_children(terms: &TermStore, term: TermId, stack: &mut Vec<TermId>) -> Option<()> {
    match terms.get(term) {
        TermData::Const(_) | TermData::Var(..) => {}
        TermData::App(_, args) => stack.extend(args.iter().copied()),
        TermData::Let(bindings, body) => {
            stack.extend(bindings.iter().map(|(_, bound)| *bound));
            stack.push(*body);
        }
        TermData::Not(inner) => stack.push(*inner),
        TermData::Ite(condition, then_branch, else_branch) => {
            stack.extend([*condition, *then_branch, *else_branch]);
        }
        TermData::Forall(_, body, triggers) | TermData::Exists(_, body, triggers) => {
            stack.push(*body);
            stack.extend(triggers.iter().flatten().copied());
        }
        _ => return None,
    }
    Some(())
}

#[derive(Default)]
struct Supported {
    /// Each lemma answered `true`, and the store it was rendered from.
    entries: DetHashMap<Key, TermStoreSnapshotStamp>,
    bytes: usize,
}

thread_local! {
    static SUPPORTED: RefCell<Supported> = RefCell::new(Supported::default());
}

/// `render`'s answer for the lemma `(kind, clause)`, or `true` without it
/// when this thread has already rendered that lemma, from this store, under
/// these spellings and this dialect.
pub(super) fn answered(
    terms: &TermStore,
    kind: TheoryLemmaKind,
    clause: &[TermId],
    overrides: Option<&HashMap<TermId, String>>,
    render: impl FnOnce() -> bool,
) -> bool {
    if super::super::resolution_dag_memo::memo_disabled() {
        return render();
    }
    let Some((key, bytes)) = Key::of(terms, kind, clause, overrides) else {
        return render();
    };
    if supported_already(&key, terms) {
        return true;
    }
    let stamp = terms.snapshot_stamp();
    let answer = render();
    if answer {
        remember_supported(key, stamp, bytes);
    }
    answer
}

/// Whether this thread rendered the lemma `key` names `true`, from `terms`
/// or a store `terms` only extends.
fn supported_already(key: &Key, terms: &TermStore) -> bool {
    SUPPORTED.with(|supported| {
        supported
            .borrow()
            .entries
            .get(key)
            .is_some_and(|stamp| stamp.is_append_only_prefix_of(terms))
    })
}

/// Remember that the lemma `key` names rendered `true` from the store
/// `stamp` stamps.
fn remember_supported(key: Key, stamp: TermStoreSnapshotStamp, bytes: usize) {
    SUPPORTED.with(|supported| {
        let mut supported = supported.borrow_mut();
        if supported.entries.len() >= MAX_ENTRIES || supported.bytes + bytes > MAX_RETAINED_BYTES {
            *supported = Supported::default();
        }
        if supported.entries.insert(key, stamp).is_none() {
            supported.bytes += bytes;
        }
    });
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_core::Sort;

    #[test]
    fn a_supported_lemma_is_answered_again_without_a_render_until_its_store_changes() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::bitvec(8));
        let y = terms.mk_var("y", Sort::bitvec(8));
        let equal = terms.mk_eq(x, y);
        let kind = TheoryLemmaKind::BvBitBlast;
        let renders = std::cell::Cell::new(0);
        let render = |answer: bool| {
            renders.set(renders.get() + 1);
            answer
        };
        // A decline is never remembered.
        assert!(!answered(&terms, kind, &[equal], None, || render(false)));
        assert!(answered(&terms, kind, &[equal], None, || render(true)));
        assert_eq!(renders.get(), 2);
        assert!(answered(&terms, kind, &[equal], None, || render(false)));
        assert_eq!(renders.get(), 2, "the remembered lemma rendered again");
        // Growth keeps the lemma's terms; a different spelling of one of
        // them is a different lemma.
        let _ = terms.mk_var("z", Sort::bitvec(8));
        assert!(answered(&terms, kind, &[equal], None, || render(false)));
        assert_eq!(renders.get(), 2);
        let mut overrides = HashMap::default();
        overrides.insert(x, "|x|".to_string());
        assert!(!answered(&terms, kind, &[equal], Some(&overrides), || {
            render(false)
        }));
        assert_eq!(renders.get(), 3);
        // Another store is never served from this one's answers.
        let mut other = TermStore::new();
        let x = other.mk_var("x", Sort::bitvec(8));
        let y = other.mk_var("y", Sort::bitvec(8));
        let equal = other.mk_eq(x, y);
        assert!(!answered(&other, kind, &[equal], None, || render(false)));
        assert_eq!(renders.get(), 4);
    }
}
