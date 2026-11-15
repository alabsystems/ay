//! Reconcile actual installed clauses with a still-live theory instance.
//! The input must be a current SAT-scope post-add ledger, never planned seen
//! entries or unvalidated historical cache rows. No clause is installed here.
use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::{TheoryLemma, TheoryLemmaReplay, TheoryResult, TheorySolver};

pub(crate) fn recheck_installed_theory_lemmas<T: TheorySolver>(
    theory: &mut T,
    initial: TheoryResult,
    installed: &[TheoryLemma],
    should_stop: &dyn Fn() -> bool,
) -> TheoryResult {
    recheck_installed_theory_lemmas_with(theory, initial, installed, should_stop, T::check)
}

/// Repeat exactly the caller's checking phase. In particular a provisional
/// propagation Sat must still pass the ordinary full check before acceptance.
pub(crate) fn recheck_installed_theory_lemmas_with<T: TheorySolver>(
    theory: &mut T,
    initial: TheoryResult,
    installed: &[TheoryLemma],
    should_stop: &dyn Fn() -> bool,
    mut check: impl FnMut(&mut T) -> TheoryResult,
) -> TheoryResult {
    if !matches!(initial, TheoryResult::NeedLemmas(_)) || installed.is_empty() {
        return initial;
    }
    if should_stop() {
        return TheoryResult::Unknown;
    }
    // Exact ordered-slice equality is stronger than signed-set equality. An
    // unrecognized ordering simply receives no acknowledgment. ROW2 clauses
    // are already sorted/deduped; borrow their payloads without cloning them.
    // A clause can fund at most one successful current-work acknowledgment
    // in this helper call, even if a theory internally reconstructs its work.
    // This gives a finite progress bound from the actual ledger, not a fresh
    // solver budget or a duplicate-to-SAT shortcut.
    let mut known: HashMap<&[ay_core::TheoryLit], bool> = HashMap::default();
    if known.try_reserve(installed.len()).is_err() {
        return TheoryResult::Unknown;
    }
    for (index, lemma) in installed.iter().enumerate() {
        if index % 64 == 0 && should_stop() {
            return TheoryResult::Unknown;
        }
        known.insert(lemma.clause.as_slice(), false);
    }
    let mut result = initial;
    loop {
        if should_stop() {
            return TheoryResult::Unknown;
        }
        let TheoryResult::NeedLemmas(requested) = result else {
            return result;
        };
        let mut changed = false;
        let mut has_new = false;
        for (index, lemma) in requested.iter().enumerate() {
            if index % 64 == 0 && should_stop() {
                return TheoryResult::Unknown;
            }
            if let Some(replayed) = known.get_mut(lemma.clause.as_slice()) {
                if !*replayed
                    && matches!(
                        theory.reacknowledge_applied_theory_lemma(&lemma.clause),
                        TheoryLemmaReplay::CurrentWorkAcknowledged,
                    )
                {
                    *replayed = true;
                    changed = true;
                }
            } else {
                has_new = true;
            }
        }
        if !changed {
            // Preserve the original handler for other/default theories. Mere
            // membership never supplies a SAT result or an extra recheck loop.
            return TheoryResult::NeedLemmas(requested);
        }
        if has_new {
            let mut new = Vec::new();
            if new.try_reserve_exact(requested.len()).is_err() {
                return TheoryResult::Unknown;
            }
            for (index, lemma) in requested.into_iter().enumerate() {
                if index % 64 == 0 && should_stop() {
                    return TheoryResult::Unknown;
                }
                if !known.contains_key(lemma.clause.as_slice()) {
                    new.push(lemma);
                }
            }
            return TheoryResult::NeedLemmas(new);
        }
        // Recheck this instance with its original stop/deadline and existing
        // handlers. New/changed clauses still require the ordinary add path.
        result = check(theory);
    }
}
