// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Scheduling-only lazy choices, published only by an accepted render.

use super::*;

const MAX_SETTLED: usize = 256;
pub(super) const MAX_SETTLED_BYTES: usize = 16 * 1024 * 1024;

#[derive(Default)]
struct Settled {
    entries: DetHashMap<String, DetHashSet<String>>,
    bytes: usize,
    publishing: bool,
}

thread_local! {
    static SETTLED: std::cell::RefCell<Settled> = std::cell::RefCell::new(Settled::default());
}

/// No step id or definition prefix participates in this scheduling key.
/// Cached opacity is not evidence: every resulting document still replays.
pub(super) fn settled_key(
    printer: &AlethePrinter<'_>,
    roots: &[TermId],
    case: Option<(&str, &case_split::Case)>,
) -> Option<String> {
    printer.check_emission_progress(0).ok()?;
    let mut key = case.map_or_else(String::new, |(_, case)| case.memo_key(printer));
    printer.check_emission_progress(0).ok()?;
    for &root in roots {
        printer.check_emission_progress(0).ok()?;
        let text = printer.format_term(root);
        printer.check_emission_progress(0).ok()?;
        key.push('\n');
        key.push_str(&text);
        printer.check_emission_progress(0).ok()?;
    }
    Some(key)
}

pub(super) fn settled_opaque(
    printer: &AlethePrinter<'_>,
    key: &str,
) -> Option<Option<DetHashSet<String>>> {
    printer.check_emission_progress(0).ok()?;
    let found = raw_lookup(key);
    printer.check_emission_progress(0).ok()?;
    Some(found)
}

pub(super) fn retained_opaque(
    printer: &AlethePrinter<'_>,
    opaque: DetHashSet<TermId>,
    kept: &DetHashSet<String>,
) -> Option<DetHashSet<TermId>> {
    let mut retained = DetHashSet::default();
    for term in opaque {
        printer.check_emission_progress(0).ok()?;
        let text = printer.format_term(term);
        printer.check_emission_progress(0).ok()?;
        if kept.contains(&text) {
            retained.insert(term);
        }
        printer.check_emission_progress(0).ok()?;
    }
    Some(retained)
}

pub(super) struct Candidate {
    key: String,
    kept: DetHashSet<String>,
}

impl Candidate {
    pub(super) fn new(
        printer: &AlethePrinter<'_>,
        key: String,
        opaque: &DetHashSet<TermId>,
    ) -> Option<Self> {
        printer.check_emission_progress(0).ok()?;
        let mut kept = DetHashSet::default();
        for &term in opaque {
            printer.check_emission_progress(0).ok()?;
            let text = printer.format_term(term);
            printer.check_emission_progress(0).ok()?;
            kept.insert(text);
        }
        printer.check_emission_progress(0).ok()?;
        Some(Self { key, kept })
    }

    pub(super) fn commit(self, printer: &AlethePrinter<'_>) -> Option<()> {
        printer.check_emission_progress(0).ok()?;
        let rollback_key = self.key.clone();
        printer.check_emission_progress(0).ok()?;
        let publication = publish(self.key, self.kept, rollback_key);
        // A post-retention refusal or callback unwind rolls back only this
        // transaction; an eviction's old table is moved, never deep-cloned.
        printer.check_emission_progress(0).ok()?;
        if let Some(mut publication) = publication {
            publication.prior = None;
            SETTLED.with(|settled| settled.borrow_mut().publishing = false);
        }
        Some(())
    }
}

enum Prior {
    Evicted(Settled),
    Entry {
        key: String,
        value: Option<DetHashSet<String>>,
        bytes: usize,
    },
}

struct Publication {
    prior: Option<Prior>,
}

impl Drop for Publication {
    fn drop(&mut self) {
        let Some(prior) = self.prior.take() else {
            return;
        };
        SETTLED.with(|settled| {
            let mut settled = settled.borrow_mut();
            match prior {
                Prior::Evicted(old) => *settled = old,
                Prior::Entry { key, value, bytes } => {
                    settled.entries.remove(&key);
                    if let Some(value) = value {
                        settled.entries.insert(key, value);
                    }
                    settled.bytes = bytes;
                    settled.publishing = false;
                }
            }
        });
    }
}

fn publish(key: String, kept: DetHashSet<String>, rollback_key: String) -> Option<Publication> {
    let bytes = kept
        .iter()
        .try_fold(key.len(), |bytes, term| bytes.checked_add(term.len()))?;
    if bytes > MAX_SETTLED_BYTES {
        return None;
    }
    SETTLED.with(|settled| {
        let mut settled = settled.borrow_mut();
        // A different owner may reenter through the observation callback.
        // Do not let it publish into, or later lose work to, this transaction.
        if settled.publishing {
            return None;
        }
        let evict = settled.entries.len() >= MAX_SETTLED
            || settled.bytes.saturating_add(bytes) > MAX_SETTLED_BYTES;
        let old_bytes = settled.bytes;
        let old = evict.then(|| std::mem::take(&mut *settled));
        settled.publishing = true;
        settled.bytes += bytes;
        let value = settled.entries.insert(key, kept);
        let prior = match old {
            Some(old) => Prior::Evicted(old),
            None => Prior::Entry {
                key: rollback_key,
                value,
                bytes: old_bytes,
            },
        };
        Some(Publication { prior: Some(prior) })
    })
}

pub(super) fn raw_lookup(key: &str) -> Option<DetHashSet<String>> {
    SETTLED.with(|settled| {
        let settled = settled.borrow();
        (!settled.publishing)
            .then(|| settled.entries.get(key).cloned())
            .flatten()
    })
}

#[cfg(test)]
pub(super) fn remember_settled(key: String, kept: DetHashSet<String>) {
    if let Some(mut publication) = publish(key.clone(), kept, key) {
        publication.prior = None;
        SETTLED.with(|settled| settled.borrow_mut().publishing = false);
    }
}

#[cfg(test)]
pub(super) fn reset() {
    SETTLED.with(|settled| *settled.borrow_mut() = Settled::default());
}
