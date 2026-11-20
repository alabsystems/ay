// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! What the PROBLEM spells at an `assume`, as against what AY stores for it.
//!
//! `TermStore::mk_not` eliminates a double negation at term CONSTRUCTION, so
//! `(assert (not (not phi)))` never produces a `TermId` for `(not (not phi))`
//! at all: the assertion stack, the provenance record and the proof's `Assume`
//! leaf all hold `phi`. Every term-level provenance check therefore answers
//! "yes, the problem asserted this" about AY's own rewriting — which is
//! precisely how `foreign_assumes=no` was printed beside a carcara refusal on
//! the document's FIRST line:
//!
//! ```text
//! [ERROR] checking failed on step 't0' with rule 'assume': could not match
//!         term to any of the original problem premises:
//!         (= (concat (_ bv0 24) (_ bv0 8))
//!            (concat (_ bv0 24) (select packet (_ bv28 32))))
//! ```
//!
//! (`benchmarks/smtlib-all/QF_ABV/non-incremental__QF_ABV__egt__egt-6069.smt2`,
//! whose assertion 6 is `(assert (not (not (= ...))))`.) The blindness is not a
//! bug in the detector's comparison; it is a consequence of comparing terms at
//! all, because the authored term is not representable. The authored SYNTAX is
//! still in hand — `Context::assertions_parsed` keeps the parse tree — so this
//! module answers the question on the syntax instead.
//!
//! Two outputs, and they are deliberately the two halves of the same decision:
//!
//! * `bridgeable` — the authored spelling is exactly `k` `not` shell pairs
//!   around the text the DOCUMENT prints for the term, so the printer can
//!   `assume` the problem's own bytes and derive that unit with `k` stock
//!   `not_not` tautologies. Admitted by
//!   `ay_proof::negation_shell_assume_surface_pairs`, the SAME predicate the
//!   printer re-asks at emission, so producer and printer cannot disagree
//!   about a leaf without the export failing closed.
//! * `unbridgeable` — the authored spelling lost `not` shells AND is not that
//!   shape, so any `assume` of the term prints a rewriting the problem does not
//!   state. Nothing can be emitted honestly for it, and the certificate must
//!   say so (`foreign_assumes=yes`, `ay_self_checkable=no`).
//!
//! A second, independent rule rides the same scan: a `let`-ROOTED authored
//! assertion whose printed leaf is not itself a `let` can never match, because
//! carcara's `assume` matching recurses THROUGH `Term::Let` and never
//! eliminates it. That one is judged on the root token alone, so no rendering
//! difference inside the body can turn it into a false accusation. It was found
//! by the seed-5309 sweep as a SECOND live false green (QF_ABV `egt-1488`,
//! whose assertion 10 is `(assert (let ((?v_0 …)) (= … (_ bv50 32))))` and
//! whose leaf printed `(= (_ bv50 32) ((_ zero_extend 24) (select …)))`).
//!
//! Both rules judge against the PRINTED text: a source override that already
//! restores the authored spelling (what the surface-override channel does for
//! `(not (and a b))` elaborated to an `or`) leaves nothing stripped in the
//! document and is not foreign.
//!
//! NOT covered, and the reason is measured rather than assumed: a general
//! "authored text != printed text" rule would be the whole boundary in one
//! predicate, but `Context::assertions_parsed` retains the parse tree BEFORE
//! `define-fun` expansion, while both AY and carcara expand. Every macro-using
//! benchmark would be accused of a rewriting it did not make. Shapes such as a
//! conjunct assumed out of an authored `(and A B)` therefore stay open.
//!
//! `AY_DEBUG_SHELL=1` prints each unbridgeable pair to stderr. It is a
//! diagnostic only: nothing about the emitted document or the verdict depends
//! on it.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::TermData;
use ay_core::TermId;
use ay_frontend::command::Term as FrontendTerm;

use super::proof_surface_syntax::{format_frontend_term, strip_frontend_annotations};
use super::Executor;

mod export_surfaces;
#[cfg(test)]
mod tests;

pub(in crate::executor) use export_surfaces::AuthoredExportSurfaces;

/// Assertion stacks past this are not judged. The whole scan is linear, but a
/// pathological stack must not turn certificate disclosure into the run's cost
/// centre; declining to judge preserves today's behaviour exactly.
const MAX_JUDGED_ASSERTIONS: usize = 16_384;
/// Per-assertion and aggregate caps on rendered authored text. The printed
/// side is judged by the same per-assertion cap, rendered under it (see
/// `printed_assume_text`); the aggregate binds only the authored surfaces of
/// the negation-shell branch, as on origin/main.
const MAX_SHELL_SURFACE_BYTES: usize = 64 * 1024;
const MAX_SHELL_TOTAL_BYTES: usize = 8 * 1024 * 1024;

#[cfg(test)]
thread_local! {
    /// `printed_assume_text` renders this thread has run (pins that every
    /// `let`-rooted assertion is judged, with no aggregate cutoff).
    static PRINTED_ASSUME_RENDERS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// Authored `assume` spellings the emitted document would otherwise misstate.
#[derive(Default, Debug)]
pub(in crate::executor) struct AuthoredNegationShellSpellings {
    /// Canonical assume term -> the exact authored text, admitted for the
    /// printer's `not_not` bridge.
    pub(in crate::executor) bridgeable: HashMap<TermId, String>,
    /// Canonical assume terms no honest `assume` can be printed for.
    pub(in crate::executor) unbridgeable: HashSet<TermId>,
}

/// Leading `not` applications on the AUTHORED syntax, annotations stripped.
fn frontend_negation_shell_depth(term: &FrontendTerm) -> usize {
    let mut depth = 0usize;
    let mut cursor = strip_frontend_annotations(term);
    while let FrontendTerm::App(op, args) = cursor {
        if op != "not" || args.len() != 1 {
            break;
        }
        depth += 1;
        cursor = strip_frontend_annotations(&args[0]);
    }
    depth
}

/// Leading `Not` wrappers the term store actually kept.
fn canonical_negation_shell_depth(terms: &ay_core::TermStore, term: TermId) -> usize {
    let mut depth = 0usize;
    let mut cursor = term;
    while let TermData::Not(inner) = terms.get(cursor) {
        depth += 1;
        cursor = *inner;
    }
    depth
}

impl Executor {
    /// Exactly the text the exported document will print for `term`, when it
    /// is at most `MAX_SHELL_SURFACE_BYTES` long; `None` past that.
    ///
    /// The override table is the one the export hands the printer, and it is
    /// materialized at most once per scan (only when a candidate exists).
    ///
    /// Rendered BOUNDED (DR-PROOF-RENDER-BUDGET-20261118). Rendering in full
    /// and measuring afterwards was a memout, not a size check: a `let`-shared
    /// assertion of a few thousand DAG nodes spells ~1e14 bytes (measured 4 GB
    /// after an `unsat` was already published). The bounded renderer streams
    /// and charges exactly the bytes it writes, so it answers `Some` for
    /// exactly the texts the unbounded `len() <= MAX_SHELL_SURFACE_BYTES` test
    /// admitted (classification is unchanged), and one render costs at most
    /// about that many bytes, however large the term (streamed, nothing is
    /// assembled or cached: the output is the only `String` that grows).
    ///
    /// It does NOT poll the solve's stop: the byte cap already bounds each
    /// call, and a stop here would turn faithful spellings into foreign
    /// premises after the verdict (the export runs past the solve deadline).
    fn printed_assume_text(
        &self,
        term: TermId,
        overrides: &mut Option<HashMap<TermId, String>>,
        loaded: &mut bool,
    ) -> Option<String> {
        if !*loaded {
            *overrides = self.proof_export_term_overrides();
            *loaded = true;
        }
        #[cfg(test)]
        PRINTED_ASSUME_RENDERS.with(|renders| renders.set(renders.get() + 1));
        ay_proof::format_term_alethe_bounded(
            &self.ctx.terms,
            term,
            overrides.as_ref(),
            MAX_SHELL_SURFACE_BYTES as u64,
            &mut || true,
        )
    }

    /// Classify every authored assertion whose `assume` leaf this document
    /// would spell differently from the problem file.
    ///
    /// Fails OPEN (empty result, today's behaviour) whenever the authored
    /// syntax and the provenance-tracked original stack cannot be aligned
    /// index-for-index: a misaligned view is not evidence of a rewriting, and
    /// inventing one would withhold verdicts for a bookkeeping reason.
    pub(in crate::executor) fn authored_negation_shell_spellings(
        &self,
    ) -> AuthoredNegationShellSpellings {
        let mut spellings = AuthoredNegationShellSpellings::default();
        let parsed = self.ctx.assertions_parsed();
        let originals = self.proof_original_problem_assertions_slice();
        if parsed.is_empty() || parsed.len() != originals.len() {
            return spellings;
        }
        if parsed.len() > MAX_JUDGED_ASSERTIONS {
            return spellings;
        }
        // A canonical term some OTHER assertion spells the way the document
        // prints it is genuinely a problem premise; a rewritten sibling spelling
        // does not make it foreign.
        let mut spelling_faithful: HashSet<TermId> = HashSet::default();
        let mut total_bytes = 0usize;
        // Materialized once, and only when a candidate exists: this is the same
        // table the export hands the printer.
        let mut effective_overrides: Option<HashMap<TermId, String>> = None;
        let mut effective_overrides_loaded = false;
        for (&canonical, authored) in originals.iter().zip(parsed.iter()) {
            // A `let`-ROOTED assertion assumed in eliminated form can never
            // match. This is not a heuristic about AY: carcara's `assume`
            // matching recurses THROUGH `Term::Let` and never eliminates it, so
            // a premise the problem wrote as `(let ...)` is matchable only by a
            // leaf that is still a `let`. Judged on the root token alone, which
            // is exactly the part that decides matchability and is immune to
            // every rendering difference inside the body.
            //
            // Every such assertion is judged by the per-assertion cap alone,
            // exactly as origin/main judged it: an aggregate cutoff here would
            // turn later faithful premises foreign and withhold `unsat` under
            // `--strict-proofs`/`--self-check`. Each render is bounded by that
            // cap, so the scan costs at most `MAX_JUDGED_ASSERTIONS` x 64 KiB
            // of transient writes and 64 KiB live.
            if matches!(strip_frontend_annotations(authored), FrontendTerm::Let(..)) {
                let printed = self.printed_assume_text(
                    canonical,
                    &mut effective_overrides,
                    &mut effective_overrides_loaded,
                );
                if printed.is_some_and(|printed| printed.starts_with("(let ")) {
                    spelling_faithful.insert(canonical);
                } else {
                    spellings.unbridgeable.insert(canonical);
                }
                continue;
            }
            let authored_depth = frontend_negation_shell_depth(authored);
            let canonical_depth = canonical_negation_shell_depth(&self.ctx.terms, canonical);
            if authored_depth <= canonical_depth {
                spelling_faithful.insert(canonical);
                continue;
            }
            if !super::proof_trust_surgery_surface_audit::surface_source_is_bounded(authored) {
                spellings.unbridgeable.insert(canonical);
                continue;
            }
            let surface = format_frontend_term(authored);
            let Some(next_total) = total_bytes.checked_add(surface.len()).filter(|&bytes| {
                surface.len() <= MAX_SHELL_SURFACE_BYTES && bytes <= MAX_SHELL_TOTAL_BYTES
            }) else {
                spellings.unbridgeable.insert(canonical);
                continue;
            };
            total_bytes = next_total;
            // Against the rendering the DOCUMENT will use for this term, not
            // the override-free canonical one: an assumed term commonly carries
            // a source override of its own, and the leaf must sit `k` shells
            // above whatever the rest of the document already prints for it.
            let Some(printed) = self.printed_assume_text(
                canonical,
                &mut effective_overrides,
                &mut effective_overrides_loaded,
            ) else {
                spellings.unbridgeable.insert(canonical);
                continue;
            };
            // ALREADY FAITHFUL. A source override can restore the authored
            // spelling on its own — that is exactly what the existing
            // surface-override channel does for `(not (and a b))` elaborated to
            // an `or`. Nothing is stripped in the emitted document, so nothing
            // is owed, and calling this foreign would withhold real evidence.
            if surface == printed {
                spelling_faithful.insert(canonical);
                continue;
            }
            if ay_proof::negation_shell_assume_surface_pairs(&surface, &printed).is_some() {
                spellings.bridgeable.insert(canonical, surface);
            } else {
                if std::env::var_os("AY_DEBUG_SHELL").is_some() {
                    ay_core::safe_eprintln!("c !! shell-unbridgeable");
                    ay_core::safe_eprintln!("c !!   authored={surface}");
                    ay_core::safe_eprintln!("c !!   printed={printed}");
                }
                spellings.unbridgeable.insert(canonical);
            }
        }
        // A bridgeable spelling wins over an unbridgeable sibling: the printer
        // can put the bridgeable one at the leaf and the leaf is then the
        // problem's own text.
        for term in spellings.bridgeable.keys() {
            spellings.unbridgeable.remove(term);
        }
        for term in &spelling_faithful {
            spellings.bridgeable.remove(term);
            spellings.unbridgeable.remove(term);
        }
        spellings
    }

    /// Canonical terms whose every authored spelling is a rewriting.
    pub(in crate::executor) fn unbridgeable_authored_assume_terms(&self) -> HashSet<TermId> {
        self.authored_negation_shell_spellings().unbridgeable
    }
}
