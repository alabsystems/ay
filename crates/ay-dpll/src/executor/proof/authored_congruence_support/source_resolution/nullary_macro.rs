// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Raw-ledger roots whose authored row names a nullary `define-fun`.
//!
//! A `RawIdentity` grant authenticates a root's TERM and publishes its
//! canonical rendering, on the premise that the author's spelling survives in
//! that rendering or in descendant overrides. A nullary macro breaks that
//! premise: `raw_intern_surface` elaborates the symbol `one` to its body, so
//! the raw root of `(assert (= v0 one))` renders `(= v0 #b1)` and no
//! descendant override can say `one` without re-spelling every `#b1` in the
//! document. MEASURED on a BV row with `(define-fun one () (_ BitVec 1) #b1)`:
//! the packed bit-blast refutation published `(assume t0 (= v0 #b1))` and
//! pinned carcara 1.1.0 refused the document at `t0` ("could not match term
//! to any of the original problem premises"). Without
//! `--apply-function-defs` carcara holds `(= one #b1)` as a premise, which is
//! exactly the bridge the Alethe printer's authored-assume equivalence can
//! `assume` (`ay_proof::nullary_definition_assume_bridge_is_supported`).
//!
//! This pass only re-selects a PRESENTATION for a root the raw ledgers
//! already authenticated: it grants no authority, and it re-spells a root only
//! when exactly one authored spelling expands to the root's canonical text, or,
//! when none does, exactly one macro row's raw re-intern is the root, and the
//! printer's own builder proves that spelling equal to it. Everything else
//! keeps the `RawIdentity` presentation it had.
//!
//! The same shape comes from the BV guarded-collapse lane, which raw-interns
//! the macro-EXPANDED authored assertion on purpose (`bv_identity_promotion/
//! guarded/source.rs`) and can install its candidate at the final boundary,
//! after the ordinary restoration pass. That lane deliberately purges every
//! other spelling of what it prints, so `finalize_bv_source_proof` re-spells
//! ONLY these macro roots ([`Executor::respell_nullary_macro_roots_of`]); a
//! full second restoration re-added purged root spellings and turned the
//! lane's checked bit-blast lowering into a `hole` (measured on the
//! source-bound frame fixtures).

use super::*;
use crate::executor::normalize_premise_surface;
use ay_core::quote_symbol;

/// Frontend nodes one row's expansion may visit, the body walk included.
const MAX_ROW_NODES: usize = 64 * 1024;
/// Frontend nodes all rows' expansions may visit together.
const MAX_TOTAL_NODES: usize = 1024 * 1024;
/// Nesting depth one expansion may recurse through.
const MAX_DEPTH: usize = 256;

impl Executor {
    /// Re-spell each `RawIdentity` root whose canonical rendering is exactly
    /// one authored row with its nullary `define-fun` symbols expanded, or,
    /// when no expansion spells it, whose raw re-intern IS exactly one macro
    /// row, when the printer can bridge that row's spelling back to the root.
    pub(in super::super) fn respell_nullary_macro_raw_roots(
        &mut self,
        sources: Vec<ReachableAuthoredSource>,
    ) -> Vec<ReachableAuthoredSource> {
        let raw_roots: Vec<TermId> = sources
            .iter()
            .filter_map(|source| match source {
                ReachableAuthoredSource::RawIdentity(root) => Some(*root),
                _ => None,
            })
            .collect();
        if raw_roots.is_empty() {
            return sources;
        }
        let definitions = self.nullary_definition_premises();
        if definitions.is_empty() {
            return sources;
        }
        let (rows, macro_rows) = self.nullary_macro_rows(&definitions);
        if macro_rows.is_empty() {
            return sources;
        }
        let Some(canonical) = canonical_render::render(&self.ctx.terms, raw_roots) else {
            return sources;
        };
        let mut by_raw_root = None;
        let mut respelled = Vec::with_capacity(sources.len());
        for source in sources {
            let ReachableAuthoredSource::RawIdentity(root) = source else {
                respelled.push(source);
                continue;
            };
            let exact = canonical
                .get(&root)
                .and_then(|text| rows.get(&normalize_premise_surface(text)))
                .copied();
            let row = match exact {
                Some(row) => row,
                None => by_raw_root
                    .get_or_insert_with(|| self.macro_rows_by_raw_root(&macro_rows))
                    .get(&root)
                    .copied()
                    .flatten(),
            };
            let row = row
                .map(|index| self.ctx.assertions_parsed()[index].clone())
                .filter(|row| self.macro_row_is_bridged(root, row, &definitions));
            respelled.push(match row {
                Some(row) => ReachableAuthoredSource::Parsed(root, row, false),
                None => source,
            });
        }
        respelled
    }

    /// Whether a macro row may present `root`: its head is one the planner
    /// confines (or it is a bare macro symbol, which has no head to compare),
    /// and the printer's definition-reading bridge proves it equal to `root`
    /// (`ay_proof::nullary_definition_assume_bridge_is_supported`, the
    /// planner's own admission).
    fn macro_row_is_bridged(
        &self,
        root: TermId,
        row: &FrontendTerm,
        definitions: &DetHashMap<String, String>,
    ) -> bool {
        (authored_surface_is_assume_confinable(&self.ctx.terms, root, row)
            || bare_macro_row(row, definitions))
            && ay_proof::nullary_definition_assume_bridge_is_supported(
                &self.ctx.terms,
                root,
                &proof_surface_syntax::format_frontend_term(
                    proof_surface_syntax::strip_frontend_annotations(row),
                ),
                definitions,
            )
    }

    /// Parsed-row index of the one macro row whose raw re-intern is each
    /// root, `None` where two different spellings re-intern to it.
    ///
    /// Raw interning canonicalizes comparisons, so `(assert (and lo r))` over
    /// `(define-fun lo () Bool (>= x 3))` has the raw root `(and (<= 3 x) r)`
    /// while its expansion reads `(and (>= x 3) r)`: no expansion spells the
    /// root, but `raw_intern_surface` of the row IS the root, exactly as the
    /// raw ledger minted it (`proof_original_rebuild.rs`), and the printer
    /// bridges `(and lo r)` with `cong`, the definition premise and
    /// `comp_simplify`. MEASURED at the base: the root kept its `RawIdentity`
    /// text, the query published `(assume t1 (and (<= 3 x) r))` under
    /// `foreign_assumes=yes`, and pinned carcara 1.1.0 refused it ("could not
    /// match term to any of the original problem premises").
    ///
    /// The lookup is exact and costs one re-intern per macro row, the work
    /// the ledger already spent, so no probe budget can run out. An earlier
    /// draft instead tried the printer preflight on every macro row under a
    /// 64-probe pass budget, and from 65 macro rows upward that budget ran
    /// out and the root kept its foreign canonical text (MEASURED: `(assume
    /// t1 (and (< 0 x0) (> x0 (- 5))))`, carcara `invalid`).
    fn macro_rows_by_raw_root(
        &mut self,
        macro_rows: &[usize],
    ) -> DetHashMap<TermId, Option<usize>> {
        let mut by_root: DetHashMap<TermId, Option<usize>> = DetHashMap::default();
        for &index in macro_rows {
            let row = self.ctx.assertions_parsed()[index].clone();
            // The raw ledger re-interns only application rows.
            if !matches!(
                proof_surface_syntax::strip_frontend_annotations(&row),
                FrontendTerm::App(_, _)
            ) {
                continue;
            }
            let Some(raw) = self.raw_intern_surface(&row) else {
                continue;
            };
            let spelling = row_spelling(&row);
            let parsed = self.ctx.assertions_parsed();
            by_root
                .entry(raw)
                .and_modify(|slot| {
                    if slot.is_some_and(|prior| row_spelling(&parsed[prior]) != spelling) {
                        *slot = None;
                    }
                })
                .or_insert(Some(index));
        }
        by_root
    }

    /// Whether a source row may present `root` at all; see
    /// [`Self::authored_row_confinement`].
    pub(in super::super) fn authored_row_is_assume_confinable(
        &self,
        root: TermId,
        row: &FrontendTerm,
        definitions: &mut Option<DetHashMap<String, String>>,
    ) -> bool {
        self.authored_row_confinement(root, row, definitions)
            .is_some()
    }

    /// How a source row may present `root`: `None` when it may not,
    /// `Some(false)` when [`authored_surface_is_assume_confinable`] admits it
    /// by head, and `Some(true)` when the row names a nullary `define-fun` and
    /// the printer's definition-reading bridge proves it equal to `root`
    /// (`ay_proof::nullary_definition_assume_bridge_is_supported`, the
    /// planner's own admission). `definitions` is filled once, on the first
    /// macro-naming row.
    ///
    /// A head comparison cannot judge a bare symbol (`(assert lo)` over
    /// `(define-fun lo () Bool (bvult x #x3))` elaborates to `(bvult x #x3)`)
    /// or a double negation `mk_not` dropped (`(assert (not (not lo)))`).
    /// Declared unconfinable, such a root kept whatever spelling an earlier
    /// pass left: a proof-replacing lane purged it, or the ordinary collector
    /// overwrote it while descending a LATER row's `(not body)` onto the same
    /// `TermId`. Either way the published `assume` was the expanded body.
    /// MEASURED on pinned carcara 1.1.0: "could not match term to any of the
    /// original problem premises" at that `assume`.
    ///
    /// `Some(true)` is `Parsed`'s replacing bit. A bridged macro spelling is
    /// confined to its `assume` by the printer's planner, so a spelling the
    /// collector left on the root from another row's descendant is stale for
    /// it. Without the bit, `(assert lo)` then `(assert (not (bvult x #x3)))`
    /// met the descendant `(bvult x #x3)` on the root, the restoration
    /// declined the whole reconstruction, and the query answered `unknown`
    /// under `:produce-proofs` (it published `unsat` with a foreign `assume`
    /// before the bare-symbol bridge existed).
    pub(in super::super) fn authored_row_confinement(
        &self,
        root: TermId,
        row: &FrontendTerm,
        definitions: &mut Option<DetHashMap<String, String>>,
    ) -> Option<bool> {
        let by_head = authored_surface_is_assume_confinable(&self.ctx.terms, root, row);
        if !row_names_nullary_macro(&self.ctx, row) {
            return by_head.then_some(false);
        }
        let definitions = definitions.get_or_insert_with(|| self.nullary_definition_premises());
        let bridged = ay_proof::nullary_definition_assume_bridge_is_supported(
            &self.ctx.terms,
            root,
            &proof_surface_syntax::format_frontend_term(
                proof_surface_syntax::strip_frontend_annotations(row),
            ),
            definitions,
        );
        if bridged {
            Some(true)
        } else {
            by_head.then_some(false)
        }
    }

    /// The presentation one source row gives `root`: `Parsed` when
    /// [`Self::authored_row_confinement`] admits it, `Untouched` when it does
    /// not, and `AletheSurfaceUnavailable` when that unconfined row would
    /// publish a foreign `assume` ([`Self::unconfined_macro_row_is_foreign`]).
    pub(in super::super) fn single_authored_row_source(
        &self,
        root: TermId,
        row: &FrontendTerm,
        definitions: &mut Option<DetHashMap<String, String>>,
    ) -> Result<ReachableAuthoredSource, AuthoredSourceResolutionFailure> {
        match self.authored_row_confinement(root, row, definitions) {
            Some(stale) => Ok(ReachableAuthoredSource::Parsed(root, row.clone(), stale)),
            None if self.unconfined_macro_row_is_foreign(root, row) => {
                Err(AuthoredSourceResolutionFailure::AletheSurfaceUnavailable)
            }
            None => Ok(ReachableAuthoredSource::Untouched),
        }
    }

    /// Whether a single source row that [`Self::authored_row_confinement`]
    /// refused would publish a FOREIGN `assume`: it names a nullary macro,
    /// and no earlier pass left its authored spelling on the root. Source
    /// resolution then withholds the Alethe surface (`AletheSurfaceUnavailable`,
    /// exactly as for an unconfinable repeated row) instead of leaving the
    /// root `Untouched`; the native proof and its verdict are unaffected.
    ///
    /// Elaboration replaced the macro symbol, so the root's canonical text is
    /// the expanded body, which pinned carcara 1.1.0, run without
    /// `--apply-function-defs`, matches against no premise. MEASURED before
    /// this refusal on `(define-fun m () Bool (let ((y (+ x 1))) (< y 0)))`,
    /// `(assert m)`, `(assert (> x 5))`, on an array body `(= (select (store a
    /// 0 v) 0) w)`, and on folded macro rows such as `(and lo (= x x))`: each
    /// query published the expanded `assume` under `foreign_assumes=yes`, and
    /// carcara answered `invalid` ("could not match term to any of the
    /// original problem premises"). A root that still carries the authored
    /// spelling prints it at its `assume` and is left to the printer's own
    /// fail-closed surface gates (`(assert hi)` over `(define-fun hi () Bool
    /// (or lo r))` publishes an honest `hole` there).
    fn unconfined_macro_row_is_foreign(&self, root: TermId, row: &FrontendTerm) -> bool {
        row_names_nullary_macro(&self.ctx, row)
            && self
                .last_proof_term_overrides
                .as_ref()
                .and_then(|overrides| overrides.get(&root))
                .is_none_or(|spelling| *spelling != row_spelling(row))
    }

    /// The final-boundary twin of the restoration pass, narrowed to the one
    /// presentation it owes: every reachable raw-ledger root of `proof` that
    /// [`Self::respell_nullary_macro_raw_roots`] re-spells gets its authored
    /// root spelling. Nothing else is added, removed or replaced, and a
    /// conflicting existing spelling keeps it.
    ///
    /// A root that is itself a source row is included. The lane purges the
    /// spelling the ordinary restoration gave it, and nothing runs after this
    /// pass. MEASURED at the base on `(define-fun lo () Bool (bvslt x #x00))`,
    /// `(assert (not lo))`, `(assert (bvslt x #xf0))`: the final joint
    /// candidate purged `(not lo)`, the query published `(assume t0 (not
    /// (bvslt x #b00000000)))` under `foreign_assumes=yes`, and pinned carcara
    /// 1.1.0 refused it. A row that names no macro has no expansion entry, so
    /// its lane presentation stands.
    pub(in crate::executor::proof) fn respell_nullary_macro_roots_of(&mut self, proof: &Proof) {
        let Some(roots) = reachable_authored_assume_roots(proof) else {
            return;
        };
        let raw: DetHashSet<TermId> = self
            .last_proof_raw_original_assertions
            .iter()
            .copied()
            .collect();
        let sources = roots
            .into_iter()
            .filter(|root| raw.contains(root) && self.last_proof_rebuild_originals.contains(root))
            .map(ReachableAuthoredSource::RawIdentity)
            .collect();
        let mut overrides = self.last_proof_term_overrides.clone().unwrap_or_default();
        let mut changed = false;
        for source in self.respell_nullary_macro_raw_roots(sources) {
            let ReachableAuthoredSource::Parsed(root, row, _) = source else {
                continue;
            };
            let mut root_override = DetHashMap::default();
            proof_surface_syntax::collect_root_surface_term_override(
                &mut self.ctx,
                root,
                &row,
                &mut root_override,
            );
            let Some(surface) = root_override.remove(&root) else {
                continue;
            };
            if overrides
                .get(&root)
                .is_some_and(|existing| existing != &surface)
            {
                continue;
            }
            changed |= overrides.insert(root, surface).is_none();
        }
        if changed && proof_surface_syntax::surface_override_map_is_bounded(&overrides) {
            self.last_proof_term_overrides = Some(overrides);
        }
    }

    /// Expanded text, compared as `normalize_premise_surface` compares an
    /// `assume` with a premise (whitespace and bit-vector literal spelling
    /// are not distinctions to the checker's parser) -> the parsed-row index
    /// of the one authored row spelling it through a nullary macro, or `None`
    /// when two different authored spellings expand to it; and the index of
    /// every row whose expansion names a macro.
    /// Empty on any budget overrun, which keeps today's presentation.
    fn nullary_macro_rows(
        &self,
        definitions: &DetHashMap<String, String>,
    ) -> (DetHashMap<String, Option<usize>>, Vec<usize>) {
        let mut rows: DetHashMap<String, Option<usize>> = DetHashMap::default();
        let mut macro_rows = Vec::new();
        let mut total = MAX_TOTAL_NODES;
        let parsed = self.ctx.assertions_parsed();
        for (index, row) in parsed.iter().enumerate() {
            let stripped = proof_surface_syntax::strip_frontend_annotations(row);
            let mut budget = MAX_ROW_NODES.min(total);
            let mut replaced = false;
            let expanded = expand_nullary_macros(
                &self.ctx,
                definitions,
                stripped,
                0,
                &mut replaced,
                &mut budget,
            );
            total -= MAX_ROW_NODES.min(total) - budget;
            if total == 0 {
                return (DetHashMap::default(), Vec::new());
            }
            let Some(expanded) = expanded.filter(|_| replaced) else {
                continue;
            };
            macro_rows.push(index);
            let authored = row_spelling(row);
            let expanded = proof_surface_syntax::format_frontend_term(&expanded);
            rows.entry(normalize_premise_surface(&expanded))
                .and_modify(|slot| {
                    if slot.is_some_and(|prior| row_spelling(&parsed[prior]) != authored) {
                        *slot = None;
                    }
                })
                .or_insert(Some(index));
        }
        (rows, macro_rows)
    }
}

/// The printed spelling of an authored row, annotations aside.
fn row_spelling(row: &FrontendTerm) -> String {
    proof_surface_syntax::format_frontend_term(proof_surface_syntax::strip_frontend_annotations(
        row,
    ))
}

/// Whether `row` is, annotations aside, exactly one nullary `define-fun`
/// symbol of `definitions`.
fn bare_macro_row(row: &FrontendTerm, definitions: &DetHashMap<String, String>) -> bool {
    matches!(
        proof_surface_syntax::strip_frontend_annotations(row),
        FrontendTerm::Symbol(name) if definitions.contains_key(&quote_symbol(name))
    )
}

/// Whether `row` mentions a nullary `define-fun` symbol outside any binder,
/// within [`MAX_ROW_NODES`] frontend nodes (an oversized row answers `false`
/// and keeps the head judgement alone).
pub(super) fn row_names_nullary_macro(ctx: &ay_frontend::Context, row: &FrontendTerm) -> bool {
    let mut budget = MAX_ROW_NODES;
    let mut stack: Vec<&FrontendTerm> = vec![row];
    while let Some(term) = stack.pop() {
        let Some(left) = budget.checked_sub(1) else {
            return false;
        };
        budget = left;
        match proof_surface_syntax::strip_frontend_annotations(term) {
            FrontendTerm::Symbol(name) => {
                if ctx.source_nullary_definition_for_proof(name).is_some() {
                    return true;
                }
            }
            FrontendTerm::App(_, args) | FrontendTerm::IndexedApp(_, _, args) => {
                stack.extend(args.iter());
            }
            _ => {}
        }
    }
    false
}

/// `term` with every nullary `define-fun` symbol replaced by its (expanded)
/// body, or `None` for a shape this pass does not judge: a binder, `let`,
/// `match`, qualified application, or an exhausted budget or depth. Binders
/// are refused outright, so no bound name can shadow a macro.
fn expand_nullary_macros(
    ctx: &ay_frontend::Context,
    definitions: &DetHashMap<String, String>,
    term: &FrontendTerm,
    depth: usize,
    replaced: &mut bool,
    budget: &mut usize,
) -> Option<FrontendTerm> {
    *budget = budget.checked_sub(1)?;
    if depth > MAX_DEPTH {
        return None;
    }
    let mut expand_all = |args: &[FrontendTerm], replaced: &mut bool| {
        args.iter()
            .map(|arg| expand_nullary_macros(ctx, definitions, arg, depth + 1, replaced, budget))
            .collect::<Option<Vec<_>>>()
    };
    match proof_surface_syntax::strip_frontend_annotations(term) {
        FrontendTerm::Symbol(name) if definitions.contains_key(&quote_symbol(name)) => {
            // A body naming another macro expands too; the printer bridges it
            // with a nested definition leaf joined by `trans`. The depth bound
            // stops a cyclic chain, which the frontend already refuses.
            let body = ctx.source_nullary_definition_for_proof(name)?;
            *replaced = true;
            expand_all(std::slice::from_ref(body), replaced)?.pop()
        }
        leaf @ (FrontendTerm::Symbol(_) | FrontendTerm::Const(_)) => Some(leaf.clone()),
        FrontendTerm::App(head, args) => {
            Some(FrontendTerm::App(head.clone(), expand_all(args, replaced)?))
        }
        FrontendTerm::IndexedApp(head, indices, args) => Some(FrontendTerm::IndexedApp(
            head.clone(),
            indices.clone(),
            expand_all(args, replaced)?,
        )),
        _ => None,
    }
}

// EXPLICIT: this file is itself loaded through a `#[path]` (see
// `identity_surfaces.rs`), so a bare `mod tests;` would not resolve here.
#[cfg(test)]
#[path = "nullary_macro/tests.rs"]
mod tests;
