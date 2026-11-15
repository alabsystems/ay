// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded print-faithful interning of binder-free authored terms.

use ay_core::{Symbol, TermId};
use ay_frontend::command::{Index as FrontendIndex, Term as FrontendTerm};

use super::Executor;
use crate::executor::proof_surface_syntax::strip_frontend_annotations;
use crate::executor::proof_trust_surgery_provenance::surface_source_is_bounded;

#[path = "proof_trust_surgery_surface_ground.rs"]
mod ground;
#[path = "proof_trust_surgery_surface_ground_dag.rs"]
mod ground_dag;

/// What [`Executor::raw_intern_surface_prechecked`] does with a binder.
#[derive(Clone, Copy)]
enum BinderPolicy {
    /// Refuse it, and with it the whole enclosing assertion. The behaviour
    /// every pre-existing caller of `raw_intern_surface` was written against.
    FailClosed,
    /// Admit a quantifier as an opaque leaf carrying the identity elaboration
    /// already gave it.
    ShareElaborated,
}

impl Executor {
    /// Bound full expanded output, including repeated override occurrences,
    /// before allocating strings. The returned conservative printer-copy-work
    /// bound uses different units; neither allowance is reset per root.
    pub(in crate::executor) fn ground_surface_render_budget(
        &self,
        roots: &[TermId],
        overrides: &ay_core::kani_compat::DetHashMap<TermId, String>,
    ) -> Option<u64> {
        use crate::executor::proof_repair::proof_trust_surgery_surface_audit::{
            expanded_render_work_bound, render_roots_have_bounded_depth,
            render_roots_have_bounded_payload,
        };
        if !crate::executor::proof_surface_syntax::surface_override_map_is_bounded(overrides)
            || !render_roots_have_bounded_depth(
                &self.ctx.terms,
                roots,
                ground::MAX_NODES,
                ground::MAX_NODE_VISITS,
            )
            || !render_roots_have_bounded_payload(
                &self.ctx.terms,
                roots,
                ground::MAX_NODES,
                ground::MAX_TOKEN_VISITS,
            )
        {
            return None;
        }
        expanded_render_work_bound(
            &self.ctx.terms,
            roots,
            overrides,
            ground::MAX_NODES,
            ground::MAX_NODE_VISITS,
            ground::MAX_TOKEN_VISITS,
        )
    }

    /// Raw-intern a surface term so it prints exactly like the problem file
    /// even where elaboration folds it. Unsupported binders and over-budget
    /// source trees fail closed before recursive elaboration.
    pub(in crate::executor) fn raw_intern_surface(
        &mut self,
        surface: &FrontendTerm,
    ) -> Option<TermId> {
        if !surface_source_is_bounded(surface) {
            return None;
        }
        self.raw_intern_surface_memoized(
            surface,
            BinderPolicy::FailClosed,
            &mut Vec::new(),
            &mut None,
        )
    }

    /// Rebuild a bounded ground BV/array source using precise ancestor work.
    /// This does not grant assumption authority or relax generic provenance.
    pub(in crate::executor) fn raw_intern_ground_bv_surface(
        &mut self,
        surface: &FrontendTerm,
    ) -> Option<TermId> {
        ground::work(surface, Some(&self.ctx))?;
        self.raw_intern_surface_memoized(
            surface,
            BinderPolicy::FailClosed,
            &mut Vec::new(),
            &mut None,
        )
    }

    /// Share exactly equal closed BV/array source through the frontend's
    /// ordinary type/declaration authenticator, under unchanged ground limits.
    /// Raw syntax and canonical typing retain separate source-indexed caches.
    pub(in crate::executor) fn raw_intern_shared_ground_memory_surface(
        &mut self,
        surface: &FrontendTerm,
    ) -> Option<TermId> {
        if self.should_abort_theory_loop() {
            return None;
        }
        let should_stop = self.make_strict_check_stop();
        let memory_limit = self.memory_limit;
        let term_memory_limit = self.term_memory_limit;
        let plan = ground_dag::Plan::new(surface, &mut self.ctx, |context| {
            should_stop()
                || ay_core::resource::work_grant_spent()
                || crate::memory::memory_exceeded(memory_limit)
                || ay_sys::process_memory_exceeded()
                || term_memory_limit
                    .is_some_and(|limit| context.terms.instance_memory_exceeded(limit))
        })?;
        if !plan.reads_array {
            return None;
        }
        self.raw_intern_surface_memoized(
            surface,
            BinderPolicy::FailClosed,
            &mut Vec::new(),
            &mut Some(plan),
        )
    }

    /// Raw-intern a surface term exactly as [`Self::raw_intern_surface`] does,
    /// except that a QUANTIFIER subterm is admitted as an opaque LEAF whose
    /// identity is the one elaboration already interned.
    ///
    /// `raw_intern_surface` fails closed on every binder and that is right for
    /// its 50-odd callers: they rebuild ground terms node-by-node, and a
    /// binder rebuilt that way would mint fresh bound variables and print
    /// unlike the source. This entry point never rebuilds a binder either. It
    /// asks the ELABORATOR for the quantifier's canonical `TermId` — the same
    /// hash-consed term the assertion itself elaborated to — and rebuilds only
    /// the propositional skeleton ABOVE it with raw constructors.
    ///
    /// That split is the whole point. The skeleton is what the folding
    /// constructors erased, so it must be rebuilt raw; the quantifier is what
    /// must keep the identity the problem gave it, because two syntactically
    /// identical authored quantifiers are ONE term and that shared identity is
    /// the fact the refutation rests on. Rebuilding the binder would destroy
    /// the very thing being proved.
    ///
    /// No new authority: `elaborate_surface_subterm` is the same best-effort
    /// provenance query proof export already uses to map a surface subterm
    /// back to its canonical term, and every caller must still round-trip the
    /// result through the exporter's own printer before it may become an
    /// `assume`.
    /// `quantifiers` collects each admitted binder leaf with the surface it
    /// came from, in first-seen order. The caller needs those pairs because
    /// elaboration alpha-renames bound variables (`n` is interned as `n_2`),
    /// so a rebuilt root prints unlike the source until each binder carries
    /// its authored spelling as a printer override.
    pub(in crate::executor) fn raw_intern_surface_sharing_quantifiers(
        &mut self,
        surface: &FrontendTerm,
        quantifiers: &mut Vec<(TermId, FrontendTerm)>,
    ) -> Option<TermId> {
        if !surface_source_is_bounded(surface) {
            return None;
        }
        self.raw_intern_surface_memoized(
            surface,
            BinderPolicy::ShareElaborated,
            quantifiers,
            &mut None,
        )
    }

    fn canonical_surface_subterm(
        &mut self,
        surface: &FrontendTerm,
        memo: &Option<ground_dag::Plan<'_>>,
    ) -> Option<TermId> {
        match memo {
            Some(plan) => plan.canonical(&self.ctx, surface),
            None => self.ctx.elaborate_surface_subterm(surface),
        }
    }

    fn raw_intern_surface_memoized<'source>(
        &mut self,
        surface: &'source FrontendTerm,
        binders: BinderPolicy,
        quantifiers: &mut Vec<(TermId, FrontendTerm)>,
        memo: &mut Option<ground_dag::Plan<'source>>,
    ) -> Option<TermId> {
        if let Some(plan) = memo.as_ref() {
            if let Some(raw) = plan.cached(&self.ctx, surface)? {
                return Some(raw);
            }
        }
        let raw = self.raw_intern_surface_prechecked(surface, binders, quantifiers, memo)?;
        if let Some(plan) = memo.as_mut() {
            plan.record(&self.ctx, surface, raw)?;
        }
        Some(raw)
    }

    fn raw_intern_surface_prechecked<'source>(
        &mut self,
        surface: &'source FrontendTerm,
        binders: BinderPolicy,
        quantifiers: &mut Vec<(TermId, FrontendTerm)>,
        memo: &mut Option<ground_dag::Plan<'source>>,
    ) -> Option<TermId> {
        let stripped = strip_frontend_annotations(surface);
        // A quantifier is admitted as a leaf ONLY under the sharing policy,
        // and only ever by asking elaboration for the term it already made.
        // `Let`, `Lambda` and `Match` stay closed under both policies: their
        // elaborations expand or desugar the source, so the rebuilt root would
        // not print as authored and the round-trip gate would refuse it
        // anyway — failing closed here says so one step earlier.
        if matches!(binders, BinderPolicy::ShareElaborated)
            && matches!(
                stripped,
                FrontendTerm::Forall(..) | FrontendTerm::Exists(..)
            )
        {
            let elaborated = self.ctx.elaborate_surface_subterm(stripped)?;
            if !quantifiers.iter().any(|(term, _)| *term == elaborated) {
                quantifiers.push((elaborated, stripped.clone()));
            }
            return Some(elaborated);
        }
        match stripped {
            FrontendTerm::Symbol(_) | FrontendTerm::Const(_) => {
                self.canonical_surface_subterm(stripped, memo)
            }
            FrontendTerm::App(head, arguments) => {
                let elaborated = self.canonical_surface_subterm(stripped, memo)?;
                // SMT-LIB has no negative numeral (2.6, section 3.1): `(- 5)`
                // over a numeral or decimal literal IS the spelling of the
                // constant `-5`, and the Alethe printer renders that constant
                // as exactly `(- 5)`. Re-interning it as a unary-minus
                // application would mint a second term for the same printed
                // text, which every proof step then has to bridge.
                // Zero is the exception: its canonical constant prints `0`
                // (or `0.0`), losing the authored `(- 0)` / `(- 0.0)` node.
                // Keep that raw application so exact-source fidelity checks
                // can preserve it even in an unreachable arithmetic branch.
                if head == "-"
                    && arguments.len() == 1
                    && matches!(
                        strip_frontend_annotations(&arguments[0]),
                        FrontendTerm::Const(_)
                    )
                    && matches!(
                        self.ctx.terms.get(elaborated),
                        ay_core::term::TermData::Const(_)
                    )
                    && !ay_core::nonlinear::is_zero_constant(&self.ctx.terms, elaborated)
                {
                    return Some(elaborated);
                }
                // Source spelling is not declaration authority. If a user
                // declaration shadows a builtin-looking head (`=`, `rem`,
                // `to_int`, ...), retain the exact private core identity that
                // elaboration selected rather than rebuilding the canonical
                // builtin with the same text.
                let declared_symbol = self
                    .authenticated_surface_application_symbol(head, elaborated)
                    .ok()?;
                let raw_arguments = arguments
                    .iter()
                    .map(|argument| {
                        self.raw_intern_surface_memoized(argument, binders, quantifiers, memo)
                    })
                    .collect::<Option<Vec<TermId>>>()?;
                let sort = self.ctx.terms.sort(elaborated).clone();
                if let Some(symbol) = declared_symbol {
                    return Some(self.ctx.terms.mk_app(symbol, raw_arguments, sort));
                }
                if head == "not" && raw_arguments.len() == 1 {
                    return Some(self.ctx.terms.mk_not_raw(raw_arguments[0]));
                }
                if head == "ite" && raw_arguments.len() == 3 {
                    return Some(self.ctx.terms.mk_ite_raw(
                        raw_arguments[0],
                        raw_arguments[1],
                        raw_arguments[2],
                    ));
                }
                Some(
                    self.ctx
                        .terms
                        .mk_app(Symbol::named(head), raw_arguments, sort),
                )
            }
            // Qualified identifier `((as <id> <sort>) arg..)` — the shape every
            // sort-polymorphic nullary constant takes (`(as seq.empty (Seq
            // Int))`, `(as const (Array ..))`). Without this arm the whole
            // enclosing assertion lost its raw re-intern (the
            // #raw-intern-head-cliff failure mode one level down), which
            // denied the substitution-bridge repair to any SEQ assertion
            // written with an explicit empty — the deductive-checks calc_basic class.
            // Elaboration is the identity authority for the qualified head
            // (it resolves the sort ascription); arguments are still rebuilt
            // raw, so this grants exactly the same authority as the `App` arm.
            FrontendTerm::QualifiedApp(_, _, arguments) => {
                let elaborated = self.canonical_surface_subterm(stripped, memo)?;
                if arguments.is_empty() {
                    // A nullary qualified constant IS its canonical form; the
                    // ascription only selected the sort.
                    return Some(elaborated);
                }
                let ay_core::term::TermData::App(symbol, _) = self.ctx.terms.get(elaborated) else {
                    return None;
                };
                let symbol = symbol.clone();
                let raw_arguments = arguments
                    .iter()
                    .map(|argument| {
                        self.raw_intern_surface_memoized(argument, binders, quantifiers, memo)
                    })
                    .collect::<Option<Vec<TermId>>>()?;
                let sort = self.ctx.terms.sort(elaborated).clone();
                let rebuilt = self
                    .ctx
                    .terms
                    .mk_app(symbol.clone(), raw_arguments.clone(), sort);
                matches!(
                    self.ctx.terms.get(rebuilt),
                    ay_core::term::TermData::App(rebuilt_symbol, rebuilt_args)
                        if *rebuilt_symbol == symbol && rebuilt_args.as_slice() == raw_arguments
                )
                .then_some(rebuilt)
            }
            FrontendTerm::IndexedApp(name, indices, arguments) => {
                let elaborated = self.canonical_surface_subterm(stripped, memo)?;
                // SMT-LIB datatype tester `((_ is C) t)`. Its index is a
                // CONSTRUCTOR SYMBOL, not a numeral, so the numeric-index path
                // below fails closed on it and the whole enclosing assertion
                // loses its raw re-intern — the #raw-intern-head-cliff failure
                // mode, one level down. That cliff is what denies a QF_DT
                // fold-to-`false` refutation any recorded argument at all
                // (`authored_conjunct_eval`): the conjunct that made the
                // assertion false IS a tester application.
                //
                // Rebuild it exactly as the elaborator names it — `is-C` from
                // the index symbol (`elaborate_indexed_app`) — and re-read the
                // result so a store that folded it fails closed. This grants
                // no new authority: the term is rebuilt node-by-node from an
                // assertion THE AUTHOR WROTE, which is the same grant every
                // other arm of this function makes.
                if name == "is" && arguments.len() == 1 {
                    let [FrontendIndex::Symbol(constructor)] = indices.as_slice() else {
                        return None;
                    };
                    let raw_argument = self.raw_intern_surface_memoized(
                        &arguments[0],
                        binders,
                        quantifiers,
                        memo,
                    )?;
                    let sort = self.ctx.terms.sort(elaborated).clone();
                    let tester = Symbol::named(format!("is-{constructor}"));
                    let rebuilt = self
                        .ctx
                        .terms
                        .mk_app(tester.clone(), vec![raw_argument], sort);
                    return matches!(
                        self.ctx.terms.get(rebuilt),
                        ay_core::term::TermData::App(symbol, args)
                            if *symbol == tester && args.as_slice() == [raw_argument]
                    )
                    .then_some(rebuilt);
                }
                if arguments.is_empty() {
                    let [FrontendIndex::Numeral(width)] = indices.as_slice() else {
                        return None;
                    };
                    let value = name.strip_prefix("bv")?;
                    if value.is_empty()
                        || !value.bytes().all(|byte| byte.is_ascii_digit())
                        || width.parse::<u32>().ok().is_none_or(|bits| bits == 0)
                    {
                        return None;
                    }
                    return Some(elaborated);
                }
                let numeric_indices = indices
                    .iter()
                    .map(|index| match index {
                        FrontendIndex::Numeral(value) => value.parse::<u32>().ok(),
                        _ => None,
                    })
                    .collect::<Option<Vec<_>>>()?;
                let raw_arguments = arguments
                    .iter()
                    .map(|argument| {
                        self.raw_intern_surface_memoized(argument, binders, quantifiers, memo)
                    })
                    .collect::<Option<Vec<_>>>()?;
                let sort = self.ctx.terms.sort(elaborated).clone();
                Some(self.ctx.terms.mk_app(
                    Symbol::indexed(name, numeric_indices),
                    raw_arguments,
                    sort,
                ))
            }
            _ => None,
        }
    }
}
