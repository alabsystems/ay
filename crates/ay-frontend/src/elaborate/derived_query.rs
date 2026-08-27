// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Rebuilding a [`Context`]'s term arena around one DERIVED query.
//!
//! # Why this exists
//!
//! An internal re-discharge (see `Executor::reconfirms_unsat_within`) clones the
//! whole solving context so a fresh executor re-decides an authored problem with
//! the same declarations, logic and options the original solve had. The clone is
//! deliberate and stays: a thin re-translate of the roots alone leaves deep
//! nested-`ite` obligations `Unknown` (that is the documented reason `Context`
//! is `Clone` at all).
//!
//! What the clone must NOT carry is the outer solve's SCRATCH. Proof-planning
//! bridges hash-cons denormalised scaffolding straight into the live arena —
//! `(not (= x x))`, `(= t true)` — and nothing ever asserts it. Those nodes are
//! not part of the derived query, yet whole-store scans in the nested solve see
//! them and can turn a 0.26s re-solve into a 28s one that misses its deadline.
//! A slower nested solve is not a wrong answer, but it silently converts a
//! provable obligation into `unknown`, which is what a caller reads as "not
//! established".
//!
//! # What this does
//!
//! [`Context::compact_terms_for_derived_query`] runs the existing mark-compact
//! collector ([`TermStore::mark_and_compact`]) over the cloned arena, rooted at
//! EVERY `TermId` the context itself still names. Terms the context cannot name
//! are unreachable scratch and are reclaimed; every term it CAN name survives
//! with byte-identical [`TermData`], only relabelled.
//!
//! # How terms are identified — NOT by numeric index across stores
//!
//! There is exactly one term arena involved. `mark_and_compact` relabels the
//! arena IN PLACE and returns a [`RemapTable`] built during that same
//! relabelling, so a stale id is translated by the table that produced its
//! successor — never by assuming a slot number means the same thing in two
//! different stores. Nothing here compares an id against a length, and nothing
//! here transplants an id from one store into another. A translation that the
//! table cannot supply fails the whole rebuild closed (see the `false` return),
//! so a partially-remapped context can never be handed to a solver.
//!
//! # Exhaustiveness
//!
//! [`Context::walk_term_ids`] destructures `Context` with NO `..` rest pattern.
//! A new field is therefore a compile error here until someone decides whether
//! it carries a `TermId`. That is the property that makes "every holder is a
//! root" checkable rather than aspirational — the contract `mark_and_compact`
//! states in its safety section.

use ay_core::TermId;

use super::public_sorts::{PublicAssertionMetadata, PublicTermMetadata};
use super::{AuthoredAssertion, Context, ScopeFrame, ScopedSymbolState, SymbolInfo};

impl Context {
    /// Reclaim every arena term this context can no longer name, then relabel
    /// the ids it keeps.
    ///
    /// Call this on a context that is ALREADY set up for the derived query —
    /// in particular with [`Context::assertions`] already replaced by the
    /// derived roots, so those roots are seen as roots here.
    ///
    /// Returns `false` if any held id could not be translated. The caller must
    /// then abandon the context: it is fail-closed, never "mostly remapped".
    #[doc(hidden)]
    #[must_use]
    pub fn compact_terms_for_derived_query(&mut self) -> bool {
        let mut roots: Vec<TermId> = Vec::new();
        let collected = self.walk_term_ids(&mut |id| {
            roots.push(*id);
            true
        });
        debug_assert!(collected, "the collecting walk cannot fail");
        if !collected {
            return false;
        }
        let table = self.terms.mark_and_compact(&roots);
        self.walk_term_ids(&mut |id| match table.get(*id) {
            Some(new_id) => {
                *id = new_id;
                true
            }
            None => false,
        })
    }

    /// Apply `f` to every [`TermId`] stored anywhere in this context.
    ///
    /// Returns `false` as soon as any application reports failure, after
    /// visiting the rest (the caller discards the context either way, and a
    /// partial walk would make the failure position observable).
    ///
    /// The destructuring below is deliberately exhaustive — see the module
    /// docs.
    #[allow(clippy::too_many_lines)]
    fn walk_term_ids(&mut self, f: &mut dyn FnMut(&mut TermId) -> bool) -> bool {
        let Context {
            context_identity: _,
            source_revision: _,
            terms: _,
            symbols,
            internal_symbols: _,
            overloaded_symbols,
            next_overload_identity: _,
            declaration_core_identities_used: _,
            next_sort_identity: _,
            sort_core_identities_used: _,
            nominal_sort_surfaces: _,
            sort_defs: _,
            public_sort_defs: _,
            parametric_sort_defs: _,
            sort_parameters: _,
            polymorphic_declarations: _,
            instantiating_polymorphic_declaration: _,
            // Schematic assertions are un-elaborated parser ASTs
            // (`crate::command::Term`), which hold no `TermId`.
            polymorphic_assertions: _,
            authored_assertions,
            materialized_polymorphic_assertions: _,
            polymorphic_instantiation_complete: _,
            elaborating_polymorphic_instance: _,
            expanding_sort_synonyms: _,
            // `FunctionDefinition` is (binders, result sort, parser AST).
            fun_defs: _,
            adopted_macro_interps,
            adopted_macro_declaration_ids: _,
            #[cfg(test)]
                fail_next_assert_after_macro_adoption: _,
            recursive_fun_names: _,
            datatypes: _,
            live_datatype_carriers: _,
            monomorphic_datatype_decs: _,
            constructors: _,
            ctor_selectors: _,
            ctor_selector_info: _,
            nullary_ctor_terms,
            datatype_member_symbols,
            parametric_datatypes: _,
            parametric_datatype_ids: _,
            parametric_instance_args: _,
            parametric_instance_sorts: _,
            dt_internal_surface: _,
            dt_field_surface,
            logic: _,
            strict_logic_compliance: _,
            logic_set_by_command: _,
            assertions,
            assertion_finite_set_metadata,
            // Parsed assertion ASTs carry no `TermId`.
            assertions_parsed: _,
            retain_parsed_assertions: _,
            objectives,
            objective_finite_set_metadata,
            soft_constraints,
            soft_finite_set_metadata,
            scopes,
            scope_commands_used: _,
            check_sat_commands: _,
            native_global_declaration: _,
            options: _,
            numeral_as_real: _,
            int_real_coercions: _,
            named_terms,
            // Retained as authored SPELLINGS precisely so no `TermId` is stored.
            z3_debug_exprs: _,
            fun_expansion_depth: _,
            multivar_lambda_curry_allowed: _,
            uses_multiset: _,
            uses_set: _,
            special_relations: _,
            lenient_sort_coercions: _,
            finite_set_typing_mode: _,
        } = self;

        let mut ok = true;

        for term in assertions.iter_mut() {
            ok &= f(term);
        }
        for objective in objectives.iter_mut() {
            ok &= f(&mut objective.term);
        }
        for soft in soft_constraints.iter_mut() {
            ok &= f(&mut soft.term);
        }
        for term in named_terms.values_mut() {
            ok &= f(term);
        }
        for term in nullary_ctor_terms.values_mut() {
            ok &= f(term);
        }
        for (_, body) in adopted_macro_interps.values_mut() {
            ok &= f(body);
        }
        for authored in authored_assertions.iter_mut() {
            match authored {
                AuthoredAssertion::Concrete { term, .. } => ok &= f(term),
                AuthoredAssertion::Schematic(_) => {}
            }
        }
        for info in symbols.values_mut() {
            ok &= walk_symbol_info(info, f);
        }
        for infos in overloaded_symbols.values_mut() {
            for info in infos.iter_mut() {
                ok &= walk_symbol_info(info, f);
            }
        }
        for info in datatype_member_symbols.values_mut() {
            ok &= walk_symbol_info(info, f);
        }
        for scope in scopes.iter_mut() {
            ok &= walk_scope_frame(scope, f);
        }
        // Public finite-set metadata carries the LOWERED engine term for each
        // source occurrence, so these three vectors are term holders even though
        // nothing about their names says so. Missing them was a real
        // out-of-bounds in an earlier draft of this patch, which is why the
        // helpers below destructure exhaustively rather than reach for a field.
        for meta in assertion_finite_set_metadata
            .iter_mut()
            .chain(objective_finite_set_metadata.iter_mut())
            .chain(soft_finite_set_metadata.iter_mut())
        {
            ok &= walk_public_assertion_metadata(meta, f);
        }
        // Keyed BY `TermId`, so the map is rebuilt rather than walked in place.
        // A key the callback rejects drops its row: the field is export-time
        // RENDERING provenance, and a row that cannot name its term must not
        // survive as a claim about some other term.
        if !dt_field_surface.is_empty() {
            let old = std::mem::take(dt_field_surface);
            for (mut key, surface) in old {
                if f(&mut key) {
                    dt_field_surface.insert(key, surface);
                } else {
                    ok = false;
                }
            }
        }

        ok
    }
}

/// Every `TermId` inside one symbol-table row.
///
/// Exhaustive destructure: a new [`SymbolInfo`] field is a compile error here.
fn walk_symbol_info(info: &mut SymbolInfo, f: &mut dyn FnMut(&mut TermId) -> bool) -> bool {
    let SymbolInfo {
        term,
        sort: _,
        arg_sorts: _,
        public_sort: _,
        public_arg_sorts: _,
        internal_name: _,
        declaration_id: _,
        declaration_kind: _,
        binding_origin: _,
    } = info;
    match term {
        Some(term) => f(term),
        None => true,
    }
}

/// Every `TermId` inside one push/pop scope frame.
///
/// Exhaustive destructure: a new [`ScopeFrame`] field is a compile error here.
fn walk_scope_frame(scope: &mut ScopeFrame, f: &mut dyn FnMut(&mut TermId) -> bool) -> bool {
    let ScopeFrame {
        symbols,
        assertion_count: _,
        objective_count: _,
        soft_constraint_count: _,
        // Scope bookkeeping records NAMES to un-bind on pop, not terms.
        named_terms: _,
        datatypes: _,
        constructors: _,
        sort_defs: _,
        fun_defs: _,
        parametric_datatypes: _,
        polymorphic_assertion_count: _,
        authored_assertion_count: _,
        polymorphic_declarations: _,
    } = scope;
    let mut ok = true;
    for state in symbols.values_mut() {
        let ScopedSymbolState {
            name: _,
            primary,
            overloads,
            was_internal: _,
        } = state;
        if let Some(info) = primary.as_mut() {
            ok &= walk_symbol_info(info, f);
        }
        if let Some(infos) = overloads.as_mut() {
            for info in infos.iter_mut() {
                ok &= walk_symbol_info(info, f);
            }
        }
    }
    ok
}

/// Every `TermId` inside one assertion's public finite-set metadata.
///
/// The occurrence tree mirrors source nesting, so it is walked with an explicit
/// stack rather than by recursion.
fn walk_public_assertion_metadata(
    meta: &mut PublicAssertionMetadata,
    f: &mut dyn FnMut(&mut TermId) -> bool,
) -> bool {
    let PublicAssertionMetadata {
        finite_sets: _,
        root,
    } = meta;
    let Some(root) = root.as_mut() else {
        return true;
    };
    let mut ok = true;
    let mut stack: Vec<&mut PublicTermMetadata> = vec![root];
    while let Some(node) = stack.pop() {
        let PublicTermMetadata {
            engine_term,
            public_sort: _,
            finite_set_op: _,
            public_bound_sorts: _,
            arguments,
        } = node;
        ok &= f(engine_term);
        stack.extend(arguments.iter_mut());
    }
    ok
}

#[cfg(test)]
#[allow(clippy::panic, clippy::expect_used)]
mod tests {
    use ay_core::term::{Symbol, TermData};
    use ay_core::{Sort, TermId, TermStore};

    use super::Context;

    /// Lockstep structural comparison of two term DAGs living in two different
    /// stores.
    ///
    /// This is the identity relation the rebuild has to preserve, written out so
    /// the tests below assert it rather than assert an id. It never compares a
    /// slot number across stores: it compares node KIND, symbol name, sort,
    /// constant value and binder spelling, and recurses on children in lockstep,
    /// memoizing on the visited pair.
    fn structurally_equal(
        left: &TermStore,
        left_id: TermId,
        right: &TermStore,
        right_id: TermId,
        seen: &mut Vec<(TermId, TermId)>,
    ) -> bool {
        if seen.contains(&(left_id, right_id)) {
            return true;
        }
        seen.push((left_id, right_id));
        if left.sort(left_id) != right.sort(right_id) {
            return false;
        }
        match (left.get(left_id), right.get(right_id)) {
            (TermData::Const(a), TermData::Const(b)) => a == b,
            (TermData::Var(a, _), TermData::Var(b, _)) => a == b,
            (TermData::App(a_sym, a_args), TermData::App(b_sym, b_args)) => {
                a_sym.name() == b_sym.name()
                    && a_args.len() == b_args.len()
                    && a_args
                        .clone()
                        .into_iter()
                        .zip(b_args.clone())
                        .all(|(a, b)| structurally_equal(left, a, right, b, seen))
            }
            (TermData::Not(a), TermData::Not(b)) => structurally_equal(left, *a, right, *b, seen),
            (TermData::Ite(a_c, a_t, a_e), TermData::Ite(b_c, b_t, b_e)) => {
                structurally_equal(left, *a_c, right, *b_c, seen)
                    && structurally_equal(left, *a_t, right, *b_t, seen)
                    && structurally_equal(left, *a_e, right, *b_e, seen)
            }
            _ => false,
        }
    }

    /// The rebuild reclaims what the context cannot name and keeps, verbatim,
    /// what it can.
    #[test]
    fn derived_query_rebuild_drops_scratch_and_preserves_the_query() {
        let mut ctx = Context::new();
        let x = ctx.terms.mk_var("rebuild_x", Sort::Bool);
        let y = ctx.terms.mk_var("rebuild_y", Sort::Bool);
        let not_y = ctx.terms.mk_not_raw(y);
        ctx.assertions = vec![x, not_y];

        // Scratch of the shape a proof-planning bridge hash-conses into the live
        // arena: nodes nothing ever asserts and nothing ever names.
        for index in 0..64 {
            let scratch = ctx.terms.mk_app(
                Symbol::named(format!("scratch_{index}")),
                [x, not_y],
                Sort::Bool,
            );
            let _negated = ctx.terms.mk_not_raw(scratch);
        }
        let before = ctx.terms.clone();
        let before_len = ctx.terms.len();

        assert!(ctx.compact_terms_for_derived_query());

        assert!(
            ctx.terms.len() + 100 < before_len,
            "the 128 scratch nodes must be reclaimed: {before_len} -> {}",
            ctx.terms.len()
        );
        assert_eq!(ctx.assertions.len(), 2);
        let mut seen = Vec::new();
        assert!(structurally_equal(
            &before,
            x,
            &ctx.terms,
            ctx.assertions[0],
            &mut seen
        ));
        let mut seen = Vec::new();
        assert!(structurally_equal(
            &before,
            not_y,
            &ctx.terms,
            ctx.assertions[1],
            &mut seen
        ));
    }

    /// A declared-but-unasserted constant is context state, not scratch, so it
    /// must survive with its symbol-table row still pointing at it.
    #[test]
    fn derived_query_rebuild_keeps_a_declared_but_unused_constant() {
        let mut ctx = Context::new();
        let used = ctx.terms.mk_var("kept_used", Sort::Bool);
        let unused = ctx.terms.mk_var("kept_unused", Sort::Int);
        ctx.assertions = vec![used];
        let before = ctx.terms.clone();

        assert!(ctx.compact_terms_for_derived_query());

        let relabelled = ctx
            .terms
            .find_var("kept_unused")
            .expect("a declared constant must survive the rebuild");
        let mut seen = Vec::new();
        assert!(structurally_equal(
            &before, unused, &ctx.terms, relabelled, &mut seen
        ));
    }
}
