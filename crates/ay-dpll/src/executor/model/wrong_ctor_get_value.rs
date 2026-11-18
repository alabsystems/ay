// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `(get-value)` of selector applications the query never mentions, read
//! through the printed selector tables (#get-value-wrong-ctor).
//!
//! The model printer totalizes each selector
//! (`total_selector_definitions`): an argument VALUE that some committed
//! query application `(sel b)` takes on the wrong constructor gets an
//! explicit `(ite (= @p0 <value of b>) <value of (sel b)> ...)` arm. A
//! `(get-value)` term `(sel a)` that is not a query term (e.g. `(tl nil)`)
//! used to fall to the canonical default even when `a` has exactly such a
//! committed argument value, so `(get-value)` contradicted the printed
//! function (verify-1 audit `m01_c8_model`: the table said
//! `tl(nil) = (cons A nil)`, `(get-value ((tl nil)))` said `nil`).
//!
//! Selectors are functions of their argument's value, so a non-query
//! `(sel a)` is evaluated here from the value `v` of `a` (recursively, by the
//! same rule when `a` is itself such an application): the field of `v` when
//! `v` is built by a constructor owning `sel`, else exactly what the printed
//! table answers for `v`: its committed case, else its canonical default
//! (both read from [`Executor::selector_tables`], the printer's own source,
//! #get-value-wrong-ctor-congruence). Reading only the query's applications
//! here let `(tl nil)` and an internal `(tl k)` with `k = nil` print two
//! values (E13 round 6, `main_congruence_plain_check_tl_nil`). Anything else
//! (`v` unrenderable, no table — the printer withholds it — or a field this
//! reader cannot split out) declines to the ordinary path, unchanged.

use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::term::TermData;
use ay_core::TermId;

use super::Model;
use crate::executor::Executor;

/// Nesting bound of non-query selector applications.
const MAX_NESTING: u32 = 64;

impl Executor {
    /// The `(get-value)` rendering of a non-query selector application
    /// (module docs); `None` sends `term` down the ordinary path.
    pub(super) fn wrong_ctor_selector_case_value(
        &self,
        model: &Model,
        term: TermId,
    ) -> Result<Option<String>, String> {
        if self.selector_owners(term).is_none()
            || super::dt_model::BUILDING_SELECTOR_TABLES.with(std::cell::Cell::get)
        {
            return Ok(None);
        }
        let query = self
            .query_term_closure()
            .map_err(|origin| format!("selector query roots unavailable: {origin:?}"))?;
        Ok(self.non_query_selector_value(model, term, &query, MAX_NESTING, false))
    }

    /// [`Self::wrong_ctor_selector_case_value`] only where its answer is the
    /// printed table's (the argument's value is built by a constructor that
    /// does not own the selector); a projection of an owning constructor's
    /// field is left to the ordinary readers.
    pub(super) fn wrong_ctor_selector_table_value(
        &self,
        model: &Model,
        term: TermId,
    ) -> Result<Option<String>, String> {
        if self.selector_owners(term).is_none()
            || super::dt_model::BUILDING_SELECTOR_TABLES.with(std::cell::Cell::get)
        {
            return Ok(None);
        }
        let query = self
            .query_term_closure()
            .map_err(|origin| format!("selector query roots unavailable: {origin:?}"))?;
        Ok(self.non_query_selector_value(model, term, &query, MAX_NESTING, true))
    }

    /// Constructors owning the selector `term` applies, when `term` is a
    /// unary selector application.
    fn selector_owners(&self, term: TermId) -> Option<(String, TermId, Vec<(String, usize)>)> {
        let TermData::App(sym, args) = self.ctx.terms.get(term) else {
            return None;
        };
        let [arg] = args.as_slice() else {
            return None;
        };
        let sel = sym.name();
        let owners: Vec<(String, usize)> = self
            .ctx
            .ctor_selectors_iter()
            .filter_map(|(ctor, sels)| {
                sels.iter()
                    .position(|s| s == sel)
                    .map(|i| (ctor.clone(), i))
            })
            .collect();
        (!owners.is_empty()).then(|| (sel.to_string(), *arg, owners))
    }

    fn non_query_selector_value(
        &self,
        model: &Model,
        term: TermId,
        query: &HashSet<TermId>,
        fuel: u32,
        wrong_only: bool,
    ) -> Option<String> {
        if fuel == 0 || query.contains(&term) {
            return None;
        }
        let (sel, arg, owners) = self.selector_owners(term)?;
        let key = match self.non_query_selector_value(model, arg, query, fuel - 1, false) {
            Some(v) => v,
            None => self.term_value_string(model, arg).ok()?,
        };
        if key.contains('@') {
            return None;
        }
        let (head, fields) = ay_core::smtlib_application_parts(&key)?;
        if let Some((_, index)) = owners.iter().find(|(c, _)| self.dt_value_head(c) == head) {
            if wrong_only {
                return None;
            }
            return fields.get(*index).map(|f| (*f).to_string());
        }
        // The printed table's arm for `key`: its committed case, else its
        // canonical default (#get-value-wrong-ctor-congruence).
        let tables = self.selector_tables(model)?;
        let (_, info) = tables.infos.iter().find(|(n, _)| *n == sel)?;
        if info.skip
            || tables.dropped.contains(&sel)
            || self.datatype_sort_name(self.ctx.terms.sort(arg)).as_deref()
                != Some(info.dt_name.as_str())
        {
            return None;
        }
        if let Some((_, value)) = tables
            .cases
            .get(&sel)
            .and_then(|cases| cases.iter().find(|(a, _)| *a == key))
        {
            return Some(value.clone());
        }
        Some(self.canonical_default_value(&info.ret_sort))
    }

    /// `(arg, tested constructor)` when `term` is a tester application.
    pub(super) fn tester_application(&self, term: TermId) -> Option<(TermId, &str)> {
        let TermData::App(sym, args) = self.ctx.terms.get(term) else {
            return None;
        };
        let [arg] = args.as_slice() else {
            return None;
        };
        let kind = self
            .ctx
            .exact_datatype_member_info(sym.name())?
            .declaration_kind();
        if kind != ay_frontend::DeclarationKind::DatatypeTester {
            return None;
        }
        Some((*arg, sym.name().strip_prefix("is-")?))
    }

    /// The tester `tested` on `arg` whose printed value is `value`
    /// (#get-value-tester-coherence): whether `value`'s head is `tested`.
    /// A tester is a function of its argument's value, so this is the only
    /// answer coherent with the printed value of `arg`; the per-term
    /// evaluator either had none (`(error ...)` after `check-sat-assuming`)
    /// or answered for another class than the one printed (E13 round 6,
    /// `both_gv_tester_error_after_csa`, `both_tester_contradicts_value_after_csa`).
    /// `None` unless `value` is built by a constructor of `arg`'s datatype.
    pub(super) fn tester_on_printed_value(
        &self,
        arg: TermId,
        tested: &str,
        value: &str,
    ) -> Option<bool> {
        if value.contains('@') {
            return None;
        }
        let head = printed_head(value)?;
        let dt = self.datatype_sort_name(self.ctx.terms.sort(arg))?;
        let (_, ctors) = self.ctx.datatype_iter().find(|(n, _)| *n == dt)?;
        if !ctors.iter().any(|c| c == tested) {
            return None;
        }
        let built = ctors.iter().find(|c| self.dt_value_head(c) == head)?;
        Some(built == tested)
    }

    /// The arguments of an `=` / `distinct` over datatype-sorted terms.
    pub(super) fn datatype_comparison(&self, term: TermId) -> Option<&[TermId]> {
        let TermData::App(sym, args) = self.ctx.terms.get(term) else {
            return None;
        };
        if !matches!(sym.name(), "=" | "distinct") || args.len() < 2 {
            return None;
        }
        let sort = self.ctx.terms.sort(args[0]);
        self.datatype_sort_name(sort)?;
        Some(args.as_slice())
    }

    /// Whether `value` is a ground constructor term whose text is its
    /// identity: constructor applications (an `(as C S)` qualification
    /// included) over Boolean, numeral, decimal, bit-vector and string
    /// literals. Two such texts are equal exactly when the values are; an
    /// abstract element, an array or any other symbol is not admitted.
    pub(super) fn canonical_datatype_value(&self, value: &str) -> bool {
        self.canonical_value_at(value.trim(), MAX_NESTING)
    }

    fn canonical_value_at(&self, value: &str, fuel: u32) -> bool {
        if fuel == 0 || value.contains(['@', '|', '"']) {
            return false;
        }
        let Some((head, fields)) = ay_core::smtlib_application_parts(value) else {
            return false;
        };
        if fields.is_empty() && !value.starts_with('(') {
            return matches!(head, "true" | "false")
                || head.starts_with(|c: char| c.is_ascii_digit() || c == '#')
                || self.is_constructor_surface(head);
        }
        match head {
            "as" => fields.len() == 2 && self.is_constructor_surface(fields[0]),
            "-" | "/" => fields.iter().all(|f| {
                f.starts_with(|c: char| c.is_ascii_digit() || c == '(')
                    && (!f.starts_with('(') || self.canonical_value_at(f, fuel - 1))
            }),
            "_" => fields.first().is_some_and(|f| f.starts_with("bv")),
            _ => {
                self.is_constructor_surface(head)
                    && fields.iter().all(|f| self.canonical_value_at(f, fuel - 1))
            }
        }
    }

    fn is_constructor_surface(&self, name: &str) -> bool {
        self.ctx
            .datatype_iter()
            .any(|(_, ctors)| ctors.iter().any(|c| self.dt_value_head(c) == name))
    }

    /// Every term reachable from the query's assertions and authored roots.
    fn query_term_closure(&self) -> Result<HashSet<TermId>, crate::executor_types::UnknownOrigin> {
        use super::construction_owner::pay_metadata;
        use crate::executor_types::UnknownOrigin;

        fn push(
            exec: &Executor,
            stack: &mut Vec<TermId>,
            term: TermId,
        ) -> Result<(), UnknownOrigin> {
            pay_metadata(exec, 1, 0)?;
            if stack.len() == stack.capacity() {
                let before = stack.capacity();
                let target = before
                    .checked_mul(2)
                    .map(|n| n.max(8))
                    .ok_or_else(|| exec.record_evaluation_stop(UnknownOrigin::MemoryBudget))?;
                let planned = target
                    .checked_sub(before)
                    .and_then(|n| n.checked_mul(size_of::<TermId>()))
                    .ok_or_else(|| exec.record_evaluation_stop(UnknownOrigin::MemoryBudget))?;
                // Admit the entire planned growth and relocation before the
                // opaque reserve. Geometric growth bounds total ID copying.
                pay_metadata(exec, stack.len(), planned)?;
                stack
                    .try_reserve_exact(target - stack.len())
                    .map_err(|_| exec.record_evaluation_stop(UnknownOrigin::MemoryBudget))?;
                let actual = stack
                    .capacity()
                    .checked_sub(before)
                    .and_then(|n| n.checked_mul(size_of::<TermId>()))
                    .ok_or_else(|| exec.record_evaluation_stop(UnknownOrigin::MemoryBudget))?;
                pay_metadata(exec, 0, actual.saturating_sub(planned))?;
            }
            stack.push(term);
            Ok(())
        }

        // Resolve the fallible window before allocating/copying any additional
        // working roots. Reuse its admitted buffer, then borrow every input ID.
        let mut stack = self.independent_gate_query_roots()?;
        let mut seen = HashSet::default();
        for &root in &self.ctx.assertions {
            push(self, &mut stack, root)?;
        }
        while let Some(term) = stack.pop() {
            pay_metadata(self, 1, 0)?;
            if seen.contains(&term) {
                continue;
            }
            pay_metadata(self, 1, 0)?;
            if seen.len() == seen.capacity() {
                let target = seen
                    .capacity()
                    .checked_mul(2)
                    .map(|n| n.max(8))
                    .ok_or_else(|| self.record_evaluation_stop(UnknownOrigin::MemoryBudget))?;
                let before = seen.allocation_size();
                // Match the native TermStore hash-growth prepayment: controls,
                // spare capacity and rehash scans are paid before allocation.
                // This is logical storage admission, not an RSS reservation.
                let planned = before
                    .checked_mul(4)
                    .and_then(|n| n.checked_add(4096))
                    .ok_or_else(|| self.record_evaluation_stop(UnknownOrigin::MemoryBudget))?;
                let rehash = seen
                    .len()
                    .checked_add(before)
                    .ok_or_else(|| self.record_evaluation_stop(UnknownOrigin::MemoryBudget))?;
                pay_metadata(self, rehash, planned)?;
                seen.try_reserve(target - seen.len())
                    .map_err(|_| self.record_evaluation_stop(UnknownOrigin::MemoryBudget))?;
                let actual = seen
                    .allocation_size()
                    .checked_sub(before)
                    .ok_or_else(|| self.record_evaluation_stop(UnknownOrigin::MemoryBudget))?;
                pay_metadata(self, 0, actual.saturating_sub(planned))?;
            }
            seen.insert(term);
            // Same children as TermStore::children, borrowed so the original
            // stop/ledger is checked before each worklist copy. Triggers remain
            // outside the native generic child relation.
            match self.ctx.terms.get(term) {
                TermData::Const(_) | TermData::Var(_, _) => {}
                TermData::App(_, args) => {
                    for &child in args {
                        push(self, &mut stack, child)?;
                    }
                }
                TermData::Let(bindings, body) => {
                    for (_, child) in bindings {
                        push(self, &mut stack, *child)?;
                    }
                    push(self, &mut stack, *body)?;
                }
                TermData::Not(body)
                | TermData::Forall(_, body, _)
                | TermData::Exists(_, body, _) => push(self, &mut stack, *body)?,
                TermData::Ite(condition, then_term, else_term) => {
                    push(self, &mut stack, *condition)?;
                    push(self, &mut stack, *then_term)?;
                    push(self, &mut stack, *else_term)?;
                }
                // The external enum is non-exhaustive. An unknown child
                // relation is unavailable, never an empty/leaf relation.
                _ => return Err(self.record_evaluation_stop(UnknownOrigin::IncompleteSolverLane)),
            }
        }
        pay_metadata(self, 0, 0)?;
        Ok(seen)
    }
}

/// The constructor token a rendered datatype value is built by: the head of
/// an application, a bare nullary constructor, or the name inside an
/// `(as C S)` qualification, as `ay_core::smtlib_application_parts` splits
/// them.
fn printed_head(value: &str) -> Option<&str> {
    let (head, fields) = ay_core::smtlib_application_parts(value)?;
    if head == "as" {
        return match fields.first() {
            Some(inner) => printed_head(inner),
            None => None,
        };
    }
    Some(head)
}

#[cfg(test)]
mod tests {
    #[test]
    fn query_closure_polls_original_ledger_through_shared_dag_and_keeps_source() {
        use crate::executor::Executor;
        use crate::executor_types::UnknownOrigin;
        let mut exec = Executor::new();
        let leaf = exec.ctx.terms.mk_var("leaf", ay_core::Sort::Bool);
        let mut root = leaf;
        for _ in 0..64 {
            root = exec.ctx.terms.mk_app(
                ay_core::Symbol::named("and"),
                vec![root, root],
                ay_core::Sort::Bool,
            );
        }
        exec.ctx.assertions.push(root);
        let terms = exec.ctx.terms.len();
        {
            let _scope =
                super::super::recovery_admission::RecoveryScope::enter(&exec, 32, usize::MAX)
                    .unwrap();
            assert_eq!(
                exec.query_term_closure(),
                Err(UnknownOrigin::DeterministicResourceBudget)
            );
            assert_eq!(
                exec.query_term_closure(),
                Err(UnknownOrigin::DeterministicResourceBudget)
            );
            assert_eq!(exec.ctx.assertions, [root]);
            assert_eq!(exec.ctx.terms.len(), terms);
        }
        let _fresh = exec.begin_external_evaluation_read();
        let closure = exec.query_term_closure().unwrap();
        assert_eq!(closure.len(), 65);
        assert!(closure.contains(&leaf));
        assert!(closure.contains(&root));
    }
    #[test]
    fn wide_query_frontier_keeps_amortized_copying_with_original_work() {
        use crate::executor::Executor;
        let mut exec = Executor::new();
        let leaves: Vec<_> = (0..512)
            .map(|index| {
                exec.ctx
                    .terms
                    .mk_var(format!("wide_{index}"), ay_core::Sort::Bool)
            })
            .collect();
        let root =
            exec.ctx
                .terms
                .mk_app(ay_core::Symbol::named("and"), &leaves, ay_core::Sort::Bool);
        exec.ctx.assertions.push(root);
        let _scope = super::super::recovery_admission::RecoveryScope::enter(
            &exec,
            64 * leaves.len(),
            usize::MAX,
        )
        .unwrap();
        let closure = exec.query_term_closure().unwrap();
        assert_eq!(closure.len(), leaves.len() + 1);
        assert!(leaves.iter().all(|leaf| closure.contains(leaf)));
        assert!(closure.contains(&root));
        assert_eq!(exec.ctx.assertions, [root]);
    }
}
