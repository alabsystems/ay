// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Binder separation for native quantifier and lambda construction.
//!
//! Option C of the development design notes:
//! a native binder never shares its term identity with a declared constant.
//!
//! AY binds by NAME and hash-conses `Var` nodes, so `try_forall(&[c], body)`
//! over a constant `c` from `try_declare_const` used to make ONE `TermId` both
//! the binder and a free constant of the problem. SMT-LIB text cannot produce
//! that shape — the elaborator gives every `forall`/`exists`/`lambda` binder a
//! fresh `<name>_<id>` variable — but ay-dpll's E-matching classifies boundness
//! by `TermId`, so the shared identity made the incremental ground-term index
//! and a full rebuild disagree (canary LI-1/LI-2) and made a refutation depend
//! on assertion order.
//!
//! Every native binder constructor therefore renames such a binder to a fresh
//! TWIN variable, minted exactly as the elaborator mints binders, and
//! substitutes it for the binder's occurrences in the body and the triggers:
//! precisely the occurrences the quantifier bound under name binding, so the
//! result is alpha-equivalent to what the caller wrote. Occurrences inside a
//! nested binder of the same name stay with that binder; the constant's
//! occurrences outside the quantifier are untouched, and it keeps its place in
//! declarations, models and unsat cores.
//!
//! API-VISIBLE CHANGE: a caller that inspects the returned quantifier or lambda
//! (`quantifier_bound_vars`, `term_children`, `format_term`, proofs) sees the
//! twin's name (`x_17`), not the constant's. A binder that is not a declared
//! constant — `fresh_var`, the documented way to build one — is untouched.
//!
//! Each constant has one canonical twin, reused across quantifiers, so building
//! the same quantifier twice still yields one hash-consed term. A one-off twin
//! is minted instead whenever the canonical twin's name already occurs in the
//! body, the triggers or the binder list, so the renaming never captures.
//!
//! The Z3-compatible C API (`ay-ffi`) keeps binder identity through the
//! `z3_compat_*` friend constructors below: its public contract
//! (`Z3_get_quantifier_body` over the bound constants, bound-name metadata,
//! cross-context translation, z3 printing parity) is defined over the constant
//! it was handed. Separating there needs a public view of the twin first.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::{TermData, TermEntryStamp};
use ay_core::{Sort, TermId};

use super::super::types::{SolverError, Term, TermArenaStamp};
use super::super::Solver;
use super::binder_rename::{names_in_scope, var_name, Rename};
use super::quantifiers::contains_bound_var;
use super::HashSet;

/// The canonical twin of each declared constant, for one term-arena generation
/// (a full reset starts a new one), with the birth stamp proving the slot still
/// holds that twin.
#[derive(Default)]
pub(in crate::api) struct BinderTwins {
    pub(in crate::api) arena: Option<TermArenaStamp>,
    pub(in crate::api) twins: HashMap<TermId, (TermId, TermEntryStamp)>,
}

/// Which quantifier a native constructor builds, and the operation name its
/// errors report.
#[derive(Clone, Copy)]
pub(super) struct QuantifierSpec {
    pub(super) is_forall: bool,
    pub(super) operation: &'static str,
}

impl Solver {
    /// Shared body of every native `forall`/`exists` constructor.
    ///
    /// Validates exactly as each constructor always has (body sort, one `Var`
    /// per binder, no duplicate, every application trigger mentions a binder),
    /// then separates declared-constant binders when `separate` is set.
    pub(super) fn try_quantifier(
        &mut self,
        spec: QuantifierSpec,
        vars: &[Term],
        body: Term,
        triggers: &[&[Term]],
        separate: bool,
    ) -> Result<Term, SolverError> {
        let operation = spec.operation;
        let mut body_id = self.resolve_term(operation, body)?;
        let mut var_ids = self.resolve_terms(operation, vars)?;
        let trigger_ids = triggers
            .iter()
            .map(|multi| self.resolve_terms(operation, multi))
            .collect::<Result<Vec<_>, _>>()?;
        let body_sort = self.terms().sort(body_id).clone();
        if body_sort != Sort::Bool {
            return Err(SolverError::SortMismatch {
                operation,
                expected: "Bool",
                got: vec![body_sort],
            });
        }

        let mut seen = HashSet::default();
        let mut bound_names: HashSet<String> = HashSet::default();
        for &var_id in &var_ids {
            let name = match self.terms().get(var_id) {
                TermData::Var(name, _) => name.clone(),
                other => {
                    return Err(SolverError::InvalidArgument {
                        operation,
                        message: format!("expected variable term, got {other:?}"),
                    });
                }
            };
            if !seen.insert(var_id) {
                return Err(SolverError::InvalidArgument {
                    operation,
                    message: format!("duplicate bound variable: {name}"),
                });
            }
            bound_names.insert(name);
        }

        let mut core_triggers: Vec<Vec<TermId>> = Vec::new();
        for multi in trigger_ids {
            let mut multi_terms: Vec<TermId> = Vec::new();
            for term_id in multi {
                if !matches!(self.terms().get(term_id), TermData::App(_, _)) {
                    continue;
                }
                if !contains_bound_var(self.terms(), term_id, &bound_names) {
                    return Err(SolverError::InvalidTrigger {
                        operation,
                        message: "trigger must contain at least one bound variable".to_string(),
                    });
                }
                multi_terms.push(term_id);
            }
            if !multi_terms.is_empty() {
                core_triggers.push(multi_terms);
            }
        }

        if separate {
            self.separate_declared_binders(&mut var_ids, &mut body_id, &mut core_triggers);
        }
        let core_vars: Vec<(String, Sort)> = var_ids
            .iter()
            .map(|&var| (var_name(self.terms(), var), self.terms().sort(var).clone()))
            .collect();
        let result = if spec.is_forall {
            self.terms_mut()
                .mk_forall_with_triggers(core_vars, body_id, core_triggers)
        } else {
            self.terms_mut()
                .mk_exists_with_triggers(core_vars, body_id, core_triggers)
        };
        self.index_quantifier_for_alpha_sharing(result);
        Ok(self.wrap_term(result))
    }

    /// Build the single-variable lambda array `(lambda ((x T)) body)` with
    /// bound variable `var` and `body`, i.e. an array with
    /// `select(arr, i) = body[x := i]`. Multi-variable lambdas are curried in
    /// the FFI layer. Exposes `TermArena::mk_lambda_array`. A declared-constant
    /// `var` is separated like a quantifier binder (see the module docs).
    #[must_use]
    pub fn lambda_array(&mut self, var: Term, body: Term) -> Term {
        self.bind_lambda_array(var, body, true)
    }

    /// [`Self::lambda_array`] for the Z3-compatible C API, which keeps the
    /// binder's identity (see the module docs). Backs `Z3_mk_lambda` /
    /// `Z3_mk_lambda_const`.
    #[cfg(feature = "z3-compat-internals")]
    #[doc(hidden)]
    #[must_use]
    pub fn z3_compat_lambda_array(&mut self, var: Term, body: Term) -> Term {
        self.bind_lambda_array(var, body, false)
    }

    /// A native `forall`/`exists` for the Z3-compatible C API, which keeps the
    /// binders' identity (see the module docs). `triggers: None` reports the
    /// plain constructor's operation name, `Some` the `_with_triggers` one.
    ///
    /// # Errors
    ///
    /// Exactly the errors of the public constructor it mirrors.
    #[cfg(feature = "z3-compat-internals")]
    #[doc(hidden)]
    pub fn z3_compat_quantifier(
        &mut self,
        is_forall: bool,
        vars: &[Term],
        body: Term,
        triggers: Option<&[&[Term]]>,
    ) -> Result<Term, SolverError> {
        let operation = match (is_forall, triggers.is_some()) {
            (true, false) => "forall",
            (true, true) => "forall_with_triggers",
            (false, false) => "exists",
            (false, true) => "exists_with_triggers",
        };
        let spec = QuantifierSpec {
            is_forall,
            operation,
        };
        self.try_quantifier(spec, vars, body, triggers.unwrap_or(&[]), false)
    }

    fn bind_lambda_array(&mut self, var: Term, body: Term, separate: bool) -> Term {
        let mut binder = [self.require_term("lambda_array", var)];
        let mut body_id = self.require_term("lambda_array", body);
        if separate && matches!(self.terms().get(binder[0]), TermData::Var(_, _)) {
            self.separate_declared_binders(&mut binder, &mut body_id, &mut []);
        }
        let result = self.terms_mut().mk_lambda_array(binder[0], body_id);
        self.wrap_term(result)
    }

    /// Register a natively built quantifier in the elaborator's
    /// alpha-equivalence sharing index.
    ///
    /// A binder's `TermId` is NOT canonical under alpha-renaming — every
    /// occurrence mints globally unique binder names — so re-elaborating a
    /// faithful SMT-LIB spelling of a natively built quantifier would
    /// otherwise produce an unrelated alpha-variant. That is what made
    /// [`Self::try_assert_term_with_source`] refuse every binder-carrying
    /// assertion. Indexing only: the caller keeps the term it just built.
    fn index_quantifier_for_alpha_sharing(&mut self, quantifier: TermId) {
        self.executor
            .context_mut_internal()
            .index_quantifier_for_alpha_sharing(quantifier);
    }

    /// Rename every declared-constant binder in `var_ids` to its twin in
    /// `body` and `triggers` (see the module docs). A binder whose renaming
    /// meets a term kind the walk does not know is left as written: that is the
    /// pre-separation shape, still sound, merely unseparated.
    fn separate_declared_binders(
        &mut self,
        var_ids: &mut [TermId],
        body: &mut TermId,
        triggers: &mut [Vec<TermId>],
    ) {
        for index in 0..var_ids.len() {
            let binder = var_ids[index];
            if !self.binder_is_declared_constant(binder) {
                continue;
            }
            let Some(occupied) = names_in_scope(self.terms(), var_ids, *body, triggers) else {
                continue;
            };
            let twin = self.binder_twin(binder, &occupied);
            let binder_name = var_name(self.terms(), binder);
            let rename = Rename {
                from: binder,
                from_name: &binder_name,
                to: twin,
            };
            let mut cache = HashMap::default();
            let terms = self.terms_mut();
            let Some(new_body) = rename.apply(terms, *body, &mut cache) else {
                continue;
            };
            let new_triggers = triggers
                .iter()
                .map(|multi| {
                    multi
                        .iter()
                        .map(|&pattern| rename.apply(terms, pattern, &mut cache))
                        .collect::<Option<Vec<_>>>()
                })
                .collect::<Option<Vec<_>>>();
            let Some(new_triggers) = new_triggers else {
                continue;
            };
            *body = new_body;
            for (slot, renamed) in triggers.iter_mut().zip(new_triggers) {
                *slot = renamed;
            }
            var_ids[index] = twin;
        }
    }

    /// A declared constant: registered through the native API, or bound as a
    /// constant in the frontend symbol table (an SMT-LIB declaration executed
    /// on this solver). Decided from declarations alone, so the separation of
    /// a quantifier never depends on which assertions happen to precede it.
    fn binder_is_declared_constant(&self, binder: TermId) -> bool {
        if self.var_sorts.contains_key(&binder) {
            return true;
        }
        let TermData::Var(name, _) = self.terms().get(binder) else {
            return false;
        };
        self.executor
            .context()
            .symbol_info_by_identity(name)
            .is_some_and(|info| info.term == Some(binder))
    }

    /// The canonical twin of `binder`, or a one-off twin when the canonical
    /// one's name is `occupied` in the quantifier under construction.
    fn binder_twin(&mut self, binder: TermId, occupied: &HashSet<String>) -> TermId {
        if self.binder_twins.arena != Some(self.term_arena) {
            self.binder_twins = BinderTwins {
                arena: Some(self.term_arena),
                twins: HashMap::default(),
            };
        }
        if let Some(&(twin, stamp)) = self.binder_twins.twins.get(&binder) {
            if self.terms().entry_stamp(twin) == Some(stamp) {
                if !occupied.contains(&var_name(self.terms(), twin)) {
                    return twin;
                }
                return self.mint_twin(binder, occupied);
            }
        }
        let twin = self.mint_twin(binder, occupied);
        if let Some(stamp) = self.terms().entry_stamp(twin) {
            self.binder_twins.twins.insert(binder, (twin, stamp));
        }
        twin
    }

    /// Mint `<name>_<id>` exactly as the SMT-LIB elaborator mints a binder,
    /// skipping any spelling already occupied in the quantifier.
    fn mint_twin(&mut self, binder: TermId, occupied: &HashSet<String>) -> TermId {
        let name = var_name(self.terms(), binder);
        let sort = self.terms().sort(binder).clone();
        loop {
            let twin = self.terms_mut().mk_fresh_var(&name, sort.clone());
            if !occupied.contains(&var_name(self.terms(), twin)) {
                return twin;
            }
        }
    }
}
