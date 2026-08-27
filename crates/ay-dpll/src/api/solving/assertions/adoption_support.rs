// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Definitional-forall adoption policy and exact-head recognition.

use ay_core::term::Symbol;
use ay_core::{Sort, TermData, TermId};

use crate::api::Solver;

impl Solver {
    /// Exclude `name` (the caller-visible declaration name) from
    /// definitional-forall macro adoption for the rest of this session.
    ///
    /// Adoption rewrites every later application of the head into its
    /// definition body. That is the right default for decidability, but it
    /// deletes the function applications an E-matching-only (`mark_no_mbqi`)
    /// axiom uses as its triggers AND the ground witness applications those
    /// triggers are meant to match — the Hilbert-`choose` discipline (fire
    /// only on a genuine witness) then never fires and a provable obligation
    /// degrades to `quantifier-unhandled`. Only the embedder knows which
    /// heads participate in such axioms, and it learns this before asserting
    /// the definition, so suppression is its call. Suppressing costs only
    /// the adoption OPTIMIZATION: the definitional `forall` stays asserted
    /// verbatim and remains fully authoritative.
    pub fn suppress_definitional_adoption(&mut self, name: &str) {
        self.adoption_suppressed_funs.insert(name.to_string());
    }

    /// Whether `assertion` is a definitional `forall` whose head function was
    /// suppressed via [`Self::suppress_definitional_adoption`]. Shape checks
    /// are deliberately loose here (either equality side with a matching
    /// registered core name counts): a suppressed head must never be adopted,
    /// and a false positive merely declines an optimization.
    pub(super) fn definitional_head_is_adoption_suppressed(&self, assertion: TermId) -> bool {
        let TermData::Forall(_, body, _) = self.terms().get(assertion) else {
            return false;
        };
        let TermData::App(Symbol::Named(eq), sides) = self.terms().get(*body) else {
            return false;
        };
        if eq != "=" || sides.len() != 2 {
            return false;
        }
        sides.iter().any(|&side| {
            let TermData::App(Symbol::Named(core_name), _) = self.terms().get(side) else {
                return false;
            };
            self.adoption_suppressed_funs.iter().any(|suppressed| {
                suppressed == core_name
                    || self
                        .native_fun_signatures
                        .get(suppressed)
                        .is_some_and(|registration| &registration.core_name == core_name)
            })
        })
    }

    /// Recognize one exact binder-ordered application of a registered native
    /// function as the possible head of a definitional forall.
    ///
    /// Candidacy is restricted to user declarations. A theory builtin is
    /// already totally interpreted, while two registered heads remain
    /// genuinely ambiguous and are rejected by the caller.
    pub(super) fn exact_native_definitional_head(
        &self,
        candidate: TermId,
        vars: &[(String, Sort)],
    ) -> Option<(String, Vec<TermId>, TermId)> {
        let TermData::App(Symbol::Named(name), args) = self.terms().get(candidate) else {
            return None;
        };
        if !self.native_fun_signatures.contains_key(name) {
            return None;
        }
        if args.len() != vars.len()
            || args
                .iter()
                .zip(vars.iter())
                .any(|(&arg, (var_name, sort))| {
                    !matches!(
                        self.terms().get(arg),
                        TermData::Var(name, _) if name == var_name
                    ) || self.terms().sort(arg) != sort
                })
        {
            return None;
        }
        Some((name.clone(), args.clone(), candidate))
    }
}
