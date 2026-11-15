// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Quantifier proxies for the expansion certificate's ground probe (plan
//! §4.1 steps 2 and 4).
//!
//! The probe decides only quantifier-free assertions, so every MAXIMAL
//! quantified subterm `Q` of the certificate's clause set is replaced by a
//! fresh Boolean constant `p_Q` (one per `TermId`, so a quantifier shared by
//! two lemmas stays one atom). The probe's proof is then RENAMED back: every
//! term it mentions has each `p_Q` replaced by `Q`.
//!
//! Renaming is a uniform substitution of propositional atoms, so every
//! propositional step (Tseitin tautologies, resolution, contraction) stays
//! valid. A theory lemma that mentions a proxy is refused outright
//! ([`RenameDecline::TheoryProxy`]); the probe is LRA over Real atoms, where
//! a Boolean proxy has no business. Both directions rebuild with the RAW
//! constructors, so the round trip `rename(proxy(t)) == t` holds exactly; the
//! certificate checks it for every probe assertion, and the strict checker
//! re-derives every renamed step anyway.
//!
//! CONSTANT ATOMS. Substituting instance values into an authored body can
//! leave an atom whose arithmetic is variable-free (`60 = -21` once the
//! search's value cancels its binder) or a Boolean constant (a Bool binder's
//! value). The probe's preprocessing would FOLD such an atom and rewrite the
//! whole assertion around it; the rewritten assertion is no probe assertion,
//! so its leaf demotes to a premiseless `trust` and the probe's own strict
//! check refuses the refutation (measured: every T2 exemplar but one). Such
//! an atom is proxied too, and its truth value is handed to the probe as a
//! separate unit FACT (`k` or `(not k)`) that the stitch derives with a
//! strict step of its own (`true` / `false`, or a one-literal `la_generic`).
//! A fact is only ever a hint: a wrong truth value yields a unit the strict
//! checker refuses.

use crate::qe::cooper::Rel;
use crate::qe::linrat::parse_literal;
use ay_core::term::Constant;
use num_traits::{Signed, Zero};

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::TermData;
use ay_core::{Proof, ProofStep, Sort, TermId, TermStore};

/// Stack red zone / growth for the recursive rebuilds.
const STACK_RED_ZONE: usize = 64 * 1024;
const STACK_SIZE: usize = 2 * 1024 * 1024;

/// Why a probe proof could not be renamed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::executor) enum RenameDecline {
    /// A theory lemma mentions a proxy.
    TheoryProxy,
    /// A step kind the flat renaming does not model (anchors, SOS).
    UnsupportedStep,
    /// A term the rebuild does not model (a `let`, or a quantifier in the
    /// probe's own proof).
    UnsupportedTerm,
}

impl RenameDecline {
    pub(in crate::executor) fn label(self) -> &'static str {
        match self {
            Self::TheoryProxy => "rename-theory-proxy",
            Self::UnsupportedStep => "rename-unsupported-step",
            Self::UnsupportedTerm => "rename-unsupported-term",
        }
    }
}

/// The two-way quantifier ↔ proxy map, with memoized rebuilds.
#[derive(Default)]
pub(in crate::executor) struct ProxyRenaming {
    to_proxy: HashMap<TermId, TermId>,
    to_quantifier: HashMap<TermId, TermId>,
    proxied: HashMap<TermId, TermId>,
    renamed: HashMap<TermId, TermId>,
    /// Constant atoms proxied, in creation order, with their truth value.
    constants: Vec<(TermId, TermId, bool)>,
    /// The first quantifier proxied (test mutation support).
    #[cfg(test)]
    first_quantifier: Option<TermId>,
    /// Test mutation: a LOSSY reverse map that renames every proxy to the
    /// first quantifier proxied, so `rename(proxy(t)) != t` whenever two
    /// quantifiers were proxied.
    #[cfg(test)]
    pub(in crate::executor) lossy_rename: bool,
}

impl ProxyRenaming {
    /// Proxies minted so far.
    pub(in crate::executor) fn len(&self) -> usize {
        self.to_proxy.len()
    }

    /// `(proxy, atom, truth)` for every constant atom proxied so far.
    pub(in crate::executor) fn constants(&self) -> &[(TermId, TermId, bool)] {
        &self.constants
    }

    /// The probe's unit facts: `k` for a true constant atom, `(not k)` for a
    /// false one.
    pub(in crate::executor) fn constant_facts(&self, terms: &mut TermStore) -> Vec<TermId> {
        self.constants
            .iter()
            .map(|&(proxy, _, truth)| {
                if truth {
                    proxy
                } else {
                    terms.mk_not_raw(proxy)
                }
            })
            .collect()
    }

    fn proxy_constant(&mut self, terms: &mut TermStore, atom: TermId, truth: bool) -> TermId {
        let proxy = terms.mk_fresh_var("qlra!pc", Sort::Bool);
        self.to_proxy.insert(atom, proxy);
        self.to_quantifier.insert(proxy, atom);
        self.constants.push((proxy, atom, truth));
        proxy
    }

    /// `term` with every maximal quantified subterm and every constant atom
    /// replaced by its proxy. `None` on a `let` or an unmodelled term.
    pub(in crate::executor) fn proxy(
        &mut self,
        terms: &mut TermStore,
        term: TermId,
    ) -> Option<TermId> {
        if let Some(&done) = self.proxied.get(&term) {
            return Some(done);
        }
        let out = stacker::maybe_grow(STACK_RED_ZONE, STACK_SIZE, || {
            Some(match terms.get(term).clone() {
                TermData::Forall(..) | TermData::Exists(..) => {
                    let proxy = terms.mk_fresh_var("qlra!px", Sort::Bool);
                    #[cfg(test)]
                    {
                        self.first_quantifier.get_or_insert(term);
                    }
                    self.to_proxy.insert(term, proxy);
                    self.to_quantifier.insert(proxy, term);
                    proxy
                }
                TermData::Const(Constant::Bool(value)) => self.proxy_constant(terms, term, value),
                TermData::App(..) if constant_atom_value(terms, term).is_some() => {
                    let truth = constant_atom_value(terms, term)?;
                    self.proxy_constant(terms, term, truth)
                }
                TermData::Var(..) | TermData::Const(_) => term,
                TermData::Not(inner) => {
                    let rewritten = self.proxy(terms, inner)?;
                    if rewritten == inner {
                        term
                    } else {
                        terms.mk_not_raw(rewritten)
                    }
                }
                TermData::Ite(c, a, b) => {
                    let c2 = self.proxy(terms, c)?;
                    let a2 = self.proxy(terms, a)?;
                    let b2 = self.proxy(terms, b)?;
                    if (c2, a2, b2) == (c, a, b) {
                        term
                    } else {
                        terms.mk_ite_raw(c2, a2, b2)
                    }
                }
                TermData::App(symbol, args) => {
                    let mut rewritten = Vec::with_capacity(args.len());
                    for &arg in &args {
                        rewritten.push(self.proxy(terms, arg)?);
                    }
                    if rewritten == args {
                        term
                    } else {
                        let sort = terms.sort(term).clone();
                        terms.mk_app(symbol, rewritten, sort)
                    }
                }
                _ => return None,
            })
        })?;
        self.proxied.insert(term, out);
        Some(out)
    }

    /// `term` with every proxy replaced by its quantifier. `None` on a term
    /// the rebuild does not model.
    pub(in crate::executor) fn rename(
        &mut self,
        terms: &mut TermStore,
        term: TermId,
    ) -> Option<TermId> {
        if let Some(&quantifier) = self.to_quantifier.get(&term) {
            #[cfg(test)]
            if self.lossy_rename {
                return self.first_quantifier;
            }
            return Some(quantifier);
        }
        if let Some(&done) = self.renamed.get(&term) {
            return Some(done);
        }
        let out = stacker::maybe_grow(STACK_RED_ZONE, STACK_SIZE, || {
            Some(match terms.get(term).clone() {
                TermData::Var(..) | TermData::Const(_) => term,
                TermData::Not(inner) => {
                    let rewritten = self.rename(terms, inner)?;
                    if rewritten == inner {
                        term
                    } else {
                        terms.mk_not_raw(rewritten)
                    }
                }
                TermData::Ite(c, a, b) => {
                    let c2 = self.rename(terms, c)?;
                    let a2 = self.rename(terms, a)?;
                    let b2 = self.rename(terms, b)?;
                    if (c2, a2, b2) == (c, a, b) {
                        term
                    } else {
                        terms.mk_ite_raw(c2, a2, b2)
                    }
                }
                TermData::App(symbol, args) => {
                    let mut rewritten = Vec::with_capacity(args.len());
                    for &arg in &args {
                        rewritten.push(self.rename(terms, arg)?);
                    }
                    if rewritten == args {
                        term
                    } else {
                        let sort = terms.sort(term).clone();
                        terms.mk_app(symbol, rewritten, sort)
                    }
                }
                _ => return None,
            })
        })?;
        self.renamed.insert(term, out);
        Some(out)
    }

    fn rename_all(
        &mut self,
        terms: &mut TermStore,
        list: &[TermId],
    ) -> Result<Vec<TermId>, RenameDecline> {
        list.iter()
            .map(|&t| self.rename(terms, t).ok_or(RenameDecline::UnsupportedTerm))
            .collect()
    }

    /// Rename every term of the probe's proof. Premise indices are kept, so
    /// the DAG is unchanged.
    pub(in crate::executor) fn rename_proof(
        &mut self,
        terms: &mut TermStore,
        probe: &Proof,
    ) -> Result<Proof, RenameDecline> {
        let mut steps = Vec::with_capacity(probe.steps.len());
        for step in &probe.steps {
            steps.push(match step {
                ProofStep::Assume(term) => ProofStep::Assume(
                    self.rename(terms, *term)
                        .ok_or(RenameDecline::UnsupportedTerm)?,
                ),
                ProofStep::Resolution {
                    clause,
                    pivot,
                    clause1,
                    clause2,
                } => ProofStep::Resolution {
                    clause: self.rename_all(terms, clause)?,
                    pivot: self
                        .rename(terms, *pivot)
                        .ok_or(RenameDecline::UnsupportedTerm)?,
                    clause1: *clause1,
                    clause2: *clause2,
                },
                ProofStep::TheoryLemma { clause, .. } => {
                    let renamed = self.rename_all(terms, clause)?;
                    if renamed != *clause {
                        return Err(RenameDecline::TheoryProxy);
                    }
                    step.clone()
                }
                ProofStep::Step {
                    rule,
                    clause,
                    premises,
                    args,
                } => ProofStep::Step {
                    rule: rule.clone(),
                    clause: self.rename_all(terms, clause)?,
                    premises: premises.clone(),
                    args: self.rename_all(terms, args)?,
                },
                _ => return Err(RenameDecline::UnsupportedStep),
            });
        }
        Ok(Proof::from_steps(steps))
    }
}

/// The truth value of an arithmetic comparison whose two sides are linear
/// real terms with variable-free difference, or `None`.
pub(in crate::executor) fn constant_atom_value(terms: &TermStore, atom: TermId) -> Option<bool> {
    let TermData::App(symbol, args) = terms.get(atom) else {
        return None;
    };
    if !matches!(symbol.name(), "=" | "<" | "<=" | ">" | ">=")
        || args.len() != 2
        || !matches!(terms.sort(args[0]), Sort::Real)
    {
        return None;
    }
    let (rel, lin) = parse_literal(terms, atom)?;
    if !lin.coeffs.is_empty() {
        return None;
    }
    let c = &lin.constant;
    Some(match rel {
        Rel::Eq => c.is_zero(),
        Rel::Ne => !c.is_zero(),
        Rel::Le => !c.is_positive(),
        Rel::Lt => c.is_negative(),
    })
}
