// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Whole-proof provenance for FRESH-symbol definitional extensions.
//!
//! # What is being certified
//!
//! AY's `EqDiffVar` preprocessing pass mints a symbol the problem never
//! mentions and defines it by a linear term over the problem's own symbols,
//! asserting the definition as the inequality pair `(<= d lin)` / `(>= d lin)`
//! — canonically `(<= d lin)` and `(<= lin d)`. Those assertions reach proof
//! reconstruction as leaves, and they are neither authored (so `assume` would
//! claim authority the problem never granted) nor valid (so no theory-lemma
//! kind can carry them: `d ≤ lin` is false for most valuations of a symbol the
//! problem constrains). Before this module they demoted to a premiseless
//! `trust` step and strict certification rejected a CORRECT refutation.
//!
//! `purify_bool_args` does the same thing in the more DIRECT form: it mints a
//! fresh Boolean `p` for a compound Boolean argument `b` and asserts the
//! equality `(= p b)` outright. That leaf arrives as
//! [`AletheRule::FreshDefEq`], and this ONE registry vets both rules.
//!
//! # Why the two rules MUST share this registry
//!
//! Not a convenience — a soundness requirement. The guards below are about a
//! SYMBOL, not about a step, and the population of definitions for a symbol is
//! the union over both rules. A proof carrying `(<= d 0)` as a
//! `fresh_def_bound` and `(= d (+ x 1))` as a `fresh_def_eq` has TWO
//! definientia for one `d`, and jointly they force `x + 1 ≤ 0` — a genuine
//! constraint on the problem's own `x`. Two separate registries would each see
//! one definition, find it unique, and accept. One registry sees both and
//! rejects on **SINGLE DEFINIENS**. The same argument applies to
//! **INDEPENDENT**: a symbol defined by one rule must not occur in a definiens
//! recorded by the other.
//!
//! # The soundness argument
//!
//! Write `A` for the proof's `assume` set and `P` for the set of bound atoms
//! carried by the proof's `fresh_def_bound` steps. Every other step in a
//! strictly checked proof is an inference whose conclusion is entailed by its
//! premises, or a tautology; by induction, deriving the empty clause proves
//! `A ∪ P` unsatisfiable. The claim this module has to establish is therefore
//! exactly:
//!
//! > `A ∪ P` unsatisfiable ⟹ `A` unsatisfiable.
//!
//! Equivalently: `A` satisfiable ⟹ `A ∪ P` satisfiable. Let `M ⊨ A`. Define
//! `M'` to agree with `M` everywhere except on the introduced symbols, setting
//! `d ↦ lin_d^M` for each binding `d := lin_d`. Then
//!
//! * `M' ⊨ A`, because no introduced `d` occurs in `A` (guard **FRESH**);
//! * `lin_d^{M'} = lin_d^M`, because no introduced symbol occurs in ANY
//!   definiens (guard **INDEPENDENT**), so the reinterpretation cannot change
//!   a defining term — this is what makes the assignments simultaneous rather
//!   than mutually recursive;
//! * `d^{M'} = lin_d^{M'}` is a legal assignment, because `d` and `lin_d` have
//!   the same sort (guard **SORT**, checked in
//!   [`ay_core::proof_validation::recognize_fresh_def_bound`]); and
//! * every atom in `P` for `d` is `(<= d lin_d)`, `(<= lin_d d)` or
//!   `(= d lin_d)` for the ONE `lin_d` recorded for `d` (guard **SINGLE
//!   DEFINIENS**), each of which is satisfied by `d = lin_d` — the equality
//!   most directly of all.
//!
//! Hence `M' ⊨ A ∪ P`. ∎
//!
//! The argument is INDIFFERENT to which of the two rules carried an atom: it
//! only ever uses `d^{M'} = lin_d^{M'}`. That is why one registry suffices, and
//! why the equality form needs no additional condition beyond the four.
//!
//! # What each guard is standing in for
//!
//! Every guard is load-bearing and each has a concrete counterexample, all of
//! them in `fresh_def_tests.rs` with the falsifying assignment named:
//!
//! * **FRESH** — `d` also occurring in the problem makes `(<= d lin)` an
//!   ordinary added constraint. `A = {d = 5}`, `lin = 0`: `A` is satisfiable,
//!   `A ∪ {d ≤ 0, 0 ≤ d}` is not.
//! * **INDEPENDENT** — a definiens mentioning an introduced symbol makes the
//!   definitions recursive and possibly jointly unsatisfiable. `d := d + 1`
//!   (self), or `d1 := d2 + 1` with `d2 := d1 + 1` (cycle): no assignment
//!   exists, so the "extension" refutes a satisfiable `A`.
//! * **SINGLE DEFINIENS** — two definientia for one symbol equate them.
//!   `d := x` and `d := x + 1` forces `x = x + 1`, refuting a satisfiable `A`.
//!   This is also what the two directions being *consistent* means: the pair
//!   `(<= d 0)` with `(<= 1 d)` is `0 ≥ d ≥ 1`, unsatisfiable outright.
//! * **SORT** — `d : Int` bounded above and below by a `Real` term forces that
//!   term to be integral. `lin = (/ x 2)` with `A = {x = 1}` is satisfiable but
//!   admits no integer `d` with `d ≤ 1/2 ≤ d`.
//!
//! # A single direction is enough, and is NOT a weakening
//!
//! The argument above never needs both bounds: `M'` satisfies every atom in
//! `P` for `d` whether `P` holds one of them or both, because `d = lin_d`
//! satisfies `d ≤ lin_d` and `lin_d ≤ d` alike. Requiring both to be PRESENT
//! would be a completeness restriction with no soundness content, and a costly
//! one — measured on `dillig12_m`, 102 of 130 (proof, symbol) groups carry
//! exactly one direction, because a refutation normally needs only one bound
//! of a definition. What the "both directions" instinct is really protecting
//! against is an INCONSISTENT pair — an upper bound by `lin1` and a lower
//! bound by a different `lin2` — and that is precisely what **SINGLE
//! DEFINIENS** rejects.
//!
//! # Freshness is checked, never assumed
//!
//! The introduced symbols are spelled `__ay_eqdv!N`, and nothing here looks at
//! that. A name prefix is a producer convention; the property that matters is
//! that the PROBLEM does not constrain the symbol, and this module decides it
//! by traversing the problem's own terms — the same discipline
//! [`super::array_axiom::ExtDiffRegistry`] applies to extensionality witnesses.

use ay_core::kani_compat::{DetHashMap, DetHashSet};
use ay_core::term::TermData;
use ay_core::{AletheRule, Proof, ProofId, ProofStep, TermId, TermStore};

use super::fresh_def_dispatch::recognize_fresh_definition;
use super::ProofCheckError;

/// One certified definitional extension: the introduced symbol and the term it
/// was defined by.
#[derive(Debug, Clone, Copy)]
pub(crate) struct FreshDefBinding {
    /// The single defining term recorded for the symbol this is keyed by.
    ///
    /// The SYMBOL itself is the map key, deliberately: `mk_var` keys on
    /// (name, sort), so one spelling can carry two `TermId`s, and the freshness
    /// question is about the spelling. Keeping only the definiens here means
    /// there is no second identity to drift out of sync with the key.
    pub(crate) definiens: TermId,
    /// The first introducing step, for diagnostics.
    pub(crate) step: ProofId,
}

/// Whole-proof registry of fresh-symbol definitional extensions.
///
/// Built ONCE per check from the proof's `fresh_def_bound` AND `fresh_def_eq`
/// steps and the problem's assertion terms — one registry over both rules, for
/// the soundness reason the module docs give. Construction enforces every
/// whole-proof condition of the module-level soundness argument; per-step
/// validation then only has to confirm that the atom in hand belongs to its
/// symbol's recorded binding.
#[derive(Debug, Default)]
pub struct FreshDefRegistry {
    bindings: DetHashMap<String, FreshDefBinding>,
}

impl FreshDefRegistry {
    /// Whether the proof introduced no fresh definitions at all.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.bindings.is_empty()
    }

    /// Number of distinct symbols introduced.
    #[must_use]
    pub fn len(&self) -> usize {
        self.bindings.len()
    }

    /// Build the registry for `proof`.
    ///
    /// `problem_assertions` should be the AUTHORED assertions when the caller
    /// has them. It is an ADDITIONAL freshness source, not the primary one:
    /// the property the soundness argument needs is that no introduced symbol
    /// occurs in the proof's own `assume` leaves, and that is always available.
    /// Supplying the problem can therefore only REJECT more (a symbol the
    /// problem constrains but this particular refutation never assumed), which
    /// is the safe direction and catches a producer that mints a colliding
    /// name. Passing a superset is likewise always safe.
    ///
    /// Passing `None` deliberately does NOT fail closed. A fresh-definition
    /// bound that cannot be validated becomes a hard `InvalidTheoryLemma`
    /// rejection, which is strictly WORSE than the premiseless `trust` it
    /// replaced (that one is rescuable by the deferred-trust discharge lane).
    /// `check_proof_collecting_trust_with_typed_context` is called with `None`
    /// from the proof-surgery revert gate, so failing closed there would
    /// convert a rescuable rejection into an unrescuable one.
    ///
    /// # Errors
    ///
    /// Returns [`ProofCheckError::InvalidTheoryLemma`] naming the offending
    /// step whenever any condition fails. There is no lenient mode: an
    /// introduction that cannot be verified fails the whole check rather than
    /// being silently dropped, which would only resurface as an unbound symbol
    /// with a worse diagnostic.
    pub fn collect(
        proof: &Proof,
        terms: &TermStore,
        problem_assertions: Option<&[TermId]>,
    ) -> Result<Self, ProofCheckError> {
        let bindings = Self::collect_bindings(proof, terms)?;
        if bindings.is_empty() {
            return Ok(Self { bindings });
        }
        verify_fresh_and_independent(proof, terms, problem_assertions, &bindings)?;
        Ok(Self { bindings })
    }

    /// (1) SHAPE and (2) SINGLE DEFINIENS, per introducing step.
    ///
    /// BOTH fresh-definition rules feed one map. See the module docs for why
    /// splitting them would be unsound rather than merely redundant.
    fn collect_bindings(
        proof: &Proof,
        terms: &TermStore,
    ) -> Result<DetHashMap<String, FreshDefBinding>, ProofCheckError> {
        let mut bindings: DetHashMap<String, FreshDefBinding> = DetHashMap::default();
        for (index, step) in proof.steps.iter().enumerate() {
            let ProofStep::Step {
                rule: rule @ (AletheRule::FreshDefBound | AletheRule::FreshDefEq),
                clause,
                premises,
                args,
            } = step
            else {
                continue;
            };
            let step_id = ProofId(index as u32);
            let (definiendum, definiens) =
                recognize_fresh_definition(terms, rule, clause, premises.len(), args)
                    .map_err(|reason| invalid(step_id, &reason))?;
            let name = definiendum_name(terms, step_id, definiendum)?;
            match bindings.get(&name) {
                Some(prior) => {
                    // Two definientia for one symbol is an EQUATION between
                    // them, not a definition: `d := x` with `d := x + 1`
                    // forces `x = x + 1`. Same-`TermId` repeats are the
                    // ordinary case (an upper and a lower bound, or the same
                    // leaf reached twice) and stay accepted.
                    //
                    // Only the DEFINIENS is compared. A differing definiendum
                    // at an EQUAL definiens is unreachable by construction —
                    // `mk_var` keys on (name, sort) and the shape gate forces
                    // `sort(d) == sort(lin)`, so one definiens `TermId` fixes
                    // the sort and therefore the symbol — and an unreachable
                    // branch is not a guard, because it cannot be
                    // mutation-checked.
                    if prior.definiens != definiens {
                        return Err(invalid(
                            step_id,
                            &format!(
                                "fresh definition `{name}` is given a SECOND definiens (already \
                                 bound at step {}); two definitions of one symbol equate their \
                                 defining terms and are not a conservative extension",
                                prior.step
                            ),
                        ));
                    }
                }
                None => {
                    bindings.insert(
                        name,
                        FreshDefBinding {
                            definiens,
                            step: step_id,
                        },
                    );
                }
            }
        }

        Ok(bindings)
    }

    /// Validate one `fresh_def_bound` step against this registry and return the
    /// atom it introduces.
    ///
    /// # Errors
    ///
    /// Returns [`ProofCheckError::InvalidTheoryLemma`] when the step is
    /// malformed or names a symbol this registry did not bind to this exact
    /// definiens.
    pub(crate) fn validate_bound(
        &self,
        terms: &TermStore,
        step_id: ProofId,
        clause: &[TermId],
        premises: &[ProofId],
        args: &[TermId],
    ) -> Result<TermId, ProofCheckError> {
        self.validate_introduction(
            terms,
            &AletheRule::FreshDefBound,
            step_id,
            clause,
            premises,
            args,
        )
    }

    /// Validate one `fresh_def_eq` step against this registry and return the
    /// atom it introduces.
    ///
    /// # Errors
    ///
    /// Returns [`ProofCheckError::InvalidTheoryLemma`] when the step is
    /// malformed or names a symbol this registry did not bind to this exact
    /// definiens.
    pub(crate) fn validate_eq(
        &self,
        terms: &TermStore,
        step_id: ProofId,
        clause: &[TermId],
        premises: &[ProofId],
        args: &[TermId],
    ) -> Result<TermId, ProofCheckError> {
        self.validate_introduction(
            terms,
            &AletheRule::FreshDefEq,
            step_id,
            clause,
            premises,
            args,
        )
    }

    /// The per-step half, shared by both rules.
    ///
    /// It re-runs the SAME recognizer `collect_bindings` ran and then confirms
    /// the step belongs to its symbol's ONE vetted binding. Consulting the
    /// registry rather than re-deciding locally is the point: a step the
    /// whole-proof pass never saw has had none of FRESH / INDEPENDENT /
    /// SINGLE DEFINIENS checked.
    fn validate_introduction(
        &self,
        terms: &TermStore,
        rule: &AletheRule,
        step_id: ProofId,
        clause: &[TermId],
        premises: &[ProofId],
        args: &[TermId],
    ) -> Result<TermId, ProofCheckError> {
        let (definiendum, definiens) =
            recognize_fresh_definition(terms, rule, clause, premises.len(), args)
                .map_err(|reason| invalid(step_id, &reason))?;
        let name = definiendum_name(terms, step_id, definiendum)?;
        let binding = self.bindings.get(&name).ok_or_else(|| {
            invalid(
                step_id,
                &format!("fresh definition `{name}` has no vetted whole-proof binding"),
            )
        })?;
        if binding.definiens != definiens {
            return Err(invalid(
                step_id,
                &format!(
                    "fresh definition `{name}` was bound to a different definiens at step {}",
                    binding.step
                ),
            ));
        }
        // The step's own clause literal, re-read from the recognizer rather
        // than echoed from `clause`: the recognizer is what established the
        // literal IS the definitional atom.
        Ok(clause[0])
    }
}

/// (3) FRESH and (4) INDEPENDENT.
///
/// `constrained` collects every symbol name the problem mentions and every
/// symbol name the proof's `assume` leaves mention; `definiens_names` collects
/// every symbol name any recorded DEFINIENS mentions. An introduced symbol
/// appearing in either set fails one of the two guards, and the two sets are
/// kept apart so the diagnostic can say WHICH.
fn verify_fresh_and_independent(
    proof: &Proof,
    terms: &TermStore,
    problem_assertions: Option<&[TermId]>,
    bindings: &DetHashMap<String, FreshDefBinding>,
) -> Result<(), ProofCheckError> {
    let mut constrained: DetHashSet<String> = DetHashSet::default();
    let mut visited: DetHashSet<TermId> = DetHashSet::default();
    for &assertion in problem_assertions.unwrap_or(&[]) {
        collect_symbol_names(terms, assertion, &mut constrained, &mut visited);
    }
    for step in &proof.steps {
        if let ProofStep::Assume(term) = step {
            collect_symbol_names(terms, *term, &mut constrained, &mut visited);
        }
    }

    let mut definiens_names: DetHashSet<String> = DetHashSet::default();
    let mut definiens_visited: DetHashSet<TermId> = DetHashSet::default();
    for binding in bindings.values() {
        collect_symbol_names(
            terms,
            binding.definiens,
            &mut definiens_names,
            &mut definiens_visited,
        );
    }

    for (name, binding) in bindings {
        if definiens_names.contains(name) {
            return Err(invalid(
                binding.step,
                &format!(
                    "fresh definition `{name}` occurs inside a definiens; the definitions \
                     would be recursive and need not admit any simultaneous assignment"
                ),
            ));
        }
        if constrained.contains(name) {
            return Err(invalid(
                binding.step,
                &format!(
                    "fresh definition `{name}` is NOT fresh: the symbol also occurs in the \
                     problem or in an `assume` of this proof, so bounding it is an ordinary \
                     added constraint rather than a conservative extension"
                ),
            ));
        }
    }

    Ok(())
}

fn definiendum_name(
    terms: &TermStore,
    step_id: ProofId,
    definiendum: TermId,
) -> Result<String, ProofCheckError> {
    match terms.get(definiendum) {
        TermData::Var(name, _) => Ok(name.clone()),
        _ => Err(invalid(
            step_id,
            "a fresh-definition bound's defined symbol must be an atomic variable",
        )),
    }
}

fn invalid(step: ProofId, reason: &str) -> ProofCheckError {
    ProofCheckError::InvalidTheoryLemma {
        step,
        reason: reason.to_string(),
    }
}

/// Collect every symbol NAME reachable from `root`.
///
/// Names, not `TermId`s: two entries can share a name at different sorts, and
/// the freshness question is about the SYMBOL. `visited` is shared across roots
/// so a whole assertion stack costs one traversal of the interned DAG.
fn collect_symbol_names(
    terms: &TermStore,
    root: TermId,
    names: &mut DetHashSet<String>,
    visited: &mut DetHashSet<TermId>,
) {
    let mut stack = vec![root];
    while let Some(id) = stack.pop() {
        if !visited.insert(id) {
            continue;
        }
        match terms.get(id) {
            TermData::Var(name, _) => {
                names.insert(name.clone());
            }
            TermData::App(sym, args) => {
                names.insert(sym.name().to_string());
                stack.extend(args.iter().copied());
            }
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(c, t, e) => {
                stack.push(*c);
                stack.push(*t);
                stack.push(*e);
            }
            TermData::Let(bindings, body) => {
                for (name, value) in bindings {
                    names.insert(name.clone());
                    stack.push(*value);
                }
                stack.push(*body);
            }
            TermData::Forall(vars, body, triggers) | TermData::Exists(vars, body, triggers) => {
                for (name, _) in vars {
                    names.insert(name.clone());
                }
                stack.push(*body);
                stack.extend(triggers.iter().flatten().copied());
            }
            _ => {}
        }
    }
}
