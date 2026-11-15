// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Skolemization of the authored existentials a QSAT `unsat` publication
//! walks: a top-level `exists` conjunct (depth 1) and an effective
//! existential of the expansion chain. A single binder is one `sko` step; a
//! multi-binder existential is Skolemized ONE BINDER AT A TIME
//! ([`skolemize_binders`]): a `qnt_join` split peels its first binder off and
//! a single-binder `sko` step Skolemizes it through its own registered
//! witness. Every step is a hint the strict validators re-derive.

use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::term::TermData;
use ay_core::{Sort, TermId, TermStore};

use super::super::proof::{ExpansionStep, QuantifierJoinRecord};
use super::super::{Executor, SkolemInstanceRecord};
use super::unsat::Records;
use crate::cegqi::lra_nested;
use crate::ematching::contains_quantifier;
use crate::qsat::Game;

type Outcome<T> = Result<T, &'static str>;

/// Skolemize the effective existential `quantified` with at least two
/// binders, derivable as the unit `source` (`quantified` itself when
/// `positive`, `(not quantified)` for a negated `forall`), ONE BINDER AT A
/// TIME:
///
/// ```text
/// Q x₁…xₙ φ  --qnt_join-->  Q x₁ (Q x₂…xₙ φ)  --sko w₁-->  Q x₂…xₙ φ[x₁:=w₁]  --> …
/// ```
///
/// Every witness is a fresh symbol with its OWN registered choice over the
/// single-binder quantifier it Skolemizes, so each `sko` step is validated
/// per binder by the unchanged single-binder `sko_forall`/`sko_ex` validator,
/// and each split by the strict `qnt_join` validator. Nothing here carries
/// authority: a wrong step is refused by those validators.
///
/// Returns the witnesses in binder order and the final unit (the fully
/// instantiated body, negated for a `forall` source).
/// Build the quantifier of the source's polarity (`exists` when the
/// source is positive, `forall` for a negated-`forall` source).
fn skolem_quantifier(
    terms: &mut TermStore,
    positive: bool,
    binders: Vec<(String, Sort)>,
    body: TermId,
) -> TermId {
    if positive {
        terms.mk_exists(binders, body)
    } else {
        terms.mk_forall(binders, body)
    }
}

pub(in crate::executor) fn skolemize_binders(
    terms: &mut TermStore,
    source: TermId,
    quantified: TermId,
    positive: bool,
    steps: &mut Vec<ExpansionStep>,
) -> Outcome<(Vec<TermId>, TermId)> {
    let (binders, body) = match terms.get(quantified).clone() {
        TermData::Exists(binders, body, _) if positive => (binders, body),
        TermData::Forall(binders, body, _) if !positive => (binders, body),
        _ => return Err("unsat-skolem-shape"),
    };
    if binders.len() < 2 {
        return Err("unsat-skolem-shape");
    }
    // `qnt_join` requires distinct names: refuse up front rather than build a
    // chain its validator rejects.
    let mut names = HashSet::default();
    if !binders.iter().all(|(name, _)| names.insert(name.as_str())) {
        return Err("unsat-skolem-binder-names");
    }
    let mut source = source;
    let mut current = quantified;
    let mut current_body = body;
    let mut witnesses = Vec::with_capacity(binders.len());
    for (index, (name, sort)) in binders.iter().enumerate() {
        let binder = vec![(name.clone(), sort.clone())];
        let rest = &binders[index + 1..];
        // The single-binder quantifier this witness Skolemizes, and its body.
        let (single, single_body) = if rest.is_empty() {
            (current, current_body)
        } else {
            let inner = skolem_quantifier(terms, positive, rest.to_vec(), current_body);
            let nested = skolem_quantifier(terms, positive, binder.clone(), inner);
            steps.push(ExpansionStep::Join(QuantifierJoinRecord {
                source,
                joined: current,
                nested,
                positive,
            }));
            source = if positive {
                nested
            } else {
                terms.mk_not_raw(nested)
            };
            (nested, inner)
        };
        let witness = terms.mk_fresh_var(&format!("sk!{name}"), sort.clone());
        if let TermData::Var(fresh, _) = terms.get(witness).clone() {
            terms.mark_skolem_symbol(fresh);
        }
        // `current_body[xᵢ := wᵢ]`; for a non-final binder the instance is
        // the remaining quantifier over it.
        let next_body = lra_nested::tree::instantiate(terms, current_body, &binder, &[witness])
            .ok_or("unsat-expansion-substitution")?;
        let instance = if rest.is_empty() {
            next_body
        } else {
            skolem_quantifier(terms, positive, rest.to_vec(), next_body)
        };
        // A `forall` source is `¬∀x. B ≡ ∃x. ¬B`: its choice body is negated.
        let choice_body = if positive {
            single_body
        } else {
            terms.mk_not(single_body)
        };
        terms.register_skolem_choice(
            witness,
            ay_core::SkolemChoice {
                binder: name.clone(),
                sort: sort.clone(),
                body: choice_body,
            },
        );
        let asserted = if positive {
            instance
        } else {
            terms.mk_not_raw(instance)
        };
        steps.push(ExpansionStep::Skolem(SkolemInstanceRecord {
            source,
            quantified: single,
            witness,
            instance,
            asserted,
            positive,
        }));
        witnesses.push(witness);
        source = asserted;
        current = instance;
        current_body = next_body;
    }
    Ok((witnesses, source))
}

impl Executor {
    /// Skolemize a top-level `exists` conjunct with several binders one
    /// binder at a time (`skolemize_binders`: `qnt_join` splits and
    /// single-binder `sko` steps, each witness with its own registered
    /// choice), mapping each engine variable to its binder's witness.
    pub(super) fn qsat_skolem_conjunct_binders(
        &mut self,
        game: &Game,
        conjunct: TermId,
        map: &mut Vec<(TermId, TermId)>,
        records: &mut Records,
    ) -> Result<(), &'static str> {
        let TermData::Exists(binders, body, _) = self.ctx.terms.get(conjunct).clone() else {
            return Err("unsat-shape");
        };
        if contains_quantifier(&self.ctx.terms, body) {
            return Err("unsat-nested-exists");
        }
        let occ = game
            .occurrences
            .iter()
            .find(|o| o.quantifier == conjunct && o.positive && !o.universal && o.level == 0)
            .ok_or("unsat-exists-unplaced")?;
        if occ.vars.len() != binders.len() {
            return Err("unsat-exists-unplaced");
        }
        let vars = occ.vars.clone();
        let (witnesses, _) = skolemize_binders(
            &mut self.ctx.terms,
            conjunct,
            conjunct,
            true,
            &mut records.chain,
        )?;
        map.extend(vars.into_iter().zip(witnesses));
        Ok(())
    }

    /// Skolemize a top-level single-binder `exists` conjunct through a
    /// registered witness, mapping its engine variable to the witness.
    pub(super) fn qsat_skolem_conjunct(
        &mut self,
        game: &Game,
        conjunct: TermId,
        map: &mut Vec<(TermId, TermId)>,
    ) -> Result<SkolemInstanceRecord, &'static str> {
        let TermData::Exists(binders, body, _) = self.ctx.terms.get(conjunct).clone() else {
            return Err("unsat-shape");
        };
        let [(name, sort)] = binders.as_slice() else {
            return Err("unsat-multi-binder-exists");
        };
        if contains_quantifier(&self.ctx.terms, body) {
            return Err("unsat-nested-exists");
        }
        let occ = game
            .occurrences
            .iter()
            .find(|o| o.quantifier == conjunct && o.positive && !o.universal && o.level == 0)
            .ok_or("unsat-exists-unplaced")?;
        let witness = self
            .ctx
            .terms
            .mk_fresh_var(&format!("sk!{name}"), sort.clone());
        if let TermData::Var(fresh, _) = self.ctx.terms.get(witness).clone() {
            self.ctx.terms.mark_skolem_symbol(fresh);
        }
        let instance =
            lra_nested::tree::instantiate(&mut self.ctx.terms, body, &binders, &[witness])
                .ok_or("unsat-substitution")?;
        self.ctx.terms.register_skolem_choice(
            witness,
            ay_core::SkolemChoice {
                binder: name.clone(),
                sort: sort.clone(),
                body,
            },
        );
        map.push((occ.vars[0], witness));
        Ok(SkolemInstanceRecord {
            source: conjunct,
            quantified: conjunct,
            witness,
            instance,
            asserted: instance,
            positive: true,
        })
    }
}

#[cfg(test)]
impl Executor {
    /// Test probe: [`skolemize_binders`] on `(exists ((r Real) (r Real)) (> r 0))`;
    /// its result and the number of chain steps it recorded.
    pub(crate) fn test_skolemize_binders_with_repeated_name(
        &mut self,
    ) -> (Result<(), &'static str>, usize) {
        let terms = &mut self.ctx.terms;
        let r = terms.mk_var("r", Sort::Real);
        let zero = terms.mk_rational(num_rational::BigRational::from_integer(0.into()));
        let body = terms.mk_app(ay_core::Symbol::named(">"), [r, zero], Sort::Bool);
        let binders = vec![("r".to_string(), Sort::Real), ("r".to_string(), Sort::Real)];
        let quantified = terms.mk_exists(binders, body);
        let mut steps = Vec::new();
        let result = skolemize_binders(terms, quantified, quantified, true, &mut steps).map(|_| ());
        (result, steps.len())
    }
}
