// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! UNSAT beyond depth 1: an EXPANSION of the authored roots along the ∀
//! player's strategy.
//!
//! Walking each authored conjunct from the outside in, every effective
//! universal is instantiated at its strategy term (a decision list over the
//! ∃ player's lemmas, over the terms already bound for the enclosing
//! binders) and every effective existential is Skolemized through a
//! registered witness; the chain ends at a quantifier-free instance of the
//! matrix, which the consequence replay's ground probe must refute. The walk
//! declines any shape the chain cannot carry: quantifiers under `or` or a
//! double negation, repeated binder names, and a strategy term over a
//! binder that does not enclose the occurrence. A multi-binder effective
//! existential is Skolemized one binder at a time ([`skolemize_binders`]):
//! a `qnt_join` split peels its first binder off, and a single-binder `sko`
//! step Skolemizes that binder through its own registered witness.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::TermData;
use ay_core::{Sort, TermId, TermStore};

use super::super::proof::{ExpansionStep, NegatedExistsDual};
use super::super::{Executor, SkolemInstanceRecord};
use super::skolem::skolemize_binders;
use super::unsat::{and_closure, fold_closed};
use crate::cegqi::lra_nested;
use crate::ematching::{contains_quantifier, ForallInstantiationProvenance};
use crate::qsat::prenex::Occurrence;
use crate::qsat::{self, Game, Run};

type Outcome<T> = Result<T, &'static str>;

/// The quantifier node being expanded: the instantiated quantifier, its
/// binders, its instantiated body and the authored body.
struct Node {
    current: TermId,
    binders: Vec<(String, Sort)>,
    cbody: TermId,
    abody: TermId,
}

/// One pending node of the walk: a derivable term, the authored term it
/// instantiates (itself when `pol`, its negation otherwise), the polarity,
/// and the engine-variable bindings of the enclosing occurrences.
struct Item {
    derivable: TermId,
    authored: TermId,
    pol: bool,
    emap: Vec<(TermId, TermId)>,
}

/// The chain being built and what it is built from.
struct Chain<'g> {
    game: &'g Game,
    strategy: HashMap<TermId, TermId>,
    purified: Vec<(TermId, TermId)>,
    engine: HashSet<TermId>,
    steps: Vec<ExpansionStep>,
    work: Vec<Item>,
}

fn mentions_any(terms: &TermStore, t: TermId, vars: &HashSet<TermId>) -> bool {
    let mut stack = vec![t];
    let mut seen = HashSet::default();
    while let Some(x) = stack.pop() {
        if !seen.insert(x) {
            continue;
        }
        if vars.contains(&x) {
            return true;
        }
        match terms.get(x) {
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Not(i) => stack.push(*i),
            TermData::Ite(c, a, b) => stack.extend([*c, *a, *b]),
            _ => {}
        }
    }
    false
}

impl Chain<'_> {
    fn occurrence(&self, quantifier: TermId, positive: bool) -> Outcome<&Occurrence> {
        self.game
            .occurrences
            .iter()
            .find(|o| o.quantifier == quantifier && o.positive == positive)
            .ok_or("unsat-expansion-occurrence")
    }

    /// The strategy tuple of a universal occurrence, over the bound terms.
    fn tuple(
        &self,
        terms: &mut TermStore,
        occ: &Occurrence,
        emap: &[(TermId, TermId)],
    ) -> Outcome<Vec<TermId>> {
        let mut tuple = Vec::with_capacity(occ.vars.len());
        for &v in &occ.vars {
            let s = self
                .strategy
                .get(&v)
                .copied()
                .ok_or("unsat-expansion-strategy")?;
            let s = qsat::mbp::substitute(terms, s, &self.purified);
            let s = qsat::mbp::substitute(terms, s, emap);
            if mentions_any(terms, s, &self.engine) {
                return Err("unsat-expansion-out-of-scope");
            }
            tuple.push(fold_closed(terms, s));
        }
        Ok(tuple)
    }

    /// Instantiate an effective universal at its strategy.
    fn universal(
        &mut self,
        terms: &mut TermStore,
        item: &Item,
        node: &Node,
        occ_vars: &[TermId],
        tuple: Vec<TermId>,
    ) -> Outcome<()> {
        let (current, binders, cbody, abody) =
            (node.current, &node.binders[..], node.cbody, node.abody);
        let (source, body) = if item.pol {
            (current, cbody)
        } else {
            // (not (exists x B)) → dual (forall x (not B)).
            let negated = terms.mk_not_raw(cbody);
            let dual = terms.mk_forall(binders.to_vec(), negated);
            self.steps.push(ExpansionStep::Dual(NegatedExistsDual {
                not_exists_root: item.derivable,
                exists: current,
                forall: dual,
                co_units: Vec::new(),
            }));
            (dual, negated)
        };
        let instance = lra_nested::tree::instantiate(terms, body, binders, &tuple)
            .ok_or("unsat-expansion-substitution")?;
        self.steps
            .push(ExpansionStep::Forall(ForallInstantiationProvenance {
                quantifier: source,
                binding: tuple.clone(),
                instance,
            }));
        let mut emap = item.emap.clone();
        emap.extend(occ_vars.iter().copied().zip(tuple));
        self.work.push(Item {
            derivable: instance,
            authored: abody,
            pol: item.pol,
            emap,
        });
        Ok(())
    }

    /// Skolemize an effective existential (single binder).
    fn existential(
        &mut self,
        terms: &mut TermStore,
        item: &Item,
        node: &Node,
        occ_vars: &[TermId],
    ) -> Outcome<()> {
        let (current, binders, cbody, abody) =
            (node.current, &node.binders[..], node.cbody, node.abody);
        let [(name, sort)] = binders else {
            return self.existential_binders(terms, item, node, occ_vars);
        };
        let occ_var = occ_vars[0];
        let witness = terms.mk_fresh_var(&format!("sk!{name}"), sort.clone());
        if let TermData::Var(fresh, _) = terms.get(witness).clone() {
            terms.mark_skolem_symbol(fresh);
        }
        let instance = lra_nested::tree::instantiate(terms, cbody, binders, &[witness])
            .ok_or("unsat-expansion-substitution")?;
        // A `forall` source is `¬∀x. B ≡ ∃x. ¬B`: its choice body is negated.
        let choice_body = if item.pol { cbody } else { terms.mk_not(cbody) };
        terms.register_skolem_choice(
            witness,
            ay_core::SkolemChoice {
                binder: name.clone(),
                sort: sort.clone(),
                body: choice_body,
            },
        );
        let asserted = if item.pol {
            instance
        } else {
            terms.mk_not_raw(instance)
        };
        self.steps.push(ExpansionStep::Skolem(SkolemInstanceRecord {
            source: item.derivable,
            quantified: current,
            witness,
            instance,
            asserted,
            positive: item.pol,
        }));
        let mut emap = item.emap.clone();
        emap.push((occ_var, witness));
        self.work.push(Item {
            derivable: asserted,
            authored: abody,
            pol: item.pol,
            emap,
        });
        Ok(())
    }

    /// Skolemize an effective existential with several binders, one binder at
    /// a time ([`skolemize_binders`]); each occurrence variable maps to its
    /// binder's witness.
    fn existential_binders(
        &mut self,
        terms: &mut TermStore,
        item: &Item,
        node: &Node,
        occ_vars: &[TermId],
    ) -> Outcome<()> {
        if occ_vars.len() != node.binders.len() {
            return Err("unsat-expansion-occurrence");
        }
        let (witnesses, asserted) = skolemize_binders(
            terms,
            item.derivable,
            node.current,
            item.pol,
            &mut self.steps,
        )?;
        let mut emap = item.emap.clone();
        emap.extend(occ_vars.iter().copied().zip(witnesses));
        self.work.push(Item {
            derivable: asserted,
            authored: node.abody,
            pol: item.pol,
            emap,
        });
        Ok(())
    }

    /// One quantifier node of the walk.
    fn quantifier(&mut self, terms: &mut TermStore, item: &Item, current: TermId) -> Outcome<()> {
        let (binders, abody, cbinders, cbody) =
            match (terms.get(item.authored).clone(), terms.get(current).clone()) {
                (TermData::Forall(b, ab, _), TermData::Forall(cb, cbody, _))
                | (TermData::Exists(b, ab, _), TermData::Exists(cb, cbody, _)) => {
                    (b, ab, cb, cbody)
                }
                _ => return Err("unsat-expansion-shape"),
            };
        if binders != cbinders {
            return Err("unsat-expansion-shape");
        }
        let is_forall = matches!(terms.get(item.authored), TermData::Forall(..));
        let universal = is_forall == item.pol;
        let occ = self.occurrence(item.authored, item.pol)?;
        if occ.universal != universal || occ.vars.len() != binders.len() {
            return Err("unsat-expansion-occurrence");
        }
        let occ_vars = occ.vars.clone();
        let node = Node {
            current,
            binders: cbinders,
            cbody,
            abody,
        };
        if universal {
            let tuple = self.tuple(terms, occ, &item.emap)?;
            self.universal(terms, item, &node, &occ_vars, tuple)
        } else {
            self.existential(terms, item, &node, &occ_vars)
        }
    }

    /// Process one work item.
    fn step(&mut self, terms: &mut TermStore, item: Item) -> Outcome<()> {
        if !contains_quantifier(terms, item.authored) {
            return Ok(());
        }
        let current = if item.pol {
            item.derivable
        } else {
            match terms.get(item.derivable) {
                TermData::Not(inner) => *inner,
                _ => return Err("unsat-expansion-polarity"),
            }
        };
        match (terms.get(item.authored).clone(), terms.get(current).clone()) {
            (TermData::Not(a1), TermData::Not(_)) if item.pol => {
                // `(not A1)` positively: A1 at negative polarity.
                self.work.push(Item {
                    derivable: item.derivable,
                    authored: a1,
                    pol: false,
                    emap: item.emap,
                });
                Ok(())
            }
            (TermData::App(sym, args), TermData::App(_, cargs))
                if sym.name() == "and" && item.pol =>
            {
                if args.len() != cargs.len() {
                    return Err("unsat-expansion-shape");
                }
                for (a, c) in args.into_iter().zip(cargs) {
                    if !contains_quantifier(terms, a) || !contains_quantifier(terms, c) {
                        return Err("unsat-expansion-mixed-and");
                    }
                    self.work.push(Item {
                        derivable: c,
                        authored: a,
                        pol: true,
                        emap: item.emap.clone(),
                    });
                }
                Ok(())
            }
            (TermData::Forall(..), _) | (TermData::Exists(..), _) => {
                self.quantifier(terms, &item, current)
            }
            _ => Err("unsat-expansion-shape"),
        }
    }
}

impl Executor {
    /// The expansion chain of a QSAT `unsat` (see the module docs).
    pub(super) fn qsat_expansion_chain(
        &mut self,
        roots: &[TermId],
        game: &Game,
        run: &Run,
    ) -> Outcome<Vec<ExpansionStep>> {
        let strategy = qsat::strategy::forall_strategy(&mut self.ctx.terms, game, run);
        let mut purified: Vec<(TermId, TermId)> =
            game.purified.iter().map(|p| (p.var, p.def)).collect();
        purified.sort_by_key(|&(v, _)| game.level_of.get(&v).copied().unwrap_or(0));
        let engine: HashSet<TermId> = game
            .levels
            .iter()
            .flatten()
            .copied()
            .filter(|v| !game.free.contains(v))
            .collect();
        let work: Vec<Item> = and_closure(self, roots)
            .into_iter()
            .filter(|&c| contains_quantifier(&self.ctx.terms, c))
            .map(|c| Item {
                derivable: c,
                authored: c,
                pol: true,
                emap: Vec::new(),
            })
            .collect();
        if work.is_empty() {
            return Err("unsat-expansion-empty");
        }
        let mut chain = Chain {
            game,
            strategy,
            purified,
            engine,
            steps: Vec::new(),
            work,
        };
        let mut budget = 4_096usize;
        while let Some(item) = chain.work.pop() {
            budget = budget.checked_sub(1).ok_or("unsat-expansion-size")?;
            chain.step(&mut self.ctx.terms, item)?;
        }
        if chain.steps.len() > 4 * lra_nested::caps::M1_PUBLISHABLE_INSTANCES {
            return Err("unsat-expansion-too-long");
        }
        Ok(chain.steps)
    }
}
