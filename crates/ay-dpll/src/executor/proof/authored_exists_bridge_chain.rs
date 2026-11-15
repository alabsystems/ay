// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exists-bridge chain translation for the artifact firewall
//! (#exists-bridge-chain).
//!
//! THE GAP THIS CLOSES. Sledgehammer QEpres `uf.787634` refutes through a
//! bridge universal whose body is an equivalence with an existential
//! side:
//!
//! ```smt2
//! (assert (forall ((v S2)) (= (= (f3 f4 v) f1)
//!                             (exists ((w1 S4) (w2 S2)) B))))
//! ```
//!
//! E-matching instantiates it, the deep Skolemizer eliminates the
//! existential, and the ground re-solve refutes — but no producer could
//! certify the skolemized bridge, so publication was withheld as
//! `unknown`. The missing derivation is a consequence-replay EXPANSION
//! CHAIN over instances this lane proposes itself:
//!
//! ```text
//! forall_inst   bridge ∀ at t⃗        (cl (= A E))        E = (exists w⃗ B)
//! equiv_pos     + (cl A)              (cl E)              [Implied step]
//! qnt_join/sko  E one binder at a time (cl B[w⃗])
//! forall_inst   closing ∀ at w⃗       ground consequences
//! ```
//!
//! The antecedent `A` is itself the consequent of a second bridge
//! equivalence, up to a congruence transport (`(f22 f4) = f4` rewriting
//! one subterm): the chain carries that `Implied` step too, plus a
//! `Congruence` equality (derived by `cong`/`refl` over planned units)
//! and the implied step across it. Every record here is a HINT: the
//! stitcher re-derives each `forall_inst`, `equiv_pos`, `cong` and `sko`
//! step, and the installed candidate still passes the strict
//! installation boundary and the mandatory mint. A wrong chain costs a
//! declined candidate, never a wrong verdict.
//!
//! UNSAT-ONLY, consulted at the same two places as the sibling builders
//! (the artifact firewall's downgrade and CEGQI-UNSAT certification),
//! under the parent `--no-consequence-replay` switch.

use super::authored_consequence_replay::ExpansionStep;
use super::authored_negated_exists_ground_inst::bounded_tuples;
use super::*;

mod saturation;

/// Authored-scope size beyond which this lane declines.
const MAX_AUTHORED_ROOTS: usize = 64;
/// Bridge universals considered per public query.
const MAX_BRIDGES: usize = 2;
/// Instantiation tuples proposed per bridge universal.
const MAX_TUPLES_PER_BRIDGE: usize = 4;
/// Binders (bridge or existential) beyond which planning declines.
const MAX_BINDERS: usize = 3;
/// Saturation records added across all authored universals.
const MAX_SATURATION_RECORDS: usize = 24;
/// Witness candidates per binder sort.
const MAX_WITNESSES_PER_SORT: usize = 8;
/// Chain steps this lane may propose per public query.
const MAX_CHAIN_STEPS: usize = 64;
/// Probe attempts this lane may consume per public check-sat.
const MAX_LANE_ATTEMPTS: u8 = 1;
/// Node budget for the closure and congruence-candidate walks.
const MAX_SCAN_WORK: usize = 20_000;

fn note(message: impl FnOnce() -> String) {
    tracing::debug!(target: "ay::cert::exists_bridge", "{}", message());
}

/// One authored bridge universal and its existential consequent shape.
struct BridgeRoot {
    forall: TermId,
    bindings: Vec<(String, Sort)>,
    body: TermId,
}

impl Executor {
    /// Artifact-firewall translation: turn a semantic refutation that
    /// routes through an authored exists-bridge universal into an
    /// authored-scope strict certificate and install it as `last_proof`.
    /// Returns `true` only when a complete certificate was installed.
    pub(in crate::executor) fn try_translate_exists_bridge_chain_unsat(&mut self) -> bool {
        if !crate::quant_unit_authority::consequence_replay_enabled() {
            return false;
        }
        let attempts = self.exists_bridge_chain_attempts.get();
        if attempts >= MAX_LANE_ATTEMPTS {
            note(|| "decline: lane attempt budget exhausted".into());
            return false;
        }
        let authored = self.exact_concrete_authored_scope();
        if authored.is_empty() || authored.len() > MAX_AUTHORED_ROOTS {
            return false;
        }
        let Some((records, chain)) = self.plan_exists_bridge_chain(&authored) else {
            return false;
        };
        self.exists_bridge_chain_attempts.set(attempts + 1);
        let installed = self.try_translate_authored_consequence_replay_unsat_with_clauses(
            &records,
            &[],
            &[],
            &[],
            &chain,
        );
        note(|| {
            format!(
                "translate: records={} chain={} installed={installed}",
                records.len(),
                chain.len()
            )
        });
        installed
    }

    /// Build the saturation records and expansion chain, or `None` when
    /// no bridge chain is proposable. Hints only; see the module doc.
    fn plan_exists_bridge_chain(
        &mut self,
        authored: &[TermId],
    ) -> Option<(
        Vec<crate::ematching::ForallInstantiationProvenance>,
        Vec<ExpansionStep>,
    )> {
        let (closure, derivable) = self.bridge_and_closure(authored);
        let bridges = self.exact_authored_exists_bridges(&closure);
        if bridges.is_empty() {
            note(|| "decline: no authored exists-bridge universal".into());
            return None;
        }
        let bound_names = self.authored_binder_names(authored);
        // Terms whose units the stitcher can already derive without this
        // lane: the authored closure plus every recorded instance.
        let mut known: ay_core::kani_compat::DetHashSet<TermId> = derivable.clone();
        for record in &self.ematching_proof_records {
            known.insert(record.instance);
        }

        let mut chain: Vec<ExpansionStep> = Vec::new();
        let mut witnesses: Vec<(Sort, TermId)> = Vec::new();
        let mut bridged = false;
        for bridge in bridges.into_iter().take(MAX_BRIDGES) {
            for tuple in self.bridge_tuples(authored, &bridge, &bound_names) {
                if chain.len() >= MAX_CHAIN_STEPS {
                    break;
                }
                let Some(instance) = crate::cegqi::lra_nested::tree::instantiate(
                    &mut self.ctx.terms,
                    bridge.body,
                    &bridge.bindings,
                    &tuple,
                ) else {
                    continue;
                };
                let Some((antecedent, exists)) = self.exists_consequent(instance) else {
                    continue;
                };
                let steps_before = chain.len();
                // Antecedent support first (dependency order for the
                // chain's insert-time checks), then the bridge steps.
                self.plan_antecedent_support(antecedent, &derivable, &known, &mut chain);
                chain.push(ExpansionStep::Forall(
                    crate::ematching::ForallInstantiationProvenance {
                        quantifier: bridge.forall,
                        binding: tuple,
                        instance,
                    },
                ));
                chain.push(ExpansionStep::Implied {
                    implication: instance,
                    antecedent,
                    consequent: exists,
                });
                match self.skolemize_bridge_exists(exists, &mut chain) {
                    Some(fresh) => {
                        witnesses.extend(fresh);
                        bridged = true;
                    }
                    None => chain.truncate(steps_before),
                }
            }
        }
        if !bridged {
            note(|| "decline: no bridge instance skolemizable".into());
            return None;
        }
        let records = self.bridge_saturation_records(authored, &closure, &bound_names, &witnesses);
        Some((records, chain))
    }

    /// The authored `and`-conjunct closure (ordered members + set),
    /// guiding this lane's hints; the stitcher recomputes its own.
    fn bridge_and_closure(
        &self,
        authored: &[TermId],
    ) -> (Vec<TermId>, ay_core::kani_compat::DetHashSet<TermId>) {
        let mut ordered: Vec<TermId> = Vec::new();
        let mut set = ay_core::kani_compat::DetHashSet::default();
        let mut stack = authored.to_vec();
        while let Some(term) = stack.pop() {
            if !set.insert(term) || set.len() > MAX_SCAN_WORK {
                continue;
            }
            ordered.push(term);
            if let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(term) {
                if name == "and" {
                    stack.extend(args.iter().copied());
                }
            }
        }
        (ordered, set)
    }

    /// Authored universals whose body has an implication/equivalence
    /// reading with an `Exists` consequent (quantifier-free body,
    /// bounded binders).
    fn exact_authored_exists_bridges(&self, closure: &[TermId]) -> Vec<BridgeRoot> {
        let mut out = Vec::new();
        for &term in closure {
            let TermData::Forall(bindings, body, _) = self.ctx.terms.get(term).clone() else {
                continue;
            };
            if bindings.is_empty() || bindings.len() > MAX_BINDERS {
                continue;
            }
            if self.exists_consequent(body).is_some() {
                out.push(BridgeRoot {
                    forall: term,
                    bindings,
                    body,
                });
            }
        }
        out
    }

    /// The `(antecedent, exists)` reading of `term`, when some
    /// implication/equivalence orientation has an `Exists` consequent
    /// with a quantifier-free body and bounded binders.
    fn exists_consequent(&self, term: TermId) -> Option<(TermId, TermId)> {
        self.bridge_orientations(term)
            .into_iter()
            .find(|(_, consequent)| match self.ctx.terms.get(*consequent) {
                TermData::Exists(bindings, ebody, _) => {
                    !bindings.is_empty()
                        && bindings.len() <= MAX_BINDERS
                        && !matches!(
                            self.ctx.terms.get(*ebody),
                            TermData::Forall(..) | TermData::Exists(..) | TermData::Let(..)
                        )
                        && !crate::ematching::contains_quantifier(&self.ctx.terms, *ebody)
                }
                _ => false,
            })
    }

    /// `(antecedent, consequent)` readings of an implication (or its
    /// desugared `or`) or of a Boolean equality, mirroring the implied
    /// lane's orientations so the stitcher's derivation accepts them.
    fn bridge_orientations(&self, term: TermId) -> Vec<(TermId, TermId)> {
        if let Some(reading) = Self::decode_implication_local(&self.ctx.terms, term) {
            return vec![reading];
        }
        match self.ctx.terms.get(term) {
            TermData::App(symbol, args)
                if symbol.name() == "="
                    && args.len() == 2
                    && matches!(self.ctx.terms.sort(args[0]), Sort::Bool) =>
            {
                vec![(args[0], args[1]), (args[1], args[0])]
            }
            _ => Vec::new(),
        }
    }

    /// Skolemize the bridge `exists` into the chain, returning its fresh
    /// witnesses by sort. Single-binder exists get one registered `sko`
    /// step; multi-binder ones go through the shared one-binder-at-a-time
    /// chain builder.
    fn skolemize_bridge_exists(
        &mut self,
        exists: TermId,
        chain: &mut Vec<ExpansionStep>,
    ) -> Option<Vec<(Sort, TermId)>> {
        let TermData::Exists(bindings, body, _) = self.ctx.terms.get(exists).clone() else {
            return None;
        };
        if bindings.len() >= 2 {
            let (witnesses, _) = crate::executor::qsat_route::skolemize_binders(
                &mut self.ctx.terms,
                exists,
                exists,
                true,
                chain,
            )
            .ok()?;
            return Some(
                bindings
                    .iter()
                    .map(|(_, sort)| sort.clone())
                    .zip(witnesses)
                    .collect(),
            );
        }
        let [(name, sort)] = bindings.as_slice() else {
            return None;
        };
        let witness = self
            .ctx
            .terms
            .mk_fresh_var(&format!("sk!{name}"), sort.clone());
        if let TermData::Var(fresh, _) = self.ctx.terms.get(witness).clone() {
            self.ctx.terms.mark_skolem_symbol(fresh);
        }
        let instance = crate::cegqi::lra_nested::tree::instantiate(
            &mut self.ctx.terms,
            body,
            &bindings,
            &[witness],
        )?;
        self.ctx.terms.register_skolem_choice(
            witness,
            ay_core::SkolemChoice {
                binder: name.clone(),
                sort: sort.clone(),
                body,
            },
        );
        chain.push(ExpansionStep::Skolem(
            crate::executor::SkolemInstanceRecord {
                source: exists,
                quantified: exists,
                witness,
                instance,
                asserted: instance,
                positive: true,
            },
        ));
        Some(vec![(sort.clone(), witness)])
    }

    /// Emit chain support deriving the bridge antecedent `a`, when a
    /// recorded instance's implication/equivalence reading yields `a`
    /// itself — or a congruent `a'` transported across a planned
    /// congruence equality — from an authored-derivable antecedent.
    /// Best-effort: no step is emitted when no support is found, and the
    /// stitcher then declines at the antecedent (fail-closed).
    fn plan_antecedent_support(
        &mut self,
        antecedent: TermId,
        derivable: &ay_core::kani_compat::DetHashSet<TermId>,
        known: &ay_core::kani_compat::DetHashSet<TermId>,
        chain: &mut Vec<ExpansionStep>,
    ) {
        if derivable.contains(&antecedent) {
            return;
        }
        for record in self.ematching_proof_records.clone() {
            if chain.len() >= MAX_CHAIN_STEPS {
                return;
            }
            for (ant_j, cons_j) in self.bridge_orientations(record.instance) {
                if !derivable.contains(&ant_j) {
                    continue;
                }
                if cons_j == antecedent {
                    chain.push(ExpansionStep::Forall(
                        crate::ematching::ForallInstantiationProvenance {
                            quantifier: record.quantifier,
                            binding: record.binding.clone(),
                            instance: record.instance,
                        },
                    ));
                    chain.push(ExpansionStep::Implied {
                        implication: record.instance,
                        antecedent: ant_j,
                        consequent: antecedent,
                    });
                    return;
                }
                if matches!(self.ctx.terms.sort(antecedent), Sort::Bool)
                    && self.congruence_candidate(cons_j, antecedent, known)
                {
                    let transport =
                        self.ctx
                            .terms
                            .mk_app(Symbol::named("="), [cons_j, antecedent], Sort::Bool);
                    chain.push(ExpansionStep::Forall(
                        crate::ematching::ForallInstantiationProvenance {
                            quantifier: record.quantifier,
                            binding: record.binding.clone(),
                            instance: record.instance,
                        },
                    ));
                    chain.push(ExpansionStep::Implied {
                        implication: record.instance,
                        antecedent: ant_j,
                        consequent: cons_j,
                    });
                    chain.push(ExpansionStep::Congruence {
                        equality: transport,
                    });
                    chain.push(ExpansionStep::Implied {
                        implication: transport,
                        antecedent: cons_j,
                        consequent: antecedent,
                    });
                    return;
                }
            }
        }
    }

    /// Whether `a` and `b` are structurally congruent: same application
    /// spine, with every differing leaf pair's equality already known
    /// (authored/recorded) or recursively congruent. The stitcher's
    /// congruence derivation is the authority; this only avoids
    /// proposing transports it cannot possibly discharge.
    fn congruence_candidate(
        &self,
        a: TermId,
        b: TermId,
        known: &ay_core::kani_compat::DetHashSet<TermId>,
    ) -> bool {
        if a == b {
            return true;
        }
        if self.ctx.terms.sort(a) != self.ctx.terms.sort(b) {
            return false;
        }
        let (a_head, a_args) = match self.bridge_application(a) {
            Some(parts) => parts,
            None => return self.known_equality(a, b, known),
        };
        let Some((b_head, b_args)) = self.bridge_application(b) else {
            return self.known_equality(a, b, known);
        };
        a_head == b_head
            && a_args.len() == b_args.len()
            && a_args
                .iter()
                .zip(&b_args)
                .all(|(&x, &y)| x == y || self.congruence_candidate(x, y, known))
    }

    fn known_equality(
        &self,
        a: TermId,
        b: TermId,
        known: &ay_core::kani_compat::DetHashSet<TermId>,
    ) -> bool {
        // Equality terms are not order-canonicalized on mint, so probe
        // membership by scanning the (bounded) known set for either
        // orientation instead of interning a candidate from `&self`.
        known.iter().any(|&term| match self.ctx.terms.get(term) {
            TermData::App(symbol, args) if symbol.name() == "=" && args.len() == 2 => {
                (args[0] == a && args[1] == b) || (args[0] == b && args[1] == a)
            }
            _ => false,
        })
    }

    fn bridge_application(&self, term: TermId) -> Option<(BridgeHead, Vec<TermId>)> {
        match self.ctx.terms.get(term).clone() {
            TermData::App(symbol, args) => Some((BridgeHead::App(symbol), args)),
            TermData::Ite(condition, then_branch, else_branch) => {
                Some((BridgeHead::Ite, vec![condition, then_branch, else_branch]))
            }
            TermData::Not(inner) => Some((BridgeHead::Not, vec![inner])),
            _ => None,
        }
    }
}

#[derive(PartialEq, Eq)]
enum BridgeHead {
    App(Symbol),
    Ite,
    Not,
}

#[cfg(test)]
#[path = "authored_exists_bridge_chain_tests.rs"]
mod tests;
