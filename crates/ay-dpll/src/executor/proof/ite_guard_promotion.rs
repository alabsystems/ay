// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Certified rebuild of Boolean-ITE guard-clause trust leaves
//! (#ite-guard-promotion, the frame-quantifier consequence-replay probes).
//!
//! THE GAP THIS CLOSES. An asserted formula-level ITE `(ite c A B)` — the
//! exact shape of every Shannon-lifted update-axiom instance
//! `ite(k=1, val = snew[k], snew[k] = s[k])` handed to the same-context
//! consequence-replay probe — is clausified by preprocessing into the two
//! guard clauses `(or (not c') A)` and `(or c' B)` (`c'` the condition,
//! possibly with canonically swapped equality arguments). Neither clause is a
//! problem premise, so proof export demotes both assumes to premiseless
//! `trust` steps, `check_proof_strict` rejects the whole refutation ("step tN
//! uses unverified trust rule"), and a genuine ground UNSAT fails
//! certification. Measured on the same-context consequence-replay probe of
//! `group_quantifiers::frame_quantifier_instance_resolve`: the probe
//! re-solves the consequence set to UNSAT and then discards it over exactly
//! these leaves.
//!
//! THE FIX IS A DERIVATION, NOT A RELAXATION. Each guard clause is re-derived
//! from its authored root with rules the UNTOUCHED strict checker already
//! validates:
//!
//! ```text
//! t1: assume (cl (ite c A B))                  ; problem premise only
//! t2: ite1 (cl c B)      |  ite2 (cl (not c) A)
//! t3+: eq_symmetric + equiv_pos2 + resolutions ; only when the clausifier
//!                                              ; swapped the condition's
//!                                              ; equality arguments
//! t4+: or_neg + resolutions + contraction to the unit (cl (or ...))
//! ```
//!
//! Fail-closed on every doubt: the pass plans only premiseless unit `trust`
//! steps whose clause is a two-literal `or` matching a problem root's exact
//! guard-clause shape (by `TermId`, not spelling); anything else declines and
//! the whole rebuild commits only when the complete rebuilt proof passes the
//! strict checker — a leftover trust obligation reverts everything
//! byte-for-byte. UNSAT-only presentation work: no arm can produce or
//! influence a SAT grant. Kill switch: `--no-quant-unit-authority` (the
//! umbrella exact-proof derivation-authority switch) disables the pass.

use super::*;

/// Planning/scan bounds; this is a small proof-repair lane.
const MAX_ITE_GUARD_ROOTS: usize = 256;
const MAX_ITE_GUARD_PLANS: usize = 128;
const MAX_ITE_GUARD_PROOF_STEPS: usize = 50_000;

/// One recognized guard-clause trust leaf and its authorizing root.
#[derive(Clone)]
struct IteGuardPlan {
    /// The problem root `(ite c A B)`, a formula-level Boolean ite.
    root: TermId,
    /// The or-term the trust step concludes.
    or_term: TermId,
    /// `true`: `(or c' B)` via `ite1`; `false`: `(or (not c') A)` via `ite2`.
    guard_positive: bool,
    /// The or-clause's exact guard literal (`c'` or `(not c')`, where `c'`
    /// is the root's condition or its argument-swapped equality).
    guard_lit: TermId,
    /// The or-clause's exact branch literal (`B` or `A`, by `TermId`).
    branch_lit: TermId,
}

/// Whether `candidate` is `reference` itself or its argument-swapped binary
/// equality (the clausifier rebuilds conditions with the canonicalizing
/// constructor, which may reverse the substituted orientation).
fn same_equality_modulo_orientation(
    terms: &ay_core::TermStore,
    candidate: TermId,
    reference: TermId,
) -> bool {
    if candidate == reference {
        return true;
    }
    let (TermData::App(cs, cargs), TermData::App(rs, rargs)) =
        (terms.get(candidate), terms.get(reference))
    else {
        return false;
    };
    cs.name() == "="
        && rs.name() == "="
        && cargs.len() == 2
        && rargs.len() == 2
        && cargs[0] == rargs[1]
        && cargs[1] == rargs[0]
}

impl Executor {
    /// Replace recognized Boolean-ITE guard-clause `trust` leaves with
    /// checker-validated derivations from their authored roots, atomically.
    pub(super) fn promote_shannon_ite_guard_trust_leaves(&mut self, proof: &mut Proof) {
        if !crate::quant_unit_authority::quant_unit_authority_enabled() {
            return;
        }
        // Surface-override interplay is out of scope for this lane: the
        // shape it exists for (the native-API same-context probe) retains no
        // parsed source surface. Decline whole when overrides are active
        // rather than re-deriving the surface audit here.
        if self
            .last_proof_term_overrides
            .as_ref()
            .is_some_and(|overrides| !overrides.is_empty())
        {
            return;
        }
        if proof.steps.len() > MAX_ITE_GUARD_PROOF_STEPS {
            return;
        }

        // Candidate roots: the problem premises this proof may assume.
        let mut roots: Vec<TermId> = Vec::new();
        for term in self
            .proof_problem_assertions()
            .into_iter()
            .chain(self.proof_original_problem_assertions())
        {
            if !roots.contains(&term) {
                roots.push(term);
            }
            if roots.len() > MAX_ITE_GUARD_ROOTS {
                return;
            }
        }

        let mut plans: Vec<Option<IteGuardPlan>> = vec![None; proof.steps.len()];
        let mut planned = 0usize;
        for (index, step) in proof.steps.iter().enumerate() {
            let ProofStep::Step {
                rule: AletheRule::Trust,
                clause,
                premises,
                ..
            } = step
            else {
                continue;
            };
            if !premises.is_empty() {
                continue;
            }
            let [or_term] = clause.as_slice() else {
                continue;
            };
            let Some(plan) = Self::plan_ite_guard_leaf(&self.ctx.terms, &roots, *or_term) else {
                continue;
            };
            // Validate the chain in ISOLATION before admitting the plan: emit
            // it into a scratch proof (assume + tautology steps + resolutions)
            // and run the unchanged strict derivation checker over it. A chain
            // that does not check is dropped, leaving that leaf's `trust` step
            // byte-identical — the outer mandatory gate still sees it, so a
            // partial promotion can never conceal a trust obligation. This
            // per-chain gate (rather than a whole-proof one) is what lets this
            // pass compose with the later atomic EUF-leaf promotion: each
            // fixes defects the other's whole-proof gate would revert on.
            let mut scratch = Proof::new();
            let mut scratch_assumes: ay_core::kani_compat::DetHashMap<TermId, ProofId> =
                ay_core::kani_compat::DetHashMap::default();
            let unit = self.emit_ite_guard_chain(&mut scratch, &plan, &mut scratch_assumes);
            // The derivation checker demands a closed refutation; close the
            // scratch over the unit's own negation (scope authorization is
            // the outer problem-scope validator's job, not this shape check).
            let not_or_term = self.ctx.terms.mk_not_raw(*or_term);
            let negated = scratch.add_assume(not_or_term, None);
            let _ = scratch.add_resolution(Vec::new(), *or_term, negated, unit);
            if let Err(error) = self.check_proof_strict_derivation_with_datatypes(&scratch) {
                if ay_core::misc_cli_flags().trace_cegqi_attr {
                    eprintln!("[ite-guard-promo] chain declined t{index}: {error}");
                }
                continue;
            }
            planned += 1;
            if planned > MAX_ITE_GUARD_PLANS {
                return;
            }
            plans[index] = Some(plan);
        }
        if planned == 0 {
            return;
        }

        // Atomic rebuild: recognized leaves are replaced, everything else is
        // copied byte-for-byte with premise ids remapped mechanically.
        let mut rebuilt = Proof::new();
        let mut assume_ids: ay_core::kani_compat::DetHashMap<TermId, ProofId> =
            ay_core::kani_compat::DetHashMap::default();
        let mut remap: Vec<ProofId> = Vec::with_capacity(proof.steps.len());
        for (index, step) in proof.steps.iter().cloned().enumerate() {
            if let Some(plan) = &plans[index] {
                let plan = plan.clone();
                let unit = self.emit_ite_guard_chain(&mut rebuilt, &plan, &mut assume_ids);
                remap.push(unit);
                continue;
            }
            let remap_id = |id: ProofId| remap.get(id.0 as usize).copied().unwrap_or(id);
            let step = match step {
                ProofStep::Resolution {
                    clause,
                    pivot,
                    clause1,
                    clause2,
                } => ProofStep::Resolution {
                    clause,
                    pivot,
                    clause1: remap_id(clause1),
                    clause2: remap_id(clause2),
                },
                ProofStep::Step {
                    rule,
                    clause,
                    premises,
                    args,
                } => ProofStep::Step {
                    rule,
                    clause,
                    premises: premises.into_iter().map(remap_id).collect(),
                    args,
                },
                other => other,
            };
            if let ProofStep::Assume(term) = &step {
                let term = *term;
                let id = rebuilt.add_step(step);
                assume_ids.entry(term).or_insert(id);
                remap.push(id);
                continue;
            }
            remap.push(rebuilt.add_step(step));
        }
        let mut remapped_named = proof.named_steps.clone();
        remapped_named.retain(|_, id| {
            let old_idx = id.0 as usize;
            if !matches!(proof.steps.get(old_idx), Some(ProofStep::Assume(_))) {
                return false;
            }
            let Some(new_id) = remap.get(old_idx) else {
                return false;
            };
            *id = *new_id;
            true
        });
        rebuilt.named_steps = remapped_named;

        // Every admitted chain was strict-checked in isolation and concludes
        // exactly the clause of the `trust` step it replaces, so the rebuild
        // preserves every other step's validity verbatim; committing without
        // a whole-proof gate cannot conceal anything — the outer mandatory
        // strict certification still re-decides the complete proof.
        *proof = rebuilt;
    }

    /// Recognize one guard-clause or-term against the candidate roots.
    fn plan_ite_guard_leaf(
        terms: &ay_core::TermStore,
        roots: &[TermId],
        or_term: TermId,
    ) -> Option<IteGuardPlan> {
        let TermData::App(symbol, disjuncts) = terms.get(or_term) else {
            return None;
        };
        if symbol.name() != "or" || disjuncts.len() != 2 {
            return None;
        }
        let [first, second] = [disjuncts[0], disjuncts[1]];
        if first == second {
            return None;
        }
        for &root in roots {
            let TermData::Ite(cond, then_f, else_f) = *terms.get(root) else {
                continue;
            };
            if *terms.sort(root) != Sort::Bool {
                continue;
            }
            // A negated condition would make the clausifier's guard literal a
            // folded double negation `ite2` cannot re-derive; decline.
            if matches!(terms.get(cond), TermData::Not(_)) {
                continue;
            }
            for (lit_guard, lit_branch) in [(first, second), (second, first)] {
                // Guard-positive: {c', B} concluded by ite1.
                if lit_branch == else_f && same_equality_modulo_orientation(terms, lit_guard, cond)
                {
                    return Some(IteGuardPlan {
                        root,
                        or_term,
                        guard_positive: true,
                        guard_lit: lit_guard,
                        branch_lit: lit_branch,
                    });
                }
                // Guard-negative: {(not c'), A} concluded by ite2.
                if lit_branch == then_f {
                    if let TermData::Not(guard_atom) = terms.get(lit_guard) {
                        if same_equality_modulo_orientation(terms, *guard_atom, cond) {
                            return Some(IteGuardPlan {
                                root,
                                or_term,
                                guard_positive: false,
                                guard_lit: lit_guard,
                                branch_lit: lit_branch,
                            });
                        }
                    }
                }
            }
        }
        None
    }

    /// Emit the checked derivation for one planned guard clause, leaving the
    /// unit `(cl or_term)`.
    fn emit_ite_guard_chain(
        &mut self,
        rebuilt: &mut Proof,
        plan: &IteGuardPlan,
        assume_ids: &mut ay_core::kani_compat::DetHashMap<TermId, ProofId>,
    ) -> ProofId {
        let TermData::Ite(cond, _, _) = *self.ctx.terms.get(plan.root) else {
            unreachable!("plan recognition fixed the root shape");
        };
        let assume_root = *assume_ids
            .entry(plan.root)
            .or_insert_with(|| rebuilt.add_assume(plan.root, None));
        let root_guard_literal = if plan.guard_positive {
            cond
        } else {
            self.ctx.terms.mk_not_raw(cond)
        };
        let mut guard_clause = rebuilt.add_rule_step(
            if plan.guard_positive {
                AletheRule::Ite1
            } else {
                AletheRule::Ite2
            },
            vec![root_guard_literal, plan.branch_lit],
            vec![assume_root],
            Vec::new(),
        );

        // The clausifier may store the condition with canonically swapped
        // equality arguments; bridge the root's exact condition to the
        // or-clause's literal with the checked `eq_symmetric` equivalence.
        if plan.guard_lit != root_guard_literal {
            if plan.guard_positive {
                // Held `(cl cond B)`; target literal `c'` (swapped).
                // `eq_symmetric` proves `(= cond c')`; `equiv_pos2` yields
                // `(cl (not (= cond c')) (not cond) c')`; two resolutions
                // leave `(cl c' B)`.
                let symmetry_eq =
                    self.ctx
                        .terms
                        .mk_app(Symbol::named("="), [cond, plan.guard_lit], Sort::Bool);
                let not_symmetry_eq = self.ctx.terms.mk_not_raw(symmetry_eq);
                let not_cond = self.ctx.terms.mk_not_raw(cond);
                let symmetry = rebuilt.add_rule_step(
                    AletheRule::EqSymmetric,
                    vec![symmetry_eq],
                    Vec::new(),
                    Vec::new(),
                );
                let tautology = rebuilt.add_rule_step(
                    AletheRule::EquivPos2,
                    vec![not_symmetry_eq, not_cond, plan.guard_lit],
                    Vec::new(),
                    Vec::new(),
                );
                let transfer = rebuilt.add_resolution(
                    vec![not_cond, plan.guard_lit],
                    symmetry_eq,
                    tautology,
                    symmetry,
                );
                guard_clause = rebuilt.add_resolution(
                    vec![plan.guard_lit, plan.branch_lit],
                    cond,
                    transfer,
                    guard_clause,
                );
            } else {
                // Held `(cl (not cond) A)`; target literal `(not g)` with `g`
                // the argument-swapped condition. `eq_symmetric` proves
                // `(= g cond)`; `equiv_pos2` yields
                // `(cl (not (= g cond)) (not g) cond)`; two resolutions leave
                // `(cl (not g) A)`.
                let TermData::Not(swapped_atom) = *self.ctx.terms.get(plan.guard_lit) else {
                    unreachable!("plan recognition fixed the negative guard shape");
                };
                let symmetry_eq =
                    self.ctx
                        .terms
                        .mk_app(Symbol::named("="), [swapped_atom, cond], Sort::Bool);
                let not_symmetry_eq = self.ctx.terms.mk_not_raw(symmetry_eq);
                let symmetry = rebuilt.add_rule_step(
                    AletheRule::EqSymmetric,
                    vec![symmetry_eq],
                    Vec::new(),
                    Vec::new(),
                );
                let tautology = rebuilt.add_rule_step(
                    AletheRule::EquivPos2,
                    vec![not_symmetry_eq, plan.guard_lit, cond],
                    Vec::new(),
                    Vec::new(),
                );
                let transfer = rebuilt.add_resolution(
                    vec![plan.guard_lit, cond],
                    symmetry_eq,
                    tautology,
                    symmetry,
                );
                guard_clause = rebuilt.add_resolution(
                    vec![plan.guard_lit, plan.branch_lit],
                    cond,
                    transfer,
                    guard_clause,
                );
            }
        }

        // Introduce the or-term and contract to its unit, exactly the
        // `emit_euf_lemma` or-unit pattern.
        let mut clause = vec![plan.guard_lit, plan.branch_lit];
        let mut cursor = guard_clause;
        for literal in [plan.guard_lit, plan.branch_lit] {
            let not_literal = self.ctx.terms.mk_not_raw(literal);
            let introduction = rebuilt.add_rule_step(
                AletheRule::OrNeg,
                vec![plan.or_term, not_literal],
                Vec::new(),
                Vec::new(),
            );
            if let Some(position) = clause.iter().position(|&l| l == literal) {
                let _ = clause.remove(position);
            }
            clause.push(plan.or_term);
            cursor = rebuilt.add_resolution(clause.clone(), literal, cursor, introduction);
        }
        rebuilt.add_rule_step(
            AletheRule::Contraction,
            vec![plan.or_term],
            vec![cursor],
            Vec::new(),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Executor with the single problem root `(ite (= a 1) p q)` (raw ite,
    /// raw condition orientation) plus the interesting derived terms.
    fn guard_fixture() -> (Executor, TermId, TermId, TermId, TermId, TermId) {
        let mut exec = Executor::new();
        let terms = &mut exec.ctx.terms;
        let a = terms.mk_var("iteguard_a", Sort::Int);
        let one = terms.mk_int(1.into());
        let p = terms.mk_var("iteguard_p", Sort::Bool);
        let q = terms.mk_var("iteguard_q", Sort::Bool);
        let cond = terms.mk_app(Symbol::named("="), [a, one], Sort::Bool);
        let swapped = terms.mk_app(Symbol::named("="), [one, a], Sort::Bool);
        let root = terms.mk_ite_raw(cond, p, q);
        exec.ctx.assertions = vec![root];
        (exec, root, cond, swapped, p, q)
    }

    fn strict_ok_after_closing(exec: &mut Executor, proof: &Proof, or_term: TermId) -> bool {
        let mut closed = proof.clone();
        let contraction = ProofId((closed.steps.len() - 1) as u32);
        let not_or = exec.ctx.terms.mk_not_raw(or_term);
        let negated = closed.add_assume(not_or, None);
        let _ = closed.add_resolution(Vec::new(), or_term, negated, contraction);
        exec.check_proof_strict_derivation_with_datatypes(&closed)
            .is_ok()
    }

    fn trust_count(proof: &Proof) -> usize {
        proof
            .steps
            .iter()
            .filter(|step| {
                matches!(
                    step,
                    ProofStep::Step {
                        rule: AletheRule::Trust,
                        ..
                    }
                )
            })
            .count()
    }

    /// The clausifier's guard-positive clause `(or (= 1 a) q)` — condition
    /// with swapped equality arguments — must rebuild strict-valid via
    /// `ite1` plus the `eq_symmetric` bridge.
    #[test]
    fn promotes_swapped_guard_positive_clause_to_strict_chain() {
        let (mut exec, root, _cond, swapped, _p, q) = guard_fixture();
        let or_term = exec
            .ctx
            .terms
            .mk_app(Symbol::named("or"), [swapped, q], Sort::Bool);
        let mut proof = Proof::new();
        let _ = proof.add_rule_step(AletheRule::Trust, vec![or_term], Vec::new(), Vec::new());

        exec.promote_shannon_ite_guard_trust_leaves(&mut proof);

        assert_eq!(trust_count(&proof), 0, "the trust leaf must be rebuilt");
        assert!(
            proof
                .steps
                .iter()
                .any(|step| matches!(step, ProofStep::Assume(term) if *term == root)),
            "the chain must assume exactly the authored root"
        );
        assert!(
            proof.steps.iter().any(|step| matches!(
                step,
                ProofStep::Step {
                    rule: AletheRule::Ite1,
                    ..
                }
            )),
            "the guard-positive chain derives through ite1"
        );
        assert!(
            strict_ok_after_closing(&mut exec, &proof, or_term),
            "the emitted chain must pass the unchanged strict checker"
        );
    }

    /// The guard-negative clause `(or (not (= 1 a)) p)` must rebuild via
    /// `ite2` plus the `eq_symmetric` bridge.
    #[test]
    fn promotes_swapped_guard_negative_clause_to_strict_chain() {
        let (mut exec, _root, _cond, swapped, p, _q) = guard_fixture();
        let not_swapped = exec.ctx.terms.mk_not_raw(swapped);
        let or_term = exec
            .ctx
            .terms
            .mk_app(Symbol::named("or"), [not_swapped, p], Sort::Bool);
        let mut proof = Proof::new();
        let _ = proof.add_rule_step(AletheRule::Trust, vec![or_term], Vec::new(), Vec::new());

        exec.promote_shannon_ite_guard_trust_leaves(&mut proof);

        assert_eq!(trust_count(&proof), 0, "the trust leaf must be rebuilt");
        assert!(
            proof.steps.iter().any(|step| matches!(
                step,
                ProofStep::Step {
                    rule: AletheRule::Ite2,
                    ..
                }
            )),
            "the guard-negative chain derives through ite2"
        );
        assert!(
            strict_ok_after_closing(&mut exec, &proof, or_term),
            "the emitted chain must pass the unchanged strict checker"
        );
    }

    /// GUARD-REMOVAL PROOF (branch pairing): `(or c then)` pairs the POSITIVE
    /// guard with the THEN branch — not a consequence of the root — and must
    /// stay an untouched trust leaf. Dropping the `lit_branch == else_f`
    /// pairing check makes this fail.
    #[test]
    fn mispaired_guard_clause_is_never_promoted() {
        let (mut exec, _root, cond, _swapped, p, _q) = guard_fixture();
        let or_term = exec
            .ctx
            .terms
            .mk_app(Symbol::named("or"), [cond, p], Sort::Bool);
        let mut proof = Proof::new();
        let _ = proof.add_rule_step(AletheRule::Trust, vec![or_term], Vec::new(), Vec::new());

        exec.promote_shannon_ite_guard_trust_leaves(&mut proof);

        assert_eq!(
            trust_count(&proof),
            1,
            "an or-term that is not a guard-clause consequence of any root \
             must be left byte-identical"
        );
    }

    /// GUARD-REMOVAL PROOF (kill switch): `--no-quant-unit-authority` must
    /// disable the whole pass.
    #[test]
    fn ite_guard_promotion_respects_the_kill_switch() {
        let (mut exec, _root, _cond, swapped, _p, q) = guard_fixture();
        let or_term = exec
            .ctx
            .terms
            .mk_app(Symbol::named("or"), [swapped, q], Sort::Bool);
        let mut proof = Proof::new();
        let _ = proof.add_rule_step(AletheRule::Trust, vec![or_term], Vec::new(), Vec::new());

        let off = ay_core::MiscCliFlags {
            no_quant_unit_authority: true,
            ..Default::default()
        };
        let _guard = ay_core::misc_test_override::set(off);
        exec.promote_shannon_ite_guard_trust_leaves(&mut proof);

        assert_eq!(
            trust_count(&proof),
            1,
            "the umbrella kill switch must leave the trust leaf untouched"
        );
    }
}
