// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl Executor {
    /// Rebuild a refutation whose whole content is EQUALITY REASONING over the
    /// exact authored roots (#trust-count→0, the `dt_and_term` / `check-sat-assuming`
    /// / constructor-congruence family).
    ///
    /// The shape this closes is a conjunction (or a set of roots) whose
    /// equalities chain two terms together that cannot be equal:
    ///
    /// ```text
    ///   (assert (and (= red c1) (= blue c1)))          ; red, blue distinct ctors
    ///   (assert (= m1 (just x))) (assert (= nothing m2)) (assert (= m1 m2))
    ///   (assert (= result (Accept claimed))) (assert (= actual claimed))
    ///   (assert (not (= result (Accept actual))))
    /// ```
    ///
    /// AY decides every one of these as `unsat`, but the refutation is reached
    /// inside the congruence closure / datatype solver, which publishes the
    /// conflict as ONE `Generic` (trust) clause — typically the bare negation of
    /// the authored conjunction, e.g.
    /// `(cl (not (and (= red c1) (= blue c1))))`. That clause carries no
    /// argument, so strict mode must reject it
    /// (`unsupported theory lemma kind Generic` / `unverified trust rule`),
    /// discharging it is re-proving the problem, and the mandatory publication
    /// gate correctly degrades a correct `unsat` to `unknown`.
    ///
    /// THE FIX IS A DERIVATION, NOT A RELAXATION. Every inference this pass uses
    /// already has an independent strict validator in `ay-proof`, and the
    /// producer states nothing the checker does not re-derive from the clause:
    ///
    ///  * `and_pos` + resolution to project a conjunct out of an authored root
    ///    (`boolean::validate_and_pos`);
    ///  * [`AletheRule::EqTransitive`] — `validate_euf_transitive` re-runs its OWN
    ///    BFS over the premise equalities and rejects a conclusion its premises
    ///    do not chain to, and any redundant premise;
    ///  * [`AletheRule::EqCongruent`] — `validate_euf_congruent` re-checks that
    ///    both conclusion sides apply the SAME symbol at the SAME arity and that
    ///    premise `i` links argument position `i`;
    ///  * [`AletheRule::EqReflexive`] — `validate_eq_reflexive` re-checks that the
    ///    unit equality's two sides are the same term;
    ///  * [`AletheRule::Or`] + resolution, to clausify an exact authored
    ///    disjunction of disequalities and close it only after EVERY refuted
    ///    equality has been derived;
    ///  * [`TheoryLemmaKind::DatatypeDistinct`] — validated against the datatype
    ///    constructor REGISTRY, so two applications are declared unequal only when
    ///    the declarations say they are different constructors of one datatype.
    ///    Without declarations it fails closed.
    ///
    /// Saturation is a bounded, purely SYMBOLIC search first: derived equalities
    /// are recorded as recipes ([`AuthoredEqDerivation`]) with no proof steps
    /// emitted. Only once a closer fires is the dependency cone of THAT closer
    /// emitted, so the rebuilt proof contains no dead steps.
    ///
    /// Fail-closed at every level, exactly like
    /// [`Self::replace_with_exact_authored_store_permutation_refutation`]: it runs
    /// only on a proof the strict checker ALREADY rejects; every `assume` is an
    /// exact authored root; and the candidate replaces nothing until
    /// `validate_reachable_assumes_in_problem_scope`,
    /// `proof_derives_empty_clause` and the plain
    /// `check_proof_strict_with_datatypes` have all accepted it. A construction
    /// this pass gets wrong therefore costs completeness (the verdict stays
    /// `unknown`), never soundness.
    pub(super) fn replace_with_exact_authored_equality_closure_refutation(
        &mut self,
        proof: &mut Proof,
    ) {
        // Work bounds. This pass runs on every refutation the strict checker
        // rejects, and declining an oversized problem leaves today's behaviour
        // exactly as it is, so the bounds can only cost completeness.
        // The live verification-consumer snapshot-alias obligation has 33 distinct authored
        // roots after deduplication (72 source rows, most repeated equality
        // bridges). Keep a bounded margin above that exact observed shape.
        // Resource parity remains explicit: root collection is linear and is
        // followed by the independent 64-leaf / 96-universe / 192-derived /
        // 3-round caps below, so widening this admission count does not unbound
        // either pairwise saturation loop. Every emitted premise is still
        // checked against `authored`, and the completed candidate is committed
        // only after strict replay.
        const MAX_AUTHORED_ROOTS: usize = 64;
        const MAX_LEAVES: usize = 64;
        // `fmap_deref`-class WP obligations carry several independent
        // equality components. Pairwise saturation can produce well over 48
        // checked recipes before the two four-edge goal chains are complete.
        // 192 remains a hard completeness-only work bound; the emitted
        // dependency cone and the final strict gate retain soundness.
        const MAX_DERIVED: usize = 192;
        const MAX_ROUNDS: usize = 3;
        const MAX_UNIVERSE: usize = 96;

        if self.check_proof_strict_with_datatypes(proof).is_ok() {
            return;
        }
        let authored = self.exact_concrete_authored_scope();
        if authored.is_empty() || authored.len() > MAX_AUTHORED_ROOTS {
            return;
        }

        // 1. Conjunction leaves of the authored roots, each with the `and`-path
        //    that reaches it. A leaf is derivable from its root by `and_pos`
        //    projections alone, so nothing outside the authored scope enters.
        let mut leaves: Vec<AuthoredLeaf> = Vec::new();
        for &root in &authored {
            collect_authored_conjunction_leaves(
                &self.ctx.terms,
                root,
                root,
                &mut Vec::new(),
                &mut leaves,
                MAX_LEAVES,
            );
        }
        if leaves.len() > MAX_LEAVES {
            return;
        }

        // 2. Seed the derived-equality set with the leaves that ARE equalities,
        //    and collect the leaves that are DISEQUALITIES as closing targets.
        let mut derived: Vec<AuthoredDerivedEq> = Vec::new();
        let mut goals: Vec<AuthoredEqGoal> = Vec::new();
        for (index, leaf) in leaves.iter().enumerate() {
            if let Some((a, b)) = decode_eq_local(&self.ctx.terms, leaf.term) {
                if a != b {
                    push_authored_derived_eq(
                        &mut derived,
                        AuthoredDerivedEq {
                            eq: leaf.term,
                            a,
                            b,
                            derivation: AuthoredEqDerivation::Leaf(index),
                        },
                    );
                }
                continue;
            }
            if let TermData::Not(inner) = self.ctx.terms.get(leaf.term) {
                let inner = *inner;
                if decode_eq_local(&self.ctx.terms, inner).is_some() {
                    goals.push(AuthoredEqGoal::Disequality {
                        equality: inner,
                        leaf: index,
                    });
                    continue;
                }
            }
            // A common WP postcondition shape is
            // `(or (not (= a x)) (not (= b y)))`: refuting it requires BOTH
            // equalities. Keep this narrowly structural and bounded. The
            // eventual `or` and resolution steps are checked independently;
            // a malformed or incomplete candidate cannot pass the final
            // strict commit gate.
            if let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(leaf.term) {
                const MAX_DISEQUALITY_DISJUNCTS: usize = 8;
                if name == "or" && (2..=MAX_DISEQUALITY_DISJUNCTS).contains(&args.len()) {
                    let mut equalities = Vec::with_capacity(args.len());
                    for &disjunct in args {
                        let TermData::Not(inner) = self.ctx.terms.get(disjunct) else {
                            equalities.clear();
                            break;
                        };
                        let inner = *inner;
                        if decode_eq_local(&self.ctx.terms, inner).is_none()
                            || equalities.contains(&inner)
                        {
                            equalities.clear();
                            break;
                        }
                        equalities.push(inner);
                    }
                    if !equalities.is_empty() {
                        goals.push(AuthoredEqGoal::DisequalityDisjunction {
                            equalities,
                            leaf: index,
                        });
                    }
                }
            }
        }
        if derived.is_empty() {
            return;
        }

        // 3. The congruence universe: every subterm of the authored roots. A
        //    congruence step may only conclude about applications the PROBLEM
        //    already mentions, which keeps the search finite and the rebuilt
        //    proof free of invented terms.
        let mut universe: Vec<TermId> = Vec::new();
        for &root in &authored {
            collect_authored_subterms(&self.ctx.terms, root, &mut universe, MAX_UNIVERSE);
        }
        if universe.len() > MAX_UNIVERSE {
            return;
        }

        // 4. Bounded saturation, then close. Closers are tried on the seeds and
        //    after every round, so the smallest refutation wins.
        for _ in 0..=MAX_ROUNDS {
            if let Some(candidate) =
                self.build_authored_equality_closure_candidate(&leaves, &derived, &goals)
            {
                if ay_proof::validate_reachable_assumes_in_problem_scope(&candidate, &authored)
                    .is_ok()
                    && Self::proof_derives_empty_clause(&candidate)
                    && self.check_proof_strict_with_datatypes(&candidate).is_ok()
                {
                    *proof = candidate;
                    return;
                }
            }
            if derived.len() >= MAX_DERIVED {
                return;
            }
            if !self.saturate_authored_equalities(&mut derived, &universe, MAX_DERIVED) {
                return;
            }
        }
    }

    /// One saturation round: extend `derived` with the transitivity and
    /// congruence consequences of what it already holds. Returns whether
    /// anything new was added (a fixpoint ends the search).
    ///
    /// Purely symbolic — no proof step is emitted here. Each new entry records
    /// only the RECIPE that justifies it; the corresponding strict-checked step
    /// is built later, and only if that entry ends up in a closer's cone.
    fn saturate_authored_equalities(
        &mut self,
        derived: &mut Vec<AuthoredDerivedEq>,
        universe: &[TermId],
        max_derived: usize,
    ) -> bool {
        let mut added = false;
        let existing = derived.len();

        // Transitivity: two derived equalities sharing an endpoint.
        for left in 0..existing {
            for right in (left + 1)..existing {
                if derived.len() >= max_derived {
                    return added;
                }
                let (la, lb) = (derived[left].a, derived[left].b);
                let (ra, rb) = (derived[right].a, derived[right].b);
                let endpoints = [
                    (la == ra, lb, rb),
                    (la == rb, lb, ra),
                    (lb == ra, la, rb),
                    (lb == rb, la, ra),
                ];
                for (shares, first, second) in endpoints {
                    if !shares || first == second {
                        continue;
                    }
                    let Some(eq) = self.authored_equality_term(first, second) else {
                        continue;
                    };
                    added |= push_authored_derived_eq(
                        derived,
                        AuthoredDerivedEq {
                            eq,
                            a: first,
                            b: second,
                            derivation: AuthoredEqDerivation::Transitive { left, right },
                        },
                    );
                    break;
                }
            }
        }

        // Congruence: two applications of the same symbol whose argument
        // positions are pairwise identical or already linked.
        for (left_index, &left) in universe.iter().enumerate() {
            let TermData::App(left_symbol, left_args) = self.ctx.terms.get(left) else {
                continue;
            };
            let (left_symbol, left_args) = (left_symbol.clone(), left_args.clone());
            if left_args.is_empty() {
                continue;
            }
            for &right in universe.iter().skip(left_index + 1) {
                if derived.len() >= max_derived {
                    return added;
                }
                let TermData::App(right_symbol, right_args) = self.ctx.terms.get(right) else {
                    continue;
                };
                if *right_symbol != left_symbol || right_args.len() != left_args.len() {
                    continue;
                }
                if self.ctx.terms.sort(left) != self.ctx.terms.sort(right) {
                    continue;
                }
                let right_args = right_args.clone();
                let mut positions: Vec<Option<usize>> = Vec::with_capacity(left_args.len());
                for (&argument_left, &argument_right) in left_args.iter().zip(right_args.iter()) {
                    if argument_left == argument_right {
                        positions.push(None);
                        continue;
                    }
                    let Some(index) = derived.iter().position(|entry| {
                        (entry.a == argument_left && entry.b == argument_right)
                            || (entry.a == argument_right && entry.b == argument_left)
                    }) else {
                        positions.clear();
                        break;
                    };
                    positions.push(Some(index));
                }
                if positions.len() != left_args.len() {
                    continue;
                }
                // An all-reflexive "congruence" concludes `(= t t)`, which is
                // reflexivity, not a new fact; skip it.
                if positions.iter().all(Option::is_none) {
                    continue;
                }
                let Some(eq) = self.authored_equality_term(left, right) else {
                    continue;
                };
                added |= push_authored_derived_eq(
                    derived,
                    AuthoredDerivedEq {
                        eq,
                        a: left,
                        b: right,
                        derivation: AuthoredEqDerivation::Congruent {
                            left,
                            right,
                            positions,
                        },
                    },
                );
            }
        }
        added
    }

    /// The canonical equality term for two terms, or `None` when they are not
    /// the same sort.
    ///
    /// Built with `mk_app` on the SAME operand order `TermStore::mk_eq` interns
    /// with, so the result is the identical `TermId` the authored problem uses;
    /// `mk_eq` itself is unusable here because it constant-folds and expands
    /// `ite` equalities, which would silently change the term being proved.
    fn authored_equality_term(&mut self, left: TermId, right: TermId) -> Option<TermId> {
        if self.ctx.terms.sort(left) != self.ctx.terms.sort(right) {
            return None;
        }
        let (a, b) = if left < right {
            (left, right)
        } else {
            (right, left)
        };
        Some(
            self.ctx
                .terms
                .mk_app(Symbol::named("="), [a, b], Sort::Bool),
        )
    }

    /// Emit the refutation for the first closer that fires, or `None`.
    ///
    /// Two closers, both of which turn one derived equality into the empty
    /// clause:
    ///  * an authored DISEQUALITY leaf whose equality was derived; and
    ///  * a derived equality between two applications the datatype REGISTRY
    ///    says are different constructors of the same datatype.
    fn build_authored_equality_closure_candidate(
        &mut self,
        leaves: &[AuthoredLeaf],
        derived: &[AuthoredDerivedEq],
        goals: &[AuthoredEqGoal],
    ) -> Option<Proof> {
        for (index, entry) in derived.iter().enumerate() {
            // Closer 1: the derived equality is exactly an authored disequality.
            let Some(leaf_index) = goals.iter().find_map(|goal| match goal {
                AuthoredEqGoal::Disequality { equality, leaf } if *equality == entry.eq => {
                    Some(*leaf)
                }
                _ => None,
            }) else {
                continue;
            };
            let mut builder = AuthoredEqProofBuilder::new(leaves, derived);
            let equality = builder.emit_derived(&mut self.ctx.terms, index)?;
            let disequality = builder.emit_leaf(&mut self.ctx.terms, leaf_index)?;
            let mut candidate = builder.finish();
            candidate.add_resolution(Vec::new(), entry.eq, equality, disequality);
            return Some(candidate);
        }

        // Closer 2: every disjunct of an exact authored `(or (not e1) ..)`
        // has been refuted by a derived equality. The builder clausifies that
        // exact authored root with `or`, then resolves each checked equality
        // unit against its matching disequality literal.
        for goal in goals {
            let AuthoredEqGoal::DisequalityDisjunction { equalities, leaf } = goal else {
                continue;
            };
            let mut sources = Vec::with_capacity(equalities.len());
            for equality in equalities {
                let Some(index) = derived.iter().position(|entry| entry.eq == *equality) else {
                    sources.clear();
                    break;
                };
                sources.push(index);
            }
            if sources.len() != equalities.len() {
                continue;
            }
            let mut builder = AuthoredEqProofBuilder::new(leaves, derived);
            builder.emit_disequality_disjunction(&mut self.ctx.terms, *leaf, &sources)?;
            return Some(builder.finish());
        }

        let datatype_decls = self.datatype_decls_for_strict_proof();
        if datatype_decls.is_empty() {
            return None;
        }
        for (index, entry) in derived.iter().enumerate() {
            // Closer 3: the two sides are DIFFERENT constructors of one
            // datatype. Whether they are is decided by the CHECKER'S OWN
            // registry-backed recognizer, never by this producer.
            let disequality_term = self.ctx.terms.mk_not_raw(entry.eq);
            if !ay_proof::recognize_datatype_distinct(
                &self.ctx.terms,
                &[disequality_term],
                &datatype_decls,
            ) {
                continue;
            }
            let mut builder = AuthoredEqProofBuilder::new(leaves, derived);
            let equality = builder.emit_derived(&mut self.ctx.terms, index)?;
            let mut candidate = builder.finish();
            let distinct = candidate.add_theory_lemma_with_kind(
                "datatype",
                vec![disequality_term],
                TheoryLemmaKind::DatatypeDistinct,
            );
            candidate.add_resolution(Vec::new(), entry.eq, equality, distinct);
            return Some(candidate);
        }
        None
    }
}

/// One conjunction leaf of an authored root, with the `and`-argument path that
/// reaches it. `path` is empty when the root IS the leaf.
///
/// Used by [`Executor::replace_with_exact_authored_equality_closure_refutation`],
/// whose every premise must be derivable from an exact authored root — a leaf is
/// reached by `and_pos` projections alone, so nothing outside the authored scope
/// can enter the rebuilt proof.
#[derive(Clone, Debug)]
struct AuthoredLeaf {
    root: TermId,
    path: Vec<u32>,
    term: TermId,
}

/// An authored negative equality target. A direct disequality needs one
/// derived equality; an `or` of disequalities needs all of them.
#[derive(Clone, Debug)]
enum AuthoredEqGoal {
    Disequality {
        equality: TermId,
        leaf: usize,
    },
    DisequalityDisjunction {
        equalities: Vec<TermId>,
        leaf: usize,
    },
}

/// How a derived equality was obtained. Recorded WITHOUT emitting proof steps so
/// saturation stays cheap; the corresponding strict-checked step is built only
/// for the entries inside a successful closer's dependency cone.
#[derive(Clone, Debug)]
enum AuthoredEqDerivation {
    /// The equality is an authored conjunction leaf (index into the leaf list).
    Leaf(usize),
    /// Two earlier derived equalities sharing an endpoint (`eq_transitive`).
    Transitive { left: usize, right: usize },
    /// Two applications of one symbol whose arguments are pairwise identical
    /// (`None`, discharged by `eq_reflexive`) or already linked (`Some(index)`),
    /// giving `eq_congruent`.
    Congruent {
        left: TermId,
        right: TermId,
        positions: Vec<Option<usize>>,
    },
}

/// A derived equality: the canonical equality term, its two sides, and its
/// recipe.
#[derive(Clone, Debug)]
struct AuthoredDerivedEq {
    eq: TermId,
    a: TermId,
    b: TermId,
    derivation: AuthoredEqDerivation,
}

/// Record `entry` unless an equality between the same two terms is already
/// known. Returns whether the set grew.
fn push_authored_derived_eq(
    derived: &mut Vec<AuthoredDerivedEq>,
    entry: AuthoredDerivedEq,
) -> bool {
    if derived.iter().any(|existing| existing.eq == entry.eq) {
        return false;
    }
    derived.push(entry);
    true
}

/// Flatten an authored root into its top-level `and` leaves, recording the
/// argument path to each. Bails out (leaving the caller's bound exceeded) rather
/// than walking an unbounded tree.
fn collect_authored_conjunction_leaves(
    terms: &TermStore,
    root: TermId,
    term: TermId,
    path: &mut Vec<u32>,
    out: &mut Vec<AuthoredLeaf>,
    limit: usize,
) {
    if out.len() > limit {
        return;
    }
    if let TermData::App(Symbol::Named(name), args) = terms.get(term) {
        if name == "and" {
            for (index, &child) in args.iter().enumerate() {
                path.push(index as u32);
                collect_authored_conjunction_leaves(terms, root, child, path, out, limit);
                path.pop();
            }
            return;
        }
    }
    out.push(AuthoredLeaf {
        root,
        path: path.clone(),
        term,
    });
}

/// Collect the distinct subterms of `term` into `out`, stopping once `limit` is
/// exceeded (the caller then declines the whole reconstruction).
fn collect_authored_subterms(terms: &TermStore, term: TermId, out: &mut Vec<TermId>, limit: usize) {
    if out.len() > limit || out.contains(&term) {
        return;
    }
    out.push(term);
    match terms.get(term) {
        TermData::App(_, args) => {
            let args = args.clone();
            for child in args {
                collect_authored_subterms(terms, child, out, limit);
            }
        }
        TermData::Not(inner) => {
            let inner = *inner;
            collect_authored_subterms(terms, inner, out, limit);
        }
        TermData::Ite(condition, then_branch, else_branch) => {
            let (condition, then_branch, else_branch) = (*condition, *then_branch, *else_branch);
            collect_authored_subterms(terms, condition, out, limit);
            collect_authored_subterms(terms, then_branch, out, limit);
            collect_authored_subterms(terms, else_branch, out, limit);
        }
        _ => {}
    }
}

/// Emits the strict-checkable steps behind a chosen closer, memoizing each
/// authored `assume` and each derived equality so a shared sub-derivation is
/// built once.
///
/// Every emitted derivation has UNIT clause shape — `[eq]` for a derived
/// equality, `[leaf]` for an authored conjunct — which is what lets the caller
/// close with a single resolution against the refuting lemma.
struct AuthoredEqProofBuilder<'a> {
    proof: Proof,
    leaves: &'a [AuthoredLeaf],
    derived: &'a [AuthoredDerivedEq],
    assumes: Vec<(TermId, ProofId)>,
    emitted_leaves: Vec<(usize, ProofId)>,
    emitted_derived: Vec<(usize, ProofId)>,
}

impl<'a> AuthoredEqProofBuilder<'a> {
    fn new(leaves: &'a [AuthoredLeaf], derived: &'a [AuthoredDerivedEq]) -> Self {
        Self {
            proof: Proof::new(),
            leaves,
            derived,
            assumes: Vec::new(),
            emitted_leaves: Vec::new(),
            emitted_derived: Vec::new(),
        }
    }

    fn finish(self) -> Proof {
        self.proof
    }

    /// The `assume` step for an exact authored root, created at most once.
    fn assume(&mut self, root: TermId) -> ProofId {
        if let Some(&(_, id)) = self.assumes.iter().find(|(term, _)| *term == root) {
            return id;
        }
        let id = self.proof.add_assume(root, None);
        self.assumes.push((root, id));
        id
    }

    /// Derive one authored conjunction leaf as a UNIT clause, projecting through
    /// each `and` on its path with `and_pos` + resolution.
    fn emit_leaf(&mut self, terms: &mut TermStore, index: usize) -> Option<ProofId> {
        if let Some(&(_, id)) = self.emitted_leaves.iter().find(|(at, _)| *at == index) {
            return Some(id);
        }
        let leaf = self.leaves.get(index)?.clone();
        let mut current = self.assume(leaf.root);
        let mut current_term = leaf.root;
        for &position in &leaf.path {
            let TermData::App(Symbol::Named(name), args) = terms.get(current_term) else {
                return None;
            };
            if name != "and" {
                return None;
            }
            let child = *args.get(position as usize)?;
            let negated = terms.mk_not_raw(current_term);
            let projection = self.proof.add_rule_step(
                AletheRule::AndPos(position),
                vec![negated, child],
                Vec::new(),
                vec![current_term],
            );
            current = self
                .proof
                .add_resolution(vec![child], current_term, projection, current);
            current_term = child;
        }
        if current_term != leaf.term {
            return None;
        }
        self.emitted_leaves.push((index, current));
        Some(current)
    }

    /// Close an exact authored disjunction of disequalities after the matching
    /// equality unit for every disjunct has been emitted.
    fn emit_disequality_disjunction(
        &mut self,
        terms: &mut TermStore,
        leaf_index: usize,
        derived_indices: &[usize],
    ) -> Option<ProofId> {
        let leaf_term = self.leaves.get(leaf_index)?.term;
        let TermData::App(Symbol::Named(name), args) = terms.get(leaf_term) else {
            return None;
        };
        if name != "or" || args.len() != derived_indices.len() {
            return None;
        }
        let clause = args.clone();
        let root = self.emit_leaf(terms, leaf_index)?;
        let mut current =
            self.proof
                .add_rule_step(AletheRule::Or, clause.clone(), vec![root], Vec::new());
        let mut residual = clause;
        for &derived_index in derived_indices {
            let equality = self.derived.get(derived_index)?.eq;
            let disequality = terms.mk_not_raw(equality);
            let at = residual
                .iter()
                .position(|literal| *literal == disequality)?;
            let _ = residual.remove(at);
            let equality_unit = self.emit_derived(terms, derived_index)?;
            current = self
                .proof
                .add_resolution(residual.clone(), equality, current, equality_unit);
        }
        residual.is_empty().then_some(current)
    }

    /// Derive one recorded equality as a UNIT clause `[eq]`.
    fn emit_derived(&mut self, terms: &mut TermStore, index: usize) -> Option<ProofId> {
        if let Some(&(_, id)) = self.emitted_derived.iter().find(|(at, _)| *at == index) {
            return Some(id);
        }
        let entry = self.derived.get(index)?.clone();
        let id = match entry.derivation {
            AuthoredEqDerivation::Leaf(leaf) => self.emit_leaf(terms, leaf)?,
            AuthoredEqDerivation::Transitive { left, right } => {
                let left_id = self.emit_derived(terms, left)?;
                let right_id = self.emit_derived(terms, right)?;
                let left_eq = self.derived.get(left)?.eq;
                let right_eq = self.derived.get(right)?.eq;
                let negated_left = terms.mk_not_raw(left_eq);
                let negated_right = terms.mk_not_raw(right_eq);
                // `validate_euf_transitive` re-runs its own BFS over these two
                // premise edges and independently rejects a conclusion they do
                // not chain to, so the ORDER here is presentation only.
                let chain = self.proof.add_rule_step(
                    AletheRule::EqTransitive,
                    vec![negated_left, negated_right, entry.eq],
                    Vec::new(),
                    Vec::new(),
                );
                let residual = self.proof.add_resolution(
                    vec![negated_right, entry.eq],
                    left_eq,
                    chain,
                    left_id,
                );
                self.proof
                    .add_resolution(vec![entry.eq], right_eq, residual, right_id)
            }
            AuthoredEqDerivation::Congruent {
                left,
                right,
                ref positions,
            } => {
                let TermData::App(_, left_args) = terms.get(left) else {
                    return None;
                };
                let left_args = left_args.clone();
                let TermData::App(_, right_args) = terms.get(right) else {
                    return None;
                };
                let right_args = right_args.clone();
                if left_args.len() != positions.len() || right_args.len() != positions.len() {
                    return None;
                }
                // One premise per argument position, in position order — the
                // shape `validate_euf_congruent` re-checks. A position whose two
                // arguments are the SAME term needs a raw `(= x x)`: the
                // canonical builder folds that to `true`, so it is interned
                // directly and discharged by `eq_reflexive` below.
                let mut premises: Vec<(TermId, ProofId)> = Vec::with_capacity(positions.len());
                for (position, slot) in positions.iter().enumerate() {
                    match *slot {
                        Some(source) => {
                            let id = self.emit_derived(terms, source)?;
                            premises.push((self.derived.get(source)?.eq, id));
                        }
                        None => {
                            let argument = *left_args.get(position)?;
                            let reflexive =
                                terms.mk_app(Symbol::named("="), [argument, argument], Sort::Bool);
                            let id = self.proof.add_rule_step(
                                AletheRule::EqReflexive,
                                vec![reflexive],
                                Vec::new(),
                                Vec::new(),
                            );
                            premises.push((reflexive, id));
                        }
                    }
                }
                let mut clause: Vec<TermId> = Vec::with_capacity(premises.len() + 1);
                for &(equality, _) in &premises {
                    let negated = terms.mk_not_raw(equality);
                    clause.push(negated);
                }
                clause.push(entry.eq);
                let mut current = self.proof.add_rule_step(
                    AletheRule::EqCongruent,
                    clause.clone(),
                    Vec::new(),
                    Vec::new(),
                );
                // Resolve the premises away one at a time. A repeated premise
                // equality contributes one literal per occurrence, so the
                // residual is recomputed by removing exactly one occurrence.
                let mut residual = clause;
                for (equality, premise) in premises {
                    let negated = terms.mk_not_raw(equality);
                    if let Some(at) = residual.iter().position(|&literal| literal == negated) {
                        let _ = residual.remove(at);
                    }
                    current =
                        self.proof
                            .add_resolution(residual.clone(), equality, current, premise);
                }
                current
            }
        };
        self.emitted_derived.push((index, id));
        Some(id)
    }
}
