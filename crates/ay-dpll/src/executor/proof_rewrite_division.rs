// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Auxiliary division variable analysis and demotion for proof rewriting.
//!
//! Identifies `_mod_q`/`_div_q`/`_divmod_q` (quotient) and
//! `_mod_r`/`_div_r`/`_divmod_r` (remainder) auxiliary variables
//! introduced by the LIA division encoding, infers division term rewrites,
//! and demotes non-problem assumptions to `trust` steps.
//!
//! Extracted from `proof_rewrite.rs` for code health (#5970).

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::Symbol;
use ay_core::term::TermData;
use ay_core::{
    AletheRule, Constant, FarkasAnnotation, Proof, ProofStep, TermId, TermStore, TheoryLemmaKind,
    TheoryLit,
};
use num_bigint::BigInt;

use super::Executor;

impl Executor {
    pub(in crate::executor) fn collect_assume_steps_with_aux_mod_div_vars(
        terms: &TermStore,
        proof: &Proof,
    ) -> HashSet<u32> {
        let mut out = HashSet::default();
        for (idx, step) in proof.steps.iter().enumerate() {
            if let ProofStep::Assume(term) = step {
                if Self::term_contains_aux_mod_div_var(terms, *term) {
                    out.insert(idx as u32);
                }
            }
        }
        out
    }

    pub(in crate::executor) fn infer_auxiliary_division_rewrites(
        terms: &mut TermStore,
        proof: &Proof,
        rewrites: &mut HashMap<TermId, TermId>,
    ) {
        for step in &proof.steps {
            let ProofStep::Assume(term) = step else {
                continue;
            };
            let Some((dividend, divisor, quotient, remainder)) =
                Self::parse_aux_division_constraint(terms, *term)
            else {
                continue;
            };
            let div_term = terms.mk_intdiv(dividend, divisor);
            let mod_term = terms.mk_mod(dividend, divisor);
            rewrites.insert(quotient, div_term);
            rewrites.insert(remainder, mod_term);
        }
    }

    fn parse_aux_division_constraint(
        terms: &mut TermStore,
        term: TermId,
    ) -> Option<(TermId, TermId, TermId, TermId)> {
        let (lhs, rhs) = match terms.get(term) {
            TermData::App(Symbol::Named(name), args) if name == "=" && args.len() == 2 => {
                (args[0], args[1])
            }
            _ => return None,
        };
        Self::parse_aux_division_rhs(terms, lhs, rhs)
            .or_else(|| Self::parse_aux_division_rhs(terms, rhs, lhs))
    }

    fn parse_aux_division_rhs(
        terms: &mut TermStore,
        dividend: TermId,
        rhs: TermId,
    ) -> Option<(TermId, TermId, TermId, TermId)> {
        let (lhs, rhs) = match terms.get(rhs) {
            TermData::App(Symbol::Named(name), args) if name == "+" && args.len() == 2 => {
                (args[0], args[1])
            }
            _ => return None,
        };
        Self::parse_aux_division_addend_pair(terms, dividend, lhs, rhs)
            .or_else(|| Self::parse_aux_division_addend_pair(terms, dividend, rhs, lhs))
    }

    fn parse_aux_division_addend_pair(
        terms: &mut TermStore,
        dividend: TermId,
        scaled_q: TermId,
        remainder: TermId,
    ) -> Option<(TermId, TermId, TermId, TermId)> {
        let (divisor, quotient) = Self::parse_scaled_aux_quotient(terms, scaled_q)?;
        let remainder = Self::as_aux_remainder_var(terms, remainder)?;
        Some((dividend, divisor, quotient, remainder))
    }

    fn parse_scaled_aux_quotient(terms: &mut TermStore, term: TermId) -> Option<(TermId, TermId)> {
        if let Some(q) = Self::as_aux_quotient_var(terms, term) {
            return Some((terms.mk_int(BigInt::from(1)), q));
        }
        let (lhs, rhs) = match terms.get(term) {
            TermData::App(Symbol::Named(name), args) if name == "*" && args.len() == 2 => {
                (args[0], args[1])
            }
            _ => return None,
        };
        if Self::is_int_const_term(terms, lhs) {
            return Self::as_aux_quotient_var(terms, rhs).map(|q| (lhs, q));
        }
        if Self::is_int_const_term(terms, rhs) {
            return Self::as_aux_quotient_var(terms, lhs).map(|q| (rhs, q));
        }
        None
    }

    fn as_aux_quotient_var(terms: &TermStore, term: TermId) -> Option<TermId> {
        let TermData::Var(name, _) = terms.get(term) else {
            return None;
        };
        (name.starts_with("_mod_q") || name.starts_with("_div_q") || name.starts_with("_divmod_q"))
            .then_some(term)
    }

    fn as_aux_remainder_var(terms: &TermStore, term: TermId) -> Option<TermId> {
        let TermData::Var(name, _) = terms.get(term) else {
            return None;
        };
        (name.starts_with("_mod_r") || name.starts_with("_div_r") || name.starts_with("_divmod_r"))
            .then_some(term)
    }

    fn is_int_const_term(terms: &TermStore, term: TermId) -> bool {
        matches!(terms.get(term), TermData::Const(Constant::Int(_)))
    }

    pub(in crate::executor) fn demote_auxiliary_non_problem_assumptions(
        proof: &mut Proof,
        problem_assertions: &[TermId],
        aux_assume_steps: &HashSet<u32>,
    ) {
        if aux_assume_steps.is_empty() {
            return;
        }
        debug_assert!(
            aux_assume_steps
                .iter()
                .all(|&idx| (idx as usize) < proof.steps.len()),
            "BUG: aux_assume_steps contains index beyond proof.steps.len() ({})",
            proof.steps.len()
        );
        let problem_set: HashSet<TermId> = problem_assertions.iter().copied().collect();
        for (idx, step) in proof.steps.iter_mut().enumerate() {
            if !aux_assume_steps.contains(&(idx as u32)) {
                continue;
            }
            let ProofStep::Assume(term) = step else {
                continue;
            };
            if problem_set.contains(term) {
                continue;
            }
            *step = ProofStep::Step {
                rule: AletheRule::Trust,
                clause: vec![*term],
                premises: Vec::new(),
                args: Vec::new(),
            };
        }
    }

    pub(in crate::executor) fn demote_non_problem_assumptions(
        proof: &mut Proof,
        problem_assertions: &[TermId],
    ) {
        let problem_set: HashSet<TermId> = problem_assertions.iter().copied().collect();
        for step in &mut proof.steps {
            let ProofStep::Assume(term) = step else {
                continue;
            };
            if problem_set.contains(term) {
                continue;
            }
            *step = ProofStep::Step {
                rule: AletheRule::Trust,
                clause: vec![*term],
                premises: Vec::new(),
                args: Vec::new(),
            };
        }
    }

    /// Derive non-problem conjunct assumptions from their problem-assertion
    /// roots BEFORE the demotion pass turns them into unverified `trust` steps.
    ///
    /// Top-level and-flattening asserts each conjunct of `(and ...)` problem
    /// assertions separately, so the proof's `Assume` steps carry the
    /// CONJUNCTS, not the asserted conjunction. Demoting those assumes to
    /// `trust` made the strict checker fail-close every trivially-UNSAT
    /// conjunctive query ("step t0 uses unverified trust rule").
    ///
    /// For each `Assume(t)` where `t` is NOT a problem assertion but IS a
    /// (possibly nested) conjunct of one, rebuild the proof so `(cl t)` is
    /// DERIVED: `(assume root)` + a per-nesting-level `and_pos` tautology
    /// (`(cl (not parent) child)`, axiomatic in Alethe, validated
    /// structurally by the strict checker) resolved via `th_resolution`.
    /// Assumes with no derivation root are left for the demotion pass — the
    /// fail-closed default for genuinely underivable inputs is unchanged.
    pub(in crate::executor) fn derive_conjunct_assumptions_from_problem_roots(
        terms: &mut TermStore,
        proof: &mut Proof,
        problem_assertions: &[TermId],
    ) {
        use ay_core::ProofId;

        let problem_set: HashSet<TermId> = problem_assertions.iter().copied().collect();

        // Positional path to `target` inside the (possibly nested) `and` tree.
        fn find_and_path(terms: &TermStore, root: TermId, target: TermId) -> Option<Vec<u32>> {
            if root == target {
                return Some(Vec::new());
            }
            let TermData::App(Symbol::Named(name), args) = terms.get(root) else {
                return None;
            };
            if name != "and" {
                return None;
            }
            let args = args.clone();
            for (i, arg) in args.into_iter().enumerate() {
                if let Some(mut path) = find_and_path(terms, arg, target) {
                    path.insert(0, u32::try_from(i).ok()?);
                    return Some(path);
                }
            }
            None
        }

        // All (conjunct, path) leaves of a root's and-tree.
        fn collect_and_leaves(
            terms: &TermStore,
            root: TermId,
            path: &mut Vec<u32>,
            out: &mut Vec<(TermId, Vec<u32>)>,
        ) {
            if let TermData::App(Symbol::Named(name), args) = terms.get(root) {
                if name == "and" {
                    let args = args.clone();
                    for (i, arg) in args.into_iter().enumerate() {
                        path.push(i as u32);
                        collect_and_leaves(terms, arg, path, out);
                        path.pop();
                    }
                    return;
                }
            }
            if !path.is_empty() {
                out.push((root, path.clone()));
            }
        }

        // A substituted conjunct: `target` equals conjunct C with exactly one
        // argument position rewritten x -> y, where `(= x y)` (either
        // orientation) is itself a conjunct E. Preprocessing variable
        // substitution produces exactly this shape (e.g. `(<= n5 i)` under
        // `(= len n5)` becomes `(<= len i)`).
        #[allow(clippy::type_complexity)]
        fn find_substituted_conjunct(
            terms: &TermStore,
            leaves: &[(TermId, TermId, Vec<u32>)],
            eq_leaf_index: &HashMap<(TermId, TermId), usize>,
            target: TermId,
        ) -> Option<(TermId, Vec<u32>, TermId, Vec<u32>, TermId)> {
            let TermData::App(Symbol::Named(t_name), t_args) = terms.get(target) else {
                return None;
            };
            for (c_root, c_term, c_path) in leaves {
                let TermData::App(Symbol::Named(c_name), c_args) = terms.get(*c_term) else {
                    continue;
                };
                if c_name != t_name || c_args.len() != t_args.len() {
                    continue;
                }
                let mut diffs = (0..t_args.len()).filter(|&k| c_args[k] != t_args[k]);
                let (Some(k), None) = (diffs.next(), diffs.next()) else {
                    continue;
                };
                let (from, to) = (c_args[k], t_args[k]);
                // Equality-conjunct lookup, orientation-insensitive. The
                // index maps the normalized pair to the FIRST matching `=`
                // leaf in `leaves` order — identical to the linear scan it
                // replaces (#proof-tax: the scan made this quadratic per
                // assume over the leaf list).
                let key = if from <= to { (from, to) } else { (to, from) };
                if let Some(&e_idx) = eq_leaf_index.get(&key) {
                    let (e_root, _, e_path) = &leaves[e_idx];
                    return Some((*c_root, c_path.clone(), *e_root, e_path.clone(), *c_term));
                }
            }
            None
        }

        // A theory-atom Boolean definition: `target` (or its negation) is one
        // side of a Boolean equality leaf E = `(= a b)` and the OTHER side
        // (with matching polarity) is itself a problem leaf L. The Tseitin
        // bridge `(= c atom), c ⊢ atom` (any polarity/orientation) is then a
        // real Alethe derivation: the premiseless `equiv_pos1`/`equiv_pos2`
        // tautology resolved against `(cl E)` and `(cl L)`. Previously these
        // assumes were demoted to unverifiable `:rule trust` steps.
        fn find_equiv_defined_atom(
            terms: &TermStore,
            leaves: &[(TermId, TermId, Vec<u32>)],
            target: TermId,
        ) -> Option<(TermId, Vec<u32>, TermId, TermId, Vec<u32>, bool, bool)> {
            let (atom, negated) = match terms.get(target) {
                TermData::Not(inner) => (*inner, true),
                _ => (target, false),
            };
            for (e_root, e_term, e_path) in leaves {
                if *e_term == target {
                    continue;
                }
                let TermData::App(Symbol::Named(e_name), e_args) = terms.get(*e_term) else {
                    continue;
                };
                if e_name != "=" || e_args.len() != 2 || e_args[0] == e_args[1] {
                    continue;
                }
                let (a, b) = (e_args[0], e_args[1]);
                // Both sides must be plain (non-negated, non-constant) Boolean
                // terms so the equiv_pos tautology literals `(not a)` / `(not b)`
                // are plain single negations (no not_not shape drift).
                let plain_bool = |t: TermId| {
                    matches!(terms.sort(t), ay_core::Sort::Bool)
                        && !matches!(terms.get(t), TermData::Not(_) | TermData::Const(_))
                };
                if !plain_bool(a) || !plain_bool(b) {
                    continue;
                }
                let (atom_is_first, other) = if a == atom {
                    (true, b)
                } else if b == atom {
                    (false, a)
                } else {
                    continue;
                };
                // The defining literal L: `other` for a positive target,
                // `(not other)` for a negated target.
                for (l_root, l_term, l_path) in leaves {
                    let l_matches = if negated {
                        matches!(terms.get(*l_term), TermData::Not(inner) if *inner == other)
                    } else {
                        *l_term == other
                    };
                    if l_matches {
                        return Some((
                            *e_root,
                            e_path.clone(),
                            *e_term,
                            *l_root,
                            l_path.clone(),
                            atom_is_first,
                            negated,
                        ));
                    }
                }
            }
            None
        }

        /// An arithmetic equality rewritten by preprocessing into the
        /// conjunction of its two non-strict directions.
        ///
        /// Recognition is semantic, not just syntactic: every target conjunct
        /// must form a checker-accepted `[1, 1]` Farkas clause
        /// `(cl (not equality) bound)`. This prevents a merely similar
        /// generated conjunction from acquiring proof authority.
        fn find_equality_bounds(
            terms: &mut TermStore,
            leaves: &[(TermId, TermId, Vec<u32>)],
            target: TermId,
        ) -> Option<(TermId, Vec<u32>, TermId, Vec<TermId>)> {
            let TermData::App(Symbol::Named(name), bounds) = terms.get(target) else {
                return None;
            };
            if name != "and" || bounds.len() < 2 {
                return None;
            }
            let bounds = bounds.clone();
            let unique: HashSet<TermId> = bounds.iter().copied().collect();
            if unique.len() != bounds.len() {
                return None;
            }

            for (root, equality, path) in leaves {
                let TermData::App(Symbol::Named(eq), args) = terms.get(*equality) else {
                    continue;
                };
                if eq != "="
                    || args.len() != 2
                    || !matches!(
                        terms.sort(args[0]),
                        ay_core::Sort::Int | ay_core::Sort::Real
                    )
                    || terms.sort(args[0]) != terms.sort(args[1])
                {
                    continue;
                }
                let farkas = FarkasAnnotation::from_ints(&[1, 1]);
                let every_bound_is_entailed = bounds.iter().all(|&bound| {
                    let lits = [
                        TheoryLit::new(*equality, true),
                        TheoryLit::new(bound, false),
                    ];
                    // This certificate is exported as stock Alethe
                    // `la_generic`, whose arithmetic fragment is linear.
                    // The broader checker can also justify nonlinear atoms
                    // through congruence, which Carcara's rule cannot.
                    ay_core::proof_validation::verify_farkas_conflict_lits_linear(
                        terms, &lits, &farkas,
                    )
                    .is_ok()
                });
                if every_bound_is_entailed {
                    return Some((*root, path.clone(), *equality, bounds));
                }
            }
            None
        }

        enum Derivation {
            // Direct conjunct of the root's and-tree.
            Conjunct(TermId, Vec<u32>),
            // Conjunct with one argument rewritten under an equality conjunct.
            // C and E may live in DIFFERENT assertion roots (the in-process
            // encode asserts top-level conjuncts separately).
            Substituted {
                c_root: TermId,
                c_path: Vec<u32>,
                e_root: TermId,
                e_path: Vec<u32>,
                c_term: TermId,
            },
            // Boolean atom defined by an equality leaf `(= a b)` plus the
            // defining literal leaf (see `find_equiv_defined_atom`).
            EquivDefined {
                e_root: TermId,
                e_path: Vec<u32>,
                e_term: TermId,
                l_root: TermId,
                l_path: Vec<u32>,
                atom_is_first: bool,
                negated: bool,
            },
            // Arithmetic equality split into an `and` of entailed non-strict
            // bounds. Each implication is independently Farkas-checked.
            EqualityBounds {
                e_root: TermId,
                e_path: Vec<u32>,
                equality: TermId,
                bounds: Vec<TermId>,
            },
        }

        // Cross-root substitution leaves: C and E may come from different
        // assertion roots. LOOP-INVARIANT and LAZY (#proof-tax): `terms` is
        // not mutated while scanning the assumes below, so the leaf list and
        // its equality index are built at most ONCE — on the first
        // non-problem assume that needs them — instead of re-collecting the
        // full and-tree of every root for every such assume (quadratic in
        // practice on the qg5 QF_UF family). Proofs whose assumes are all
        // problem assertions or direct conjuncts never pay for the build.
        type LeafList = Vec<(TermId, TermId, Vec<u32>)>;
        type EqLeafIndex = HashMap<(TermId, TermId), usize>;
        fn build_leaves_and_eq_index(
            terms: &TermStore,
            problem_assertions: &[TermId],
        ) -> (LeafList, EqLeafIndex) {
            let mut all_leaves: LeafList = Vec::new();
            for &root in problem_assertions {
                let mut leaves = Vec::new();
                collect_and_leaves(terms, root, &mut Vec::new(), &mut leaves);
                for (t, path) in leaves {
                    all_leaves.push((root, t, path));
                }
                // A root that is not an `and` is itself a unit conjunct usable
                // as C or E (path empty = the assume itself).
                if !matches!(
                    terms.get(root),
                    TermData::App(Symbol::Named(name), _) if name == "and"
                ) {
                    all_leaves.push((root, root, Vec::new()));
                }
            }
            // Orientation-normalized index of `=` leaves: (min, max) argument
            // pair -> FIRST matching leaf position in `all_leaves` order, so
            // `find_substituted_conjunct` resolves its equality conjunct in
            // O(1) with the exact first-match semantics of the linear scan
            // it replaces.
            let mut eq_leaf_index: EqLeafIndex = HashMap::default();
            for (leaf_idx, (_, leaf_term, _)) in all_leaves.iter().enumerate() {
                if let TermData::App(Symbol::Named(name), args) = terms.get(*leaf_term) {
                    if name == "=" && args.len() == 2 {
                        let (a, b) = (args[0], args[1]);
                        let key = if a <= b { (a, b) } else { (b, a) };
                        eq_leaf_index.entry(key).or_insert(leaf_idx);
                    }
                }
            }
            (all_leaves, eq_leaf_index)
        }
        let mut leaves_cache: Option<(LeafList, EqLeafIndex)> = None;

        let mut derivable: HashMap<usize, Derivation> = HashMap::default();
        for (idx, step) in proof.steps.iter().enumerate() {
            let ProofStep::Assume(term) = step else {
                continue;
            };
            if problem_set.contains(term) {
                continue;
            }
            let mut matched = false;
            for &root in problem_assertions {
                if let Some(path) = find_and_path(terms, root, *term) {
                    if !path.is_empty() {
                        derivable.insert(idx, Derivation::Conjunct(root, path));
                        matched = true;
                        break;
                    }
                }
            }
            if matched {
                continue;
            }
            let (all_leaves, eq_leaf_index) = leaves_cache
                .get_or_insert_with(|| build_leaves_and_eq_index(terms, problem_assertions));
            if let Some((c_root, c_path, e_root, e_path, c_term)) =
                find_substituted_conjunct(terms, all_leaves, eq_leaf_index, *term)
            {
                derivable.insert(
                    idx,
                    Derivation::Substituted {
                        c_root,
                        c_path,
                        e_root,
                        e_path,
                        c_term,
                    },
                );
                continue;
            }
            if let Some((e_root, e_path, equality, bounds)) =
                find_equality_bounds(terms, all_leaves, *term)
            {
                derivable.insert(
                    idx,
                    Derivation::EqualityBounds {
                        e_root,
                        e_path,
                        equality,
                        bounds,
                    },
                );
                continue;
            }
            if let Some((e_root, e_path, e_term, l_root, l_path, atom_is_first, negated)) =
                find_equiv_defined_atom(terms, all_leaves, *term)
            {
                derivable.insert(
                    idx,
                    Derivation::EquivDefined {
                        e_root,
                        e_path,
                        e_term,
                        l_root,
                        l_path,
                        atom_is_first,
                        negated,
                    },
                );
            }
        }
        if derivable.is_empty() {
            return;
        }

        // Linear rebuild with an old->new id map so every reference stays
        // backward (Alethe and both checkers require premises before use).
        let old_steps = std::mem::take(&mut proof.steps);
        let mut new_proof = Proof::new();
        let mut id_map: Vec<ProofId> = Vec::with_capacity(old_steps.len());
        // One assume per distinct root, shared across its conjuncts.
        let mut root_assumes: HashMap<TermId, ProofId> = HashMap::default();

        fn remap(id: ProofId, id_map: &[ProofId]) -> ProofId {
            id_map.get(id.0 as usize).copied().unwrap_or(id)
        }

        // Emit the and_pos + th_resolution chain deriving the conjunct at
        // `path` from `assume_id : (cl root)`. Returns the (cl conjunct) id.
        fn emit_conjunct_chain(
            terms: &mut TermStore,
            new_proof: &mut Proof,
            assume_id: ProofId,
            root: TermId,
            path: &[u32],
        ) -> ProofId {
            let mut current_id = assume_id;
            let mut current_term = root;
            for &pos in path {
                let TermData::App(_, args) = terms.get(current_term) else {
                    unreachable!("find_and_path returned a non-and path segment");
                };
                let child = args[pos as usize];
                let not_parent = terms.mk_not(current_term);
                let and_pos_id = new_proof.add_rule_step(
                    AletheRule::AndPos(pos),
                    vec![not_parent, child],
                    Vec::new(),
                    vec![current_term],
                );
                current_id = new_proof.add_rule_step(
                    AletheRule::ThResolution,
                    vec![child],
                    vec![and_pos_id, current_id],
                    Vec::new(),
                );
                current_term = child;
            }
            current_id
        }

        for (idx, step) in old_steps.into_iter().enumerate() {
            if let Some(derivation) = derivable.get(&idx) {
                let target = match &step {
                    ProofStep::Assume(t) => *t,
                    _ => unreachable!("derivable indexes only Assume steps"),
                };
                let derived_id = match derivation {
                    Derivation::Conjunct(root, path) => {
                        let assume_id = *root_assumes
                            .entry(*root)
                            .or_insert_with(|| new_proof.add_assume(*root, None));
                        emit_conjunct_chain(terms, &mut new_proof, assume_id, *root, path)
                    }
                    Derivation::Substituted {
                        c_root,
                        c_path,
                        e_root,
                        e_path,
                        c_term,
                    } => {
                        // (cl C) and (cl E) from the root, then bridge to the
                        // substituted unit with a Farkas-certified LIA lemma
                        // (cl (not E) (not C) target) — validated SEMANTICALLY
                        // by the strict checker, so a wrong bridge can only be
                        // Rejected (fail-closed), never falsely accepted.
                        let c_assume = *root_assumes
                            .entry(*c_root)
                            .or_insert_with(|| new_proof.add_assume(*c_root, None));
                        let c_id =
                            emit_conjunct_chain(terms, &mut new_proof, c_assume, *c_root, c_path);
                        let e_assume = *root_assumes
                            .entry(*e_root)
                            .or_insert_with(|| new_proof.add_assume(*e_root, None));
                        let e_id =
                            emit_conjunct_chain(terms, &mut new_proof, e_assume, *e_root, e_path);
                        // Equality substitution IS congruence: from (cl E)
                        // derive (cl (= C target)) via `cong` (orientation-free,
                        // equal args skip), then the premiseless `equiv_pos2`
                        // tautology (cl (not (= C target)) (not C) target) and
                        // two resolutions yield (cl target). Every step is
                        // validated structurally by the strict checker.
                        let not_c = terms.mk_not(*c_term);
                        let eq_c_u = terms.mk_eq(*c_term, target);
                        let cong_id = new_proof.add_rule_step(
                            AletheRule::Cong,
                            vec![eq_c_u],
                            vec![e_id],
                            Vec::new(),
                        );
                        let not_eq = terms.mk_not(eq_c_u);
                        // mk_eq canonicalizes argument order; pick the
                        // equiv_pos variant matching the STORED orientation:
                        //   equiv_pos2: (cl (not (= a b)) (not a) b)
                        //   equiv_pos1: (cl (not (= a b)) a (not b))
                        // Both clauses carry the same literal set
                        // {not_eq, not C, target}; only the rule tag differs.
                        let stored_first = match terms.get(eq_c_u) {
                            TermData::App(_, args) if args.len() == 2 => args[0],
                            _ => *c_term,
                        };
                        let ep_rule = if stored_first == *c_term {
                            AletheRule::EquivPos2
                        } else {
                            AletheRule::EquivPos1
                        };
                        let ep2_id = new_proof.add_rule_step(
                            ep_rule,
                            vec![not_eq, not_c, target],
                            Vec::new(),
                            Vec::new(),
                        );
                        let after_cong = new_proof.add_rule_step(
                            AletheRule::ThResolution,
                            vec![not_c, target],
                            vec![ep2_id, cong_id],
                            Vec::new(),
                        );
                        new_proof.add_rule_step(
                            AletheRule::ThResolution,
                            vec![target],
                            vec![after_cong, c_id],
                            Vec::new(),
                        )
                    }
                    Derivation::EquivDefined {
                        e_root,
                        e_path,
                        e_term,
                        l_root,
                        l_path,
                        atom_is_first,
                        negated,
                    } => {
                        // (cl E) and (cl L) from their problem roots, then the
                        // premiseless equiv_pos tautology over E = (= a b):
                        //   equiv_pos1: (cl (not (= a b)) a (not b))
                        //   equiv_pos2: (cl (not (= a b)) (not a) b)
                        // Two th_resolutions (pivot E, then pivot the defining
                        // literal) yield (cl target). Every step is validated
                        // structurally by the strict checker; nothing is
                        // trusted.
                        let e_assume = *root_assumes
                            .entry(*e_root)
                            .or_insert_with(|| new_proof.add_assume(*e_root, None));
                        let e_id =
                            emit_conjunct_chain(terms, &mut new_proof, e_assume, *e_root, e_path);
                        let l_assume = *root_assumes
                            .entry(*l_root)
                            .or_insert_with(|| new_proof.add_assume(*l_root, None));
                        let l_id =
                            emit_conjunct_chain(terms, &mut new_proof, l_assume, *l_root, l_path);
                        let (a, b) = match terms.get(*e_term) {
                            TermData::App(_, args) if args.len() == 2 => (args[0], args[1]),
                            _ => unreachable!("EquivDefined e_term is a binary equality"),
                        };
                        // Rule selection: the tautology's non-negated literal
                        // must be the target-side literal for a positive
                        // target, and the negated literal must be the
                        // target-side literal for a negated target.
                        //   atom first,  positive → equiv_pos1 (a positive)
                        //   atom second, positive → equiv_pos2 (b positive)
                        //   atom first,  negated  → equiv_pos2 ((not a))
                        //   atom second, negated  → equiv_pos1 ((not b))
                        let use_pos1 = *atom_is_first != *negated;
                        let not_eq = terms.mk_not(*e_term);
                        let (rule, lit_a, lit_b) = if use_pos1 {
                            let not_b = terms.mk_not(b);
                            (AletheRule::EquivPos1, a, not_b)
                        } else {
                            let not_a = terms.mk_not(a);
                            (AletheRule::EquivPos2, not_a, b)
                        };
                        let ep_id = new_proof.add_rule_step(
                            rule,
                            vec![not_eq, lit_a, lit_b],
                            Vec::new(),
                            Vec::new(),
                        );
                        let after_e = new_proof.add_rule_step(
                            AletheRule::ThResolution,
                            vec![lit_a, lit_b],
                            vec![ep_id, e_id],
                            Vec::new(),
                        );
                        debug_assert!(
                            lit_a == target || lit_b == target,
                            "EquivDefined tautology does not contain the target literal"
                        );
                        new_proof.add_rule_step(
                            AletheRule::ThResolution,
                            vec![target],
                            vec![after_e, l_id],
                            Vec::new(),
                        )
                    }
                    Derivation::EqualityBounds {
                        e_root,
                        e_path,
                        equality,
                        bounds,
                    } => {
                        let e_assume = *root_assumes
                            .entry(*e_root)
                            .or_insert_with(|| new_proof.add_assume(*e_root, None));
                        let e_id =
                            emit_conjunct_chain(terms, &mut new_proof, e_assume, *e_root, e_path);
                        let not_equality = terms.mk_not(*equality);
                        let mut bound_units = Vec::with_capacity(bounds.len());
                        for &bound in bounds {
                            let farkas = FarkasAnnotation::from_ints(&[1, 1]);
                            let lemma = new_proof.add_step(ProofStep::TheoryLemma {
                                theory: "LRA".to_string(),
                                clause: vec![not_equality, bound],
                                farkas: Some(farkas),
                                kind: TheoryLemmaKind::LraFarkas,
                                lia: None,
                            });
                            bound_units.push(new_proof.add_resolution(
                                vec![bound],
                                *equality,
                                lemma,
                                e_id,
                            ));
                        }

                        let mut clause = Vec::with_capacity(bounds.len() + 1);
                        clause.push(target);
                        for &bound in bounds {
                            clause.push(terms.mk_not(bound));
                        }
                        let mut current = new_proof.add_rule_step(
                            AletheRule::AndNeg,
                            clause.clone(),
                            Vec::new(),
                            vec![target],
                        );
                        for (&bound, &unit) in bounds.iter().zip(&bound_units) {
                            let not_bound = terms.mk_not(bound);
                            let Some(position) = clause.iter().position(|&lit| lit == not_bound)
                            else {
                                unreachable!("equality-bound conjunction lost a child")
                            };
                            let _ = clause.remove(position);
                            current =
                                new_proof.add_resolution(clause.clone(), bound, current, unit);
                        }
                        current
                    }
                };
                id_map.push(derived_id);
                continue;
            }
            let step = match step {
                ProofStep::Step {
                    rule,
                    clause,
                    premises,
                    args,
                } => ProofStep::Step {
                    rule,
                    clause,
                    premises: premises.into_iter().map(|p| remap(p, &id_map)).collect(),
                    args,
                },
                ProofStep::Resolution {
                    clause,
                    pivot,
                    clause1,
                    clause2,
                } => ProofStep::Resolution {
                    clause,
                    pivot,
                    clause1: remap(clause1, &id_map),
                    clause2: remap(clause2, &id_map),
                },
                ProofStep::Anchor {
                    end_step,
                    variables,
                } => ProofStep::Anchor {
                    end_step: remap(end_step, &id_map),
                    variables,
                },
                other => other,
            };
            id_map.push(new_proof.add_step(step));
        }

        *proof = new_proof;
    }

    pub(in crate::executor) fn term_contains_aux_mod_div_var(
        terms: &TermStore,
        root: TermId,
    ) -> bool {
        let mut stack = vec![root];
        let mut visited: HashSet<TermId> = HashSet::default();
        while let Some(term) = stack.pop() {
            if !visited.insert(term) {
                continue;
            }
            match terms.get(term) {
                TermData::Var(name, _)
                    if name.starts_with("_mod_") || name.starts_with("_div_") =>
                {
                    return true
                }
                TermData::Const(_) => {}
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, t, e) => {
                    stack.push(*c);
                    stack.push(*t);
                    stack.push(*e);
                }
                TermData::App(_, args) => stack.extend(args.iter().copied()),
                TermData::Let(bindings, body) => {
                    for (_, v) in bindings {
                        stack.push(*v);
                    }
                    stack.push(*body);
                }
                TermData::Forall(_, body, trig) | TermData::Exists(_, body, trig) => {
                    stack.push(*body);
                    for m in trig {
                        stack.extend(m.iter().copied());
                    }
                }
                _ => {} // non_exhaustive catch-all
            }
        }
        false
    }
}
