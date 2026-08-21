// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by executor::quantifier_loop::preprocess to preserve item paths.

/// Rewrite GROUND integer STRICT order atoms — in every syntactic form the
/// skolemizer / arithmetic normalizer emits — to the equivalent POSITIVE
/// NON-STRICT `(<= _ _)` bound, recursing through Boolean / function structure
/// but NOT into `forall`/`exists` bodies.
///
/// Over `Int`, all of these are exact equivalences (true in every model, so safe
/// in any polarity):
///   * `(< a b)`        ⇒ `(<= a (- b 1))`           (a < b   ⇔ a ≤ b-1)
///   * `(not (<= a b))` ⇒ `(<= (+ b 1) a)`           (a > b   ⇔ a ≥ b+1)
///   * `(not (< a b))`  ⇒ `(<= b a)`                 (a ≥ b   ⇔ b ≤ a)
///
/// The skolemized negation of a per-element GOAL `(forall i. (and (<= lo i)
/// (< i hi)) ⇒ P)` surfaces its boundary bounds as the *negated* atoms
/// `(not (<= k (- len 1)))` (k ≥ len) and `(not (<= (+ len 1) k))` (k ≤ len) —
/// strict bounds in disguise. ay-lia only EXPORTS an implied equality from
/// POSITIVE non-strict two-sided bounds, so without this normalization the
/// boundary index `k` is never pinned to `len` and the goal stays Unknown/Sat.
/// Normalizing every strict form to a positive `<=` feeds the existing
/// (sound) export, letting `k ≥ len ∧ k ≤ len ⇒ k = len` propagate to the
/// congruence closure so the just-pushed element closes the new-element case.
///
/// See [`Executor::tighten_ground_int_strict_bounds`] for the full rationale.
/// `cache` memoizes on the original (pre-rewrite) `TermId`; existing terms are
/// never mutated (only fresh terms interned), so cached ids stay valid.
/// Real-sorted comparisons are left untouched (strict ≠ non-strict over `Real`).
///
/// `subst` folds asserted GROUND integer equalities `v = <expr>` (keyed on the
/// `Var` `TermId` of `v`, value the integer-equal `<expr>`) into the OPERANDS of
/// the integer order atoms it tightens — and ONLY there. A boundary bound
/// written against a SEPARATE upper-bound variable — e.g. `(< k new_len)` with
/// `(= new_len (+ len 1))` asserted — then resolves to the SAME concrete
/// `(<= k (- (+ len 1) 1))` the inline `(< k (+ len 1))` form already produces,
/// which ay-lia simplifies to `(<= k len)` and pins `k = len`. Confining the
/// fold to order-atom operands (rather than substituting every `Var` leaf) keeps
/// the blast radius minimal: the asserted defining equation and all non-order
/// atoms are left byte-identical, so E-matching / array reasoning are
/// unperturbed. The map values are pre-filtered (see
/// [`Executor::collect_ground_int_eq_subst`]) to contain no key `Var`. Folding an
/// ASSERTED equality is an exact integer-equivalence substitution, so it cannot
/// turn an invalid goal `unsat` — only normalize the boundary atom so the
/// existing (sound) implied-equality export can fire.
fn tighten_int_strict_term(
    terms: &mut TermStore,
    term: TermId,
    subst: &HashMap<TermId, TermId>,
    cache: &mut HashMap<TermId, TermId>,
) -> TermId {
    if let Some(&cached) = cache.get(&term) {
        return cached;
    }
    let result = stacker::maybe_grow(TIGHTEN_STACK_RED_ZONE, TIGHTEN_STACK_SIZE, || {
        match terms.get(term).clone() {
            TermData::App(sym, args) => {
                let new_args: Vec<TermId> = args
                    .iter()
                    .map(|&a| tighten_int_strict_term(terms, a, subst, cache))
                    .collect();
                // Integer strict less-than: `(< a b)` ⇒ `(<= a (- b 1))`. `>`/`>=`
                // are already normalized to `<`/`<=` at construction (mk_gt/mk_ge),
                // and `<=` needs no change. Real-sorted `<` is left untouched
                // (strict ≠ non-strict over the reals).
                if sym.name() == "<"
                    && new_args.len() == 2
                    && matches!(terms.sort(new_args[0]), Sort::Int)
                {
                    // Ground-equality fold (#ground-length-equation): resolve any
                    // asserted `v = <expr>` in the boundary operands so a strict
                    // bound against a separate length variable becomes pinnable.
                    let lhs = subst_ground_int_vars(terms, new_args[0], subst);
                    let rhs = subst_ground_int_vars(terms, new_args[1], subst);
                    let one = terms.mk_int(num_bigint::BigInt::from(1));
                    let t_minus_1 = terms.mk_sub(vec![rhs, one]);
                    terms.mk_le(lhs, t_minus_1)
                } else if new_args == args {
                    term
                } else {
                    let sort = terms.sort(term).clone();
                    terms.mk_app(sym, new_args, sort)
                }
            }
            TermData::Not(inner) => {
                // Normalize a NEGATED integer order atom into a positive `<=`.
                if let TermData::App(isym, iargs) = terms.get(inner).clone() {
                    if iargs.len() == 2 && matches!(terms.sort(iargs[0]), Sort::Int) {
                        let a0 = tighten_int_strict_term(terms, iargs[0], subst, cache);
                        let b0 = tighten_int_strict_term(terms, iargs[1], subst, cache);
                        // Ground-equality fold into the (negated) boundary operands.
                        let a = subst_ground_int_vars(terms, a0, subst);
                        let b = subst_ground_int_vars(terms, b0, subst);
                        match isym.name() {
                            // ¬(a ≤ b) ⇔ a ≥ b+1 ⇔ (b+1) ≤ a
                            "<=" => {
                                let one = terms.mk_int(num_bigint::BigInt::from(1));
                                let b_plus_1 = terms.mk_add(vec![b, one]);
                                return terms.mk_le(b_plus_1, a);
                            }
                            // ¬(a < b) ⇔ a ≥ b ⇔ b ≤ a
                            "<" => return terms.mk_le(b, a),
                            _ => {}
                        }
                    }
                }
                let ni = tighten_int_strict_term(terms, inner, subst, cache);
                if ni == inner {
                    term
                } else {
                    terms.mk_not(ni)
                }
            }
            TermData::Ite(c, t, e) => {
                let nc = tighten_int_strict_term(terms, c, subst, cache);
                let nt = tighten_int_strict_term(terms, t, subst, cache);
                let ne = tighten_int_strict_term(terms, e, subst, cache);
                if nc == c && nt == t && ne == e {
                    term
                } else {
                    terms.mk_ite(nc, nt, ne)
                }
            }
            TermData::Let(bindings, body) => {
                let new_bindings: Vec<(String, TermId)> = bindings
                    .iter()
                    .map(|(n, v)| (n.clone(), tighten_int_strict_term(terms, *v, subst, cache)))
                    .collect();
                let nb = tighten_int_strict_term(terms, body, subst, cache);
                if nb == body && new_bindings == bindings {
                    term
                } else {
                    terms.mk_let(new_bindings, nb)
                }
            }
            // Surviving quantifier bodies are deliberately opaque: tightening only
            // the GROUND atoms keeps E-matching / trigger selection unperturbed.
            // Leaves (Const, Var) and Forall/Exists return unchanged.
            _ => term,
        }
    });
    cache.insert(term, result);
    result
}

/// Replace asserted ground-equality variables (`subst` keys) inside an INTEGER
/// arithmetic operand of an order atom, rebuilding the term around the
/// replacements. `subst` values are key-free (collection-time filter), so a
/// single non-recursive replacement per `Var` leaf is exact and terminating.
///
/// This is the ONLY place the ground-equality fold rewrites terms: it touches
/// just the operands of the strict / negated order atoms
/// [`tighten_int_strict_term`] already normalizes, leaving the asserted defining
/// equation and every other atom untouched. No descent into `Forall`/`Exists`
/// bodies (ground order-atom operands never contain them; guarded for safety).
fn subst_ground_int_vars(
    terms: &mut TermStore,
    term: TermId,
    subst: &HashMap<TermId, TermId>,
) -> TermId {
    if subst.is_empty() {
        return term;
    }
    stacker::maybe_grow(TIGHTEN_STACK_RED_ZONE, TIGHTEN_STACK_SIZE, || {
        match terms.get(term).clone() {
            TermData::Var(..) => subst.get(&term).copied().unwrap_or(term),
            TermData::App(sym, args) => {
                let new_args: Vec<TermId> = args
                    .iter()
                    .map(|&a| subst_ground_int_vars(terms, a, subst))
                    .collect();
                if new_args == args {
                    term
                } else {
                    let sort = terms.sort(term).clone();
                    terms.mk_app(sym, new_args, sort)
                }
            }
            TermData::Ite(c, t, e) => {
                let nc = subst_ground_int_vars(terms, c, subst);
                let nt = subst_ground_int_vars(terms, t, subst);
                let ne = subst_ground_int_vars(terms, e, subst);
                if nc == c && nt == t && ne == e {
                    term
                } else {
                    terms.mk_ite(nc, nt, ne)
                }
            }
            // Const leaves and (defensively) any Forall/Exists/Not/Let return
            // unchanged: an integer order-atom operand is ground arithmetic.
            _ => term,
        }
    })
}

/// Does any `Var` whose `TermId` is in `targets` occur anywhere in `term`?
///
/// Iterative (heap stack) so deeply nested ground terms cannot overflow.
/// Descends into EVERY structural position — including quantifier bodies — so
/// the acyclicity / self-reference checks for the ground-equality fold are
/// conservative (a candidate is rejected if its right-hand side mentions any
/// substituted variable *anywhere*).
fn term_mentions_any_var(terms: &TermStore, term: TermId, targets: &HashSet<TermId>) -> bool {
    let mut stack = vec![term];
    let mut seen: HashSet<TermId> = HashSet::default();
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        // `targets` holds only `Var` ids; reaching one means the var occurs.
        if targets.contains(&t) {
            return true;
        }
        match terms.get(t) {
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Not(i) => stack.push(*i),
            TermData::Ite(c, th, e) => {
                stack.push(*c);
                stack.push(*th);
                stack.push(*e);
            }
            TermData::Let(binds, b) => {
                for (_, v) in binds {
                    stack.push(*v);
                }
                stack.push(*b);
            }
            TermData::Forall(_, b, _) | TermData::Exists(_, b, _) => stack.push(*b),
            _ => {}
        }
    }
    false
}

/// Validate the two-literal arithmetic tautology `(cl a b)` with an explicit
/// `[1, 1]` Farkas certificate.  Clause literals are converted to the conflict
/// polarity expected by the shared proof validator exactly as the final
/// `la_generic` checker does.  This is the admission gate for affine-bound
/// bridges: failure means no clause is injected.
fn farkas_pair_clause_valid(terms: &TermStore, a: TermId, b: TermId) -> bool {
    let farkas = FarkasAnnotation::from_ints(&[1, 1]);
    let lits: Vec<TheoryLit> = [a, b]
        .iter()
        .map(|&literal| match terms.get(literal) {
            TermData::Not(inner) => TheoryLit::new(*inner, true),
            _ => TheoryLit::new(literal, false),
        })
        .collect();
    ay_core::proof_validation::verify_farkas_conflict_lits_full(terms, &lits, &farkas).is_ok()
}

/// Insert every `Var` `TermId` reachable from `root` into `out`.
fn collect_all_var_ids(terms: &TermStore, root: TermId, out: &mut HashSet<TermId>) {
    let mut stack = vec![root];
    let mut seen: HashSet<TermId> = HashSet::default();
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        match terms.get(t) {
            TermData::Var(..) => {
                out.insert(t);
            }
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Not(i) => stack.push(*i),
            TermData::Ite(c, th, e) => {
                stack.push(*c);
                stack.push(*th);
                stack.push(*e);
            }
            TermData::Let(binds, b) => {
                for (_, v) in binds {
                    stack.push(*v);
                }
                stack.push(*b);
            }
            TermData::Forall(_, b, _) | TermData::Exists(_, b, _) => stack.push(*b),
            _ => {}
        }
    }
}

/// Insert the `Var` `TermId`s that occur inside ANY quantifier body reachable
/// from `root` into `out` (the body subtree's full var set, nested quantifiers
/// included).
///
/// Variables that appear under a surviving `Forall`/`Exists` are excluded from
/// the ground-equality fold so E-matching / trigger alignment stays byte
/// identical: the fold rewrites only GROUND atoms, never quantifier bodies, so
/// folding a variable that ALSO occurs in a body would desync the ground atom
/// from the matching instantiation (e.g. a ground `(+ bit0 bit1)` rewritten to
/// `(+ 0 1)` while the live `forall` body keeps `(+ bit0 bit1)`), dropping the
/// syntactic conflict E-matching relies on.
fn collect_vars_under_quantifiers(terms: &TermStore, root: TermId, out: &mut HashSet<TermId>) {
    let mut stack = vec![root];
    let mut seen: HashSet<TermId> = HashSet::default();
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        match terms.get(t) {
            TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => {
                collect_all_var_ids(terms, *body, out);
            }
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Not(i) => stack.push(*i),
            TermData::Ite(c, th, e) => {
                stack.push(*c);
                stack.push(*th);
                stack.push(*e);
            }
            TermData::Let(binds, b) => {
                for (_, v) in binds {
                    stack.push(*v);
                }
                stack.push(*b);
            }
            _ => {}
        }
    }
}

/// Recursively fold datatype selector-over-constructor applications
/// `sel_i(C(t0..tn)) -> t_i` throughout `term`, re-interning the result. This is
/// the exact SMT-LIB datatype selector axiom applied as a semantics-preserving
/// rewrite — the same fold the elaborator performs (`elaborate_app`). Only fires
/// when the selector provably OWNS the applied constructor (looked up in
/// `ctor_sels`, the constructor -> ordered-selector-name map); a selector over a
/// foreign constructor is left opaque for the existing selector-axiom path.
/// `memo` shares folded subterms across the whole assertion DAG so shared
/// structure is rewritten once (no exponential blowup). Descends `App`/`Not`/
/// `Ite`; E-matching instances are quantifier-free ground bodies, so any residual
/// binder/let (never produced by `instantiate_body`) is returned unchanged.
fn reduce_selectors_rec(
    terms: &mut TermStore,
    ctor_sels: &HashMap<String, Vec<String>>,
    term: TermId,
    memo: &mut HashMap<TermId, TermId>,
) -> TermId {
    if let Some(&cached) = memo.get(&term) {
        return cached;
    }
    let result = match terms.get(term).clone() {
        TermData::App(sym, args) => {
            let rargs: Vec<TermId> = args
                .iter()
                .map(|&a| reduce_selectors_rec(terms, ctor_sels, a, memo))
                .collect();
            // Datatype folds when the (already-reduced) single argument is a
            // constructor application `C(f0..fn)`:
            //   * selector:  `sel_i(C(f..)) -> f_i` (the field, already reduced)
            //   * tester:    `is-D(C(..))  -> (D == C)` as `true`/`false`
            // Both are exact SMT-LIB datatype axioms. The tester name is
            // `is-<constructor>` (elaborator convention, `datatypes.rs`); it is a
            // genuine tester only when the stripped name is itself a constructor,
            // and the fold to a Boolean constant is sound only when the argument is
            // KNOWN to be a constructor of the same datatype — guaranteed here
            // because a well-sorted tester is applied to a term of its datatype and
            // `C` is that term's actual head constructor.
            let mut folded = None;
            if let (Symbol::Named(name), [only]) = (&sym, rargs.as_slice()) {
                if let TermData::App(Symbol::Named(ctor), cargs) = terms.get(*only).clone() {
                    if let Some(sels) = ctor_sels.get(&ctor) {
                        if let Some(idx) = sels.iter().position(|s| s == name) {
                            folded = cargs.get(idx).copied();
                        }
                    }
                    if folded.is_none() {
                        if let Some(tested) = name.strip_prefix("is-") {
                            if ctor_sels.contains_key(tested) && ctor_sels.contains_key(&ctor) {
                                folded = Some(if tested == ctor {
                                    terms.true_term()
                                } else {
                                    terms.false_term()
                                });
                            }
                        }
                    }
                }
            }
            match folded {
                Some(field) => field,
                None => {
                    let sort = terms.sort(term).clone();
                    terms.mk_app(sym, rargs, sort)
                }
            }
        }
        TermData::Not(x) => {
            let rx = reduce_selectors_rec(terms, ctor_sels, x, memo);
            terms.mk_not(rx)
        }
        TermData::Ite(c, t, e) => {
            let rc = reduce_selectors_rec(terms, ctor_sels, c, memo);
            let rt = reduce_selectors_rec(terms, ctor_sels, t, memo);
            let re = reduce_selectors_rec(terms, ctor_sels, e, memo);
            terms.mk_ite(rc, rt, re)
        }
        _ => term,
    };
    memo.insert(term, result);
    result
}
