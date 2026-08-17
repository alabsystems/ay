// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded literal witnesses for authored closed universals.

use super::*;

use num_bigint::BigInt;

const MAX_BINDERS: usize = 3;
const MAX_VALUES_PER_BINDER: usize = 8;
const MAX_TUPLES: usize = 64;
/// Total tuples enumerated once the lexicographic prefix has been emitted.
///
/// Raising the cap is affordable because the per-tuple cost is one call to the
/// term evaluator on a CLOSED ground instance: no solver, no allocation of a
/// query. The genuinely expensive leg — the ground fallback solve for an
/// instance the evaluator returns `Unknown` for — keeps its own, unchanged
/// [`MAX_FALLBACK_SOLVES`] budget, and `should_abort_theory_loop` is still
/// consulted before every tuple.
const MAX_TUPLES_TOTAL: usize = 256;
const MAX_FALLBACK_SOLVES: usize = 8;
/// Term nodes visited by one linear-form walk. A closed quantifier-free body is
/// small by construction; the bound only stops a pathological share.
const MAX_LINEAR_WALK: u32 = 4_000;

/// The linear form `coefficient * binder + constant` of an Int term, when the
/// term is linear in `binder` and every other leaf is a numeral.
///
/// `None` means "not in the linear fragment" — a different binder, a `div`, an
/// `ite`, a product of two non-constant factors. That is a DECLINE of one
/// candidate source, never of a verdict: the caller only uses the result to
/// propose integers to try, and every proposal is re-decided by evaluating the
/// substituted instance.
fn linear_form(
    terms: &ay_core::TermStore,
    term: TermId,
    binder: &str,
    fuel: &mut u32,
) -> Option<(BigInt, BigInt)> {
    if *fuel == 0 {
        return None;
    }
    *fuel -= 1;
    match terms.get(term) {
        TermData::Const(ay_core::Constant::Int(value)) => Some((BigInt::ZERO, value.clone())),
        TermData::Var(name, _) => {
            if *terms.sort(term) != ay_core::Sort::Int {
                return None;
            }
            // A `Var` that is not this binder is either another binder or a
            // declared constant; neither is a numeral, so the atom is not a
            // pure bound on `binder` and yields no boundary.
            (name.as_str() == binder).then(|| (BigInt::from(1), BigInt::ZERO))
        }
        TermData::App(ay_core::Symbol::Named(name), args) => match (name.as_str(), args.len()) {
            ("+", _) if !args.is_empty() => {
                let mut coefficient = BigInt::ZERO;
                let mut constant = BigInt::ZERO;
                for &arg in args.iter() {
                    let (a, b) = linear_form(terms, arg, binder, fuel)?;
                    coefficient += a;
                    constant += b;
                }
                Some((coefficient, constant))
            }
            ("-", 1) => {
                let (a, b) = linear_form(terms, args[0], binder, fuel)?;
                Some((-a, -b))
            }
            ("-", _) if args.len() >= 2 => {
                let (mut coefficient, mut constant) = linear_form(terms, args[0], binder, fuel)?;
                for &arg in args.iter().skip(1) {
                    let (a, b) = linear_form(terms, arg, binder, fuel)?;
                    coefficient -= a;
                    constant -= b;
                }
                Some((coefficient, constant))
            }
            ("*", _) if !args.is_empty() => {
                let mut coefficient = BigInt::ZERO;
                let mut constant = BigInt::from(1);
                let mut seen_binder = false;
                for &arg in args.iter() {
                    let (a, b) = linear_form(terms, arg, binder, fuel)?;
                    if a == BigInt::ZERO {
                        coefficient *= &b;
                        constant *= b;
                        continue;
                    }
                    // Two binder-bearing factors would be quadratic.
                    if seen_binder {
                        return None;
                    }
                    seen_binder = true;
                    // Multiply the accumulated constant product by `a*v + b`.
                    let product = constant.clone();
                    coefficient = a * &product;
                    constant = b * &product;
                }
                Some((coefficient, constant))
            }
            _ => None,
        },
        _ => None,
    }
}

/// Integers at which some atom of `body` changes truth value for `binder`.
///
/// For a comparison / equality atom whose two sides have linear forms in
/// `binder`, the atom flips at `binder = -constant / coefficient`; both integers
/// bracketing that rational, and their immediate neighbours, are proposed. This
/// is the only way a refuting witness that is not a small number and not
/// syntactically present in the problem — `∀q. q >= 2*q - 11` is false exactly
/// from `q = 12` upward — can ever be reached by a bounded enumeration.
/// Per-ATOM boundary groups, each ordered flip-point-first.
///
/// Returning one group per atom (instead of one flat first-atom-wins list) is
/// what lets the caller interleave: with `MAX_VALUES_PER_BINDER = 8` and the
/// small window taking five slots, a flat list spends the remaining three on
/// the FIRST atom's neighbourhood, so a refuting witness on the SECOND atom's
/// boundary — `x = 3` for `∀x. (2x ≥ 5 ∧ x ≤ 10) ⇒ x > 3`, whose traversal
/// visits `x ≤ 10` first — was provably never tried. Round-robin across
/// groups reaches every atom's flip point before any atom's third neighbour.
/// Selection carries no authority — every proposal is re-decided by
/// evaluating the substituted instance.
fn linear_boundary_candidate_groups(
    terms: &ay_core::TermStore,
    body: TermId,
    binder: &str,
) -> Vec<Vec<BigInt>> {
    use num_integer::Integer;

    let mut groups: Vec<Vec<BigInt>> = Vec::new();
    let mut fuel = MAX_LINEAR_WALK;
    let mut visited: ay_core::kani_compat::DetHashSet<TermId> =
        ay_core::kani_compat::DetHashSet::default();
    let mut stack = vec![body];
    while let Some(term) = stack.pop() {
        if fuel == 0 {
            break;
        }
        fuel -= 1;
        if !visited.insert(term) {
            continue;
        }
        match terms.get(term) {
            TermData::App(ay_core::Symbol::Named(name), args) => {
                if matches!(name.as_str(), "=" | "<" | "<=" | ">" | ">=" | "distinct")
                    && args.len() == 2
                {
                    if let (Some((a0, b0)), Some((a1, b1))) = (
                        linear_form(terms, args[0], binder, &mut fuel),
                        linear_form(terms, args[1], binder, &mut fuel),
                    ) {
                        let coefficient = a0 - a1;
                        let constant = b0 - b1;
                        if coefficient != BigInt::ZERO {
                            // The atom flips where `coefficient * binder + constant == 0`.
                            let one = BigInt::from(1);
                            let (floor, remainder) =
                                (BigInt::ZERO - constant).div_mod_floor(&coefficient);
                            let ceiling = if remainder == BigInt::ZERO {
                                floor.clone()
                            } else {
                                floor.clone() + &one
                            };
                            // Flip points first, neighbours after.
                            let mut group: Vec<BigInt> = Vec::new();
                            for value in [
                                floor.clone(),
                                ceiling.clone(),
                                floor.clone() - &one,
                                floor.clone() + &one,
                                ceiling.clone() + &one,
                            ] {
                                if !group.contains(&value) {
                                    group.push(value);
                                }
                            }
                            groups.push(group);
                        }
                    }
                }
                stack.extend(args.iter().copied());
            }
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(condition, then_term, else_term) => {
                stack.push(*condition);
                stack.push(*then_term);
                stack.push(*else_term);
            }
            _ => {}
        }
    }
    groups
}

/// Int candidates for ONE binder, in the order they will be tried.
///
/// The shared `synthesize_int_refutation_candidates` list appends the
/// problem-derived constants LAST, so the old `truncate(MAX_VALUES_PER_BINDER)`
/// discarded every one of them and left only the fixed small window. Interleave
/// instead: the small window first (it discharges most shapes for free), then
/// this binder's own atom boundaries, then whatever the shared synthesizer had
/// left over. Selection carries no authority — only the ordering of guesses.
fn int_candidates_for_binder(
    terms: &ay_core::TermStore,
    body: TermId,
    forall_id: TermId,
    binder: &str,
) -> Vec<BigInt> {
    let mut out: Vec<BigInt> = Vec::new();
    let push = |out: &mut Vec<BigInt>, value: BigInt| {
        if out.len() < MAX_VALUES_PER_BINDER && !out.contains(&value) {
            out.push(value);
        }
    };
    for small in [0i64, 1, -1, 2, -2] {
        push(&mut out, BigInt::from(small));
    }
    // Round-robin across the per-atom boundary groups so every atom's flip
    // point is reachable before any single atom's whole neighbourhood.
    let groups = linear_boundary_candidate_groups(terms, body, binder);
    let deepest = groups.iter().map(Vec::len).max().unwrap_or(0);
    for rank in 0..deepest {
        for group in &groups {
            if let Some(boundary) = group.get(rank) {
                push(&mut out, boundary.clone());
            }
        }
    }
    for synthesized in
        crate::executor::mbqi::synthesize_int_refutation_candidates(terms, body, &[forall_id])
    {
        push(&mut out, synthesized);
    }
    out
}

fn literal_sets(
    exec: &mut Executor,
    vars: &[(String, ay_core::Sort)],
    body: TermId,
    forall_id: TermId,
) -> Option<Vec<Vec<TermId>>> {
    let rational = |numerator| num_rational::BigRational::from_integer(BigInt::from(numerator));
    let fraction =
        |numerator| num_rational::BigRational::new(BigInt::from(numerator), BigInt::from(2));
    let real_values = [
        rational(0),
        rational(1),
        rational(-1),
        fraction(1),
        fraction(-1),
        fraction(3),
        fraction(-3),
    ];
    // Collected before the `&mut` rebuild loop: candidate synthesis only reads.
    let int_sets: Vec<Option<Vec<BigInt>>> = vars
        .iter()
        .map(|(name, sort)| {
            matches!(sort, ay_core::Sort::Int)
                .then(|| int_candidates_for_binder(&exec.ctx.terms, body, forall_id, name))
        })
        .collect();
    vars.iter()
        .zip(int_sets)
        .map(|((_, sort), int_values)| match sort {
            // EXHAUSTIVE, not heuristic: `Bool` has exactly these two values,
            // so a decline here means the universal is genuinely valid.
            ay_core::Sort::Bool => Some(
                [false, true]
                    .into_iter()
                    .map(|value| exec.ctx.terms.mk_bool(value))
                    .collect(),
            ),
            ay_core::Sort::Int => Some(
                int_values?
                    .into_iter()
                    .map(|value| exec.ctx.terms.mk_int(value))
                    .collect(),
            ),
            ay_core::Sort::Real => Some(
                real_values
                    .iter()
                    .cloned()
                    .map(|value| exec.ctx.terms.mk_rational(value))
                    .collect(),
            ),
            ay_core::Sort::BitVec(sort) => {
                let width = sort.width;
                let mut values = crate::executor::bv_mbqi::synthesize_bv_refutation_candidates(
                    &exec.ctx.terms,
                    body,
                    width,
                );
                values.truncate(MAX_VALUES_PER_BINDER);
                Some(
                    values
                        .into_iter()
                        .map(|value| exec.ctx.terms.mk_bitvec(value, width))
                        .collect(),
                )
            }
            _ => None,
        })
        .collect()
}

/// The tuples the enumeration used to reach: lexicographic, stopping the moment
/// the partial product hits [`MAX_TUPLES`].
///
/// Kept verbatim and emitted FIRST so the widening below is strictly additive —
/// no tuple this order used to reach can be displaced by the new one.
fn lexicographic_index_tuples(sizes: &[usize]) -> Vec<Vec<usize>> {
    let mut tuples = vec![Vec::new()];
    for &size in sizes {
        let mut next = Vec::new();
        'prefixes: for prefix in &tuples {
            for index in 0..size {
                let mut tuple = prefix.clone();
                tuple.push(index);
                next.push(tuple);
                if next.len() >= MAX_TUPLES {
                    break 'prefixes;
                }
            }
        }
        tuples = next;
    }
    tuples
}

/// Index tuples in GROWING-HYPERCUBE order: everything inside `[0..=r]^n` before
/// anything that needs index `r + 1`.
fn hypercube_index_tuples(sizes: &[usize], budget: usize) -> Vec<Vec<usize>> {
    let arity = sizes.len();
    let widest = sizes.iter().copied().max().unwrap_or(0);
    let mut tuples: Vec<Vec<usize>> = Vec::new();
    if arity == 0 {
        return tuples;
    }
    let mut indices = vec![0usize; arity];
    for shell in 0..widest {
        loop {
            // A tuple belongs to shell `r` when its LARGEST index is exactly
            // `r`; anything smaller was emitted by an earlier shell.
            if indices.iter().copied().max().unwrap_or(0) == shell
                && indices
                    .iter()
                    .zip(sizes)
                    .all(|(&index, &size)| index < size)
            {
                tuples.push(indices.clone());
                if tuples.len() >= budget {
                    return tuples;
                }
            }
            // Odometer over `[0..=shell]^arity`.
            let mut position = 0usize;
            while position < arity {
                if indices[position] < shell {
                    indices[position] += 1;
                    break;
                }
                indices[position] = 0;
                position += 1;
            }
            if position == arity {
                break;
            }
        }
    }
    tuples
}

/// Literal tuples to try, in order.
///
/// The old enumeration was purely lexicographic and stopped as soon as the
/// partial product reached the cap: with three binders of eight candidates the
/// cap is exhausted while the FIRST binder is still pinned to its first value,
/// so seven eighths of its candidates were unreachable however good they were.
/// The lexicographic prefix is still emitted first — every tuple that used to be
/// tried is still tried, in the same order — and the remaining budget is then
/// spent shell by shell, which distributes it symmetrically across binders.
///
/// ORDER AND BUDGET ONLY. Each tuple is still independently re-decided by
/// evaluating the substituted instance, so a tuple reached earlier or later can
/// change only whether a refutation is FOUND, never whether one is believed.
fn bounded_tuples(literal_sets: Vec<Vec<TermId>>) -> Vec<Vec<TermId>> {
    if literal_sets.is_empty() || literal_sets.iter().any(Vec::is_empty) {
        return Vec::new();
    }
    let sizes: Vec<usize> = literal_sets.iter().map(Vec::len).collect();
    let mut seen: ay_core::kani_compat::DetHashSet<Vec<usize>> =
        ay_core::kani_compat::DetHashSet::default();
    let mut ordered: Vec<Vec<usize>> = Vec::new();
    for tuple in lexicographic_index_tuples(&sizes) {
        if seen.insert(tuple.clone()) {
            ordered.push(tuple);
        }
    }
    for tuple in hypercube_index_tuples(&sizes, MAX_TUPLES_TOTAL) {
        if ordered.len() >= MAX_TUPLES_TOTAL {
            break;
        }
        if seen.insert(tuple.clone()) {
            ordered.push(tuple);
        }
    }
    ordered
        .into_iter()
        .map(|tuple| {
            tuple
                .into_iter()
                .zip(&literal_sets)
                .map(|(index, values)| values[index])
                .collect()
        })
        .collect()
}

/// `--debug-cert`-gated note, matching `const_interp_note`.
///
/// This lane used to decline in total silence, which is what made three
/// long-standing red rows unattributable: an observer could see only the
/// downstream `unknown` and could not tell "no candidate tuple was false" from
/// "a false tuple was found but the exact certificate refused it". They are
/// completely different defects — one is candidate synthesis, the other is
/// scope authority — and telling them apart should not require a rebuild.
fn closed_universal_note(msg: &str) {
    if ay_core::misc_cli_flags().debug_cert || ay_core::misc_cli_flags().trace_cegqi_attr {
        eprintln!("c CERT/closed-universal {msg}");
    }
}

impl Executor {
    /// Find a concrete numeral tuple whose closed instance is false.
    ///
    /// Enumeration is completeness-only: each accepted tuple is independently
    /// checked after exact substitution, so poor candidates only cause decline.
    pub(super) fn closed_universal_false_at_literal_witness(
        &mut self,
        vars: &[(String, ay_core::Sort)],
        body: TermId,
        forall_id: TermId,
        fallback_category: LogicCategory,
    ) -> Option<ClosedUniversalRefutation> {
        if vars.is_empty() || vars.len() > MAX_BINDERS || self.should_abort_theory_loop() {
            closed_universal_note("decline: binder count out of range, or the loop is aborting");
            return None;
        }
        let Some(literal_sets) = literal_sets(self, vars, body, forall_id) else {
            closed_universal_note("decline: a binder sort has no closed-literal candidate family");
            return None;
        };
        if literal_sets.iter().any(Vec::is_empty) {
            closed_universal_note("decline: a binder produced zero candidates");
            return None;
        }

        let empty_model = Model::empty();
        let mut fallback_solves = 0usize;
        let mut false_instances = 0usize;
        let tuples = bounded_tuples(literal_sets);
        let tuple_count = tuples.len();
        for tuple in tuples {
            if self.should_abort_theory_loop() {
                return None;
            }
            let subst: HashMap<String, TermId> = vars
                .iter()
                .zip(&tuple)
                .map(|((name, _), &literal)| (name.clone(), literal))
                .collect();
            let instance = crate::ematching::subst_vars(&mut self.ctx.terms, body, &subst);
            match self.evaluate_term(&empty_model, instance) {
                EvalValue::Bool(false) => {
                    false_instances += 1;
                    // Translate before minting evidence because proof construction interns terms.
                    if tuple.len() == 1
                        && self.try_translate_arithmetic_forall_instance_unsat(forall_id, tuple[0])
                    {
                        return Some(ClosedUniversalRefutation::TranslatedProof);
                    }
                    if let Some(evidence) = self
                        .try_authorize_current_query_exact_closed_forall_unsat(forall_id, &tuple)
                    {
                        return Some(ClosedUniversalRefutation::CheckedLiteral(evidence));
                    }
                    // #consequence-replay fallback: a guarded / non-comparison
                    // closed instance the exact closed-forall certificate also
                    // refuses (operator identity, scope, or substitution
                    // restrictions) is replayed on the same-context probe and
                    // its strict proof stitched onto a `forall_inst` prologue.
                    // Deliberately AFTER the checked-literal evidence so the
                    // established exact semantic lane keeps every case it
                    // already decides; fail-closed on every leg.
                    if let Some(exact) = self.exact_forall_instance(forall_id, &tuple) {
                        let record = crate::ematching::ForallInstantiationProvenance {
                            quantifier: forall_id,
                            binding: tuple.clone(),
                            instance: exact,
                        };
                        if self.try_translate_authored_consequence_replay_unsat_with(
                            std::slice::from_ref(&record),
                        ) {
                            return Some(ClosedUniversalRefutation::TranslatedProof);
                        }
                    }
                    closed_universal_note(
                        "a candidate tuple makes the body FALSE, but neither the translated \
                         arithmetic proof nor the exact closed-forall certificate would take it \
                         (authored-root scope, operator identity, or exact substitution refused)",
                    );
                }
                EvalValue::Bool(true) => continue,
                _ if fallback_solves < MAX_FALLBACK_SOLVES => {
                    fallback_solves += 1;
                    let obligation = vec![instance];
                    if self
                        .checked_ground_solve(obligation.clone(), fallback_category, 2_000)
                        .is_some_and(|decision| match decision {
                            CheckedGroundDecision::Unsat(checked) => {
                                checked.consume(self, &obligation)
                            }
                            CheckedGroundDecision::Sat(_) => false,
                        })
                    {
                        return Some(ClosedUniversalRefutation::UntranslatedSkolemModel);
                    }
                }
                _ => {}
            }
        }
        closed_universal_note(&format!(
            "decline: {tuple_count} candidate tuples tried, {false_instances} evaluated FALSE, \
             {fallback_solves} ground fallback solves — no publishable refutation"
        ));
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Every tuple the OLD lexicographic enumeration reached is still reached,
    /// in the same order, before any tuple the widening added.
    #[test]
    fn bounded_tuple_order_is_strictly_additive() {
        let sizes = [8usize, 8, 8];
        let lexicographic = lexicographic_index_tuples(&sizes);
        assert_eq!(lexicographic.len(), MAX_TUPLES);
        let mut seen: ay_core::kani_compat::DetHashSet<Vec<usize>> =
            ay_core::kani_compat::DetHashSet::default();
        let mut ordered: Vec<Vec<usize>> = Vec::new();
        for tuple in lexicographic.clone() {
            if seen.insert(tuple.clone()) {
                ordered.push(tuple);
            }
        }
        for tuple in hypercube_index_tuples(&sizes, MAX_TUPLES_TOTAL) {
            if ordered.len() >= MAX_TUPLES_TOTAL {
                break;
            }
            if seen.insert(tuple.clone()) {
                ordered.push(tuple);
            }
        }
        assert_eq!(&ordered[..lexicographic.len()], &lexicographic[..]);
        assert_eq!(ordered.len(), MAX_TUPLES_TOTAL);
    }

    /// The widening is what makes a candidate of the FIRST binder past index 0
    /// reachable at all with three binders.
    #[test]
    fn hypercube_order_reaches_every_binder() {
        let sizes = [8usize, 8, 8];
        assert!(
            lexicographic_index_tuples(&sizes)
                .iter()
                .all(|tuple| tuple[0] == 0),
            "the old order never moves the first binder off its first candidate"
        );
        let widened = hypercube_index_tuples(&sizes, MAX_TUPLES_TOTAL);
        for binder in 0..3 {
            for value in 0..4 {
                assert!(
                    widened.iter().any(|tuple| tuple[binder] == value),
                    "binder {binder} candidate {value} must be reachable"
                );
            }
        }
    }

    #[test]
    fn hypercube_respects_ragged_sizes() {
        let sizes = [2usize, 5];
        let tuples = hypercube_index_tuples(&sizes, 1_000);
        assert_eq!(tuples.len(), 10);
        for tuple in &tuples {
            assert!(tuple[0] < 2 && tuple[1] < 5);
        }
        let mut sorted = tuples.clone();
        sorted.sort_unstable();
        sorted.dedup();
        assert_eq!(sorted.len(), tuples.len(), "no duplicates");
    }
}
