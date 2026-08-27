// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `closed_universal.rs` to preserve item paths.

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
