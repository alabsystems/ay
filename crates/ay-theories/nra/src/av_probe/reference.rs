// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// ============================================================================
// PART B — INDEPENDENT REFERENCE MODEL
//
// The point set as a BITMASK over the 2m+1 atoms cut out by m ordered
// landmarks. Union/intersect/complement/subtract are bit operations. Nothing
// in the model does interval reasoning, so it shares no code path with `ialg`.
// ============================================================================

#[cfg(test)]
struct Land {
    /// Distinct values, strictly ascending. Each may have several equal-valued
    /// representations through DIFFERENT defining polynomials.
    reps: Vec<Vec<Anum>>,
    /// A representative point of each of the 2m+1 atoms.
    atoms: Vec<Anum>,
}

#[cfg(test)]
fn build_landmarks() -> Land {
    // Strictly ascending. sqrt(10) and sqrt(5) each appear twice: once as a root
    // of an irreducible quadratic and once as a root of the reducible quartic
    // (x^2-5)(x^2-10). Equal values, different defining polynomials.
    let reps: Vec<Vec<Anum>> = vec![
        vec![sq(10).neg().unwrap()],       // -sqrt(10) ~ -3.162
        vec![ri(-3)],                      // -3
        vec![sq(5).neg().unwrap()],        // -sqrt(5)  ~ -2.236
        vec![ri(-2), rq(-4, 2)],           // -2, two rational spellings
        vec![rq(-1, 2)],                   // -1/2
        vec![ri(0)],                       // 0
        vec![rq(1, 3)],                    // 1/3 (non-dyadic)
        vec![ri(1)],                       // 1
        vec![sq(3)],                       // sqrt(3) ~ 1.732
        vec![sq(5), sq_via(5, 10, 2, 3)],  // sqrt(5), two defining polys
        vec![ri(3)],                       // 3
        vec![sq(10), sq_via(10, 5, 3, 4)], // sqrt(10), two defining polys
    ];
    // Verify the ordering and the equalities with the module's own comparator
    // (this is the model's *precondition*, not its answer).
    for i in 0..reps.len() {
        for r in &reps[i] {
            assert_eq!(
                reps[i][0].cmp_anum(r),
                Some(Ordering::Equal),
                "landmark {i} representations disagree"
            );
        }
        if i + 1 < reps.len() {
            assert_eq!(
                reps[i][0].cmp_anum(&reps[i + 1][0]),
                Some(Ordering::Less),
                "landmarks {i}/{} not ascending",
                i + 1
            );
        }
    }
    // Atom representatives, computed WITHOUT any ialg code: refine each pair of
    // neighbours until their isolating brackets are disjoint, then take a
    // rational strictly between.
    let m = reps.len();
    let mut atoms: Vec<Anum> = Vec::with_capacity(2 * m + 1);
    for i in 0..=m {
        let lo = if i == 0 { None } else { Some(&reps[i - 1][0]) };
        let hi = if i == m { None } else { Some(&reps[i][0]) };
        atoms.push(between(lo, hi));
        if i < m {
            atoms.push(reps[i][0].clone());
        }
    }
    assert_eq!(atoms.len(), 2 * m + 1);
    Land { reps, atoms }
}

/// A rational STRICTLY between `lo` and `hi` (either may be unbounded),
/// computed by bisecting on exact sign evaluations only.
#[cfg(test)]
fn between(lo: Option<&Anum>, hi: Option<&Anum>) -> Anum {
    let f = |a: &Anum| -> BigRational {
        match a {
            Anum::Rational(r) => r.clone(),
            _ => {
                // refine hard, then read the isolating bracket
                let t = Bq::inv_two_pow(80);
                match a.refine(&t).expect("refines") {
                    Anum::Rational(r) => r,
                    Anum::Alg(c) => c.interval().lo().to_rational(),
                }
            }
        }
    };
    match (lo, hi) {
        (None, None) => Anum::rational(BigRational::zero()),
        (None, Some(h)) => Anum::rational(f(h) - BigRational::from_integer(BigInt::from(1000))),
        (Some(l), None) => Anum::rational(f(l) + BigRational::from_integer(BigInt::from(1000))),
        (Some(l), Some(h)) => {
            // Bisect the rational bracket until it is strictly inside.
            let (mut a, mut b) = (f(l), f(h));
            // f(l) may sit slightly below l and f(h) slightly below h; widen and
            // then verify with the exact comparator.
            for _ in 0..200 {
                let mid = (&a + &b) / BigRational::from_integer(BigInt::from(2));
                let v = Anum::rational(mid.clone());
                let above = l.cmp_anum(&v) == Some(Ordering::Less);
                let below = v.cmp_anum(h) == Some(Ordering::Less);
                if above && below {
                    return v;
                }
                if !above {
                    a = mid;
                } else {
                    b = mid;
                }
            }
            panic!("could not find a point strictly between two landmarks");
        }
    }
}

/// One interval, expressed against the landmark indices.
#[cfg(test)]
#[derive(Clone, Copy, Debug)]
struct Spec {
    lo: Option<usize>,
    lo_open: bool,
    hi: Option<usize>,
    hi_open: bool,
}

#[cfg(test)]
impl Spec {
    /// The REFERENCE answer: which atoms this interval covers.
    fn mask(&self, m: usize) -> u64 {
        let n = 2 * m + 1;
        let start: usize = match self.lo {
            None => 0,
            Some(i) => {
                if self.lo_open {
                    2 * i + 2
                } else {
                    2 * i + 1
                }
            }
        };
        let endi: isize = match self.hi {
            None => (n - 1) as isize,
            Some(j) => {
                if self.hi_open {
                    2 * j as isize
                } else {
                    2 * j as isize + 1
                }
            }
        };
        if (start as isize) > endi {
            return 0;
        }
        let mut msk = 0u64;
        for k in start..=(endi as usize) {
            msk |= 1u64 << k;
        }
        msk
    }
}

#[cfg(test)]
fn spec_to_interval(s: &Spec, land: &Land, rng: &mut R, lit: i32) -> Option<DecidedInterval> {
    let pick = |i: usize, rng: &mut R| -> Anum {
        let v = &land.reps[i];
        v[usize::try_from(rng.below(v.len() as u64)).unwrap()].clone()
    };
    let lo = match s.lo {
        None => AEnd::NegInf,
        Some(i) => AEnd::Fin(pick(i, rng)),
    };
    let hi = match s.hi {
        None => AEnd::PosInf,
        Some(j) => AEnd::Fin(pick(j, rng)),
    };
    DecidedInterval::from_bounds(lo, s.lo_open, hi, s.hi_open, Just::of(lit).unwrap())
}

#[cfg(test)]
fn ay_mask(set: &IntervalSet, land: &Land) -> u64 {
    let mut m = 0u64;
    for (k, a) in land.atoms.iter().enumerate() {
        if set
            .contains(a)
            .expect("contains must decide on decidable landmarks")
        {
            m |= 1u64 << k;
        }
    }
    m
}

#[cfg(test)]
fn rand_spec(rng: &mut R, m: usize) -> Spec {
    let lo = if rng.below(8) == 0 {
        None
    } else {
        Some(usize::try_from(rng.below(m as u64)).unwrap())
    };
    let hi = if rng.below(8) == 0 {
        None
    } else {
        Some(usize::try_from(rng.below(m as u64)).unwrap())
    };
    Spec {
        // An infinite endpoint MUST be open; the module refuses a closed one,
        // and the atom model treats an unbounded side as open too.
        lo_open: if lo.is_none() { true } else { rng.bit() },
        hi_open: if hi.is_none() { true } else { rng.bit() },
        lo,
        hi,
    }
}

#[cfg(test)]
fn build_set(specs: &[Spec], land: &Land, rng: &mut R, base: i32) -> Option<IntervalSet> {
    let mut ivs = Vec::new();
    for (i, s) in specs.iter().enumerate() {
        if let Some(interval) =
            spec_to_interval(s, land, rng, base + i32::try_from(i).unwrap())?.into_interval()
        {
            ivs.push(interval);
        }
    }
    IntervalSet::normalize(ivs)
}

#[cfg(test)]
fn ref_mask(specs: &[Spec], m: usize) -> u64 {
    specs.iter().fold(0u64, |acc, s| acc | s.mask(m))
}

#[cfg(test)]
#[derive(Default)]
struct ReferenceCounts {
    cases: u64,
    empties: u64,
    singletons: u64,
    adjacent: u64,
}

#[cfg(test)]
struct ReferenceSetCase<'a> {
    set: &'a IntervalSet,
    mask: u64,
    specs: &'a [Spec],
}

#[cfg(test)]
fn exercise_reference_case(
    land: &Land,
    m: usize,
    all: u64,
    rng: &mut R,
    counts: &mut ReferenceCounts,
) {
    let ka = 1 + usize::try_from(rng.below(4)).unwrap();
    let kb = 1 + usize::try_from(rng.below(4)).unwrap();
    let sa: Vec<Spec> = (0..ka).map(|_| rand_spec(rng, m)).collect();
    let sb: Vec<Spec> = (0..kb).map(|_| rand_spec(rng, m)).collect();

    let Some(a) = build_set(&sa, land, rng, 100) else {
        panic!("build declined on a fully decidable input: {sa:?}");
    };
    let Some(b) = build_set(&sb, land, rng, 200) else {
        panic!("build declined on a fully decidable input: {sb:?}");
    };
    let ma = ref_mask(&sa, m);
    let mb = ref_mask(&sb, m);
    counts.cases += 1;
    counts.empties += u64::from(ma == 0);
    for spec in &sa {
        if spec.lo == spec.hi && !spec.lo_open && !spec.hi_open && spec.lo.is_some() {
            counts.singletons += 1;
        }
    }
    if sa.len() >= 2 && sa[0].hi.is_some() && sa[0].hi == sa[1].lo {
        counts.adjacent += 1;
    }
    assert_reference_set_operations(
        ReferenceSetCase {
            set: &a,
            mask: ma,
            specs: &sa,
        },
        ReferenceSetCase {
            set: &b,
            mask: mb,
            specs: &sb,
        },
        all,
        land,
    );
}

#[cfg(test)]
fn assert_reference_set_operations(
    a: ReferenceSetCase<'_>,
    b: ReferenceSetCase<'_>,
    all: u64,
    land: &Land,
) {
    let ReferenceSetCase {
        set: a,
        mask: ma,
        specs: sa,
    } = a;
    let ReferenceSetCase {
        set: b,
        mask: mb,
        specs: sb,
    } = b;

    assert_eq!(ay_mask(a, land), ma, "MEMBERSHIP diverged: {sa:?}");
    assert_eq!(ay_mask(b, land), mb, "MEMBERSHIP diverged: {sb:?}");
    assert_eq!(
        a.is_empty(),
        ma == 0,
        "IS_EMPTY diverged: {sa:?} mask={ma:#x}"
    );
    assert_eq!(
        b.is_empty(),
        mb == 0,
        "IS_EMPTY diverged: {sb:?} mask={mb:#x}"
    );

    let union = a.union(b).expect("union decides");
    assert_eq!(
        ay_mask(&union, land),
        ma | mb,
        "UNION diverged: {sa:?} U {sb:?}"
    );
    assert_eq!(union.is_empty(), (ma | mb) == 0, "UNION is_empty diverged");

    let intersection = a.intersect(b).expect("intersect decides");
    assert_eq!(
        ay_mask(&intersection, land),
        ma & mb,
        "INTERSECT diverged: {sa:?} n {sb:?}"
    );
    assert_eq!(
        intersection.is_empty(),
        (ma & mb) == 0,
        "INTERSECT is_empty diverged"
    );

    let complement = a.complement().expect("complement decides");
    assert_eq!(
        ay_mask(&complement, land),
        all & !ma,
        "COMPLEMENT diverged: {sa:?}"
    );
    assert_eq!(
        complement.is_empty(),
        (all & !ma) == 0,
        "COMPLEMENT is_empty diverged"
    );

    let difference = a.subtract(b).expect("subtract decides");
    assert_eq!(
        ay_mask(&difference, land),
        ma & !mb,
        "SUBTRACT diverged: {sa:?} \\ {sb:?}"
    );
    assert_eq!(
        difference.is_empty(),
        (ma & !mb) == 0,
        "SUBTRACT is_empty diverged"
    );

    match a.pick() {
        Some(value) => {
            assert!(!a.is_empty(), "pick returned a value from an empty set");
            assert_eq!(a.contains(&value), Some(true), "pick returned a non-member");
            for (index, atom) in land.atoms.iter().enumerate() {
                if atom.cmp_anum(&value) == Some(Ordering::Equal) {
                    assert!(
                        ma >> index & 1 == 1,
                        "pick landed on an atom OUTSIDE the model"
                    );
                }
            }
        }
        None => assert!(a.is_empty(), "pick REFUSED a non-empty set: {sa:?}"),
    }

    let same = a.same_set_as(b).expect("same_set_as decides");
    assert_eq!(same, ma == mb, "SAME_SET_AS diverged: {ma:#x} vs {mb:#x}");
}

#[test]
fn av_reference_model_differential() {
    let land = build_landmarks();
    let m = land.reps.len();
    let n_atoms = 2 * m + 1;
    let all = if n_atoms >= 64 {
        u64::MAX
    } else {
        (1u64 << n_atoms) - 1
    };
    let started = Instant::now();
    let mut counts = ReferenceCounts::default();

    for seed in [
        0xA5F0_1234_DEAD_BEEFu64,
        0x0BAD_C0DE_1234_5678,
        20260806,
        31337,
    ] {
        let mut rng = R::new(seed);
        for _ in 0..2500 {
            exercise_reference_case(&land, m, all, &mut rng, &mut counts);
        }
    }

    println!(
        "AV-REFERENCE: {} cases, {} empty sets, {} closed singletons, \
         {} adjacent pairs, {} atoms, {:?}",
        counts.cases,
        counts.empties,
        counts.singletons,
        counts.adjacent,
        n_atoms,
        started.elapsed()
    );
}
