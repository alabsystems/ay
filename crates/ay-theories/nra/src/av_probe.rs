// ADVERSARIAL VERIFICATION probe harness for `crate::ialg`.
// Not part of the lane under review. Independent reference model + fail-open
// probes + liveness probes. Everything here is `#[cfg(test)]`.

#![allow(clippy::needless_range_loop)]

use std::cmp::Ordering;
use std::time::Instant;

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Zero};

use crate::anum::Anum;
use crate::ialg::*;
use crate::mpbq::{Bq, BqInterval};

// ---------------------------------------------------------------- rng
struct R(u64);
impl R {
    fn new(s: u64) -> Self {
        R(s ^ 0x9E37_79B9_7F4A_7C15)
    }
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }
    fn below(&mut self, n: u64) -> u64 {
        if n == 0 {
            0
        } else {
            self.next() % n
        }
    }
    fn bit(&mut self) -> bool {
        self.next() & 1 == 1
    }
}

// ---------------------------------------------------------------- builders
fn ri(n: i64) -> Anum {
    Anum::rational(BigRational::from_integer(BigInt::from(n)))
}
fn rq(n: i64, d: i64) -> Anum {
    Anum::rational(BigRational::new(BigInt::from(n), BigInt::from(d)))
}
fn bq_i(n: i64) -> Bq {
    Bq::from_int(BigInt::from(n))
}

/// The unique root of `coeffs` in `(lo, hi)`, as an `Anum`.
fn alg(coeffs: &[i64], lo: i64, hi: i64) -> Anum {
    let c: Vec<BigInt> = coeffs.iter().map(|&v| BigInt::from(v)).collect();
    let iv = BqInterval::new(bq_i(lo), bq_i(hi)).expect("ordered bracket");
    Anum::from_poly_interval(&c, &iv).expect("isolating bracket")
}

/// sqrt(d) as a root of `x^2 - d`.
fn sq(d: i64) -> Anum {
    alg(&[-d, 0, 1], 0, d + 1)
}
/// sqrt(d) as a root of the REDUCIBLE `(x^2 - d)(x^2 - e)` — the SAME real
/// value through a DIFFERENT defining polynomial. The bracket must isolate
/// +sqrt(d) away from +sqrt(e) and from the negative roots, so it is given
/// explicitly rather than guessed.
fn sq_via(d: i64, e: i64, lo: i64, hi: i64) -> Anum {
    // (x^2-d)(x^2-e) = x^4 - (d+e)x^2 + d*e
    alg(&[d * e, 0, -(d + e), 0, 1], lo, hi)
}

fn end(a: &Anum) -> AEnd {
    AEnd::Fin(a.clone())
}

fn mk(lo: AEnd, lo_open: bool, hi: AEnd, hi_open: bool, lit: i32) -> Option<Made> {
    AInterval::new(lo, lo_open, hi, hi_open, Just::of(lit).unwrap())
}

// ============================================================================
// PART A — FAIL-OPEN PROBES
//
// For every predicate: construct an input it CANNOT decide and record what
// comes back. A permissive answer is a soundness defect.
// ============================================================================

/// An `Anum` whose comparison against `sq(2)` is genuinely UNDECIDABLE, because
/// `root_separation_exponent` on the combined defining polynomial exceeds
/// `anum::MAX_SEPARATION_BITS`. Returns `None` if no such value was found.
fn undecidable_partner() -> Option<(Anum, Anum)> {
    let a = sq(2);
    // x^2 - K for a huge non-square K: gcd with x^2-2 is 1, so cmp_cell must go
    // through the separation bound, which refuses past 8192 bits.
    for bits in [2600u32, 2725, 2800, 3000, 4000, 8000, 16000] {
        let k: BigInt = (BigInt::one() << bits) + BigInt::from(3);
        let p = vec![-k.clone(), BigInt::zero(), BigInt::one()];
        // sqrt(K) is in (2^(bits/2), 2^(bits/2+1)).
        let lo = Bq::from_int(BigInt::one() << (bits / 2));
        let hi = Bq::from_int(BigInt::one() << (bits / 2 + 1));
        let iv = BqInterval::new(lo, hi)?;
        let Some(b) = Anum::from_poly_interval(&p, &iv) else {
            continue;
        };
        if a.cmp_anum(&b).is_none() {
            return Some((a, b));
        }
    }
    None
}

#[test]
fn av_failopen_every_predicate_on_an_undecidable_input() {
    let Some((a, b)) = undecidable_partner() else {
        panic!("could not manufacture an undecidable comparison — probe is void");
    };
    println!(
        "AV-FAILOPEN: manufactured an UNDECIDABLE pair (deg {} vs deg {})",
        a.degree(),
        b.degree()
    );
    assert_eq!(
        a.cmp_anum(&b),
        None,
        "precondition: the pair is undecidable"
    );

    // 1. AEnd::cmp_value — the ordering of two endpoints.
    let r = end(&a).cmp_value(&end(&b));
    println!("  cmp_value(a, b)                 -> {r:?}");
    assert_eq!(r, None, "FAIL-OPEN: endpoint ordering guessed");
    let r = end(&b).cmp_value(&end(&a));
    println!("  cmp_value(b, a)                 -> {r:?}");
    assert_eq!(r, None, "FAIL-OPEN: endpoint ordering guessed");

    // 2. AInterval::new / is_proved_empty — emptiness of an undecidable interval.
    for (lo_open, hi_open) in [(true, true), (false, false), (true, false), (false, true)] {
        let r = mk(end(&a), lo_open, end(&b), hi_open, 1);
        println!(
            "  AInterval::new(a,{lo_open},b,{hi_open})       -> {}",
            if r.is_none() {
                "None (REFUSED)"
            } else {
                "Some(..)  *** FAIL-OPEN ***"
            }
        );
        assert!(r.is_none(), "FAIL-OPEN: an undecidable interval was built");
        // and the reversed orientation
        let r = mk(end(&b), lo_open, end(&a), hi_open, 1);
        assert!(
            r.is_none(),
            "FAIL-OPEN: an undecidable interval was built (reversed)"
        );
    }

    // 3. AInterval::contains — membership at an undecidable point.
    let dec = match mk(end(&sq(2)), true, end(&sq(3)), true, 1).unwrap() {
        Made::Iv(v) => v,
        Made::Empty => panic!(),
    };
    let r = dec.contains(&b);
    println!("  (sqrt2,sqrt3).contains(b)       -> {r:?}");
    assert_eq!(
        r, None,
        "FAIL-OPEN: membership guessed on an undecidable point"
    );

    // 4. IntervalSet::contains — the set-level predicate.
    let s = IntervalSet::normalize(vec![dec.clone()]).unwrap();
    let r = s.contains(&b);
    println!("  set.contains(b)                 -> {r:?}");
    assert_eq!(r, None, "FAIL-OPEN: set membership guessed");

    // 4b. ... and with the undecidable interval FIRST vs LAST in the scan, since
    // `contains` short-circuits on the first `true`.
    let neg = match mk(AEnd::NegInf, true, end(&ri(-100)), true, 2).unwrap() {
        Made::Iv(v) => v,
        Made::Empty => panic!(),
    };
    let s2 = IntervalSet::normalize(vec![neg, dec.clone()]).unwrap();
    let r = s2.contains(&b);
    println!("  set(2 ivs).contains(b)          -> {r:?}");
    assert_eq!(
        r, None,
        "FAIL-OPEN: set membership guessed after a decided miss"
    );

    // 5. normalize — the fallible insertion sort and the gap scan.
    let ia = match mk(end(&a), true, end(&ri(10)), true, 1).unwrap() {
        Made::Iv(v) => v,
        Made::Empty => panic!(),
    };
    let ib = match mk(end(&b), true, end(&b.add(&ri(1)).unwrap()), true, 2) {
        Some(Made::Iv(v)) => v,
        other => {
            println!("  (b, b+1) itself refused: {other:?} — using a rational-anchored partner");
            match mk(end(&b), true, AEnd::PosInf, true, 2).unwrap() {
                Made::Iv(v) => v,
                Made::Empty => panic!(),
            }
        }
    };
    let r = IntervalSet::normalize(vec![ia.clone(), ib.clone()]);
    println!(
        "  normalize([a..10],[b..])        -> {}",
        if r.is_none() {
            "None (REFUSED)"
        } else {
            "Some(..)  *** FAIL-OPEN ***"
        }
    );
    assert!(
        r.is_none(),
        "FAIL-OPEN: normalize sorted an undecidable pair"
    );
    let r = IntervalSet::normalize(vec![ib.clone(), ia.clone()]);
    assert!(
        r.is_none(),
        "FAIL-OPEN: normalize sorted an undecidable pair (swapped)"
    );

    // 6. union / intersect / subtract where the undecidable comparison is
    //    genuinely REQUIRED. `(0, a)` and `(0, b)` share a rational lower bound,
    //    so the only comparison that can settle either operation is `a` vs `b`.
    //
    //    NOTE, measured: with the sets `(a, 10)` and `(b, +inf)` instead, every
    //    operation SUCCEEDS and returns the right answer — `intersect` compares
    //    lo-with-lo and hi-with-hi only, and neither of those pairings is the
    //    undecidable one. That is correct behaviour, not a fail-open: the module
    //    declines exactly when it needs the comparison it cannot make.
    let zero_a = match mk(end(&ri(0)), true, end(&a), true, 1).unwrap() {
        Made::Iv(v) => v,
        Made::Empty => panic!(),
    };
    let zero_b = match mk(end(&ri(0)), true, end(&b), true, 2).unwrap() {
        Made::Iv(v) => v,
        Made::Empty => panic!(),
    };
    let sa = IntervalSet::normalize(vec![zero_a]).unwrap();
    let sb = IntervalSet::normalize(vec![zero_b]).unwrap();
    println!(
        "  sa=(0,a) sb=(0,b): is_empty {} / {}",
        sa.is_empty(),
        sb.is_empty()
    );
    for (name, r) in [
        ("union", sa.union(&sb)),
        ("intersect", sa.intersect(&sb)),
        ("intersect(rev)", sb.intersect(&sa)),
        ("subtract", sa.subtract(&sb)),
        ("subtract(rev)", sb.subtract(&sa)),
    ] {
        println!(
            "  {name:<14}                  -> {}",
            if r.is_none() {
                "None (REFUSED)"
            } else {
                "Some(..)  *** FAIL-OPEN ***"
            }
        );
        assert!(
            r.is_none(),
            "FAIL-OPEN: {name} produced a set across an undecidable boundary"
        );
    }
    // The disjoint-shape control: `(a,10)` vs `(b,+inf)` needs no a-vs-b
    // comparison and must therefore SUCCEED, proving the declines above are
    // targeted rather than a module that refuses everything algebraic.
    let sa2 = IntervalSet::normalize(vec![ia.clone()]).unwrap();
    let sb2 = IntervalSet::normalize(vec![ib.clone()]).unwrap();
    let ctl = sa2.subtract(&sb2);
    println!(
        "  CONTROL (a,10)\\(b,inf)          -> {}",
        if ctl.is_none() {
            "None"
        } else {
            "Some(..) (expected: no a-vs-b needed)"
        }
    );
    assert!(
        ctl.is_some(),
        "the control declined too — the module refuses everything"
    );

    // 7. same_set_as.
    let r = sa.same_set_as(&sb);
    println!("  same_set_as((0,a),(0,b))        -> {r:?}");
    assert_eq!(r, None, "FAIL-OPEN: set equality guessed");

    // 8. from_sign_condition with an undecidable root list.
    let p: Vec<BigInt> = vec![BigInt::from(-2), BigInt::zero(), BigInt::one()];
    let r = from_sign_condition(&p, &[a.clone(), b.clone()], SignCond::Gt, Just::none());
    println!(
        "  from_sign_condition([a,b])      -> {}",
        if r.is_none() {
            "None (REFUSED)"
        } else {
            "Some(..)  *** FAIL-OPEN ***"
        }
    );
    assert!(
        r.is_none(),
        "FAIL-OPEN: an undecidable root ordering was accepted"
    );

    // 9. as_singleton.
    let probe = AInterval::new(end(&a), false, end(&b), false, Just::none());
    assert!(
        probe.is_none(),
        "FAIL-OPEN: closed undecidable interval built"
    );

    // 10. pick — can a set holding an undecidable endpoint even exist?
    //     `sa` holds `a` and rationals only, so pick must still work there.
    let r = sa.pick();
    println!(
        "  sa.pick()                       -> {:?}",
        r.as_ref().map(classify_value)
    );
    // Not asserted either way: the point is that no set spanning the
    // undecidable boundary can be constructed at all.
}

/// The other half of the fail-open question: `IntervalSet::is_empty` returns a
/// bare `bool`. Prove there is NO route to a set whose emptiness was undecided.
#[test]
fn av_failopen_is_empty_has_no_undecided_route() {
    let Some((a, b)) = undecidable_partner() else {
        panic!("probe void");
    };
    // Every public constructor of IntervalSet, fed an undecidable pair.
    let bad = vec![AInterval::full(Just::none())];
    assert!(IntervalSet::normalize(bad).is_some());

    // The only constructors are empty(), full(), normalize(), from_ordered()
    // (private), intersect(), complement(), union(), subtract(). Each is fed an
    // undecidable input above; all refuse. The remaining question is whether an
    // *interval* holding two mutually-undecidable endpoints can exist at all.
    for lo_open in [true, false] {
        for hi_open in [true, false] {
            assert!(
                AInterval::new(end(&a), lo_open, end(&b), hi_open, Just::none()).is_none(),
                "an interval with undecidable endpoints was constructed"
            );
        }
    }
    println!(
        "AV: no AInterval with mutually-undecidable endpoints can be constructed, \
              so `is_empty()`'s bare bool has no undecided route."
    );
}

// ============================================================================
// PART B — INDEPENDENT REFERENCE MODEL
//
// The point set as a BITMASK over the 2m+1 atoms cut out by m ordered
// landmarks. Union/intersect/complement/subtract are bit operations. Nothing
// in the model does interval reasoning, so it shares no code path with `ialg`.
// ============================================================================

struct Land {
    /// Distinct values, strictly ascending. Each may have several equal-valued
    /// representations through DIFFERENT defining polynomials.
    reps: Vec<Vec<Anum>>,
    /// A representative point of each of the 2m+1 atoms.
    atoms: Vec<Anum>,
}

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
#[derive(Clone, Copy, Debug)]
struct Spec {
    lo: Option<usize>,
    lo_open: bool,
    hi: Option<usize>,
    hi_open: bool,
}

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

fn spec_to_interval(s: &Spec, land: &Land, rng: &mut R, lit: i32) -> Option<Made> {
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
    AInterval::new(lo, s.lo_open, hi, s.hi_open, Just::of(lit).unwrap())
}

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

fn build_set(specs: &[Spec], land: &Land, rng: &mut R, base: i32) -> Option<IntervalSet> {
    let mut ivs = Vec::new();
    for (i, s) in specs.iter().enumerate() {
        match spec_to_interval(s, land, rng, base + i32::try_from(i).unwrap())? {
            Made::Iv(v) => ivs.push(v),
            Made::Empty => {}
        }
    }
    IntervalSet::normalize(ivs)
}

fn ref_mask(specs: &[Spec], m: usize) -> u64 {
    specs.iter().fold(0u64, |acc, s| acc | s.mask(m))
}

#[test]
fn av_reference_model_differential() {
    let land = build_landmarks();
    let m = land.reps.len();
    let n_atoms = 2 * m + 1;
    let all: u64 = if n_atoms >= 64 {
        u64::MAX
    } else {
        (1u64 << n_atoms) - 1
    };
    let t0 = Instant::now();

    let mut cases = 0u64;
    let mut empties = 0u64;
    let mut singletons = 0u64;
    let mut adjacent = 0u64;

    for seed in [
        0xA5F0_1234_DEAD_BEEFu64,
        0x0BAD_C0DE_1234_5678,
        20260806,
        31337,
    ] {
        let mut rng = R::new(seed);
        for _ in 0..2500 {
            let ka = 1 + usize::try_from(rng.below(4)).unwrap();
            let kb = 1 + usize::try_from(rng.below(4)).unwrap();
            let sa: Vec<Spec> = (0..ka).map(|_| rand_spec(&mut rng, m)).collect();
            let sb: Vec<Spec> = (0..kb).map(|_| rand_spec(&mut rng, m)).collect();

            let Some(a) = build_set(&sa, &land, &mut rng, 100) else {
                panic!("build declined on a fully decidable input: {sa:?}");
            };
            let Some(b) = build_set(&sb, &land, &mut rng, 200) else {
                panic!("build declined on a fully decidable input: {sb:?}");
            };
            let ma = ref_mask(&sa, m);
            let mb = ref_mask(&sb, m);
            cases += 1;
            if ma == 0 {
                empties += 1;
            }
            for s in &sa {
                if s.lo == s.hi && !s.lo_open && !s.hi_open && s.lo.is_some() {
                    singletons += 1;
                }
            }
            if sa.len() >= 2 && sa[0].hi.is_some() && sa[0].hi == sa[1].lo {
                adjacent += 1;
            }

            // --- the four claims, each against the bitmask model ---
            assert_eq!(ay_mask(&a, &land), ma, "MEMBERSHIP diverged: {sa:?}");
            assert_eq!(ay_mask(&b, &land), mb, "MEMBERSHIP diverged: {sb:?}");

            // is_empty, BOTH directions.
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

            let u = a.union(&b).expect("union decides");
            assert_eq!(
                ay_mask(&u, &land),
                ma | mb,
                "UNION diverged: {sa:?} U {sb:?}"
            );
            assert_eq!(u.is_empty(), (ma | mb) == 0, "UNION is_empty diverged");

            let i = a.intersect(&b).expect("intersect decides");
            assert_eq!(
                ay_mask(&i, &land),
                ma & mb,
                "INTERSECT diverged: {sa:?} n {sb:?}"
            );
            assert_eq!(i.is_empty(), (ma & mb) == 0, "INTERSECT is_empty diverged");

            let c = a.complement().expect("complement decides");
            assert_eq!(ay_mask(&c, &land), all & !ma, "COMPLEMENT diverged: {sa:?}");
            assert_eq!(
                c.is_empty(),
                (all & !ma) == 0,
                "COMPLEMENT is_empty diverged"
            );

            let d = a.subtract(&b).expect("subtract decides");
            assert_eq!(
                ay_mask(&d, &land),
                ma & !mb,
                "SUBTRACT diverged: {sa:?} \\ {sb:?}"
            );
            assert_eq!(d.is_empty(), (ma & !mb) == 0, "SUBTRACT is_empty diverged");

            // pick: must land on an atom that is IN the reference mask.
            match a.pick() {
                Some(v) => {
                    assert!(!a.is_empty(), "pick returned a value from an empty set");
                    assert_eq!(a.contains(&v), Some(true), "pick returned a non-member");
                    // and z3-free adjudication: the value must be inside the model.
                    let mut hit = false;
                    for (k, at) in land.atoms.iter().enumerate() {
                        if at.cmp_anum(&v) == Some(Ordering::Equal) {
                            assert!(ma >> k & 1 == 1, "pick landed on an atom OUTSIDE the model");
                            hit = true;
                        }
                    }
                    let _ = hit; // a pick may be an interior rational, not an atom rep
                }
                None => assert!(a.is_empty(), "pick REFUSED a non-empty set: {sa:?}"),
            }

            // same_set_as must be a genuine equality: equal iff masks equal.
            let sm = a.same_set_as(&b).expect("same_set_as decides");
            assert_eq!(sm, ma == mb, "SAME_SET_AS diverged: {ma:#x} vs {mb:#x}");
        }
    }

    println!(
        "AV-REFERENCE: {cases} cases, {empties} empty sets, {singletons} closed singletons, \
         {adjacent} adjacent pairs, {} atoms, {:?}",
        n_atoms,
        t0.elapsed()
    );
}

/// Degenerate cases, hand-built, that a random sweep may under-sample.
#[test]
fn av_degenerate_cases() {
    let a1 = sq(10);
    let a2 = sq_via(10, 5, 3, 4); // same value, different defining polynomial
    assert_eq!(a1.cmp_anum(&a2), Some(Ordering::Equal));

    // (a, a) written through DIFFERENT polynomials must be EMPTY.
    for (lo, hi) in [(&a1, &a2), (&a2, &a1), (&a1, &a1)] {
        let r = AInterval::new(end(lo), true, end(hi), true, Just::none());
        assert_eq!(r, Some(Made::Empty), "(a,a) not proved empty");
        let r = AInterval::new(end(lo), true, end(hi), false, Just::none());
        assert_eq!(r, Some(Made::Empty), "(a,a] not proved empty");
        let r = AInterval::new(end(lo), false, end(hi), true, Just::none());
        assert_eq!(r, Some(Made::Empty), "[a,a) not proved empty");
    }
    // [a, a] across representations is a NON-empty singleton containing a.
    let m = AInterval::new(end(&a1), false, end(&a2), false, Just::none()).unwrap();
    let Made::Iv(iv) = m else {
        panic!("[a,a] wrongly empty — LOST CONFLICT / WRONG UNSAT")
    };
    assert_eq!(iv.contains(&a1), Some(true));
    assert_eq!(iv.contains(&a2), Some(true));
    let s = IntervalSet::normalize(vec![iv]).unwrap();
    assert!(!s.is_empty());
    assert_eq!(s.len(), 1);
    assert_eq!(
        s.pick().map(|v| v.cmp_anum(&a1)),
        Some(Some(Ordering::Equal))
    );

    // Half-lines meeting at an algebraic point.
    let lower_open =
        match AInterval::new(AEnd::NegInf, true, end(&a1), true, Just::of(1).unwrap()).unwrap() {
            Made::Iv(v) => v,
            Made::Empty => panic!(),
        };
    let upper_open =
        match AInterval::new(end(&a2), true, AEnd::PosInf, true, Just::of(2).unwrap()).unwrap() {
            Made::Iv(v) => v,
            Made::Empty => panic!(),
        };
    let lower_cl =
        match AInterval::new(AEnd::NegInf, true, end(&a1), false, Just::of(1).unwrap()).unwrap() {
            Made::Iv(v) => v,
            Made::Empty => panic!(),
        };
    let upper_cl =
        match AInterval::new(end(&a2), false, AEnd::PosInf, true, Just::of(2).unwrap()).unwrap() {
            Made::Iv(v) => v,
            Made::Empty => panic!(),
        };
    // (-inf,a) U (a,inf) must NOT merge — the single point a is a genuine gap.
    let s = IntervalSet::normalize(vec![lower_open.clone(), upper_open.clone()]).unwrap();
    assert_eq!(
        s.len(),
        2,
        "an open/open pair at a shared algebraic point was wrongly merged"
    );
    assert_eq!(s.contains(&a1), Some(false));
    assert_eq!(s.contains(&a2), Some(false));
    // (-inf,a] U (a,inf) MUST merge to the whole line.
    let s = IntervalSet::normalize(vec![lower_cl.clone(), upper_open.clone()]).unwrap();
    assert_eq!(s.len(), 1, "adjacent closed/open pair not merged");
    assert_eq!(s.contains(&a1), Some(true));
    // (-inf,a) U [a,inf) likewise.
    let s = IntervalSet::normalize(vec![lower_open.clone(), upper_cl.clone()]).unwrap();
    assert_eq!(s.len(), 1);
    assert_eq!(s.contains(&a2), Some(true));
    // (-inf,a] U [a,inf) — overlapping at one point.
    let s = IntervalSet::normalize(vec![lower_cl.clone(), upper_cl.clone()]).unwrap();
    assert_eq!(s.len(), 1);

    // Intersections at a single shared algebraic point.
    let sl = IntervalSet::normalize(vec![lower_cl.clone()]).unwrap();
    let su = IntervalSet::normalize(vec![upper_cl.clone()]).unwrap();
    let i = sl.intersect(&su).unwrap();
    assert!(
        !i.is_empty(),
        "LOST the singleton {{a}} — a conflict that should not exist"
    );
    assert_eq!(i.len(), 1);
    assert_eq!(i.contains(&a1), Some(true));
    // both justifications survive
    let j = i.justification().unwrap();
    assert!(
        j.lits().contains(&1) && j.lits().contains(&2),
        "justification dropped a side"
    );

    let slo = IntervalSet::normalize(vec![lower_open]).unwrap();
    let suo = IntervalSet::normalize(vec![upper_open]).unwrap();
    let i = slo.intersect(&suo).unwrap();
    assert!(i.is_empty(), "(-inf,a) n (a,inf) is not empty");

    // Complement round-trips at an algebraic endpoint.
    let c = sl.complement().unwrap();
    assert_eq!(c.contains(&a1), Some(false));
    assert_eq!(c.complement().unwrap().same_set_as(&sl), Some(true));

    // +-inf handling.
    let full = IntervalSet::full(Just::none());
    assert!(full.complement().unwrap().is_empty());
    assert!(IntervalSet::empty()
        .complement()
        .unwrap()
        .same_set_as(&full)
        .unwrap());
    // a closed infinity is refused
    assert!(AInterval::new(AEnd::NegInf, false, end(&a1), true, Just::none()).is_none());
    assert!(AInterval::new(end(&a1), true, AEnd::PosInf, false, Just::none()).is_none());
    // reversed infinities are proved EMPTY, not accepted
    assert_eq!(
        AInterval::new(AEnd::PosInf, true, end(&a1), true, Just::none()),
        Some(Made::Empty)
    );
    assert_eq!(
        AInterval::new(end(&a1), true, AEnd::NegInf, true, Just::none()),
        Some(Made::Empty)
    );
    println!("AV-DEGENERATE: all degenerate shapes behave");
}

// ============================================================================
// PART C — LIVENESS
// ============================================================================

#[test]
fn av_liveness_equal_algebraic_endpoints_do_not_refine_forever() {
    let t = Instant::now();
    let a = sq(10);
    let b = sq_via(10, 5, 3, 4);
    for _ in 0..200 {
        assert_eq!(a.cmp_anum(&b), Some(Ordering::Equal));
    }
    println!(
        "AV-LIVENESS: 200 equal-value/different-poly comparisons in {:?}",
        t.elapsed()
    );

    // The same equality driven through every ialg predicate that could spin.
    let t = Instant::now();
    for _ in 0..200 {
        assert_eq!(
            AInterval::new(end(&a), true, end(&b), true, Just::none()),
            Some(Made::Empty)
        );
        let s = IntervalSet::normalize(vec![
            match AInterval::new(AEnd::NegInf, true, end(&a), false, Just::none()).unwrap() {
                Made::Iv(v) => v,
                Made::Empty => panic!(),
            },
            match AInterval::new(end(&b), true, AEnd::PosInf, true, Just::none()).unwrap() {
                Made::Iv(v) => v,
                Made::Empty => panic!(),
            },
        ])
        .unwrap();
        assert_eq!(s.len(), 1);
    }
    println!(
        "AV-LIVENESS: 200 normalize() over equal algebraic endpoints in {:?}",
        t.elapsed()
    );
}

#[test]
fn av_liveness_pathologically_narrow_cells_decline_not_spin() {
    // A cell of width 2^-300 between two RATIONAL roots: the bracket ladder
    // tops out at 2^-256 and must DECLINE.
    let t = Instant::now();
    let k = 300u32;
    let lo = ri(0);
    let hi = Anum::rational(BigRational::new(BigInt::one(), BigInt::one() << k));
    let m = AInterval::new(end(&lo), true, end(&hi), true, Just::none()).unwrap();
    let Made::Iv(iv) = m else {
        panic!("(0, 2^-300) wrongly empty")
    };
    let s = IntervalSet::normalize(vec![iv]).unwrap();
    assert!(!s.is_empty());
    let p = s.pick();
    println!(
        "AV-LIVENESS: pick on a 2^-300-wide open rational cell -> {:?} in {:?}",
        p.as_ref().map(classify_value),
        t.elapsed()
    );

    // The same shape driven through from_sign_condition: p = 2^300 x^2 - x has
    // roots 0 and 2^-300, so the middle open cell has no dyadic sample.
    let t = Instant::now();
    let big = BigInt::one() << k;
    let poly = vec![BigInt::zero(), BigInt::from(-1), big];
    let r = from_sign_condition(&poly, &[ri(0), hi.clone()], SignCond::Gt, Just::none());
    println!(
        "AV-LIVENESS: from_sign_condition over a 2^-300 cell -> {} in {:?}",
        if r.is_none() {
            "None (DECLINED)"
        } else {
            "Some(..)"
        },
        t.elapsed()
    );
    assert!(
        t.elapsed().as_secs() < 30,
        "from_sign_condition took too long"
    );
}

#[test]
fn av_liveness_at_the_ceilings() {
    // MAX_INTERVALS worth of algebraic-endpoint intervals through the O(n^2)
    // fallible insertion sort, fed in DESCENDING order (worst case).
    let t = Instant::now();
    let n = 256usize;
    let mut ivs = Vec::with_capacity(n);
    for i in (0..n).rev() {
        let base = 4 * i as i64;
        // roots of (x - base)^2 - 2  ->  base +- sqrt(2)
        let c = vec![
            BigInt::from(base * base - 2),
            BigInt::from(-2 * base),
            BigInt::one(),
        ];
        let lo_iv = BqInterval::new(bq_i(base - 2), bq_i(base)).unwrap();
        let hi_iv = BqInterval::new(bq_i(base), bq_i(base + 2)).unwrap();
        let lo = Anum::from_poly_interval(&c, &lo_iv).unwrap();
        let hi = Anum::from_poly_interval(&c, &hi_iv).unwrap();
        match AInterval::new(AEnd::Fin(lo), false, AEnd::Fin(hi), false, Just::none()).unwrap() {
            Made::Iv(v) => ivs.push(v),
            Made::Empty => panic!(),
        }
    }
    let build = Instant::now();
    let s = IntervalSet::normalize(ivs).expect("normalizes at the ceiling");
    let dt = build.elapsed();
    assert_eq!(s.len(), n);
    println!(
        "AV-LIVENESS: normalize(256 descending algebraic intervals) = {:?} (setup {:?})",
        dt,
        t.elapsed() - dt
    );

    let t2 = Instant::now();
    let c = s.complement();
    println!(
        "AV-LIVENESS: complement at n=256 -> {} in {:?}",
        if c.is_none() {
            "None (ceiling DECLINE)"
        } else {
            "Some(..)"
        },
        t2.elapsed()
    );

    let t3 = Instant::now();
    let i = s.intersect(&s).expect("self-intersection");
    assert_eq!(i.len(), n);
    println!("AV-LIVENESS: intersect(256,256) in {:?}", t3.elapsed());

    let t4 = Instant::now();
    let v = s.pick();
    println!(
        "AV-LIVENESS: pick at n=256 -> {:?} in {:?}",
        v.map(|x| classify_value(&x)),
        t4.elapsed()
    );
}

#[test]
fn av_liveness_chained_intersections_do_not_grow_degree() {
    // 40 chained intersections; degree and cost must stay flat.
    let t = Instant::now();
    let mut s = IntervalSet::full(Just::none());
    let mut rng = R::new(99);
    for step in 0..40 {
        let mut ivs = Vec::new();
        for j in 0..8 {
            let base = (rng.below(20) as i64) - 10 + j * 3;
            let c = vec![
                BigInt::from(base * base - 2),
                BigInt::from(-2 * base),
                BigInt::one(),
            ];
            let lo_iv = BqInterval::new(bq_i(base - 2), bq_i(base)).unwrap();
            let hi_iv = BqInterval::new(bq_i(base), bq_i(base + 2)).unwrap();
            let lo = Anum::from_poly_interval(&c, &lo_iv).unwrap();
            let hi = Anum::from_poly_interval(&c, &hi_iv).unwrap();
            if let Made::Iv(v) =
                AInterval::new(AEnd::Fin(lo), false, AEnd::Fin(hi), false, Just::none()).unwrap()
            {
                ivs.push(v);
            }
        }
        let Some(o) = IntervalSet::normalize(ivs) else {
            continue;
        };
        let Some(next) = s.intersect(&o) else {
            println!("AV-LIVENESS: chain DECLINED at step {step}");
            break;
        };
        s = next;
        if s.is_empty() {
            break;
        }
        let maxdeg = s
            .intervals()
            .iter()
            .flat_map(|iv| [iv.lo().value(), iv.hi().value()])
            .flatten()
            .map(Anum::degree)
            .max()
            .unwrap_or(0);
        assert!(
            maxdeg <= 2,
            "endpoint degree GREW to {maxdeg} at step {step}"
        );
    }
    println!(
        "AV-LIVENESS: 40 chained intersections, max endpoint degree 2, {:?}",
        t.elapsed()
    );
}

// ============================================================================
// PART D — COST, on MY OWN irregular sequence
// ============================================================================

#[test]
fn av_cost_sweep() {
    // Measurement harness, not a regression (the gate forbids disabled
    // tests): no-ops unless opted in, like the repo's other env-guarded
    // harnesses (AY_LIA_HOT_LOOP_ITERS class).
    if std::env::var_os("AY_NRA_PROFILE").is_none() {
        return;
    }
    println!("n\tkind\tbuild_us\tinter_us\tcompl_us\tpick_us\tpick_rung");
    for &n in &[
        2usize, 7, 19, 41, 83, 127, 173, 211, 249, 255, 256, 257, 400,
    ] {
        for kind in ["rational", "algebraic"] {
            let mut ivs = Vec::with_capacity(n);
            let mut ok = true;
            for i in 0..n {
                let base = 4 * i as i64;
                let (lo, hi) = if kind == "rational" {
                    (ri(base), ri(base + 2))
                } else {
                    let c = vec![
                        BigInt::from(base * base - 2),
                        BigInt::from(-2 * base),
                        BigInt::one(),
                    ];
                    let a = Anum::from_poly_interval(
                        &c,
                        &BqInterval::new(bq_i(base - 2), bq_i(base)).unwrap(),
                    )
                    .unwrap();
                    let b = Anum::from_poly_interval(
                        &c,
                        &BqInterval::new(bq_i(base), bq_i(base + 2)).unwrap(),
                    )
                    .unwrap();
                    (a, b)
                };
                match AInterval::new(AEnd::Fin(lo), false, AEnd::Fin(hi), false, Just::none()) {
                    Some(Made::Iv(v)) => ivs.push(v),
                    _ => {
                        ok = false;
                        break;
                    }
                }
            }
            if !ok {
                println!("{n}\t{kind}\tBUILD-REFUSED");
                continue;
            }
            let t = Instant::now();
            let s = IntervalSet::normalize(ivs);
            let build = t.elapsed().as_micros();
            let Some(s) = s else {
                println!("{n}\t{kind}\t*REFUSED at the ceiling* ({build} us)");
                continue;
            };
            let t = Instant::now();
            let _ = s.intersect(&s);
            let inter = t.elapsed().as_micros();
            let t = Instant::now();
            let c = s.complement();
            let compl = t.elapsed().as_micros();
            let t = Instant::now();
            let p = s.pick();
            let pick = t.elapsed().as_micros();
            println!(
                "{n}\t{kind}\t{build}\t{inter}\t{}\t{pick}\t{:?}",
                if c.is_none() {
                    "DECLINED".to_string()
                } else {
                    compl.to_string()
                },
                p.map(|v| classify_value(&v))
            );
        }
    }
}

/// The measurement the lane's own harness cannot make: `normalize` sorts with a
/// FALLIBLE comparator, so it is an O(n^2) insertion sort. `ialg_cost.rs` builds
/// its sweep with `for k in 0..n`, i.e. ALREADY ASCENDING, which is insertion
/// sort's best case (`n - 1` comparisons). MCSAT does not hand cells over
/// sorted, so the number that matters is the other end.
#[test]
fn av_cost_normalize_input_order() {
    // Measurement harness, not a regression (the gate forbids disabled
    // tests): no-ops unless opted in, like the repo's other env-guarded
    // harnesses (AY_LIA_HOT_LOOP_ITERS class).
    if std::env::var_os("AY_NRA_PROFILE").is_none() {
        return;
    }
    println!("n\torder\tbuild_us\tcmp_calls_bound");
    for &n in &[3usize, 11, 29, 61, 113, 181, 233, 256] {
        let mut base = Vec::with_capacity(n);
        for i in 0..n {
            let b = 4 * i as i64;
            let c = vec![BigInt::from(b * b - 2), BigInt::from(-2 * b), BigInt::one()];
            let lo = Anum::from_poly_interval(&c, &BqInterval::new(bq_i(b - 2), bq_i(b)).unwrap())
                .unwrap();
            let hi = Anum::from_poly_interval(&c, &BqInterval::new(bq_i(b), bq_i(b + 2)).unwrap())
                .unwrap();
            match AInterval::new(AEnd::Fin(lo), false, AEnd::Fin(hi), false, Just::none()).unwrap()
            {
                Made::Iv(v) => base.push(v),
                Made::Empty => panic!(),
            }
        }
        for order in ["ascending", "descending", "shuffled"] {
            let mut ivs = base.clone();
            match order {
                "descending" => ivs.reverse(),
                "shuffled" => {
                    let mut rng = R::new(7);
                    for i in (1..ivs.len()).rev() {
                        let j = usize::try_from(rng.below((i + 1) as u64)).unwrap();
                        ivs.swap(i, j);
                    }
                }
                _ => {}
            }
            let t = Instant::now();
            let s = IntervalSet::normalize(ivs).expect("normalizes");
            let us = t.elapsed().as_micros();
            assert_eq!(s.len(), n);
            println!("{n}\t{order}\t{us}\t{}", n * (n - 1) / 2);
        }
    }
}

#[test]
fn av_cost_endpoint_degree() {
    // Measurement harness, not a regression (the gate forbids disabled
    // tests): no-ops unless opted in, like the repo's other env-guarded
    // harnesses (AY_LIA_HOT_LOOP_ITERS class).
    if std::env::var_os("AY_NRA_PROFILE").is_none() {
        return;
    }
    // What endpoint DEGREE costs, on an irregular ladder.
    println!("deg\tn\tbuild_us\tinter_us\tcompl_us\tpick_us");
    for &deg in &[2usize, 3, 5, 6, 8, 10, 12, 16, 20, 24, 32, 48, 64] {
        // x^deg - 2 has one positive real root (and a negative one for even deg).
        let mut c = vec![BigInt::zero(); deg + 1];
        c[0] = BigInt::from(-2);
        c[deg] = BigInt::one();
        let Some(r) = Anum::from_poly_interval(&c, &BqInterval::new(bq_i(1), bq_i(2)).unwrap())
        else {
            println!("{deg}\t-\tROOT-REFUSED");
            continue;
        };
        // Build a set of 13 intervals whose endpoints are shifts of that root.
        let n = 13usize;
        let t = Instant::now();
        let mut ivs = Vec::new();
        let mut ok = true;
        for i in 0..n {
            let shift = 4 * i as i64;
            let (Some(a), Some(b)) = (r.add(&ri(shift)), r.add(&ri(shift + 1))) else {
                ok = false;
                break;
            };
            match AInterval::new(AEnd::Fin(a), false, AEnd::Fin(b), false, Just::none()) {
                Some(Made::Iv(v)) => ivs.push(v),
                _ => {
                    ok = false;
                    break;
                }
            }
        }
        if !ok {
            println!("{deg}\t{n}\tSHIFT-REFUSED (after {:?})", t.elapsed());
            continue;
        }
        let t = Instant::now();
        let Some(s) = IntervalSet::normalize(ivs) else {
            println!("{deg}\t{n}\tNORMALIZE-REFUSED");
            continue;
        };
        let build = t.elapsed().as_micros();
        let t = Instant::now();
        let _ = s.intersect(&s);
        let inter = t.elapsed().as_micros();
        let t = Instant::now();
        let _ = s.complement();
        let compl = t.elapsed().as_micros();
        let t = Instant::now();
        let _ = s.pick();
        let pick = t.elapsed().as_micros();
        println!("{deg}\t{n}\t{build}\t{inter}\t{compl}\t{pick}");
    }
}

#[test]
fn av_cost_sign_cells() {
    // Measurement harness, not a regression (the gate forbids disabled
    // tests): no-ops unless opted in, like the repo's other env-guarded
    // harnesses (AY_LIA_HOT_LOOP_ITERS class).
    if std::env::var_os("AY_NRA_PROFILE").is_none() {
        return;
    }
    println!("roots\tcells\tus");
    for &m in &[1usize, 3, 6, 11, 19, 30, 47, 74, 101, 127] {
        // (x-1)(x-2)...(x-m) via repeated multiplication
        let mut p = vec![BigInt::one()];
        for i in 1..=m {
            let lin = vec![BigInt::from(-(i as i64)), BigInt::one()];
            let mut out = vec![BigInt::zero(); p.len() + 1];
            for (a, x) in p.iter().enumerate() {
                for (b, y) in lin.iter().enumerate() {
                    out[a + b] += x * y;
                }
            }
            p = out;
        }
        let roots: Vec<Anum> = (1..=m).map(|i| ri(i as i64)).collect();
        let t = Instant::now();
        let r = from_sign_condition(&p, &roots, SignCond::Gt, Just::none());
        let us = t.elapsed().as_micros();
        match r {
            Some(s) => println!("{m}\t{}\t{us}", s.len()),
            None => println!("{m}\tDECLINED\t{us}"),
        }
    }
}

/// Does the lane's own `ialg_cost::algebraic_set(n)` actually produce `n`
/// intervals? Its endpoints are `3k + sqrt(d)` and `3k + 2 + sqrt(d)` for a
/// ROTATING `d`, so consecutive cells can overlap and merge.
#[test]
fn av_cost_lane_algebraic_set_size_is_not_n() {
    // Measurement harness, not a regression (the gate forbids disabled
    // tests): no-ops unless opted in, like the repo's other env-guarded
    // harnesses (AY_LIA_HOT_LOOP_ITERS class).
    if std::env::var_os("AY_NRA_PROFILE").is_none() {
        return;
    }
    const DS: [i64; 4] = [2, 3, 5, 7];
    println!("n\tlane_algebraic_set.len()\tlane_rational_set.len()");
    for &n in &[3usize, 23, 91, 199, 251, 256] {
        let mut ivs = Vec::with_capacity(n);
        for k in 0..n {
            let d = DS[k % DS.len()];
            let base = 3 * k as i64;
            let lo = ri(base).add(&sq(d)).unwrap();
            let hi = ri(base + 2).add(&sq(d)).unwrap();
            match AInterval::new(AEnd::Fin(lo), true, AEnd::Fin(hi), true, Just::none()).unwrap() {
                Made::Iv(v) => ivs.push(v),
                Made::Empty => panic!(),
            }
        }
        let alg_len = IntervalSet::normalize(ivs).map(|s| s.len());
        let mut rivs = Vec::with_capacity(n);
        for k in 0..n {
            let k = k as i64;
            match AInterval::new(
                AEnd::Fin(ri(3 * k)),
                false,
                AEnd::Fin(ri(3 * k + 1)),
                false,
                Just::none(),
            )
            .unwrap()
            {
                Made::Iv(v) => rivs.push(v),
                Made::Empty => panic!(),
            }
        }
        let rat_len = IntervalSet::normalize(rivs).map(|s| s.len());
        println!("{n}\t{alg_len:?}\t{rat_len:?}");
    }
}

/// REGRESSION GUARD for the blind spot this probe originally FOUND.
///
/// As first measured (on the pre-integration cut of `ialg.rs`),
/// `from_sign_condition` verified that the root list ASCENDS but never that it
/// IS the root list of `p`. An incomplete list silently produced a wrong
/// feasible set in the UNSOUND direction: the EMPTY set for a non-empty one,
/// i.e. a conflict that does not exist.
///
/// The integrated `ialg.rs` closes it — see the "STRONG half" comment on
/// `from_sign_condition`, which cites this very `p = x^2 - 1` case. The probe is
/// kept, inverted, so the refusal cannot silently regress.
#[test]
fn av_from_sign_condition_refuses_an_unverified_root_list() {
    // p = x^2 - 1, real roots -1 and +1.
    let p = vec![BigInt::from(-1), BigInt::zero(), BigInt::one()];
    let full_roots = vec![ri(-1), ri(1)];
    let partial = vec![ri(1)]; // -1 dropped

    // Ground truth with the COMPLETE list is unchanged: {p<0} is (-1,1).
    let lt_ok = from_sign_condition(&p, &full_roots, SignCond::Lt, Just::none()).unwrap();
    assert!(!lt_ok.is_empty(), "{{p<0}} is (-1,1), not empty");
    assert_eq!(lt_ok.contains(&ri(0)), Some(true));

    // The SAME query with an INCOMPLETE list must now be REFUSED outright,
    // rather than answered with the empty set.
    assert!(
        from_sign_condition(&p, &partial, SignCond::Lt, Just::none()).is_none(),
        "an incomplete root list must be refused, not answered with `empty` \
         (that was the original unsound finding)"
    );
    assert!(
        from_sign_condition(&p, &partial, SignCond::Gt, Just::none()).is_none(),
        "the too-large direction must be refused as well"
    );

    // A root list containing a NON-root must be refused too.
    let bogus = vec![ri(-1), ri(0), ri(1)];
    assert!(
        from_sign_condition(&p, &bogus, SignCond::Eq, Just::none()).is_none(),
        "a non-root (0) in the list must be refused"
    );
}
