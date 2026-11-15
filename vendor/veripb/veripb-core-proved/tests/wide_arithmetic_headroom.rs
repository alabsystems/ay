//! The i128 `Wide` arithmetic has the headroom its soundness argument claims.
//!
//! The whole-crate compiler_consumer lane *refutes* the panic-freedom obligations on
//! `<i128 as Exact>::add/sub/neg` and `div_mod_floor` — bare `+`/`-`/`neg`
//! with no precondition, and a `debug_assert!(*k > 0)` that release compiles
//! out. Those refutations are honest: the functions, in isolation, can wrap
//! and can divide by zero. The reason they are not defects is an argument
//! about the callers — every i128 on the live path is a widened i64 or an
//! accumulation of at most N of them, so overflow needs N > 2^64 while memory
//! caps N near 2^36, and every divisor has passed a `k > 0` check before the
//! shim is reached. Sixty-plus bits of headroom, and zero divisors
//! unreachable.
//!
//! An argument about callers is exactly the shape defects 20-24 had, so it is
//! tested rather than trusted. The negative control is what makes this test
//! worth its runtime: truncating `<i128 as Exact>::add` to i64 makes it fail
//! immediately on a diverged degree, so it detects precisely the defect class
//! whose absence it asserts.
//!
//! Strategy: run every rule at the narrow domain (`Coeff = i64`, `Exact = i128`,
//! which is what the live bridge tries FIRST) and at `Big` (BigInt, exact), on
//! maximally adversarial inputs, and demand the two agree. A silent i128 wrap
//! makes them diverge. Debug profile => overflow-checks ON and `debug_assert!`
//! armed, so a wrap or a zero divisor panics outright.

use veripb_core_proved::{
    Big, Coeff, Constraint, Lit, Term, add, divide, mir::mir as mir_rule, mir::mir_variable,
    multiply, negate, normalize::normalize, saturate, weaken_degree,
};

struct R(u64);
impl R {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
    /// Extreme-biased coefficient: mostly at the i64 rails.
    fn coeff(&mut self) -> Coeff {
        match self.below(8) {
            0 => i64::MAX,
            1 => i64::MIN,
            2 => i64::MIN + 1,
            3 => i64::MAX - 1,
            4 => -(self.next() as i64).saturating_abs(),
            5 => (self.next() >> 1) as i64,
            6 => self.next() as i64,
            _ => (self.below(9) as i64) - 4,
        }
    }
}

fn to_big(c: &Constraint<Coeff>) -> Constraint<Big> {
    Constraint {
        terms: c
            .terms
            .iter()
            .map(|t| Term {
                coeff: Big::from(t.coeff),
                lit: t.lit,
            })
            .collect(),
        degree: Big::from(c.degree),
    }
}

/// Narrow result must be either a refusal, or equal to the Big result.
fn agree<A, B>(narrow: Result<Constraint<Coeff>, A>, big: Result<Constraint<Big>, B>, what: &str) {
    if let Ok(n) = narrow {
        let b = big.unwrap_or_else(|_| panic!("{what}: narrow accepted where Big refused"));
        assert_eq!(
            n.degree as i128,
            i128::try_from(&b.degree).unwrap(),
            "{what}: degree diverged"
        );
        assert_eq!(n.terms.len(), b.terms.len(), "{what}: arity diverged");
        for (tn, tb) in n.terms.iter().zip(b.terms.iter()) {
            assert_eq!(tn.lit, tb.lit, "{what}: literal diverged");
            assert_eq!(
                tn.coeff as i128,
                i128::try_from(&tb.coeff).unwrap(),
                "{what}: coeff diverged"
            );
        }
    }
}

fn gen_constraint(r: &mut R, n: usize, vars: u32) -> Constraint<Coeff> {
    let terms = (0..n)
        .map(|_| Term {
            coeff: r.coeff(),
            lit: if r.below(2) == 0 {
                Lit::pos(r.below(vars as u64) as u32)
            } else {
                Lit::neg(r.below(vars as u64) as u32)
            },
        })
        .collect();
    Constraint {
        terms,
        degree: r.coeff(),
    }
}

#[test]
fn narrow_i128_never_diverges_from_exact_big_on_adversarial_inputs() {
    let mut r = R(0x5eed_1234_9876_abcd);
    // Wide terms AND heavy variable reuse: reuse is what makes `ins_term`'s
    // merge accumulate, which is the only unbounded i128 accumulation there is.
    for round in 0..4000u32 {
        let n = 1 + (r.below(40) as usize);
        let vars = 1 + r.below(4) as u32; // few vars => maximal merging
        let c = gen_constraint(&mut r, n, vars);
        let cb = to_big(&c);

        agree(normalize(&c), normalize(&cb), "normalize");
        agree(saturate(&c), saturate(&cb), "saturate");
        agree(negate(&c), negate(&cb), "negate");

        let k = r.coeff();
        agree(multiply(k, &c), multiply(Big::from(k), &cb), "multiply");
        agree(divide(k, &c), divide(Big::from(k), &cb), "divide");
        agree(
            weaken_degree(&c, k),
            weaken_degree(&cb, Big::from(k)),
            "weaken_degree",
        );

        // MIR needs a normalized (all-nonneg) input; feed it the normalized form
        // when one exists, which is exactly how the live checker reaches it.
        if let (Ok(nn), Ok(nb)) = (normalize(&c), normalize(&cb)) {
            agree(mir_rule(k, &nn), mir_rule(Big::from(k), &nb), "mir");
            agree(
                mir_variable(k, &nn),
                mir_variable(Big::from(k), &nb),
                "mir_variable",
            );
        }
        // Variable-form MIR on an UNnormalized constraint: the one shape with
        // mixed signs, where `neg_sum` accumulates without an all-nonneg bound.
        agree(
            mir_variable(k, &c),
            mir_variable(Big::from(k), &cb),
            "mir_variable_raw",
        );

        let n2 = 1 + (r.below(40) as usize);
        let c2 = gen_constraint(&mut r, n2, vars);
        let c2b = to_big(&c2);
        agree(add(&c, &c2), add(&cb, &c2b), "add");

        if round % 500 == 0 {
            // keep the harness honest about actually running
            assert!(n >= 1);
        }
    }
}

/// The accumulation bound, at a size big enough to matter: 200k terms all on
/// one variable at the i64 rail. Max |Wide| reached is ~N*2^63 = 2^81.
#[test]
fn massive_single_variable_accumulation_stays_exact() {
    const N: usize = 200_000;
    for &(sign, deg) in &[(1i64, i64::MIN), (-1i64, i64::MAX), (1i64, i64::MAX)] {
        let terms: Vec<Term<Coeff>> = (0..N)
            .map(|i| Term {
                coeff: if sign > 0 { i64::MAX } else { i64::MIN },
                lit: if i % 2 == 0 { Lit::pos(0) } else { Lit::neg(0) },
            })
            .collect();
        let c = Constraint { terms, degree: deg };
        let cb = to_big(&c);
        agree(normalize(&c), normalize(&cb), "normalize@200k");
        agree(negate(&c), negate(&cb), "negate@200k");
        agree(
            mir_variable(3, &c),
            mir_variable(Big::from(3), &cb),
            "mir_variable@200k",
        );
        // The contradiction test the driver uses: coeff_sum() < degree.widen().
        let narrow_contra = c.coeff_sum() < (c.degree as i128);
        let big_contra = cb.coeff_sum() < cb.degree.clone();
        assert_eq!(
            narrow_contra, big_contra,
            "contradiction test diverged @200k"
        );
    }
}
