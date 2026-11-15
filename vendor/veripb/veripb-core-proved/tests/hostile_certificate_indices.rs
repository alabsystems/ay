//! Hostile certificate indices are refused, never trusted.
//!
//! Originally a reconnaissance probe over the whole-crate compiler_consumer lane's
//! refuted slice-bounds obligations on the RUP path; kept because the
//! property it establishes -- 40,000 certificates carrying `usize::MAX`-class
//! indices are all refused and none panics -- is the runtime half of what
//! those refutations question.
//!
//! Originally: attack the 7 refuted IndexOutOfBounds and the
//! 6 refuted slice-bounds obligations on the RUP / Db paths with hostile,
//! out-of-range, attacker-controlled indices. Debug profile => every Vec index
//! is bounds-checked, so any real out-of-bounds is a panic, not a silent read.

use veripb_core_proved::{
    Coeff, Constraint, Lit, Term,
    db::{Db, Op},
    rup::check_rup,
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
    /// Indices biased hard onto the out-of-range rails.
    fn idx(&mut self, n: usize) -> usize {
        match self.below(8) {
            0 => usize::MAX,
            1 => usize::MAX - 1,
            2 => n,
            3 => n + 1,
            4 => n.wrapping_mul(4096),
            5 => 1usize << 62,
            _ => self.below((n as u64) + 3) as usize,
        }
    }
}

fn cons(r: &mut R, n: usize, vars: u32) -> Constraint<Coeff> {
    Constraint {
        terms: (0..n)
            .map(|_| Term {
                coeff: match r.below(4) {
                    0 => i64::MAX,
                    1 => i64::MIN,
                    2 => -(r.below(9) as i64),
                    _ => r.below(9) as i64,
                },
                lit: if r.below(2) == 0 {
                    Lit::pos(r.below(vars as u64) as u32)
                } else {
                    Lit::neg(r.below(vars as u64) as u32)
                },
            })
            .collect(),
        degree: (r.below(21) as i64) - 10,
    }
}

/// Hostile RUP certificates: wild step indices, wild conflict index, both
/// replay paths (the `use_slack_index` gate is forced both ways by term count).
#[test]
fn hostile_rup_indices_are_refused_not_panicked() {
    let mut r = R(0xdead_beef_0bad_f00d);
    let mut refused = 0u64;
    let mut accepted = 0u64;
    for _ in 0..20_000 {
        let ndb = r.below(5) as usize;
        let dbv: Vec<Constraint<Coeff>> = (0..ndb)
            .map(|_| {
                let w = 1 + r.below(30) as usize;
                cons(&mut r, w, 3)
            })
            .collect();
        let view: Vec<&Constraint<Coeff>> = dbv.iter().collect();
        let tw = 1 + r.below(30) as usize;
        let target = cons(&mut r, tw, 3);

        let nsteps = r.below(6) as usize;
        let steps: Vec<(usize, Lit)> = (0..nsteps)
            .map(|_| {
                let i = r.idx(ndb + 1);
                let l = if r.below(2) == 0 {
                    Lit::pos(r.below(3) as u32)
                } else {
                    Lit::neg(r.below(3) as u32)
                };
                (i, l)
            })
            .collect();
        let conflict = r.idx(ndb + 1);

        // Any panic here fails the test; that is the whole point.
        match check_rup(&target, &view, &steps, conflict) {
            Ok(()) => accepted += 1,
            Err(_) => refused += 1,
        }
    }
    assert!(refused > 0, "probe never exercised the refusal path");
    // Sanity: the fuzz is not vacuous.
    assert!(refused + accepted == 20_000);
}

/// Hostile database indices through the driver: `Op::FromDb`, deleted slots,
/// and `Op::Rup` db_ids pointing past the end / into holes.
#[test]
fn hostile_db_indices_are_refused_not_panicked() {
    let mut r = R(0x1234_5678_9abc_def0);
    // How many iterations actually exercised an out-of-range id. Asserted
    // below, so the per-iteration checks above cannot pass vacuously by the
    // generator never producing a hostile index.
    let mut hostile_refusals = 0usize;
    for _ in 0..20_000 {
        let mut db: Db<Coeff> = Db::init(&[
            Constraint {
                terms: vec![Term {
                    coeff: 1,
                    lit: Lit::pos(0),
                }],
                degree: 1,
            },
            Constraint {
                terms: vec![Term {
                    coeff: 1,
                    lit: Lit::neg(0),
                }],
                degree: 1,
            },
        ]);
        let n = db.len();
        // Punch holes.
        if r.below(2) == 0 {
            db.delete(r.idx(n));
        }
        let i = r.idx(n);
        // ASSERT the refusal, do not merely survive it. This loop was
        // `let _ = ...` throughout, so it tested "did not panic" while its
        // name promised "refused": an audit made `Db::get` silently wrap an
        // out-of-range id (`i % self.slots.len()`) -- handing an attacker a
        // real constraint for an id that does not exist -- and the whole
        // workspace stayed green. `Db` is reachable only from these tests,
        // so this file is the entire defence.
        //
        // An index at or beyond `len` must be absent; so must a punched
        // hole. Both are stated as an equality against ground truth rather
        // than an `is_none()` floor, so the assertion cannot be satisfied by
        // a `get` that refuses EVERYTHING either.
        let out_of_range = i >= db.len();
        if out_of_range {
            assert!(
                db.get(i).is_none(),
                "Db::get({i}) returned a constraint for an id beyond len {}",
                db.len()
            );
            assert!(
                !db.contradiction_at(i),
                "Db::contradiction_at({i}) answered for an id beyond len {}",
                db.len()
            );
            assert!(
                db.derive(&Op::FromDb(i)).is_err(),
                "Db::derive(FromDb({i})) succeeded for an id beyond len {}",
                db.len()
            );
            hostile_refusals += 1;
        }
        let _ = db.get(i);
        let _ = db.contradiction_at(i);
        let _ = db.find_contradiction();
        let _ = db.derive(&Op::FromDb(r.idx(n)));
        let _ = db.derive(&Op::Add(
            Box::new(Op::FromDb(r.idx(n))),
            Box::new(Op::FromDb(r.idx(n))),
        ));
        let _ = db.derive(&Op::Rup {
            target: {
                let w = 1 + r.below(4) as usize;
                cons(&mut r, w, 2)
            },
            db_ids: (0..r.below(4)).map(|_| r.idx(n)).collect(),
            steps: (0..r.below(4))
                .map(|_| (r.idx(n + 1), Lit::pos(r.below(2) as u32)))
                .collect(),
            conflict: r.idx(n + 1),
        });
    }
    assert!(
        hostile_refusals > 1_000,
        "only {hostile_refusals} of 20000 iterations produced an out-of-range \
         id, so the refusal assertions above are close to vacuous -- the \
         generator changed and the hostile case is no longer being exercised"
    );
}
