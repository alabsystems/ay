// Targeted witness for the oracle blind spot: an input on which a corrupted
// `sample_points` (open cells dropped only when the merged root list exceeds 6)
// makes `explain_univariate` EMIT a clause that is not a theory consequence.
//
// The in-tree oracle's generator tops out at 6 merged roots, so it cannot
// build this input at all. Run against the pristine module it must print
// "clause emitted, cited conjunction UNSAT" (or nothing); against the injected
// module it prints a clause whose citation set z3 finds SATISFIABLE.

use num_bigint::BigInt;
use num_rational::BigRational as Q;
use num_traits::Zero;

use ay_nra::oracle_api::{
    oexplain_clause_is_valid, oexplain_univariate, ODyadicAnum, OExplainLit, OISignCond,
};

fn bi(n: i64) -> BigInt {
    BigInt::from(n)
}
fn rat(n: i64) -> ODyadicAnum {
    ODyadicAnum::rational(Q::from_integer(bi(n)))
}
fn linear_prod(rs: &[i64]) -> Vec<BigInt> {
    let mut p = vec![bi(1)];
    for &r in rs {
        let mut np = vec![BigInt::zero(); p.len() + 1];
        for (i, c) in p.iter().enumerate() {
            np[i + 1] += c;
            np[i] -= c * bi(r);
        }
        p = np;
    }
    p
}
fn render(p: &[BigInt]) -> String {
    let mut t: Vec<String> = Vec::new();
    for (i, c) in p.iter().enumerate() {
        if c.is_zero() {
            continue;
        }
        t.push(match i {
            0 => format!("{c}"),
            1 => format!("{c}*x"),
            _ => format!("{c}*x^{i}"),
        });
    }
    t.join(" + ")
}
fn smt(p: &[BigInt], c: OISignCond) -> String {
    let mut t: Vec<String> = Vec::new();
    for (i, co) in p.iter().enumerate() {
        if co.is_zero() {
            continue;
        }
        let cs = if *co < BigInt::zero() {
            format!("(- {})", -co)
        } else {
            format!("{co}")
        };
        t.push(match i {
            0 => cs,
            _ => format!("(* {cs} {})", vec!["x"; i].join(" ")),
        });
    }
    let e = if t.len() == 1 {
        t[0].clone()
    } else {
        format!("(+ {})", t.join(" "))
    };
    match c {
        OISignCond::Lt => format!("(< {e} 0)"),
        OISignCond::Le => format!("(<= {e} 0)"),
        OISignCond::Eq => format!("(= {e} 0)"),
        OISignCond::Ne => format!("(not (= {e} 0))"),
        OISignCond::Ge => format!("(>= {e} 0)"),
        OISignCond::Gt => format!("(> {e} 0)"),
    }
}

fn main() {
    // #govern: see crates/ay-sys/src/govern.rs.
    ay_sys::govern::arm();
    // A: P > 0 where P = (x-1)(x-3)(x-5)(x-7)(x-9)(x-11)(x-13)  [7 roots]
    // B: x - 20 < 0                                             [1 root]
    // C: x(x-20) >= 0                                           [2 roots]
    // {A,B,C} is UNSAT; every pair is SATISFIABLE.
    let pa = linear_prod(&[1, 3, 5, 7, 9, 11, 13]);
    let pb = vec![bi(-20), bi(1)];
    let pc = vec![bi(0), bi(-20), bi(1)];
    let lits = vec![
        OExplainLit {
            lit: 1,
            p: pa.clone(),
            cond: OISignCond::Gt,
            roots: [1, 3, 5, 7, 9, 11, 13].iter().map(|&r| rat(r)).collect(),
        },
        OExplainLit {
            lit: 2,
            p: pb.clone(),
            cond: OISignCond::Lt,
            roots: vec![rat(20)],
        },
        OExplainLit {
            lit: 3,
            p: pc.clone(),
            cond: OISignCond::Ge,
            roots: vec![rat(0), rat(20)],
        },
    ];
    println!("L1: ({}) > 0", render(&pa));
    println!("L2: ({}) < 0", render(&pb));
    println!("L3: ({}) >= 0", render(&pc));
    println!(
        "\nclause_is_valid(full {{L1,L2,L3}})  = {:?}   (truth: UNSAT, so `true`)",
        oexplain_clause_is_valid(&lits)
    );
    println!(
        "clause_is_valid(pair  {{L1,L2}})    = {:?}   (truth: SAT at x=2, so `false`)",
        oexplain_clause_is_valid(&lits[..2])
    );

    let mut f = String::from("(set-logic QF_NRA)\n(declare-fun x () Real)\n");
    match oexplain_univariate(&lits) {
        Some(e) => {
            println!(
                "\nexplain_univariate -> clause {:?}  cited {:?}",
                e.lits, e.cited
            );
            f.push_str("(push 1)\n");
            for c in &e.cited {
                let l = lits.iter().find(|l| l.lit == *c).unwrap();
                f.push_str(&format!("(assert {})\n", smt(&l.p, l.cond)));
            }
            f.push_str("(check-sat)\n(pop 1)\n");
            std::fs::write("/tmp/vgap_cited.smt2", &f).unwrap();
            println!("cited conjunction written to /tmp/vgap_cited.smt2 -- z3 must say `unsat`");
        }
        None => println!("\nexplain_univariate -> None"),
    }
}
