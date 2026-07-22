//! Differential soundness oracle: cross-check the difference-logic engine
//! against z3 on randomly generated QF_IDL / QF_RDL systems.
//!
//! For each random system we:
//!   1. ask our engine (`solve_int_atoms` / `solve_rational_atoms`),
//!   2. ask z3 for ground truth (`z3 -in` on the serialized SMT-LIB),
//!   3. assert the **sat/unsat labels agree**, and
//!   4. on SAT, append our model as equality assertions and confirm **z3 still
//!      returns sat** — real model validation, not just label agreement.
//!
//! The test SKIPS gracefully (passes, printing a note) when `z3` is not on
//! `PATH`, and runs for real when it is present. The engine's own always-on
//! `debug_assert!` self-certification covers soundness even in the skip case;
//! this oracle is the external confirmation.

use ay_diff_logic::atom::Op;
use ay_diff_logic::{solve_int_atoms, solve_rational_atoms, BuildResult, DiffAtom};
use num_rational::BigRational;
use num_traits::Signed;
use rand::{Rng, SeedableRng};
use rand_chacha::ChaCha8Rng;
use std::io::Write;
use std::process::{Command, Stdio};

const N_VARS: usize = 6;
const NUM_INSTANCES: usize = 400; // per logic (IDL, RDL)

/// Locate a z3 binary, or `None` to skip.
fn z3_path() -> Option<String> {
    for cand in [
        "z3",
        "/opt/homebrew/bin/z3",
        "/usr/local/bin/z3",
        "/usr/bin/z3",
    ] {
        if Command::new(cand)
            .arg("--version")
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .status()
            .map(|s| s.success())
            .unwrap_or(false)
        {
            return Some(cand.to_string());
        }
    }
    None
}

/// Run a z3 SMT-LIB script and return its trimmed `(check-sat)` answer
/// ("sat" / "unsat" / "unknown").
fn run_z3(z3: &str, script: &str) -> String {
    let mut child = Command::new(z3)
        .arg("-in")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn z3");
    child
        .stdin
        .take()
        .unwrap()
        .write_all(script.as_bytes())
        .expect("write z3 stdin");
    let out = child.wait_with_output().expect("z3 output");
    let stdout = String::from_utf8_lossy(&out.stdout);
    // First non-empty line is the check-sat verdict.
    stdout
        .lines()
        .map(str::trim)
        .find(|l| !l.is_empty())
        .unwrap_or("")
        .to_string()
}

fn op_smt(op: Op) -> &'static str {
    match op {
        Op::Le => "<=",
        Op::Lt => "<",
        Op::Eq => "=",
        Op::Ge => ">=",
        Op::Gt => ">",
    }
}

/// SMT-LIB term for an atom `x − y ⋈ c` (or `x ⋈ c` for var-const).
fn atom_smt_int(a: &DiffAtom<i64>) -> String {
    let lhs = match a.rhs {
        Some(y) => format!("(- v{} v{})", a.lhs, y),
        None => format!("v{}", a.lhs),
    };
    format!("(assert ({} {} {}))", op_smt(a.op), lhs, smt_int(a.c))
}

fn atom_smt_rat(a: &DiffAtom<BigRational>) -> String {
    let lhs = match a.rhs {
        Some(y) => format!("(- v{} v{})", a.lhs, y),
        None => format!("v{}", a.lhs),
    };
    format!("(assert ({} {} {}))", op_smt(a.op), lhs, smt_rat(&a.c))
}

/// SMT-LIB integer literal (negatives wrapped in `(- n)`).
fn smt_int(n: i64) -> String {
    if n < 0 {
        format!("(- {})", -n)
    } else {
        n.to_string()
    }
}

/// SMT-LIB real literal for a rational.
fn smt_rat(r: &BigRational) -> String {
    let num = r.numer();
    let den = r.denom();
    let abs = |b: &num_bigint::BigInt| {
        if b.is_negative() {
            format!("(- {})", (-b))
        } else {
            format!("{b}.0")
        }
    };
    if *den == num_bigint::BigInt::from(1) {
        abs(num)
    } else {
        // (/ num den) with .0 reals
        let n = abs(num);
        let d = format!("{den}.0");
        format!("(/ {n} {d})")
    }
}

fn header(vars: usize, logic: &str, sort: &str) -> String {
    let mut s = format!("(set-logic {logic})\n");
    for v in 0..vars {
        s.push_str(&format!("(declare-fun v{v} () {sort})\n"));
    }
    s
}

#[test]
fn z3_oracle_idl() {
    let Some(z3) = z3_path() else {
        eprintln!("SKIP z3_oracle_idl: z3 not found on PATH");
        return;
    };
    let mut rng = ChaCha8Rng::seed_from_u64(0xD1FF_10C0_1D10_0001);
    let ops = [Op::Le, Op::Lt, Op::Eq, Op::Ge, Op::Gt];

    let mut sat_validated = 0usize;
    let mut unsat_count = 0usize;
    for inst in 0..NUM_INSTANCES {
        let n_atoms = rng.gen_range(1..=12);
        let mut atoms: Vec<DiffAtom<i64>> = Vec::with_capacity(n_atoms);
        for _ in 0..n_atoms {
            let x = rng.gen_range(0..N_VARS);
            let y = rng.gen_range(0..N_VARS);
            let op = ops[rng.gen_range(0..ops.len())];
            let c = rng.gen_range(-15i64..=15);
            if rng.gen_bool(0.2) {
                atoms.push(DiffAtom::var_const(x, op, c));
            } else {
                atoms.push(DiffAtom::diff(x, y, op, c));
            }
        }

        let ours = solve_int_atoms(&atoms);
        // We only generate pure DL atoms, so rejection must never happen.
        assert!(
            !matches!(ours, BuildResult::Rejected),
            "engine rejected a pure-DL IDL instance #{inst}: {atoms:?}"
        );

        // Build base script.
        let mut base = header(N_VARS, "QF_IDL", "Int");
        for a in &atoms {
            base.push_str(&atom_smt_int(a));
            base.push('\n');
        }
        let z3_verdict = run_z3(&z3, &format!("{base}(check-sat)\n"));

        let our_label = match &ours {
            BuildResult::Sat { .. } => "sat",
            BuildResult::Unsat { .. } => "unsat",
            BuildResult::Rejected => unreachable!(),
        };
        assert_eq!(
            our_label, z3_verdict,
            "IDL DISAGREEMENT #{inst}: ours={our_label} z3={z3_verdict} atoms={atoms:?}"
        );

        match &ours {
            BuildResult::Sat { model } => {
                // Validate the model: append equalities and re-run z3.
                let mut val = base.clone();
                for (v, m) in model.iter().enumerate() {
                    val.push_str(&format!("(assert (= v{v} {}))\n", smt_int(*m)));
                }
                val.push_str("(check-sat)\n");
                let mv = run_z3(&z3, &val);
                assert_eq!(
                    mv, "sat",
                    "IDL MODEL REJECTED by z3 #{inst}: model={model:?} atoms={atoms:?}"
                );
                sat_validated += 1;
            }
            BuildResult::Unsat { .. } => unsat_count += 1,
            BuildResult::Rejected => unreachable!(),
        }
    }
    eprintln!(
        "z3_oracle_idl: {NUM_INSTANCES} instances cross-checked, {sat_validated} SAT models \
         validated, {unsat_count} UNSAT agreed; 0 disagreements"
    );
}

#[test]
fn z3_oracle_rdl() {
    let Some(z3) = z3_path() else {
        eprintln!("SKIP z3_oracle_rdl: z3 not found on PATH");
        return;
    };
    let mut rng = ChaCha8Rng::seed_from_u64(0x5D10_AC1E_9900_0002);
    let ops = [Op::Le, Op::Lt, Op::Eq, Op::Ge, Op::Gt];

    let mut sat_validated = 0usize;
    let mut unsat_count = 0usize;
    for inst in 0..NUM_INSTANCES {
        let n_atoms = rng.gen_range(1..=12);
        let mut atoms: Vec<DiffAtom<BigRational>> = Vec::with_capacity(n_atoms);
        for _ in 0..n_atoms {
            let x = rng.gen_range(0..N_VARS);
            let y = rng.gen_range(0..N_VARS);
            let op = ops[rng.gen_range(0..ops.len())];
            let num = rng.gen_range(-15i64..=15);
            let den = rng.gen_range(1i64..=6);
            let c = BigRational::new(num.into(), den.into());
            if rng.gen_bool(0.2) {
                atoms.push(DiffAtom::var_const(x, op, c));
            } else {
                atoms.push(DiffAtom::diff(x, y, op, c));
            }
        }

        let ours = solve_rational_atoms(&atoms);
        assert!(
            !matches!(ours, BuildResult::Rejected),
            "engine rejected a pure-DL RDL instance #{inst}: {atoms:?}"
        );

        let mut base = header(N_VARS, "QF_RDL", "Real");
        for a in &atoms {
            base.push_str(&atom_smt_rat(a));
            base.push('\n');
        }
        let z3_verdict = run_z3(&z3, &format!("{base}(check-sat)\n"));

        let our_label = match &ours {
            BuildResult::Sat { .. } => "sat",
            BuildResult::Unsat { .. } => "unsat",
            BuildResult::Rejected => unreachable!(),
        };
        assert_eq!(
            our_label, z3_verdict,
            "RDL DISAGREEMENT #{inst}: ours={our_label} z3={z3_verdict} atoms={atoms:?}"
        );

        match &ours {
            BuildResult::Sat { model } => {
                let mut val = base.clone();
                for (v, m) in model.iter().enumerate() {
                    val.push_str(&format!("(assert (= v{v} {}))\n", smt_rat(m)));
                }
                val.push_str("(check-sat)\n");
                let mv = run_z3(&z3, &val);
                assert_eq!(
                    mv, "sat",
                    "RDL MODEL REJECTED by z3 #{inst}: model={model:?} atoms={atoms:?}"
                );
                sat_validated += 1;
            }
            BuildResult::Unsat { .. } => unsat_count += 1,
            BuildResult::Rejected => unreachable!(),
        }
    }
    eprintln!(
        "z3_oracle_rdl: {NUM_INSTANCES} instances cross-checked, {sat_validated} SAT models \
         validated, {unsat_count} UNSAT agreed; 0 disagreements"
    );
}
