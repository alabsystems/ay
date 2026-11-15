// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Wrong-UNSAT regression, the rest of the 23 known witnesses: 19 satisfiable
//! problems main `f399eca07a` answered `unsat` in BOTH postures (z3 5.1.0
//! `sat` on every one; each file's header carries z3's model and the door the
//! verdict went through). `nia_sign_cut_wrong_unsat.rs` holds the other four.
//!
//! - `sat_nia_sign_cut_gen2_h*` (14, QF_NIA): the sign-cut attack's gen2
//!   generator. The NIA refinement loop's tentative sign cut or rounding pin —
//!   a bound whose reason is the variable term — was read as a fact by a LIA
//!   side check (`check_modular_for_var`, the direct-enumeration box, the
//!   Diophantine fixed-variable fold), which returned the whole asserted set.
//!   Fixed by justified-bound reads (`ay-lia/src/justified_bounds.rs`).
//! - `sat_ufnia_shared_eq_*` (5, QF_UFNIA): a second mechanism at the same
//!   NIA sites. The inner LIA held the EUF shared equality `f(a) = f(b)`
//!   (reason `(= a b)`) as a row, the refutation used it, and the check loop
//!   returned the asserted atoms alone — a z3-satisfiable set, an empty
//!   learned clause. Fixed by `full_conflict_lits`
//!   (`ay-nia/src/full_conflict.rs`), whose theory-level pin re-checks the
//!   returned conflict standalone (`ay-nia/src/shared_reason_tests.rs`).
//! - `sat_nia_factor_split_premise_*` (4, QF_NIA, found 2026-09-23 while
//!   landing the two above): a third mechanism. The factor split's aggregated
//!   conflict (the union of the branch conflicts plus the cover) omitted the
//!   asserted equality each branch had derived a pin from; the default
//!   posture of main `866731b184` answered `unsat` (`--z3-mode` `sat`). Fixed
//!   by `split_conflict` (`ay-nia/src/factor_split.rs`), pinned at theory
//!   level by `ay-nia/src/factor_split_premise_tests.rs`.
//!
//! The files live in `benchmarks/smt/wrong-verdict/` (in the repo, not the
//! gitignored corpus) and are also rows of `scripts/z3_parity_reproducers.sh`.
//! `unknown` would be a completeness loss, reported but not wrong; `unsat` is
//! the regression.

use std::time::Duration;

use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;

fn solve(input: &str, shed_proof_cycle: bool) -> String {
    let commands = parse(input).unwrap_or_else(|err| panic!("parse failed: {err}"));
    let mut exec = Executor::new();
    // `--z3-mode` / `--no-proof` posture when set; the batteries-on default
    // otherwise. The wrong verdicts fired in both.
    exec.set_competition_mode(shed_proof_cycle);
    exec.set_timeout(Some(Duration::from_secs(30)));
    exec.set_memory_limit(Some(8 << 30));
    let outputs = exec
        .execute_all(&commands)
        .unwrap_or_else(|err| panic!("execution failed: {err}"));
    outputs.last().cloned().unwrap_or_default()
}

fn assert_never_unsat(name: &str, input: &str) {
    for shed in [false, true] {
        let verdict = solve(input, shed);
        assert_ne!(
            verdict, "unsat",
            "{name} (shed_proof_cycle={shed}) declares :status sat and z3 5.1.0 answers sat"
        );
    }
}

macro_rules! never_unsat {
    ($test:ident, $file:literal) => {
        #[test]
        #[timeout(180_000)]
        fn $test() {
            assert_never_unsat(
                $file,
                include_str!(concat!(
                    "../../../../benchmarks/smt/wrong-verdict/",
                    $file,
                    ".smt2"
                )),
            );
        }
    };
}

never_unsat!(gen2_h0129_is_never_unsat, "sat_nia_sign_cut_gen2_h0129");
never_unsat!(gen2_h0139_is_never_unsat, "sat_nia_sign_cut_gen2_h0139");
never_unsat!(gen2_h0231_is_never_unsat, "sat_nia_sign_cut_gen2_h0231");
never_unsat!(gen2_h0447_is_never_unsat, "sat_nia_sign_cut_gen2_h0447");
never_unsat!(gen2_h0536_is_never_unsat, "sat_nia_sign_cut_gen2_h0536");
never_unsat!(gen2_h0685_is_never_unsat, "sat_nia_sign_cut_gen2_h0685");
never_unsat!(gen2_h0731_is_never_unsat, "sat_nia_sign_cut_gen2_h0731");
never_unsat!(gen2_h0778_is_never_unsat, "sat_nia_sign_cut_gen2_h0778");
never_unsat!(gen2_h0852_is_never_unsat, "sat_nia_sign_cut_gen2_h0852");
never_unsat!(gen2_h0986_is_never_unsat, "sat_nia_sign_cut_gen2_h0986");
never_unsat!(gen2_h1052_is_never_unsat, "sat_nia_sign_cut_gen2_h1052");
never_unsat!(gen2_h1302_is_never_unsat, "sat_nia_sign_cut_gen2_h1302");
never_unsat!(gen2_h1402_is_never_unsat, "sat_nia_sign_cut_gen2_h1402");
never_unsat!(gen2_h1466_is_never_unsat, "sat_nia_sign_cut_gen2_h1466");
never_unsat!(
    shared_eq_euf_div_010_is_never_unsat,
    "sat_ufnia_shared_eq_euf_div_010"
);
never_unsat!(
    shared_eq_euf_div_020_is_never_unsat,
    "sat_ufnia_shared_eq_euf_div_020"
);
never_unsat!(
    shared_eq_euf_div_022_is_never_unsat,
    "sat_ufnia_shared_eq_euf_div_022"
);
never_unsat!(
    shared_eq_euf_div_026_is_never_unsat,
    "sat_ufnia_shared_eq_euf_div_026"
);
never_unsat!(shared_eq_min_is_never_unsat, "sat_ufnia_shared_eq_min");
// The third mechanism (#nia-factor-split-premises): the factor split's
// aggregated conflict omitted the asserted equality a branch derived a pin
// from. Answered `unsat` by the default posture of main 866731b184.
never_unsat!(
    factor_split_premise_0005_is_never_unsat,
    "sat_nia_factor_split_premise_0005"
);
never_unsat!(
    factor_split_premise_0028_is_never_unsat,
    "sat_nia_factor_split_premise_0028"
);
never_unsat!(
    factor_split_premise_0250_is_never_unsat,
    "sat_nia_factor_split_premise_0250"
);
never_unsat!(
    factor_split_premise_0265_is_never_unsat,
    "sat_nia_factor_split_premise_0265"
);
