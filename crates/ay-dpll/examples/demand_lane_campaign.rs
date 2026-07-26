// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Extended production-demand campaign for the full takesome bridge query.
//!
//! The default unit tests exercise bounded reductions of the frontier and
//! accounting invariants.  This executable retains the slower full query as
//! explicit tooling:
//!
//! ```text
//! cargo run -p ay-dpll --release --example demand_lane_campaign -- 120
//! ```
//!
//! The optional positional argument is the solver timeout in seconds.

use std::time::Duration;

use ay_dpll::Executor;
use ay_frontend::parse;

const FREEVAR_TAKESOME_REPRO: &str = r#"
(set-logic ALL)
(declare-datatypes ((Lst 0)) (((Nil) (Cons (hd Int) (tl Lst)))))
(declare-fun sum (Lst) Int)
(declare-fun payload_hd (Lst) Int)
(declare-fun payload_get (Lst) Lst)
(assert (forall ((l Lst)) (! (=> ((_ is Cons) l) (= (payload_get l) (tl l))) :pattern ((payload_get l)))))
(assert (forall ((l Lst)) (! (=> ((_ is Cons) l) (= (payload_hd l) (hd l))) :pattern ((payload_hd l)))))
(assert (forall ((l Lst)) (! (= (sum l) (ite ((_ is Cons) l) (+ (hd l) (sum (tl l))) 0)) :pattern ((sum l)))))
(assert (forall ((l Lst)) (! (>= (sum l) 0) :pattern ((sum l)))))
(declare-const self Lst)
(declare-const final Lst)
(declare-const k Int)
(assert ((_ is Cons) self))
(assert ((_ is Cons) final))
(assert (>= k 0))
(assert (= (payload_hd final) (+ (payload_hd self) k)))
(assert (= (payload_get final) (payload_get self)))
(assert (not (= (- (sum final) (sum self)) k)))
(check-sat)
"#;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let timeout_seconds = match std::env::args().nth(1) {
        Some(raw) => raw
            .parse::<u64>()
            .map_err(|_| format!("invalid timeout `{raw}`; expected positive seconds"))?,
        None => 120,
    };
    if timeout_seconds == 0 {
        return Err("timeout must be positive".into());
    }

    let commands = parse(FREEVAR_TAKESOME_REPRO)?;
    let mut executor = Executor::new();
    executor.set_timeout(Some(Duration::from_secs(timeout_seconds)));
    let outputs = executor.execute_all(&commands)?;
    let verdict = outputs
        .iter()
        .rev()
        .find(|output| matches!(output.as_str(), "sat" | "unsat" | "unknown"))
        .ok_or("campaign produced no solver verdict")?;
    println!("{verdict}");
    if verdict != "unsat" {
        return Err(
            format!("expected production demand lane to prove unsat, got {verdict}").into(),
        );
    }
    Ok(())
}
