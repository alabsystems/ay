// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic, clippy::uninlined_format_args, clippy::manual_assert)]

use std::path::PathBuf;

use ay_chc::testing::{self, pdr_solve_from_file, pdr_solve_from_str};
use ay_chc::{CancellationToken, PdrConfig, PdrResult};
use ntest::timeout;

fn example_path(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("examples")
        .join(name)
}

// Embedded benchmark for #1348 regression test (hermetic; does not rely on local benchmark checkout).
#[cfg(not(debug_assertions))]
const THREE_DOTS_MOVING_2_000_SMT2: &str = r#"(set-logic HORN)


(declare-fun |inv| ( Int Int Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) )
    (=>
      (and
        (and (>= D (+ B (* (- 1) C)))
     (>= D (+ B (* (- 1) A)))
     (not (<= B A))
     (>= D (+ C (* (- 2) A) B)))
      )
      (inv A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) )
    (=>
      (and
        (inv B C F A)
        (let ((a!1 (and (= D (ite (<= B F) (+ 1 B) (+ (- 1) B))) (= E D) (= B C))))
(let ((a!2 (or (and (= D B) (= E (+ (- 1) C)) (not (= B C))) a!1)))
  (and (= G (+ (- 1) A)) a!2 (not (= C F)))))
      )
      (inv D E F G)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) )
    (=>
      (and
        (inv A B C D)
        (and (<= D 0) (not (= B C)))
      )
      false
    )
  )
)

(check-sat)
(exit)
"#;

/// Default config for tests - matches PdrConfig::default() with optional verbose override
fn test_config(verbose: bool) -> PdrConfig {
    let mut config = PdrConfig::default();
    config.verbose = verbose;
    config
}

#[path = "../pdr_examples/basic_and_hyperedge.rs"]
mod basic_and_hyperedge;
#[path = "../pdr_examples/counterexample.rs"]
mod counterexample;
#[path = "../pdr_examples/embedded_benchmarks.rs"]
mod embedded_benchmarks;
#[path = "../pdr_examples/prover_and_regression.rs"]
mod prover_and_regression;
