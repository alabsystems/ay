// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_panic_message_extracts_str() {
    let payload: Box<dyn std::any::Any + Send> = Box::new("test panic");
    assert_eq!(panic_message(&*payload), "test panic");
}

#[test]
fn test_panic_message_extracts_string() {
    let payload: Box<dyn std::any::Any + Send> = Box::new("owned panic".to_string());
    assert_eq!(panic_message(&*payload), "owned panic");
}

#[test]
fn test_panic_message_unknown_type() {
    let payload: Box<dyn std::any::Any + Send> = Box::new(42u32);
    assert_eq!(panic_message(&*payload), "unknown panic");
}

struct ForcedSpawnFailureGuard;

impl ForcedSpawnFailureGuard {
    fn enable() -> Self {
        FORCE_SOLVER_THREAD_SPAWN_FAILURE.with(|value| value.set(true));
        Self
    }
}

impl Drop for ForcedSpawnFailureGuard {
    fn drop(&mut self) {
        FORCE_SOLVER_THREAD_SPAWN_FAILURE.with(|value| value.set(false));
    }
}

#[test]
#[serial(portfolio_spawn_failure)]
fn test_spawn_failure_hook_is_thread_local() {
    let _spawn_failure_guard = ForcedSpawnFailureGuard::enable();
    assert!(
        PortfolioSolver::spawn_solver_thread(|| ()).is_err(),
        "current thread should observe forced spawn failure",
    );

    let child = thread::spawn(|| {
        let handle = PortfolioSolver::spawn_solver_thread(|| 7u8)
            .expect("spawn hook must not leak into other threads");
        handle
            .join()
            .expect("child worker thread should complete successfully")
    });
    assert_eq!(
        child
            .join()
            .expect("child test thread should complete successfully"),
        7u8
    );
}

#[test]
#[serial(portfolio_spawn_failure)]
fn test_parallel_portfolio_spawn_failure_returns_unknown() {
    let _spawn_failure_guard = ForcedSpawnFailureGuard::enable();
    let problem = create_safe_problem();
    let config = PortfolioConfig {
        external_cancellation: None,
        engines: vec![
            EngineConfig::Pdr(PdrConfig::default()),
            EngineConfig::Bmc(BmcConfig::default()),
        ],
        parallel: true,
        timeout: None,
        parallel_timeout: None,
        verbose: false,

        enable_preprocessing: false,
        engine_budgets: ay_core::kani_compat::DetHashMap::default(),
        memory_budget: None,
        strict_proofs: false,
    };
    let solver = PortfolioSolver::new(problem, config);
    let result = solver.solve();
    assert!(
        matches!(result, PortfolioResult::Unknown),
        "spawn failure should degrade to Unknown, got: {result:?}"
    );
}

#[test]
#[serial(portfolio_spawn_failure)]
fn test_sequential_portfolio_timeout_spawn_failure_returns_unknown() {
    let _spawn_failure_guard = ForcedSpawnFailureGuard::enable();
    let problem = create_safe_problem();
    let config = PortfolioConfig {
        external_cancellation: None,
        engines: vec![EngineConfig::Pdr(PdrConfig::default())],
        parallel: false,
        timeout: Some(Duration::from_millis(50)),
        parallel_timeout: None,
        verbose: false,

        enable_preprocessing: false,
        engine_budgets: ay_core::kani_compat::DetHashMap::default(),
        memory_budget: None,
        strict_proofs: false,
    };
    let solver = PortfolioSolver::new(problem, config);
    let result = solver.solve();
    assert!(
        matches!(result, PortfolioResult::Unknown),
        "timeout-path spawn failure should degrade to Unknown, got: {result:?}"
    );
}

#[test]
fn test_parallel_portfolio_survives_panicking_engine() {
    // Verify that catch_unwind prevents panics from crashing the process (#2723).
    // We use a thread that explicitly panics and send the result through a channel,
    // simulating the portfolio's parallel mode.
    let (tx, rx) = mpsc::channel::<(usize, EngineResult)>();

    // Simulate a BMC engine panicking — should produce Unified(Unknown, "BMC") (#2728)
    let panic_result = EngineConfig::Bmc(BmcConfig::default()).unknown_result();
    let handle = thread::spawn(move || {
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| -> EngineResult {
            panic!("deliberate engine panic for test");
        }));
        let result = match result {
            Ok(r) => r,
            Err(payload) => {
                let _msg = panic_message(&*payload);
                panic_result
            }
        };
        let _ = tx.send((0, result));
    });

    let (idx, engine_result) = rx.recv().expect("should receive result despite panic");
    assert_eq!(idx, 0);
    // Verify correct variant: BMC panic produces Unified(Unknown, "BMC") (#2728)
    assert!(matches!(
        engine_result,
        EngineResult::Unified(ChcEngineResult::Unknown, "BMC")
    ));
    handle.join().expect("thread should not propagate panic");
}

#[test]
fn test_unknown_result_returns_correct_variant() {
    // Verify EngineConfig::unknown_result() maps each config to the correct variant (#2728).
    // Most engines use Unified variant; TPA and CEGAR use dedicated variants.
    assert!(matches!(
        EngineConfig::Pdr(PdrConfig::default()).unknown_result(),
        EngineResult::Unified(ChcEngineResult::Unknown, "PDR")
    ));
    assert!(matches!(
        EngineConfig::Bmc(BmcConfig::default()).unknown_result(),
        EngineResult::Unified(ChcEngineResult::Unknown, "BMC")
    ));
    assert!(matches!(
        EngineConfig::pdkind_default().unknown_result(),
        EngineResult::Unified(ChcEngineResult::Unknown, "PDKIND")
    ));
    assert!(matches!(
        EngineConfig::Imc(ImcConfig::default()).unknown_result(),
        EngineResult::Unified(ChcEngineResult::Unknown, "IMC")
    ));
    assert!(matches!(
        EngineConfig::Lawi(LawiConfig::default()).unknown_result(),
        EngineResult::Unified(ChcEngineResult::Unknown, "LAWI")
    ));
    assert!(matches!(
        EngineConfig::Tpa(TpaConfig::default()).unknown_result(),
        EngineResult::Tpa(TpaResult::Unknown)
    ));
    assert!(matches!(
        EngineConfig::Trl(TrlConfig::default()).unknown_result(),
        EngineResult::Unified(ChcEngineResult::Unknown, "TRL")
    ));
    assert!(matches!(
        EngineConfig::Kind(KindConfig::default()).unknown_result(),
        EngineResult::Unified(ChcEngineResult::Unknown, "Kind")
    ));
    assert!(matches!(
        EngineConfig::Decomposition(DecompositionConfig::default()).unknown_result(),
        EngineResult::Unified(ChcEngineResult::Unknown, "Decomposition")
    ));
    assert!(matches!(
        EngineConfig::Cegar(CegarConfig::default()).unknown_result(),
        EngineResult::Cegar(CegarResult::Unknown)
    ));
}

#[test]
fn test_panicking_engine_does_not_suppress_working_engine_result() {
    // Verify that when one engine panics, the portfolio still returns the
    // working engine's result (#2728). Simulates parallel portfolio behavior:
    // engine 0 panics (BMC), engine 1 returns Safe (PDR).
    let (tx, rx) = mpsc::channel::<(usize, EngineResult)>();

    // Engine 0: panics
    let tx0 = tx.clone();
    let panic_result = EngineConfig::Bmc(BmcConfig::default()).unknown_result();
    let h0 = thread::spawn(move || {
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| -> EngineResult {
            panic!("deliberate BMC engine panic");
        }));
        let result = match result {
            Ok(r) => r,
            Err(payload) => {
                let _msg = panic_message(&*payload);
                panic_result
            }
        };
        let _ = tx0.send((0, result));
    });

    // Engine 1: returns Safe with a trivial model
    let tx1 = tx.clone();
    let h1 = thread::spawn(move || {
        let model = InvariantModel::new();
        let _ = tx1.send((
            1,
            EngineResult::Unified(ChcEngineResult::Safe(model), "PDR"),
        ));
    });
    drop(tx);

    // Collect results — mirroring portfolio's result collection loop
    let mut got_safe = false;
    let mut got_unknown = false;
    for (idx, result) in rx.iter() {
        match &result {
            EngineResult::Unified(ChcEngineResult::Unknown, "BMC") => {
                assert_eq!(idx, 0, "panic result should be engine 0");
                got_unknown = true;
            }
            EngineResult::Unified(ChcEngineResult::Safe(_), "PDR") => {
                assert_eq!(idx, 1, "safe result should be engine 1");
                got_safe = true;
            }
            _ => panic!("unexpected result variant from engine {idx}"),
        }
    }

    assert!(
        got_unknown,
        "should have received Unknown from panicked engine"
    );
    assert!(got_safe, "should have received Safe from working engine");
    h0.join().expect("panicking thread should not propagate");
    h1.join().expect("working thread should complete");
}

/// RAII guard that forces `global_memory_exceeded()` to return true.
/// Resets both the term-byte counter and process memory limit on drop.
struct GlobalTermBytesGuard;

impl GlobalTermBytesGuard {
    fn force_exceeded() -> Self {
        // DEFAULT_TERM_MEMORY_LIMIT is usize::MAX (unlimited), so the
        // term-byte comparison alone cannot trigger the check. Instead,
        // force the process-level RSS limit to 1 byte so that
        // process_memory_exceeded() fires (#2771).
        ay_core::TermStore::force_process_memory_exceeded_for_testing();
        Self
    }
}

impl Drop for GlobalTermBytesGuard {
    fn drop(&mut self) {
        ay_core::TermStore::reset_global_term_bytes();
        ay_core::TermStore::reset_process_memory_limit_for_testing();
    }
}

#[test]
#[serial(global_term_memory)]
fn test_sequential_portfolio_skips_engines_when_global_memory_exceeded() {
    // Force global memory counter past the threshold so the sequential loop
    // skips all engines and returns Unknown without launching any solver.
    let _guard = GlobalTermBytesGuard::force_exceeded();

    let problem = create_safe_problem();
    let config = PortfolioConfig {
        external_cancellation: None,
        engines: vec![EngineConfig::Bmc(BmcConfig::with_engine_config(
            100, false, None,
        ))],
        parallel: false,
        timeout: Some(Duration::from_secs(5)),
        parallel_timeout: None,
        verbose: false,

        enable_preprocessing: false,
        engine_budgets: ay_core::kani_compat::DetHashMap::default(),
        memory_budget: None,
        strict_proofs: false,
    };
    let solver = PortfolioSolver::new(problem, config);
    let result = solver.solve();

    assert!(
        matches!(result, PortfolioResult::Unknown),
        "Expected Unknown when global memory is exceeded before engine launch, got: {result:?}"
    );
}
