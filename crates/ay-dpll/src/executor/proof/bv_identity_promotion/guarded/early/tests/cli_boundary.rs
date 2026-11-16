// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn authored_queries_with_memory_limits_publish_complete_proofs() {
    for (name, source) in [
        ("cell32", CELL32),
        ("cell64", CELL64),
        (
            "consumer-memory",
            include_str!("consumer-frame-positive-memory.smt2"),
        ),
        (
            "consumer-whole",
            include_str!("consumer-frame-positive-whole.smt2"),
        ),
    ] {
        let mut executor = Executor::new();
        executor.set_produce_proofs(true);
        executor.set_memory_limit(Some(8 * 1024 * 1024 * 1024));
        for command in ay_frontend::parse(source).unwrap() {
            if matches!(command, Command::Exit) {
                continue;
            }
            let output = executor.execute_authored(&command).unwrap();
            if matches!(command, Command::CheckSat) {
                assert_eq!(output.as_deref(), Some("unsat"), "{name}");
            }
        }
        let proof = executor.last_proof().expect("public proof retained");
        executor.check_proof_strict_with_datatypes(proof).unwrap();
        let text = executor
            .execute_authored(&Command::GetProof)
            .unwrap()
            .unwrap();
        assert!(!text.starts_with("(error"), "{name}: {text}");
        assert!(text.contains(":rule resolution"), "{name}");
        assert!(
            !text.contains(":rule hole") && !text.contains(":rule trust"),
            "{name}"
        );
        let path = std::env::temp_dir().join(format!(
            "ay-memory-cli-boundary-{name}-{}.json",
            std::process::id()
        ));
        std::fs::write(
            &path,
            serde_json::to_vec(&serde_json::json!({
                "type":"alethe_certificate", "version":"1.0", "problem":source, "proof":text
            }))
            .unwrap(),
        )
        .unwrap();
        println!("independent replay certificate: {}", path.display());
    }
}

#[test]
fn authored_memory_queries_honor_entry_stops() {
    for control in 0..3 {
        let mut executor = loaded(CELL32);
        match control {
            0 => executor.set_interrupt(Arc::new(AtomicBool::new(true))),
            1 => executor.set_deadline(Some(
                Instant::now()
                    .checked_sub(Duration::from_secs(1))
                    .expect("the monotonic clock can represent one second ago"),
            )),
            _ => executor.set_memory_limit(Some(1)),
        }
        assert_eq!(
            executor
                .execute_authored(&Command::CheckSat)
                .unwrap()
                .as_deref(),
            Some("unknown")
        );
        assert!(executor.last_proof().is_none());
        assert!(executor.last_unsat_certificate.is_none());
        assert_eq!(
            executor.last_proof_raw_original_assertions,
            [] as [TermId; 0]
        );
    }
}
