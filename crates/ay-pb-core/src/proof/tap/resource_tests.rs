// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use std::sync::atomic::AtomicUsize;

fn fresh(name: &str) -> bool {
    if !ay_test_support::isolated_test::run_alone(module_path!(), name).expect("fresh process") {
        return false;
    }
    ay_sys::compute_budget::tighten(std::num::NonZeroUsize::MIN).expect("Q1 ceiling");
    true
}

#[derive(Default)]
struct Observed {
    bytes: Mutex<Vec<u8>>,
    writes: AtomicUsize,
    outside: AtomicBool,
    dropped: AtomicBool,
}

struct Sink {
    observed: Arc<Observed>,
    fail: Arc<AtomicBool>,
    gate: Option<(Sender<()>, Receiver<()>)>,
    armed: Arc<AtomicBool>,
}

impl Sink {
    fn observe(&self) {
        if ay_sys::compute_budget::try_extra().is_err() {
            self.observed.outside.store(true, Ordering::Release);
        }
    }
}
impl Write for Sink {
    fn write(&mut self, bytes: &[u8]) -> std::io::Result<usize> {
        self.observe();
        self.observed.writes.fetch_add(1, Ordering::AcqRel);
        if self.fail.load(Ordering::Acquire) {
            return Err(std::io::Error::other("original sink failure"));
        }
        if self.armed.load(Ordering::Acquire) {
            if let Some((started, release)) = self.gate.take() {
                started
                    .send(())
                    .expect("sink blocked under its actual unit");
                release.recv().expect("release original sink");
                // A generic Write may compute, not just block: it remains charged.
                let mut value = 0u64;
                for index in 0..1000 {
                    value = value.wrapping_add(index);
                }
                std::hint::black_box(value);
            }
        }
        self.observed
            .bytes
            .lock()
            .expect("bytes")
            .extend_from_slice(bytes);
        Ok(bytes.len())
    }
    fn flush(&mut self) -> std::io::Result<()> {
        self.observe();
        Ok(())
    }
}
impl Drop for Sink {
    fn drop(&mut self) {
        self.observe();
        self.observed.dropped.store(true, Ordering::Release);
    }
}

#[test]
fn q1_full_ring_and_drop_preserve_every_frame_and_writer_cleanup() {
    if !fresh("q1_full_ring_and_drop_preserve_every_frame_and_writer_cleanup") {
        return;
    }
    let _caller = caller_scope();
    let observed = Arc::new(Observed::default());
    let writer = VeriPbWriter::new(
        Sink {
            observed: Arc::clone(&observed),
            fail: Arc::new(AtomicBool::new(false)),
            gate: None,
            armed: Arc::new(AtomicBool::new(false)),
        },
        2,
    )
    .expect("header");
    let headers = observed.writes.load(Ordering::Acquire);
    let mut tap = ProofTap::spawn(writer, 3, 64);
    for _ in 0..100 {
        tap.begin_frame(ConstraintId::new(1).expect("id"))
            .expect("begin");
        tap.proven_resolve(ConstraintId::new(2).expect("id"), 2, 3, vec![])
            .expect("resolve");
        tap.final_frame(1, false, Vec::new(), 0)
            .expect("complete frame");
    }
    // Q1's caller retained its original scope. Only a full-ring passive wait
    // could have allowed this serializer to execute before caller Drop.
    assert!(observed.writes.load(Ordering::Acquire) > headers);
    drop(tap);
    let text = String::from_utf8(observed.bytes.lock().expect("bytes").clone()).expect("UTF8");
    assert_eq!(text.matches("pol 1 s 2 2 d 3 * + s s ;\n").count(), 100);
    assert!(!text.contains("conclusion"));
    assert!(observed.dropped.load(Ordering::Acquire));
    assert!(!observed.outside.load(Ordering::Acquire));
}

#[test]
fn q1_blocking_computational_writer_retains_actual_unit_until_real_exit() {
    if !fresh("q1_blocking_computational_writer_retains_actual_unit_until_real_exit") {
        return;
    }
    let _caller = caller_scope();
    let observed = Arc::new(Observed::default());
    let (started, started_rx) = std::sync::mpsc::channel();
    let (release, release_rx) = std::sync::mpsc::channel();
    let armed = Arc::new(AtomicBool::new(false));
    let sink = Sink {
        observed: Arc::clone(&observed),
        fail: Arc::new(AtomicBool::new(false)),
        gate: Some((started, release_rx)),
        armed: Arc::clone(&armed),
    };
    let writer = VeriPbWriter::new(sink, 2).expect("original header");
    let mut tap = ProofTap::spawn(writer, 3, 64);
    armed.store(true, Ordering::Release);
    let monitor = std::thread::spawn(move || {
        started_rx.recv().expect("actual writer entered");
        assert!(ay_sys::compute_budget::ComputeScope::try_enter()
            .expect("probe")
            .is_none());
        release.send(()).expect("release original writer");
    });
    let contradiction = tap.log_rup_text(">= 1 ;".to_owned()).expect("record");
    tap.conclude_unsat(contradiction)
        .expect("original drain/flush ACK");
    tap.finish().expect("writer retired");
    monitor.join().expect("owned monitor");
    assert!(observed.dropped.load(Ordering::Acquire));
    assert!(!observed.outside.load(Ordering::Acquire));
}

#[test]
fn q1_original_sink_failure_never_commits_a_conclusion() {
    if !fresh("q1_original_sink_failure_never_commits_a_conclusion") {
        return;
    }
    let _caller = caller_scope();
    let observed = Arc::new(Observed::default());
    let fail = Arc::new(AtomicBool::new(false));
    let writer = VeriPbWriter::new(
        Sink {
            observed: Arc::clone(&observed),
            fail: Arc::clone(&fail),
            gate: None,
            armed: Arc::new(AtomicBool::new(false)),
        },
        2,
    )
    .expect("header");
    let mut tap = ProofTap::spawn(writer, 3, 64);
    fail.store(true, Ordering::Release);
    let id = tap.log_rup_text(">= 1 ;".to_owned()).expect("enqueue");
    assert!(tap.conclude_unsat(id).is_err());
    assert!(tap.finish().is_err());
    assert!(
        !String::from_utf8(observed.bytes.lock().expect("bytes").clone())
            .expect("UTF8")
            .contains("conclusion")
    );
    assert!(observed.dropped.load(Ordering::Acquire));
    assert!(!observed.outside.load(Ordering::Acquire));
}

#[test]
fn q1_actual_solver_proof_is_checked_and_cancellation_never_concludes() {
    if !fresh("q1_actual_solver_proof_is_checked_and_cancellation_never_concludes") {
        return;
    }
    let _caller = caller_scope();
    let directory = tempfile::tempdir().expect("private proof directory");
    let input = directory.path().join("formula.opb");
    let proof = directory.path().join("proof.pbp");
    let formula = "* #variable= 1 #constraint= 2\n+1 x1 >= 1 ;\n-1 x1 >= 0 ;\n";
    std::fs::write(&input, formula).expect("formula");
    let instance = crate::parse_opb(formula).expect("instance");
    let mut solver = crate::PbCdclSolver::with_proof_tap_interruptible(
        &instance,
        std::fs::File::create(&proof).expect("proof"),
        || false,
    )
    .expect("original proof owner");
    assert!(matches!(
        solver.solve_interruptible(|| false),
        crate::PbCdclResult::Unsatisfiable
    ));
    solver.conclude_proof().expect("actual conclusion ACK");
    drop(solver);
    let report = ay_veripb::check(ay_veripb::args::Args {
        formula: input,
        derivation: proof,
        opb: true,
        force_checked_deletion: true,
        ..Default::default()
    })
    .expect("independent maintained proof checker");
    assert_eq!(report.outcome(), ay_veripb::RunOutcome::Verified);

    let observed = Arc::new(Observed::default());
    let mut cancelled = crate::PbCdclSolver::with_proof_tap_interruptible(
        &instance,
        Sink {
            observed: Arc::clone(&observed),
            fail: Arc::new(AtomicBool::new(false)),
            gate: None,
            armed: Arc::new(AtomicBool::new(false)),
        },
        || true,
    )
    .expect("cancelled original owner");
    assert!(matches!(
        cancelled.solve_interruptible(|| true),
        crate::PbCdclResult::Unknown
    ));
    let _ = cancelled.conclude_proof();
    drop(cancelled);
    assert!(
        !String::from_utf8(observed.bytes.lock().expect("bytes").clone())
            .expect("UTF8")
            .contains("conclusion")
    );
    assert!(observed.dropped.load(Ordering::Acquire));
    assert!(!observed.outside.load(Ordering::Acquire));
}
