// Pins the fix for the 2026-07-18 consumer stack-overflow regression: Solver
// embedded a ~56 KiB Executor by value, so every consumer struct holding a
// Solver by value inherited a ~56 KiB stack slot per move in unoptimized
// builds; consumer call chains accumulated megabytes of stack and overflowed
// default 2 MiB threads. Solver must stay pointer-sized-ish (Executor boxed).
// If this fires, something re-inlined a large field into Solver.

use std::mem::size_of;

#[test]
fn solver_stays_small_executor_boxed() {
    let size = size_of::<ay_dpll::api::Solver>();
    assert!(
        size <= 4096,
        "Solver is {size} bytes; it must stay small (Executor boxed) so \
         by-value consumers do not accumulate huge stack frames"
    );
}
