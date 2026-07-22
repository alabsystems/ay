// PASS (non-vacuity control): a legitimate PRIMAL optimization worker run —
// the shape `spawn_primal_optimization_worker` accepts — streams improvements
// through the verdict-free `PrimalSender` and returns `()`. This must keep
// compiling so the compile-fail cases beside it fail for the right reason.

fn main() {
    let _run: ay_pb::portfolio::PrimalWorkerRun = Box::new(
        |_instance, _objective, _timeout_dur, _start, _term_flag, sender| {
            sender.send_improvement(0, vec![true, false]);
        },
    );
}
