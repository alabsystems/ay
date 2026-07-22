// COMPILE-FAIL: a primal run's ONLY channel surface is
// `PrimalSender::send_improvement`. There is no verdict-carrying method on the
// sender, and the coordinator's `WorkerMsg` (whose `Done` variant carries
// `OptimumFound`/`Unsatisfiable`) is private — it cannot even be named from a
// primal worker, let alone constructed or sent (design §3.2).

use ay_pb::portfolio::WorkerMsg;

fn main() {
    let _run: ay_pb::portfolio::PrimalWorkerRun = Box::new(
        |_instance, _objective, _timeout_dur, _start, _term_flag, sender| {
            sender.send_done(WorkerMsg::Finished { label: "rogue" });
        },
    );
}
