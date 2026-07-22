// COMPILE-FAIL: the primal spawn path (`spawn_primal_optimization_worker`)
// only accepts a `PrimalWorkerRun`, which returns `()`. A run that tries to
// smuggle a verdict out of the worker by RETURNING a `PbSolution` (the payload
// the coordinator's `WorkerMsg::Done` carries) must not typecheck — a primal
// worker is verdict-incapable BY CONSTRUCTION (design §3.2).

fn main() {
    let _run: ay_pb::portfolio::PrimalWorkerRun = Box::new(
        |_instance, _objective, _timeout_dur, _start, _term_flag, _sender| -> ay_pb::PbSolution {
            unreachable!()
        },
    );
}
