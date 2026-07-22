// PASS (non-vacuity control): READING the SharedBounds bus is the
// unprivileged surface — any code holding a bus reference may poll `ub`/`lb`
// (the prune-only consumption `native_oll` performs). This must keep
// compiling so the compile-fail case beside it fails for the right reason.

fn read_only(bus: &ay_pb::portfolio::SharedBounds) -> (Option<i128>, Option<i128>) {
    (bus.ub(), bus.lb())
}

fn main() {
    let _ = read_only;
}
