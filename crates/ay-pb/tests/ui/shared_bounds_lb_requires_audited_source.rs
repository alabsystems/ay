// COMPILE-FAIL: `publish_lb` is TYPED-BY-SOURCE (design §2.7): it accepts
// only a `GlobalSoundFloor`, whose field is private and whose constructors
// are all `pub(crate)` — one per AUDITED globally-sound floor derivation.
// Un-audited code cannot fabricate a floor by struct literal or by calling a
// constructor, so a heuristic / per-worker / non-global bound can never reach
// the bus lb (a fabricated floor could license a false OPTIMUM upgrade).

fn forge_by_literal(bus: &ay_pb::portfolio::SharedBounds) {
    bus.publish_lb(ay_pb::portfolio::GlobalSoundFloor { value: 0 });
}

fn forge_by_constructor(bus: &ay_pb::portfolio::SharedBounds) {
    bus.publish_lb(ay_pb::portfolio::GlobalSoundFloor::from_structural_constraint_floor(0));
}

fn main() {
    let _ = forge_by_literal;
    let _ = forge_by_constructor;
}
