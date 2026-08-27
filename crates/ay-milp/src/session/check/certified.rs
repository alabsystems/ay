// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model-bound proof routes, ordered ahead of replay-only reductions.

use super::*;

mod network;
mod pb;

pub(super) fn run(session: &mut BabSession, state: &mut CheckState) -> RouteOutcome {
    let network = network::run(session, state);
    if matches!(network, RouteOutcome::Finished(_)) {
        return network;
    }
    pb::run(session, state)
}

/// Give a typed block proof the opportunity that a pending network handoff
/// deliberately postponed. The handoff must already have been consumed, so
/// the ordinary pre-replay guard remains the single ordering authority.
pub(super) fn run_block_angular_after_network_handoff(
    session: &mut BabSession,
    state: &CheckState,
) -> RouteOutcome {
    network::try_block_angular(session, state)
}
