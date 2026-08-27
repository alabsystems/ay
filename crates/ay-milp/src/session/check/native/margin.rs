// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Marked-margin dispatch before the final anchor.

use super::super::*;

pub(super) enum Dispatch<'a> {
    Finished(Outcome),
    Anchor(Option<crate::margin::MarginProofTarget<'a>>),
}

pub(super) fn prepare<'a>(
    session: &mut BabSession,
    state: &mut CheckState,
    mode: MarginMode<'a>,
    shared_binary_prefix: &[Col],
    target_fsb_prefix: Option<crate::bab::TargetFsbPrefixRequest<'_>>,
) -> Result<Dispatch<'a>, MilpError> {
    match mode {
        MarginMode::Auto => Ok(prepare_auto(session, state).unwrap_or(Dispatch::Anchor(None))),
        MarginMode::Disabled => Ok(Dispatch::Anchor(None)),
        MarginMode::Required => {
            prepare_required(session, state, shared_binary_prefix, target_fsb_prefix)
        }
        // Ownership moves intact from the caller into the anchor dispatch.
        MarginMode::ReframedProof(target) => Ok(Dispatch::Anchor(Some(target))),
    }
}

fn prepare_auto(session: &mut BabSession, state: &mut CheckState) -> Option<Dispatch<'static>> {
    let prepared = crate::margin::prepare_auto(&session.model)?;
    let reframed = session
        .run_reframed_nested(
            prepared,
            &[],
            None,
            MarginEvidenceBar::VerifiedTreeOrRootFarkas,
        )
        .ok()?;
    let solved = state.take_solved(session);
    Some(Dispatch::Finished(finish(
        reframed.verdict,
        &session.model,
        &solved,
        &session.opts,
    )))
}

fn prepare_required(
    session: &mut BabSession,
    state: &mut CheckState,
    shared_binary_prefix: &[Col],
    target_fsb_prefix: Option<crate::bab::TargetFsbPrefixRequest<'_>>,
) -> Result<Dispatch<'static>, MilpError> {
    let prepared = crate::margin::prepare(&session.model).ok_or_else(|| MilpError::Session {
        message: "marked-margin shared prefix requires an enabled, objective-zero, \
                  nonempty one-sided margin row"
            .to_owned(),
    })?;
    let reframed = session.run_reframed_nested(
        prepared,
        shared_binary_prefix,
        target_fsb_prefix,
        MarginEvidenceBar::VerifiedTree,
    )?;
    let solved = state.take_solved(session);
    Ok(Dispatch::Finished(finish(
        reframed.verdict,
        &session.model,
        &solved,
        &session.opts,
    )))
}
