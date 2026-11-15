// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Injected cancellation controls; no solver or proof acceptance.

use crate::smt::deadline::{current_lane_token, lane_cancelled, ScopedLaneCancellation};
use crate::{CancellationToken, PdrConfig};

#[derive(Clone, Copy, Debug)]
pub(in crate::engines) enum Observer {
    Lane,
    Primary,
    External,
}

pub(in crate::engines) fn stop_reset_and_replace(
    parent: &CancellationToken,
    configured: &PdrConfig,
    observer: Observer,
) {
    let descendant = match observer {
        Observer::Lane => current_lane_token()
            .expect("attempt lane installed")
            .child(),
        Observer::Primary => configured
            .cancellation_token
            .as_ref()
            .expect("existing primary preserved")
            .child(),
        Observer::External => configured
            .external_cancellation_token
            .as_ref()
            .expect("existing external preserved")
            .child(),
    };
    parent.cancel();
    assert!(
        descendant.is_cancelled(),
        "descendant observes original stop"
    );
    parent.reset();
    assert!(
        !parent.is_cancelled(),
        "public parent reset remains unchanged"
    );
    let replacement = CancellationToken::new();
    {
        let _replacement = ScopedLaneCancellation::install(replacement.clone(), None);
        assert!(!lane_cancelled(), "replacement lane is healthy");
        assert!(
            descendant.is_cancelled(),
            "attempt observation survives reset"
        );
    }
    assert!(!replacement.is_cancelled());
}

pub(in crate::engines) fn local_child_stop(configured: &PdrConfig, primary: bool) {
    let child = if primary {
        configured.cancellation_token.as_ref().unwrap().child()
    } else {
        current_lane_token().unwrap().child()
    };
    child.cancel();
    assert!(child.is_cancelled());
    assert!(!current_lane_token().unwrap().is_cancelled());
    if let Some(token) = &configured.cancellation_token {
        assert!(!token.is_cancelled());
    }
}
