// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_chc::engines::ExternalInvariantValidationOwner;
use ay_chc::{CancellationToken, PdrConfig};
use ay_core::resource::ResourceGuard;
use ay_core::time::Instant;
use std::time::Duration;

mod archive_checks;
mod rows;
mod witnesses;

// Archive replay is expensive: exercise budget boundaries without repeating
// the entire replay once per work tick (quadratic work as the input grows).
fn work_cut_boundaries(work: u64) -> impl Iterator<Item = u64> {
    [0, 1, work / 4, work / 2, work - work / 4, work - 1, work]
        .into_iter()
        .collect::<std::collections::BTreeSet<_>>()
        .into_iter()
}

fn archive_bytes() -> Vec<u8> {
    include_str!("fixtures/original-archive.hex")
        .split_whitespace()
        .flat_map(|line| {
            let (pairs, remainder) = line.as_bytes().as_chunks::<2>();
            assert_eq!(remainder, &[] as &[u8]);
            pairs
        })
        .map(|pair| u8::from_str_radix(std::str::from_utf8(pair).unwrap(), 16).unwrap())
        .collect()
}

pub(super) fn fixture() -> R34Archive {
    let capture = capture::load().unwrap();
    let bytes = archive_bytes();
    assert_eq!(bytes.len() as u64, capture.archive.bytes);
    assert_eq!(capture::digest(&bytes), capture.archive.sha256);
    let files = archive::members(&bytes, &capture).unwrap();
    let inventory = Inventory::parse(include_str!(
        "../../../../../docs/integrations/model_checker_consumer_acceptance_manifest.json"
    ))
    .unwrap();
    R34Archive {
        capture,
        files,
        inventory_sha256: inventory.sha256,
    }
}

pub(super) fn original() -> ResourceGuard {
    let mut guard = ResourceGuard::new();
    guard.set_deadline(Some(Instant::now() + Duration::from_secs(15)));
    guard
}

fn owner(guard: &ResourceGuard) -> ExternalInvariantValidationOwner {
    let mut config = PdrConfig::production(false).with_memory_budget(Some(64 * 1024 * 1024));
    config.solve_timeout = Some(Duration::from_secs(15));
    ExternalInvariantValidationOwner::capture(guard, &config)
}

fn assert_not_promotable(record: &R34RowRecord) {
    assert!(!record.promotable_for_ask_closure);
    assert!(!matches!(
        record.status,
        R34RowStatus::Observed {
            checked_original_replay: true,
            ..
        }
    ));
}
