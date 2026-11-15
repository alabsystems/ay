// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! One exact archived R34 observation, not an acceptance/pass checker.
//! Run only through the existing OOM guard's serial 4 GiB / 15 s envelope.

use std::io::Write as _;
use std::path::Path;
use std::time::Duration;

use ay_bench::acceptance_inventory::r34::{R34Archive, R34Row, R34Witness};
use ay_bench::acceptance_inventory::Inventory;
use ay_bench::BenchError;
use ay_chc::engines::ExternalInvariantValidationOwner;
use ay_chc::{CancellationToken, PdrConfig};
use ay_core::resource::ResourceGuard;
use ay_core::time::Instant;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let [inventory_path, archive_path, case] = args.as_slice() else {
        return Err(BenchError::msg(
            "usage: model_checker_consumer_r34_replay INVENTORY ARCHIVE CASE",
        )
        .into());
    };
    let inventory = Inventory::load(Path::new(inventory_path))?;
    let request = inventory
        .document
        .request_inventory
        .iter()
        .find(|r| r.id == "R34")
        .ok_or_else(|| BenchError::msg("frozen R34 contract missing"))?;
    let millis = request.metadata["consumer_lane_budgets_ms"]["W5/W6"]
        .as_u64()
        .ok_or_else(|| BenchError::msg("original W5/W6 lane budget missing"))?;
    if millis != 15_000 {
        return Err(BenchError::msg("original lane budget changed").into());
    }
    let mut original = ResourceGuard::new();
    original.set_deadline(Some(Instant::now() + Duration::from_millis(millis)));
    // This is a local cooperative cap as well as the REQUIRED external tree
    // watchdog. It does not rewrite the captured EncodeConfig's term budget.
    ay_sys::set_process_memory_limit(usize::try_from(4_u64 * 1024 * 1024 * 1024)?);
    let cancellation = CancellationToken::new();
    let archive = R34Archive::load(Path::new(inventory_path), Path::new(archive_path))?;
    let record = match case.as_str() {
        "static-p0" => serde_json::to_value(archive.replay_row(
            R34Row::StaticErrorP0,
            &original,
            &cancellation,
        )?)?,
        "static-definition7" => serde_json::to_value(archive.replay_row(
            R34Row::StaticErrorDefinition7,
            &original,
            &cancellation,
        )?)?,
        "static-p22" => serde_json::to_value(archive.replay_row(
            R34Row::StaticErrorP22,
            &original,
            &cancellation,
        )?)?,
        "alloc-p28" => serde_json::to_value(archive.replay_row(
            R34Row::AllocErrorP28,
            &original,
            &cancellation,
        )?)?,
        "static-witness0001" => inspect(&archive, R34Witness::Static0001, &original)?,
        "static-witness0003" => inspect(&archive, R34Witness::Static0003, &original)?,
        "bitmask-witness0026" => inspect(&archive, R34Witness::Bitmask0026, &original)?,
        _ => return Err(BenchError::msg("unknown exact R34 case").into()),
    };
    let output = serde_json::json!({
        "schema": "ay.model-checker-consumer-r34-observation/v1",
        "record": record,
        "available_parallelism": std::thread::available_parallelism()?.get(),
        "local_process_cap_bytes": ay_sys::get_process_memory_limit(),
        "final_original_guard_refusal": original.exhausted().map(|why| format!("{why:?}")),
        "original_dispositions": archive.original_dispositions(),
        "promotable_for_ask_closure": false
    });
    let mut stdout = std::io::stdout().lock();
    serde_json::to_writer(&mut stdout, &output)?;
    stdout.write_all(b"\n")?;
    Ok(())
}

fn inspect(
    archive: &R34Archive,
    case: R34Witness,
    original: &ResourceGuard,
) -> Result<serde_json::Value, Box<dyn std::error::Error>> {
    // This owner bounds reconstruction ONLY. It is not the absent historical
    // per-invocation witness grant, and inspect_witness never executes a solver.
    let mut config = PdrConfig::production(false)
        .with_memory_budget(Some(usize::try_from(4_u64 * 1024 * 1024 * 1024)?));
    config.solve_timeout = original
        .effective_deadline()
        .map(|deadline| deadline.saturating_duration_since(Instant::now()));
    let owner = ExternalInvariantValidationOwner::capture(original, &config);
    Ok(serde_json::to_value(
        archive.inspect_witness(case, &owner)?,
    )?)
}
