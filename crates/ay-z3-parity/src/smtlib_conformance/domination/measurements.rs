// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Deserialize only the measurements we use. Keeping three full JSON trees
//! (including duplicate reports and diagnostics) would make the full 438k-file
//! campaign consume gigabytes merely to compute four medians per input.
use super::*;

#[derive(Deserialize)]
pub(super) struct ParsedRun {
    kind: String,
    format_version: u64,
    pub(super) timeout_secs: u64,
    host: Value,
    resource: Value,
    ay_lib: Identity,
    z3_lib: Identity,
    ay_cli_identity: Identity,
    sampling: Sampling,
    divisions_filter: Option<Vec<String>>,
    pass: bool,
    self_certification_available: bool,
    files: Vec<FileRow>,
}

#[derive(Deserialize)]
struct Identity {
    sha256: String,
}
#[derive(Deserialize)]
struct Sampling {
    mode: String,
}
#[derive(Deserialize)]
struct FileRow {
    file: String,
    ay: SolverRow,
    z3: Option<SolverRow>,
    self_certified: bool,
    declared_conflict: bool,
    verdict_shape_mismatch: bool,
}
#[derive(Deserialize)]
struct SolverRow {
    outcome: String,
    decided: bool,
    wall_ms: f64,
    peak_rss_bytes: Option<u64>,
}

#[derive(Clone, Copy, Default)]
struct Sample {
    ay_ms: f64,
    z3_ms: f64,
    ay_rss: f64,
    z3_rss: f64,
    both_decided: bool,
}

pub(super) struct Campaign<'a> {
    population: &'a [PerformanceFile],
    conditions: Option<Value>,
    samples: Vec<Vec<Sample>>,
    failures: usize,
    losses: usize,
}

impl<'a> Campaign<'a> {
    pub(super) fn new(population: &'a [PerformanceFile]) -> Result<Self, String> {
        if population.is_empty()
            || population.iter().any(|file| file.query_count == 0)
            || population
                .windows(2)
                .any(|pair| pair[0].path >= pair[1].path)
        {
            return Err(
                "performance population must be nonempty, sorted, duplicate-free and have positive query counts".to_string(),
            );
        }
        Ok(Self {
            population,
            conditions: None,
            samples: Vec::new(),
            failures: 0,
            losses: 0,
        })
    }

    pub(super) fn record(
        &mut self,
        exit: i32,
        run: ParsedRun,
        cli_sha: &str,
        ay_sha: &str,
        z3_sha: &str,
    ) -> Result<(), String> {
        if run.kind != "ay-z3-scoreboard"
            || run.format_version != 3
            || run.ay_lib.sha256 != ay_sha
            || run.z3_lib.sha256 != z3_sha
            || run.ay_cli_identity.sha256 != cli_sha
            || run.sampling.mode != "all"
            || run.divisions_filter.is_some()
        {
            return Err("scoreboard identity or population scope mismatch".to_string());
        }
        let conditions = execution_conditions(&run)?;
        if let Some(expected) = &self.conditions {
            if expected != &conditions {
                return Err(
                    "host, timeout, or enforced resources changed between repetitions".to_string(),
                );
            }
        } else {
            self.conditions = Some(conditions);
        }
        if exit != 0 || !run.pass || !run.self_certification_available {
            self.failures += 1;
        }
        if run.files.len() != self.population.len() {
            return Err("missing or unexpected result file".to_string());
        }
        let mut present = vec![false; self.population.len()];
        let mut samples = vec![Sample::default(); self.population.len()];
        for row in run.files {
            let index = self
                .population
                .binary_search_by(|expected| expected.path.cmp(&row.file))
                .map_err(|_| "unexpected result file")?;
            if std::mem::replace(&mut present[index], true) {
                return Err("duplicate result row".to_string());
            }
            let z3 = row.z3.ok_or("missing reference measurement")?;
            let ay_verdicts = verdicts(&row.ay.outcome);
            let z3_verdicts = verdicts(&z3.outcome);
            let expected_queries = self.population[index].query_count;
            // Agreement between providers does not authenticate the number of
            // decisions: both can emit the same extra or incomplete vector.
            let query_counts_match = ay_verdicts
                .as_ref()
                .is_some_and(|values| values.len() == expected_queries)
                && z3_verdicts
                    .as_ref()
                    .is_some_and(|values| values.len() == expected_queries);
            let actually_decided = |v: &Option<Vec<&str>>| {
                v.as_ref()
                    .is_some_and(|values| values.iter().all(|v| *v != "unknown"))
            };
            if !query_counts_match
                || row.ay.decided != actually_decided(&ay_verdicts)
                || z3.decided != actually_decided(&z3_verdicts)
            {
                self.failures += 1;
            }
            if let (Some(ay), Some(reference)) = (ay_verdicts, z3_verdicts) {
                if ay.len() != reference.len()
                    || ay
                        .iter()
                        .zip(reference)
                        .any(|(a, z)| z != "unknown" && *a != z)
                {
                    self.losses += 1;
                }
            } else if z3.decided {
                self.losses += 1;
            }
            if row.declared_conflict
                || row.verdict_shape_mismatch
                || (row.ay.decided && !row.self_certified)
            {
                self.failures += 1;
            }
            if !row.ay.wall_ms.is_finite()
                || row.ay.wall_ms < 0.0
                || !z3.wall_ms.is_finite()
                || z3.wall_ms < 0.0
            {
                return Err("invalid measured time".to_string());
            }
            // A failed process can have no RSS observation; preserve it as a
            // failed run instead of interpreting absent memory as zero usage.
            if row.ay.peak_rss_bytes.is_none_or(|v| v == 0)
                || z3.peak_rss_bytes.is_none_or(|v| v == 0)
            {
                self.failures += 1;
            }
            samples[index] = Sample {
                ay_ms: row.ay.wall_ms,
                z3_ms: z3.wall_ms,
                ay_rss: row.ay.peak_rss_bytes.unwrap_or(0) as f64,
                z3_rss: z3.peak_rss_bytes.unwrap_or(0) as f64,
                both_decided: query_counts_match && row.ay.decided && z3.decided,
            };
        }
        if present.iter().any(|v| !*v) {
            return Err("missing result file".to_string());
        }
        self.samples.push(samples);
        Ok(())
    }

    pub(super) fn finish(self) -> Result<Assessment, String> {
        let count = self.samples.len();
        if !(3..=31).contains(&count) || count % 2 == 0 {
            return Err("at least three odd repetitions required".to_string());
        }
        let mut result = Assessment {
            passed: false,
            files: self.population.len(),
            timed_files: 0,
            slower_files: 0,
            greater_memory_files: 0,
            capability_losses: self.losses,
            execution_or_validation_failures: self.failures,
            median_total_ay_ms: 0.0,
            median_total_z3_ms: 0.0,
        };
        let mut ay_ms = Vec::with_capacity(count);
        let mut z3_ms = Vec::with_capacity(count);
        let mut ay_rss = Vec::with_capacity(count);
        let mut z3_rss = Vec::with_capacity(count);
        for index in 0..self.population.len() {
            ay_ms.clear();
            z3_ms.clear();
            ay_rss.clear();
            z3_rss.clear();
            if !self.samples.iter().all(|run| run[index].both_decided) {
                continue;
            }
            for run in &self.samples {
                let row = run[index];
                ay_ms.push(row.ay_ms);
                z3_ms.push(row.z3_ms);
                ay_rss.push(row.ay_rss);
                z3_rss.push(row.z3_rss);
            }
            let ay = median(&mut ay_ms);
            let z3 = median(&mut z3_ms);
            result.median_total_ay_ms += ay;
            result.median_total_z3_ms += z3;
            if ay.max(z3) >= crate::bench::WIN_LOSS_MIN_SECS * 1000.0 {
                result.timed_files += 1;
                if ay > z3 {
                    result.slower_files += 1;
                }
            }
            let ay = median(&mut ay_rss);
            let z3 = median(&mut z3_rss);
            if ay.max(z3) >= 5.0 * 1024.0 * 1024.0 && ay > z3 {
                result.greater_memory_files += 1;
            }
        }
        result.passed = result.timed_files > 0
            && result.slower_files == 0
            && result.greater_memory_files == 0
            && result.capability_losses == 0
            && result.execution_or_validation_failures == 0
            && result.median_total_ay_ms <= result.median_total_z3_ms;
        Ok(result)
    }
}

pub(super) fn execution_conditions(run: &ParsedRun) -> Result<Value, String> {
    let mut values = Vec::new();
    for key in [
        "effective_jobs",
        "memlimit_mb_per_child",
        "nbcore_per_child",
        "solver_timeout_secs",
        "hard_timeout_secs",
    ] {
        values.push(json!([key, number(&run.resource, key)?]));
    }
    let enforcement = run.resource["external_ffi"]["enforcement"]
        .as_str()
        .ok_or("missing resource enforcement")?;
    if enforcement != ENFORCEMENT_RSS_WATCHDOG_V1
        || number(&run.resource, "effective_jobs")? != 1.0
        || number(&run.resource, "memlimit_mb_per_child")? <= 0.0
        || number(&run.resource, "nbcore_per_child")? < 1.0
        || number(&run.resource, "solver_timeout_secs")? != run.timeout_secs as f64
        || number(&run.resource, "hard_timeout_secs")? < run.timeout_secs as f64
    {
        return Err("performance requires one job with the native RSS watchdog".to_string());
    }
    if run.host.is_null() {
        return Err("missing host identity".to_string());
    }
    Ok(
        json!({"resources":values,"enforcement":enforcement,"host":run.host,"timeout":run.timeout_secs}),
    )
}

#[cfg(test)]
pub(super) fn assess(
    reports: &[(i32, Value)],
    population: &[PerformanceFile],
    cli: &str,
    ay: &str,
    z3: &str,
) -> Result<Assessment, String> {
    let mut campaign = Campaign::new(population)?;
    for (exit, report) in reports {
        campaign.record(
            *exit,
            serde_json::from_value(report.clone()).map_err(|e| e.to_string())?,
            cli,
            ay,
            z3,
        )?;
    }
    campaign.finish()
}
