//! One correctness projection for native run summaries, persistence and score.
//! Reference agreement is an observation, not independent model/proof replay.
use super::{definitive_item, is_definitive, verdicts_match, ResultItem, ResultsFile};
use crate::error::{BenchError, Result};
use serde::{Deserialize, Deserializer};

#[derive(Default, Clone, Copy)]
enum Exit {
    #[default]
    Missing,
    Observed(Option<i32>),
}
impl<'de> Deserialize<'de> for Exit {
    fn deserialize<D: Deserializer<'de>>(d: D) -> std::result::Result<Self, D::Error> {
        Ok(Self::Observed(Option::<i32>::deserialize(d)?))
    }
}
#[derive(Deserialize)]
struct Item {
    #[serde(alias = "name")]
    file: Option<String>,
    expected: Option<String>,
    #[serde(alias = "ay_actual", alias = "ay_result", alias = "actual")]
    result: Option<String>,
    #[serde(
        alias = "ay_elapsed_sec",
        alias = "ay_time_sec",
        alias = "elapsed_sec",
        alias = "wall_time_sec"
    )]
    time_sec: Option<f64>,
    cpu_time_sec: Option<f64>,
    #[serde(default, alias = "ay_exit_code")]
    exit_code: Exit,
    correct: Option<bool>,
    expected_source: Option<String>,
    solver_input_hash: Option<String>,
    harness_error: Option<String>,
}
#[derive(Deserialize)]
struct Comparison {
    file: String,
    solver_input_hash: Option<String>,
    ay_result: String,
    ref_result: String,
    reference_runs: Option<Vec<ReferenceRun>>,
}
#[derive(Deserialize)]
struct ReferenceRun {
    result: String,
    solver_input_hash: Option<String>,
    #[serde(default)]
    exit_code: Exit,
    #[serde(default)]
    stdout_truncated: bool,
    #[serde(default)]
    stderr_truncated: bool,
    harness_error: Option<String>,
}
#[derive(Deserialize)]
struct Reference {
    items: Vec<Comparison>,
}
#[derive(Deserialize)]
struct File {
    items: Option<Vec<Item>>,
    benchmarks: Option<Vec<Item>>,
    metrics: Option<serde_json::Value>,
    settings: Option<serde_json::Value>,
    comparisons: Option<Vec<Comparison>>,
    reference_comparisons: Option<Vec<Reference>>,
}

#[derive(Clone, Copy)]
struct Observation<'a> {
    file: &'a str,
    hash: Option<&'a str>,
    ay: &'a str,
    reference: &'a str,
    valid: bool,
}

fn project<'a>(
    mut item: ResultItem,
    source: Option<&str>,
    hash: Option<&str>,
    invalid: bool,
    observations: impl Iterator<Item = Observation<'a>>,
) -> Result<ResultItem> {
    if invalid || !super::valid_process(&item) {
        // Native watchdog outcomes deliberately have no ordinary exit code.
        // Preserve those classes; an invalid claimed SAT/UNSAT is never solved.
        if !matches!(item.result.as_deref(), Some("timeout" | "memout")) {
            item.result = Some("error".into());
        }
        return Ok(item);
    }
    if source.is_some_and(|source| !matches!(source, "header" | "path" | "header+path")) {
        item.expected = None;
    }
    if !definitive_item(&item) {
        return Ok(item);
    }
    let actual = item.result.as_deref().unwrap_or("error");
    let expected = item
        .expected
        .as_deref()
        .filter(|expected| is_definitive(expected));
    if item.correct == Some(true)
        && expected.is_some_and(|expected| !verdicts_match(expected, actual))
    {
        return Err(BenchError::msg(
            "contradictory checked correctness and authoritative expected verdict",
        ));
    }
    let mut agrees = false;
    let mut disagrees = false;
    for observation in observations {
        if item.file.as_deref() != Some(observation.file)
            || hash.filter(|s| !s.is_empty()).is_none()
            || hash != observation.hash
        {
            continue;
        }
        if !verdicts_match(observation.ay, actual) {
            return Err(BenchError::msg(
                "same-input reference row names a different AY result",
            ));
        }
        if !observation.valid {
            continue;
        }
        if is_definitive(observation.reference) {
            if verdicts_match(observation.reference, actual) {
                agrees = true;
            } else {
                disagrees = true;
            }
        }
    }
    // Explicit negative checking remains negative. An authoritative expected
    // verdict or explicit positive adjudication settles AY before a possibly
    // wrong reference is considered. No label means genuinely not checked.
    item.correct = if item.correct == Some(false) {
        Some(false)
    } else if let Some(expected) = expected {
        Some(verdicts_match(expected, actual))
    } else if item.correct == Some(true) {
        Some(true)
    } else if disagrees {
        Some(false)
    } else if agrees {
        Some(true)
    } else {
        None
    };
    Ok(item)
}

pub(super) fn deserialize<'de, D: Deserializer<'de>>(
    d: D,
) -> std::result::Result<ResultsFile, D::Error> {
    let file = File::deserialize(d)?;
    if file.items.is_some() && file.benchmarks.is_some() {
        return Err(serde::de::Error::custom(
            "ambiguous items and benchmarks collections",
        ));
    }
    let indexed = observation_index(
        file.comparisons
            .iter()
            .flatten()
            .chain(
                file.reference_comparisons
                    .iter()
                    .flatten()
                    .flat_map(|r| r.items.iter()),
            )
            .map(|row| Observation {
                file: &row.file,
                hash: row.solver_input_hash.as_deref(),
                ay: &row.ay_result,
                reference: &row.ref_result,
                valid: row.reference_runs.as_ref().is_none_or(|runs| {
                    !runs.is_empty()
                        && runs.iter().all(|run| {
                            verdicts_match(&run.result, &row.ref_result)
                                && run.solver_input_hash == row.solver_input_hash
                                && !run.stdout_truncated
                                && !run.stderr_truncated
                                && run.harness_error.is_none()
                                && match run.exit_code {
                                    Exit::Missing => true,
                                    Exit::Observed(code) => process_ok(&run.result, code),
                                }
                        })
                }),
            }),
    );
    let project_items = |items: Option<Vec<Item>>| -> Result<Option<Vec<ResultItem>>> {
        items
            .map(|items| {
                items
                    .into_iter()
                    .map(|item| {
                        let invalid = matches!(item.exit_code, Exit::Observed(None))
                            || item.harness_error.is_some();
                        let code = match item.exit_code {
                            Exit::Observed(code) => code,
                            Exit::Missing => None,
                        };
                        let row = ResultItem {
                            file: item.file,
                            expected: item.expected,
                            result: item.result,
                            time_sec: item.time_sec,
                            cpu_time_sec: item.cpu_time_sec,
                            exit_code: code,
                            correct: item.correct,
                        };
                        let observations = indexed
                            .get(row.file.as_deref().unwrap_or(""))
                            .into_iter()
                            .flatten()
                            .copied();
                        project(
                            row,
                            item.expected_source.as_deref(),
                            item.solver_input_hash.as_deref(),
                            invalid,
                            observations,
                        )
                    })
                    .collect()
            })
            .transpose()
    };
    let items = project_items(file.items).map_err(serde::de::Error::custom)?;
    let benchmarks = project_items(file.benchmarks).map_err(serde::de::Error::custom)?;
    Ok(ResultsFile {
        items,
        benchmarks,
        metrics: file.metrics,
        settings: file.settings,
    })
}

pub(super) fn native_items(results: &crate::native::NativeResults) -> Result<Vec<ResultItem>> {
    let indexed = observation_index(
        results
            .comparisons
            .iter()
            .flatten()
            .chain(
                results
                    .reference_comparisons
                    .iter()
                    .flatten()
                    .flat_map(|r| r.items.iter()),
            )
            .map(|row| Observation {
                file: &row.file,
                hash: Some(row.solver_input_hash.as_str()),
                ay: &row.ay_result,
                reference: &row.ref_result,
                valid: !row.reference_runs.is_empty()
                    && row.reference_runs.iter().all(|run| {
                        verdicts_match(&run.result, &row.ref_result)
                            && run.solver_input_hash == row.solver_input_hash
                            && !run.stdout_truncated
                            && !run.stderr_truncated
                            && run.harness_error.is_none()
                            && process_ok(&run.result, run.exit_code)
                    }),
            }),
    );
    results
        .items
        .iter()
        .map(|item| {
            let row = ResultItem {
                file: Some(item.file.clone()),
                expected: item.expected.clone(),
                result: Some(item.result.clone()),
                time_sec: Some(item.time_sec),
                cpu_time_sec: Some(item.cpu_time_sec),
                exit_code: item.exit_code,
                correct: None,
            };
            let observations = indexed
                .get(item.file.as_str())
                .into_iter()
                .flatten()
                .copied();
            project(
                row,
                Some(&item.expected_source),
                item.solver_input_hash.as_deref(),
                item.harness_error.is_some() || item.exit_code.is_none(),
                observations,
            )
        })
        .collect()
}

fn process_ok(result: &str, code: Option<i32>) -> bool {
    match code {
        Some(0) => true,
        Some(10) => result.eq_ignore_ascii_case("sat"),
        Some(20) => result.eq_ignore_ascii_case("unsat"),
        _ => false,
    }
}

fn observation_index<'a>(
    observations: impl Iterator<Item = Observation<'a>>,
) -> std::collections::BTreeMap<&'a str, Vec<Observation<'a>>> {
    let mut indexed = std::collections::BTreeMap::<_, Vec<_>>::new();
    for observation in observations {
        indexed
            .entry(observation.file)
            .or_default()
            .push(observation);
    }
    indexed
}

#[cfg(test)]
mod tests {
    use super::super::{score_chc, score_hwmcc, score_sat, score_smt};
    use super::*;
    use serde_json::{json, Value};

    fn data() -> Value {
        json!({"items":[{"file":"case","result":"sat","exit_code":0,"time_sec":0.1,"solver_input_hash":"sha256:actual"}],
            "comparisons":[{"file":"case","solver_input_hash":"sha256:actual","ay_result":"sat","ref_result":"unsat","agreement":"agree"}]})
    }
    fn load(value: Value) -> ResultsFile {
        serde_json::from_value(value).unwrap()
    }

    #[test]
    fn scoring_evidence_retains_same_input_conflict_across_competition_scores() {
        let file = load(data());
        let items = file.items();
        assert_eq!(items[0].correct, Some(false));
        let smt = score_smt(items, 5.0, "QF_BV");
        assert!(!smt.sound);
        assert_eq!(smt.errors, 1);
        assert_eq!(smt.solved, 0);
        assert_eq!(smt.verification.wrong, 1);
        let sat = score_sat(items, 5.0);
        assert!(sat.disqualified);
        assert_eq!(sat.solved, 0);
        assert_eq!(score_chc(items, 5.0, "LIA").wrong, 1);
        assert_eq!(score_hwmcc(items, 5.0, "test").wrong, 1);
        let mut value = data();
        value["reference_comparisons"] = json!([{"items":[{"file":"case","solver_input_hash":"sha256:actual","ay_result":"sat","ref_result":"sat"}]}]);
        assert_eq!(
            load(value).items()[0].correct,
            Some(false),
            "agreement cannot hide a later conflict"
        );
    }
    #[test]
    fn scoring_evidence_honors_authoritative_expected_and_explicit_adjudication() {
        let mut value = data();
        value["items"][0]["expected"] = json!("sat");
        value["items"][0]["expected_source"] = json!("header");
        let file = load(value.clone());
        assert_eq!(file.items()[0].correct, Some(true));
        assert!(score_smt(file.items(), 5.0, "test").sound);
        value["items"][0]["expected_source"] = json!("reference");
        assert_eq!(
            load(value).items()[0].correct,
            Some(false),
            "weak labels cannot overrule observed conflict"
        );
        let mut value = data();
        value["items"][0]["correct"] = json!(true);
        assert_eq!(load(value.clone()).items()[0].correct, Some(true));
        value["items"][0]["expected"] = json!("unsat");
        value["items"][0]["expected_source"] = json!("header");
        assert!(
            serde_json::from_value::<ResultsFile>(value).is_err(),
            "incompatible strong evidence must refuse"
        );
        let mut value = data();
        value["items"][0]["correct"] = json!(false);
        value["items"][0]["expected"] = json!("sat");
        assert_eq!(load(value).items()[0].correct, Some(false));
    }
    #[test]
    fn scoring_evidence_keeps_not_checked_and_rejected_candidates_distinct_from_wrong_answers() {
        let mut value = data();
        value["comparisons"][0]["solver_input_hash"] = json!("sha256:different");
        let file = load(value);
        assert_eq!(file.items()[0].correct, None);
        let score = score_smt(file.items(), 5.0, "test");
        assert_eq!(score.verification.not_checked, 1);
        assert_eq!(score.verification.checked, 0);
        let mut value = data();
        value["items"][0]["result"] = json!("unknown");
        value["items"][0]["correct"] = json!(false);
        let file = load(value);
        let score = score_smt(file.items(), 5.0, "test");
        assert_eq!(score.errors, 0);
        assert_eq!(score.solved, 0);
        assert_eq!(score.verification.non_definitive, 1);
    }
    #[test]
    fn scoring_evidence_declines_aborted_nonzero_and_inconsistent_verdicts() {
        for exit in [json!(null), json!(1), json!(20)] {
            let mut value = data();
            value["items"][0]["exit_code"] = exit;
            let file = load(value);
            assert_eq!(file.items()[0].result.as_deref(), Some("error"));
            assert_eq!(score_sat(file.items(), 5.0).solved, 0);
        }
        let mut value = data();
        value["comparisons"][0]["ay_result"] = json!("unsat");
        assert!(serde_json::from_value::<ResultsFile>(value).is_err());
        let mut value = data();
        value["comparisons"][0]["reference_runs"] =
            json!([{"result":"unsat","solver_input_hash":"sha256:actual","exit_code":null}]);
        assert_eq!(
            load(value).items()[0].correct,
            None,
            "aborted reference cannot establish a wrong AY answer"
        );
        let mut value = data();
        value["items"][0]["result"] = json!("timeout");
        value["items"][0]["exit_code"] = json!(null);
        let file = load(value);
        let score = score_smt(file.items(), 5.0, "test");
        assert_eq!(score.timeout_count, 1);
        assert_eq!(score.errors, 0);
    }
}
