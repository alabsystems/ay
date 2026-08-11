// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Source-authenticated SMT-LIB 2.7 lexical and grammar conformance.
//!
//! The pinned language snapshot is the authority.  Every production in the
//! contract has one authenticated source row, one positive live AY witness,
//! and one negative witness.  Input-language negatives must produce one
//! positioned error and then execute a sentinel command, proving deterministic
//! continued-execution recovery.  Response-language negatives are deliberate
//! malformed-output controls for the same closed response recognizers used on
//! live AY output.

use super::reference_inventory::{self, LanguageGrammarProduction};
use super::*;
use ay_frontend::SExpr;

pub(super) const VALIDATOR_ID: &str = "builtin.lexical-grammar.v1";

const DIMENSION_ID: &str = "language.lexical-and-grammar";
const DEFAULT_TIMEOUT_SECS: u64 = 10;
const SUCCESS_MARKER: &str = "AY_GRAMMAR_OK";
const SUCCESS_STDOUT: &str = "AY_GRAMMAR_OK\n";
const RECOVERY_MARKER: &str = "AY_GRAMMAR_RECOVERED";
const SOURCE_CASE_COUNT: usize = PRODUCTION_NAMES.len();
const POSITIVE_CASE_COUNT: usize = PRODUCTION_NAMES.len();
const NEGATIVE_CASE_COUNT: usize = PRODUCTION_NAMES.len();
const DETAILED_CASE_COUNT: usize = SOURCE_CASE_COUNT + POSITIVE_CASE_COUNT + NEGATIVE_CASE_COUNT;

/// Every LHS production in the normative macro blocks named by the dimension.
/// `general_response` is expanded from `cGeneralResponse`, which
/// `cResponsesII` incorporates verbatim.
pub(super) const PRODUCTION_NAMES: [&str; 45] = [
    "white_space_char",
    "printable_char",
    "digit",
    "letter",
    "numeral",
    "decimal",
    "hexadecimal",
    "binary",
    "string",
    "simple_symbol",
    "symbol",
    "keyword",
    "spec_constant",
    "s_expr",
    "index",
    "identifier",
    "sort",
    "attribute_value",
    "attribute",
    "qual_identifier",
    "var_binding",
    "sorted_var",
    "symbol_",
    "pattern",
    "match_case",
    "term",
    "error-behavior",
    "reason-unknown",
    "model_response",
    "info_response",
    "valuation_pair",
    "t_valuation_pair",
    "check_sat_response",
    "echo_response",
    "get_assertions_response",
    "get_assignment_response",
    "get_info_response",
    "get_model_response",
    "get_option_response",
    "get_proof_response",
    "get_unsat_assump_response",
    "get_unsat_core_response",
    "get_value_response",
    "specific_success_response",
    "general_response",
];

const RESPONSE_PRODUCTION_START: usize = 26;

pub(super) fn source_macro_name(name: &str) -> Option<&'static str> {
    PRODUCTION_NAMES
        .iter()
        .position(|candidate| *candidate == name)
        .and_then(|index| match index {
            0..=3 => Some("aLexical"),
            4..=11 => Some("tokens"),
            12..=13 => Some("sexpressions"),
            14..=15 => Some("cIdentifiers"),
            16 => Some("cSorts"),
            17..=18 => Some("cAttributes"),
            19..=25 => Some("cTerms"),
            26..=31 => Some("cResponsesI"),
            32..=43 => Some("cResponsesII"),
            44 => Some("cGeneralResponse"),
            _ => None,
        })
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ResponseKind {
    ErrorBehavior,
    ReasonUnknown,
    ModelResponse,
    InfoResponse,
    ValuationPair,
    TruthValuationPair,
    CheckSat,
    Echo,
    GetAssertions,
    GetAssignment,
    GetInfo,
    GetModel,
    GetOption,
    GetProof,
    GetUnsatAssumptions,
    GetUnsatCore,
    GetValue,
    SpecificSuccess,
    General,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ProcessExpectation {
    ExactSuccess,
    PositionedRecovery,
    Response(ResponseKind),
}

impl ProcessExpectation {
    fn text(self, obligation: &str) -> String {
        match self {
            Self::ExactSuccess => format!(
                "{obligation}; exact stdout={SUCCESS_MARKER:?} plus newline; stderr=\"\"; exit=0"
            ),
            Self::PositionedRecovery => format!(
                "{obligation}; one `(error \"line 2 column 3: ...\")`, then {RECOVERY_MARKER:?}; stderr=\"\"; exit=1"
            ),
            Self::Response(kind) => format!(
                "{obligation}; live output satisfies closed {kind:?} response recognizer; stderr=\"\"; exit=0"
            ),
        }
    }
}

#[derive(Debug)]
struct ProcessCase {
    id: String,
    input: Vec<u8>,
    expectation: ProcessExpectation,
    obligation: String,
}

impl ProcessCase {
    fn expected(&self) -> String {
        self.expectation.text(&self.obligation)
    }
}

#[derive(Debug)]
struct PreparedCampaign {
    static_rows: Vec<ValidatorCase>,
    process_cases: Vec<ProcessCase>,
}

#[derive(Debug, Eq, PartialEq)]
struct Execution {
    ay_sha256: String,
    resource_envelope: String,
    result: ValidatorResult,
    cases: CaseCounts,
    case_results: Vec<ValidatorCase>,
}

pub(super) fn run(args: &[String]) -> Result<i32, String> {
    let mut manifest: Option<PathBuf> = None;
    let mut receipt_path: Option<PathBuf> = None;
    let mut snapshot_path: Option<PathBuf> = None;
    let mut ay_override: Option<PathBuf> = None;
    let mut timeout_secs = DEFAULT_TIMEOUT_SECS;
    let mut index = 0usize;
    while index < args.len() {
        match args[index].as_str() {
            "--receipt" => {
                index += 1;
                receipt_path = Some(PathBuf::from(
                    args.get(index).ok_or("--receipt needs a path")?,
                ));
            }
            "--source-snapshot" => {
                index += 1;
                snapshot_path = Some(PathBuf::from(
                    args.get(index).ok_or("--source-snapshot needs a path")?,
                ));
            }
            "--ay" => {
                index += 1;
                ay_override = Some(PathBuf::from(args.get(index).ok_or("--ay needs a path")?));
            }
            "--timeout" => {
                index += 1;
                timeout_secs = args
                    .get(index)
                    .ok_or("--timeout needs seconds")?
                    .parse()
                    .map_err(|_| "--timeout must be a positive integer")?;
                if timeout_secs == 0 || timeout_secs > 3600 {
                    return Err("--timeout must be between 1 and 3600 seconds".to_string());
                }
            }
            flag if flag.starts_with("--") => {
                return Err(format!("unknown lexical-grammar flag {flag:?}"));
            }
            value => {
                if manifest.replace(PathBuf::from(value)).is_some() {
                    return Err("lexical-grammar takes exactly one manifest path".to_string());
                }
            }
        }
        index += 1;
    }

    let manifest = manifest.ok_or("lexical-grammar needs a manifest path")?;
    let receipt_path = receipt_path.ok_or("lexical-grammar requires --receipt <path>")?;
    let snapshot_path = snapshot_path.ok_or("lexical-grammar requires --source-snapshot <path>")?;
    let loaded = load_contract(&manifest)?;
    let report = validate_contract(&loaded.contract, &loaded.base, ValidationMode::Structural)?;
    if loaded.contract.campaign_id == UNASSIGNED_CAMPAIGN {
        return Err("assign a real --campaign id before producing evidence".to_string());
    }
    let dimension = grammar_dimension(&loaded.contract)?;
    if dimension.inventory.granularity != InventoryGranularity::ItemLevel {
        return Err(
            "language.lexical-and-grammar must retain its closed item-level inventory".to_string(),
        );
    }
    let subject = loaded
        .contract
        .subject
        .ay_executable
        .as_ref()
        .ok_or("lexical-grammar requires subject.ay_executable")?;
    let ay = ay_override.unwrap_or_else(|| artifact_path(&loaded.base, &subject.path));
    let source = reference_inventory::load_language_grammar(
        &loaded.contract,
        dimension,
        &loaded.base,
        Some(&snapshot_path),
    )?;
    let execution = execute(
        &ay,
        &subject.sha256,
        &source.productions,
        Duration::from_secs(timeout_secs),
        loaded.contract.resource_envelope.as_deref(),
    )?;
    let output_relative = future_relative_output(&loaded.base, &receipt_path)?;
    let current_exe = fs::canonicalize(
        std::env::current_exe().map_err(|error| format!("locating parity executable: {error}"))?,
    )
    .map_err(|error| format!("canonicalizing parity executable: {error}"))?;
    let validator_sha = sha256_file(&current_exe, "parity validator")?;
    let receipt = ValidatorReceipt {
        schema: VALIDATOR_RECEIPT_SCHEMA.to_string(),
        campaign_id: loaded.contract.campaign_id.clone(),
        profile_id: PROFILE_ID.to_string(),
        profile_sha256: canonical_profile_sha256()?,
        dimension_id: DIMENSION_ID.to_string(),
        requirement_ids: dimension
            .requirements
            .iter()
            .map(|row| row.id.clone())
            .collect(),
        inventory_sha256: dimension.inventory.sha256.clone(),
        validator: ValidatorIdentity {
            id: VALIDATOR_ID.to_string(),
            kind: ValidatorKind::TranscriptConformance,
            path: current_exe.to_string_lossy().into_owned(),
            sha256: validator_sha,
        },
        subject: ReceiptSubject {
            ay_executable_sha256: Some(execution.ay_sha256.clone()),
            ay_shared_library_sha256: loaded
                .contract
                .subject
                .ay_shared_library
                .as_ref()
                .map(|artifact| artifact.sha256.clone()),
        },
        z3_binary_sha256: None,
        z3_shared_library_sha256: None,
        reference_inputs: vec![source.binding],
        auxiliary_tools: Vec::new(),
        source_provenance: None,
        resource_envelope: Some(execution.resource_envelope.clone()),
        exhaustive: true,
        result: execution.result,
        cases: execution.cases,
        case_results: execution.case_results,
    };
    let bytes = pretty_json(&receipt)?;
    atomic_write_new(&receipt_path, &bytes)?;
    let receipt_sha = sha256_bytes(&bytes);
    println!(
        "lexical-grammar={} receipt={} sha256={}",
        if receipt.result == ValidatorResult::Pass {
            "PASS"
        } else {
            "FAIL"
        },
        output_relative,
        receipt_sha
    );
    println!(
        "coverage={} productions positive={} negative={} detailed-cases={} source=catalog-closed",
        PRODUCTION_NAMES.len(),
        POSITIVE_CASE_COUNT,
        NEGATIVE_CASE_COUNT,
        receipt.cases.total
    );
    println!(
        "attach with: ay-z3-parity smtlib-conformance attach {} {} --out <new-manifest>",
        manifest.display(),
        receipt_path.display()
    );
    if !report.complete {
        println!(
            "note: the rest of the contract remains incomplete ({} existing blockers)",
            report.blockers.len()
        );
    }
    Ok(i32::from(receipt.result != ValidatorResult::Pass))
}

pub(super) fn validate_and_replay(
    receipt: &ValidatorReceipt,
    context: EvidenceContext<'_>,
) -> Result<(), String> {
    let expected_ids = context
        .dimension
        .requirements
        .iter()
        .map(|row| row.id.clone())
        .collect::<Vec<_>>();
    if receipt.validator.kind != ValidatorKind::TranscriptConformance
        || context.dimension.id != DIMENSION_ID
        || receipt.requirement_ids != expected_ids
        || !receipt.exhaustive
        || receipt.z3_binary_sha256.is_some()
        || receipt.z3_shared_library_sha256.is_some()
        || !receipt.auxiliary_tools.is_empty()
        || receipt.source_provenance.is_some()
    {
        return Err(format!(
            "{VALIDATOR_ID} has invalid kind, dimension, coverage, exhaustive flag, or foreign bindings"
        ));
    }
    let [input] = receipt.reference_inputs.as_slice() else {
        return Err(format!(
            "{VALIDATOR_ID} requires exactly one authenticated language snapshot"
        ));
    };
    if input.id != "smtlib-language" || input.cohort != SourceCohort::SmtlibLanguage {
        return Err(format!(
            "{VALIDATOR_ID} is not bound to the authenticated SMT-LIB language source"
        ));
    }
    let productions = reference_inventory::load_bound_language_grammar(
        input,
        context.manifest_dir,
        &canonical_profile(),
    )?;
    let prepared = prepare_campaign(&productions)?;
    validate_recorded_shape(receipt, &prepared)?;
    if context.mode.replays_registered_validators() {
        let envelope = receipt
            .resource_envelope
            .as_deref()
            .ok_or("lexical-grammar receipt has no resource envelope")?;
        let parsed = parse_resource_envelope(envelope)?;
        if parsed.jobs != 1 {
            return Err("lexical-grammar receipts require a one-job resource envelope".to_string());
        }
        let subject = context
            .contract
            .subject
            .ay_executable
            .as_ref()
            .ok_or("lexical-grammar replay requires subject.ay_executable")?;
        let ay = artifact_path(context.manifest_dir, &subject.path);
        let live = execute(
            &ay,
            &subject.sha256,
            &productions,
            parsed.timeout,
            Some(envelope),
        )?;
        if receipt.result != live.result
            || receipt.cases != live.cases
            || receipt.case_results != live.case_results
        {
            return Err(format!(
                "{VALIDATOR_ID} receipt does not match a fresh authenticated AY replay"
            ));
        }
    }
    Ok(())
}

fn grammar_dimension(contract: &Contract) -> Result<&Dimension, String> {
    contract
        .dimensions
        .iter()
        .find(|dimension| dimension.id == DIMENSION_ID)
        .ok_or_else(|| format!("closed {DIMENSION_ID} dimension is missing"))
}

fn execute(
    ay_source: &Path,
    expected_ay_sha256: &str,
    productions: &[LanguageGrammarProduction],
    timeout: Duration,
    required_envelope: Option<&str>,
) -> Result<Execution, String> {
    if timeout.is_zero() || timeout > Duration::from_hours(1) {
        return Err("lexical-grammar timeout must be between 1ns and 3600 seconds".to_string());
    }
    let prepared = prepare_campaign(productions)?;
    let staged = stage_authenticated_executable(
        ay_source,
        expected_ay_sha256,
        "lexical-grammar AY executable",
    )?;
    let repo_root = locate_repo_root()?;
    let resources = PlannedResources::plan(
        &repo_root,
        1,
        "ay-z3-parity smtlib-conformance lexical-grammar",
    )
    .map_err(|error| error.to_string())?;
    let resource_envelope = effective_execution_envelope(
        &resources.plan,
        ENFORCEMENT_RSS_WATCHDOG_V1,
        timeout.as_secs_f64(),
    )
    .map_err(|error| error.to_string())?;
    if let Some(expected) = required_envelope {
        if expected != resource_envelope {
            return Err(format!(
                "live lexical-grammar resource envelope drift: expected {expected:?}, got {resource_envelope:?}"
            ));
        }
    }

    let mut rows = prepared.static_rows;
    for case in prepared.process_cases {
        let output = resources
            .run_external_transcript(
                &staged.path,
                ["--z3-mode", "--quiet", "-in"],
                &case.input,
                timeout,
                &format!("SMT-LIB lexical/grammar conformance: {}", case.id),
            )
            .map_err(|error| error.to_string())?;
        rows.push(process_case_result(&case, output));
    }
    let post_sha = sha256_file(&staged.path, "staged AY after lexical-grammar run")?;
    if post_sha != expected_ay_sha256 {
        return Err("authenticated AY staging bytes changed during grammar replay".to_string());
    }
    rows.sort_by(|left, right| left.id.cmp(&right.id));
    let cases = case_counts_from_rows(&rows)?;
    let result = overall_validator_result(&rows);
    Ok(Execution {
        ay_sha256: expected_ay_sha256.to_string(),
        resource_envelope,
        result,
        cases,
        case_results: rows,
    })
}

fn prepare_campaign(productions: &[LanguageGrammarProduction]) -> Result<PreparedCampaign, String> {
    let actual = productions
        .iter()
        .map(|production| production.name.as_str())
        .collect::<Vec<_>>();
    if actual != PRODUCTION_NAMES {
        return Err(format!(
            "authenticated grammar production order drift: expected {PRODUCTION_NAMES:?}, got {actual:?}"
        ));
    }

    let mut static_rows = Vec::new();
    let mut process_cases = Vec::new();
    for (index, production) in productions.iter().enumerate() {
        let row_prefix = format!("{DIMENSION_ID}.{}", production.name);
        let positive = positive_case(production, index)?;
        let positive_id = positive.id.clone();
        process_cases.push(positive);

        let negative_id = format!("{row_prefix}.negative");
        if index < RESPONSE_PRODUCTION_START {
            process_cases.push(ProcessCase {
                id: negative_id.clone(),
                input: grounded_script(
                    production,
                    &negative_id,
                    &negative_input(&production.name)?,
                ),
                expectation: ProcessExpectation::PositionedRecovery,
                obligation: format!(
                    "malformed {} input is rejected at its source command and recovery executes the next command",
                    production.name
                ),
            });
        } else {
            let kind = response_kind(&production.name)?;
            let invalid = b")";
            let rejected = !response_matches(kind, invalid);
            static_rows.push(ValidatorCase {
                id: negative_id.clone(),
                input_sha256: sha256_bytes(&grounded_bytes(production, &negative_id, invalid)),
                expected: format!(
                    "closed {kind:?} response recognizer rejects malformed response bytes"
                ),
                observed: format!("malformed_response_rejected={rejected}"),
                stdout: None,
                stderr: None,
                exit_code: None,
                process: None,
                outcome: if rejected {
                    ValidatorCaseOutcome::Pass
                } else {
                    ValidatorCaseOutcome::Fail
                },
            });
        }

        let source_id = format!("{row_prefix}.source");
        let witness_catalog = format!("{positive_id}\n{negative_id}\n");
        static_rows.push(ValidatorCase {
            id: source_id.clone(),
            input_sha256: sha256_bytes(&grounded_bytes(
                production,
                &source_id,
                production.production.as_bytes(),
            )),
            expected: format!(
                "authenticated {} production `{}` is owned by positive and negative witnesses",
                production.macro_name, production.name
            ),
            observed: format!(
                "path={}; git_blob={}; content_sha256={}; production_sha256={}; witness_catalog_sha256={}",
                production.path,
                production.git_blob,
                production.content_sha256,
                production.production_sha256,
                sha256_bytes(witness_catalog.as_bytes())
            ),
            stdout: None,
            stderr: None,
            exit_code: None,
            process: None,
            outcome: ValidatorCaseOutcome::Pass,
        });
    }
    static_rows.sort_by(|left, right| left.id.cmp(&right.id));
    process_cases.sort_by(|left, right| left.id.cmp(&right.id));
    for pair in process_cases.windows(2) {
        if pair[0].id >= pair[1].id {
            return Err("generated lexical/grammar witness IDs are not unique".to_string());
        }
    }
    if static_rows.len() + process_cases.len() != DETAILED_CASE_COUNT {
        return Err(format!(
            "closed lexical/grammar case count drift: static={} process={} total={}",
            static_rows.len(),
            process_cases.len(),
            static_rows.len() + process_cases.len()
        ));
    }
    Ok(PreparedCampaign {
        static_rows,
        process_cases,
    })
}

fn positive_case(
    production: &LanguageGrammarProduction,
    index: usize,
) -> Result<ProcessCase, String> {
    let id = format!("{DIMENSION_ID}.{}.positive", production.name);
    if index < RESPONSE_PRODUCTION_START {
        let body = format!(
            "{}\n(echo \"{SUCCESS_MARKER}\")\n",
            positive_input(&production.name)?
        );
        return Ok(ProcessCase {
            id: id.clone(),
            input: grounded_script(production, &id, &body),
            expectation: ProcessExpectation::ExactSuccess,
            obligation: format!(
                "authenticated {} production accepts its well-formed embedded witness",
                production.name
            ),
        });
    }
    let kind = response_kind(&production.name)?;
    Ok(ProcessCase {
        id: id.clone(),
        input: grounded_script(production, &id, response_input(kind)),
        expectation: ProcessExpectation::Response(kind),
        obligation: format!(
            "authenticated {} response production is emitted by the subject",
            production.name
        ),
    })
}

fn positive_input(name: &str) -> Result<&'static str, String> {
    match name {
        "white_space_char" => Ok(" \t\r\n; whitespace witness\r"),
        "printable_char" => Ok("(set-info :printable \" ~é\")"),
        "digit" => Ok("(assert (= 0 0))(assert (= 987 987))"),
        "letter" => Ok("(declare-const Az Bool)"),
        "numeral" => Ok("(assert (= 0 0))(assert (= 12345 12345))"),
        "decimal" => Ok("(assert (= 0.0 0.0))(assert (= 12.003 12.003))"),
        "hexadecimal" => Ok("(assert (= #x0 #x0))(assert (= #xAf #xAf))"),
        "binary" => Ok("(assert (= #b0 #b0))(assert (= #b0101 #b0101))"),
        "string" => Ok("(set-info :string \"line one\nsaid \"\"hi\"\"\")"),
        "simple_symbol" => Ok("(declare-const ~!@$%^&*_+=<>.?/-a0 Bool)"),
        "symbol" => Ok("(declare-const |two words é| Bool)"),
        "keyword" => Ok("(set-info :custom-key true)"),
        "spec_constant" => Ok("(set-info :constants (0 1.0 #xA #b1 \"s\"))"),
        "s_expr" => Ok("(set-info :tree (node 1 :key \"value\" ()))"),
        "index" => Ok("(declare-const b (_ BitVec 8))(set-info :symbolic-index (_ f idx))"),
        "identifier" => Ok("(declare-const b (_ BitVec 8))"),
        "sort" => Ok("(declare-const b Bool)(declare-const v (_ BitVec 8))(declare-const a (Array Bool Bool))"),
        "attribute_value" => Ok("(set-info :a 1)(set-info :b sym)(set-info :c (x))"),
        "attribute" => Ok("(set-info :flag)(set-info :value 1)"),
        "qual_identifier" => Ok("(declare-const c Bool)(assert (= (as c Bool) c))"),
        "var_binding" => Ok("(assert (let ((x true)) x))"),
        "sorted_var" => Ok("(assert (forall ((x Bool)) (= x x)))"),
        "symbol_" => Ok(MATCH_WITNESS),
        "pattern" => Ok(MATCH_WITNESS),
        "match_case" => Ok(MATCH_WITNESS),
        "term" => Ok("(declare-const a (Array Bool Bool))(assert (= a (lambda ((x Bool)) x)))(assert (let ((x true)) (forall ((y Bool)) (exists ((z Bool)) (and x y z)))))(assert (! true :named annotated))"),
        _ => Err(format!("no positive input witness for {name}")),
    }
}

const MATCH_WITNESS: &str = "(declare-datatype Opt ((none) (some (value Bool))))\
                              (declare-const o Opt)\
                              (assert (= (match o ((none false) ((some x) x))) true))";

fn negative_input(name: &str) -> Result<String, String> {
    let malformed = match name {
        "white_space_char" => "(\u{000b}echo \"bad\")",
        "printable_char" => "(echo \"bad\u{000b}\")",
        "digit" | "numeral" => "(assert (= 00 0))",
        "letter" | "simple_symbol" => "(declare-const é Bool)",
        "decimal" => "(assert (= 01.0 0.0))",
        "hexadecimal" => "(assert (= #xG #x0))",
        "binary" => "(assert (= #b2 #b0))",
        "string" => "(echo \"bad\u{000b}\")",
        "symbol" => "(declare-const |bad\\symbol| Bool)",
        "keyword" => "(set-info :1bad true)",
        "spec_constant" => "(assert :bad)",
        "s_expr" => "(set-info :x (a) extra)",
        "index" | "identifier" => "(declare-const x (_ BitVec))",
        "sort" => "(declare-const x ())",
        "attribute_value" => "(set-info :x :nested)",
        "attribute" => "(set-info not-a-keyword true)",
        "qual_identifier" => "(assert ((as c) true))",
        "var_binding" => "(assert (let ((x)) true))",
        "sorted_var" => "(assert (forall ((x)) true))",
        "symbol_" => "(assert (match x (((C 1) true))))",
        "pattern" => "(assert (match x ((() true))))",
        "match_case" => "(assert (match x ((C))))",
        "term" => "(assert ())",
        _ => return Err(format!("no negative input witness for {name}")),
    };
    Ok(format!("\n  {malformed}\n(echo \"{RECOVERY_MARKER}\")\n"))
}

fn response_kind(name: &str) -> Result<ResponseKind, String> {
    match name {
        "error-behavior" => Ok(ResponseKind::ErrorBehavior),
        "reason-unknown" => Ok(ResponseKind::ReasonUnknown),
        "model_response" => Ok(ResponseKind::ModelResponse),
        "info_response" => Ok(ResponseKind::InfoResponse),
        "valuation_pair" => Ok(ResponseKind::ValuationPair),
        "t_valuation_pair" => Ok(ResponseKind::TruthValuationPair),
        "check_sat_response" => Ok(ResponseKind::CheckSat),
        "echo_response" => Ok(ResponseKind::Echo),
        "get_assertions_response" => Ok(ResponseKind::GetAssertions),
        "get_assignment_response" => Ok(ResponseKind::GetAssignment),
        "get_info_response" => Ok(ResponseKind::GetInfo),
        "get_model_response" => Ok(ResponseKind::GetModel),
        "get_option_response" => Ok(ResponseKind::GetOption),
        "get_proof_response" => Ok(ResponseKind::GetProof),
        "get_unsat_assump_response" => Ok(ResponseKind::GetUnsatAssumptions),
        "get_unsat_core_response" => Ok(ResponseKind::GetUnsatCore),
        "get_value_response" => Ok(ResponseKind::GetValue),
        "specific_success_response" => Ok(ResponseKind::SpecificSuccess),
        "general_response" => Ok(ResponseKind::General),
        _ => Err(format!("{name} is not a response production")),
    }
}

fn response_input(kind: ResponseKind) -> &'static str {
    match kind {
        ResponseKind::ErrorBehavior => "(get-info :error-behavior)\n",
        ResponseKind::ReasonUnknown => "(get-info :reason-unknown)\n",
        ResponseKind::ModelResponse | ResponseKind::GetModel => {
            "(set-option :produce-models true)\n(declare-const c Bool)\n(assert c)\n(check-sat)\n(get-model)\n"
        }
        ResponseKind::InfoResponse | ResponseKind::GetInfo => "(get-info :name)\n",
        ResponseKind::ValuationPair | ResponseKind::GetValue => {
            "(set-option :produce-models true)\n(declare-const c Bool)\n(assert c)\n(check-sat)\n(get-value (c))\n"
        }
        ResponseKind::TruthValuationPair | ResponseKind::GetAssignment => {
            "(set-option :produce-assignments true)\n(declare-const c Bool)\n(assert (! c :named named_c))\n(check-sat)\n(get-assignment)\n"
        }
        ResponseKind::CheckSat | ResponseKind::SpecificSuccess => "(check-sat)\n",
        ResponseKind::Echo => "(echo \"AY_ECHO_RESPONSE\")\n",
        ResponseKind::GetAssertions => {
            "(set-option :interactive-mode true)\n(assert true)\n(get-assertions)\n"
        }
        ResponseKind::GetOption => "(get-option :print-success)\n",
        ResponseKind::GetProof => {
            "(set-option :produce-proofs true)\n(assert false)\n(check-sat)\n(get-proof)\n"
        }
        ResponseKind::GetUnsatAssumptions => {
            "(set-option :produce-unsat-assumptions true)\n(declare-const a Bool)\n(check-sat-assuming (a (not a)))\n(get-unsat-assumptions)\n"
        }
        ResponseKind::GetUnsatCore => {
            "(set-option :produce-unsat-cores true)\n(assert (! false :named core_a))\n(check-sat)\n(get-unsat-core)\n"
        }
        ResponseKind::General => "(set-option :print-success true)\n",
    }
}

fn grounded_script(production: &LanguageGrammarProduction, id: &str, body: &str) -> Vec<u8> {
    let mut bytes = body.as_bytes().to_vec();
    if !bytes.ends_with(b"\n") {
        bytes.push(b'\n');
    }
    bytes.extend_from_slice(
        format!(
            "; source={}\n; blob={}\n; content-sha256={}\n; production-sha256={}\n; case={}\n",
            production.path,
            production.git_blob,
            production.content_sha256,
            production.production_sha256,
            id
        )
        .as_bytes(),
    );
    bytes
}

fn grounded_bytes(production: &LanguageGrammarProduction, id: &str, value: &[u8]) -> Vec<u8> {
    let mut bytes = format!(
        "{}\n{}\n{}\n{}\n{}\n",
        production.path,
        production.git_blob,
        production.content_sha256,
        production.production_sha256,
        id
    )
    .into_bytes();
    bytes.extend_from_slice(value);
    bytes
}

fn process_case_result(case: &ProcessCase, output: GuardedTranscriptOutput) -> ValidatorCase {
    match case.expectation {
        ProcessExpectation::ExactSuccess => transcript_case(
            &case.id,
            &case.input,
            SUCCESS_STDOUT,
            output,
            &case.obligation,
        ),
        ProcessExpectation::PositionedRecovery => recovery_case(case, output),
        ProcessExpectation::Response(kind) => response_case(case, kind, output),
    }
}

fn recovery_case(case: &ProcessCase, output: GuardedTranscriptOutput) -> ValidatorCase {
    observed_case(case, output, |exit_code, stdout, stderr| {
        exit_code == Some(1) && stderr.is_empty() && positioned_recovery_matches(stdout)
    })
}

fn response_case(
    case: &ProcessCase,
    kind: ResponseKind,
    output: GuardedTranscriptOutput,
) -> ValidatorCase {
    observed_case(case, output, |exit_code, stdout, stderr| {
        exit_code == Some(0) && stderr.is_empty() && response_matches(kind, stdout.as_bytes())
    })
}

fn observed_case(
    case: &ProcessCase,
    output: GuardedTranscriptOutput,
    matches: impl FnOnce(Option<i32>, &str, &str) -> bool,
) -> ValidatorCase {
    let stdout_utf8 = String::from_utf8(output.stdout);
    let stderr_utf8 = String::from_utf8(output.stderr);
    let exit_code = output.status.and_then(|status| status.code());
    let (stdout, stdout_valid) = match stdout_utf8 {
        Ok(value) => (value, true),
        Err(error) => (
            String::from_utf8_lossy(error.as_bytes()).into_owned(),
            false,
        ),
    };
    let (stderr, stderr_valid) = match stderr_utf8 {
        Ok(value) => (value, true),
        Err(error) => (
            String::from_utf8_lossy(error.as_bytes()).into_owned(),
            false,
        ),
    };
    let semantic_match = stdout_valid && stderr_valid && matches(exit_code, &stdout, &stderr);
    let outcome = if output.memout {
        ValidatorCaseOutcome::Memout
    } else if output.timed_out {
        ValidatorCaseOutcome::Timeout
    } else if !output.stdin_complete
        || output.stdout_truncated
        || output.stderr_truncated
        || !stdout_valid
        || !stderr_valid
    {
        ValidatorCaseOutcome::Fail
    } else if semantic_match {
        ValidatorCaseOutcome::Pass
    } else if !matches!(exit_code, Some(0 | 1)) {
        ValidatorCaseOutcome::Crash
    } else {
        ValidatorCaseOutcome::Fail
    };
    ValidatorCase {
        id: case.id.clone(),
        input_sha256: sha256_bytes(&case.input),
        expected: case.expected(),
        observed: format!(
            "status={exit_code:?}; timeout={}; memout={}; stdin_complete={}; stdout_truncated={}; stderr_truncated={}; semantic_match={semantic_match}; stderr_empty={}",
            output.timed_out,
            output.memout,
            output.stdin_complete,
            output.stdout_truncated,
            output.stderr_truncated,
            stderr.is_empty()
        ),
        stdout: Some(stdout),
        stderr: Some(stderr),
        exit_code,
        process: Some(ProcessObservation {
            stdin_complete: output.stdin_complete,
            timed_out: output.timed_out,
            memout: output.memout,
            stdout_truncated: output.stdout_truncated,
            stderr_truncated: output.stderr_truncated,
        }),
        outcome,
    }
}

fn positioned_recovery_matches(stdout: &str) -> bool {
    let Some((error_line, remainder)) = stdout.split_once('\n') else {
        return false;
    };
    if remainder != format!("{RECOVERY_MARKER}\n") {
        return false;
    }
    let Ok(error) = ay_frontend::sexp::parse_sexp(error_line) else {
        return false;
    };
    let Some(items) = error.as_list() else {
        return false;
    };
    matches!(items, [head, SExpr::String(message)] if head.is_symbol("error") && message.starts_with("line 2 column 3: "))
}

fn response_matches(kind: ResponseKind, bytes: &[u8]) -> bool {
    let Ok(stdout) = std::str::from_utf8(bytes) else {
        return false;
    };
    if kind == ResponseKind::Echo {
        return stdout == "AY_ECHO_RESPONSE\n";
    }
    let Ok(rows) = ay_frontend::sexp::parse_sexps(stdout) else {
        return false;
    };
    let Some(last) = rows.last() else {
        return false;
    };
    match kind {
        ResponseKind::ErrorBehavior => keyword_pair(last, ":error-behavior", |value| {
            value.is_symbol("immediate-exit") || value.is_symbol("continued-execution")
        }),
        ResponseKind::ReasonUnknown => keyword_pair(last, ":reason-unknown", |_| true),
        ResponseKind::ModelResponse | ResponseKind::GetModel => {
            has_verdict_prefix(&rows) && model_response_list(last)
        }
        ResponseKind::InfoResponse | ResponseKind::GetInfo => info_response(last),
        ResponseKind::ValuationPair | ResponseKind::GetValue => {
            has_verdict_prefix(&rows) && pair_list(last, false)
        }
        ResponseKind::TruthValuationPair | ResponseKind::GetAssignment => {
            has_verdict_prefix(&rows) && pair_list(last, true)
        }
        ResponseKind::CheckSat | ResponseKind::SpecificSuccess => {
            rows.len() == 1 && check_sat_response(last)
        }
        ResponseKind::GetAssertions => list_response(last),
        ResponseKind::GetOption => attribute_value(last),
        ResponseKind::GetProof => has_verdict_prefix(&rows) && rows.len() >= 2,
        ResponseKind::GetUnsatAssumptions | ResponseKind::GetUnsatCore => {
            has_verdict_prefix(&rows) && list_response(last)
        }
        ResponseKind::General => {
            rows.len() == 1
                && (last.is_symbol("success")
                    || last.is_symbol("unsupported")
                    || check_sat_response(last)
                    || is_error_response(last))
        }
        ResponseKind::Echo => unreachable!("echo handled before S-expression parsing"),
    }
}

fn keyword_pair(value: &SExpr, keyword: &str, predicate: impl FnOnce(&SExpr) -> bool) -> bool {
    matches!(value.as_list(), Some([SExpr::Keyword(actual), item]) if actual == keyword && predicate(item))
}

fn info_response(value: &SExpr) -> bool {
    matches!(value.as_list(), Some([SExpr::Keyword(_), _]))
}

fn model_response_list(value: &SExpr) -> bool {
    value.as_list().is_some_and(|items| {
        items.iter().all(|item| {
            item.as_list().is_some_and(|definition| {
                matches!(definition.first(), Some(head) if head.is_symbol("define-fun") || head.is_symbol("define-fun-rec") || head.is_symbol("define-funs-rec"))
            })
        })
    })
}

fn pair_list(value: &SExpr, truth_value: bool) -> bool {
    value.as_list().is_some_and(|items| {
        !items.is_empty()
            && items.iter().all(|item| {
                item.as_list().is_some_and(|pair| {
                    if pair.len() != 2 {
                        return false;
                    }
                    !truth_value
                        || pair[1].is_symbol("true")
                        || pair[1].is_symbol("false")
                        || matches!(pair[1], SExpr::True | SExpr::False)
                })
            })
    })
}

fn list_response(value: &SExpr) -> bool {
    value.as_list().is_some()
}

fn attribute_value(value: &SExpr) -> bool {
    !matches!(value, SExpr::Keyword(_))
}

fn check_sat_response(value: &SExpr) -> bool {
    value.is_symbol("sat") || value.is_symbol("unsat") || value.is_symbol("unknown")
}

fn has_verdict_prefix(rows: &[SExpr]) -> bool {
    rows.first().is_some_and(check_sat_response)
}

fn is_error_response(value: &SExpr) -> bool {
    matches!(value.as_list(), Some([head, SExpr::String(_)]) if head.is_symbol("error"))
}

fn process_completed(process: &ProcessObservation) -> bool {
    process.stdin_complete
        && !process.timed_out
        && !process.memout
        && !process.stdout_truncated
        && !process.stderr_truncated
}

fn validate_recorded_shape(
    receipt: &ValidatorReceipt,
    prepared: &PreparedCampaign,
) -> Result<(), String> {
    let mut expected = prepared
        .static_rows
        .iter()
        .map(|row| {
            (
                row.id.clone(),
                row.input_sha256.clone(),
                row.expected.clone(),
                None,
            )
        })
        .collect::<Vec<_>>();
    expected.extend(prepared.process_cases.iter().map(|case| {
        (
            case.id.clone(),
            sha256_bytes(&case.input),
            case.expected(),
            Some(case.expectation),
        )
    }));
    expected.sort_by(|left, right| left.0.cmp(&right.0));
    if receipt.case_results.len() != expected.len() {
        return Err(format!(
            "{VALIDATOR_ID} detailed case inventory drift: expected {}, got {}",
            expected.len(),
            receipt.case_results.len()
        ));
    }
    for (row, (id, input_sha256, expected_text, expectation)) in
        receipt.case_results.iter().zip(expected)
    {
        if row.id != id || row.input_sha256 != input_sha256 || row.expected != expected_text {
            return Err(format!(
                "{VALIDATOR_ID} case identity, input, or obligation drift at {id}"
            ));
        }
        if expectation.is_some() != row.process.is_some() {
            return Err(format!("{id} has the wrong process-observation shape"));
        }
        if row.outcome != ValidatorCaseOutcome::Pass {
            continue;
        }
        match expectation {
            None => {
                if row.stdout.is_some()
                    || row.stderr.is_some()
                    || row.exit_code.is_some()
                    || row.process.is_some()
                {
                    return Err(format!("{id} static row forged process data"));
                }
            }
            Some(ProcessExpectation::ExactSuccess) => {
                if row.exit_code != Some(0)
                    || row.stdout.as_deref() != Some(SUCCESS_STDOUT)
                    || row.stderr.as_deref() != Some("")
                    || !row.process.as_ref().is_some_and(process_completed)
                {
                    return Err(format!(
                        "{id} claims pass without its exact success transcript"
                    ));
                }
            }
            Some(ProcessExpectation::PositionedRecovery) => {
                if row.exit_code != Some(1)
                    || !row
                        .stdout
                        .as_deref()
                        .is_some_and(positioned_recovery_matches)
                    || row.stderr.as_deref() != Some("")
                    || !row.process.as_ref().is_some_and(process_completed)
                {
                    return Err(format!("{id} claims pass without positioned recovery"));
                }
            }
            Some(ProcessExpectation::Response(kind)) => {
                if row.exit_code != Some(0)
                    || !row
                        .stdout
                        .as_deref()
                        .is_some_and(|stdout| response_matches(kind, stdout.as_bytes()))
                    || row.stderr.as_deref() != Some("")
                    || !row.process.as_ref().is_some_and(process_completed)
                {
                    return Err(format!("{id} claims pass without its response grammar"));
                }
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn production_catalog_is_closed_and_duplicate_free() {
        assert_eq!(PRODUCTION_NAMES.len(), 45);
        let names = PRODUCTION_NAMES.into_iter().collect::<BTreeSet<_>>();
        assert_eq!(names.len(), PRODUCTION_NAMES.len());
        assert_eq!(RESPONSE_PRODUCTION_START, 26);
    }

    #[test]
    fn positioned_recovery_requires_exact_location_and_sentinel() {
        assert!(positioned_recovery_matches(
            "(error \"line 2 column 3: invalid token\")\nAY_GRAMMAR_RECOVERED\n"
        ));
        assert!(!positioned_recovery_matches(
            "(error \"line 2 column 4: invalid token\")\nAY_GRAMMAR_RECOVERED\n"
        ));
    }

    #[test]
    fn every_response_recognizer_rejects_malformed_bytes() {
        for name in &PRODUCTION_NAMES[RESPONSE_PRODUCTION_START..] {
            let kind = response_kind(name).expect("response catalog entry");
            assert!(!response_matches(kind, b")"), "{name}");
        }
    }
}
