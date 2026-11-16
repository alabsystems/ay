// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Finite, named semantic obligations against the current upstream C headers.
//! A completed family is evidence for the listed input/state sequence, not a
//! proof over every argument or lifetime. Unknown declarations stay visible.

use super::*;

mod arrays_datatypes;
mod bitvector;
mod fixedpoint;
mod floating_point;
mod optimize;
mod parsing_substitution;
mod quantifiers;
mod sequences;

const CONTRACT_VERSION: &str = "ay-current-abi-semantic-contracts/v6";
const NEGATIVE_MODE: &str = "--ay-abi-invert-last-check";
const INVALID_MODE: &str = "--ay-abi-invalid-mode";
const MODE_REFUSAL: &str = "ABI_CONTRACT_MODE_REFUSED\n";

#[derive(Clone, Copy, Debug, Deserialize, Serialize, Eq, PartialEq, Ord, PartialOrd)]
#[serde(rename_all = "kebab-case")]
pub(super) enum Aspect {
    Context,
    Lifetime,
    State,
    Errors,
    Output,
}

const ASPECTS: [Aspect; 5] = [
    Aspect::Context,
    Aspect::Lifetime,
    Aspect::State,
    Aspect::Errors,
    Aspect::Output,
];

#[derive(Clone, Debug, Deserialize, Serialize, Eq, PartialEq)]
#[serde(deny_unknown_fields)]
pub(super) struct Obligation {
    pub(super) id: String,
    pub(super) aspect: Aspect,
    pub(super) statement: String,
    pub(super) family: String,
    pub(super) check: String,
    pub(super) passed: bool,
}

#[derive(Clone, Debug, Deserialize, Serialize, Eq, PartialEq)]
#[serde(deny_unknown_fields)]
pub(super) struct FunctionContract {
    pub(super) upstream_declaration: String,
    pub(super) obligations: Vec<Obligation>,
    pub(super) unregistered_aspects: Vec<Aspect>,
    pub(super) registered_obligations_passed: bool,
    pub(super) remaining_scope: String,
}

#[derive(Clone, Debug, Deserialize, Serialize, Eq, PartialEq)]
#[serde(deny_unknown_fields)]
pub(super) struct FamilyResult {
    pub(super) id: String,
    pub(super) source_sha256: String,
    pub(super) check_ids: Vec<String>,
    pub(super) negative_check_id: String,
    pub(super) reference_source_sha256: String,
    pub(super) reference_negative_control_passed: bool,
    pub(super) reference_mode_refusal_passed: bool,
    pub(super) reference_passed: bool,
    pub(super) ay_passed: bool,
    pub(super) passed: bool,
}

#[derive(Clone, Debug, Deserialize, Serialize, Eq, PartialEq)]
#[serde(deny_unknown_fields)]
pub(super) struct Execution {
    pub(super) contract_version: String,
    pub(super) inventory_sha256: String,
    pub(super) families: Vec<FamilyResult>,
    pub(super) registered_functions: usize,
    pub(super) passed_functions: usize,
    pub(super) uncovered_functions: usize,
    pub(super) passed: bool,
}

struct Family {
    id: &'static str,
    source: &'static str,
    checks: &'static [&'static str],
}

const FAMILIES: &[Family] = &[
    Family {
        id: "contract-context",
        source: concat!(
            include_str!("contracts/common.h"),
            include_str!("contracts/context.c")
        ),
        checks: &[
            "context.created-after-config-deletion",
            "context.distinct-sorts",
            "context.symbol-roundtrip",
            "context.ast-sort-and-kind",
            "context.retained-ast-survives-churn",
            "context.destination-created",
            "context.translation-created",
            "context.translation-survives-source-destruction",
        ],
    },
    Family {
        id: "contract-solver",
        source: concat!(
            include_str!("contracts/common.h"),
            include_str!("contracts/solver.c")
        ),
        checks: &[
            "solver.context-created",
            "solver.fresh-state",
            "solver.independent-instances",
            "solver.push-isolated-contradiction",
            "solver.assertion-snapshot",
            "solver.pop-restores-scope",
            "solver.assumption-contradiction",
            "solver.assumption-core",
            "solver.assumptions-do-not-persist",
            "solver.reset-and-retained-snapshots",
        ],
    },
    Family {
        id: "contract-model",
        source: concat!(
            include_str!("contracts/common.h"),
            include_str!("contracts/model.c")
        ),
        checks: &[
            "model.context-created",
            "model.terms-and-solver",
            "model.initial-satisfiable",
            "model.eval-exact-integer",
            "model.constant-interpretation",
            "model.retained-after-unsat",
            "model.changed-solver-satisfiable",
            "model.independent-retained-models",
            "model.destination-created",
            "model.translation-created",
            "model.translation-survives-source-destruction",
        ],
    },
    Family {
        id: "contract-errors",
        source: concat!(
            include_str!("contracts/common.h"),
            include_str!("contracts/errors.c")
        ),
        checks: &[
            "errors.context-created",
            "errors.valid-setup",
            "errors.invalid-sort-reported",
            "errors.message-present",
            "errors.valid-call-recovers",
            "errors.explicit-error-state",
            "errors.explicit-error-clear",
        ],
    },
    Family {
        id: "contract-vector",
        source: concat!(
            include_str!("contracts/common.h"),
            include_str!("contracts/vector.c")
        ),
        checks: &[
            "vector.context-created",
            "vector.initially-empty",
            "vector.push-preserves-order",
            "vector.set-preserves-other-elements",
            "vector.shrink-preserves-prefix",
            "vector.destination-created",
            "vector.translation-created",
            "vector.translation-survives-source-destruction",
        ],
    },
];

struct Claim {
    family: &'static str,
    check: &'static str,
    aspect: Aspect,
    functions: &'static [&'static str],
    statement: &'static str,
}

// Every claim names a specific assertion in a complete paired execution.
// Shared assertions establish joint behavior; failures do not identify which
// function caused the discrepancy. Merely appearing in a C file grants none.
const CLAIMS: &[Claim] = &[
    Claim { family: "contract-context", check: "context.created-after-config-deletion", aspect: Aspect::Context, functions: &["Z3_mk_config", "Z3_set_param_value", "Z3_mk_context_rc", "Z3_del_config"], statement: "A model-enabled reference-counted context remains usable after its configuration is deleted." },
    Claim { family: "contract-context", check: "context.distinct-sorts", aspect: Aspect::Output, functions: &["Z3_mk_int_sort", "Z3_mk_bool_sort", "Z3_get_sort_kind", "Z3_is_eq_sort"], statement: "Int and Bool are valid, correctly classified, distinct sorts in the same context." },
    Claim { family: "contract-context", check: "context.symbol-roundtrip", aspect: Aspect::Output, functions: &["Z3_mk_string_symbol", "Z3_mk_int_symbol", "Z3_get_symbol_kind", "Z3_get_symbol_string", "Z3_get_symbol_int"], statement: "String symbol contract_x and integer symbol 17 preserve their kind and exact value." },
    Claim { family: "contract-context", check: "context.ast-sort-and-kind", aspect: Aspect::Output, functions: &["Z3_mk_const", "Z3_get_ast_kind", "Z3_get_sort"], statement: "An Int constant is an application AST with its declared Int sort." },
    Claim { family: "contract-context", check: "context.retained-ast-survives-churn", aspect: Aspect::Lifetime, functions: &["Z3_inc_ref", "Z3_dec_ref", "Z3_sort_to_ast", "Z3_get_ast_id", "Z3_get_ast_hash", "Z3_is_eq_ast", "Z3_ast_to_string"], statement: "A retained constant keeps its identity, hash, and printed name across 4096 retained/released numeral allocations; reconstructing it is hash-consed." },
    Claim { family: "contract-context", check: "context.translation-survives-source-destruction", aspect: Aspect::Context, functions: &["Z3_translate", "Z3_del_context"], statement: "A retained translated constant keeps its name and Int sort after the source context is destroyed." },
    Claim { family: "contract-solver", check: "solver.fresh-state", aspect: Aspect::State, functions: &["Z3_mk_solver", "Z3_solver_inc_ref", "Z3_solver_get_num_scopes"], statement: "Two retained fresh solvers start at scope zero." },
    Claim { family: "contract-solver", check: "solver.independent-instances", aspect: Aspect::State, functions: &["Z3_solver_assert", "Z3_solver_check"], statement: "Separate solvers in one context can assert p and not-p and both remain satisfiable." },
    Claim { family: "contract-solver", check: "solver.push-isolated-contradiction", aspect: Aspect::State, functions: &["Z3_solver_push", "Z3_solver_get_num_scopes"], statement: "Pushing a contradictory assertion affects only the selected solver and increments only its scope count." },
    Claim { family: "contract-solver", check: "solver.pop-restores-scope", aspect: Aspect::State, functions: &["Z3_solver_pop"], statement: "Popping one scope restores the solver's prior satisfiable assertions and scope count." },
    Claim { family: "contract-solver", check: "solver.assertion-snapshot", aspect: Aspect::Output, functions: &["Z3_solver_get_assertions", "Z3_ast_vector_get", "Z3_ast_vector_size"], statement: "The assertion snapshot contains exactly p then not-p at the contradictory scope." },
    Claim { family: "contract-solver", check: "solver.assumption-contradiction", aspect: Aspect::State, functions: &["Z3_solver_check_assumptions"], statement: "The temporary not-p assumption contradicts an asserted p." },
    Claim { family: "contract-solver", check: "solver.assumption-core", aspect: Aspect::Output, functions: &["Z3_solver_get_unsat_core"], statement: "The sole contradictory assumption is returned as the sole unsat-core member." },
    Claim { family: "contract-solver", check: "solver.assumptions-do-not-persist", aspect: Aspect::State, functions: &["Z3_solver_check_assumptions", "Z3_solver_check"], statement: "An unsatisfiable assumption check does not persist assumptions into a later ordinary check." },
    Claim { family: "contract-solver", check: "solver.reset-and-retained-snapshots", aspect: Aspect::Lifetime, functions: &["Z3_solver_reset", "Z3_ast_vector_inc_ref", "Z3_ast_vector_dec_ref"], statement: "Reset clears assertions and scopes; explicitly retained assertion/core vectors keep their prior contents." },
    Claim { family: "contract-model", check: "model.eval-exact-integer", aspect: Aspect::Output, functions: &["Z3_solver_get_model", "Z3_model_eval", "Z3_get_numeral_int", "Z3_mk_int", "Z3_mk_eq"], statement: "The model of x=7 evaluates x to the integer 7 without model completion." },
    Claim { family: "contract-model", check: "model.constant-interpretation", aspect: Aspect::Output, functions: &["Z3_model_get_const_interp", "Z3_model_has_interp", "Z3_model_get_num_consts", "Z3_model_get_const_decl", "Z3_get_app_decl", "Z3_to_app", "Z3_is_eq_func_decl"], statement: "The single declared model constant is x and its explicit interpretation is integer 7." },
    Claim { family: "contract-model", check: "model.retained-after-unsat", aspect: Aspect::Lifetime, functions: &["Z3_model_inc_ref", "Z3_model_dec_ref"], statement: "The explicitly retained x=7 model remains evaluable after a contradictory solver check." },
    Claim { family: "contract-model", check: "model.independent-retained-models", aspect: Aspect::State, functions: &["Z3_solver_get_model", "Z3_model_eval"], statement: "After reset and solving x=9, new and previously retained models still evaluate to 9 and 7 respectively." },
    Claim { family: "contract-model", check: "model.translation-survives-source-destruction", aspect: Aspect::Context, functions: &["Z3_model_translate", "Z3_translate"], statement: "A translated retained model evaluates its translated constant to 7 after destroying the source context." },
    Claim { family: "contract-errors", check: "errors.invalid-sort-reported", aspect: Aspect::Errors, functions: &["Z3_mk_not", "Z3_set_error_handler", "Z3_get_error_code"], statement: "Applying not to an Int reports the pinned Z3_EXCEPTION through the installed handler and error-code API; the erroneous return value is not consumed." },
    Claim { family: "contract-errors", check: "errors.message-present", aspect: Aspect::Errors, functions: &["Z3_get_error_msg"], statement: "The Z3_EXCEPTION diagnostic identifies a sort mismatch at argument #1 and the supplied Int sort; other diagnostic spelling is outside this obligation." },
    Claim { family: "contract-errors", check: "errors.valid-call-recovers", aspect: Aspect::Errors, functions: &["Z3_mk_not", "Z3_mk_true", "Z3_get_bool_value", "Z3_get_error_code"], statement: "A subsequent valid Boolean construction clears the error and exposes a true literal and Bool-typed negation." },
    Claim { family: "contract-errors", check: "errors.explicit-error-state", aspect: Aspect::Errors, functions: &["Z3_set_error", "Z3_get_error_code"], statement: "Explicitly setting INVALID_ARG is observable through get_error_code." },
    Claim { family: "contract-errors", check: "errors.explicit-error-clear", aspect: Aspect::Errors, functions: &["Z3_set_error", "Z3_get_error_code"], statement: "Explicitly setting OK clears a prior INVALID_ARG." },
    Claim { family: "contract-vector", check: "vector.initially-empty", aspect: Aspect::State, functions: &["Z3_mk_ast_vector", "Z3_ast_vector_inc_ref", "Z3_ast_vector_size"], statement: "A retained newly created AST vector is empty." },
    Claim { family: "contract-vector", check: "vector.push-preserves-order", aspect: Aspect::State, functions: &["Z3_ast_vector_push", "Z3_ast_vector_get"], statement: "Pushing integers 1 and 2 yields exactly those elements in insertion order." },
    Claim { family: "contract-vector", check: "vector.set-preserves-other-elements", aspect: Aspect::State, functions: &["Z3_ast_vector_set"], statement: "Setting element zero changes only that element and preserves vector length." },
    Claim { family: "contract-vector", check: "vector.shrink-preserves-prefix", aspect: Aspect::State, functions: &["Z3_ast_vector_resize"], statement: "Shrinking a two-element vector to one preserves its first element." },
    Claim { family: "contract-vector", check: "vector.translation-survives-source-destruction", aspect: Aspect::Context, functions: &["Z3_ast_vector_translate", "Z3_ast_vector_dec_ref"], statement: "The translated retained vector still contains integer 2 after source context destruction." },
];

fn families() -> impl Iterator<Item = &'static Family> {
    FAMILIES
        .iter()
        .chain(optimize::FAMILIES.iter())
        .chain(fixedpoint::FAMILIES.iter())
        .chain(bitvector::FAMILIES.iter())
        .chain(arrays_datatypes::FAMILIES.iter())
        .chain(sequences::FAMILIES.iter())
        .chain(quantifiers::FAMILIES.iter())
        .chain(floating_point::FAMILIES.iter())
        .chain(parsing_substitution::FAMILIES.iter())
}

fn claims() -> impl Iterator<Item = &'static Claim> {
    CLAIMS
        .iter()
        .chain(optimize::CLAIMS.iter())
        .chain(fixedpoint::CLAIMS.iter())
        .chain(bitvector::CLAIMS.iter())
        .chain(arrays_datatypes::CLAIMS.iter())
        .chain(sequences::CLAIMS.iter())
        .chain(quantifiers::CLAIMS.iter())
        .chain(floating_point::CLAIMS.iter())
        .chain(parsing_substitution::CLAIMS.iter())
}

pub(super) fn probe(id: &str) -> Option<StockCProbe> {
    families()
        .find(|family| family.id == id)
        .map(|family| StockCProbe {
            id: family.id,
            source: family.source.as_bytes(),
            expected_stdout_trailer: b"",
        })
}

pub(super) fn sources() -> impl Iterator<Item = (&'static str, &'static [u8])> {
    families().map(|family| (family.id, family.source.as_bytes()))
}

fn registered_names() -> BTreeSet<&'static str> {
    claims()
        .flat_map(|claim| claim.functions.iter().copied())
        .collect()
}

fn registry_digest() -> Result<String, String> {
    let rows = claims()
        .map(|claim| {
            serde_json::json!({
                "family": claim.family, "check": claim.check, "aspect": claim.aspect,
                "functions": claim.functions, "statement": claim.statement,
            })
        })
        .collect::<Vec<_>>();
    Ok(sha256_bytes(
        &serde_json::to_vec(&(CONTRACT_VERSION, rows)).map_err(|error| error.to_string())?,
    ))
}

fn expected_stdout(family: &Family) -> Vec<u8> {
    format!("{}\n", family.checks.join("\n")).into_bytes()
}

fn negative_check(family: &Family) -> Result<&'static str, String> {
    family.checks.last().copied().ok_or_else(|| {
        format!(
            "semantic family {} has no negative-control check",
            family.id
        )
    })
}

fn reference_source(family: &Family) -> Result<String, String> {
    let check = negative_check(family)?;
    Ok(render_reference_source(family.source, check))
}

fn render_reference_source(source: &str, check: &str) -> String {
    // A closed, source-bound dispatcher runs the original fixture unchanged
    // or inverts precisely its final real assertion. Both paths execute the
    // same freshly compiled binary in separate, independently guarded children.
    // The existing CHECK macro evaluates the selected condition exactly once.
    format!(
        "static const char *ay_abi_check_target = \"\";\n\
         #define AY_CONTRACT_NEGATIVE_CHECK ay_abi_check_target\n\
         #define main ay_abi_fixture_main\n{source}\n\
         #undef main\n\
         int main(int argc, char **argv) {{\n\
         if (argc == 1) ay_abi_check_target = \"\";\n\
         else if (argc == 2 && strcmp(argv[1], \"{NEGATIVE_MODE}\") == 0) ay_abi_check_target = \"{check}\";\n\
         else {{ fputs(\"ABI_CONTRACT_MODE_REFUSED\\n\", stderr); return 64; }}\n\
         return ay_abi_fixture_main();\n}}\n"
    )
}

/// The build worker verifies its actual input file against the maintained
/// source, including the reference-only dispatcher, before invoking Clang.
pub(super) fn build_source(id: &str, subject: &str) -> Result<Option<Vec<u8>>, String> {
    families()
        .find(|family| family.id == id)
        .map(|family| match subject {
            "z3" => reference_source(family).map(String::into_bytes),
            "ay" => Ok(family.source.as_bytes().to_vec()),
            _ => Err("unknown ABI subject".to_string()),
        })
        .transpose()
}

fn negative_run_passed(capture: &Capture, family: &Family) -> bool {
    let Ok(check) = negative_check(family) else {
        return false;
    };
    let prefix = family.checks[..family.checks.len() - 1].join("\n");
    let stdout = if prefix.is_empty() {
        String::new()
    } else {
        format!("{prefix}\n")
    };
    capture.exit_code == Some(2)
        && !capture.timed_out
        && !capture.memout
        && capture.stdin_complete
        && !capture.stdout_truncated
        && !capture.stderr_truncated
        && capture.stdout == stdout
        && capture.stderr == format!("ABI_CONTRACT_FAILED:{check}\n")
}

fn mode_refusal_passed(capture: &Capture) -> bool {
    capture.exit_code == Some(64)
        && !capture.timed_out
        && !capture.memout
        && capture.stdin_complete
        && !capture.stdout_truncated
        && !capture.stderr_truncated
        && capture.stdout.is_empty()
        && capture.stderr == MODE_REFUSAL
}

/// Only the exact registered control protocols can justify a nonzero exit.
/// Unknown ids still receive the ordinary zero-exit capture assessment.
pub(super) fn negative_capture_passed(capture: &Capture) -> Option<bool> {
    for family in families() {
        if capture.id == format!("z3.{}.negative-run", family.id) {
            return Some(negative_run_passed(capture, family));
        }
        if capture.id == format!("z3.{}.invalid-mode", family.id) {
            return Some(mode_refusal_passed(capture));
        }
    }
    None
}

fn negative_control_passed(captures: &[Capture], family: &Family) -> bool {
    captures
        .iter()
        .find(|capture| capture.id == format!("z3.{}.build", family.id))
        .is_some_and(|capture| capture.exact_stdout(b""))
        && captures
            .iter()
            .find(|capture| capture.id == format!("z3.{}.negative-run", family.id))
            .is_some_and(|capture| negative_run_passed(capture, family))
}

fn family_passed(captures: &[Capture], subject: &str, family: &Family) -> bool {
    let find = |suffix| {
        captures
            .iter()
            .find(|capture| capture.id == format!("{subject}.{}.{}", family.id, suffix))
    };
    find("build").is_some_and(|capture| capture.exact_stdout(b""))
        && find("run").is_some_and(|capture| capture.exact_stdout(&expected_stdout(family)))
}

pub(super) fn compiler() -> &'static Path {
    #[cfg(target_os = "macos")]
    {
        Path::new("/usr/bin/clang")
    }
    #[cfg(not(target_os = "macos"))]
    {
        Path::new("/usr/bin/cc")
    }
}

fn validate_catalog() -> Result<(), String> {
    let mut family_ids = BTreeSet::new();
    for family in families() {
        if !family_ids.insert(family.id)
            || family.checks.is_empty()
            || family.checks.iter().any(|check| {
                check.is_empty()
                    || !check.bytes().all(|byte| {
                        byte.is_ascii_alphanumeric() || matches!(byte, b'.' | b'-' | b'_')
                    })
            })
            || family.checks.iter().copied().collect::<BTreeSet<_>>().len() != family.checks.len()
        {
            return Err("duplicate or empty ABI semantic family/check inventory".to_string());
        }
    }
    let mut obligation_ids = BTreeSet::new();
    for claim in claims() {
        if claim.functions.is_empty()
            || claim.statement.is_empty()
            || !families()
                .any(|family| family.id == claim.family && family.checks.contains(&claim.check))
        {
            return Err("ABI semantic obligation lacks an executable check".to_string());
        }
        for function in claim.functions {
            if !obligation_ids.insert((*function, claim.check)) {
                return Err("duplicate ABI function semantic obligation".to_string());
            }
        }
    }
    Ok(())
}

pub(super) fn execute(
    resources: &PlannedResources,
    evaluator: &Path,
    directory: &Path,
    ay: &Path,
    z3: &Path,
    names: &[String],
    captures: &mut Vec<Capture>,
    timeout: Duration,
) -> Result<Execution, String> {
    validate_catalog()?;
    captures.push(capture(
        resources,
        compiler(),
        &["--version".into()],
        b"",
        "semantic.compiler",
        timeout,
    )?);
    for family in families() {
        let source_path = directory.join(format!("{}.c", family.id));
        let reference = reference_source(family)?;
        for (subject, library) in [("z3", z3), ("ay", ay)] {
            let source = if subject == "z3" {
                reference.as_str()
            } else {
                family.source
            };
            fs::write(&source_path, source)
                .map_err(|error| format!("write semantic contract {}: {error}", family.id))?;
            let id = format!("{subject}.{}.build", family.id);
            let build = capture(
                resources,
                evaluator,
                &[
                    "smtlib-conformance".into(),
                    "current-abi-build-child".into(),
                    directory.as_os_str().to_owned(),
                    family.id.into(),
                    subject.into(),
                    library.as_os_str().to_owned(),
                ],
                b"",
                &id,
                timeout,
            )?;
            let built = build.exact_stdout(b"");
            captures.push(build);
            if !built {
                continue;
            }
            let binary = directory.join(format!("{}-{subject}", family.id));
            let binary_sha = sha256_file(&binary, "fresh ABI fixture binary")?;
            let mut modes = vec![(
                format!("{subject}.{}.run", family.id),
                Vec::<OsString>::new(),
            )];
            if subject == "z3" {
                modes.push((
                    format!("z3.{}.negative-run", family.id),
                    vec![NEGATIVE_MODE.into()],
                ));
                modes.push((
                    format!("z3.{}.invalid-mode", family.id),
                    vec![INVALID_MODE.into()],
                ));
            }
            for (id, args) in modes {
                if sha256_file(&binary, "ABI fixture before execution")? != binary_sha {
                    return Err(
                        "compiled ABI fixture changed between controlled executions".to_string()
                    );
                }
                captures.push(capture(resources, &binary, &args, b"", &id, timeout)?);
                if sha256_file(&binary, "ABI fixture after execution")? != binary_sha {
                    return Err(
                        "compiled ABI fixture changed during controlled execution".to_string()
                    );
                }
            }
        }
        fs::write(&source_path, family.source)
            .map_err(|error| format!("restore semantic contract {}: {error}", family.id))?;
    }
    summarize(names, captures)
}

pub(super) fn summarize(names: &[String], captures: &[Capture]) -> Result<Execution, String> {
    validate_catalog()?;
    if captures
        .iter()
        .map(|capture| &capture.id)
        .collect::<BTreeSet<_>>()
        .len()
        != captures.len()
    {
        return Err("duplicate ABI capture id".to_string());
    }
    let registered = registered_names();
    for name in &registered {
        if !names.iter().any(|candidate| candidate.as_str() == *name) {
            return Err(format!(
                "semantic contract names function absent from current upstream inventory: {name}"
            ));
        }
    }
    let compiler_ready = captures
        .iter()
        .find(|capture| capture.id == "semantic.compiler")
        .is_some_and(|capture| {
            capture.process_completed()
                && !capture.stdout.trim().is_empty()
                && capture.stderr.is_empty()
        });
    let families = families()
        .map(|family| {
            let reference_passed = family_passed(captures, "z3", family);
            let ay_passed = family_passed(captures, "ay", family);
            let reference_negative_control_passed = negative_control_passed(captures, family);
            let reference_mode_refusal_passed = captures
                .iter()
                .find(|capture| capture.id == format!("z3.{}.invalid-mode", family.id))
                .is_some_and(mode_refusal_passed);
            Ok(FamilyResult {
                id: family.id.to_string(),
                source_sha256: sha256_bytes(family.source.as_bytes()),
                check_ids: family.checks.iter().map(|id| (*id).to_string()).collect(),
                negative_check_id: negative_check(family)?.to_string(),
                reference_source_sha256: sha256_bytes(reference_source(family)?.as_bytes()),
                reference_mode_refusal_passed,
                reference_negative_control_passed,
                reference_passed,
                ay_passed,
                passed: reference_passed
                    && ay_passed
                    && reference_negative_control_passed
                    && reference_mode_refusal_passed
                    && compiler_ready,
            })
        })
        .collect::<Result<Vec<_>, String>>()?;
    let mut report = Execution {
        contract_version: CONTRACT_VERSION.to_string(),
        inventory_sha256: registry_digest()?,
        registered_functions: registered.len(),
        passed_functions: 0,
        uncovered_functions: names.len() - registered.len(),
        passed: families.iter().all(|family| family.passed),
        families,
    };
    report.passed_functions = names
        .iter()
        .filter(|name| function_contract(name, &report).registered_obligations_passed)
        .count();
    Ok(report)
}

pub(super) fn function_contract(name: &str, execution: &Execution) -> FunctionContract {
    let obligations = claims()
        .filter(|claim| claim.functions.contains(&name))
        .map(|claim| Obligation {
            id: format!("{name}.{}", claim.check),
            aspect: claim.aspect,
            statement: claim.statement.to_string(),
            family: claim.family.to_string(),
            check: claim.check.to_string(),
            passed: execution
                .families
                .iter()
                .find(|family| family.id == claim.family)
                .is_some_and(|family| family.passed),
        })
        .collect::<Vec<_>>();
    let unregistered_aspects = ASPECTS
        .iter()
        .filter(|aspect| {
            !obligations
                .iter()
                .any(|obligation| obligation.aspect == **aspect)
        })
        .copied()
        .collect();
    FunctionContract {
        upstream_declaration: format!("Z3 5.3.3 src/api public declaration {name}"),
        registered_obligations_passed: !obligations.is_empty()
            && obligations.iter().all(|obligation| obligation.passed),
        obligations,
        unregistered_aspects,
        remaining_scope: remaining_scope(name),
    }
}

fn remaining_scope(name: &str) -> String {
    let mut scope = "Only the named finite input/state sequences are covered. Additional values, invalid arguments, call interleavings, resource failures, threading, reclamation/leak behavior and unlisted aspects remain unqualified; passing these obligations is not a full-domain semantic contract.".to_string();
    if name == "Z3_mk_optimize" || name.starts_with("Z3_optimize_") {
        scope.push_str(" Optimize checks cover only bounded integer objectives, one finite integer Pareto frontier, selected nonnegative rational soft groups, and named lifetime/error sequences. Open, unbounded, irrational/algebraic, nonlinear, quantified and bit-vector objectives; box priority; negative soft weights; callbacks; interruption/resource exhaustion; parser/file import; cross-context translation; and every other unlisted input/state sequence remain unqualified.");
    }
    if name == "Z3_mk_fixedpoint" || name.starts_with("Z3_fixedpoint_") {
        scope.push_str(" Fixedpoint checks cover selected finite bit-vector Datalog relations and one ground-fact Spacer resource-refusal/recovery sequence. Arbitrary CHCs, other engines, proof validity, callback behavior, concurrent interruption, cover queries, relation representations, file input, nonlinear arithmetic and all other unlisted input/state sequences remain unqualified.");
    }
    if sequences::CLAIMS
        .iter()
        .any(|claim| claim.functions.contains(&name))
    {
        scope.push(' ');
        scope.push_str(sequences::REMAINING_SCOPE);
    }
    if quantifiers::CLAIMS
        .iter()
        .any(|claim| claim.functions.contains(&name))
    {
        scope.push(' ');
        scope.push_str(quantifiers::REMAINING_SCOPE);
    }
    if floating_point::CLAIMS
        .iter()
        .any(|claim| claim.functions.contains(&name))
    {
        scope.push(' ');
        scope.push_str(floating_point::REMAINING_SCOPE);
    }
    if parsing_substitution::CLAIMS
        .iter()
        .any(|claim| claim.functions.contains(&name))
    {
        scope.push(' ');
        scope.push_str(parsing_substitution::REMAINING_SCOPE);
    }
    scope
}

pub(super) fn validate(
    execution: &Execution,
    names: &[String],
    captures: &[Capture],
) -> Result<(), String> {
    if execution != &summarize(names, captures)? {
        return Err(
            "current ABI semantic contract outcomes differ from retained exact observations"
                .to_string(),
        );
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn successful_capture(id: String, stdout: String) -> Capture {
        Capture {
            id,
            exit_code: Some(0),
            timed_out: false,
            memout: false,
            stdin_complete: true,
            stdout_truncated: false,
            stderr_truncated: false,
            stdout,
            stderr: String::new(),
        }
    }

    fn passing_fixture() -> (Vec<String>, Vec<Capture>) {
        let names = registered_names()
            .into_iter()
            .map(str::to_string)
            .chain(["Z3_uncovered_example".to_string()])
            .collect();
        let mut captures = vec![successful_capture(
            "semantic.compiler".to_string(),
            "fixture compiler 1\n".to_string(),
        )];
        for family in families() {
            for subject in ["z3", "ay"] {
                captures.push(successful_capture(
                    format!("{subject}.{}.build", family.id),
                    String::new(),
                ));
                captures.push(successful_capture(
                    format!("{subject}.{}.run", family.id),
                    String::from_utf8(expected_stdout(family)).unwrap(),
                ));
            }
            let mut refused =
                successful_capture(format!("z3.{}.invalid-mode", family.id), String::new());
            refused.exit_code = Some(64);
            refused.stderr = MODE_REFUSAL.to_string();
            captures.push(refused);
            let mut negative = successful_capture(
                format!("z3.{}.negative-run", family.id),
                format!("{}\n", family.checks[..family.checks.len() - 1].join("\n")),
            );
            negative.exit_code = Some(2);
            negative.stderr = format!("ABI_CONTRACT_FAILED:{}\n", negative_check(family).unwrap());
            captures.push(negative);
        }
        (names, captures)
    }

    #[test]
    fn every_reference_family_must_reject_its_inverted_assertion_exactly() {
        let (names, captures) = passing_fixture();
        for family in families() {
            for mutation in 0..9 {
                let mut invalid = captures.clone();
                let id = format!("z3.{}.negative-run", family.id);
                let row = invalid.iter_mut().find(|row| row.id == id).unwrap();
                match mutation {
                    0 => row.exit_code = Some(0),
                    1 => row.exit_code = Some(1),
                    2 => row.timed_out = true,
                    3 => row.memout = true,
                    4 => row.stdin_complete = false,
                    5 => row.stdout_truncated = true,
                    6 => row.stderr_truncated = true,
                    7 => row.stdout.push_str(negative_check(family).unwrap()),
                    _ => row.stderr = "ABI_CONTRACT_FAILED:unrelated-check\n".to_string(),
                }
                let report = summarize(&names, &invalid).unwrap();
                let result = report
                    .families
                    .iter()
                    .find(|row| row.id == family.id)
                    .unwrap();
                // Good positive runs cannot overrule a broken negative control.
                assert!(result.reference_passed && result.ay_passed);
                assert!(!result.reference_negative_control_passed && !result.passed);
                assert!(!report.passed);
            }
            let mut missing = captures.clone();
            missing.retain(|row| row.id != format!("z3.{}.build", family.id));
            assert!(!summarize(&names, &missing).unwrap().passed);
            let mut failed_build = captures.clone();
            failed_build
                .iter_mut()
                .find(|row| row.id == format!("z3.{}.build", family.id))
                .unwrap()
                .exit_code = Some(1);
            assert!(!summarize(&names, &failed_build).unwrap().passed);
        }
    }

    #[test]
    fn negative_exit_credit_is_limited_to_the_registered_exact_protocol() {
        let (_, captures) = passing_fixture();
        let mut negative = captures
            .iter()
            .find(|row| row.id == "z3.contract-model.negative-run")
            .unwrap()
            .clone();
        assert_eq!(negative_capture_passed(&negative), Some(true));
        negative.id = "ay.contract-model.negative-run".to_string();
        assert_eq!(negative_capture_passed(&negative), None);
        negative.id = "z3.unregistered-family.negative-run".to_string();
        assert_eq!(negative_capture_passed(&negative), None);
        negative.id = "z3.contract-model.run".to_string();
        assert_eq!(negative_capture_passed(&negative), None);
        let mut refused = captures
            .iter()
            .find(|row| row.id == "z3.contract-model.invalid-mode")
            .unwrap()
            .clone();
        assert_eq!(negative_capture_passed(&refused), Some(true));
        refused.id = "ay.contract-model.invalid-mode".to_string();
        assert_eq!(negative_capture_passed(&refused), None);
    }

    #[test]
    fn replay_rejects_changed_negative_control_source_target_and_verdict() {
        let (names, captures) = passing_fixture();
        let report = summarize(&names, &captures).unwrap();
        for mutation in 0..4 {
            let mut forged = report.clone();
            let family = forged.families.first_mut().unwrap();
            match mutation {
                0 => family.reference_source_sha256 = "0".repeat(64),
                1 => family.negative_check_id = "unregistered-check".to_string(),
                2 => family.reference_negative_control_passed = false,
                _ => family.reference_mode_refusal_passed = false,
            }
            assert!(validate(&forged, &names, &captures).is_err());
        }
    }

    #[test]
    fn malformed_mode_control_requires_exact_refusal_without_fixture_output() {
        let (names, captures) = passing_fixture();
        for mutation in 0..9 {
            let mut invalid = captures.clone();
            let row = invalid
                .iter_mut()
                .find(|row| row.id == "z3.contract-model.invalid-mode")
                .unwrap();
            match mutation {
                0 => row.exit_code = Some(0),
                1 => row.exit_code = Some(2),
                2 => row.timed_out = true,
                3 => row.memout = true,
                4 => row.stdin_complete = false,
                5 => row.stdout_truncated = true,
                6 => row.stderr_truncated = true,
                7 => row.stdout = "model.context-created\n".to_string(),
                _ => row.stderr = "arbitrary failure\n".to_string(),
            }
            assert_eq!(negative_capture_passed(row), Some(false));
            let execution = summarize(&names, &invalid).unwrap();
            let model = execution
                .families
                .iter()
                .find(|family| family.id == "contract-model")
                .unwrap();
            assert!(!model.reference_mode_refusal_passed && !model.passed);
        }
        let mut missing = captures;
        missing.retain(|row| row.id != "z3.contract-model.invalid-mode");
        assert!(!summarize(&names, &missing).unwrap().passed);
    }

    #[test]
    fn reference_dispatcher_executes_conditions_once_and_refuses_arbitrary_targets() {
        let _guard = resource_test_lock();
        let directory = tempfile::tempdir().unwrap();
        let root = locate_repo_root().unwrap();
        let resources =
            PlannedResources::plan(&root, 1, "ABI dispatcher semantic regression").unwrap();
        // Use the actual maintained CHECK implementation without the unrelated
        // Z3 context helpers. The postcondition also detects double evaluation.
        let common = include_str!("contracts/common.h");
        let (_, macros) = common
            .split_once("#ifdef AY_CONTRACT_NEGATIVE_CHECK")
            .unwrap();
        let source = format!("#include <stdio.h>\n#include <string.h>\n#ifdef AY_CONTRACT_NEGATIVE_CHECK{macros}\nint main(void) {{ unsigned count = 0; CHECK(\"once.initial\", ++count == 1); CHECK(\"once.final\", ++count == 2); return count == 2 ? 0 : 3; }}\n");
        let wrapped = render_reference_source(&source, "once.final");
        let source_path = directory.path().join("dispatcher.c");
        let binary = directory.path().join("dispatcher");
        fs::write(&source_path, wrapped).unwrap();
        let built = capture(
            &resources,
            compiler(),
            &[
                "-std=c11".into(),
                "-O0".into(),
                "-Wall".into(),
                "-Wextra".into(),
                "-Werror".into(),
                source_path.as_os_str().to_owned(),
                "-o".into(),
                binary.as_os_str().to_owned(),
            ],
            b"",
            "dispatcher.build",
            Duration::from_secs(30),
        )
        .unwrap();
        assert!(built.exact_stdout(b""), "{}", built.stderr);
        let identity = sha256_file(&binary, "dispatcher test binary").unwrap();
        let positive = capture(
            &resources,
            &binary,
            &[],
            b"",
            "dispatcher.positive",
            Duration::from_secs(5),
        )
        .unwrap();
        assert!(positive.exact_stdout(b"once.initial\nonce.final\n"));
        let family = Family {
            id: "test-once",
            source: "",
            checks: &["once.initial", "once.final"],
        };
        let negative = capture(
            &resources,
            &binary,
            &[NEGATIVE_MODE.into()],
            b"",
            "dispatcher.negative",
            Duration::from_secs(5),
        )
        .unwrap();
        assert!(negative_run_passed(&negative, &family));
        for args in [
            vec![INVALID_MODE.into()],
            vec![NEGATIVE_MODE.into(), "once.initial".into()],
            vec!["once.initial".into()],
            vec!["--ay-abi-invert-last-check=once.initial".into()],
        ] {
            let refused = capture(
                &resources,
                &binary,
                &args,
                b"",
                "dispatcher.refused",
                Duration::from_secs(5),
            )
            .unwrap();
            assert!(mode_refusal_passed(&refused));
        }
        assert_eq!(
            sha256_file(&binary, "dispatcher test binary after all modes").unwrap(),
            identity
        );
    }

    #[test]
    fn contracts_require_both_complete_bounded_provider_runs() {
        let (names, captures) = passing_fixture();
        let report = summarize(&names, &captures).unwrap();
        assert!(report.passed);
        assert_eq!(report.uncovered_functions, 1);
        assert!(!function_contract("Z3_uncovered_example", &report).registered_obligations_passed);
        for subject in ["ay", "z3"] {
            let mut wrong = captures.clone();
            let model = wrong
                .iter_mut()
                .find(|capture| capture.id == format!("{subject}.contract-model.run"))
                .unwrap();
            model.stdout = model
                .stdout
                .replace("model.independent-retained-models\n", "");
            let failed = summarize(&names, &wrong).unwrap();
            assert!(!failed.passed);
            assert!(!function_contract("Z3_model_eval", &failed).registered_obligations_passed);
        }
        for failure in 0..3 {
            let mut wrong = captures.clone();
            let row = wrong
                .iter_mut()
                .find(|capture| capture.id == "ay.contract-context.run")
                .unwrap();
            match failure {
                0 => row.timed_out = true,
                1 => row.stdout_truncated = true,
                _ => row.stderr = "error".to_string(),
            }
            assert!(!summarize(&names, &wrong).unwrap().passed);
        }
    }

    #[test]
    fn missing_builds_and_absent_inventory_entries_cannot_receive_credit() {
        let (mut names, mut captures) = passing_fixture();
        captures.retain(|capture| capture.id != "ay.contract-solver.build");
        assert!(!summarize(&names, &captures).unwrap().passed);
        names.retain(|name| name != "Z3_model_eval");
        assert!(summarize(&names, &captures).is_err());
    }

    #[test]
    fn replay_rejects_invented_passes_and_ambiguous_capture_populations() {
        let (names, captures) = passing_fixture();
        let mut report = summarize(&names, &captures).unwrap();
        report.passed_functions += 1;
        assert!(validate(&report, &names, &captures).is_err());
        let mut duplicated = captures.clone();
        duplicated.push(captures[0].clone());
        assert!(summarize(&names, &duplicated).is_err());
        let missing_compiler = captures
            .into_iter()
            .filter(|capture| capture.id != "semantic.compiler")
            .collect::<Vec<_>>();
        let report = summarize(&names, &missing_compiler).unwrap();
        assert!(!report.passed);
        assert_eq!(report.passed_functions, 0);
    }

    #[test]
    fn each_family_requires_its_own_reference_and_subject_evidence() {
        let (names, captures) = passing_fixture();
        let passed = summarize(&names, &captures).unwrap();
        for family in families() {
            assert!(passed
                .families
                .iter()
                .any(|row| row.id == family.id && row.passed));
            for subject in ["z3", "ay"] {
                for mutation in 0..4 {
                    let mut invalid = captures.clone();
                    let capture = invalid
                        .iter_mut()
                        .find(|capture| capture.id == format!("{subject}.{}.run", family.id))
                        .unwrap();
                    match mutation {
                        0 => capture.exit_code = Some(2),
                        1 => {
                            capture.stdout = capture
                                .stdout
                                .replace(*family.checks.last().unwrap(), "unearned-check")
                        }
                        2 => capture.stdout_truncated = true,
                        _ => capture.stderr = "ABI_CONTRACT_FAILED:wrong result\n".to_string(),
                    }
                    let refused = summarize(&names, &invalid).unwrap();
                    assert!(!refused.passed);
                    assert!(
                        !refused
                            .families
                            .iter()
                            .find(|row| row.id == family.id)
                            .unwrap()
                            .passed
                    );
                    assert!(refused
                        .families
                        .iter()
                        .filter(|row| row.id != family.id)
                        .all(|row| row.passed));
                    for claim in claims().filter(|claim| claim.family == family.id) {
                        for function in claim.functions {
                            let contract = function_contract(function, &refused);
                            assert!(contract
                                .obligations
                                .iter()
                                .filter(|row| row.family == family.id)
                                .all(|row| !row.passed));
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn selected_optimize_contracts_leave_other_domains_explicitly_unqualified() {
        validate_catalog().unwrap();
        let (names, captures) = passing_fixture();
        let passed = summarize(&names, &captures).unwrap();
        for function in [
            "Z3_optimize_check",
            "Z3_optimize_assert_soft",
            "Z3_optimize_pop",
        ] {
            let contract = function_contract(function, &passed);
            assert!(contract.registered_obligations_passed);
            assert!(contract
                .remaining_scope
                .contains("Open, unbounded, irrational/algebraic"));
            assert!(contract.remaining_scope.contains("remain unqualified"));
        }
        for function in [
            "Z3_optimize_translate",
            "Z3_optimize_register_model_eh",
            "Z3_optimize_from_file",
        ] {
            let contract = function_contract(function, &passed);
            assert_eq!(contract.obligations.as_slice(), &[] as &[Obligation]);
            assert!(!contract.registered_obligations_passed);
            assert_eq!(contract.unregistered_aspects, ASPECTS);
        }
    }

    #[test]
    fn fixedpoint_refusal_cannot_be_promoted_to_complete_semantics() {
        let (names, mut captures) = passing_fixture();
        let passed = summarize(&names, &captures).unwrap();
        let contract = function_contract("Z3_fixedpoint_query", &passed);
        assert!(contract.registered_obligations_passed);
        assert!(contract.remaining_scope.contains("Arbitrary CHCs"));
        let observation = captures
            .iter_mut()
            .find(|capture| capture.id == "z3.contract-fixedpoint-resource.run")
            .unwrap();
        observation.stdout = observation.stdout.replace(
            "fixedpoint-resource.budget-refuses-decision\n",
            "fixedpoint-resource.unearned-decision\n",
        );
        let refused = summarize(&names, &captures).unwrap();
        assert!(!refused.passed);
        assert!(!function_contract("Z3_fixedpoint_query", &refused).registered_obligations_passed);
        assert!(
            !function_contract("Z3_fixedpoint_add_cover", &passed).registered_obligations_passed
        );
    }
}
