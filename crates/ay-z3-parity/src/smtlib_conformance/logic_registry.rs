// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Closed semantic witnesses for the 25 official SMT-LIB logic declarations.
//!
//! The authenticated registry files are the authority.  This module parses
//! every `:theories`, `:language`, `:extensions`, `:values`, `:note`, and
//! `:notes` field, binds each field to a detailed catalog row, and maps each
//! declaration to a finite language policy.  The policy generates positive
//! and negative theory witnesses plus one rejection transcript for every
//! excluded feature class.  A source field, logic, theory class, or policy
//! class that is not owned by that catalog prevents receipt construction.

use super::reference_inventory::{self, RegistryLogicDeclaration};
use super::*;
use ay_frontend::SExpr;

pub(super) const VALIDATOR_ID: &str = "builtin.logic-registry.v1";

const DIMENSION_ID: &str = "registry.logics";
const DEFAULT_TIMEOUT_SECS: u64 = 10;
const SEMANTIC_FIELD_COUNT: usize = 76;
const SEMANTIC_WITNESS_CASE_COUNT: usize = 208;
const RESTRICTION_CASE_COUNT: usize = 187;
const PROCESS_CASE_COUNT: usize = SEMANTIC_WITNESS_CASE_COUNT + RESTRICTION_CASE_COUNT;
const DETAILED_CASE_COUNT: usize = SEMANTIC_FIELD_COUNT + PROCESS_CASE_COUNT;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum QuantifierPolicy {
    QuantifierFree,
    Quantified,
}

impl QuantifierPolicy {
    const fn id(self) -> &'static str {
        match self {
            Self::QuantifierFree => "quantifier-free",
            Self::Quantified => "quantified",
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ExpansionPolicy {
    ConstantsOnly,
    FreeSortsAndConstants,
    FreeSortsAndFunctions,
}

impl ExpansionPolicy {
    const fn id(self) -> &'static str {
        match self {
            Self::ConstantsOnly => "constants-only",
            Self::FreeSortsAndConstants => "free-sorts-and-constants",
            Self::FreeSortsAndFunctions => "free-sorts-and-functions",
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ArithmeticPolicy {
    None,
    IntegerDifference,
    UfIntegerDifference,
    LinearInteger,
    NonlinearIntegerWithoutPower,
    FullInteger,
    RealDifference,
    LinearReal,
    NonlinearReal,
    MixedLinear,
    MixedNonlinear,
}

impl ArithmeticPolicy {
    const fn id(self) -> &'static str {
        match self {
            Self::None => "none",
            Self::IntegerDifference => "integer-difference",
            Self::UfIntegerDifference => "uf-integer-difference",
            Self::LinearInteger => "linear-integer",
            Self::NonlinearIntegerWithoutPower => "nonlinear-integer-without-power",
            Self::FullInteger => "full-integer-with-power",
            Self::RealDifference => "real-difference",
            Self::LinearReal => "linear-real",
            Self::NonlinearReal => "nonlinear-real",
            Self::MixedLinear => "mixed-linear-integer-real",
            Self::MixedNonlinear => "mixed-nonlinear-integer-real",
        }
    }

    const fn has_integers(self) -> bool {
        matches!(
            self,
            Self::IntegerDifference
                | Self::UfIntegerDifference
                | Self::LinearInteger
                | Self::NonlinearIntegerWithoutPower
                | Self::FullInteger
                | Self::MixedLinear
                | Self::MixedNonlinear
        )
    }

    const fn has_reals(self) -> bool {
        matches!(
            self,
            Self::RealDifference
                | Self::LinearReal
                | Self::NonlinearReal
                | Self::MixedLinear
                | Self::MixedNonlinear
        )
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ArrayPolicy {
    None,
    Any,
    IntToInt,
    IntToRealOrNested,
    BitVectorToBitVector,
}

impl ArrayPolicy {
    const fn id(self) -> &'static str {
        match self {
            Self::None => "none",
            Self::Any => "arbitrary-array-sorts",
            Self::IntToInt => "array-int-int-only",
            Self::IntToRealOrNested => "array-int-real-or-nested-only",
            Self::BitVectorToBitVector => "array-bv-bv-only",
        }
    }
}

#[derive(Clone, Copy)]
struct ProseShape {
    extensions: usize,
    values: usize,
    note: usize,
    notes: usize,
}

#[derive(Clone, Copy)]
struct LogicCatalog {
    name: &'static str,
    theories: &'static [&'static str],
    quantifiers: QuantifierPolicy,
    expansion: ExpansionPolicy,
    arithmetic: ArithmeticPolicy,
    arrays: ArrayPolicy,
    bitvectors: bool,
    prose: ProseShape,
}

const fn prose(extensions: usize, values: usize, note: usize, notes: usize) -> ProseShape {
    ProseShape {
        extensions,
        values,
        note,
        notes,
    }
}

const CATALOG: [LogicCatalog; 25] = [
    LogicCatalog {
        name: "AUFLIA",
        theories: &["Ints", "ArraysEx"],
        quantifiers: QuantifierPolicy::Quantified,
        expansion: ExpansionPolicy::FreeSortsAndFunctions,
        arithmetic: ArithmeticPolicy::LinearInteger,
        arrays: ArrayPolicy::IntToInt,
        bitvectors: false,
        prose: prose(1, 0, 0, 1),
    },
    LogicCatalog {
        name: "AUFLIRA",
        theories: &["Reals_Ints", "ArraysEx"],
        quantifiers: QuantifierPolicy::Quantified,
        expansion: ExpansionPolicy::FreeSortsAndFunctions,
        arithmetic: ArithmeticPolicy::MixedLinear,
        arrays: ArrayPolicy::IntToRealOrNested,
        bitvectors: false,
        prose: prose(2, 0, 0, 0),
    },
    LogicCatalog {
        name: "AUFNIRA",
        theories: &["Reals_Ints", "ArraysEx"],
        quantifiers: QuantifierPolicy::Quantified,
        expansion: ExpansionPolicy::FreeSortsAndFunctions,
        arithmetic: ArithmeticPolicy::MixedNonlinear,
        arrays: ArrayPolicy::Any,
        bitvectors: false,
        prose: prose(1, 0, 0, 1),
    },
    LogicCatalog {
        name: "LIA",
        theories: &["Ints"],
        quantifiers: QuantifierPolicy::Quantified,
        expansion: ExpansionPolicy::ConstantsOnly,
        arithmetic: ArithmeticPolicy::LinearInteger,
        arrays: ArrayPolicy::None,
        bitvectors: false,
        prose: prose(1, 0, 0, 0),
    },
    LogicCatalog {
        name: "LRA",
        theories: &["Reals"],
        quantifiers: QuantifierPolicy::Quantified,
        expansion: ExpansionPolicy::ConstantsOnly,
        arithmetic: ArithmeticPolicy::LinearReal,
        arrays: ArrayPolicy::None,
        bitvectors: false,
        prose: prose(1, 0, 0, 1),
    },
    LogicCatalog {
        name: "QF_ABV",
        theories: &["FixedSizeBitVectors", "ArraysEx"],
        quantifiers: QuantifierPolicy::QuantifierFree,
        expansion: ExpansionPolicy::ConstantsOnly,
        arithmetic: ArithmeticPolicy::None,
        arrays: ArrayPolicy::BitVectorToBitVector,
        bitvectors: true,
        prose: prose(1, 0, 0, 0),
    },
    LogicCatalog {
        name: "QF_AUFBV",
        theories: &["FixedSizeBitVectors", "ArraysEx"],
        quantifiers: QuantifierPolicy::QuantifierFree,
        expansion: ExpansionPolicy::FreeSortsAndFunctions,
        arithmetic: ArithmeticPolicy::None,
        arrays: ArrayPolicy::BitVectorToBitVector,
        bitvectors: true,
        prose: prose(1, 0, 0, 0),
    },
    LogicCatalog {
        name: "QF_AUFLIA",
        theories: &["Ints", "ArraysEx"],
        quantifiers: QuantifierPolicy::QuantifierFree,
        expansion: ExpansionPolicy::FreeSortsAndFunctions,
        arithmetic: ArithmeticPolicy::LinearInteger,
        arrays: ArrayPolicy::IntToInt,
        bitvectors: false,
        prose: prose(1, 0, 0, 0),
    },
    LogicCatalog {
        name: "QF_AX",
        theories: &["ArraysEx"],
        quantifiers: QuantifierPolicy::QuantifierFree,
        expansion: ExpansionPolicy::FreeSortsAndConstants,
        arithmetic: ArithmeticPolicy::None,
        arrays: ArrayPolicy::Any,
        bitvectors: false,
        prose: prose(0, 0, 0, 1),
    },
    LogicCatalog {
        name: "QF_BV",
        theories: &["FixedSizeBitVectors"],
        quantifiers: QuantifierPolicy::QuantifierFree,
        expansion: ExpansionPolicy::ConstantsOnly,
        arithmetic: ArithmeticPolicy::None,
        arrays: ArrayPolicy::None,
        bitvectors: true,
        prose: prose(1, 0, 0, 1),
    },
    LogicCatalog {
        name: "QF_EIA",
        theories: &["Ints"],
        quantifiers: QuantifierPolicy::QuantifierFree,
        expansion: ExpansionPolicy::ConstantsOnly,
        arithmetic: ArithmeticPolicy::FullInteger,
        arrays: ArrayPolicy::None,
        bitvectors: false,
        prose: prose(0, 0, 0, 0),
    },
    LogicCatalog {
        name: "QF_IDL",
        theories: &["Ints"],
        quantifiers: QuantifierPolicy::QuantifierFree,
        expansion: ExpansionPolicy::ConstantsOnly,
        arithmetic: ArithmeticPolicy::IntegerDifference,
        arrays: ArrayPolicy::None,
        bitvectors: false,
        prose: prose(0, 0, 0, 0),
    },
    LogicCatalog {
        name: "QF_LIA",
        theories: &["Ints"],
        quantifiers: QuantifierPolicy::QuantifierFree,
        expansion: ExpansionPolicy::ConstantsOnly,
        arithmetic: ArithmeticPolicy::LinearInteger,
        arrays: ArrayPolicy::None,
        bitvectors: false,
        prose: prose(1, 0, 0, 0),
    },
    LogicCatalog {
        name: "QF_LRA",
        theories: &["Reals"],
        quantifiers: QuantifierPolicy::QuantifierFree,
        expansion: ExpansionPolicy::ConstantsOnly,
        arithmetic: ArithmeticPolicy::LinearReal,
        arrays: ArrayPolicy::None,
        bitvectors: false,
        prose: prose(1, 0, 0, 0),
    },
    LogicCatalog {
        name: "QF_NIA",
        theories: &["Ints"],
        quantifiers: QuantifierPolicy::QuantifierFree,
        expansion: ExpansionPolicy::ConstantsOnly,
        arithmetic: ArithmeticPolicy::NonlinearIntegerWithoutPower,
        arrays: ArrayPolicy::None,
        bitvectors: false,
        prose: prose(0, 0, 0, 0),
    },
    LogicCatalog {
        name: "QF_NRA",
        theories: &["Reals"],
        quantifiers: QuantifierPolicy::QuantifierFree,
        expansion: ExpansionPolicy::ConstantsOnly,
        arithmetic: ArithmeticPolicy::NonlinearReal,
        arrays: ArrayPolicy::None,
        bitvectors: false,
        prose: prose(0, 0, 0, 0),
    },
    LogicCatalog {
        name: "QF_RDL",
        theories: &["Reals"],
        quantifiers: QuantifierPolicy::QuantifierFree,
        expansion: ExpansionPolicy::ConstantsOnly,
        arithmetic: ArithmeticPolicy::RealDifference,
        arrays: ArrayPolicy::None,
        bitvectors: false,
        prose: prose(1, 0, 0, 0),
    },
    LogicCatalog {
        name: "QF_UF",
        theories: &[],
        quantifiers: QuantifierPolicy::QuantifierFree,
        expansion: ExpansionPolicy::FreeSortsAndFunctions,
        arithmetic: ArithmeticPolicy::None,
        arrays: ArrayPolicy::None,
        bitvectors: false,
        prose: prose(0, 1, 0, 2),
    },
    LogicCatalog {
        name: "QF_UFBV",
        theories: &["FixedSizeBitVectors"],
        quantifiers: QuantifierPolicy::QuantifierFree,
        expansion: ExpansionPolicy::FreeSortsAndFunctions,
        arithmetic: ArithmeticPolicy::None,
        arrays: ArrayPolicy::None,
        bitvectors: true,
        prose: prose(1, 0, 0, 0),
    },
    LogicCatalog {
        name: "QF_UFIDL",
        theories: &["Ints"],
        quantifiers: QuantifierPolicy::QuantifierFree,
        expansion: ExpansionPolicy::FreeSortsAndFunctions,
        arithmetic: ArithmeticPolicy::UfIntegerDifference,
        arrays: ArrayPolicy::None,
        bitvectors: false,
        prose: prose(0, 0, 1, 0),
    },
    LogicCatalog {
        name: "QF_UFLIA",
        theories: &["Ints"],
        quantifiers: QuantifierPolicy::QuantifierFree,
        expansion: ExpansionPolicy::FreeSortsAndFunctions,
        arithmetic: ArithmeticPolicy::LinearInteger,
        arrays: ArrayPolicy::None,
        bitvectors: false,
        prose: prose(1, 0, 0, 0),
    },
    LogicCatalog {
        name: "QF_UFLRA",
        theories: &["Reals"],
        quantifiers: QuantifierPolicy::QuantifierFree,
        expansion: ExpansionPolicy::FreeSortsAndFunctions,
        arithmetic: ArithmeticPolicy::LinearReal,
        arrays: ArrayPolicy::None,
        bitvectors: false,
        prose: prose(1, 0, 0, 0),
    },
    LogicCatalog {
        name: "QF_UFNRA",
        theories: &["Reals"],
        quantifiers: QuantifierPolicy::QuantifierFree,
        expansion: ExpansionPolicy::FreeSortsAndFunctions,
        arithmetic: ArithmeticPolicy::NonlinearReal,
        arrays: ArrayPolicy::None,
        bitvectors: false,
        prose: prose(0, 0, 0, 0),
    },
    LogicCatalog {
        name: "UFLRA",
        theories: &["Reals"],
        quantifiers: QuantifierPolicy::Quantified,
        expansion: ExpansionPolicy::FreeSortsAndFunctions,
        arithmetic: ArithmeticPolicy::LinearReal,
        arrays: ArrayPolicy::None,
        bitvectors: false,
        prose: prose(1, 0, 0, 0),
    },
    LogicCatalog {
        name: "UFNIA",
        theories: &["Ints"],
        quantifiers: QuantifierPolicy::Quantified,
        expansion: ExpansionPolicy::FreeSortsAndFunctions,
        arithmetic: ArithmeticPolicy::NonlinearIntegerWithoutPower,
        arrays: ArrayPolicy::None,
        bitvectors: false,
        prose: prose(0, 0, 0, 0),
    },
];

#[derive(Debug, Serialize)]
struct ParsedSemanticFields {
    theories: Vec<String>,
    language: String,
    extensions: Vec<String>,
    values: Vec<String>,
    note: Vec<String>,
    notes: Vec<String>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum SemanticKind {
    Core,
    Integers,
    IntegerDifference,
    UfIntegerDifference,
    LinearInteger,
    NonlinearInteger,
    IntegerPower,
    Reals,
    RealDifference,
    LinearReal,
    NonlinearReal,
    MixedIntegerReal,
    ArraysAny,
    ArraysIntToInt,
    ArraysIntToRealOrNested,
    ArraysBitVectorToBitVector,
    BitVectors,
    BitVectorExtensions,
    FreeSorts,
    UninterpretedFunctions,
    Quantifiers,
}

impl SemanticKind {
    const fn id(self) -> &'static str {
        match self {
            Self::Core => "core",
            Self::Integers => "integers",
            Self::IntegerDifference => "integer-difference",
            Self::UfIntegerDifference => "uf-integer-difference",
            Self::LinearInteger => "linear-integer",
            Self::NonlinearInteger => "nonlinear-integer",
            Self::IntegerPower => "integer-power",
            Self::Reals => "reals",
            Self::RealDifference => "real-difference",
            Self::LinearReal => "linear-real",
            Self::NonlinearReal => "nonlinear-real",
            Self::MixedIntegerReal => "mixed-integer-real",
            Self::ArraysAny => "arrays-any-sort",
            Self::ArraysIntToInt => "arrays-int-int",
            Self::ArraysIntToRealOrNested => "arrays-int-real-nested",
            Self::ArraysBitVectorToBitVector => "arrays-bv-bv",
            Self::BitVectors => "bitvectors",
            Self::BitVectorExtensions => "bitvector-extensions",
            Self::FreeSorts => "free-sorts",
            Self::UninterpretedFunctions => "uninterpreted-functions",
            Self::Quantifiers => "quantifiers",
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum RestrictionKind {
    Quantifiers,
    FreeSorts,
    FreeFunctions,
    Integers,
    Reals,
    Arrays,
    BitVectors,
    NonlinearInteger,
    IntegerPower,
    IntegerSlash,
    IntegerDiv,
    IntegerMod,
    IntegerAbs,
    NonlinearReal,
    RealVariableDivision,
    GeneralIntegerAtom,
    SymbolicIntegerDifferenceBound,
    UfDifferenceNonNumeralOperands,
    GeneralRealAtom,
    ArraySort,
    BitVectorZeroWidth,
    BitVectorLiteralOverflow,
}

impl RestrictionKind {
    const fn id(self) -> &'static str {
        match self {
            Self::Quantifiers => "exclude-quantifiers",
            Self::FreeSorts => "exclude-free-sorts",
            Self::FreeFunctions => "exclude-free-functions",
            Self::Integers => "exclude-integer-theory",
            Self::Reals => "exclude-real-theory",
            Self::Arrays => "exclude-array-theory",
            Self::BitVectors => "exclude-bitvector-theory",
            Self::NonlinearInteger => "exclude-nonlinear-integer",
            Self::IntegerPower => "exclude-integer-power",
            Self::IntegerSlash => "exclude-integer-slash",
            Self::IntegerDiv => "exclude-integer-div",
            Self::IntegerMod => "exclude-integer-mod",
            Self::IntegerAbs => "exclude-integer-abs",
            Self::NonlinearReal => "exclude-nonlinear-real",
            Self::RealVariableDivision => "exclude-real-variable-division",
            Self::GeneralIntegerAtom => "exclude-general-integer-atom",
            Self::SymbolicIntegerDifferenceBound => "exclude-symbolic-integer-difference-bound",
            Self::UfDifferenceNonNumeralOperands => "exclude-ufidl-nonnumeral-operands",
            Self::GeneralRealAtom => "exclude-general-real-atom",
            Self::ArraySort => "exclude-array-sort",
            Self::BitVectorZeroWidth => "exclude-zero-width-bitvector",
            Self::BitVectorLiteralOverflow => "exclude-overflowing-bitvector-literal",
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ProcessExpectation {
    ExactStdout(&'static str),
    Rejection,
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
        match self.expectation {
            ProcessExpectation::ExactStdout(stdout) => format!(
                "{}; stdout={stdout:?}; stderr=\"\"; exit=0",
                self.obligation
            ),
            ProcessExpectation::Rejection => format!(
                "{}; exactly one SMT-LIB `(error \"...\")` response; no verdict; stderr=\"\"; exit=0-or-1",
                self.obligation
            ),
        }
    }
}

#[derive(Debug)]
struct PreparedCampaign {
    catalog_rows: Vec<ValidatorCase>,
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
                return Err(format!("unknown logic-registry flag {flag:?}"));
            }
            value => {
                if manifest.replace(PathBuf::from(value)).is_some() {
                    return Err("logic-registry takes exactly one manifest path".to_string());
                }
            }
        }
        index += 1;
    }

    let manifest = manifest.ok_or("logic-registry needs a manifest path")?;
    let receipt_path = receipt_path.ok_or("logic-registry requires --receipt <path>")?;
    let snapshot_path = snapshot_path.ok_or("logic-registry requires --source-snapshot <path>")?;
    let loaded = load_contract(&manifest)?;
    let report = validate_contract(&loaded.contract, &loaded.base, ValidationMode::Structural)?;
    if loaded.contract.campaign_id == UNASSIGNED_CAMPAIGN {
        return Err("assign a real --campaign id before producing evidence".to_string());
    }
    let dimension = logic_dimension(&loaded.contract)?;
    if dimension.inventory.granularity != InventoryGranularity::ItemLevel {
        return Err("registry.logics must retain its closed item-level inventory".to_string());
    }
    let subject = loaded
        .contract
        .subject
        .ay_executable
        .as_ref()
        .ok_or("logic-registry requires subject.ay_executable")?;
    let ay = ay_override.unwrap_or_else(|| artifact_path(&loaded.base, &subject.path));
    let source = reference_inventory::load_registry_source(
        &loaded.contract,
        dimension,
        &loaded.base,
        Some(&snapshot_path),
    )?;
    let execution = execute(
        &ay,
        &subject.sha256,
        &source.declarations,
        Duration::from_secs(timeout_secs),
        loaded.contract.resource_envelope.as_deref(),
    )?;
    let output_relative = future_relative_output(&loaded.base, &receipt_path)?;
    let current_exe = fs::canonicalize(
        std::env::current_exe().map_err(|error| format!("locating parity executable: {error}"))?,
    )
    .map_err(|error| format!("canonicalizing parity executable: {error}"))?;
    let validator_sha = sha256_file(&current_exe, "parity validator")?;
    let requirement_ids = dimension
        .requirements
        .iter()
        .map(|row| row.id.clone())
        .collect::<Vec<_>>();
    let receipt = ValidatorReceipt {
        schema: VALIDATOR_RECEIPT_SCHEMA.to_string(),
        campaign_id: loaded.contract.campaign_id.clone(),
        profile_id: PROFILE_ID.to_string(),
        profile_sha256: canonical_profile_sha256()?,
        dimension_id: DIMENSION_ID.to_string(),
        requirement_ids,
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
        "logic-registry={} receipt={} sha256={}",
        if receipt.result == ValidatorResult::Pass {
            "PASS"
        } else {
            "FAIL"
        },
        output_relative,
        receipt_sha
    );
    println!(
        "coverage=25-logics source-fields={SEMANTIC_FIELD_COUNT} semantic-witnesses={SEMANTIC_WITNESS_CASE_COUNT} restriction-witnesses={RESTRICTION_CASE_COUNT} detailed-cases={} catalog=closed",
        receipt.cases.total,
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
            "{VALIDATOR_ID} requires exactly one authenticated registry snapshot"
        ));
    };
    if input.id != "smtlib-registry" || input.cohort != SourceCohort::SmtlibRegistry {
        return Err(format!(
            "{VALIDATOR_ID} is not bound to the authenticated SMT-LIB registry"
        ));
    }
    let declarations = reference_inventory::load_bound_registry_source(
        input,
        context.manifest_dir,
        &canonical_profile(),
    )?;
    let prepared = prepare_campaign(&declarations)?;
    validate_recorded_shape(receipt, &prepared)?;
    if context.mode.replays_registered_validators() {
        let envelope = receipt
            .resource_envelope
            .as_deref()
            .ok_or("logic-registry receipt has no resource envelope")?;
        let parsed = parse_resource_envelope(envelope)?;
        if parsed.jobs != 1 {
            return Err("logic-registry receipts require a one-job resource envelope".to_string());
        }
        let subject = context
            .contract
            .subject
            .ay_executable
            .as_ref()
            .ok_or("logic-registry replay requires subject.ay_executable")?;
        let ay = artifact_path(context.manifest_dir, &subject.path);
        let live = execute(
            &ay,
            &subject.sha256,
            &declarations,
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

fn logic_dimension(contract: &Contract) -> Result<&Dimension, String> {
    contract
        .dimensions
        .iter()
        .find(|dimension| dimension.id == DIMENSION_ID)
        .ok_or_else(|| "closed registry.logics dimension is missing".to_string())
}

fn execute(
    ay_source: &Path,
    expected_ay_sha256: &str,
    declarations: &[RegistryLogicDeclaration],
    timeout: Duration,
    required_envelope: Option<&str>,
) -> Result<Execution, String> {
    if timeout.is_zero() || timeout > Duration::from_secs(3600) {
        return Err("logic-registry timeout must be between 1ns and 3600 seconds".to_string());
    }
    let prepared = prepare_campaign(declarations)?;
    let staged = stage_authenticated_executable(
        ay_source,
        expected_ay_sha256,
        "logic-registry AY executable",
    )?;
    let repo_root = locate_repo_root()?;
    let resources = PlannedResources::plan(
        &repo_root,
        1,
        "ay-z3-parity smtlib-conformance logic-registry",
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
                "live logic-registry resource envelope drift: expected {expected:?}, got {resource_envelope:?}"
            ));
        }
    }

    let mut rows = prepared.catalog_rows;
    for case in prepared.process_cases {
        let output = resources
            .run_external_transcript(
                &staged.path,
                ["--quiet", "-in"],
                &case.input,
                timeout,
                &format!("SMT-LIB logic conformance: {}", case.id),
            )
            .map_err(|error| error.to_string())?;
        rows.push(process_case_result(&case, output));
    }
    let post_sha = sha256_file(&staged.path, "staged AY after logic-registry run")?;
    if post_sha != expected_ay_sha256 {
        return Err("authenticated AY staging bytes changed during logic replay".to_string());
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

fn prepare_campaign(declarations: &[RegistryLogicDeclaration]) -> Result<PreparedCampaign, String> {
    if declarations.len() != CATALOG.len() {
        return Err(format!(
            "logic catalog source count drift: expected {}, got {}",
            CATALOG.len(),
            declarations.len()
        ));
    }
    let declaration_names = declarations
        .iter()
        .map(|declaration| declaration.name.as_str())
        .collect::<Vec<_>>();
    if declaration_names != SMTLIB_LOGICS {
        return Err(
            "authenticated logic declaration order differs from the closed catalog".to_string(),
        );
    }
    let catalog_names = CATALOG.iter().map(|entry| entry.name).collect::<Vec<_>>();
    if catalog_names != SMTLIB_LOGICS {
        return Err(
            "internal logic policy catalog is not the exact canonical inventory".to_string(),
        );
    }

    let mut catalog_rows = Vec::new();
    let mut process_cases = Vec::new();
    for (declaration, catalog) in declarations.iter().zip(CATALOG.iter()) {
        let parsed = parse_semantic_fields(declaration, catalog)?;
        let projection = serde_json::to_vec(&parsed)
            .map_err(|error| format!("serializing {} semantic fields: {error}", catalog.name))?;
        let source_catalog_sha256 = sha256_bytes(&projection);
        let mut logic_cases =
            process_cases_for_logic(declaration, catalog, &source_catalog_sha256)?;
        logic_cases.sort_by(|left, right| left.id.cmp(&right.id));
        let witness_ids = logic_cases
            .iter()
            .map(|case| case.id.as_str())
            .collect::<Vec<_>>()
            .join("\n");
        let witness_catalog_sha256 = sha256_bytes(witness_ids.as_bytes());
        let mut fields = semantic_field_values(&parsed);
        let expected_fields = 2
            + catalog.prose.extensions
            + catalog.prose.values
            + catalog.prose.note
            + catalog.prose.notes;
        if fields.len() != expected_fields {
            return Err(format!(
                "{} has an unowned semantic source field: expected {expected_fields}, got {}",
                catalog.name,
                fields.len()
            ));
        }
        for (field_id, value) in fields.drain(..) {
            let row_id = format!("registry.logics.{}.catalog.{field_id}", catalog.name);
            let input = grounded_bytes(
                declaration,
                &source_catalog_sha256,
                &row_id,
                value.as_bytes(),
            );
            catalog_rows.push(ValidatorCase {
                id: row_id,
                input_sha256: sha256_bytes(&input),
                expected: format!(
                    "authenticated source field is owned by witness catalog {witness_catalog_sha256}"
                ),
                observed: format!(
                    "path={}; git_blob={}; content_sha256={}; field_sha256={}; policy=quantifiers:{},expansion:{},arithmetic:{},arrays:{},bitvectors:{}",
                    declaration.path,
                    declaration.git_blob,
                    declaration.content_sha256,
                    sha256_bytes(value.as_bytes()),
                    catalog.quantifiers.id(),
                    catalog.expansion.id(),
                    catalog.arithmetic.id(),
                    catalog.arrays.id(),
                    catalog.bitvectors,
                ),
                stdout: None,
                stderr: None,
                exit_code: None,
                process: None,
                outcome: ValidatorCaseOutcome::Pass,
            });
        }
        process_cases.append(&mut logic_cases);
    }
    if catalog_rows.len() != SEMANTIC_FIELD_COUNT {
        return Err(format!(
            "closed semantic-field inventory drift: expected {SEMANTIC_FIELD_COUNT}, got {}",
            catalog_rows.len()
        ));
    }
    process_cases.sort_by(|left, right| left.id.cmp(&right.id));
    for pair in process_cases.windows(2) {
        if pair[0].id >= pair[1].id {
            return Err("generated logic witness IDs are not unique".to_string());
        }
    }
    let semantic_count = process_cases
        .iter()
        .filter(|case| case.id.contains(".semantic."))
        .count();
    let restriction_count = process_cases.len().saturating_sub(semantic_count);
    if semantic_count != SEMANTIC_WITNESS_CASE_COUNT
        || restriction_count != RESTRICTION_CASE_COUNT
        || catalog_rows.len() + process_cases.len() != DETAILED_CASE_COUNT
    {
        return Err(format!(
            "closed logic case inventory drift: fields={}, semantic={semantic_count}, restrictions={restriction_count}, total={}",
            catalog_rows.len(),
            catalog_rows.len() + process_cases.len()
        ));
    }
    catalog_rows.sort_by(|left, right| left.id.cmp(&right.id));
    Ok(PreparedCampaign {
        catalog_rows,
        process_cases,
    })
}

fn parse_semantic_fields(
    declaration: &RegistryLogicDeclaration,
    catalog: &LogicCatalog,
) -> Result<ParsedSemanticFields, String> {
    if declaration.name != catalog.name {
        return Err(format!(
            "logic catalog entry {} was paired with source {}",
            catalog.name, declaration.name
        ));
    }
    let parsed = ay_frontend::sexp::parse_sexp(&declaration.content)
        .map_err(|error| format!("parsing authenticated {}: {error}", declaration.path))?;
    let items = parsed
        .as_list()
        .ok_or_else(|| format!("{} is not one registry list", declaration.path))?;
    if items.len() < 4
        || !items[0].is_symbol("logic")
        || items[1].as_symbol() != Some(catalog.name)
        || (items.len() - 2) % 2 != 0
    {
        return Err(format!(
            "{} has an invalid logic declaration shape",
            declaration.path
        ));
    }
    let mut theories: Option<Vec<String>> = None;
    let mut language: Option<String> = None;
    let mut extensions = Vec::new();
    let mut values = Vec::new();
    let mut note = Vec::new();
    let mut notes = Vec::new();
    for pair in items[2..].chunks_exact(2) {
        let key = match &pair[0] {
            SExpr::Keyword(value) => value.as_str(),
            _ => {
                return Err(format!(
                    "{} contains a non-keyword registry attribute",
                    declaration.path
                ))
            }
        };
        match key {
            ":theories" => {
                if theories.is_some() {
                    return Err(format!("{} repeats :theories", declaration.path));
                }
                let list = pair[1]
                    .as_list()
                    .ok_or_else(|| format!("{} :theories is not a list", declaration.path))?;
                let names = list
                    .iter()
                    .map(|item| {
                        item.as_symbol().map(str::to_string).ok_or_else(|| {
                            format!("{} :theories contains a non-symbol", declaration.path)
                        })
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                theories = Some(names);
            }
            ":language" => set_one_string(&mut language, &pair[1], declaration, key)?,
            ":extensions" => push_string(&mut extensions, &pair[1], declaration, key)?,
            ":values" => push_string(&mut values, &pair[1], declaration, key)?,
            ":note" => push_string(&mut note, &pair[1], declaration, key)?,
            ":notes" => push_string(&mut notes, &pair[1], declaration, key)?,
            ":smt-lib-version" | ":smt-lib-release" | ":written-by" | ":date" | ":last-updated"
            | ":update-history" => {}
            other => {
                return Err(format!(
                    "{} has unclassified registry attribute {other:?}",
                    declaration.path
                ))
            }
        }
    }
    let theories = theories.ok_or_else(|| format!("{} has no :theories", declaration.path))?;
    let language = language.ok_or_else(|| format!("{} has no :language", declaration.path))?;
    let expected_theories = catalog
        .theories
        .iter()
        .map(|value| (*value).to_string())
        .collect::<Vec<_>>();
    if theories != expected_theories {
        return Err(format!(
            "{} theory catalog mismatch: source={theories:?}, catalog={expected_theories:?}",
            catalog.name
        ));
    }
    if extensions.len() != catalog.prose.extensions
        || values.len() != catalog.prose.values
        || note.len() != catalog.prose.note
        || notes.len() != catalog.prose.notes
    {
        return Err(format!(
            "{} prose-field catalog mismatch: extensions={}/{}, values={}/{}, note={}/{}, notes={}/{}",
            catalog.name,
            extensions.len(),
            catalog.prose.extensions,
            values.len(),
            catalog.prose.values,
            note.len(),
            catalog.prose.note,
            notes.len(),
            catalog.prose.notes,
        ));
    }
    validate_catalog_theory_projection(catalog)?;
    Ok(ParsedSemanticFields {
        theories,
        language,
        extensions,
        values,
        note,
        notes,
    })
}

fn set_one_string(
    target: &mut Option<String>,
    value: &SExpr,
    declaration: &RegistryLogicDeclaration,
    key: &str,
) -> Result<(), String> {
    let SExpr::String(value) = value else {
        return Err(format!("{} {key} is not a string", declaration.path));
    };
    if target.replace(value.clone()).is_some() {
        return Err(format!("{} repeats {key}", declaration.path));
    }
    Ok(())
}

fn push_string(
    target: &mut Vec<String>,
    value: &SExpr,
    declaration: &RegistryLogicDeclaration,
    key: &str,
) -> Result<(), String> {
    let SExpr::String(value) = value else {
        return Err(format!("{} {key} is not a string", declaration.path));
    };
    target.push(value.clone());
    Ok(())
}

fn validate_catalog_theory_projection(catalog: &LogicCatalog) -> Result<(), String> {
    let has_ints = catalog.theories.contains(&"Ints") || catalog.theories.contains(&"Reals_Ints");
    let has_reals = catalog.theories.contains(&"Reals") || catalog.theories.contains(&"Reals_Ints");
    let has_arrays = catalog.theories.contains(&"ArraysEx");
    let has_bitvectors = catalog.theories.contains(&"FixedSizeBitVectors");
    if has_ints != catalog.arithmetic.has_integers()
        || has_reals != catalog.arithmetic.has_reals()
        || has_arrays != (catalog.arrays != ArrayPolicy::None)
        || has_bitvectors != catalog.bitvectors
    {
        return Err(format!(
            "{} policy does not own every included theory class",
            catalog.name
        ));
    }
    Ok(())
}

fn semantic_field_values(fields: &ParsedSemanticFields) -> Vec<(String, String)> {
    let mut values = vec![
        ("theories".to_string(), format!("{:?}", fields.theories)),
        ("language".to_string(), fields.language.clone()),
    ];
    values.extend(
        fields
            .extensions
            .iter()
            .enumerate()
            .map(|(index, value)| (format!("extensions.{index}"), value.clone())),
    );
    values.extend(
        fields
            .values
            .iter()
            .enumerate()
            .map(|(index, value)| (format!("values.{index}"), value.clone())),
    );
    values.extend(
        fields
            .note
            .iter()
            .enumerate()
            .map(|(index, value)| (format!("note.{index}"), value.clone())),
    );
    values.extend(
        fields
            .notes
            .iter()
            .enumerate()
            .map(|(index, value)| (format!("notes.{index}"), value.clone())),
    );
    values
}

fn process_cases_for_logic(
    declaration: &RegistryLogicDeclaration,
    catalog: &LogicCatalog,
    source_catalog_sha256: &str,
) -> Result<Vec<ProcessCase>, String> {
    let mut cases = Vec::new();
    for kind in semantic_kinds(catalog) {
        for (polarity, body, stdout) in semantic_bodies(kind) {
            let id = format!(
                "registry.logics.{}.semantic.{}.{}",
                catalog.name,
                kind.id(),
                polarity
            );
            let script = logic_script(
                declaration,
                source_catalog_sha256,
                &id,
                catalog.name,
                body,
                true,
            );
            cases.push(ProcessCase {
                id,
                input: script.into_bytes(),
                expectation: ProcessExpectation::ExactStdout(stdout),
                obligation: format!(
                    "authenticated {} must decide the {} {} witness without fallback",
                    catalog.name,
                    kind.id(),
                    polarity
                ),
            });
        }
    }
    let mut restrictions = restriction_kinds(catalog);
    restrictions.sort_by_key(|kind| kind.id());
    restrictions.dedup_by_key(|kind| kind.id());
    for kind in restrictions {
        let id = format!("registry.logics.{}.restriction.{}", catalog.name, kind.id());
        let script = logic_script(
            declaration,
            source_catalog_sha256,
            &id,
            catalog.name,
            restriction_body(kind),
            false,
        );
        cases.push(ProcessCase {
            id,
            input: script.into_bytes(),
            expectation: ProcessExpectation::Rejection,
            obligation: format!(
                "authenticated {} language must reject excluded feature class {}",
                catalog.name,
                kind.id()
            ),
        });
    }
    if cases.is_empty() {
        return Err(format!("{} generated no semantic cases", catalog.name));
    }
    Ok(cases)
}

fn semantic_kinds(catalog: &LogicCatalog) -> Vec<SemanticKind> {
    let mut kinds = vec![SemanticKind::Core];
    match catalog.arithmetic {
        ArithmeticPolicy::None => {}
        ArithmeticPolicy::IntegerDifference => {
            kinds.push(SemanticKind::IntegerDifference);
        }
        ArithmeticPolicy::UfIntegerDifference => {
            kinds.extend([SemanticKind::Integers, SemanticKind::UfIntegerDifference]);
        }
        ArithmeticPolicy::LinearInteger => {
            kinds.extend([SemanticKind::Integers, SemanticKind::LinearInteger]);
        }
        ArithmeticPolicy::NonlinearIntegerWithoutPower => {
            kinds.extend([SemanticKind::Integers, SemanticKind::NonlinearInteger]);
        }
        ArithmeticPolicy::FullInteger => {
            kinds.extend([
                SemanticKind::Integers,
                SemanticKind::NonlinearInteger,
                SemanticKind::IntegerPower,
            ]);
        }
        ArithmeticPolicy::RealDifference => {
            kinds.push(SemanticKind::RealDifference);
        }
        ArithmeticPolicy::LinearReal => {
            kinds.extend([SemanticKind::Reals, SemanticKind::LinearReal]);
        }
        ArithmeticPolicy::NonlinearReal => {
            kinds.extend([SemanticKind::Reals, SemanticKind::NonlinearReal]);
        }
        ArithmeticPolicy::MixedLinear => {
            kinds.extend([
                SemanticKind::Integers,
                SemanticKind::Reals,
                SemanticKind::MixedIntegerReal,
                SemanticKind::LinearInteger,
                SemanticKind::LinearReal,
            ]);
        }
        ArithmeticPolicy::MixedNonlinear => {
            kinds.extend([
                SemanticKind::Integers,
                SemanticKind::Reals,
                SemanticKind::MixedIntegerReal,
                SemanticKind::NonlinearInteger,
                SemanticKind::NonlinearReal,
            ]);
        }
    }
    match catalog.arrays {
        ArrayPolicy::None => {}
        ArrayPolicy::Any => kinds.push(SemanticKind::ArraysAny),
        ArrayPolicy::IntToInt => kinds.push(SemanticKind::ArraysIntToInt),
        ArrayPolicy::IntToRealOrNested => kinds.push(SemanticKind::ArraysIntToRealOrNested),
        ArrayPolicy::BitVectorToBitVector => kinds.push(SemanticKind::ArraysBitVectorToBitVector),
    }
    if catalog.bitvectors {
        kinds.extend([SemanticKind::BitVectors, SemanticKind::BitVectorExtensions]);
    }
    match catalog.expansion {
        ExpansionPolicy::ConstantsOnly => {}
        ExpansionPolicy::FreeSortsAndConstants => kinds.push(SemanticKind::FreeSorts),
        ExpansionPolicy::FreeSortsAndFunctions => kinds.push(SemanticKind::UninterpretedFunctions),
    }
    if catalog.quantifiers == QuantifierPolicy::Quantified {
        kinds.push(SemanticKind::Quantifiers);
    }
    kinds.sort_by_key(|kind| kind.id());
    kinds.dedup_by_key(|kind| kind.id());
    kinds
}

fn restriction_kinds(catalog: &LogicCatalog) -> Vec<RestrictionKind> {
    let mut kinds = Vec::new();
    if catalog.quantifiers == QuantifierPolicy::QuantifierFree {
        kinds.push(RestrictionKind::Quantifiers);
    }
    match catalog.expansion {
        ExpansionPolicy::ConstantsOnly => {
            kinds.extend([RestrictionKind::FreeSorts, RestrictionKind::FreeFunctions]);
        }
        ExpansionPolicy::FreeSortsAndConstants => kinds.push(RestrictionKind::FreeFunctions),
        ExpansionPolicy::FreeSortsAndFunctions => {}
    }
    if !catalog.arithmetic.has_integers() {
        kinds.push(RestrictionKind::Integers);
    }
    if !catalog.arithmetic.has_reals() {
        kinds.push(RestrictionKind::Reals);
    }
    if catalog.arrays == ArrayPolicy::None {
        kinds.push(RestrictionKind::Arrays);
    }
    if !catalog.bitvectors {
        kinds.push(RestrictionKind::BitVectors);
    }
    match catalog.arithmetic {
        ArithmeticPolicy::None
        | ArithmeticPolicy::FullInteger
        | ArithmeticPolicy::NonlinearReal
        | ArithmeticPolicy::MixedNonlinear => {}
        ArithmeticPolicy::IntegerDifference => kinds.extend([
            RestrictionKind::GeneralIntegerAtom,
            RestrictionKind::SymbolicIntegerDifferenceBound,
            RestrictionKind::NonlinearInteger,
            RestrictionKind::IntegerPower,
            RestrictionKind::IntegerSlash,
            RestrictionKind::IntegerDiv,
            RestrictionKind::IntegerMod,
            RestrictionKind::IntegerAbs,
        ]),
        ArithmeticPolicy::UfIntegerDifference => kinds.extend([
            RestrictionKind::UfDifferenceNonNumeralOperands,
            RestrictionKind::NonlinearInteger,
            RestrictionKind::IntegerPower,
            RestrictionKind::IntegerSlash,
            RestrictionKind::IntegerDiv,
            RestrictionKind::IntegerMod,
            RestrictionKind::IntegerAbs,
        ]),
        ArithmeticPolicy::LinearInteger => kinds.extend([
            RestrictionKind::NonlinearInteger,
            RestrictionKind::IntegerPower,
            RestrictionKind::IntegerSlash,
            RestrictionKind::IntegerDiv,
            RestrictionKind::IntegerMod,
            RestrictionKind::IntegerAbs,
        ]),
        ArithmeticPolicy::NonlinearIntegerWithoutPower => kinds.push(RestrictionKind::IntegerPower),
        ArithmeticPolicy::RealDifference => kinds.extend([
            RestrictionKind::GeneralRealAtom,
            RestrictionKind::NonlinearReal,
            RestrictionKind::RealVariableDivision,
        ]),
        ArithmeticPolicy::LinearReal => kinds.extend([
            RestrictionKind::NonlinearReal,
            RestrictionKind::RealVariableDivision,
        ]),
        ArithmeticPolicy::MixedLinear => kinds.extend([
            RestrictionKind::NonlinearInteger,
            RestrictionKind::IntegerSlash,
            RestrictionKind::IntegerDiv,
            RestrictionKind::IntegerMod,
            RestrictionKind::IntegerAbs,
            RestrictionKind::NonlinearReal,
            RestrictionKind::RealVariableDivision,
        ]),
    }
    if matches!(
        catalog.arrays,
        ArrayPolicy::IntToInt | ArrayPolicy::IntToRealOrNested | ArrayPolicy::BitVectorToBitVector
    ) {
        kinds.push(RestrictionKind::ArraySort);
    }
    if catalog.bitvectors {
        kinds.extend([
            RestrictionKind::BitVectorZeroWidth,
            RestrictionKind::BitVectorLiteralOverflow,
        ]);
    }
    kinds
}

fn semantic_bodies(kind: SemanticKind) -> [(&'static str, &'static str, &'static str); 2] {
    match kind {
        SemanticKind::Core => [
            ("positive", "(assert true)\n", "sat\n"),
            ("negative", "(assert false)\n", "unsat\n"),
        ],
        SemanticKind::Integers => [
            ("positive", "(assert (= (+ 2 3) 5))\n", "sat\n"),
            ("negative", "(assert (distinct (+ 2 3) 5))\n", "unsat\n"),
        ],
        SemanticKind::IntegerDifference => [
            (
                "positive",
                "(declare-const x Int)\n(declare-const y Int)\n(assert (<= (- x y) 2))\n",
                "sat\n",
            ),
            (
                "negative",
                "(declare-const x Int)\n(declare-const y Int)\n(declare-const z Int)\n(assert (<= (- x y) (- 1)))\n(assert (<= (- y z) (- 1)))\n(assert (<= (- z x) (- 1)))\n",
                "unsat\n",
            ),
        ],
        SemanticKind::UfIntegerDifference => [
            (
                "positive",
                "(declare-const x Int)\n(declare-fun f (Int) Int)\n(assert (= x 2))\n(assert (= (f (+ x 1)) (f 3)))\n",
                "sat\n",
            ),
            (
                "negative",
                "(declare-const x Int)\n(declare-fun f (Int) Int)\n(assert (= x 2))\n(assert (distinct (f (+ x 1)) (f 3)))\n",
                "unsat\n",
            ),
        ],
        SemanticKind::LinearInteger => [
            (
                "positive",
                "(declare-const x Int)\n(assert (= x 4))\n(assert (= (* 3 x) 12))\n",
                "sat\n",
            ),
            (
                "negative",
                "(declare-const x Int)\n(assert (= x 4))\n(assert (distinct (* 3 x) 12))\n",
                "unsat\n",
            ),
        ],
        SemanticKind::NonlinearInteger => [
            (
                "positive",
                "(declare-const x Int)\n(declare-const y Int)\n(assert (= x 3))\n(assert (= y 4))\n(assert (= (* x y) 12))\n",
                "sat\n",
            ),
            (
                "negative",
                "(declare-const x Int)\n(declare-const y Int)\n(assert (= x 3))\n(assert (= y 4))\n(assert (distinct (* x y) 12))\n",
                "unsat\n",
            ),
        ],
        SemanticKind::IntegerPower => [
            ("positive", "(assert (= (** 2 10) 1024))\n", "sat\n"),
            (
                "negative",
                "(assert (distinct (** 2 10) 1024))\n",
                "unsat\n",
            ),
        ],
        SemanticKind::Reals => [
            ("positive", "(assert (= (+ 1.0 2.0) 3.0))\n", "sat\n"),
            (
                "negative",
                "(assert (distinct (+ 1.0 2.0) 3.0))\n",
                "unsat\n",
            ),
        ],
        SemanticKind::RealDifference => [
            (
                "positive",
                "(declare-const x Real)\n(declare-const y Real)\n(assert (< (- x y) (/ 3 2)))\n",
                "sat\n",
            ),
            (
                "negative",
                "(declare-const x Real)\n(declare-const y Real)\n(assert (< x y))\n(assert (<= y x))\n",
                "unsat\n",
            ),
        ],
        SemanticKind::LinearReal => [
            (
                "positive",
                "(declare-const x Real)\n(assert (= x 2.0))\n(assert (= (* (/ 3 2) x) 3.0))\n",
                "sat\n",
            ),
            (
                "negative",
                "(declare-const x Real)\n(assert (= x 2.0))\n(assert (distinct (* (/ 3 2) x) 3.0))\n",
                "unsat\n",
            ),
        ],
        SemanticKind::NonlinearReal => [
            (
                "positive",
                "(declare-const x Real)\n(assert (= x 3.0))\n(assert (= (* x x) 9.0))\n",
                "sat\n",
            ),
            (
                "negative",
                "(declare-const x Real)\n(assert (= x 3.0))\n(assert (distinct (* x x) 9.0))\n",
                "unsat\n",
            ),
        ],
        SemanticKind::MixedIntegerReal => [
            (
                "positive",
                "(declare-const i Int)\n(declare-const r Real)\n(assert (= i 2))\n(assert (= r i))\n(assert (= (/ i 2) 1.0))\n",
                "sat\n",
            ),
            (
                "negative",
                "(declare-const i Int)\n(declare-const r Real)\n(assert (= i 2))\n(assert (= r i))\n(assert (distinct (/ i 2) 1.0))\n",
                "unsat\n",
            ),
        ],
        SemanticKind::ArraysAny => [
            (
                "positive",
                "(declare-sort I 0)\n(declare-sort E 0)\n(declare-const a (Array I E))\n(declare-const i I)\n(declare-const v E)\n(assert (= (select (store a i v) i) v))\n",
                "sat\n",
            ),
            (
                "negative",
                "(declare-sort I 0)\n(declare-sort E 0)\n(declare-const a (Array I E))\n(declare-const i I)\n(declare-const v E)\n(assert (distinct (select (store a i v) i) v))\n",
                "unsat\n",
            ),
        ],
        SemanticKind::ArraysIntToInt => [
            (
                "positive",
                "(declare-const a (Array Int Int))\n(declare-const i Int)\n(declare-const v Int)\n(assert (= (select (store a i v) i) v))\n",
                "sat\n",
            ),
            (
                "negative",
                "(declare-const a (Array Int Int))\n(declare-const i Int)\n(declare-const v Int)\n(assert (distinct (select (store a i v) i) v))\n",
                "unsat\n",
            ),
        ],
        SemanticKind::ArraysIntToRealOrNested => [
            (
                "positive",
                "(declare-const a (Array Int Real))\n(declare-const nested (Array Int (Array Int Real)))\n(declare-const i Int)\n(declare-const j Int)\n(declare-const v Real)\n(assert (= (select (store a i v) i) v))\n(assert (= (select (select (store nested i (store a j v)) i) j) v))\n",
                "sat\n",
            ),
            (
                "negative",
                "(declare-const a (Array Int Real))\n(declare-const i Int)\n(declare-const v Real)\n(assert (distinct (select (store a i v) i) v))\n",
                "unsat\n",
            ),
        ],
        SemanticKind::ArraysBitVectorToBitVector => [
            (
                "positive",
                "(declare-const a (Array (_ BitVec 4) (_ BitVec 8)))\n(declare-const i (_ BitVec 4))\n(assert (= (select (store a i #xff) i) #xff))\n",
                "sat\n",
            ),
            (
                "negative",
                "(declare-const a (Array (_ BitVec 4) (_ BitVec 8)))\n(declare-const i (_ BitVec 4))\n(assert (distinct (select (store a i #xff) i) #xff))\n",
                "unsat\n",
            ),
        ],
        SemanticKind::BitVectors => [
            (
                "positive",
                "(assert (= (bvadd #x0f #x01) #x10))\n",
                "sat\n",
            ),
            (
                "negative",
                "(assert (distinct (bvadd #x0f #x01) #x10))\n",
                "unsat\n",
            ),
        ],
        SemanticKind::BitVectorExtensions => [
            (
                "positive",
                "(assert (= (bvsub #x10 #x01) #x0f))\n(assert (= ((_ rotate_left 1) #x81) #x03))\n(assert (bvuaddo #xff #x01))\n",
                "sat\n",
            ),
            (
                "negative",
                "(assert (distinct (bvsub #x10 #x01) #x0f))\n",
                "unsat\n",
            ),
        ],
        SemanticKind::FreeSorts => [
            (
                "positive",
                "(declare-sort U 0)\n(declare-const a U)\n(assert (= (let ((x a)) x) a))\n",
                "sat\n",
            ),
            (
                "negative",
                "(declare-sort U 0)\n(declare-const a U)\n(assert (distinct (let ((x a)) x) a))\n",
                "unsat\n",
            ),
        ],
        SemanticKind::UninterpretedFunctions => [
            (
                "positive",
                "(declare-sort U 0)\n(declare-fun f (U) U)\n(declare-const a U)\n(declare-const b U)\n(assert (= a b))\n(assert (= (f a) (f b)))\n",
                "sat\n",
            ),
            (
                "negative",
                "(declare-sort U 0)\n(declare-fun f (U) U)\n(declare-const a U)\n(declare-const b U)\n(assert (= a b))\n(assert (distinct (f a) (f b)))\n",
                "unsat\n",
            ),
        ],
        SemanticKind::Quantifiers => [
            (
                "positive",
                "(assert (forall ((q Bool)) (= q q)))\n",
                "sat\n",
            ),
            (
                "negative",
                "(assert (exists ((q Bool)) (distinct q q)))\n",
                "unsat\n",
            ),
        ],
    }
}

fn restriction_body(kind: RestrictionKind) -> &'static str {
    match kind {
        RestrictionKind::Quantifiers => "(assert (forall ((q Bool)) (= q q)))\n",
        RestrictionKind::FreeSorts => {
            "(declare-sort U 0)\n(declare-const u U)\n(assert (= u u))\n"
        }
        RestrictionKind::FreeFunctions => {
            "(declare-fun f (Bool) Bool)\n(assert (f true))\n"
        }
        RestrictionKind::Integers => {
            "(declare-const x Int)\n(assert (= (+ x 1) 2))\n"
        }
        RestrictionKind::Reals => {
            "(declare-const x Real)\n(assert (= (+ x 1.0) 2.0))\n"
        }
        RestrictionKind::Arrays => {
            "(declare-const a (Array Bool Bool))\n(assert (= (select (store a true false) true) false))\n"
        }
        RestrictionKind::BitVectors => "(assert (= (bvadd #x01 #x01) #x02))\n",
        RestrictionKind::NonlinearInteger => {
            "(declare-const x Int)\n(declare-const y Int)\n(assert (= (* x y) 4))\n"
        }
        RestrictionKind::IntegerPower => {
            "(declare-const x Int)\n(assert (= (** x 2) 4))\n"
        }
        RestrictionKind::IntegerSlash => {
            "(declare-const x Int)\n(declare-const y Int)\n(assert (= (/ x y) 1.0))\n"
        }
        RestrictionKind::IntegerDiv => {
            "(declare-const x Int)\n(declare-const y Int)\n(assert (= (div x y) 1))\n"
        }
        RestrictionKind::IntegerMod => {
            "(declare-const x Int)\n(declare-const y Int)\n(assert (= (mod x y) 1))\n"
        }
        RestrictionKind::IntegerAbs => {
            "(declare-const x Int)\n(assert (= (abs x) x))\n"
        }
        RestrictionKind::NonlinearReal => {
            "(declare-const x Real)\n(declare-const y Real)\n(assert (= (* x y) 4.0))\n"
        }
        RestrictionKind::RealVariableDivision => {
            "(declare-const x Real)\n(declare-const y Real)\n(assert (= (/ x y) 1.0))\n"
        }
        RestrictionKind::GeneralIntegerAtom => {
            "(declare-const x Int)\n(declare-const y Int)\n(assert (< (+ x y) 0))\n"
        }
        RestrictionKind::SymbolicIntegerDifferenceBound => {
            "(declare-const x Int)\n(declare-const y Int)\n(declare-const z Int)\n(assert (< (- x y) z))\n"
        }
        RestrictionKind::UfDifferenceNonNumeralOperands => {
            "(declare-const x Int)\n(declare-const y Int)\n(assert (= (+ x y) 0))\n"
        }
        RestrictionKind::GeneralRealAtom => {
            "(declare-const x Real)\n(declare-const y Real)\n(assert (< (+ x y) 0.0))\n"
        }
        RestrictionKind::ArraySort => {
            "(declare-const a (Array Bool Bool))\n(assert (= (select (store a true false) true) false))\n"
        }
        RestrictionKind::BitVectorZeroWidth => {
            "(declare-const x (_ BitVec 0))\n(assert (= x x))\n"
        }
        RestrictionKind::BitVectorLiteralOverflow => {
            "(assert (= (_ bv256 8) #x00))\n"
        }
    }
}

fn logic_script(
    declaration: &RegistryLogicDeclaration,
    source_catalog_sha256: &str,
    case_id: &str,
    logic: &str,
    body: &str,
    check_sat: bool,
) -> String {
    let suffix = if check_sat {
        "(check-sat)\n(exit)\n"
    } else {
        "(exit)\n"
    };
    format!(
        "; ay-smtlib-logic-catalog/v1\n; source-path={}\n; source-git-blob={}\n; source-content-sha256={}\n; semantic-catalog-sha256={}\n; case={}\n(set-option :print-success false)\n(set-logic {})\n{}{}",
        declaration.path,
        declaration.git_blob,
        declaration.content_sha256,
        source_catalog_sha256,
        case_id,
        logic,
        body,
        suffix,
    )
}

fn grounded_bytes(
    declaration: &RegistryLogicDeclaration,
    source_catalog_sha256: &str,
    id: &str,
    value: &[u8],
) -> Vec<u8> {
    let mut bytes = format!(
        "{}\n{}\n{}\n{}\n{}\n",
        declaration.path,
        declaration.git_blob,
        declaration.content_sha256,
        source_catalog_sha256,
        id
    )
    .into_bytes();
    bytes.extend_from_slice(value);
    bytes
}

fn process_case_result(case: &ProcessCase, output: GuardedTranscriptOutput) -> ValidatorCase {
    match case.expectation {
        ProcessExpectation::ExactStdout(stdout) => {
            let mut row = transcript_case(&case.id, &case.input, stdout, output, &case.obligation);
            if row.outcome == ValidatorCaseOutcome::Fail
                && row.exit_code == Some(0)
                && row.stdout.as_deref() == Some("unknown\n")
                && row.stderr.as_deref() == Some("")
                && row.process.as_ref().is_some_and(process_completed)
            {
                row.outcome = ValidatorCaseOutcome::Unknown;
                row.observed.push_str("; solver_result=unknown");
            }
            row
        }
        ProcessExpectation::Rejection => rejection_case(case, output),
    }
}

fn rejection_case(case: &ProcessCase, output: GuardedTranscriptOutput) -> ValidatorCase {
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
    let rejection_match = stdout_valid
        && stderr_valid
        && stderr.is_empty()
        && matches!(exit_code, Some(0 | 1))
        && is_single_error_response(&stdout);
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
    } else if rejection_match {
        ValidatorCaseOutcome::Pass
    } else if !output.status.is_some_and(|status| status.success()) {
        ValidatorCaseOutcome::Crash
    } else {
        ValidatorCaseOutcome::Fail
    };
    ValidatorCase {
        id: case.id.clone(),
        input_sha256: sha256_bytes(&case.input),
        expected: case.expected(),
        observed: format!(
            "status={exit_code:?}; timeout={}; memout={}; stdin_complete={}; stdout_truncated={}; stderr_truncated={}; single_error_response={rejection_match}; stderr_empty={}",
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

fn is_single_error_response(stdout: &str) -> bool {
    let Ok(rows) = ay_frontend::sexp::parse_sexps(stdout) else {
        return false;
    };
    let [row] = rows.as_slice() else {
        return false;
    };
    let Some(items) = row.as_list() else {
        return false;
    };
    matches!(items, [head, SExpr::String(_)] if head.is_symbol("error"))
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
        .catalog_rows
        .iter()
        .map(|row| {
            (
                row.id.clone(),
                row.input_sha256.clone(),
                row.expected.clone(),
                false,
                None,
            )
        })
        .collect::<Vec<_>>();
    expected.extend(prepared.process_cases.iter().map(|case| {
        (
            case.id.clone(),
            sha256_bytes(&case.input),
            case.expected(),
            true,
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
    for (row, (id, input_sha256, expected_text, process_required, expectation)) in
        receipt.case_results.iter().zip(expected)
    {
        if row.id != id || row.input_sha256 != input_sha256 || row.expected != expected_text {
            return Err(format!(
                "{VALIDATOR_ID} case identity, input, or obligation drift at {id}"
            ));
        }
        if process_required != row.process.is_some() {
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
                    return Err(format!("{id} source-catalog row forged process data"));
                }
            }
            Some(ProcessExpectation::ExactStdout(stdout)) => {
                if row.exit_code != Some(0)
                    || row.stdout.as_deref() != Some(stdout)
                    || row.stderr.as_deref() != Some("")
                    || !row.process.as_ref().is_some_and(process_completed)
                {
                    return Err(format!(
                        "{id} claims pass without its exact solver transcript"
                    ));
                }
            }
            Some(ProcessExpectation::Rejection) => {
                if !matches!(row.exit_code, Some(0 | 1))
                    || !row.stdout.as_deref().is_some_and(is_single_error_response)
                    || row.stderr.as_deref() != Some("")
                    || !row.process.as_ref().is_some_and(process_completed)
                {
                    return Err(format!("{id} claims pass without an exact error response"));
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
    fn policy_catalog_is_exact_and_source_field_count_is_closed() {
        assert_eq!(CATALOG.len(), SMTLIB_LOGICS.len());
        assert_eq!(
            CATALOG.iter().map(|entry| entry.name).collect::<Vec<_>>(),
            SMTLIB_LOGICS
        );
        let fields = CATALOG
            .iter()
            .map(|entry| {
                2 + entry.prose.extensions
                    + entry.prose.values
                    + entry.prose.note
                    + entry.prose.notes
            })
            .sum::<usize>();
        assert_eq!(fields, SEMANTIC_FIELD_COUNT);
        let semantic = CATALOG
            .iter()
            .map(|entry| semantic_kinds(entry).len() * 2)
            .sum::<usize>();
        let restrictions = CATALOG
            .iter()
            .map(|entry| {
                let mut kinds = restriction_kinds(entry);
                kinds.sort_by_key(|kind| kind.id());
                kinds.dedup_by_key(|kind| kind.id());
                kinds.len()
            })
            .sum::<usize>();
        assert_eq!(semantic, SEMANTIC_WITNESS_CASE_COUNT);
        assert_eq!(restrictions, RESTRICTION_CASE_COUNT);
        assert_eq!(fields + semantic + restrictions, DETAILED_CASE_COUNT);
        for entry in CATALOG {
            validate_catalog_theory_projection(&entry).expect("theory projection");
            assert!(!semantic_kinds(&entry).is_empty());
        }
    }

    #[test]
    fn error_response_classifier_is_exact() {
        assert!(is_single_error_response("(error \"bad term\")\n"));
        assert!(!is_single_error_response(""));
        assert!(!is_single_error_response("sat\n"));
        assert!(!is_single_error_response(
            "(error \"one\")\n(error \"two\")\n"
        ));
    }
}
