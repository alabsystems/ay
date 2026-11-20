// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Independent validation of one exported SAT interpretation.
//!
//! A Z3 `sat` on the original input is only corroboration. This owner instead
//! asks whether the exported interpretation is consistent, and whether that
//! same interpretation admits any violation of the original assertions. The
//! required ordered result is exactly SAT, UNSAT. The first query prevents
//! inconsistent interpretation constraints from passing by vacuous implication.

use super::*;
use ay_frontend::sexp::{parse_sexp, parse_sexps};
use ay_frontend::SExpr;

const MAX_MODEL_BYTES: u64 = 1024 * 1024;
const MAX_SCRIPT_BYTES: usize = 64 * 1024 * 1024;

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
struct Transcript {
    exit_code: Option<i32>,
    stdin_complete: bool,
    timed_out: bool,
    memout: bool,
    stdout_truncated: bool,
    stderr_truncated: bool,
    stdout_utf8: bool,
    stderr_utf8: bool,
    stdout: String,
    stderr: String,
    stdout_sha256: String,
    stderr_sha256: String,
}

impl Transcript {
    fn capture(output: GuardedTranscriptOutput) -> Self {
        Self {
            exit_code: output.status.and_then(|status| status.code()),
            stdin_complete: output.stdin_complete,
            timed_out: output.timed_out,
            memout: output.memout,
            stdout_truncated: output.stdout_truncated,
            stderr_truncated: output.stderr_truncated,
            stdout_utf8: std::str::from_utf8(&output.stdout).is_ok(),
            stderr_utf8: std::str::from_utf8(&output.stderr).is_ok(),
            stdout: String::from_utf8_lossy(&output.stdout).into_owned(),
            stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
            stdout_sha256: sha256_bytes(&output.stdout),
            stderr_sha256: sha256_bytes(&output.stderr),
        }
    }

    fn complete(&self) -> bool {
        self.exit_code == Some(0)
            && self.stdin_complete
            && !self.timed_out
            && !self.memout
            && !self.stdout_truncated
            && !self.stderr_truncated
            && self.stdout_utf8
            && self.stderr_utf8
            && self.stderr.is_empty()
    }

    fn accepts_model(&self) -> bool {
        self.complete() && self.stdout == "sat\nunsat\n"
    }

    fn validate(&self) -> Result<(), String> {
        if self.stdout_utf8 && sha256_bytes(self.stdout.as_bytes()) != self.stdout_sha256
            || self.stderr_utf8 && sha256_bytes(self.stderr.as_bytes()) != self.stderr_sha256
            || self.stdout.len() > MAX_MODEL_BYTES as usize * 3
            || self.stderr.len() > MAX_MODEL_BYTES as usize * 3
        {
            return Err("SAT evidence transcript/hash mismatch".to_string());
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub(super) struct Evidence {
    pub(super) error: Option<String>,
    original: Option<Artifact>,
    #[serde(
        default,
        deserialize_with = "deserialize_checkpoint_field",
        skip_serializing_if = "Option::is_none"
    )]
    scoped: Option<Artifact>,
    producer_input: Option<Artifact>,
    model: Option<Artifact>,
    verification_input: Option<Artifact>,
    producer: Option<Transcript>,
    verifier: Option<Transcript>,
    z3_sha256: String,
    original_assertions: usize,
    #[serde(
        default,
        deserialize_with = "deserialize_checkpoint_field",
        skip_serializing_if = "Option::is_none"
    )]
    original_assumptions: Option<usize>,
    covered_declarations: usize,
}

impl Evidence {
    pub(super) fn accepted(&self) -> bool {
        self.error.is_none()
    }

    pub(super) fn records_accepted_model(&self, query_sha256: &str, z3_sha256: &str) -> bool {
        self.accepted()
            && self.z3_sha256 == z3_sha256
            && self
                .original
                .as_ref()
                .is_some_and(|artifact| artifact.sha256 == query_sha256)
            && self.producer_input.is_some()
            && self.model.is_some()
            && self.verification_input.is_some()
            && self.producer.as_ref().is_some_and(Transcript::complete)
            && self
                .verifier
                .as_ref()
                .is_some_and(Transcript::accepts_model)
    }

    pub(super) fn has_checkpoint_fields(&self) -> bool {
        self.scoped.is_some() || self.original_assumptions.is_some()
    }

    pub(super) fn artifacts(&self) -> [Option<&Artifact>; 4] {
        [
            self.original.as_ref(),
            self.producer_input.as_ref(),
            self.model.as_ref(),
            self.verification_input.as_ref(),
        ]
    }
}

#[derive(Debug)]
struct Signature<'a> {
    raw_name: &'a str,
    argument_sorts: Vec<SExpr>,
    result_sort: SExpr,
    requires_model: bool,
}

#[derive(Debug)]
struct Verification {
    script: String,
    assertions: usize,
    declarations: usize,
}

/// Framing only; the native frontend parser validates every token tree first.
/// Raw slices preserve quoted identifiers, numeric spellings and string escapes
/// instead of reprinting decoded symbols into potentially different syntax.
fn raw_expressions(input: &str) -> Result<Vec<&str>, String> {
    let native = parse_sexps(input).map_err(|error| format!("SAT syntax: {error}"))?;
    let bytes = input.as_bytes();
    let mut index = 0usize;
    let mut spans = Vec::with_capacity(native.len());
    while index < bytes.len() {
        match bytes[index] {
            b';' => {
                while index < bytes.len() && bytes[index] != b'\n' {
                    index += 1;
                }
                continue;
            }
            byte if byte.is_ascii_whitespace() => {
                index += 1;
                continue;
            }
            _ => {}
        }
        let start = index;
        let mut depth = 0usize;
        loop {
            if index >= bytes.len() {
                break;
            }
            match bytes[index] {
                b'"' => {
                    index += 1;
                    loop {
                        if index >= bytes.len() {
                            return Err("unterminated model string".to_string());
                        }
                        if bytes[index] == b'"' {
                            index += 1;
                            if bytes.get(index) == Some(&b'"') {
                                index += 1;
                            } else {
                                break;
                            }
                        } else {
                            index += 1;
                        }
                    }
                    if depth == 0 {
                        break;
                    }
                }
                b'|' => {
                    index += 1;
                    while index < bytes.len() && bytes[index] != b'|' {
                        if bytes[index] == b'\\' {
                            index += 1;
                        }
                        index += 1;
                    }
                    if index >= bytes.len() {
                        return Err("unterminated model identifier".to_string());
                    }
                    index += 1;
                    if depth == 0 {
                        break;
                    }
                }
                b';' if depth > 0 => {
                    while index < bytes.len() && bytes[index] != b'\n' {
                        index += 1;
                    }
                }
                b'(' => {
                    depth += 1;
                    index += 1;
                }
                b')' if depth > 0 => {
                    depth -= 1;
                    index += 1;
                    if depth == 0 {
                        break;
                    }
                }
                b')' => return Err("unexpected closing model delimiter".to_string()),
                byte if depth == 0 && (byte.is_ascii_whitespace() || byte == b';') => break,
                _ => {
                    index += 1;
                }
            }
        }
        spans.push(&input[start..index]);
    }
    if spans.len() != native.len() {
        return Err("raw model spans disagree with native parse".to_string());
    }
    Ok(spans)
}

fn children(raw: &str) -> Result<Vec<&str>, String> {
    let tree = parse_sexp(raw).map_err(|error| format!("SAT syntax: {error}"))?;
    if tree.as_list().is_none() || !raw.starts_with('(') || !raw.ends_with(')') {
        return Err("expected a model/declaration list".to_string());
    }
    raw_expressions(&raw[1..raw.len() - 1])
}

fn symbol(raw: &str) -> Result<String, String> {
    if raw.contains('\\') {
        return Err("escaped symbol names need an independently shared lexer contract".to_string());
    }
    parse_sexp(raw)
        .map_err(|error| error.to_string())?
        .as_symbol()
        .map(str::to_string)
        .ok_or_else(|| "expected a symbol".to_string())
}

fn verification_name(raw: &str) -> Result<String, String> {
    let name = symbol(raw)?;
    // Z3 resolves user functions/macros before builtins. Such a declaration
    // could hijack our added equality, conjunction or counterexample negation.
    // Preserve a refusal until capture-free builtin transport is available.
    if matches!(
        name.as_str(),
        "=" | "and" | "not" | "forall" | "true" | "false"
    ) {
        return Err(format!(
            "declaration {raw} collides with an independent verifier operator"
        ));
    }
    Ok(name)
}

fn supported_sort(raw: &str) -> Result<SExpr, String> {
    let tree = parse_sexp(raw).map_err(|error| error.to_string())?;
    fn supported(tree: &SExpr) -> bool {
        let mut pending = vec![tree];
        while let Some(tree) = pending.pop() {
            if let Some(symbol) = tree.as_symbol() {
                if !matches!(symbol, "Bool" | "Int" | "Real" | "String" | "RoundingMode") {
                    return false;
                }
                continue;
            }
            let Some(items) = tree.as_list() else {
                return false;
            };
            if items.len() == 4 && items[0].is_symbol("_") && items[1].is_symbol("FloatingPoint") {
                if items[2].as_numeral().is_none() || items[3].as_numeral().is_none() {
                    return false;
                }
            } else if items.len() == 3 && items[0].is_symbol("_") && items[1].is_symbol("BitVec") {
                if items[2].as_numeral().is_none() {
                    return false;
                }
            } else if items.len() == 3 && items[0].is_symbol("Array") {
                pending.extend([&items[1], &items[2]]);
            } else if items.len() == 2 && (items[0].is_symbol("Seq") || items[0].is_symbol("RegEx"))
            {
                pending.push(&items[1]);
            } else {
                return false;
            }
        }
        true
    }
    if !supported(&tree) {
        return Err(format!(
            "model sort {raw} needs independent domain/alias transport"
        ));
    }
    Ok(tree)
}

fn same_sorts(left: &[SExpr], right: &[SExpr]) -> bool {
    if left.len() != right.len() {
        return false;
    }
    let mut pending = left.iter().zip(right).collect::<Vec<_>>();
    while let Some((left, right)) = pending.pop() {
        match (left, right) {
            (SExpr::Symbol(left), SExpr::Symbol(right))
            | (SExpr::Numeral(left), SExpr::Numeral(right))
                if left == right => {}
            (SExpr::List(left), SExpr::List(right)) if left.len() == right.len() => {
                pending.extend(left.iter().zip(right))
            }
            _ => return false,
        }
    }
    true
}

fn parameter_sorts(raw: &str) -> Result<Vec<SExpr>, String> {
    children(raw)?
        .iter()
        .map(|parameter| {
            let pair = children(parameter)?;
            if pair.len() != 2 {
                return Err("malformed model function parameter".to_string());
            }
            symbol(pair[0])?;
            supported_sort(pair[1])
        })
        .collect()
}

fn contains_keyword(tree: &SExpr, name: &str) -> bool {
    let mut pending = vec![tree];
    while let Some(node) = pending.pop() {
        match node {
            SExpr::Keyword(value) if value == name => return true,
            SExpr::List(items) => pending.extend(items),
            _ => {}
        }
    }
    false
}

fn body_references_declaration(
    tree: &SExpr,
    declarations: &BTreeMap<String, Signature<'_>>,
    parameters: &BTreeSet<String>,
) -> bool {
    let mut pending = vec![tree];
    while let Some(node) = pending.pop() {
        if let Some(symbol) = node.as_symbol() {
            if declarations.contains_key(symbol) && !parameters.contains(symbol) {
                return true;
            }
        }
        if let Some(items) = node.as_list() {
            pending.extend(items);
        }
    }
    false
}

fn reject_escaped_symbol_tokens(text: &str) -> Result<(), String> {
    enum State {
        Normal,
        String,
        QuotedSymbol,
    }
    let mut state = State::Normal;
    let bytes = text.as_bytes();
    let mut index = 0;
    while index < bytes.len() {
        match (&state, bytes[index]) {
            (State::Normal, b';') => {
                while index < bytes.len() && bytes[index] != b'\n' {
                    index += 1;
                }
                continue;
            }
            (State::Normal, b'"') => state = State::String,
            (State::Normal, b'|') => state = State::QuotedSymbol,
            (State::String, b'"') if bytes.get(index + 1) == Some(&b'"') => {
                index += 2;
                continue;
            }
            (State::String, b'"') => state = State::Normal,
            (State::QuotedSymbol, b'|') => state = State::Normal,
            (State::Normal | State::QuotedSymbol, b'\\') => {
                return Err("escaped symbols require independent lexer equivalence".to_string())
            }
            _ => {}
        }
        index += 1;
    }
    Ok(())
}

fn verification_script<'a>(prefix: &'a str, model: &str) -> Result<Verification, String> {
    // A fresh assertion macro captures the declaration-resolved formula at
    // its original position. Hoisting raw assertions past later definitions
    // would let a later user macro (for example `>`) change their meaning.
    let mut occupied = BTreeSet::new();
    for text in [prefix, model] {
        let trees = parse_sexps(text).map_err(|error| error.to_string())?;
        let mut pending = trees.iter().collect::<Vec<_>>();
        while let Some(tree) = pending.pop() {
            if let Some(name) = tree.as_symbol() {
                occupied.insert(name.to_string());
            }
            if let Some(items) = tree.as_list() {
                pending.extend(items);
            }
        }
    }
    let mut fresh_prefix = "ay_audit_assertion_".to_string();
    while occupied.iter().any(|name| name.starts_with(&fresh_prefix))
        || prefix.contains(&fresh_prefix)
        || model.contains(&fresh_prefix)
    {
        fresh_prefix.push('_');
    }
    reject_escaped_symbol_tokens(prefix)?;
    reject_escaped_symbol_tokens(model)?;
    let mut declarations: BTreeMap<String, Signature<'a>> = BTreeMap::new();
    let mut assertion_terms: Vec<String> = Vec::new();
    let mut declaration_text = String::new();
    let mut queries = 0;
    for raw in raw_expressions(prefix)? {
        let fields = children(raw)?;
        let head = fields.first().ok_or("empty command")?;
        match symbol(head)?.as_str() {
            "set-logic" | "set-option" | "set-info" => {}
            "assert" if fields.len() == 2 => {
                let term = parse_sexp(fields[1]).map_err(|error| error.to_string())?;
                if contains_keyword(&term, ":named") {
                    return Err("named assertion binding transport is not yet supported by model validation".to_string());
                }
                let name = format!("|{fresh_prefix}{}|", assertion_terms.len());
                declaration_text.push_str(&format!("(define-fun {name} () Bool {})\n", fields[1]));
                assertion_terms.push(name);
            }
            "declare-const" if fields.len() == 3 => {
                let name = verification_name(fields[1])?;
                let signature = Signature {
                    raw_name: fields[1],
                    argument_sorts: vec![],
                    result_sort: supported_sort(fields[2])?,
                    requires_model: true,
                };
                if declarations.insert(name, signature).is_some() {
                    return Err("duplicate source declaration".to_string());
                }
                declaration_text.push_str(raw);
                declaration_text.push('\n');
            }
            "declare-fun" if fields.len() == 4 => {
                let name = verification_name(fields[1])?;
                let sorts = children(fields[2])?
                    .into_iter()
                    .map(supported_sort)
                    .collect::<Result<Vec<_>, _>>()?;
                let signature = Signature {
                    raw_name: fields[1],
                    argument_sorts: sorts,
                    result_sort: supported_sort(fields[3])?,
                    requires_model: true,
                };
                if declarations.insert(name, signature).is_some() {
                    return Err("duplicate source declaration".to_string());
                }
                declaration_text.push_str(raw);
                declaration_text.push('\n');
            }
            "define-fun" if fields.len() == 5 => {
                let name = verification_name(fields[1])?;
                let signature = Signature {
                    raw_name: fields[1],
                    argument_sorts: parameter_sorts(fields[2])?,
                    result_sort: supported_sort(fields[3])?,
                    requires_model: false,
                };
                if declarations.insert(name, signature).is_some() {
                    return Err("duplicate source definition".to_string());
                }
                declaration_text.push_str(raw);
                declaration_text.push('\n');
            }
            "define-const" if fields.len() == 4 => {
                let name = verification_name(fields[1])?;
                let signature = Signature {
                    raw_name: fields[1],
                    argument_sorts: vec![],
                    result_sort: supported_sort(fields[2])?,
                    requires_model: false,
                };
                if declarations.insert(name, signature).is_some() {
                    return Err("duplicate source definition".to_string());
                }
                declaration_text.push_str(raw);
                declaration_text.push('\n');
            }
            "check-sat" if fields.len() == 1 => queries += 1,
            command => {
                return Err(format!(
                    "source command {command} lacks independent model transport"
                ))
            }
        }
    }
    if queries != 1 {
        return Err("model verification requires exactly one plain check-sat".to_string());
    }
    let entries = children(model)?;
    let entries = if entries
        .first()
        .is_some_and(|head| symbol(head).ok().as_deref() == Some("model"))
    {
        &entries[1..]
    } else {
        &entries[..]
    };
    let mut seen = BTreeSet::new();
    let mut constraints = String::new();
    for raw in entries {
        let fields = children(raw)?;
        if fields.len() != 5 || symbol(fields[0])? != "define-fun" {
            return Err("only complete define-fun model entries are supported".to_string());
        }
        let name = symbol(fields[1])?;
        if !seen.insert(name.clone()) {
            return Err(format!("duplicate model definition {name}"));
        }
        let signature = declarations.get(&name).ok_or_else(|| {
            format!("model helper/domain symbol {name} has no original declaration")
        })?;
        if !same_sorts(&signature.argument_sorts, &parameter_sorts(fields[2])?)
            || !same_sorts(
                std::slice::from_ref(&signature.result_sort),
                std::slice::from_ref(&supported_sort(fields[3])?),
            )
        {
            return Err(format!(
                "model signature differs from original declaration {name}"
            ));
        }
        let parameters = children(fields[2])?;
        let mut parameter_names = BTreeSet::new();
        let mut raw_names = Vec::new();
        for parameter in parameters {
            let pair = children(parameter)?;
            let name = verification_name(pair[0])?;
            if declarations.contains_key(&name) || !parameter_names.insert(name) {
                return Err(
                    "model parameter shadows a declared function or duplicate parameter"
                        .to_string(),
                );
            }
            raw_names.push(pair[0]);
        }
        let body = parse_sexp(fields[4]).map_err(|error| error.to_string())?;
        if body_references_declaration(&body, &declarations, &parameter_names) {
            return Err("model body depends on original/model symbols; acyclic helper expansion is not yet supported".to_string());
        }
        let application = if raw_names.is_empty() {
            signature.raw_name.to_string()
        } else {
            format!("({} {})", signature.raw_name, raw_names.join(" "))
        };
        // Check the model body at its declared result sort. Equality alone
        // permits Int/Real coercion and could accept an ill-typed model body.
        let helper = format!("|{fresh_prefix}model_{}|", seen.len());
        declaration_text.push_str(&format!(
            "(define-fun {helper} {} {} {})\n",
            fields[2], fields[3], fields[4]
        ));
        let model_application = if raw_names.is_empty() {
            helper
        } else {
            format!("({helper} {})", raw_names.join(" "))
        };
        let equality = format!("(= {application} {model_application})");
        let constraint = if raw_names.is_empty() {
            equality
        } else {
            format!("(forall {} {equality})", fields[2])
        };
        constraints.push_str(&format!("(assert {constraint})\n"));
    }
    for (name, signature) in &declarations {
        if signature.requires_model && !seen.contains(name) {
            return Err(format!("model omits original declaration {name}"));
        }
    }
    let conjunction = if assertion_terms.is_empty() {
        "true".to_string()
    } else {
        format!("(and {})", assertion_terms.join(" "))
    };
    let script = format!("(set-option :print-success false)\n(set-logic ALL)\n{declaration_text}{constraints}(check-sat)\n(push 1)\n(assert (not {conjunction}))\n(check-sat)\n(pop 1)\n");
    if script.len() > MAX_SCRIPT_BYTES {
        return Err("independent model script exceeds transport budget".to_string());
    }
    Ok(Verification {
        script,
        assertions: assertion_terms.len(),
        declarations: seen.len(),
    })
}

fn model_from_output(output: &str) -> Result<&str, String> {
    let mut status = 0;
    let mut model = None;
    for raw in raw_expressions(output)? {
        let tree = parse_sexp(raw).map_err(|error| error.to_string())?;
        if tree.is_symbol("sat") && status == 0 && model.is_none() {
            status += 1;
            continue;
        }
        if tree.is_symbol("success") {
            continue;
        }
        if tree.as_list().is_some() && status == 1 && model.replace(raw).is_none() {
            continue;
        }
        return Err("unexpected or duplicate model response".to_string());
    }
    if status != 1 {
        return Err("model producer did not report exactly one SAT result".to_string());
    }
    model.ok_or_else(|| "model producer omitted its model".to_string())
}

fn producer_script(prefix: &str) -> Result<String, String> {
    let expressions = raw_expressions(prefix)?;
    let last = expressions.last().ok_or("empty query")?;
    let fields = children(last)?;
    if fields.len() != 1 || symbol(fields[0])? != "check-sat" {
        return Err("model producer requires a final plain check-sat".to_string());
    }
    let position = last.as_ptr() as usize - prefix.as_ptr() as usize;
    Ok(format!(
        "{}(set-option :produce-models true)\n{}\n(get-model)\n",
        &prefix[..position],
        last
    ))
}

fn store_artifact(
    base: &Path,
    directory: &Path,
    name: &str,
    bytes: &[u8],
) -> Result<Artifact, String> {
    let path = directory.join(name);
    atomic_write_new(&path, bytes)?;
    let relative = future_relative_output(base, &path)?;
    Ok(Artifact {
        path: relative,
        sha256: sha256_bytes(bytes),
    })
}

fn read_artifact(base: &Path, artifact: &Artifact, max: u64) -> Result<Vec<u8>, String> {
    let path = resolve_relative_evidence_path(base, &artifact.path)?;
    let bytes = read_bounded_bytes(&path, max, "SAT query artifact", true)?;
    if sha256_bytes(&bytes) != artifact.sha256 {
        return Err("SAT query artifact hash mismatch".to_string());
    }
    Ok(bytes)
}

pub(super) fn run(
    prefix: &[u8],
    directory: &Path,
    base: &Path,
    ay: &Path,
    z3: &Path,
    resources: &PlannedResources,
    timeout: Duration,
) -> Evidence {
    let mut evidence = Evidence {
        error: None,
        original: None,
        scoped: None,
        producer_input: None,
        model: None,
        verification_input: None,
        producer: None,
        verifier: None,
        z3_sha256: String::new(),
        original_assertions: 0,
        original_assumptions: None,
        covered_declarations: 0,
    };
    let outcome = (|| {
        evidence.z3_sha256 = canonical_profile()?.z3_overlay.reference_executable.sha256;
        if prefix.len() > MAX_SCRIPT_BYTES {
            return Err("SAT original exceeds the model transport budget".to_string());
        }
        fs::create_dir(directory)
            .map_err(|error| format!("create SAT evidence directory: {error}"))?;
        evidence.original = Some(store_artifact(base, directory, "problem.smt2", prefix)?);
        let prefix = std::str::from_utf8(prefix).map_err(|_| "SAT original input is not UTF-8")?;
        let producer_input = producer_script(prefix)?;
        evidence.producer_input = Some(store_artifact(
            base,
            directory,
            "producer.smt2",
            producer_input.as_bytes(),
        )?);
        let producer_path = directory.join("producer.smt2");
        let producer = Transcript::capture(
            resources
                .run_external_transcript_scrubbed_with_file_limit(
                    ay,
                    [
                        OsString::from("--z3-mode"),
                        OsString::from("--quiet"),
                        producer_path.as_os_str().to_owned(),
                    ],
                    b"",
                    timeout,
                    "official corpus exported SAT model",
                    MAX_SCRIPT_BYTES as u64,
                )
                .map_err(|error| error.to_string())?,
        );
        let model = if producer.complete() {
            model_from_output(&producer.stdout).map(str::to_string)
        } else {
            Err("SAT model producer failed or exceeded its envelope".to_string())
        };
        evidence.producer = Some(producer);
        let model = model?;
        evidence.model = Some(store_artifact(
            base,
            directory,
            "model.smt2",
            model.as_bytes(),
        )?);
        let verifier = verification_script(prefix, &model)?;
        evidence.original_assertions = verifier.assertions;
        evidence.covered_declarations = verifier.declarations;
        evidence.verification_input = Some(store_artifact(
            base,
            directory,
            "verify.smt2",
            verifier.script.as_bytes(),
        )?);
        let verifier_path = directory.join("verify.smt2");
        let output = Transcript::capture(
            resources
                .run_external_transcript_scrubbed(
                    z3,
                    [
                        OsString::from("-smt2"),
                        verifier_path.as_os_str().to_owned(),
                    ],
                    b"",
                    timeout,
                    "official corpus independent model consistency and implication",
                )
                .map_err(|error| error.to_string())?,
        );
        let accepted = output.accepts_model();
        evidence.verifier = Some(output);
        if !accepted {
            return Err("independent model check requires exactly SAT consistency then UNSAT counterexample".to_string());
        }
        Ok(())
    })();
    if let Err(error) = outcome {
        evidence.error = Some(error);
    }
    evidence
}

pub(super) fn validate(evidence: &Evidence, prefix: &[u8], base: &Path) -> Result<(), String> {
    if evidence.z3_sha256 != canonical_profile()?.z3_overlay.reference_executable.sha256 {
        return Err("SAT checker reference digest drift".to_string());
    }
    for transcript in [evidence.producer.as_ref(), evidence.verifier.as_ref()]
        .into_iter()
        .flatten()
    {
        transcript.validate()?;
    }
    for artifact in [
        evidence.original.as_ref(),
        evidence.producer_input.as_ref(),
        evidence.model.as_ref(),
        evidence.verification_input.as_ref(),
    ]
    .into_iter()
    .flatten()
    {
        read_artifact(base, artifact, MAX_SCRIPT_BYTES as u64)?;
    }
    if !evidence.accepted() {
        return Ok(());
    }
    let original = read_artifact(
        base,
        evidence.original.as_ref().ok_or("SAT original missing")?,
        MAX_SCRIPT_BYTES as u64,
    )?;
    if original != prefix {
        return Err("SAT original artifact differs from exact query prefix".to_string());
    }
    let prefix = std::str::from_utf8(prefix).map_err(|_| "SAT prefix is not UTF-8")?;
    let producer_input = read_artifact(
        base,
        evidence
            .producer_input
            .as_ref()
            .ok_or("SAT producer input missing")?,
        MAX_SCRIPT_BYTES as u64,
    )?;
    if producer_input != producer_script(prefix)?.as_bytes() {
        return Err("SAT producer script differs from original query".to_string());
    }
    let producer = evidence
        .producer
        .as_ref()
        .ok_or("SAT producer transcript missing")?;
    if !producer.complete() {
        return Err("SAT producer transcript failed".to_string());
    }
    let model = read_artifact(
        base,
        evidence.model.as_ref().ok_or("SAT model missing")?,
        MAX_MODEL_BYTES,
    )?;
    if model != model_from_output(&producer.stdout)?.as_bytes() {
        return Err("SAT model differs from actual producer output".to_string());
    }
    let model = std::str::from_utf8(&model).map_err(|_| "SAT model is not UTF-8")?;
    let verification = verification_script(prefix, model)?;
    let retained = read_artifact(
        base,
        evidence
            .verification_input
            .as_ref()
            .ok_or("SAT verifier input missing")?,
        MAX_SCRIPT_BYTES as u64,
    )?;
    if retained != verification.script.as_bytes()
        || evidence.original_assertions != verification.assertions
        || evidence.covered_declarations != verification.declarations
    {
        return Err("SAT verifier input/counts differ from independent regeneration".to_string());
    }
    let verifier = evidence
        .verifier
        .as_ref()
        .ok_or("SAT verifier transcript missing")?;
    if !verifier.accepts_model() {
        return Err("SAT consistency/implication evidence failed".to_string());
    }
    Ok(())
}

pub(super) fn replay(
    evidence: &Evidence,
    base: &Path,
    z3: &Path,
    resources: &PlannedResources,
    timeout: Duration,
) -> Result<(), String> {
    if !evidence.accepted() {
        return Ok(());
    }
    let artifact = evidence
        .verification_input
        .as_ref()
        .ok_or("missing SAT replay input")?;
    let bytes = read_artifact(base, artifact, MAX_SCRIPT_BYTES as u64)?;
    let directory = tempfile::tempdir()
        .map_err(|error| format!("create private SAT replay directory: {error}"))?;
    let input = directory.path().join("verify.smt2");
    fs::write(&input, &bytes)
        .map_err(|error| format!("stage authenticated SAT replay: {error}"))?;
    let output = Transcript::capture(
        resources
            .run_external_transcript_scrubbed(
                z3,
                [OsString::from("-smt2"), input.as_os_str().to_owned()],
                b"",
                timeout,
                "official corpus retained independent model replay",
            )
            .map_err(|error| error.to_string())?,
    );
    if !output.accepts_model() {
        return Err("retained SAT interpretation fails independent replay".to_string());
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn completed(stdout: &str) -> Transcript {
        Transcript {
            exit_code: Some(0),
            stdin_complete: true,
            timed_out: false,
            memout: false,
            stdout_truncated: false,
            stderr_truncated: false,
            stdout_utf8: true,
            stderr_utf8: true,
            stdout: stdout.to_string(),
            stderr: String::new(),
            stdout_sha256: sha256_bytes(stdout.as_bytes()),
            stderr_sha256: sha256_bytes(b""),
        }
    }

    #[test]
    fn inconsistent_constraints_never_pass_vacuously() {
        assert!(completed("sat\nunsat\n").accepts_model());
        for output in [
            "unsat\nunsat\n",
            "sat\nsat\n",
            "unknown\nunsat\n",
            "sat\nunknown\n",
            "unsat\n",
            "sat\nunsat\n(error \"oops\")\n",
        ] {
            assert!(!completed(output).accepts_model(), "{output:?}");
        }
        let mut timed_out = completed("sat\nunsat\n");
        timed_out.timed_out = true;
        assert!(!timed_out.accepts_model());
    }

    #[test]
    fn declared_verifier_operators_cannot_make_a_wrong_model_pass() {
        let source = "(declare-const x Int)(define-fun not ((b Bool)) Bool false)(assert (= x 1))(check-sat)";
        let wrong = "(model (define-fun x () Int 0))";
        assert!(verification_script(source, wrong)
            .unwrap_err()
            .contains("collides"));
        for name in ["and", "=", "|not|"] {
            let source = format!("(declare-fun {name} (Bool Bool) Bool)(check-sat)");
            assert!(verification_script(&source, "(model)")
                .unwrap_err()
                .contains("collides"));
        }
    }

    #[test]
    fn original_assertion_binding_is_captured_before_later_macro_shadowing() {
        let source = "(declare-const x Int)(assert (> x 0))(define-fun > ((a Int) (b Int)) Bool true)(check-sat)";
        let script = verification_script(source, "(model (define-fun x () Int (- 1)))")
            .unwrap()
            .script;
        let capture = script.find("(define-fun |ay_audit_assertion_0|").unwrap();
        assert!(capture < script.find("(define-fun >").unwrap());
        assert!(script.contains("(assert (not (and |ay_audit_assertion_0|)))"));
        let collision = "(declare-const ay_audit_assertion_0 Int)(assert (= ay_audit_assertion_0 1))(check-sat)";
        let script = verification_script(
            collision,
            "(model (define-fun ay_audit_assertion_0 () Int 1))",
        )
        .unwrap()
        .script;
        assert!(script.contains("(define-fun |ay_audit_assertion__0| () Bool"));
    }

    #[test]
    fn complete_model_coverage_and_signatures_are_required() {
        let source = "(declare-const x Int)(declare-const y Int)(assert (> x y))(check-sat)";
        for model in [
            "(model (define-fun x () Int 1))",
            "(model (define-fun x () Int 1)(define-fun x () Int 2)(define-fun y () Int 0))",
            "(model (define-fun x () Bool true)(define-fun y () Int 0))",
            "(model (define-fun x () Int y)(define-fun y () Int x))",
            "(model (define-fun x () Int 1)(define-fun y () Int 0)(declare-fun helper () Int))",
        ] {
            assert!(verification_script(source, model).is_err(), "{model}");
        }
        let valid = verification_script(
            source,
            "(model (define-fun x () Int 1)(define-fun y () Int 0))",
        )
        .unwrap();
        assert_eq!(valid.declarations, 2);
        assert_eq!(valid.assertions, 1);
        assert!(ay_frontend::parse(&valid.script).is_ok());
    }

    #[test]
    fn model_verifier_checks_real_reference_semantics_and_result_types() {
        let _resource_guard = resource_test_lock();
        let Some(reference) = ay_test_support::z3::optional_z3("model-verifier semantics") else {
            return;
        };
        let profile = canonical_profile().unwrap();
        let staged = stage_authenticated_executable(
            reference.path(),
            &profile.z3_overlay.reference_executable.sha256,
            "model verifier reference",
        )
        .unwrap();
        let resources = PlannedResources::plan(
            &locate_repo_root().unwrap(),
            1,
            "model-verifier reference controls",
        )
        .unwrap();
        let source = "(declare-const x Int)(assert (= x 1))(check-sat)";
        for (model, accepted) in [
            ("(model (define-fun x () Int 1))", true),
            ("(model (define-fun x () Int 0))", false),
            ("(model (define-fun x () Int 1.0))", false),
        ] {
            let verification = verification_script(source, model).unwrap();
            let output = resources
                .run_external_transcript_scrubbed(
                    &staged.path,
                    ["-in"],
                    verification.script.as_bytes(),
                    Duration::from_secs(2),
                    "independent model control",
                )
                .unwrap();
            assert_eq!(
                Transcript::capture(output).accepts_model(),
                accepted,
                "{model}"
            );
        }
    }

    #[test]
    fn quoted_identifiers_and_string_payloads_keep_their_original_spelling() {
        let source = r#"(declare-const |a b| String)(assert (= |a b| "say ""hi"""))(check-sat)"#;
        let model = r#"(model (define-fun |a b| () String "say ""hi"""))"#;
        let verification = verification_script(source, model).unwrap();
        assert!(ay_frontend::parse(&verification.script).is_ok());
        let changed = source.replace("hi", "bye");
        let other = verification_script(&changed, model).unwrap();
        assert_ne!(
            sha256_bytes(verification.script.as_bytes()),
            sha256_bytes(other.script.as_bytes())
        );
    }

    #[test]
    fn model_function_is_a_total_definition_over_the_original_signature() {
        let source = "(declare-fun f (Int) Int)(assert (= (f 7) 1))(check-sat)";
        let model = "(model (define-fun f ((x!0 Int)) Int (ite (> x!0 0) 1 0)))";
        let verification = verification_script(source, model).unwrap();
        let parsed = ay_frontend::parse(&verification.script).unwrap();
        assert_eq!(
            parsed
                .iter()
                .filter(|command| matches!(command, ay_frontend::Command::CheckSat))
                .count(),
            2
        );
        assert!(verification_script(source, "(model (define-fun f ((x!0 Real)) Int 1))").is_err());
    }

    #[test]
    fn domain_helpers_and_incremental_scope_are_explicitly_unsupported() {
        for source in [
            "(declare-sort U 0)(declare-const x U)(check-sat)",
            "(declare-const x Int)(push 1)(assert (= x 0))(pop 1)(check-sat)",
            "(declare-const p Bool)(assert (! p :named input))(check-sat)",
        ] {
            assert!(verification_script(source, "(model)").is_err());
        }
    }

    #[test]
    fn unknown_missing_and_multiple_models_are_rejected() {
        for output in [
            "unknown\n(model)",
            "sat\n",
            "sat\n(model)(model)",
            "(model)\nsat",
            "sat\nsat\n(model)",
        ] {
            assert!(model_from_output(output).is_err(), "{output}");
        }
        assert_eq!(
            model_from_output("success\nsat\n(model)\n").unwrap(),
            "(model)"
        );
    }

    #[test]
    fn retained_model_cannot_be_reused_for_a_mutated_original_assertion() {
        let original = b"(declare-const x Int)(assert (= x 1))(check-sat)";
        let changed = b"(declare-const x Int)(assert (= x 2))(check-sat)";
        let model = "(model (define-fun x () Int 1))";
        let directory = tempfile::tempdir().unwrap();
        let base = directory.path();
        let generated = verification_script(std::str::from_utf8(original).unwrap(), model).unwrap();
        let evidence = Evidence {
            error: None,
            scoped: None,
            original: Some(store_artifact(base, base, "original.smt2", original).unwrap()),
            producer_input: Some(
                store_artifact(
                    base,
                    base,
                    "producer.smt2",
                    producer_script(std::str::from_utf8(original).unwrap())
                        .unwrap()
                        .as_bytes(),
                )
                .unwrap(),
            ),
            model: Some(store_artifact(base, base, "model.smt2", model.as_bytes()).unwrap()),
            verification_input: Some(
                store_artifact(base, base, "verify.smt2", generated.script.as_bytes()).unwrap(),
            ),
            producer: Some(completed(&format!("sat\n{model}\n"))),
            verifier: Some(completed("sat\nunsat\n")),
            z3_sha256: canonical_profile()
                .unwrap()
                .z3_overlay
                .reference_executable
                .sha256,
            original_assertions: generated.assertions,
            original_assumptions: None,
            covered_declarations: generated.declarations,
        };
        validate(&evidence, original, base).unwrap();
        assert!(evidence.records_accepted_model(&sha256_bytes(original), &evidence.z3_sha256));
        assert!(!evidence.records_accepted_model(&sha256_bytes(changed), &evidence.z3_sha256));
        assert!(validate(&evidence, changed, base)
            .unwrap_err()
            .contains("exact query prefix"));
        fs::write(base.join("model.smt2"), "(model (define-fun x () Int 2))").unwrap();
        assert!(validate(&evidence, original, base)
            .unwrap_err()
            .contains("hash mismatch"));
    }
}
