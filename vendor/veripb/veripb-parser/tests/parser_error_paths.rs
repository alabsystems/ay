//! The error-reporting path must be total.
//!
//! `ParserError::add_file_and_line` used to return `Option<Self>` -- `None`
//! for every variant that already carries its own position -- and all ten of
//! its call sites `.unwrap()`ed the result. That is a partial function
//! unwrapped *while reporting a syntax error*, so any parse helper that
//! produced something other than a bare `TokenError` turned a diagnosis into
//! a panic; under the release profile (`panic = "abort"`) that is a process
//! abort with no verdict at all.
//!
//! It was not hypothetical. `IntegerToken::parse` and `RUPHint::parse` in the
//! version-2 lexer end in `lex.slice().parse()?`, whose `ParseIntError`
//! converts to `ParserError::ParseIntError` -- so a constraint ID that does
//! not fit `isize` reached `add_file_and_line(..).unwrap()` in
//! `Version2Parser::parse`. Measured against `66138cf7`, all four rule
//! spellings below panicked at `legacy_v2/parser.rs:167`; the two `pol`
//! spellings panicked one layer down, at the `slice.parse().unwrap()` that
//! built `Instruction::ConstraintId`. The version-3 parser reported every one
//! of them as an ordinary syntax error throughout.
//!
//! These are parse-time refusals in both cases, so no accepted proof changes
//! verdict: the only behaviour that existed before was the abort.

use std::fs::File;
use std::io::{BufReader, Write};

use veripb_formula::prelude::*;
use veripb_formula::var_name_manager::{VarNameManager, VarNameRecorder};
use veripb_parser::error::ParserError;
use veripb_parser::pbp_parser::legacy_v2::parser::Version2Parser;
use veripb_parser::pbp_parser::proof_processor::ProofProcessor;
use veripb_rules::VeriPBRule;

/// The smallest [`ProofProcessor`] that can drive a parse: it records variable
/// names (the parser needs somewhere to put them) and drops every rule.
#[derive(Default)]
struct Sink {
    var_names: VarNameManager,
}

impl VarNameRecorder for Sink {
    fn add_by_name(&mut self, name: &str) -> VarIdx {
        self.var_names.add_by_name(name)
    }
}

impl ProofProcessor for Sink {
    type Error = ParserError;

    fn process_version(&mut self, _major: i64, _minor: i64) {}

    fn process_var_name(
        &mut self,
        _line: usize,
        name: &str,
        _is_aux_var: bool,
    ) -> Result<usize, Self::Error> {
        Ok(self.var_names.add_by_name(name))
    }

    fn process_rule(&mut self, _line: usize, _rule: VeriPBRule) -> Result<(), Self::Error> {
        Ok(())
    }

    fn should_trace(&self, _line: usize) -> bool {
        false
    }

    fn last_returned_constraint_id(&mut self) -> Option<isize> {
        None
    }
}

/// Run the version-2 parser over a proof body and return its verdict.
fn parse_v2(body: &str) -> Result<(), ParserError> {
    let proof =
        format!("pseudo-Boolean proof version 2.0\nf 1\n{body}\nend pseudo-Boolean proof\n");

    let dir = tempfile::tempdir().expect("failed to create temporary directory");
    let path = dir.path().join("t.pbp");
    let mut file = File::create(&path).expect("failed to create temporary proof");
    file.write_all(proof.as_bytes())
        .expect("failed to write temporary proof");
    file.flush().expect("failed to flush temporary proof");

    let reader = BufReader::new(File::open(&path).expect("failed to reopen temporary proof"));
    let mut sink = Sink::default();
    Version2Parser::new(&mut sink).parse(&path, reader)
}

/// An integer literal the lexeme accepts and `isize` cannot hold.
const TOO_BIG: &str = "99999999999999999999999";

#[test]
fn a_constraint_id_outside_isize_is_a_version_2_syntax_error_not_a_panic() {
    for body in [
        format!("core id {TOO_BIG}"),
        format!("core range {TOO_BIG} 2"),
        format!("del range {TOO_BIG} 2"),
        format!("u >= 1 ; {TOO_BIG}"),
        // Both `pol` spellings: the id consumed inside the instruction loop,
        // and the id left in the buffer when the line ends.
        format!("p {TOO_BIG} +"),
        format!("p 1 {TOO_BIG}"),
    ] {
        let err = parse_v2(&body)
            .err()
            .unwrap_or_else(|| panic!("`{body}` parsed, but {TOO_BIG} does not fit `isize`"));
        assert!(
            matches!(err, ParserError::ParseIntError(_)),
            "`{body}` was rejected with the wrong error: {err}"
        );
    }
}

#[test]
fn a_well_formed_constraint_id_still_parses() {
    // The positive control: the refusal above is about the width of the
    // integer and not about the rule, so nothing that parsed before stops
    // parsing.
    assert!(
        parse_v2("core id 1").is_ok(),
        "`core id 1` must still parse"
    );
    assert!(parse_v2("p 1 +").is_ok(), "`p 1 +` must still parse");
}
