// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Whether pinned Carcara (1.1.0, git 9a352ee) can PARSE the authored problem
//! a certificate is checked against.
//!
//! The certificate an external checker receives is the problem and the proof.
//! The CLI pairs `X.alethe` with the authored `X.smt2`, and the problem-scoped
//! export reprints each authored assertion in its authored spelling, so every
//! construct the author wrote is one Carcara's parser reads. The rest of the
//! surface verdict reads AY's elaborated signature and the proof's terms,
//! where these constructs are gone: `((as mkVec Vec) ...)` elaborates to the
//! constructor application, `is-C` to the tester, `(= x 1)` over a `Real` `x`
//! to `(= x 1.0)`. Measured at 938ec0327 on
//! `benchmarks/smt/model_checker_consumer_quantified_counterexample/typed_vec_pins_cell64_unsat.smt2`:
//! `carcara_surface=supported` beside a problem Carcara stops at with
//! `not a valid qualified operator: 'mkVec'`, and seventeen sibling shapes
//! published `unsat` under `--rigor strict` with `trust_free=yes
//! carcara_surface=supported` on problems Carcara cannot parse.
//!
//! This module replays Carcara's problem parser on each authored command, in
//! the order the executor receives them: its lexer on the command's text
//! ([`lexer`], which also covers the commands and attributes its parser skips),
//! its command set (`parse_problem`), sort grammar ([`sorts`]), builtin
//! operators with their parse-time sort checks ([`operators`]) and term forms
//! ([`terms`]). The first construct it refuses is remembered, and every surface
//! reader discloses it. Within what it reads it leans to `unsupported`: a
//! command, term form, sort or builtin not listed as one Carcara parses is
//! refused, whether or not Carcara would in fact accept it.
//!
//! The state is sticky, because Carcara's `parse_problem` skips `push`, `pop`
//! and `reset` and so reads every command of the file: a construct inside a
//! popped scope, or before a `(reset)`, still stops its parse. For the same
//! reason a command AFTER the query that decides a verdict counts: the CLI's
//! file mode reads the rest of the file ahead at its first query
//! ([`AuthoredProblemSurface::look_ahead`]). A problem command AY itself
//! discards never reaches the parsed-command scan, and never needs to: such a
//! run publishes no certificate (measured at 938ec0327: `unknown`, reason `a
//! problem-contributing command was discarded`); its text is still lexed.
//!
//! Not modelled here:
//!
//! * the checker's own resource limits on a problem it parses: carcara
//!   9a352ee overflows its 8 MiB main-thread stack on some deeply nested terms,
//!   and times out on some large files, both of which parse given the stack or
//!   the time;
//! * commands a caller hands over after a verdict was published (the `-in`
//!   stream and the library API cannot read ahead); a library caller also
//!   hands over no source text, so the spellings only the text shows are
//!   invisible to it;
//! * whether Carcara's verdict on a problem it parses is evidence. It expands
//!   `:named` labels before any scope lookup, and so misreads a binder that
//!   reuses or captures a label; every in-tree runner refuses such a pair
//!   through `ay_core::pinned_carcara`, which reads the exact file pair.

mod lexer;
mod operators;
mod skipped_commands;
mod sorts;
mod source_text;
#[cfg(test)]
mod spelling_tests;
mod terms;
#[cfg(test)]
mod tests;
#[cfg(test)]
mod whole_file_tests;

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_frontend::command::{DatatypeDec, Sort as ParsedSort, SortDec, Term as ParsedTerm};
use ay_frontend::{Command, CommandStream, CommandStreamItem};

use sorts::{resolve, CarcaraSort, SortEntry};
use source_text::TextReading;
use terms::TermCheck;

/// The authored problem's parse state as pinned Carcara would build it, and
/// the first construct its parser refuses.
#[derive(Clone, Default)]
pub(crate) struct AuthoredProblemSurface {
    gap: Option<String>,
    scope: ProblemScope,
    /// The first gap among the commands after the first query, read ahead of
    /// their execution ([`Self::look_ahead`]), and whether that has run.
    ahead_gap: Option<String>,
    looked_ahead: bool,
}

/// What Carcara's parser has read so far: the logic's numeral reading, and
/// every sort, function and `:named` label the problem introduced.
#[derive(Clone, Default)]
pub(super) struct ProblemScope {
    real_only_logic: bool,
    sorts: HashMap<String, SortEntry>,
    functions: HashMap<String, Signature>,
    named: HashMap<String, CarcaraSort>,
    /// The command whose text was just read is one Carcara skips whole
    /// (`define-const`): the `define-fun` AY parsed from it introduces nothing.
    skip_next: bool,
    /// Symbols only such a skipped command defined, for the reason a later
    /// use of one is refused with.
    skipped: HashSet<String>,
}

/// A declared, defined or datatype function symbol. `params` are the sort
/// parameters of a parametric datatype's constructor or selector.
#[derive(Clone)]
pub(super) struct Signature {
    params: Vec<String>,
    args: Vec<CarcaraSort>,
    result: CarcaraSort,
    constructor: bool,
}

impl AuthoredProblemSurface {
    /// The first authored construct pinned Carcara cannot parse, if any.
    pub(crate) fn gap(&self) -> Option<&str> {
        self.gap.as_deref().or(self.ahead_gap.as_deref())
    }

    /// Whether pinned Carcara reads the problem's numerals as `Real`s: its
    /// logic has reals and no integers. Its PROOF parser reads every numeral
    /// as an `Int` all the same, so an `assume` whose `let` binds such a
    /// numeral term is not the premise Carcara parsed from the problem.
    pub(crate) fn reads_numerals_as_reals(&self) -> bool {
        self.scope.real_only_logic
    }

    /// Read one authored command as pinned Carcara's problem parser would.
    pub(crate) fn observe(&mut self, command: &Command) {
        if self.gap.is_none() {
            self.gap = self.scope.command(command).err();
        }
    }

    /// Read the exact source text of one authored command. AY's command
    /// parser normalizes spellings Carcara refuses (`assert-not`, the legacy
    /// `(declare-datatypes () ...)`, a bare-symbol constructor) and reads
    /// `define-const`, which Carcara skips, as a `define-fun`, so only the
    /// text shows them. Read before the parsed command.
    pub(crate) fn observe_source_text(&mut self, source: &str) {
        if self.gap.is_some() {
            return;
        }
        match source_text::read_source_text(source) {
            Ok(reading) => self.scope.skip_next = reading == TextReading::SkippedWhole,
            Err(gap) => self.gap = Some(gap),
        }
    }

    /// Read the text of a command AY dropped because it could not parse it.
    /// Carcara still tokenizes it, so only its lexer is replayed: whether
    /// Carcara's parser would read it is moot, because a dropped command that
    /// contributes to the problem already withholds every later verdict.
    pub(crate) fn observe_dropped_text(&mut self, source: &str) {
        if self.gap.is_none() {
            self.gap = lexer::lexer_gap(source);
        }
    }

    /// Read `remainder`, the authored file from its first query command on,
    /// before that query runs: Carcara parses the whole file, so a construct
    /// after the query that decides a verdict still stops the parse of that
    /// verdict's certificate. Runs once, on a copy of the state so far; the
    /// commands are read again, in order, as they execute.
    pub(crate) fn look_ahead(&mut self, remainder: &str) {
        if self.gap.is_some() || std::mem::replace(&mut self.looked_ahead, true) {
            return;
        }
        let mut ahead = self.clone();
        let mut stream = CommandStream::new(remainder);
        while ahead.gap.is_none() {
            let start = stream.position();
            let Some(item) = stream.next_command() else {
                break;
            };
            let text = remainder.get(start..stream.position()).unwrap_or_default();
            match item {
                CommandStreamItem::Command(command) => {
                    ahead.observe_source_text(text);
                    ahead.observe(&command);
                }
                CommandStreamItem::Error(_) => ahead.observe_dropped_text(text),
            }
        }
        self.ahead_gap = ahead.gap;
    }
}

/// Carcara reads every numeral of a real-only logic's problem as a Real,
/// including the index of `(_ BitVec n)` and of an indexed operator and a
/// `declare-datatypes` arity, which it then requires to be an integer.
pub(super) const REAL_ONLY_NUMERAL: &str = "the problem's logic has reals and no integers, so \
     pinned Carcara 1.1.0 reads every numeral as a Real, including a sort index, an indexed \
     operator's index or a datatype arity, and then refuses it";

/// Why pinned Carcara cannot read `name` as the problem spells it: a word its
/// lexer reserves (AY does not retain whether the input quoted it) or a
/// symbol only the AY/Z3 escape extension spells.
pub(super) fn spelling_gap(name: &str) -> Result<(), String> {
    match ay_proof::carcara_declaration_gap(name, &[], &ay_core::Sort::Bool) {
        Some(reason) => Err(reason),
        None => Ok(()),
    }
}

impl ProblemScope {
    fn command(&mut self, command: &Command) -> Result<(), String> {
        // Carcara skips a `define-const` token by token (its text was lexed),
        // so the symbol is undefined to it wherever the problem uses it, and
        // harmless where it is not. Only the `define-fun` AY parsed from that
        // text is skipped; any other command is read as usual.
        if std::mem::take(&mut self.skip_next) {
            if let Command::DefineFun(name, ..) = command {
                self.skipped.insert(name.clone());
                return Ok(());
            }
        }
        match command {
            Command::SetLogic(logic) => {
                self.real_only_logic =
                    (logic.contains("LRA") || logic.contains("NRA") || logic.contains("RDL"))
                        && !logic.contains('I');
                Ok(())
            }
            Command::DeclareSort(name, arity) => {
                spelling_gap(name)?;
                let arity = usize::try_from(*arity).map_err(|_| "sort arity".to_string())?;
                self.sorts.insert(name.clone(), SortEntry::Declared(arity));
                Ok(())
            }
            Command::DefineSort(name, params, body) => self.define_sort(name, params, body),
            Command::DeclareDatatype(name, datatype) => {
                let arity = datatype.type_params.len();
                self.declare_datatypes(&[(name.as_str(), arity)], std::slice::from_ref(datatype))
            }
            // `parse_datatype_dec` reads the arity with `parse_constant`, so a
            // real-only logic makes it a Real and Carcara panics unwrapping it.
            Command::DeclareDatatypes(..) if self.real_only_logic => Err(REAL_ONLY_NUMERAL.into()),
            Command::DeclareDatatypes(sorts, datatypes) => self.datatypes(sorts, datatypes),
            Command::DeclareFun(name, args, result) => self.declare(name, args, result),
            Command::DeclareConst(name, sort) => self.declare(name, &[], sort),
            Command::DefineFun(name, params, result, body) => {
                self.define(name, params, result, body, false)
            }
            Command::DefineFunRec(name, params, result, body) => {
                self.define(name, params, result, body, true)
            }
            Command::DefineFunsRec(declarations, bodies) => {
                self.define_recursive_group(declarations, bodies)
            }
            Command::Assert(term) => TermCheck::new(self).infer(term).map(drop),
            Command::CheckSatAssuming(terms) if terms.is_empty() => Err(
                "the problem writes `(check-sat-assuming ())`: pinned Carcara 1.1.0 requires a \
                 non-empty assumption list"
                    .to_string(),
            ),
            Command::CheckSatAssuming(terms) => {
                let mut check = TermCheck::new(self);
                terms
                    .iter()
                    .try_for_each(|term| check.infer(term).map(drop))
            }
            other if skipped_commands::carcara_skips(other) => Ok(()),
            // `declare-sort-parameter`, the fixedpoint and SyGuS commands, and
            // any command added later: Carcara skips the command and then
            // meets the symbols it introduced as undefined.
            _ => Err(
                "the problem uses a command pinned Carcara 1.1.0's problem parser skips, \
                 while later commands depend on what it introduces"
                    .to_string(),
            ),
        }
    }

    fn resolve(&self, params: &[String], sort: &ParsedSort) -> Result<CarcaraSort, String> {
        if self.real_only_logic && sorts::has_indexed(sort) {
            return Err(REAL_ONLY_NUMERAL.to_string());
        }
        resolve(&self.sorts, params, sort)
    }

    fn define_sort(
        &mut self,
        name: &str,
        params: &[String],
        body: &ParsedSort,
    ) -> Result<(), String> {
        spelling_gap(name)?;
        params.iter().try_for_each(|param| spelling_gap(param))?;
        let body = self.resolve(params, body)?;
        self.sorts.insert(
            name.to_string(),
            SortEntry::Defined {
                params: params.to_vec(),
                body,
            },
        );
        Ok(())
    }

    fn datatypes(&mut self, sorts: &[SortDec], datatypes: &[DatatypeDec]) -> Result<(), String> {
        if sorts.len() != datatypes.len() {
            return Err("a `declare-datatypes` whose sort and datatype lists differ".to_string());
        }
        let mut heads = Vec::with_capacity(sorts.len());
        for sort in sorts {
            let arity = usize::try_from(sort.arity).map_err(|_| "datatype arity".to_string())?;
            heads.push((sort.name.as_str(), arity));
        }
        self.declare_datatypes(&heads, datatypes)
    }

    /// `parse_declare_datatype(s)`: every datatype sort is declared first, so
    /// mutually recursive fields resolve; then each constructor and selector.
    fn declare_datatypes(
        &mut self,
        heads: &[(&str, usize)],
        datatypes: &[DatatypeDec],
    ) -> Result<(), String> {
        for &(name, arity) in heads {
            spelling_gap(name)?;
            self.sorts
                .insert(name.to_string(), SortEntry::Declared(arity));
        }
        for (&(name, arity), datatype) in heads.iter().zip(datatypes) {
            if datatype.type_params.len() != arity {
                return Err(format!(
                    "datatype `{name}` declares arity {arity} with {} `par` parameter(s)",
                    datatype.type_params.len()
                ));
            }
            let params = &datatype.type_params;
            params.iter().try_for_each(|param| spelling_gap(param))?;
            let datatype_sort = CarcaraSort::Named(
                name.to_string(),
                params.iter().cloned().map(CarcaraSort::Param).collect(),
            );
            for constructor in &datatype.constructors {
                spelling_gap(&constructor.name)?;
                let mut fields = Vec::with_capacity(constructor.selectors.len());
                for selector in &constructor.selectors {
                    spelling_gap(&selector.name)?;
                    let field = self.resolve(params, &selector.sort)?;
                    self.functions.insert(
                        selector.name.clone(),
                        Signature {
                            params: params.clone(),
                            args: vec![datatype_sort.clone()],
                            result: field.clone(),
                            constructor: false,
                        },
                    );
                    fields.push(field);
                }
                self.functions.insert(
                    constructor.name.clone(),
                    Signature {
                        params: params.clone(),
                        args: fields,
                        result: datatype_sort.clone(),
                        constructor: true,
                    },
                );
            }
        }
        Ok(())
    }

    fn declare(
        &mut self,
        name: &str,
        args: &[ParsedSort],
        result: &ParsedSort,
    ) -> Result<(), String> {
        spelling_gap(name)?;
        let args = args
            .iter()
            .map(|sort| self.resolve(&[], sort))
            .collect::<Result<Vec<_>, _>>()?;
        let result = self.resolve(&[], result)?;
        self.functions.insert(
            name.to_string(),
            Signature {
                params: Vec::new(),
                args,
                result,
                constructor: false,
            },
        );
        Ok(())
    }

    /// `define-fun` (the symbol is visible only after its body) and
    /// `define-fun-rec` (visible inside it). Without `--apply-function-defs`
    /// Carcara reads either as a declared function plus a premise, and its
    /// parser checks the body against the declared result sort exactly.
    fn define(
        &mut self,
        name: &str,
        params: &[(String, ParsedSort)],
        result: &ParsedSort,
        body: &ParsedTerm,
        recursive: bool,
    ) -> Result<(), String> {
        let sorts: Vec<ParsedSort> = params.iter().map(|(_, sort)| sort.clone()).collect();
        if recursive {
            self.declare(name, &sorts, result)?;
        }
        self.check_body(name, params, result, body)?;
        if !recursive {
            self.declare(name, &sorts, result)?;
        }
        Ok(())
    }

    fn define_recursive_group(
        &mut self,
        declarations: &[(String, Vec<(String, ParsedSort)>, ParsedSort)],
        bodies: &[ParsedTerm],
    ) -> Result<(), String> {
        if declarations.len() != bodies.len() {
            return Err("a `define-funs-rec` whose declaration and body lists differ".to_string());
        }
        for (name, params, result) in declarations {
            let sorts: Vec<ParsedSort> = params.iter().map(|(_, sort)| sort.clone()).collect();
            self.declare(name, &sorts, result)?;
        }
        for ((name, params, result), body) in declarations.iter().zip(bodies) {
            self.check_body(name, params, result, body)?;
        }
        Ok(())
    }

    fn check_body(
        &mut self,
        name: &str,
        params: &[(String, ParsedSort)],
        result: &ParsedSort,
        body: &ParsedTerm,
    ) -> Result<(), String> {
        let result = self.resolve(&[], result)?;
        let mut bound = Vec::with_capacity(params.len());
        for (param, sort) in params {
            bound.push((param, self.resolve(&[], sort)?));
        }
        let mut check = TermCheck::new(self);
        for (param, sort) in bound {
            check.bind(param, sort)?;
        }
        let body = check.infer(body)?;
        if body == result {
            return Ok(());
        }
        Err(format!(
            "the body of `{name}` has sort {body}, not its declared {result}; pinned Carcara \
             1.1.0 coerces no Int/Real, Bool/Int or bit-vector width"
        ))
    }
}
