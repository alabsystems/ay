// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! An Alethe proof-**document** parser, and the round-trip self-check built on
//! it.
//!
//! # Why this exists
//!
//! AY's shipping proof gate (`check_proof_partial`) validates the in-memory
//! `Proof` IR. Carcara validates the emitted **text**. Those are different
//! artifacts, and the gap is not theoretical: a differential over 275
//! non-datatype instances found 50 proofs that carcara calls `invalid` and the
//! IR gate accepted — 50 of 50. Half of those defects live in the document
//! layer (an undeclared symbol, an unparseable preamble, a malformed step) and
//! no amount of IR checking can see them, because nothing in AY ever read an
//! Alethe file back.
//!
//! This module reads it back.
//!
//! # Scope discipline
//!
//! This is **not** a general Alethe implementation and must not grow into one.
//! It parses exactly what AY emits and refuses anything carcara would refuse.
//! Every acceptance/rejection decision below is pinned to an empirical probe
//! against `carcara 1.1.0 [git main 9a352ee]`.
//!
//! **Conservative is correct.** Where carcara's behaviour is unknown, or where
//! carcara is *lenient* about something AY never emits, this parser REJECTS. A
//! false accept is precisely the failure mode being fixed; a false reject on a
//! document AY cannot produce costs nothing.
//!
//! Three deliberate places where this parser is STRICTER than carcara:
//!
//! 1. **Out-of-order step attributes.** carcara silently *discards* a
//!    `:premises` that appears before `:rule` — probe `silent_drop` shows an
//!    undefined premise id vanishing with no diagnostic. Silently dropping a
//!    premise turns an unsound step into an accepted one, so this parser makes
//!    it a hard error.
//! 2. **Unknown attributes.** carcara accepts and ignores `:junk (((( x ))))`
//!    (probe `silent_garbage` → `valid`). AY emits exactly five keywords; a
//!    sixth means the printer changed under us.
//! 3. **The `unsat` / extra-paren wrappers.** carcara tolerates them. AY never
//!    emits the paren wrapper, so it is rejected rather than guessed at.
//!
//! And one place it is deliberately *narrower in aim*: it checks the DOCUMENT
//! layer only. `assume`-matches-a-problem-premise and per-rule side conditions
//! are carcara *check*-level failures, not parse-level ones, and reproducing
//! them would mean reimplementing the checker. The one check-level failure
//! cheap enough to keep is structural and is included: a document that never
//! concludes `(cl)`, and a rule name outside the checkable set.

use ay_core::{is_checkable_alethe_rule, CHECKABLE_ALETHE_RULES};
use std::collections::{HashMap, HashSet};
use std::fmt;

// ---------------------------------------------------------------------------
// Source positions
// ---------------------------------------------------------------------------

/// A 0-indexed source position, matching carcara's `(on line L, column C)`
/// convention so diagnostics can be compared side by side.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct Pos {
    /// 0-indexed line.
    pub line: usize,
    /// 0-indexed column.
    pub column: usize,
}

impl fmt::Display for Pos {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(on line {}, column {})", self.line, self.column)
    }
}

// ---------------------------------------------------------------------------
// Defects
// ---------------------------------------------------------------------------

/// A precise, typed document-layer defect.
///
/// Every variant corresponds to something carcara rejects (or, for the three
/// documented strictness upgrades, to something carcara accepts *unsafely*).
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum AletheDefect {
    /// A character that cannot begin any token (carcara: `unexpected
    /// character: '\'`).
    UnexpectedCharacter {
        /// Source position (0-indexed, matching carcara).
        pos: Pos,
        /// The offending character.
        ch: char,
    },
    /// `007` — SMT-LIB numerals may not carry leading zeros.
    LeadingZeroNumeral {
        /// Source position (0-indexed, matching carcara).
        pos: Pos,
        /// The offending numeral as written.
        text: String,
    },
    /// A `|...|` symbol containing a backslash.
    BackslashInQuotedSymbol {
        /// Source position (0-indexed, matching carcara).
        pos: Pos,
    },
    /// End of input inside `|...|`.
    UnterminatedQuotedSymbol {
        /// Source position (0-indexed, matching carcara).
        pos: Pos,
    },
    /// End of input inside `"..."`.
    UnterminatedString {
        /// Source position (0-indexed, matching carcara).
        pos: Pos,
    },
    /// `#b` / `#x` with no digits.
    EmptyBitvectorLiteral {
        /// Source position (0-indexed, matching carcara).
        pos: Pos,
    },
    /// Input ended while a construct was still open.
    UnexpectedEof {
        /// Source position (0-indexed, matching carcara).
        pos: Pos,
        /// What the parser required at that point.
        expected: &'static str,
    },
    /// A declaration command anywhere in the proof file.
    ///
    /// This is the single largest known defect family: carcara's proof parser
    /// accepts **no** declaration command, so AY's `(declare-fun ...)`
    /// preamble makes the whole document unparseable at line 0 before a
    /// single step is read.
    DeclarationCommand {
        /// Source position (0-indexed, matching carcara).
        pos: Pos,
        /// The command name.
        command: String,
    },
    /// A command that is not `assume`, `step`, `anchor` or `define-fun`.
    UnknownCommand {
        /// Source position (0-indexed, matching carcara).
        pos: Pos,
        /// The command name.
        command: String,
    },
    /// Generic syntactic mismatch.
    UnexpectedToken {
        /// Source position (0-indexed, matching carcara).
        pos: Pos,
        /// What the parser required at that point.
        expected: &'static str,
        /// What was found instead.
        found: String,
    },
    /// A known step attribute in the wrong position. carcara silently drops
    /// these; see the module docs for why that is not survivable.
    MisplacedAttribute {
        /// Source position (0-indexed, matching carcara).
        pos: Pos,
        /// The attribute keyword.
        keyword: String,
    },
    /// An attribute keyword AY never emits.
    UnknownAttribute {
        /// Source position (0-indexed, matching carcara).
        pos: Pos,
        /// The attribute keyword.
        keyword: String,
    },
    /// `:premises ()` / `:args ()` / `:discharge ()`.
    EmptySequence {
        /// Source position (0-indexed, matching carcara).
        pos: Pos,
        /// The attribute keyword.
        keyword: String,
    },
    /// A step's clause was not headed by `cl`.
    ClauseNotCl {
        /// Source position (0-indexed, matching carcara).
        pos: Pos,
        /// What was found instead.
        found: String,
    },
    /// A symbol with no declaration reachable from the proof document.
    UndefinedSymbol {
        /// Source position (0-indexed, matching carcara).
        pos: Pos,
        /// The unresolved name.
        name: String,
    },
    /// A sort name the problem never declared.
    UndefinedSort {
        /// Source position (0-indexed, matching carcara).
        pos: Pos,
        /// The unresolved name.
        name: String,
    },
    /// A `:premises` / `:discharge` reference that resolves to nothing in
    /// scope. carcara resolves premises eagerly, so forward and dangling
    /// references are both parse errors.
    UndefinedStepId {
        /// Source position (0-indexed, matching carcara).
        pos: Pos,
        /// The step id.
        id: String,
    },
    /// Two commands sharing an id (assumes and steps share one namespace).
    DuplicateStepId {
        /// Source position (0-indexed, matching carcara).
        pos: Pos,
        /// The step id.
        id: String,
    },
    /// A step id that is not a Symbol token (`1`, `cl`, `step`, ...).
    InvalidStepId {
        /// Source position (0-indexed, matching carcara).
        pos: Pos,
        /// The offending token, rendered.
        token: String,
    },
    /// A rule name outside [`CHECKABLE_ALETHE_RULES`].
    UnknownRule {
        /// Source position (0-indexed, matching carcara).
        pos: Pos,
        /// The rule name.
        rule: String,
    },
    /// A subproof holding fewer than two commands.
    EmptySubproof {
        /// Source position (0-indexed, matching carcara).
        pos: Pos,
        /// The step id.
        id: String,
    },
    /// An `anchor` with no closing step.
    UnclosedSubproof {
        /// The step id.
        id: String,
    },
    /// A subproof whose final command is not a step.
    SubproofLastCommandNotStep {
        /// Source position (0-indexed, matching carcara).
        pos: Pos,
        /// The step id.
        id: String,
    },
    /// `assume` after a `step` inside a subproof.
    AssumeAfterStepInSubproof {
        /// Source position (0-indexed, matching carcara).
        pos: Pos,
        /// The step id.
        id: String,
    },
    /// The document never derives the empty clause.
    NoEmptyClause,
    /// A construct AY must never emit. `match` is the load-bearing case: it
    /// panics carcara (exit 101), which is neither valid, holey nor invalid
    /// and crashes any harness assuming the three-way ladder.
    ForbiddenConstruct {
        /// Source position (0-indexed, matching carcara).
        pos: Pos,
        /// The forbidden construct.
        what: &'static str,
    },
    /// Term nesting past the conservative depth cap.
    TermTooDeep {
        /// Source position (0-indexed, matching carcara).
        pos: Pos,
    },
    /// The document was not valid UTF-8.
    NotUtf8,
}

impl fmt::Display for AletheDefect {
    #[allow(clippy::too_many_lines)]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnexpectedCharacter { pos, ch } => {
                write!(f, "unexpected character: '{ch}' {pos}")
            }
            Self::LeadingZeroNumeral { pos, text } => {
                write!(f, "leading zero in numeral '{text}' {pos}")
            }
            Self::BackslashInQuotedSymbol { pos } => {
                write!(f, "quoted symbol contains backslash {pos}")
            }
            Self::UnterminatedQuotedSymbol { pos } => {
                write!(f, "unexpected EOF in quoted symbol {pos}")
            }
            Self::UnterminatedString { pos } => write!(f, "unexpected EOF in string literal {pos}"),
            Self::EmptyBitvectorLiteral { pos } => write!(f, "empty bitvector literal {pos}"),
            Self::UnexpectedEof { pos, expected } => {
                write!(f, "unexpected EOF, expected {expected} {pos}")
            }
            Self::DeclarationCommand { pos, command } => write!(
                f,
                "declaration command '{command}' is not accepted anywhere in an Alethe proof file {pos}"
            ),
            Self::UnknownCommand { pos, command } => {
                write!(f, "unexpected command: '{command}' {pos}")
            }
            Self::UnexpectedToken {
                pos,
                expected,
                found,
            } => write!(f, "unexpected token: '{found}', expected {expected} {pos}"),
            Self::MisplacedAttribute { pos, keyword } => write!(
                f,
                "step attribute '{keyword}' out of order (carcara silently discards it) {pos}"
            ),
            Self::UnknownAttribute { pos, keyword } => {
                write!(f, "unknown attribute '{keyword}' {pos}")
            }
            Self::EmptySequence { pos, keyword } => {
                write!(f, "expected non-empty sequence after '{keyword}' {pos}")
            }
            Self::ClauseNotCl { pos, found } => {
                write!(f, "step clause must be headed by 'cl', got '{found}' {pos}")
            }
            Self::UndefinedSymbol { pos, name } => {
                write!(f, "identifier '{name}' is not defined {pos}")
            }
            Self::UndefinedSort { pos, name } => write!(f, "sort '{name}' is not defined {pos}"),
            Self::UndefinedStepId { pos, id } => {
                write!(f, "step id '{id}' is not defined {pos}")
            }
            Self::DuplicateStepId { pos, id } => write!(f, "step id '{id}' was repeated {pos}"),
            Self::InvalidStepId { pos, token } => {
                write!(f, "invalid step id token '{token}' {pos}")
            }
            Self::UnknownRule { pos, rule } => write!(f, "unknown rule '{rule}' {pos}"),
            Self::EmptySubproof { pos, id } => write!(f, "subproof '{id}' is empty {pos}"),
            Self::UnclosedSubproof { id } => write!(f, "subproof '{id}' was not closed"),
            Self::SubproofLastCommandNotStep { pos, id } => {
                write!(f, "last command in subproof '{id}' is not a step {pos}")
            }
            Self::AssumeAfterStepInSubproof { pos, id } => write!(
                f,
                "`assume` command '{id}' appears after step inside subproof {pos}"
            ),
            Self::NoEmptyClause => write!(f, "proof does not conclude empty clause"),
            Self::ForbiddenConstruct { pos, what } => {
                write!(f, "construct '{what}' must never be emitted {pos}")
            }
            Self::TermTooDeep { pos } => write!(f, "term nesting exceeds the depth cap {pos}"),
            Self::NotUtf8 => write!(f, "proof document is not valid UTF-8"),
        }
    }
}

impl std::error::Error for AletheDefect {}

impl AletheDefect {
    /// A short, stable machine-readable tag. Used by the offline differential
    /// harness to bucket rejections without string-matching `Display`.
    #[must_use]
    pub fn tag(&self) -> &'static str {
        match self {
            Self::UnexpectedCharacter { .. } => "unexpected-character",
            Self::LeadingZeroNumeral { .. } => "leading-zero-numeral",
            Self::BackslashInQuotedSymbol { .. } => "backslash-in-quoted-symbol",
            Self::UnterminatedQuotedSymbol { .. } => "unterminated-quoted-symbol",
            Self::UnterminatedString { .. } => "unterminated-string",
            Self::EmptyBitvectorLiteral { .. } => "empty-bitvector-literal",
            Self::UnexpectedEof { .. } => "unexpected-eof",
            Self::DeclarationCommand { .. } => "declaration-command",
            Self::UnknownCommand { .. } => "unknown-command",
            Self::UnexpectedToken { .. } => "unexpected-token",
            Self::MisplacedAttribute { .. } => "misplaced-attribute",
            Self::UnknownAttribute { .. } => "unknown-attribute",
            Self::EmptySequence { .. } => "empty-sequence",
            Self::ClauseNotCl { .. } => "clause-not-cl",
            Self::UndefinedSymbol { .. } => "undefined-symbol",
            Self::UndefinedSort { .. } => "undefined-sort",
            Self::UndefinedStepId { .. } => "undefined-step-id",
            Self::DuplicateStepId { .. } => "duplicate-step-id",
            Self::InvalidStepId { .. } => "invalid-step-id",
            Self::UnknownRule { .. } => "unknown-rule",
            Self::EmptySubproof { .. } => "empty-subproof",
            Self::UnclosedSubproof { .. } => "unclosed-subproof",
            Self::SubproofLastCommandNotStep { .. } => "subproof-last-not-step",
            Self::AssumeAfterStepInSubproof { .. } => "assume-after-step",
            Self::NoEmptyClause => "no-empty-clause",
            Self::ForbiddenConstruct { .. } => "forbidden-construct",
            Self::TermTooDeep { .. } => "term-too-deep",
            Self::NotUtf8 => "not-utf8",
        }
    }
}

// ---------------------------------------------------------------------------
// Problem scope
// ---------------------------------------------------------------------------

/// The symbols and sorts a proof document may legitimately refer to without
/// defining them itself.
///
/// carcara resolves every identifier in a proof against the *problem* file's
/// declarations plus the proof's own `define-fun`s. Anything else is
/// `identifier '<x>' is not defined` — a parse error that kills the whole
/// document.
#[derive(Debug, Clone, Default)]
pub struct ProblemScope {
    symbols: HashSet<String>,
    sorts: HashSet<String>,
    /// When true, an unrecognised sort name is tolerated.
    ///
    /// Set only on the in-process path, where AY knows the free symbols of the
    /// problem assertions but does not retain the problem's `declare-sort` /
    /// `declare-datatype` names. Sorts appear only in binder lists and are not
    /// a known defect source; symbols are, and those are always checked.
    open_sorts: bool,
}

impl ProblemScope {
    /// Build a scope from an explicit symbol list (in-process path).
    pub fn from_symbols<I, S>(symbols: I) -> Self
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        Self {
            symbols: symbols.into_iter().map(Into::into).collect(),
            sorts: HashSet::new(),
            open_sorts: true,
        }
    }

    /// Scan an SMT-LIB problem for the names it declares.
    ///
    /// Deliberately a *scanner*, not a parser: it walks balanced s-expressions
    /// and picks out the declaration forms. It never rejects — a problem file
    /// AY already solved is not the artifact under test, and being generous
    /// here can only make the proof check *more* permissive about symbols,
    /// never less. (The dangerous direction is a missing declaration causing a
    /// false REJECT, so erring toward "declared" is right.)
    #[must_use]
    pub fn from_smtlib_source(source: &str) -> Self {
        let mut scope = Self {
            symbols: HashSet::new(),
            sorts: HashSet::new(),
            open_sorts: false,
        };
        for form in top_level_forms(source) {
            scope.absorb_command(&form);
        }
        scope
    }

    /// Symbols known to the scope.
    #[must_use]
    pub fn symbol_count(&self) -> usize {
        self.symbols.len()
    }

    /// Sorts known to the scope.
    #[must_use]
    pub fn sort_count(&self) -> usize {
        self.sorts.len()
    }

    fn contains_symbol(&self, name: &str) -> bool {
        self.symbols.contains(name)
    }

    fn contains_sort(&self, name: &str) -> bool {
        self.open_sorts || self.sorts.contains(name)
    }

    fn absorb_command(&mut self, form: &Sexp) {
        let Sexp::List(items) = form else { return };
        let Some(Sexp::Atom(head)) = items.first() else {
            return;
        };
        match head.as_str() {
            "declare-fun" | "declare-const" | "define-fun" | "define-const" | "define-fun-rec" => {
                if let Some(Sexp::Atom(name)) = items.get(1) {
                    self.symbols.insert(unquote(name));
                }
            }
            "define-funs-rec" => {
                if let Some(Sexp::List(decls)) = items.get(1) {
                    for decl in decls {
                        if let Sexp::List(parts) = decl {
                            if let Some(Sexp::Atom(name)) = parts.first() {
                                self.symbols.insert(unquote(name));
                            }
                        }
                    }
                }
            }
            "declare-sort" | "define-sort" => {
                if let Some(Sexp::Atom(name)) = items.get(1) {
                    self.sorts.insert(unquote(name));
                }
            }
            "declare-datatype" => {
                if let Some(Sexp::Atom(name)) = items.get(1) {
                    self.sorts.insert(unquote(name));
                }
                if let Some(body) = items.get(2) {
                    self.absorb_datatype_body(body);
                }
            }
            "declare-datatypes" => {
                if let Some(Sexp::List(names)) = items.get(1) {
                    for entry in names {
                        match entry {
                            Sexp::Atom(name) => {
                                self.sorts.insert(unquote(name));
                            }
                            Sexp::List(parts) => {
                                if let Some(Sexp::Atom(name)) = parts.first() {
                                    self.sorts.insert(unquote(name));
                                }
                            }
                        }
                    }
                }
                if let Some(Sexp::List(bodies)) = items.get(2) {
                    for body in bodies {
                        self.absorb_datatype_body(body);
                    }
                }
            }
            _ => {}
        }
    }

    /// `((nil) (cons (head Int) (tail List)))`, or the `par` wrapper around it.
    fn absorb_datatype_body(&mut self, body: &Sexp) {
        let Sexp::List(ctors) = body else { return };
        if let Some(Sexp::Atom(first)) = ctors.first() {
            if first == "par" {
                if let Some(inner) = ctors.get(2) {
                    self.absorb_datatype_body(inner);
                }
                return;
            }
        }
        for ctor in ctors {
            match ctor {
                Sexp::Atom(name) => {
                    self.symbols.insert(unquote(name));
                }
                Sexp::List(parts) => {
                    let mut it = parts.iter();
                    if let Some(Sexp::Atom(name)) = it.next() {
                        self.symbols.insert(unquote(name));
                    }
                    for field in it {
                        if let Sexp::List(field_parts) = field {
                            if let Some(Sexp::Atom(sel)) = field_parts.first() {
                                self.symbols.insert(unquote(sel));
                            }
                        }
                    }
                }
            }
        }
    }
}

fn advance(pos: &mut Pos, c: u8) {
    if c == b'\n' {
        pos.line += 1;
        pos.column = 0;
    } else {
        pos.column += 1;
    }
}

fn unquote(name: &str) -> String {
    name.strip_prefix('|')
        .and_then(|rest| rest.strip_suffix('|'))
        .unwrap_or(name)
        .to_string()
}

/// Minimal s-expression used only by the problem scanner.
#[derive(Debug, Clone)]
enum Sexp {
    Atom(String),
    List(Vec<Sexp>),
}

/// Split an SMT-LIB source into top-level balanced forms. Tolerant by design:
/// unbalanced tails are dropped rather than reported.
fn top_level_forms(source: &str) -> Vec<Sexp> {
    let bytes = source.as_bytes();
    let mut i = 0usize;
    let mut stack: Vec<Vec<Sexp>> = Vec::new();
    let mut out = Vec::new();
    while i < bytes.len() {
        let c = bytes[i];
        match c {
            b';' => {
                while i < bytes.len() && bytes[i] != b'\n' {
                    i += 1;
                }
            }
            b'(' => {
                stack.push(Vec::new());
                i += 1;
            }
            b')' => {
                i += 1;
                if let Some(items) = stack.pop() {
                    let node = Sexp::List(items);
                    if let Some(parent) = stack.last_mut() {
                        parent.push(node);
                    } else {
                        out.push(node);
                    }
                }
            }
            b'|' => {
                let start = i;
                i += 1;
                while i < bytes.len() && bytes[i] != b'|' {
                    i += 1;
                }
                i = (i + 1).min(bytes.len());
                push_atom(&mut stack, &mut out, &source[start..i]);
            }
            b'"' => {
                let start = i;
                i += 1;
                while i < bytes.len() {
                    if bytes[i] == b'"' {
                        if i + 1 < bytes.len() && bytes[i + 1] == b'"' {
                            i += 2;
                            continue;
                        }
                        i += 1;
                        break;
                    }
                    i += 1;
                }
                push_atom(&mut stack, &mut out, &source[start..i.min(bytes.len())]);
            }
            c if c.is_ascii_whitespace() => i += 1,
            _ => {
                let start = i;
                while i < bytes.len()
                    && !bytes[i].is_ascii_whitespace()
                    && !matches!(bytes[i], b'(' | b')' | b';' | b'|' | b'"')
                {
                    i += 1;
                }
                push_atom(&mut stack, &mut out, &source[start..i]);
            }
        }
    }
    out
}

fn push_atom(stack: &mut [Vec<Sexp>], out: &mut Vec<Sexp>, text: &str) {
    let node = Sexp::Atom(text.to_string());
    if let Some(parent) = stack.last_mut() {
        parent.push(node);
    } else {
        out.push(node);
    }
}

// ---------------------------------------------------------------------------
// Built-in vocabulary
// ---------------------------------------------------------------------------

/// Operator names carcara resolves without a declaration.
///
/// Transcribed from `Operator` / `ParamOperator` in the carcara source tree.
/// Being generous here can only cause a false ACCEPT for a head symbol AY
/// never emits; AY's printed operator vocabulary is `not and or => = ite
/// distinct < <= > >= + - * / select store` plus `(_ is C)`, so the extra
/// names are inert. They are present so that a future AY that emits, say,
/// bit-vector terms is not falsely rejected.
const BUILTIN_OPERATORS: &[&str] = &[
    "true",
    "false",
    "not",
    "=>",
    "and",
    "or",
    "xor",
    "=",
    "distinct",
    "ite",
    "+",
    "-",
    "*",
    "div",
    "/",
    "mod",
    "abs",
    "<",
    ">",
    "<=",
    ">=",
    "to_real",
    "to_int",
    "is_int",
    "select",
    "store",
    "str.++",
    "str.len",
    "str.<",
    "str.<=",
    "str.at",
    "str.substr",
    "str.prefixof",
    "str.suffixof",
    "str.contains",
    "str.indexof",
    "str.replace",
    "str.replace_all",
    "str.replace_re",
    "str.replace_re_all",
    "str.is_digit",
    "str.to_code",
    "str.from_code",
    "str.to_int",
    "str.from_int",
    "str.to_re",
    "str.in_re",
    "re.none",
    "re.all",
    "re.allchar",
    "re.++",
    "re.union",
    "re.inter",
    "re.*",
    "re.comp",
    "re.diff",
    "re.+",
    "re.opt",
    "re.range",
    "bvnot",
    "bvneg",
    "bvand",
    "bvor",
    "bvadd",
    "bvmul",
    "bvudiv",
    "bvurem",
    "bvshl",
    "bvlshr",
    "bvult",
    "concat",
    "bvnand",
    "bvnor",
    "bvxor",
    "bvxnor",
    "bvcomp",
    "bvsub",
    "bvsdiv",
    "bvsrem",
    "bvsmod",
    "bvashr",
    "bvule",
    "bvugt",
    "bvuge",
    "bvslt",
    "bvsle",
    "bvsgt",
    "bvsge",
    "ubv_to_int",
    "sbv_to_int",
    "int.pow2",
    "int.ispow2",
    "int.log2",
];

/// Indexed identifier heads carcara resolves: `(_ NAME idx+)`.
const BUILTIN_INDEXED: &[&str] = &[
    "extract",
    "zero_extend",
    "sign_extend",
    "rotate_left",
    "rotate_right",
    "repeat",
    "bv",
    "int_to_bv",
    "re.^",
    "re.loop",
    "is",
    "const",
];

/// Sort names available without a `declare-sort`.
const BUILTIN_SORTS: &[&str] = &["Bool", "Int", "Real", "String", "RegLan", "RoundingMode"];

/// Indexed sort constructors: `(_ BitVec n)`, `(_ FloatingPoint e s)`.
const BUILTIN_INDEXED_SORTS: &[&str] = &["BitVec", "FloatingPoint"];

/// Parametric sort constructors: `(Array s s)`, `(Seq s)`.
const BUILTIN_SORT_CONSTRUCTORS: &[&str] = &["Array", "Seq"];

/// Commands SMT-LIB defines that a *proof* file must never contain. Split out
/// from `UnknownCommand` because the declaration family is the known defect —
/// naming it in the diagnostic is the whole point.
const DECLARATION_COMMANDS: &[&str] = &[
    "declare-fun",
    "declare-const",
    "declare-sort",
    "declare-datatype",
    "declare-datatypes",
    "define-sort",
    "define-fun-rec",
    "define-funs-rec",
    "define-const",
];

/// The maximum term nesting this parser will follow. AY's deepest observed
/// document nests to 109. Anything past the cap is REJECTED rather than
/// risking a stack overflow — a crash is not a verdict.
const MAX_TERM_DEPTH: usize = 4096;

// ---------------------------------------------------------------------------
// Lexer
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq)]
enum Tok {
    Open,
    Close,
    Symbol(String),
    Keyword(String),
    Numeral(String),
    Decimal(String),
    StringLit(String),
    BitVec(String),
    Eof,
}

impl Tok {
    fn describe(&self) -> String {
        match self {
            Self::Open => "(".to_string(),
            Self::Close => ")".to_string(),
            Self::Symbol(s) => s.clone(),
            Self::Keyword(k) => k.clone(),
            Self::Numeral(n) | Self::Decimal(n) => n.clone(),
            Self::StringLit(s) => format!("\"{s}\""),
            Self::BitVec(b) => b.clone(),
            Self::Eof => "EOF".to_string(),
        }
    }
}

fn is_simple_symbol_char(c: u8) -> bool {
    c.is_ascii_alphanumeric()
        || matches!(
            c,
            b'~' | b'!'
                | b'@'
                | b'$'
                | b'%'
                | b'^'
                | b'&'
                | b'*'
                | b'_'
                | b'+'
                | b'='
                | b'<'
                | b'>'
                | b'.'
                | b'?'
                | b'/'
                | b'-'
        )
}

struct Lexer<'a> {
    src: &'a [u8],
    text: &'a str,
    idx: usize,
    line: usize,
    col: usize,
    /// Line offset applied to every reported position, so that a command
    /// extracted from a larger document reports document coordinates.
    line_base: usize,
    col_base: usize,
}

impl<'a> Lexer<'a> {
    fn new(text: &'a str, line_base: usize, col_base: usize) -> Self {
        Self {
            src: text.as_bytes(),
            text,
            idx: 0,
            line: 0,
            col: 0,
            line_base,
            col_base,
        }
    }

    fn pos(&self) -> Pos {
        Pos {
            line: self.line_base + self.line,
            column: if self.line == 0 {
                self.col_base + self.col
            } else {
                self.col
            },
        }
    }

    fn bump(&mut self) {
        if self.idx < self.src.len() {
            if self.src[self.idx] == b'\n' {
                self.line += 1;
                self.col = 0;
            } else {
                self.col += 1;
            }
            self.idx += 1;
        }
    }

    fn peek(&self) -> Option<u8> {
        self.src.get(self.idx).copied()
    }

    fn skip_trivia(&mut self) {
        loop {
            match self.peek() {
                Some(c) if c.is_ascii_whitespace() => self.bump(),
                Some(b';') => {
                    while let Some(c) = self.peek() {
                        if c == b'\n' {
                            break;
                        }
                        self.bump();
                    }
                }
                _ => return,
            }
        }
    }

    fn next_token(&mut self) -> Result<(Tok, Pos), AletheDefect> {
        self.skip_trivia();
        let pos = self.pos();
        let Some(c) = self.peek() else {
            return Ok((Tok::Eof, pos));
        };
        match c {
            b'(' => {
                self.bump();
                Ok((Tok::Open, pos))
            }
            b')' => {
                self.bump();
                Ok((Tok::Close, pos))
            }
            b'|' => self.lex_quoted_symbol(pos),
            b'"' => self.lex_string(pos),
            b'#' => self.lex_bitvector(pos),
            b':' => {
                let start = self.idx;
                self.bump();
                while matches!(self.peek(), Some(k) if is_simple_symbol_char(k)) {
                    self.bump();
                }
                Ok((Tok::Keyword(self.text[start..self.idx].to_string()), pos))
            }
            b'0'..=b'9' => self.lex_number(pos, false),
            b'-' if matches!(self.src.get(self.idx + 1), Some(d) if d.is_ascii_digit()) => {
                // carcara lexes bare `-3` and `-3.5` as literals, not symbols
                // (probes `tm_bareneg`, `tm_baregnegdec`).
                self.bump();
                self.lex_number(pos, true)
            }
            c if is_simple_symbol_char(c) => {
                let start = self.idx;
                while matches!(self.peek(), Some(k) if is_simple_symbol_char(k)) {
                    self.bump();
                }
                Ok((Tok::Symbol(self.text[start..self.idx].to_string()), pos))
            }
            c => Err(AletheDefect::UnexpectedCharacter {
                pos,
                ch: char::from(c),
            }),
        }
    }

    fn lex_quoted_symbol(&mut self, pos: Pos) -> Result<(Tok, Pos), AletheDefect> {
        self.bump(); // opening |
        let start = self.idx;
        loop {
            match self.peek() {
                None => return Err(AletheDefect::UnterminatedQuotedSymbol { pos }),
                Some(b'\\') => return Err(AletheDefect::BackslashInQuotedSymbol { pos }),
                Some(b'|') => {
                    let body = self.text[start..self.idx].to_string();
                    self.bump();
                    return Ok((Tok::Symbol(body), pos));
                }
                Some(_) => self.bump(),
            }
        }
    }

    fn lex_string(&mut self, pos: Pos) -> Result<(Tok, Pos), AletheDefect> {
        self.bump(); // opening "
        let start = self.idx;
        loop {
            match self.peek() {
                None => return Err(AletheDefect::UnterminatedString { pos }),
                Some(b'"') => {
                    if self.src.get(self.idx + 1) == Some(&b'"') {
                        self.bump();
                        self.bump();
                        continue;
                    }
                    let body = self.text[start..self.idx].to_string();
                    self.bump();
                    return Ok((Tok::StringLit(body), pos));
                }
                Some(_) => self.bump(),
            }
        }
    }

    fn lex_bitvector(&mut self, pos: Pos) -> Result<(Tok, Pos), AletheDefect> {
        let start = self.idx;
        self.bump(); // '#'
        let radix = match self.peek() {
            Some(b'b') => 2,
            Some(b'x') => 16,
            _ => {
                return Err(AletheDefect::UnexpectedCharacter { pos, ch: '#' });
            }
        };
        self.bump();
        let digits_start = self.idx;
        while let Some(c) = self.peek() {
            let ok = if radix == 2 {
                matches!(c, b'0' | b'1')
            } else {
                c.is_ascii_hexdigit()
            };
            if !ok {
                break;
            }
            self.bump();
        }
        if self.idx == digits_start {
            return Err(AletheDefect::EmptyBitvectorLiteral { pos });
        }
        Ok((Tok::BitVec(self.text[start..self.idx].to_string()), pos))
    }

    fn lex_number(&mut self, pos: Pos, negative: bool) -> Result<(Tok, Pos), AletheDefect> {
        let start = self.idx;
        while matches!(self.peek(), Some(d) if d.is_ascii_digit()) {
            self.bump();
        }
        let int_part = &self.text[start..self.idx];
        let is_decimal = self.peek() == Some(b'.')
            && matches!(self.src.get(self.idx + 1), Some(d) if d.is_ascii_digit());
        if is_decimal {
            self.bump();
            while matches!(self.peek(), Some(d) if d.is_ascii_digit()) {
                self.bump();
            }
        }
        let text = &self.text[start..self.idx];
        if int_part.len() > 1 && int_part.starts_with('0') {
            return Err(AletheDefect::LeadingZeroNumeral {
                pos,
                text: text.to_string(),
            });
        }
        let rendered = if negative {
            format!("-{text}")
        } else {
            text.to_string()
        };
        if is_decimal {
            Ok((Tok::Decimal(rendered), pos))
        } else {
            Ok((Tok::Numeral(rendered), pos))
        }
    }
}

// ---------------------------------------------------------------------------
// Document checker
// ---------------------------------------------------------------------------

/// What a successful check observed. Reported so callers can assert the check
/// actually ran over content rather than silently over nothing.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct AletheDocumentReport {
    /// Total commands parsed.
    pub commands: usize,
    /// `step` commands.
    pub steps: usize,
    /// `assume` commands.
    pub assumes: usize,
    /// `anchor` commands.
    pub anchors: usize,
    /// `define-fun` commands.
    pub define_funs: usize,
    /// Distinct rule names seen.
    pub distinct_rules: usize,
}

/// One open subproof.
struct Frame {
    anchor_id: String,
    anchor_pos: Pos,
    /// Ids introduced directly in this frame, retired from visibility on pop.
    ids: Vec<String>,
    /// Variables bound by the anchor's `:args`.
    bound_vars: Vec<String>,
    commands: usize,
    seen_step: bool,
}

/// Incremental, streaming document checker.
///
/// Feed the emitted bytes in as they are produced (they may split anywhere,
/// including mid-token) and call [`AletheDocumentChecker::finish`]. Memory is
/// bounded by the largest single command plus the id table — the exporter
/// streams precisely to avoid materializing a 305 MB document, and this must
/// not undo that.
pub struct AletheDocumentChecker {
    scope: ProblemScope,
    /// Symbols bound by proof-level `define-fun`, with arity.
    defines: HashMap<String, usize>,
    /// Ids currently visible for premise resolution.
    visible_ids: HashSet<String>,
    /// Ids retired by a closed subproof. Kept for global uniqueness only.
    /// Tiny in practice: 31 anchors across a 2.2 M-command corpus.
    retired_ids: HashSet<String>,
    frames: Vec<Frame>,
    rules_seen: HashSet<String>,
    report: AletheDocumentReport,
    concluded_empty_clause: bool,
    saw_top_level_step: bool,

    // Incremental splitting state. The splitter re-scans the unconsumed
    // prefix on every push, so it holds no partial-scan state: `buf` never
    // exceeds one command (AY's largest observed single step is 7.6 MB).
    buf: String,
    /// Bytes carried over from a chunk that split a UTF-8 sequence.
    pending_bytes: Vec<u8>,
    /// Absolute position of `buf[0]`.
    buf_pos: Pos,
    started: bool,
    failed: Option<AletheDefect>,
}

impl AletheDocumentChecker {
    /// Start a check against `scope`.
    #[must_use]
    pub fn new(scope: ProblemScope) -> Self {
        Self {
            scope,
            defines: HashMap::new(),
            visible_ids: HashSet::new(),
            retired_ids: HashSet::new(),
            frames: Vec::new(),
            rules_seen: HashSet::new(),
            report: AletheDocumentReport::default(),
            concluded_empty_clause: false,
            saw_top_level_step: false,
            buf: String::new(),
            pending_bytes: Vec::new(),
            buf_pos: Pos::default(),
            started: false,
            failed: None,
        }
    }

    /// Feed the next chunk of emitted proof text.
    ///
    /// # Errors
    ///
    /// Returns the first defect found. Once a defect is returned the checker
    /// latches it: further pushes are no-ops and [`Self::finish`] repeats it.
    pub fn push_bytes(&mut self, chunk: &[u8]) -> Result<(), AletheDefect> {
        if let Some(defect) = &self.failed {
            return Err(defect.clone());
        }
        let mut bytes = std::mem::take(&mut self.pending_bytes);
        bytes.extend_from_slice(chunk);
        let text = match std::str::from_utf8(&bytes) {
            Ok(text) => text.to_string(),
            Err(error) => {
                let good = error.valid_up_to();
                // A trailing incomplete sequence is a chunk boundary, not a
                // defect; anything else is genuinely not UTF-8.
                if error.error_len().is_some() {
                    return Err(self.latch(AletheDefect::NotUtf8));
                }
                self.pending_bytes = bytes[good..].to_vec();
                // SAFETY-free: validated prefix.
                match std::str::from_utf8(&bytes[..good]) {
                    Ok(text) => text.to_string(),
                    Err(_) => return Err(self.latch(AletheDefect::NotUtf8)),
                }
            }
        };
        self.push_str_inner(&text)
    }

    /// Convenience wrapper over [`Self::push_bytes`] for `&str` input.
    ///
    /// # Errors
    ///
    /// See [`Self::push_bytes`].
    pub fn push_str(&mut self, chunk: &str) -> Result<(), AletheDefect> {
        if let Some(defect) = &self.failed {
            return Err(defect.clone());
        }
        self.push_str_inner(chunk)
    }

    fn latch(&mut self, defect: AletheDefect) -> AletheDefect {
        if self.failed.is_none() {
            self.failed = Some(defect.clone());
        }
        defect
    }

    fn push_str_inner(&mut self, chunk: &str) -> Result<(), AletheDefect> {
        self.buf.push_str(chunk);
        // Cut off every complete top-level segment now available.
        loop {
            let Some((segment, pos)) = self.take_segment() else {
                return Ok(());
            };
            if let Err(defect) = self.consume_segment(&segment, pos) {
                return Err(self.latch(defect));
            }
        }
    }

    /// Drain leading trivia, then, if `buf` holds a complete top-level
    /// segment, drain and return it with its absolute start position.
    ///
    /// Holds no cross-call scan state: an incomplete segment is simply left in
    /// `buf` and re-scanned when more bytes arrive. `buf` therefore never
    /// exceeds one command.
    fn take_segment(&mut self) -> Option<(String, Pos)> {
        // 1. Skip whitespace and comments.
        let mut i = 0usize;
        let mut pos = self.buf_pos;
        {
            let bytes = self.buf.as_bytes();
            while i < bytes.len() {
                let c = bytes[i];
                if c.is_ascii_whitespace() {
                    advance(&mut pos, c);
                    i += 1;
                } else if c == b';' {
                    let mut j = i;
                    while j < bytes.len() && bytes[j] != b'\n' {
                        j += 1;
                    }
                    if j == bytes.len() {
                        break; // comment may continue in the next chunk
                    }
                    while i <= j {
                        advance(&mut pos, bytes[i]);
                        i += 1;
                    }
                } else {
                    break;
                }
            }
        }
        if i > 0 {
            self.buf.drain(..i);
            self.buf_pos = pos;
        }
        let bytes = self.buf.as_bytes();
        if bytes.is_empty() {
            return None;
        }
        let start = self.buf_pos;

        // 2a. A bare atom at top level (only the tolerated `unsat` prefix).
        if bytes[0] != b'(' {
            let mut j = 0usize;
            while j < bytes.len()
                && !bytes[j].is_ascii_whitespace()
                && bytes[j] != b'('
                && bytes[j] != b')'
            {
                j += 1;
            }
            if j == bytes.len() {
                return None; // the atom may continue in the next chunk
            }
            let segment = self.buf[..j].to_string();
            let mut end = self.buf_pos;
            for &c in &bytes[..j] {
                advance(&mut end, c);
            }
            self.buf.drain(..j);
            self.buf_pos = end;
            return Some((segment, start));
        }

        // 2b. A parenthesized command: walk to the matching close.
        let mut depth = 0usize;
        let mut in_quoted = false;
        let mut in_string = false;
        let mut in_comment = false;
        let mut end = self.buf_pos;
        for (k, &c) in bytes.iter().enumerate() {
            if in_comment {
                if c == b'\n' {
                    in_comment = false;
                }
            } else if in_quoted {
                if c == b'|' {
                    in_quoted = false;
                }
            } else if in_string {
                if c == b'"' {
                    in_string = false;
                }
            } else {
                match c {
                    b';' => in_comment = true,
                    b'|' => in_quoted = true,
                    b'"' => in_string = true,
                    b'(' => depth += 1,
                    b')' => depth = depth.saturating_sub(1),
                    _ => {}
                }
            }
            advance(&mut end, c);
            if depth == 0 && !in_quoted && !in_string && !in_comment {
                let segment = self.buf[..=k].to_string();
                self.buf.drain(..=k);
                self.buf_pos = end;
                return Some((segment, start));
            }
        }
        None
    }

    fn consume_segment(&mut self, segment: &str, pos: Pos) -> Result<(), AletheDefect> {
        if !segment.starts_with('(') {
            // The only bare atom carcara tolerates before the commands.
            if segment == "unsat" && !self.started {
                self.started = true;
                return Ok(());
            }
            return Err(AletheDefect::UnexpectedToken {
                pos,
                expected: "'(' starting a command",
                found: segment.to_string(),
            });
        }
        self.started = true;
        self.parse_command(segment, pos.line, pos.column)
    }

    /// Conclude the check.
    ///
    /// # Errors
    ///
    /// Returns a defect for anything left dangling: an unclosed subproof,
    /// an unterminated token, a document that never derives `(cl)`.
    pub fn finish(mut self) -> Result<AletheDocumentReport, AletheDefect> {
        if let Some(defect) = self.failed {
            return Err(defect);
        }
        if !self.pending_bytes.is_empty() {
            return Err(AletheDefect::NotUtf8);
        }
        let trailing = self.buf.trim();
        if !trailing.is_empty() {
            // Prefer the precise lexical diagnosis when the leftover is a
            // half-open token (`|sym`, `"str`, `#b`) rather than a merely
            // truncated command — that is what carcara reports.
            let mut lexer = Lexer::new(&self.buf, self.buf_pos.line, self.buf_pos.column);
            loop {
                match lexer.next_token() {
                    Ok((Tok::Eof, _)) => break,
                    Ok(_) => {}
                    Err(defect) => return Err(defect),
                }
            }
            return Err(AletheDefect::UnexpectedEof {
                pos: self.buf_pos,
                expected: "a complete command",
            });
        }
        if let Some(frame) = self.frames.last() {
            return Err(AletheDefect::UnclosedSubproof {
                id: frame.anchor_id.clone(),
            });
        }
        if !self.concluded_empty_clause || !self.saw_top_level_step {
            return Err(AletheDefect::NoEmptyClause);
        }
        self.report.distinct_rules = self.rules_seen.len();
        Ok(self.report)
    }

    // -- command layer ------------------------------------------------------

    fn parse_command(&mut self, text: &str, line: usize, col: usize) -> Result<(), AletheDefect> {
        let mut lexer = Lexer::new(text, line, col);
        let (open, open_pos) = lexer.next_token()?;
        if open != Tok::Open {
            return Err(AletheDefect::UnexpectedToken {
                pos: open_pos,
                expected: "'('",
                found: open.describe(),
            });
        }
        let (head, head_pos) = lexer.next_token()?;
        let Tok::Symbol(name) = head else {
            return Err(AletheDefect::UnexpectedToken {
                pos: head_pos,
                expected: "a command name",
                found: head.describe(),
            });
        };
        self.report.commands += 1;
        if let Some(frame) = self.frames.last_mut() {
            frame.commands += 1;
        }
        match name.as_str() {
            "assume" => self.parse_assume(&mut lexer, head_pos),
            "step" => self.parse_step(&mut lexer, head_pos),
            "anchor" => self.parse_anchor(&mut lexer, head_pos),
            "define-fun" => self.parse_define_fun(&mut lexer, head_pos),
            other if DECLARATION_COMMANDS.contains(&other) => {
                Err(AletheDefect::DeclarationCommand {
                    pos: head_pos,
                    command: other.to_string(),
                })
            }
            other => Err(AletheDefect::UnknownCommand {
                pos: head_pos,
                command: other.to_string(),
            }),
        }
    }

    fn parse_assume(&mut self, lexer: &mut Lexer<'_>, head_pos: Pos) -> Result<(), AletheDefect> {
        let id = self.take_id(lexer)?;
        // `assume` after a step INSIDE a subproof is a parse error in carcara
        // (probe `as_after_step_sub`); at top level it is a warning only
        // (`as_after_step_top`). Mirror exactly.
        if let Some(frame) = self.frames.last() {
            // An `assume` carrying the anchor's id would close the subproof
            // with a non-step (probe `sp_allassume`).
            if frame.anchor_id == id.0 {
                return Err(AletheDefect::SubproofLastCommandNotStep {
                    pos: head_pos,
                    id: id.0,
                });
            }
            if frame.seen_step {
                return Err(AletheDefect::AssumeAfterStepInSubproof {
                    pos: head_pos,
                    id: id.0,
                });
            }
        }
        self.define_id(id.0, id.1)?;
        let (tok, pos) = lexer.next_token()?;
        if tok == Tok::Close {
            return Err(AletheDefect::UnexpectedToken {
                pos,
                expected: "the assumed term",
                found: ")".to_string(),
            });
        }
        let mut binders = self.frame_bound_vars();
        self.parse_term_from(lexer, tok, pos, &mut binders, 0)?;
        self.expect_close_ignoring_attrs(lexer)?;
        self.report.assumes += 1;
        Ok(())
    }

    fn parse_step(&mut self, lexer: &mut Lexer<'_>, _head_pos: Pos) -> Result<(), AletheDefect> {
        let (id, id_pos) = self.take_id(lexer)?;
        // The clause.
        let (tok, pos) = lexer.next_token()?;
        if tok != Tok::Open {
            return Err(AletheDefect::UnexpectedToken {
                pos,
                expected: "'(' opening the clause",
                found: tok.describe(),
            });
        }
        let (cl, cl_pos) = lexer.next_token()?;
        match &cl {
            Tok::Symbol(s) if s == "cl" => {}
            other => {
                return Err(AletheDefect::ClauseNotCl {
                    pos: cl_pos,
                    found: other.describe(),
                })
            }
        }
        let mut literals = 0usize;
        loop {
            let (tok, pos) = lexer.next_token()?;
            if tok == Tok::Close {
                break;
            }
            if tok == Tok::Eof {
                return Err(AletheDefect::UnexpectedEof {
                    pos,
                    expected: "')' closing the clause",
                });
            }
            let mut binders = self.frame_bound_vars();
            self.parse_term_from(lexer, tok, pos, &mut binders, 0)?;
            literals += 1;
        }

        // Attributes, in the ONE order carcara honours.
        let mut stage = 0u8; // 0 before :rule, 1 after, 2 after :premises, 3 after :args, 4 after :discharge
        let mut rule: Option<(String, Pos)> = None;
        let mut premises: Vec<(String, Pos)> = Vec::new();
        loop {
            let (tok, pos) = lexer.next_token()?;
            match tok {
                Tok::Close => break,
                Tok::Eof => {
                    return Err(AletheDefect::UnexpectedEof {
                        pos,
                        expected: "')' closing the step",
                    })
                }
                Tok::Keyword(kw) => match kw.as_str() {
                    ":rule" => {
                        if stage != 0 {
                            return Err(AletheDefect::MisplacedAttribute { pos, keyword: kw });
                        }
                        let (name, name_pos) = lexer.next_token()?;
                        let Tok::Symbol(name) = name else {
                            return Err(AletheDefect::UnexpectedToken {
                                pos: name_pos,
                                expected: "a rule name",
                                found: name.describe(),
                            });
                        };
                        rule = Some((name, name_pos));
                        stage = 1;
                    }
                    ":premises" => {
                        if stage != 1 {
                            return Err(AletheDefect::MisplacedAttribute { pos, keyword: kw });
                        }
                        premises = self.parse_id_sequence(lexer, &kw, pos)?;
                        stage = 2;
                    }
                    ":args" => {
                        if stage != 1 && stage != 2 {
                            return Err(AletheDefect::MisplacedAttribute { pos, keyword: kw });
                        }
                        self.parse_term_sequence(lexer, &kw, pos)?;
                        stage = 3;
                    }
                    ":discharge" => {
                        if stage == 0 || stage == 4 {
                            return Err(AletheDefect::MisplacedAttribute { pos, keyword: kw });
                        }
                        let discharged = self.parse_id_sequence(lexer, &kw, pos)?;
                        premises.extend(discharged);
                        stage = 4;
                    }
                    _ => return Err(AletheDefect::UnknownAttribute { pos, keyword: kw }),
                },
                other => {
                    return Err(AletheDefect::UnexpectedToken {
                        pos,
                        expected: "a step attribute",
                        found: other.describe(),
                    })
                }
            }
        }

        let Some((rule_name, rule_pos)) = rule else {
            return Err(AletheDefect::UnexpectedToken {
                pos: id_pos,
                expected: "':rule'",
                found: ")".to_string(),
            });
        };
        if !is_checkable_alethe_rule(&rule_name) {
            return Err(AletheDefect::UnknownRule {
                pos: rule_pos,
                rule: rule_name,
            });
        }
        // Premises resolve BACKWARD only: carcara resolves ids at parse time,
        // so a forward or dangling reference is `step id '<x>' is not defined`.
        for (premise, pos) in &premises {
            if !self.visible_ids.contains(premise) {
                return Err(AletheDefect::UndefinedStepId {
                    pos: *pos,
                    id: premise.clone(),
                });
            }
        }

        // Does this step close the innermost subproof?
        let closes = self
            .frames
            .last()
            .is_some_and(|frame| frame.anchor_id == id);
        if closes {
            let frame = self.frames.pop().expect("checked above");
            if frame.commands < 2 {
                return Err(AletheDefect::EmptySubproof {
                    pos: frame.anchor_pos,
                    id: frame.anchor_id,
                });
            }
            for retired in frame.ids {
                self.visible_ids.remove(&retired);
                self.retired_ids.insert(retired);
            }
            // The closing step counts as a step of the ENCLOSING subproof, so
            // an `assume` after a nested subproof is still misplaced.
            if let Some(parent) = self.frames.last_mut() {
                parent.seen_step = true;
            }
        } else if let Some(frame) = self.frames.last_mut() {
            frame.seen_step = true;
        }
        self.define_id(id, id_pos)?;
        if self.frames.is_empty() {
            self.saw_top_level_step = true;
            if literals == 0 {
                self.concluded_empty_clause = true;
            }
        }
        self.rules_seen.insert(rule_name);
        self.report.steps += 1;
        Ok(())
    }

    fn parse_anchor(&mut self, lexer: &mut Lexer<'_>, head_pos: Pos) -> Result<(), AletheDefect> {
        let (tok, pos) = lexer.next_token()?;
        let Tok::Keyword(kw) = tok else {
            return Err(AletheDefect::UnexpectedToken {
                pos,
                expected: "':step'",
                found: tok.describe(),
            });
        };
        if kw != ":step" {
            return Err(AletheDefect::UnexpectedToken {
                pos,
                expected: "':step'",
                found: kw,
            });
        }
        let (anchor_id, _) = self.take_id(lexer)?;
        let mut bound_vars = Vec::new();
        loop {
            let (tok, pos) = lexer.next_token()?;
            match tok {
                Tok::Close => break,
                Tok::Eof => {
                    return Err(AletheDefect::UnexpectedEof {
                        pos,
                        expected: "')' closing the anchor",
                    })
                }
                Tok::Keyword(kw) if kw == ":args" => {
                    bound_vars = self.parse_anchor_args(lexer, pos)?;
                }
                Tok::Keyword(kw) => {
                    return Err(AletheDefect::UnknownAttribute { pos, keyword: kw })
                }
                other => {
                    return Err(AletheDefect::UnexpectedToken {
                        pos,
                        expected: "':args' or ')'",
                        found: other.describe(),
                    })
                }
            }
        }
        self.frames.push(Frame {
            anchor_id,
            anchor_pos: head_pos,
            ids: Vec::new(),
            bound_vars,
            // Commands INSIDE the subproof, the anchor excluded. carcara
            // calls a subproof holding fewer than two of them empty — probe
            // `sp_empty` (anchor + closing step alone) → `subproof 't5' is
            // empty`.
            commands: 0,
            seen_step: false,
        });
        self.report.anchors += 1;
        Ok(())
    }

    /// `:args ((x U) (:= y v) (:= (z U) t))`
    fn parse_anchor_args(
        &mut self,
        lexer: &mut Lexer<'_>,
        kw_pos: Pos,
    ) -> Result<Vec<String>, AletheDefect> {
        let (tok, pos) = lexer.next_token()?;
        if tok != Tok::Open {
            return Err(AletheDefect::UnexpectedToken {
                pos,
                expected: "'(' opening the anchor arguments",
                found: tok.describe(),
            });
        }
        let mut bound = Vec::new();
        let mut count = 0usize;
        loop {
            let (tok, pos) = lexer.next_token()?;
            if tok == Tok::Close {
                break;
            }
            if tok != Tok::Open {
                return Err(AletheDefect::UnexpectedToken {
                    pos,
                    expected: "'(' opening an anchor argument",
                    found: tok.describe(),
                });
            }
            count += 1;
            let (first, first_pos) = lexer.next_token()?;
            match first {
                // `(:= name value)` or `(:= (name Sort) value)`
                Tok::Keyword(kw) if kw == ":=" => {
                    let (target, target_pos) = lexer.next_token()?;
                    match target {
                        Tok::Symbol(name) => bound.push(name),
                        Tok::Open => {
                            let (name, name_pos) = lexer.next_token()?;
                            let Tok::Symbol(name) = name else {
                                return Err(AletheDefect::UnexpectedToken {
                                    pos: name_pos,
                                    expected: "a variable name",
                                    found: name.describe(),
                                });
                            };
                            self.parse_sort(lexer)?;
                            self.expect(lexer, &Tok::Close, "')' closing the sorted variable")?;
                            bound.push(name);
                        }
                        other => {
                            return Err(AletheDefect::UnexpectedToken {
                                pos: target_pos,
                                expected: "a variable or sorted variable",
                                found: other.describe(),
                            })
                        }
                    }
                    // The value is evaluated in the OUTER scope: the variable
                    // being defined is not visible in its own definition.
                    let mut binders = self.frame_bound_vars();
                    let (tok, pos) = lexer.next_token()?;
                    self.parse_term_from(lexer, tok, pos, &mut binders, 0)?;
                    self.expect(lexer, &Tok::Close, "')' closing the anchor argument")?;
                }
                // `(x U)` sorted variable
                Tok::Symbol(name) => {
                    self.parse_sort(lexer)?;
                    self.expect(lexer, &Tok::Close, "')' closing the sorted variable")?;
                    bound.push(name);
                }
                other => {
                    return Err(AletheDefect::UnexpectedToken {
                        pos: first_pos,
                        expected: "an anchor argument",
                        found: other.describe(),
                    })
                }
            }
        }
        if count == 0 {
            return Err(AletheDefect::EmptySequence {
                pos: kw_pos,
                keyword: ":args".to_string(),
            });
        }
        Ok(bound)
    }

    fn parse_define_fun(
        &mut self,
        lexer: &mut Lexer<'_>,
        _head_pos: Pos,
    ) -> Result<(), AletheDefect> {
        let (name_tok, name_pos) = lexer.next_token()?;
        let Tok::Symbol(name) = name_tok else {
            return Err(AletheDefect::UnexpectedToken {
                pos: name_pos,
                expected: "a define-fun name",
                found: name_tok.describe(),
            });
        };
        self.expect(lexer, &Tok::Open, "'(' opening the parameter list")?;
        let mut params = Vec::new();
        loop {
            let (tok, pos) = lexer.next_token()?;
            if tok == Tok::Close {
                break;
            }
            if tok != Tok::Open {
                return Err(AletheDefect::UnexpectedToken {
                    pos,
                    expected: "'(' opening a sorted variable",
                    found: tok.describe(),
                });
            }
            let (var, var_pos) = lexer.next_token()?;
            let Tok::Symbol(var) = var else {
                return Err(AletheDefect::UnexpectedToken {
                    pos: var_pos,
                    expected: "a parameter name",
                    found: var.describe(),
                });
            };
            self.parse_sort(lexer)?;
            self.expect(lexer, &Tok::Close, "')' closing the sorted variable")?;
            params.push(var);
        }
        self.parse_sort(lexer)?;
        let arity = params.len();
        let mut binders = params;
        let (tok, pos) = lexer.next_token()?;
        self.parse_term_from(lexer, tok, pos, &mut binders, 0)?;
        self.expect(lexer, &Tok::Close, "')' closing the define-fun")?;
        // Definitions must precede use (probe `df_forward`), so register only
        // after the body parses.
        self.defines.insert(name, arity);
        self.report.define_funs += 1;
        Ok(())
    }

    // -- shared pieces ------------------------------------------------------

    fn expect(
        &self,
        lexer: &mut Lexer<'_>,
        want: &Tok,
        expected: &'static str,
    ) -> Result<(), AletheDefect> {
        let (tok, pos) = lexer.next_token()?;
        if &tok == want {
            Ok(())
        } else {
            Err(AletheDefect::UnexpectedToken {
                pos,
                expected,
                found: tok.describe(),
            })
        }
    }

    /// Consume the closing paren of an `assume`, tolerating nothing after the
    /// term. carcara *does* accept trailing attributes on `assume` (probe
    /// `at_assume_extra` → `valid`); AY never emits them, so they are refused.
    fn expect_close_ignoring_attrs(&self, lexer: &mut Lexer<'_>) -> Result<(), AletheDefect> {
        let (tok, pos) = lexer.next_token()?;
        match tok {
            Tok::Close => Ok(()),
            Tok::Keyword(kw) => Err(AletheDefect::UnknownAttribute { pos, keyword: kw }),
            other => Err(AletheDefect::UnexpectedToken {
                pos,
                expected: "')' closing the assume",
                found: other.describe(),
            }),
        }
    }

    fn take_id(&self, lexer: &mut Lexer<'_>) -> Result<(String, Pos), AletheDefect> {
        let (tok, pos) = lexer.next_token()?;
        match tok {
            Tok::Symbol(s) => {
                // carcara rejects `cl` and the command keywords as ids
                // (probes `idg_cl`, `idg_reserved`), and numerals are not
                // Symbol tokens at all (`idg_numeral`).
                if matches!(
                    s.as_str(),
                    "cl" | "step" | "assume" | "anchor" | "define-fun"
                ) {
                    return Err(AletheDefect::InvalidStepId { pos, token: s });
                }
                Ok((s, pos))
            }
            other => Err(AletheDefect::InvalidStepId {
                pos,
                token: other.describe(),
            }),
        }
    }

    fn define_id(&mut self, id: String, pos: Pos) -> Result<(), AletheDefect> {
        if self.visible_ids.contains(&id) || self.retired_ids.contains(&id) {
            return Err(AletheDefect::DuplicateStepId { pos, id });
        }
        if let Some(frame) = self.frames.last_mut() {
            frame.ids.push(id.clone());
        }
        self.visible_ids.insert(id);
        Ok(())
    }

    fn parse_id_sequence(
        &mut self,
        lexer: &mut Lexer<'_>,
        keyword: &str,
        kw_pos: Pos,
    ) -> Result<Vec<(String, Pos)>, AletheDefect> {
        self.expect(lexer, &Tok::Open, "'(' opening an id sequence")?;
        let mut ids = Vec::new();
        loop {
            let (tok, pos) = lexer.next_token()?;
            match tok {
                Tok::Close => break,
                Tok::Symbol(s) => ids.push((s, pos)),
                other => {
                    return Err(AletheDefect::UnexpectedToken {
                        pos,
                        expected: "a step id",
                        found: other.describe(),
                    })
                }
            }
        }
        if ids.is_empty() {
            return Err(AletheDefect::EmptySequence {
                pos: kw_pos,
                keyword: keyword.to_string(),
            });
        }
        Ok(ids)
    }

    fn parse_term_sequence(
        &mut self,
        lexer: &mut Lexer<'_>,
        keyword: &str,
        kw_pos: Pos,
    ) -> Result<(), AletheDefect> {
        self.expect(lexer, &Tok::Open, "'(' opening a term sequence")?;
        let mut count = 0usize;
        loop {
            let (tok, pos) = lexer.next_token()?;
            if tok == Tok::Close {
                break;
            }
            if tok == Tok::Eof {
                return Err(AletheDefect::UnexpectedEof {
                    pos,
                    expected: "')' closing the term sequence",
                });
            }
            let mut binders = self.frame_bound_vars();
            self.parse_term_from(lexer, tok, pos, &mut binders, 0)?;
            count += 1;
        }
        if count == 0 {
            return Err(AletheDefect::EmptySequence {
                pos: kw_pos,
                keyword: keyword.to_string(),
            });
        }
        Ok(())
    }

    fn frame_bound_vars(&self) -> Vec<String> {
        let mut out = Vec::new();
        for frame in &self.frames {
            out.extend(frame.bound_vars.iter().cloned());
        }
        out
    }

    // -- terms --------------------------------------------------------------

    fn resolve_symbol(&self, name: &str, pos: Pos, binders: &[String]) -> Result<(), AletheDefect> {
        if binders.iter().rev().any(|b| b == name)
            || self.defines.contains_key(name)
            || self.scope.contains_symbol(name)
            || BUILTIN_OPERATORS.contains(&name)
        {
            return Ok(());
        }
        // A frame-bound variable is in scope for the whole subproof.
        if self
            .frames
            .iter()
            .any(|frame| frame.bound_vars.iter().any(|b| b == name))
        {
            return Ok(());
        }
        Err(AletheDefect::UndefinedSymbol {
            pos,
            name: name.to_string(),
        })
    }

    #[allow(clippy::too_many_lines)]
    fn parse_term_from(
        &mut self,
        lexer: &mut Lexer<'_>,
        tok: Tok,
        pos: Pos,
        binders: &mut Vec<String>,
        depth: usize,
    ) -> Result<(), AletheDefect> {
        if depth > MAX_TERM_DEPTH {
            return Err(AletheDefect::TermTooDeep { pos });
        }
        match tok {
            Tok::Numeral(_) | Tok::Decimal(_) | Tok::StringLit(_) | Tok::BitVec(_) => Ok(()),
            Tok::Symbol(name) => self.resolve_symbol(&name, pos, binders),
            Tok::Open => self.parse_application(lexer, pos, binders, depth),
            Tok::Close => Err(AletheDefect::UnexpectedToken {
                pos,
                expected: "a term",
                found: ")".to_string(),
            }),
            Tok::Keyword(kw) => Err(AletheDefect::UnexpectedToken {
                pos,
                expected: "a term",
                found: kw,
            }),
            Tok::Eof => Err(AletheDefect::UnexpectedEof {
                pos,
                expected: "a term",
            }),
        }
    }

    #[allow(clippy::too_many_lines)]
    fn parse_application(
        &mut self,
        lexer: &mut Lexer<'_>,
        _open_pos: Pos,
        binders: &mut Vec<String>,
        depth: usize,
    ) -> Result<(), AletheDefect> {
        let (head, head_pos) = lexer.next_token()?;
        match head {
            Tok::Symbol(ref name) => match name.as_str() {
                "let" => return self.parse_let(lexer, binders, depth),
                "forall" | "exists" | "lambda" | "choice" => {
                    return self.parse_binder(lexer, binders, depth)
                }
                // `match` panics carcara (exit 101). Never accept it.
                "match" => {
                    return Err(AletheDefect::ForbiddenConstruct {
                        pos: head_pos,
                        what: "match",
                    })
                }
                "par" => {
                    return Err(AletheDefect::ForbiddenConstruct {
                        pos: head_pos,
                        what: "par",
                    })
                }
                "!" => return self.parse_annotation(lexer, binders, depth),
                "_" => {
                    // `(_ NAME idx+)` — an indexed constant used as a term.
                    self.parse_indexed_tail(lexer, head_pos)?;
                    return Ok(());
                }
                "as" => {
                    // `(as NAME SORT)` used bare as a term.
                    let (tok, pos) = lexer.next_token()?;
                    self.parse_term_from(lexer, tok, pos, binders, depth + 1)?;
                    self.parse_sort(lexer)?;
                    self.expect(lexer, &Tok::Close, "')' closing the qualified identifier")?;
                    return Ok(());
                }
                "cl" => {
                    return Err(AletheDefect::UnexpectedToken {
                        pos: head_pos,
                        expected: "a term (a nested 'cl' is not a term)",
                        found: "cl".to_string(),
                    })
                }
                _ => {
                    self.resolve_symbol(name, head_pos, binders)?;
                    if let Some(arity) = self.defines.get(name).copied() {
                        return self.parse_args_checked(
                            lexer,
                            binders,
                            depth,
                            Some((arity, name.clone(), head_pos)),
                        );
                    }
                }
            },
            Tok::Open => {
                // A qualified/indexed head: `((_ is C) t)`, `((as const S) v)`,
                // or a lambda applied directly.
                self.parse_qualified_head(lexer, binders, depth)?;
            }
            other => {
                return Err(AletheDefect::UnexpectedToken {
                    pos: head_pos,
                    expected: "an application head",
                    found: other.describe(),
                })
            }
        }
        self.parse_args_checked(lexer, binders, depth, None)?;
        Ok(())
    }

    fn parse_args_checked(
        &mut self,
        lexer: &mut Lexer<'_>,
        binders: &mut Vec<String>,
        depth: usize,
        arity_check: Option<(usize, String, Pos)>,
    ) -> Result<(), AletheDefect> {
        let mut count = 0usize;
        loop {
            let (tok, pos) = lexer.next_token()?;
            if tok == Tok::Close {
                break;
            }
            if tok == Tok::Eof {
                return Err(AletheDefect::UnexpectedEof {
                    pos,
                    expected: "')' closing the application",
                });
            }
            self.parse_term_from(lexer, tok, pos, binders, depth + 1)?;
            count += 1;
        }
        if let Some((arity, name, pos)) = arity_check {
            if arity != count {
                // carcara: `expected 0 arguments, got 1` (probe
                // `df_collide_arity`). A proof define-fun SHADOWS the problem
                // declaration, so a mismatch is a hard parse error.
                return Err(AletheDefect::UnexpectedToken {
                    pos,
                    expected: "the declared arity of a proof define-fun",
                    found: format!("{name} applied to {count} arguments (expects {arity})"),
                });
            }
        }
        Ok(())
    }

    /// Parse `(_ NAME idx+)` after the `_`, or `(as t SORT)` after the `as`.
    fn parse_indexed_tail(
        &mut self,
        lexer: &mut Lexer<'_>,
        underscore_pos: Pos,
    ) -> Result<(), AletheDefect> {
        let (name_tok, name_pos) = lexer.next_token()?;
        let Tok::Symbol(name) = name_tok else {
            return Err(AletheDefect::UnexpectedToken {
                pos: name_pos,
                expected: "an indexed identifier name",
                found: name_tok.describe(),
            });
        };
        let mut indices = 0usize;
        loop {
            let (tok, pos) = lexer.next_token()?;
            match tok {
                Tok::Close => break,
                Tok::Numeral(_) => indices += 1,
                Tok::Symbol(sym) => {
                    // `(_ is cons)` indexes by a constructor symbol.
                    self.resolve_symbol(&sym, pos, &[])?;
                    indices += 1;
                }
                other => {
                    return Err(AletheDefect::UnexpectedToken {
                        pos,
                        expected: "an index",
                        found: other.describe(),
                    })
                }
            }
        }
        if indices == 0 {
            return Err(AletheDefect::UnexpectedToken {
                pos: name_pos,
                expected: "at least one index",
                found: name.clone(),
            });
        }
        // `bvNN` literals are written `(_ bv15 8)`; the name is not in the
        // indexed table but carcara resolves it.
        let known = BUILTIN_INDEXED.contains(&name.as_str())
            || name.starts_with("bv")
            || self.scope.contains_symbol(&name)
            || self.defines.contains_key(&name);
        if !known {
            return Err(AletheDefect::UndefinedSymbol {
                pos: underscore_pos,
                name,
            });
        }
        Ok(())
    }

    fn parse_qualified_head(
        &mut self,
        lexer: &mut Lexer<'_>,
        binders: &mut Vec<String>,
        depth: usize,
    ) -> Result<(), AletheDefect> {
        let (tok, pos) = lexer.next_token()?;
        match tok {
            Tok::Symbol(ref name) if name == "_" => self.parse_indexed_tail(lexer, pos),
            Tok::Symbol(ref name) if name == "as" => {
                let (inner, inner_pos) = lexer.next_token()?;
                match inner {
                    Tok::Symbol(ref sym) if sym == "const" => {}
                    Tok::Symbol(ref sym) => self.resolve_symbol(sym, inner_pos, binders)?,
                    Tok::Open => {
                        // `(as (_ ...) SORT)`
                        self.parse_qualified_head(lexer, binders, depth)?;
                    }
                    other => {
                        return Err(AletheDefect::UnexpectedToken {
                            pos: inner_pos,
                            expected: "an identifier after 'as'",
                            found: other.describe(),
                        })
                    }
                }
                self.parse_sort(lexer)?;
                self.expect(lexer, &Tok::Close, "')' closing the qualified identifier")
            }
            Tok::Symbol(ref name) if name == "lambda" => self.parse_binder(lexer, binders, depth),
            other => Err(AletheDefect::UnexpectedToken {
                pos,
                expected: "'_', 'as' or 'lambda' in an application head",
                found: other.describe(),
            }),
        }
    }

    fn parse_let(
        &mut self,
        lexer: &mut Lexer<'_>,
        binders: &mut Vec<String>,
        depth: usize,
    ) -> Result<(), AletheDefect> {
        self.expect(lexer, &Tok::Open, "'(' opening the let bindings")?;
        let mut introduced = Vec::new();
        let mut list_pos;
        loop {
            let (tok, pos) = lexer.next_token()?;
            list_pos = pos;
            if tok == Tok::Close {
                break;
            }
            if tok != Tok::Open {
                return Err(AletheDefect::UnexpectedToken {
                    pos,
                    expected: "'(' opening a let binding",
                    found: tok.describe(),
                });
            }
            let (name_tok, name_pos) = lexer.next_token()?;
            let Tok::Symbol(name) = name_tok else {
                return Err(AletheDefect::UnexpectedToken {
                    pos: name_pos,
                    expected: "a let-bound name",
                    found: name_tok.describe(),
                });
            };
            // SMT-LIB `let` is parallel: the bound value sees only the OUTER
            // scope.
            let (tok, pos) = lexer.next_token()?;
            self.parse_term_from(lexer, tok, pos, binders, depth + 1)?;
            self.expect(lexer, &Tok::Close, "')' closing the let binding")?;
            introduced.push(name);
        }
        if introduced.is_empty() {
            return Err(AletheDefect::EmptySequence {
                pos: list_pos,
                keyword: "let".to_string(),
            });
        }
        let mark = binders.len();
        binders.extend(introduced);
        let (tok, pos) = lexer.next_token()?;
        let result = self.parse_term_from(lexer, tok, pos, binders, depth + 1);
        binders.truncate(mark);
        result?;
        self.expect(lexer, &Tok::Close, "')' closing the let")
    }

    fn parse_binder(
        &mut self,
        lexer: &mut Lexer<'_>,
        binders: &mut Vec<String>,
        depth: usize,
    ) -> Result<(), AletheDefect> {
        self.expect(lexer, &Tok::Open, "'(' opening the binder list")?;
        let mark = binders.len();
        let mut count = 0usize;
        let mut list_pos;
        loop {
            let (tok, pos) = lexer.next_token()?;
            list_pos = pos;
            if tok == Tok::Close {
                break;
            }
            if tok != Tok::Open {
                binders.truncate(mark);
                return Err(AletheDefect::UnexpectedToken {
                    pos,
                    expected: "'(' opening a sorted variable",
                    found: tok.describe(),
                });
            }
            let (name_tok, name_pos) = lexer.next_token()?;
            let Tok::Symbol(name) = name_tok else {
                binders.truncate(mark);
                return Err(AletheDefect::UnexpectedToken {
                    pos: name_pos,
                    expected: "a bound variable name",
                    found: name_tok.describe(),
                });
            };
            if let Err(defect) = self.parse_sort(lexer) {
                binders.truncate(mark);
                return Err(defect);
            }
            if let Err(defect) = self.expect(lexer, &Tok::Close, "')' closing the sorted variable")
            {
                binders.truncate(mark);
                return Err(defect);
            }
            binders.push(name);
            count += 1;
        }
        if count == 0 {
            binders.truncate(mark);
            return Err(AletheDefect::EmptySequence {
                pos: list_pos,
                keyword: "binder".to_string(),
            });
        }
        let (tok, pos) = lexer.next_token()?;
        let result = self.parse_term_from(lexer, tok, pos, binders, depth + 1);
        binders.truncate(mark);
        result?;
        self.expect(lexer, &Tok::Close, "')' closing the binder")
    }

    fn parse_annotation(
        &mut self,
        lexer: &mut Lexer<'_>,
        binders: &mut Vec<String>,
        depth: usize,
    ) -> Result<(), AletheDefect> {
        let (tok, pos) = lexer.next_token()?;
        self.parse_term_from(lexer, tok, pos, binders, depth + 1)?;
        loop {
            let (tok, pos) = lexer.next_token()?;
            match tok {
                Tok::Close => return Ok(()),
                Tok::Keyword(_) => {
                    // Annotation values are unconstrained; skip one balanced
                    // token or s-expression.
                    let (value, value_pos) = lexer.next_token()?;
                    match value {
                        Tok::Close => {
                            return Err(AletheDefect::UnexpectedToken {
                                pos: value_pos,
                                expected: "an annotation value",
                                found: ")".to_string(),
                            })
                        }
                        Tok::Open => self.skip_balanced(lexer)?,
                        _ => {}
                    }
                }
                other => {
                    return Err(AletheDefect::UnexpectedToken {
                        pos,
                        expected: "an annotation keyword",
                        found: other.describe(),
                    })
                }
            }
        }
    }

    fn skip_balanced(&self, lexer: &mut Lexer<'_>) -> Result<(), AletheDefect> {
        let mut depth = 1usize;
        loop {
            let (tok, pos) = lexer.next_token()?;
            match tok {
                Tok::Open => depth += 1,
                Tok::Close => {
                    depth -= 1;
                    if depth == 0 {
                        return Ok(());
                    }
                }
                Tok::Eof => {
                    return Err(AletheDefect::UnexpectedEof {
                        pos,
                        expected: "')'",
                    })
                }
                _ => {}
            }
        }
    }

    fn parse_sort(&mut self, lexer: &mut Lexer<'_>) -> Result<(), AletheDefect> {
        let (tok, pos) = lexer.next_token()?;
        match tok {
            Tok::Symbol(name) => {
                if BUILTIN_SORTS.contains(&name.as_str()) || self.scope.contains_sort(&name) {
                    Ok(())
                } else {
                    Err(AletheDefect::UndefinedSort { pos, name })
                }
            }
            Tok::Open => {
                let (head, head_pos) = lexer.next_token()?;
                let Tok::Symbol(name) = head else {
                    return Err(AletheDefect::UnexpectedToken {
                        pos: head_pos,
                        expected: "a sort constructor",
                        found: head.describe(),
                    });
                };
                if name == "_" {
                    let (idx_name, idx_pos) = lexer.next_token()?;
                    let Tok::Symbol(idx_name) = idx_name else {
                        return Err(AletheDefect::UnexpectedToken {
                            pos: idx_pos,
                            expected: "an indexed sort name",
                            found: idx_name.describe(),
                        });
                    };
                    if !BUILTIN_INDEXED_SORTS.contains(&idx_name.as_str()) {
                        return Err(AletheDefect::UndefinedSort {
                            pos: idx_pos,
                            name: idx_name,
                        });
                    }
                    loop {
                        let (tok, pos) = lexer.next_token()?;
                        match tok {
                            Tok::Close => return Ok(()),
                            Tok::Numeral(_) => {}
                            other => {
                                return Err(AletheDefect::UnexpectedToken {
                                    pos,
                                    expected: "a sort index",
                                    found: other.describe(),
                                })
                            }
                        }
                    }
                }
                if !BUILTIN_SORT_CONSTRUCTORS.contains(&name.as_str())
                    && !self.scope.contains_sort(&name)
                {
                    return Err(AletheDefect::UndefinedSort {
                        pos: head_pos,
                        name,
                    });
                }
                loop {
                    let (tok, pos) = lexer.next_token()?;
                    match tok {
                        Tok::Close => return Ok(()),
                        Tok::Symbol(inner) => {
                            if !BUILTIN_SORTS.contains(&inner.as_str())
                                && !self.scope.contains_sort(&inner)
                            {
                                return Err(AletheDefect::UndefinedSort { pos, name: inner });
                            }
                        }
                        Tok::Open => {
                            // Re-enter via a synthetic open: rewind is not
                            // available, so parse the nested sort inline.
                            self.parse_sort_after_open(lexer)?;
                        }
                        other => {
                            return Err(AletheDefect::UnexpectedToken {
                                pos,
                                expected: "a sort",
                                found: other.describe(),
                            })
                        }
                    }
                }
            }
            other => Err(AletheDefect::UnexpectedToken {
                pos,
                expected: "a sort",
                found: other.describe(),
            }),
        }
    }

    /// The `Tok::Open` branch of [`Self::parse_sort`], entered with the open
    /// paren already consumed.
    fn parse_sort_after_open(&mut self, lexer: &mut Lexer<'_>) -> Result<(), AletheDefect> {
        let (head, head_pos) = lexer.next_token()?;
        let Tok::Symbol(name) = head else {
            return Err(AletheDefect::UnexpectedToken {
                pos: head_pos,
                expected: "a sort constructor",
                found: head.describe(),
            });
        };
        if name == "_" {
            let (idx_name, idx_pos) = lexer.next_token()?;
            let Tok::Symbol(idx_name) = idx_name else {
                return Err(AletheDefect::UnexpectedToken {
                    pos: idx_pos,
                    expected: "an indexed sort name",
                    found: idx_name.describe(),
                });
            };
            if !BUILTIN_INDEXED_SORTS.contains(&idx_name.as_str()) {
                return Err(AletheDefect::UndefinedSort {
                    pos: idx_pos,
                    name: idx_name,
                });
            }
            loop {
                let (tok, pos) = lexer.next_token()?;
                match tok {
                    Tok::Close => return Ok(()),
                    Tok::Numeral(_) => {}
                    other => {
                        return Err(AletheDefect::UnexpectedToken {
                            pos,
                            expected: "a sort index",
                            found: other.describe(),
                        })
                    }
                }
            }
        }
        if !BUILTIN_SORT_CONSTRUCTORS.contains(&name.as_str()) && !self.scope.contains_sort(&name) {
            return Err(AletheDefect::UndefinedSort {
                pos: head_pos,
                name,
            });
        }
        loop {
            let (tok, pos) = lexer.next_token()?;
            match tok {
                Tok::Close => return Ok(()),
                Tok::Symbol(inner) => {
                    if !BUILTIN_SORTS.contains(&inner.as_str()) && !self.scope.contains_sort(&inner)
                    {
                        return Err(AletheDefect::UndefinedSort { pos, name: inner });
                    }
                }
                Tok::Open => self.parse_sort_after_open(lexer)?,
                other => {
                    return Err(AletheDefect::UnexpectedToken {
                        pos,
                        expected: "a sort",
                        found: other.describe(),
                    })
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// One-shot entry point
// ---------------------------------------------------------------------------

/// Parse and validate a complete Alethe document.
///
/// This is the round-trip self-check: hand it the text the exporter just
/// produced plus the problem's declared symbols, and it returns `Ok` only if
/// the document is one carcara can parse.
///
/// # Errors
///
/// Returns the first [`AletheDefect`] found.
pub fn check_alethe_document(
    text: &str,
    scope: &ProblemScope,
) -> Result<AletheDocumentReport, AletheDefect> {
    let mut checker = AletheDocumentChecker::new(scope.clone());
    checker.push_str(text)?;
    checker.finish()
}

/// A `Write` adapter that round-trip checks the bytes passing through it.
///
/// This is the RSS-safe hook: the exporter streams a certificate that reaches
/// 305 MB precisely so it is never materialized, and the self-check tees off
/// that stream rather than re-reading the file.
pub struct AletheSelfCheckWriter<W> {
    inner: W,
    checker: Option<AletheDocumentChecker>,
    defect: Option<AletheDefect>,
}

impl<W> AletheSelfCheckWriter<W> {
    /// Wrap `inner`, checking every byte written against `scope`.
    pub fn new(inner: W, scope: ProblemScope) -> Self {
        Self {
            inner,
            checker: Some(AletheDocumentChecker::new(scope)),
            defect: None,
        }
    }

    /// Borrow the wrapped writer.
    pub fn get_ref(&self) -> &W {
        &self.inner
    }

    /// Unwrap, returning the writer and the check verdict.
    ///
    /// # Errors
    ///
    /// Returns the first defect observed, or any defect the terminal
    /// [`AletheDocumentChecker::finish`] reports.
    pub fn finish(self) -> (W, Result<AletheDocumentReport, AletheDefect>) {
        let verdict = match (self.defect, self.checker) {
            (Some(defect), _) => Err(defect),
            (None, Some(checker)) => checker.finish(),
            (None, None) => Err(AletheDefect::NoEmptyClause),
        };
        (self.inner, verdict)
    }
}

impl<W: std::io::Write> std::io::Write for AletheSelfCheckWriter<W> {
    fn write(&mut self, bytes: &[u8]) -> std::io::Result<usize> {
        let written = self.inner.write(bytes)?;
        if self.defect.is_none() {
            if let Some(checker) = self.checker.as_mut() {
                if let Err(defect) = checker.push_bytes(&bytes[..written]) {
                    self.defect = Some(defect);
                }
            }
        }
        Ok(written)
    }

    fn flush(&mut self) -> std::io::Result<()> {
        self.inner.flush()
    }
}

/// The rule vocabulary the document checker accepts, exposed for tests and the
/// offline differential harness.
#[must_use]
pub fn checkable_rule_names() -> &'static [&'static str] {
    &CHECKABLE_ALETHE_RULES
}

#[cfg(test)]
#[path = "alethe_parser_tests.rs"]
mod tests;
