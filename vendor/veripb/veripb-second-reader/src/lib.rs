//! A **second, independent reader** for VeriPB formula files.
//!
//! # Why this crate exists
//!
//! `--kernel-verify` re-derives the checker's soundness-critical steps
//! through the proved kernel, and `KernelShadowDb` composes those steps into
//! a run-level `Unsat F` claim. But `F` there is the formula the checker
//! **stored**, not the bytes on disk (the development design notes §7.4, boundary
//! note 1). Two shipped defects lived in exactly that gap, and both of them
//! made the cross-check report *more* confidence, not less:
//!
//! * the WCNF parser took a literal's variable identity from its **spelling**,
//!   so `1`, `01`, `001` and `+1` interned four different variables;
//! * `Clause::from_unnormalized_lits` used a legal literal packing as its
//!   "no previous literal" sentinel, so a unit clause on that literal was
//!   stored as the **empty clause** — a contradiction — and the run reported
//!   `nothing outside the proved fragment` and then `COMPOSED: ... over the
//!   stored formula`. Every word of that was true.
//!
//! This crate closes the gap by reading the formula file a second time, and
//! the *only* thing that makes a second reading worth anything is that it
//! cannot fail the same way as the first. So:
//!
//! * **No dependency on `veripb-parser`.** The `Cargo.toml` dependency list
//!   is the proof, and it is one line long (`malachite-bigint`, the same
//!   integer type the rest of the workspace already uses). Not even
//!   `veripb-formula` is linked, so no shared `Lit` packing, no shared
//!   `Clause` normalization, no shared `VarNameManager` interning — the three
//!   places the known defects lived.
//! * **No cleverness.** Everything is a hand-written character scanner and a
//!   `Vec`; variables are `String` names, coefficients are `BigInt`, nothing
//!   is packed into a machine word, nothing is deduplicated by a sentinel,
//!   nothing is narrowed. The single index in the crate is the `BTreeSet` of
//!   `(name, sign)` pairs [`clause_constraint`] asks "have I emitted this
//!   literal already?" — the same question the scan it replaced asked, over
//!   the same pairs, and the reason it is not a scan is measured in that
//!   function's comment. The reader is meant to be audited by eye against
//!   `proof_format_overview.md` ("Supported Formula File Formats") and
//!   the development design notes §Integers / §Names, Variables and Literals /
//!   §Objectives and Constraints, and it is deliberately slower and more
//!   allocation-happy than the parser it checks.
//!
//! # What it produces
//!
//! [`read`] turns a file's bytes into a [`Formula`]: a list of
//! [`Constraint`]s, each already in the `>=` direction, with terms keyed by
//! the variable's **name** rather than by any index, plus the minimization
//! [`Objective`] the format implies. Nothing is normalized, merged, flipped
//! or sorted here — that is the job of the proved kernel's `normC` on the
//! comparison side, and doing it here would be a second place to get it
//! wrong.
//!
//! Names are the interface on purpose. The checker assigns variable *indices*
//! in interning order, which is an implementation detail that a cross-check
//! must not depend on; but the name a variable is known by is fixed by the
//! format, and getting it wrong is precisely defect 16. Comparing on names
//! makes that defect a mismatch instead of a shared assumption.
//!
//! # Errors
//!
//! [`read`] is **strict**: anything it cannot read under its own plain
//! reading of the format is a [`ReadError`]. It is not the authority on what
//! is a legal file — the checker's parser is — so a caller must treat a
//! `ReadError` as *"no second opinion available"* (a counted skip), never as
//! a rejection. Rejecting on it would let a reader that is merely simpler
//! than the parser reject valid proofs.

use std::str::FromStr;

use malachite_bigint::BigInt;

/// The formula file formats a VeriPB run can be given.
///
/// The caller resolves this the same way the checker does (an explicit
/// `--opb`/`--cnf`/`--wcnf` override, else the file extension, else OPB);
/// resolving it here as well would be a second place for the two to disagree
/// about something that is not a property of the file.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Format {
    /// Pseudo-Boolean (OPB).
    Opb,
    /// DIMACS CNF.
    Cnf,
    /// Weighted CNF (MaxSAT Evaluation 2022 "new" format).
    Wcnf,
}

/// One `coeff * literal` summand, with the variable named rather than
/// indexed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Term {
    /// The coefficient, exactly as the file spells it. May be negative.
    pub coeff: BigInt,
    /// The variable's name in the format's own naming: the identifier itself
    /// for OPB, `x<i>` for the DIMACS/WCNF variable `i`, `_b<i>` for the
    /// blocking variable of the `i`-th WCNF clause.
    pub var: String,
    /// Whether the literal is the negation of that variable.
    pub negated: bool,
}

/// One constraint, always in the `>=` direction, exactly as the file spells
/// it: not merged, not flipped, not sorted, not saturated.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Constraint {
    /// The summands, in file order, including duplicate and opposite
    /// literals.
    pub terms: Vec<Term>,
    /// The right-hand side.
    pub degree: BigInt,
    /// The one-based line of the file this constraint was read from, kept so
    /// a mismatch can point at the text rather than only at the constraint.
    pub line: usize,
}

/// An objective, always as a **minimization**: a `max:` objective is negated
/// on the way in, which is what the checker does internally
/// (`opb_token.rs`: "internally the objective is always minimized").
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Objective {
    /// The summands, in file order.
    pub terms: Vec<Term>,
    /// The additive constant.
    pub constant: BigInt,
}

/// A formula file's contents.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Formula {
    /// The constraints, in the order the checker files them at database ids
    /// `1, 2, ...` — in particular an OPB `=` contributes its `>=` half
    /// first and its `<=` half second.
    pub constraints: Vec<Constraint>,
    /// The objective, if the format supplies one. CNF never does; WCNF
    /// always does (possibly empty); OPB does when it carries `min:`/`max:`.
    pub objective: Option<Objective>,
}

/// Why the second reader could not read a file.
///
/// Never a reason to reject a proof; see the crate docs.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReadError {
    /// One-based line number, or 0 for a whole-file complaint.
    pub line: usize,
    /// What the reader expected and did not find.
    pub what: String,
}

impl ReadError {
    fn at(line: usize, what: impl Into<String>) -> ReadError {
        ReadError {
            line: line + 1,
            what: what.into(),
        }
    }
}

impl std::fmt::Display for ReadError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.line == 0 {
            write!(f, "{}", self.what)
        } else {
            write!(f, "line {}: {}", self.line, self.what)
        }
    }
}

impl std::error::Error for ReadError {}

/// Read a formula file.
///
/// `bytes` is the whole file. Lines are split on `\n` and each must be valid
/// UTF-8 — the same requirement the checker's own line reader makes, so this
/// is not a stricter reading.
pub fn read(bytes: &[u8], format: Format) -> Result<Formula, ReadError> {
    match format {
        Format::Opb => read_opb(bytes),
        Format::Cnf => read_cnf(bytes),
        Format::Wcnf => read_wcnf(bytes),
    }
}

// ---------------------------------------------------------------------------
// Shared lexical helpers
// ---------------------------------------------------------------------------

/// The file's lines, split on `\n`. A trailing `\r` is left in place and
/// treated as whitespace by the scanners, so CRLF files read the same as LF
/// files.
fn split_lines(bytes: &[u8]) -> Vec<&[u8]> {
    bytes.split(|b| *b == b'\n').collect()
}

/// Decode one line, refusing invalid UTF-8.
fn decode(line: &[u8], line_no: usize) -> Result<&str, ReadError> {
    std::str::from_utf8(line).map_err(|_| ReadError::at(line_no, "line is not valid UTF-8"))
}

fn is_space(b: u8) -> bool {
    b == b' ' || b == b'\t' || b == b'\r'
}

/// Skip spaces starting at `i`, returning the first non-space offset.
fn skip_spaces(s: &[u8], mut i: usize) -> usize {
    while i < s.len() && is_space(s[i]) {
        i += 1;
    }
    i
}

/// Scan `[+-]?[0-9]+` at `i`. Returns the text and the offset after it.
///
/// This is the integer of the development design notes §Integers widened to what the
/// *lexers* actually accept: the grammar forbids leading zeros and `+0`, but
/// every VeriPB lexer's integer regex is `[+-]?[0-9]+`, so `007` and `+1` do
/// reach the parsers. That difference is not academic — it is the shape
/// defect 16 turned into four different variables — so the reader accepts the
/// wider language and canonicalizes below.
fn scan_int(s: &[u8], i: usize) -> Option<(&str, usize)> {
    let start = i;
    let mut j = i;
    if j < s.len() && (s[j] == b'+' || s[j] == b'-') {
        j += 1;
    }
    let digits_start = j;
    while j < s.len() && s[j].is_ascii_digit() {
        j += 1;
    }
    if j == digits_start {
        return None;
    }
    // Safe: every byte scanned is ASCII.
    Some((std::str::from_utf8(&s[start..j]).unwrap(), j))
}

/// The value of an `[+-]?[0-9]+` token.
///
/// Written out rather than delegated to `BigInt::from_str` because that
/// implementation need not accept `+5` or `007`, and the reader must read
/// every spelling the lexers admit. Leading zeros are stripped before the
/// conversion, which is also what makes `1`, `01` and `001` one variable in
/// [`dimacs_var_name`].
fn int_value(text: &str) -> BigInt {
    let (negative, digits) = match text.as_bytes()[0] {
        b'+' => (false, &text[1..]),
        b'-' => (true, &text[1..]),
        _ => (false, text),
    };
    let magnitude = digits.trim_start_matches('0');
    let value = if magnitude.is_empty() {
        BigInt::from(0)
    } else {
        // Every byte is an ASCII digit and the leading zeros are gone, so
        // this is the plain decimal form every implementation accepts.
        BigInt::from_str(magnitude).expect("digits parse")
    };
    if negative { -value } else { value }
}

/// Is this `[+-]?[0-9]+` token the value zero? (`0`, `-0` and `+0` all are,
/// and in DIMACS all three end the clause.)
fn int_is_zero(text: &str) -> bool {
    text.trim_start_matches(['+', '-'])
        .bytes()
        .all(|b| b == b'0')
}

/// The name the DIMACS variable `|value|` is known by.
///
/// **This is the format decision defect 16 got wrong.** A DIMACS literal
/// denotes a variable by its *value*, not by its spelling: `1`, `01`, `001`
/// and `+1` are the same variable `x1`, and `-1` is `~x1`. Building the name
/// out of the token text instead interns four variables and silently relaxes
/// the formula. `proof_format_overview.md` states the value-based reading for
/// both DIMACS formats ("The variable `i` ... is represented by `x<i>`").
///
/// The magnitude is kept as text rather than as a machine integer so that an
/// index far outside `i64` — the range where defect 17 lived — still names a
/// variable here instead of overflowing into some other one.
fn dimacs_var_name(int_text: &str) -> String {
    let digits = int_text.trim_start_matches(['+', '-']);
    let magnitude = digits.trim_start_matches('0');
    let magnitude = if magnitude.is_empty() { "0" } else { magnitude };
    format!("x{magnitude}")
}

/// Is this `[+-]?[0-9]+` token negative? (`-0` is not: its value is zero.)
fn int_is_negative(text: &str) -> bool {
    text.as_bytes()[0] == b'-' && !int_is_zero(text)
}

// ---------------------------------------------------------------------------
// DIMACS CNF
// ---------------------------------------------------------------------------

/// One token of a DIMACS line.
#[derive(Debug, PartialEq, Eq)]
enum DimacsTok<'a> {
    /// `[+-]?[0-9]+`, kept as text.
    Int(&'a str),
    /// `p cnf`, the CNF problem header.
    Header,
    /// `h`, the WCNF hard-clause marker.
    Hard,
    /// `c...`: a comment, which runs to the end of the line.
    Comment,
}

/// Tokenize one DIMACS line (CNF or WCNF).
///
/// Mirrors what the two `logos` lexers accept, and nothing more:
/// whitespace-separated is the normal case but not required (`1-2` is two
/// literals, because the integer regex is greedy from the token start), a
/// comment is the letter `c` and everything after it on the line, `p cnf` is
/// one token spelled with exactly one space, and `h` is one token.
fn dimacs_tokens<'a>(
    line: &'a str,
    line_no: usize,
    wcnf: bool,
) -> Result<Vec<DimacsTok<'a>>, ReadError> {
    let s = line.as_bytes();
    let mut out = Vec::new();
    let mut i = skip_spaces(s, 0);
    while i < s.len() {
        if s[i] == b'c' {
            // `c.*` — the rest of the line is a comment.
            out.push(DimacsTok::Comment);
            break;
        }
        if !wcnf && line[i..].starts_with("p cnf") {
            out.push(DimacsTok::Header);
            i += "p cnf".len();
        } else if wcnf && s[i] == b'h' {
            out.push(DimacsTok::Hard);
            i += 1;
        } else if let Some((text, next)) = scan_int(s, i) {
            out.push(DimacsTok::Int(text));
            i = next;
        } else {
            return Err(ReadError::at(
                line_no,
                format!("expected an integer or a comment, found {:?}", &line[i..]),
            ));
        }
        i = skip_spaces(s, i);
    }
    Ok(out)
}

/// A DIMACS clause: the distinct literals, in first-occurrence order.
///
/// DIMACS clause semantics are **set** semantics — `1 -2 1 0` is the clause
/// `x1 ∨ ¬x2`, and `proof_format_overview.md` spells out that VeriPB follows
/// them: the constraint is `1 x1 1 ~x2 >= 1`, with coefficient 1 for each
/// *distinct* literal rather than 2 for the repeated one.
///
/// Opposite literals are deliberately **not** cancelled here. `1 1 2 -2 -1 3
/// 0` must become `1 x3 >= -1`, and that is exactly what the kernel's proved
/// `normC` does to `1 x1 1 x2 1 ~x2 1 ~x1 1 x3 >= 1`: cancel each opposite
/// pair and lower the degree by one per pair. Doing it here as well would be
/// a second, unproved implementation of the step whose sentinel bug is defect
/// 17.
///
/// The dedup keeps a `BTreeSet` of the `(name, sign)` pairs already emitted
/// and asks it, once, whether this literal is new. It is an **index over the
/// same data**, not a second representation of it: the set holds a borrowed
/// `&str` and a `bool`, the exact pair the scan it replaced compared, so
/// there is still no sentinel value and no packed literal — the class of bug
/// being cross-checked, and the reason the obvious `Vec::contains` was chosen
/// first. The set is ordered internally and that order is never looked at;
/// `terms` below is what carries the clause, still in the file's own
/// first-occurrence order.
///
/// `Vec::contains` had to go because it was quadratic in the clause length:
/// measured under `--kernel-verify`, one clause of 10k/20k/40k/80k literals
/// cost 87/221/950/4544 ms of cross-check overhead (~4.6x per doubling) and
/// ~14 s at 160k, against a flat 15–20 ms for the same run without the flag.
/// A cross-check nobody can afford to leave on is a cross-check that is off,
/// so the reviewability the quadratic bought was not free. `BTreeSet` rather
/// than a hash set because the workspace disallows `std::collections::Hash*`
/// and the alternative — pulling in `ahash` — would double this crate's
/// dependency list, which *is* its independence argument.
/// `tests/kernel_verify_perf.rs`'s `CnfWideClause` shape pins the result.
fn clause_constraint(lits: &[(String, bool)], line: usize) -> Constraint {
    let mut terms: Vec<Term> = Vec::new();
    let mut seen: std::collections::BTreeSet<(&str, bool)> = std::collections::BTreeSet::new();
    for (var, negated) in lits {
        if !seen.insert((var.as_str(), *negated)) {
            continue;
        }
        terms.push(Term {
            coeff: BigInt::from(1),
            var: var.clone(),
            negated: *negated,
        });
    }
    Constraint {
        terms,
        degree: BigInt::from(1),
        line,
    }
}

fn read_cnf(bytes: &[u8]) -> Result<Formula, ReadError> {
    let mut formula = Formula::default();
    let mut seen_header = false;
    let mut lits: Vec<(String, bool)> = Vec::new();

    for (line_no, raw) in split_lines(bytes).into_iter().enumerate() {
        let line = decode(raw, line_no)?;
        let tokens = dimacs_tokens(line, line_no, false)?;
        if !seen_header {
            // Before the header the checker's parser inspects only the first
            // token of the line and accepts a comment or the header itself.
            match tokens.first() {
                None => continue,
                Some(DimacsTok::Comment) => continue,
                Some(DimacsTok::Header) => {
                    // `p cnf <#vars> <#clauses>`. The counts are read so the
                    // header is checked for shape, but they are deliberately
                    // NOT enforced against the file: whether a mismatch is an
                    // error is the checker's policy question
                    // (`--lenient-header-counts`), not a fact about what the
                    // formula says.
                    let mut rest = tokens[1..].iter();
                    for what in ["variable count", "clause count"] {
                        match rest.next() {
                            Some(DimacsTok::Int(_)) => {}
                            _ => {
                                return Err(ReadError::at(
                                    line_no,
                                    format!("`p cnf` header is missing its {what}"),
                                ));
                            }
                        }
                    }
                    // The header owns its line. The primary reader returned
                    // after the two counts and dropped the rest of the header
                    // line, so `p cnf 1 2 1 0` silently lost the clause
                    // `1 0` -- and this reader, written to the same shape,
                    // inherited the same lenience, so the formula cross-check
                    // reported the truncated reading as matching the file on
                    // disk. An unsatisfiable file verified as
                    // `s VERIFIED SATISFIABLE`. Same class as the OPB
                    // one-item-per-line hole; fixed here on this reader's own
                    // terms, as that one was.
                    if rest.next().is_some() {
                        return Err(ReadError::at(
                            line_no,
                            "the `p cnf <vars> <clauses>` header owns its line; \
                             found more after the counts",
                        ));
                    }
                    seen_header = true;
                    continue;
                }
                Some(_) => {
                    return Err(ReadError::at(
                        line_no,
                        "expected the `p cnf` header or a comment",
                    ));
                }
            }
        }
        for token in tokens {
            match token {
                DimacsTok::Comment => break,
                DimacsTok::Int(text) if int_is_zero(text) => {
                    formula
                        .constraints
                        .push(clause_constraint(&lits, line_no + 1));
                    lits.clear();
                }
                DimacsTok::Int(text) => {
                    lits.push((dimacs_var_name(text), int_is_negative(text)));
                }
                DimacsTok::Header | DimacsTok::Hard => {
                    return Err(ReadError::at(line_no, "expected an integer or a comment"));
                }
            }
        }
    }

    if !seen_header {
        return Err(ReadError {
            line: 0,
            what: "the file has no `p cnf` header".to_string(),
        });
    }
    if !lits.is_empty() {
        // The file ends mid-clause. Reading the partial clause as if it were
        // whole would invent a constraint; dropping it is what defect 2 did.
        return Err(ReadError {
            line: 0,
            what: format!("the file ends mid-clause, after {} literal(s)", lits.len()),
        });
    }
    Ok(formula)
}

// ---------------------------------------------------------------------------
// WCNF (MaxSAT)
// ---------------------------------------------------------------------------

/// Read a WCNF file, applying the MaxSAT-to-PB encoding
/// `proof_format_overview.md` §MaxSAT specifies:
///
/// * a **hard** clause (`h l1 ... lk 0`) is the constraint `1 l1 ... 1 lk >= 1`;
/// * a **soft** clause `w l1 ... lk 0` never becomes a constraint on its own:
///   - `k == 0`: the weight goes to the objective's constant;
///   - `k == 1`: the **negated** literal enters the objective with coefficient
///     `w`, and no constraint is stored;
///   - `k >= 2`: a blocking variable `_b<i>` is introduced, where `i` is the
///     one-based index of this clause **among all clauses of the file**, hard
///     ones included (the worked example in the overview numbers `_b3` and
///     `_b5` by file position). The constraint is the clause plus the literal
///     `~_b<i>`, and that same literal enters the objective with coefficient
///     `w`.
///
/// The blocking-variable naming is the one place this reader has to mirror an
/// *encoding* choice rather than a fact about the file, so it is stated here
/// and pinned by `blocking_variables_are_named_by_file_clause_index`. If the
/// encoding ever changes, this reader reports a divergence until it is
/// changed here too — which is the correct failure direction for a
/// cross-check, if an annoying one.
fn read_wcnf(bytes: &[u8]) -> Result<Formula, ReadError> {
    /// What the current clause's leading marker said it is.
    enum Weight {
        Hard,
        Soft(BigInt),
    }

    let mut formula = Formula::default();
    let mut objective = Objective::default();
    let mut lits: Vec<(String, bool)> = Vec::new();
    let mut weight: Option<Weight> = None;
    // Counts every terminated clause, hard and soft alike; the blocking
    // variable of a clause is named after this index.
    let mut clause_index: u64 = 0;

    for (line_no, raw) in split_lines(bytes).into_iter().enumerate() {
        let line = decode(raw, line_no)?;
        for token in dimacs_tokens(line, line_no, true)? {
            match token {
                DimacsTok::Comment => break,
                DimacsTok::Hard => {
                    if weight.is_some() {
                        return Err(ReadError::at(
                            line_no,
                            "`h` where the previous clause has not ended",
                        ));
                    }
                    weight = Some(Weight::Hard);
                }
                // The first integer of a clause is its weight; every integer
                // after it is a literal, and `0` ends the clause.
                DimacsTok::Int(text) if weight.is_none() => {
                    weight = Some(Weight::Soft(int_value(text)));
                }
                DimacsTok::Int(text) if !int_is_zero(text) => {
                    lits.push((dimacs_var_name(text), int_is_negative(text)));
                }
                DimacsTok::Int(_) => {
                    clause_index += 1;
                    match weight.take().expect("weight is set above") {
                        Weight::Hard => formula
                            .constraints
                            .push(clause_constraint(&lits, line_no + 1)),
                        Weight::Soft(w) => match lits.len() {
                            0 => objective.constant += w,
                            1 => {
                                // The soft unit clause `l` costs `w` exactly
                                // when `l` is false, i.e. when `~l` is true.
                                let (var, negated) = lits[0].clone();
                                objective.terms.push(Term {
                                    coeff: w,
                                    var,
                                    negated: !negated,
                                });
                            }
                            _ => {
                                let blocking = format!("_b{clause_index}");
                                let mut relaxed = lits.clone();
                                relaxed.push((blocking.clone(), true));
                                formula
                                    .constraints
                                    .push(clause_constraint(&relaxed, line_no + 1));
                                objective.terms.push(Term {
                                    coeff: w,
                                    var: blocking,
                                    negated: true,
                                });
                            }
                        },
                    }
                    lits.clear();
                }
                DimacsTok::Header => {
                    return Err(ReadError::at(line_no, "expected an integer or a comment"));
                }
            }
        }
    }

    if weight.is_some() || !lits.is_empty() {
        return Err(ReadError {
            line: 0,
            what: format!("the file ends mid-clause, after {} literal(s)", lits.len()),
        });
    }
    formula.objective = Some(objective);
    Ok(formula)
}

// ---------------------------------------------------------------------------
// OPB
// ---------------------------------------------------------------------------

/// One token of an OPB line.
#[derive(Debug, PartialEq, Eq)]
enum OpbTok<'a> {
    /// `[+-]?[0-9]+`.
    Int(&'a str),
    /// A variable name.
    Var(&'a str),
    /// `@name`, a constraint label.
    Label,
    /// `~`.
    Tilde,
    /// `>=`, `<=`, `=`.
    Ge,
    Le,
    Eq,
    /// `;`.
    Semi,
    /// `min:` / `max:`.
    Min,
    Max,
    /// `preserved:`.
    Preserved,
}

/// May this byte continue an OPB identifier?
///
/// the development design notes §Names, Variables and Literals: a variable is a letter
/// or underscore followed by **at least one** more identifier symbol, where
/// an identifier symbol is a letter, an underscore, a digit, or one of
/// `^ [ ] { } -`. Two consequences worth stating because they look like bugs
/// and are not: a one-character name such as `x` is not a variable, and `-`
/// is an identifier symbol, so `x1-1` is one variable rather than a variable
/// and a coefficient.
fn is_ident_continue(b: u8) -> bool {
    b.is_ascii_alphanumeric()
        || b == b'_'
        || b == b'^'
        || b == b'['
        || b == b']'
        || b == b'{'
        || b == b'}'
        || b == b'-'
}

fn is_ident_start(b: u8) -> bool {
    b.is_ascii_alphabetic() || b == b'_'
}

/// Tokenize one OPB line. A `*` starts a comment that runs to the end of the
/// line.
fn opb_tokens<'a>(line: &'a str, line_no: usize) -> Result<Vec<OpbTok<'a>>, ReadError> {
    let s = line.as_bytes();
    let mut out = Vec::new();
    let mut i = skip_spaces(s, 0);
    while i < s.len() {
        let rest = &line[i..];
        // The keywords are matched before identifiers because `min`, `max`
        // and `preserved` are themselves legal identifier prefixes; the `:`
        // is what distinguishes them, and it is not an identifier symbol.
        if let Some(keyword) = ["min:", "max:", "preserved:"]
            .iter()
            .find(|k| rest.starts_with(**k))
        {
            out.push(match *keyword {
                "min:" => OpbTok::Min,
                "max:" => OpbTok::Max,
                _ => OpbTok::Preserved,
            });
            i += keyword.len();
        } else if s[i] == b'*' {
            break;
        } else if rest.starts_with(">=") {
            out.push(OpbTok::Ge);
            i += 2;
        } else if rest.starts_with("<=") {
            out.push(OpbTok::Le);
            i += 2;
        } else if s[i] == b'=' {
            out.push(OpbTok::Eq);
            i += 1;
        } else if s[i] == b';' {
            out.push(OpbTok::Semi);
            i += 1;
        } else if s[i] == b'~' {
            out.push(OpbTok::Tilde);
            i += 1;
        } else if s[i] == b'@' {
            let mut j = i + 1;
            while j < s.len() && is_ident_continue(s[j]) {
                j += 1;
            }
            if j == i + 1 {
                return Err(ReadError::at(line_no, "`@` with no label name after it"));
            }
            out.push(OpbTok::Label);
            i = j;
        } else if is_ident_start(s[i]) {
            let mut j = i + 1;
            while j < s.len() && is_ident_continue(s[j]) {
                j += 1;
            }
            if j - i < 2 {
                return Err(ReadError::at(
                    line_no,
                    format!(
                        "variable name {:?} is shorter than two characters",
                        &line[i..j]
                    ),
                ));
            }
            out.push(OpbTok::Var(&line[i..j]));
            i = j;
        } else if let Some((text, next)) = scan_int(s, i) {
            out.push(OpbTok::Int(text));
            i = next;
        } else {
            return Err(ReadError::at(
                line_no,
                format!("unrecognized input {:?}", &line[i..]),
            ));
        }
        i = skip_spaces(s, i);
    }
    Ok(out)
}

/// Read `[~] var` at `pos`, advancing it.
fn opb_literal(
    tokens: &[OpbTok<'_>],
    pos: &mut usize,
    line_no: usize,
) -> Result<(String, bool), ReadError> {
    let negated = matches!(tokens.get(*pos), Some(OpbTok::Tilde));
    if negated {
        *pos += 1;
    }
    match tokens.get(*pos) {
        Some(OpbTok::Var(name)) => {
            *pos += 1;
            Ok((name.to_string(), negated))
        }
        _ => Err(ReadError::at(line_no, "expected a variable name")),
    }
}

fn read_opb(bytes: &[u8]) -> Result<Formula, ReadError> {
    let mut formula = Formula::default();
    let mut seen_preserved = false;

    for (line_no, raw) in split_lines(bytes).into_iter().enumerate() {
        let line = decode(raw, line_no)?;
        let tokens = opb_tokens(line, line_no)?;
        let mut pos = 0usize;
        // A leading `@label` only names the constraint's database id; it
        // changes nothing about the constraint itself, so it is skipped.
        if matches!(tokens.first(), Some(OpbTok::Label)) {
            pos = 1;
        }
        match tokens.get(pos) {
            // Blank line, or a line that was nothing but a comment.
            None => continue,
            Some(tok @ (OpbTok::Min | OpbTok::Max)) => {
                // the development design notes §XPB Grammar:
                //
                //     xpb ::= {xpb_skip}, [xpb_objective], {xpb_skip | xpb_constraint}
                //
                // — at most one objective, before every constraint. This
                // reader used to assign on `min:`/`max:` wherever it stood, so
                // a second objective silently replaced the first and an
                // objective after the constraints read as if it led the file:
                // the same dropped-data shape as the one-item-per-line hole
                // below, and like that one it is enforced here on this
                // reader's own terms rather than by trusting the primary
                // reader to have refused first.
                if formula.objective.is_some() {
                    return Err(ReadError::at(
                        line_no,
                        "the file already has an objective; the XPB grammar \
                         allows at most one `min:`/`max:` line",
                    ));
                }
                if !formula.constraints.is_empty() {
                    return Err(ReadError::at(
                        line_no,
                        "an objective after a constraint; the XPB grammar puts \
                         the objective before every constraint",
                    ));
                }
                let maximize = matches!(tok, OpbTok::Max);
                pos += 1;
                formula.objective = Some(opb_objective(&tokens, &mut pos, line_no, maximize)?);
            }
            // `preserved: v1 v2 ;` names the projected variable set. It adds
            // no constraint and no objective term, so the reader only checks
            // that it is shaped like a variable list and moves on; see the
            // crate-level list of what the cross-check does not cover. The XPB
            // grammar does not define `preserved:` (it is an extension the
            // checker reads), so its placement is free — but a second list
            // would silently replace the first in the primary reader, which
            // refuses it, and this reader refuses on the same line.
            Some(OpbTok::Preserved) => {
                if seen_preserved {
                    return Err(ReadError::at(
                        line_no,
                        "the file already has a `preserved:` list; a second one \
                         would silently replace the first",
                    ));
                }
                seen_preserved = true;
                pos += 1;
                loop {
                    match tokens.get(pos) {
                        Some(OpbTok::Var(_)) => pos += 1,
                        Some(OpbTok::Semi) | None => break,
                        _ => {
                            return Err(ReadError::at(
                                line_no,
                                "expected a variable name or `;` in `preserved:`",
                            ));
                        }
                    }
                }
            }
            _ => {
                let (geq, leq) = opb_constraint(&tokens, &mut pos, line_no)?;
                formula.constraints.push(geq);
                if let Some(leq) = leq {
                    formula.constraints.push(leq);
                }
            }
        }

        // One line, one item -- and this reader has to enforce it for itself.
        //
        // The primary reader had the same hole: it lexed a line, parsed one
        // item and moved on, so a second constraint written after the first `;`
        // on the same line was silently discarded and the formula was checked
        // against a strict subset of itself. `1 x1 >= 1 ; 1 ~x1 >= 1 ;` on one
        // line is unsatisfiable and verified as `s VERIFIED SATISFIABLE`.
        //
        // The point of this crate is to be the *independent* reading that
        // catches exactly that class -- "formula stored is not the formula on
        // disk", which is where defects 16 and 17 lived. It did not, because it
        // was written to the same shape and inherited the same lenience: on
        // that input `--kernel-verify` reported "1 formula constraint(s)
        // cross-checked against the file on disk; nothing outside the proved
        // fragment". An independent reader that shares the primary reader's
        // blind spot is not a cross-check, so this is fixed here on its own
        // terms and not by reference to the other fix.
        // The item parsers `break` *on* the terminating `;` without stepping
        // over it, so skip exactly one before asking whether anything is left.
        if matches!(tokens.get(pos), Some(OpbTok::Semi)) {
            pos += 1;
        }
        if pos < tokens.len() {
            return Err(ReadError::at(
                line_no,
                "a formula file holds one constraint, objective or `preserved:` \
                 list per line; found more after the `;`",
            ));
        }
    }

    Ok(formula)
}

/// Read an objective body (after `min:` / `max:`).
///
/// the development design notes §Objectives and Constraints:
/// `objective ::= sum, [skip, coefficient] | coefficient`, i.e. a run of
/// `coefficient literal` pairs optionally followed by a bare coefficient,
/// which is the additive constant. `min: 0` is the empty objective and
/// `min: ;` is too.
///
/// A `max:` objective is negated — coefficients and constant — because the
/// checker only ever minimizes.
fn opb_objective(
    tokens: &[OpbTok<'_>],
    pos: &mut usize,
    line_no: usize,
    maximize: bool,
) -> Result<Objective, ReadError> {
    let mut objective = Objective::default();
    loop {
        let coeff = match tokens.get(*pos) {
            Some(OpbTok::Int(text)) => {
                *pos += 1;
                int_value(text)
            }
            Some(OpbTok::Semi) | None => break,
            _ => return Err(ReadError::at(line_no, "expected a coefficient or `;`")),
        };
        // A coefficient with no literal after it is the constant, and the
        // grammar only allows it at the very end.
        match tokens.get(*pos) {
            Some(OpbTok::Semi) | None => {
                objective.constant += coeff;
                break;
            }
            _ => {
                let (var, negated) = opb_literal(tokens, pos, line_no)?;
                objective.terms.push(Term {
                    coeff,
                    var,
                    negated,
                });
            }
        }
    }
    if maximize {
        objective.constant = -objective.constant;
        for term in &mut objective.terms {
            term.coeff = -term.coeff.clone();
        }
    }
    Ok(objective)
}

/// Read a constraint body: `{ coefficient literal } relop degree ;`.
///
/// Returns the `>=` form, plus a second constraint when the operator is `=`.
///
/// The three operators:
///
/// * `>=` is stored as written;
/// * `<=` is stored as its negation — **every** coefficient and the degree
///   are negated, because `sum c_i l_i <= d` is `sum (-c_i) l_i >= -d`. The
///   negation is exact here (`BigInt`), which is the point: doing it in the
///   constraint's own machine width is defect 6, where `<= i64::MIN` wrapped
///   into a trivially true row;
/// * `=` is both, in that order — the `>=` half first, then the `<=` half —
///   because that is the order the checker files them at consecutive database
///   ids.
fn opb_constraint(
    tokens: &[OpbTok<'_>],
    pos: &mut usize,
    line_no: usize,
) -> Result<(Constraint, Option<Constraint>), ReadError> {
    let line = line_no + 1;
    let mut terms: Vec<Term> = Vec::new();
    let operator = loop {
        match tokens.get(*pos) {
            Some(OpbTok::Ge) => {
                *pos += 1;
                break OpbTok::Ge;
            }
            Some(OpbTok::Le) => {
                *pos += 1;
                break OpbTok::Le;
            }
            Some(OpbTok::Eq) => {
                *pos += 1;
                break OpbTok::Eq;
            }
            Some(OpbTok::Int(text)) => {
                let coeff = int_value(text);
                *pos += 1;
                let (var, negated) = opb_literal(tokens, pos, line_no)?;
                terms.push(Term {
                    coeff,
                    var,
                    negated,
                });
            }
            _ => {
                return Err(ReadError::at(
                    line_no,
                    "expected a coefficient, `>=`, `<=` or `=`",
                ));
            }
        }
    };
    let degree = match tokens.get(*pos) {
        Some(OpbTok::Int(text)) => {
            *pos += 1;
            int_value(text)
        }
        _ => return Err(ReadError::at(line_no, "expected the degree")),
    };
    // The checker's parser requires the `;` and ignores whatever follows it
    // on the line, so the reader does the same rather than being stricter.
    match tokens.get(*pos) {
        Some(OpbTok::Semi) => {}
        _ => return Err(ReadError::at(line_no, "expected `;` after the degree")),
    }

    let negated = || Constraint {
        terms: terms
            .iter()
            .map(|t| Term {
                coeff: -t.coeff.clone(),
                var: t.var.clone(),
                negated: t.negated,
            })
            .collect(),
        degree: -degree.clone(),
        line,
    };
    let as_written = || Constraint {
        terms: terms.clone(),
        degree: degree.clone(),
        line,
    };
    Ok(match operator {
        OpbTok::Ge => (as_written(), None),
        OpbTok::Le => (negated(), None),
        _ => (as_written(), Some(negated())),
    })
}

#[cfg(test)]
mod tests;
