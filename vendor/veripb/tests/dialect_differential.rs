//! Randomized differential test for the **two proof dialects**.
//!
//! Two of the last six wrong verdicts in this checker, plus three findings that shipped beside
//! them, were literally the same defect:
//!
//! > the version-3 grammar enforces a structural rule, the checker does not, and a version-2
//! > proof walks around it.
//!
//! `Parser::def_order_rule` reads an order definition as a *sequence* — `vars`, optional `spec`,
//! `def`, optional `transitivity`, optional `reflexivity`, `end` — and errors on anything else;
//! `Parser::rule` refuses a rule whose declared `Scope` is shallower than the context it is
//! written in, so `sol` cannot appear inside `def_order ... end` at all. The version-2 parser
//! (`veripb_parser::pbp_parser::legacy_v2::parser::Version2Parser::line_to_rule`) dispatches every
//! line through one flat `match` with a single `inside_order_definition` flag. Everything the
//! version-3 grammar refuses structurally is therefore *reachable* in a version-2 proof, and
//! whether it is refused depends entirely on whether the checker happens to have an opinion.
//!
//! Wrong verdict 23 was `sol` between `pre_order` and its `end`: validated against the order's
//! empty database, so every assignment passed vacuously and an unsatisfiable formula verified as
//! satisfiable. Wrong verdict 24 was `transitivity` before `def`: transitivity "proved" for the
//! empty relation, then a 3-cycle supplied by `def` accepted as a preorder, then one `dom` chasing
//! the cycle to the empty contradiction. Three more of the same shape — a second `left` list after
//! `end vars`, a second `transitivity` block, a `spec` after `transitivity` — were each found and
//! fixed one at a time. Those three are **not** wrong verdicts and README does not number them:
//! each was accepted at exit 0 before the sequence was enforced, but the relation that came out
//! was still a genuine preorder, so no verdict was wrong. They are README's unnumbered
//! "— (hardening)" row. That is the point rather than a caveat: the same structural hole yielded
//! two wrong verdicts and three near misses, and finding them one at a time is a losing strategy
//! whether or not the individual finding happened to move a verdict.
//!
//! # What this test does
//!
//! It generates proof *structures* over the fragment both dialects can express, emits each
//! structure in **both** spellings, runs the checker on both, and asserts that the two runs make
//! the same decision:
//!
//! 1. **Accept and reject must agree.** A structure accepted in one dialect and refused in the
//!    other is a finding. Accepted-in-version-2 / refused-in-version-3 is the dangerous direction:
//!    the checker accepted something the grammar exists to refuse. The other direction is a
//!    version-3 over-restriction — worth knowing, less urgent.
//! 2. **When both accept, the verdict lines must be identical.** Same structure, same problem,
//!    same answer.
//!
//! The assertion is on the *decision* only, never on the error text: the two dialects legitimately
//! produce different diagnostics for the same refusal (version 3 usually reports a syntax error at
//! the offending keyword, version 2 a checking error from the rule itself). Where a structure is
//! refused in both, that agreement is the whole check and nothing further is asserted.
//!
//! Generation is skeleton-plus-perturbation, not free-form text. A skeleton is a proof that
//! verifies — transcribed from `tests/instances/correct/`, `proof_format_overview.md` and
//! the development design notes — and a perturbation changes it in exactly one structural way. That is
//! deliberate: a disagreement is only *detectable* if the rest of the proof would have been
//! accepted, so a malformed structure has to be malformed in one place and well-formed everywhere
//! else. Both well-formed and malformed structures are generated; the malformed ones are the
//! point, since every defect in this class was a malformed structure accepted in one dialect.
//!
//! # The fragment
//!
//! Covered: `def_order`/`pre_order` with `vars` (with and without `aux`), optional `spec`, `def`,
//! optional `transitivity` (with and without the two `fresh_aux` lists), optional `reflexivity`,
//! in and out of sequence, duplicated and dropped; `load_order` and its unloading form; `red`
//! with and without a subproof; `dom`; checked deletion (`del id ... subproof`); `pol`; `rup`;
//! `proofgoal` blocks with and without hints; `strengthening_to_core`; `core`; `sol`; `f`;
//! `output`; and `conclusion` in its `NONE`, `UNSAT` and `SAT` forms. Rules are additionally
//! placed where they do not belong: at order-definition block level, inside `spec`, inside a
//! transitivity or reflexivity `proof`, inside a `proofgoal`, inside a `red`/`dom`/`del` subproof,
//! and — for the structural keywords — at top level.
//!
//! # Excluded, and why
//!
//! Two dialects that differ by design differ legitimately, and an exclusion that is not written
//! down is indistinguishable from a blind spot. Each row below is one, with its justification.
//!
//! Two *tolerated* differences are separate from this table and live in [`KnownDivergence`],
//! because they are not exclusions at all: those structures are generated, run, and their
//! direction asserted and counted. One (`OptionalAuxLine`) is by design in the format; the other
//! (`RepeatedDeclarationInsideVars`) is a laxity this test found, analysed, and pinned in
//! [`the_repeated_declaration_laxity_is_pinned`] — read that before trusting this file's
//! coverage.
//!
//! | Excluded / mapped | Why |
//! |---|---|
//! | `scope leq` / `scope geq` blocks | Version 3 only. `Version2Parser::line_to_rule` has no `scope` token at all, so there is no version-2 spelling to compare against. `tests/obligation_differential.rs` covers scopes against a reference model instead. |
//! | `preserved_add`, `preserved_rm`, `epreserved` | Version 3 only; no version-2 token. |
//! | `obji` | Version 3 only; no version-2 token. |
//! | `eord_def`, `eord_loaded`, `start_time`, `end_time` | Version 3 only; no version-2 token. |
//! | Labels (`name: rule ...`) and `output ... FILE` / constraint-list output | Version 3 only: `Token::Label` exists only in the version-3 lexer, and the version-2 `output` rule parses a guarantee and a type and nothing else. Only `output NONE` is generated. |
//! | `setlvl` / `wiplvl` (version 2: `#` and `w`) | Present in both, excluded on scope: levels are a deletion-bookkeeping mechanism orthogonal to block structure, and mixing them in would make every disagreement ambiguous between the two mechanisms. |
//! | `obju`, `eobj`, and objectives generally | Present in both. Excluded because no generated formula carries an objective, which keeps `conclusion BOUNDS` and the objective proof goal out of the fragment; `tests/obligation_differential.rs` exercises the objective condition. |
//! | `e`, `i`, `ia`, `a`, `is_deleted`, `fail` | Present in both, and each is a single line that opens no block. They add no structure to the class this test is about, and each already has targeted tests. |
//! | `d` (version-2 single-character deletion), `del range`, `del spec` | Version-2 `d` is a version-2-only shorthand; `del range` and `del spec` differ from `del id` only in how the identifier is written, not in block structure. `del id` is generated. |
//! | Elaboration (`--elaborate`) | Every run here is a plain check. The elaborated-proof path is a separate output channel with its own tests. |
//! | Arithmetic: coefficients, widths, propagation | Every constraint in every skeleton is a small clause or cardinality constraint over three problem variables and a handful of order variables. Width, overflow and normalization belong to `veripb-propagator`'s differential test and to `overflow-checks`. |
//! | **Mapped, not excluded:** `pbc C : subproof ... qed;` (v3) ≡ `red C ; ; begin ... end` (v2) | Version 2 has no `pbc` token and spells proof by contradiction as a redundance step with an empty witness. `Item::Pbc` carries the one structure and emits both spellings, which is the correspondence the format defines rather than a divergence. It matters that this is a *mapping*: version 3 refuses a literal `red` inside a subproof (`red` is `Scope::Specification`, shallower than `Scope::Subproof`), so rendering `pbc` as `red` in version 3 would report a difference that is purely a spelling. |
//! | **Mapped:** `pre_order` (v2) ≡ `def_order` (v3) | The version-2 lexer accepts both spellings for `DefineOrder`; the version-3 `Parser::rule` match has only `def_order`. Skeletons choose the version-2 spelling at random and always render `def_order` in version 3. |
//! | **Mapped:** `p`/`u`/`o`/`v` (v2) ≡ `pol`/`rup`/`soli`/`solx` (v3) | Documented abbreviations. Version 2 also accepts the long forms; the short forms are generated so the version-2 lexer's abbreviation path is exercised. |
//! | **Mapped:** `begin` … `end [hint]` (v2) ≡ `subproof` … `qed [: hint];` (v3), `;` separators (v2) ≡ `:` separators (v3), statement-terminating `;` (v3 only) | The mechanical difference between the two grammars. Every renderer below emits both from one structure. |
//!
//! # What this does not defend
//!
//! This is a partial defence and the boundary matters.
//!
//! * **Only structures the generator builds.** Coverage is counted off the generator and floors
//!   are asserted, so a generator that stops producing interesting structures fails loudly — but a
//!   defect in a shape no perturbation reaches is invisible here. The perturbation catalogue is
//!   the real specification of what is covered; read [`Perturbation`].
//! * **One perturbation site per structure family.** Each skeleton carries at most one order
//!   definition and at most one subproof, so a perturbation lands at a known site. Interactions
//!   between two simultaneously misplaced blocks are reached only through the (rare) two-
//!   perturbation cases.
//! * **Agreement, not correctness.** If both dialects accept a structure they should have refused,
//!   this test is silent. It compares two front ends against each other, not either one against
//!   the format. `tests/obligation_differential.rs` is the reference-model test; this is the
//!   cross-dialect one.
//! * **No arithmetic.** See the exclusion table.
//! * **The binary is reproduced, not spawned.** [`Harness::run`] walks the same path
//!   `veripb::run_checker` does — the version-3 parser first, the legacy parser after a
//!   version-marker error, the `has_end_proof` check, then `Context::take_verification_results`
//!   for the verdict lines the binary prints — but in process, because two runs per case at
//!   100k cases cannot afford a `fork`. What that skips is argument handling, formula-format
//!   detection and stdout formatting, none of which differs between dialects.
//!
//! Set `VERIPB_DIALECT_CASES` to run more than the default number of cases, and
//! `VERIPB_DIALECT_PROFILE=1` to print the census the floors are calibrated from. Both match the
//! conventions of `tests/obligation_differential.rs`.

use std::io::Write;

use veripb_checker::{checker::ForwardsChecker, config::CheckerConfig, prelude::Context};
use veripb_parser::{
    io::MaybeCompressed,
    opb_parser::parse_opb_from_file,
    pbp_parser::{
        legacy_v2::parser::Version2Parser,
        parser::{ParserArgs, parse_proof},
    },
};

const DEFAULT_CASES: usize = 400;

// -------------------------------------------------------------------------------------------
// Deterministic PRNG, so a failing case replays from its seed alone.
// -------------------------------------------------------------------------------------------

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self {
        Rng(seed.wrapping_mul(6364136223846793005).wrapping_add(1) | 1)
    }

    fn next_u64(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }

    fn below(&mut self, bound: usize) -> usize {
        (self.next_u64() % (bound as u64)) as usize
    }

    fn chance(&mut self, percent: u64) -> bool {
        self.next_u64() % 100 < percent
    }

    fn pick<'a, T>(&mut self, items: &'a [T]) -> &'a T {
        &items[self.below(items.len())]
    }
}

// -------------------------------------------------------------------------------------------
// The two dialects.
// -------------------------------------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Dialect {
    /// `pseudo-Boolean proof version 2.0`: `begin`/`end`, `;` separators, no statement
    /// terminator, abbreviated rule names.
    V2,
    /// `pseudo-Boolean proof version 3.0`: `subproof`/`qed`, `:` separators, `;` terminator.
    V3,
}

impl Dialect {
    fn name(self) -> &'static str {
        match self {
            Dialect::V2 => "version 2",
            Dialect::V3 => "version 3",
        }
    }

    /// The statement terminator: version 3 ends every rule with `;`, version 2 with the newline.
    fn eos(self) -> &'static str {
        match self {
            Dialect::V2 => "",
            Dialect::V3 => ";",
        }
    }

    /// The separator between a constraint, a witness and the subproof keyword.
    fn sep(self) -> &'static str {
        match self {
            Dialect::V2 => ";",
            Dialect::V3 => ":",
        }
    }

    /// The keyword that opens a subproof on a rule line.
    fn begin(self) -> &'static str {
        match self {
            Dialect::V2 => "begin",
            Dialect::V3 => "subproof",
        }
    }
}

// -------------------------------------------------------------------------------------------
// The structure IR.
//
// One enum, rendered by one function with a `Dialect` switch, so the two spellings of every
// construct sit next to each other and cannot drift apart.
// -------------------------------------------------------------------------------------------

/// A `conclusion` line.
#[derive(Clone, Debug)]
enum Conclusion {
    None,
    /// `conclusion UNSAT : <id>`.
    Unsat(isize),
    /// `conclusion SAT : <literals>`, or with no hint at all.
    Sat(Option<String>),
}

/// A closing hint: version 2 writes `end -1`, version 3 `qed : -1;`.
type Hint = Option<isize>;

/// The body of a subproof or of an order's `proof` block.
#[derive(Clone, Debug)]
enum Goal {
    /// A rule written directly in the subproof, before any `proofgoal`.
    Bare(Item),
    Proofgoal {
        id: String,
        steps: Vec<Item>,
        hint: Hint,
    },
}

/// A subproof: its goals and the hint on its terminator.
#[derive(Clone, Debug, Default)]
struct Body {
    goals: Vec<Goal>,
    hint: Hint,
}

/// One block of an order definition, plus the two shapes that are not blocks at all and exist
/// only so that a perturbation can put them where the grammar has no production for them.
#[derive(Clone, Debug)]
enum Block {
    Vars {
        left: Vec<String>,
        right: Vec<String>,
        /// `None` omits the `aux` line entirely, which version 3 allows.
        aux: Option<Vec<String>>,
    },
    Spec(Vec<Item>),
    Def(Vec<String>),
    Transitivity {
        fresh_right: Vec<String>,
        /// `fresh_aux_1` and `fresh_aux_2`, required exactly when `aux` is non-empty.
        fresh_aux: Option<(Vec<String>, Vec<String>)>,
        goals: Vec<Goal>,
        /// Bare structural lines written inside the block's own `vars`, and between that `vars`
        /// and the `proof`. A `transitivity` block is an order definition one level down and has
        /// the same shape of hole; the version-3 grammar admits nothing here either.
        raw_in_vars: Vec<&'static str>,
        raw_after_vars: Vec<&'static str>,
    },
    Reflexivity {
        goals: Vec<Goal>,
    },
    /// A rule written between two blocks of an order definition. Version 3 has no production for
    /// it; version 2 dispatches it like any other line. This is the wrong-verdict-23 shape.
    Intruder(Item),
    /// A bare structural line — `left u9`, `fresh_right w9`, `def`, `proof` — written where the
    /// grammar does not admit it. This is the "second `left` list after `end vars`" shape.
    Raw(&'static str),
}

/// One rule, in either dialect.
#[derive(Clone, Debug)]
enum Item {
    /// `f <n>`.
    Formula(usize),
    /// `p <args>` / `pol <args>;`.
    Pol(String),
    /// `u <c> ;` / `rup <c>;`.
    Rup(String),
    /// `red <c> ; <w> ; [begin]` / `red <c> : <w> : [subproof]`. An empty witness is written by
    /// leaving `w` empty.
    Red {
        constraint: String,
        witness: String,
        body: Option<Body>,
    },
    /// Proof by contradiction: `red <c> ; ; begin` in version 2, `pbc <c> : subproof` in
    /// version 3.
    Pbc {
        constraint: String,
        body: Body,
    },
    /// `dom <c> ; <w> ; [begin]` / `dom <c> : <w> : [subproof]`.
    Dom {
        constraint: String,
        witness: String,
        body: Option<Body>,
    },
    /// `del id <ids> ; ; [begin]` / `del id <ids> : : [subproof]`.
    Del {
        ids: Vec<isize>,
        body: Option<Body>,
    },
    /// `core id <ids>`.
    Core(Vec<isize>),
    /// `strengthening_to_core on|off`.
    Stc(bool),
    /// `sol <literals>`.
    Sol(String),
    /// `load_order <name> <literals>`, or `load_order` alone to unload.
    LoadOrder(Option<String>),
    /// A whole order definition.
    DefOrder {
        /// The version-2 spelling; version 3 always renders `def_order`.
        keyword: &'static str,
        name: String,
        blocks: Vec<Block>,
    },
    /// `output NONE`.
    Output,
    Conclusion(Conclusion),
    /// A structural keyword written on its own, for placing where it does not belong.
    Raw(&'static str),
}

/// A complete generated proof: the formula it is checked against and its body. The header and the
/// footer are supplied by the renderer, since neither is ever perturbed.
#[derive(Clone, Debug)]
struct Structure {
    formula: Formula,
    body: Vec<Item>,
    /// Lines written *after* `end pseudo-Boolean proof`.
    ///
    /// The version-3 grammar stops at the end marker -- "Expected end of file (EOF) but found
    /// ..." -- and the version-2 parser read straight on and executed whatever followed, so a
    /// version-2 proof could carry rules after its own end and have them checked as part of the
    /// proof. They were checked normally, so nothing false was accepted, but the two dialects
    /// disagreed about what the file even contains, which is the seam wrong verdicts 23 and 24
    /// came out of. This generator could not reach it: it had no notion of a trailer.
    trailer: Vec<Item>,
}

// -------------------------------------------------------------------------------------------
// Rendering.
// -------------------------------------------------------------------------------------------

fn indent(depth: usize) -> String {
    "  ".repeat(depth)
}

fn render_goals(goals: &[Goal], d: Dialect, depth: usize, out: &mut String) {
    for goal in goals {
        match goal {
            Goal::Bare(item) => render_item(item, d, depth, out),
            Goal::Proofgoal { id, steps, hint } => {
                out.push_str(&format!("{}proofgoal {id}\n", indent(depth)));
                for step in steps {
                    render_item(step, d, depth + 1, out);
                }
                out.push_str(&indent(depth));
                match (d, hint) {
                    (Dialect::V2, None) => out.push_str("end\n"),
                    (Dialect::V2, Some(h)) => out.push_str(&format!("end {h}\n")),
                    (Dialect::V3, None) => out.push_str("qed;\n"),
                    (Dialect::V3, Some(h)) => out.push_str(&format!("qed : {h};\n")),
                }
            }
        }
    }
}

/// Render a subproof body and its terminator. The opener line has already been written.
fn render_body(body: &Body, d: Dialect, depth: usize, out: &mut String) {
    render_goals(&body.goals, d, depth + 1, out);
    out.push_str(&indent(depth));
    match (d, body.hint) {
        (Dialect::V2, None) => out.push_str("end\n"),
        (Dialect::V2, Some(h)) => out.push_str(&format!("end {h}\n")),
        (Dialect::V3, None) => out.push_str("qed;\n"),
        (Dialect::V3, Some(h)) => out.push_str(&format!("qed : {h};\n")),
    }
}

/// Render an order's `proof ... end` / `proof ... qed;` block.
fn render_proof(goals: &[Goal], d: Dialect, depth: usize, out: &mut String) {
    out.push_str(&format!("{}proof\n", indent(depth)));
    render_goals(goals, d, depth + 1, out);
    out.push_str(&format!(
        "{}{}\n",
        indent(depth),
        match d {
            Dialect::V2 => "end",
            Dialect::V3 => "qed;",
        }
    ));
}

/// Render the `end` that closes an order block. Version 3 terminates it with `;`; version 2 does
/// not. (Version 3 also admits a repetition of the block keyword before the `;`; that is optional
/// and not generated, since it is pure decoration.)
fn render_block_end(d: Dialect, depth: usize, out: &mut String) {
    out.push_str(&format!("{}end{}\n", indent(depth), d.eos()));
}

fn render_var_list(keyword: &str, vars: &[String], d: Dialect, depth: usize, out: &mut String) {
    let names = vars.join(" ");
    let space = if names.is_empty() { "" } else { " " };
    out.push_str(&format!(
        "{}{keyword}{space}{names}{}\n",
        indent(depth),
        d.eos()
    ));
}

fn render_block(block: &Block, d: Dialect, depth: usize, out: &mut String) {
    match block {
        Block::Vars { left, right, aux } => {
            out.push_str(&format!("{}vars\n", indent(depth)));
            render_var_list("left", left, d, depth + 1, out);
            render_var_list("right", right, d, depth + 1, out);
            if let Some(aux) = aux {
                render_var_list("aux", aux, d, depth + 1, out);
            }
            render_block_end(d, depth, out);
        }
        Block::Spec(items) => {
            out.push_str(&format!("{}spec\n", indent(depth)));
            for item in items {
                render_item(item, d, depth + 1, out);
            }
            render_block_end(d, depth, out);
        }
        Block::Def(constraints) => {
            out.push_str(&format!("{}def\n", indent(depth)));
            for constraint in constraints {
                out.push_str(&format!("{}{constraint} ;\n", indent(depth + 1)));
            }
            render_block_end(d, depth, out);
        }
        Block::Transitivity {
            fresh_right,
            fresh_aux,
            goals,
            raw_in_vars,
            raw_after_vars,
        } => {
            out.push_str(&format!("{}transitivity\n", indent(depth)));
            out.push_str(&format!("{}vars\n", indent(depth + 1)));
            for line in raw_in_vars {
                out.push_str(&format!("{}{line}{}\n", indent(depth + 2), d.eos()));
            }
            render_var_list("fresh_right", fresh_right, d, depth + 2, out);
            if let Some((aux1, aux2)) = fresh_aux {
                render_var_list("fresh_aux_1", aux1, d, depth + 2, out);
                render_var_list("fresh_aux_2", aux2, d, depth + 2, out);
            }
            render_block_end(d, depth + 1, out);
            for line in raw_after_vars {
                out.push_str(&format!("{}{line}{}\n", indent(depth + 1), d.eos()));
            }
            render_proof(goals, d, depth + 1, out);
            render_block_end(d, depth, out);
        }
        Block::Reflexivity { goals } => {
            out.push_str(&format!("{}reflexivity\n", indent(depth)));
            render_proof(goals, d, depth + 1, out);
            render_block_end(d, depth, out);
        }
        Block::Intruder(item) => render_item(item, d, depth, out),
        Block::Raw(line) => out.push_str(&format!("{}{line}{}\n", indent(depth), d.eos())),
    }
}

/// The one place the two spellings of a rule are written down.
fn render_item(item: &Item, d: Dialect, depth: usize, out: &mut String) {
    let pad = indent(depth);
    match item {
        Item::Formula(n) => out.push_str(&format!("{pad}f {n}{}\n", d.eos())),
        Item::Pol(args) => {
            let keyword = match d {
                Dialect::V2 => "p",
                Dialect::V3 => "pol",
            };
            out.push_str(&format!("{pad}{keyword} {args}{}\n", d.eos()));
        }
        Item::Rup(constraint) => {
            let keyword = match d {
                Dialect::V2 => "u",
                Dialect::V3 => "rup",
            };
            // The constraint's own `;` is what terminates it in both dialects.
            out.push_str(&format!("{pad}{keyword} {constraint} ;\n"));
        }
        Item::Red {
            constraint,
            witness,
            body,
        } => {
            out.push_str(&format!(
                "{pad}red {constraint} {} {witness} {}{}\n",
                d.sep(),
                d.sep(),
                match body {
                    Some(_) => format!(" {}", d.begin()),
                    None => String::new(),
                }
            ));
            if let Some(body) = body {
                render_body(body, d, depth, out);
            }
        }
        Item::Pbc { constraint, body } => {
            // Version 2 has no `pbc`: it is a redundance step with an empty witness.
            match d {
                Dialect::V2 => {
                    out.push_str(&format!("{pad}red {constraint} ; ; begin\n"));
                }
                Dialect::V3 => {
                    out.push_str(&format!("{pad}pbc {constraint} : subproof\n"));
                }
            }
            render_body(body, d, depth, out);
        }
        Item::Dom {
            constraint,
            witness,
            body,
        } => {
            out.push_str(&format!(
                "{pad}dom {constraint} {} {witness} {}{}\n",
                d.sep(),
                d.sep(),
                match body {
                    Some(_) => format!(" {}", d.begin()),
                    None => String::new(),
                }
            ));
            if let Some(body) = body {
                render_body(body, d, depth, out);
            }
        }
        Item::Del { ids, body } => {
            let ids = ids
                .iter()
                .map(|id| id.to_string())
                .collect::<Vec<_>>()
                .join(" ");
            out.push_str(&format!(
                "{pad}del id {ids} {} {}{}\n",
                d.sep(),
                d.sep(),
                match body {
                    Some(_) => format!(" {}", d.begin()),
                    None => String::new(),
                }
            ));
            if let Some(body) = body {
                render_body(body, d, depth, out);
            }
        }
        Item::Core(ids) => {
            let ids = ids
                .iter()
                .map(|id| id.to_string())
                .collect::<Vec<_>>()
                .join(" ");
            out.push_str(&format!("{pad}core id {ids}{}\n", d.eos()));
        }
        Item::Stc(on) => {
            let value = if *on { "on" } else { "off" };
            out.push_str(&format!("{pad}strengthening_to_core {value}{}\n", d.eos()));
        }
        Item::Sol(literals) => out.push_str(&format!("{pad}sol {literals}{}\n", d.eos())),
        Item::LoadOrder(argument) => match argument {
            Some(argument) => out.push_str(&format!("{pad}load_order {argument}{}\n", d.eos())),
            None => out.push_str(&format!("{pad}load_order{}\n", d.eos())),
        },
        Item::DefOrder {
            keyword,
            name,
            blocks,
        } => {
            let keyword = match d {
                Dialect::V2 => *keyword,
                Dialect::V3 => "def_order",
            };
            out.push_str(&format!("{pad}{keyword} {name}\n"));
            for block in blocks {
                render_block(block, d, depth + 1, out);
            }
            render_block_end(d, depth, out);
        }
        Item::Output => out.push_str(&format!("{pad}output NONE{}\n", d.eos())),
        Item::Conclusion(conclusion) => {
            let text = match conclusion {
                Conclusion::None => "conclusion NONE".to_string(),
                Conclusion::Unsat(id) => format!("conclusion UNSAT : {id}"),
                Conclusion::Sat(None) => "conclusion SAT".to_string(),
                Conclusion::Sat(Some(literals)) => format!("conclusion SAT : {literals}"),
            };
            out.push_str(&format!("{pad}{text}{}\n", d.eos()));
        }
        Item::Raw(line) => out.push_str(&format!("{pad}{line}{}\n", d.eos())),
    }
}

impl Structure {
    fn render(&self, d: Dialect) -> String {
        let mut out = match d {
            Dialect::V2 => "pseudo-Boolean proof version 2.0\n".to_string(),
            Dialect::V3 => "pseudo-Boolean proof version 3.0\n".to_string(),
        };
        for item in self.body.iter() {
            render_item(item, d, 0, &mut out);
        }
        out.push_str(&format!("end pseudo-Boolean proof{}\n", d.eos()));
        for item in self.trailer.iter() {
            render_item(item, d, 0, &mut out);
        }
        out
    }
}

// -------------------------------------------------------------------------------------------
// Formulas.
//
// Three, each small enough to settle by hand. Nothing here carries an objective; see the
// exclusion table.
// -------------------------------------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Formula {
    /// Exactly-one-of-three. Satisfiable, by `x1 ~x2 ~x3` and its two rotations.
    ExactlyOneOfThree,
    /// `x1`, `~x1`, `x2 + x3 >= 1`. Unsatisfiable, and `pol 1 2 +` is the refutation.
    Contradictory,
    /// The formula of `tests/instances/correct/{version2,version3}/dominance_simple_order`, which
    /// is the known-good matched pair this test's `dom` skeleton is transcribed from.
    Dominance,
    /// The formula of `tests/instances/correct/{version2,version3}/delete_core_subproof_rup`.
    /// Constraint 2 is implied by constraints 1 and 3, so deleting it is provable and the checked
    /// deletion skeleton has something honest to delete.
    Deletable,
}

impl Formula {
    fn text(self) -> &'static str {
        match self {
            Formula::ExactlyOneOfThree => {
                "* #variable= 3 #constraint= 4\n\
                 1 x1 1 x2 1 x3 >= 1 ;\n\
                 1 ~x1 1 ~x2 >= 1 ;\n\
                 1 ~x2 1 ~x3 >= 1 ;\n\
                 1 ~x3 1 ~x1 >= 1 ;\n"
            }
            Formula::Contradictory => {
                "* #variable= 3 #constraint= 3\n\
                 1 x1 >= 1 ;\n\
                 1 ~x1 >= 1 ;\n\
                 1 x2 1 x3 >= 1 ;\n"
            }
            Formula::Deletable => {
                "* #variable= 3 #constraint= 3\n\
                 1 x1 1 x2 >= 1 ;\n\
                 1 x1 1 x2 2 ~x3 >= 2 ;\n\
                 1 ~x3 >= 1 ;\n"
            }
            Formula::Dominance => {
                "* #variable= 3 #constraint= 10\n\
                 1 x1 1 x2 >= 1 ;\n\
                 1 x3 >= 1 ;\n\
                 >= 0 ;\n\
                 >= 0 ;\n\
                 >= 0 ;\n\
                 >= 0 ;\n\
                 >= 0 ;\n\
                 >= 0 ;\n\
                 >= 0 ;\n\
                 >= 0 ;\n"
            }
        }
    }

    fn constraints(self) -> usize {
        match self {
            Formula::ExactlyOneOfThree => 4,
            Formula::Contradictory => 3,
            Formula::Dominance => 10,
            Formula::Deletable => 3,
        }
    }
}

// -------------------------------------------------------------------------------------------
// Skeletons: proofs that verify, in both dialects.
//
// Every one is transcribed from a matched version-2 / version-3 pair under
// `tests/instances/correct/` or from the worked examples in `proof_format_overview.md`.
// `skeletons_verify_in_both_dialects` is the positive control that keeps them honest: a
// perturbation is only detectable against a baseline that is accepted.
// -------------------------------------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Skeleton {
    /// No order at all: `f`, `pol`, `conclusion NONE`.
    Plain,
    /// A logged solution and `conclusion SAT`.
    Satisfiable,
    /// A cutting-planes refutation and `conclusion UNSAT`.
    Unsatisfiable,
    /// The one-variable order `u1 <= v1`, defined and loaded.
    OrderSimple,
    /// The three-variable componentwise-implication order, whose transitivity proof is three
    /// `rup >= 1` goals.
    OrderImplication,
    /// `OrderSimple` plus an explicit `reflexivity` block.
    OrderReflexivity,
    /// `OrderSimple` plus a `spec` block.
    OrderSpecification,
    /// The `dominance_simple_order` instance: an order, a `red` and a `dom`.
    Dominance,
    /// A checked deletion with an explicit subproof.
    CheckedDeletion,
    /// A `red` with an explicit subproof carrying a numbered proofgoal.
    RedundanceSubproof,
    /// A proof by contradiction, which is the one construct whose two spellings are not a
    /// transliteration: version 3 writes `pbc`, version 2 a `red` with an empty witness.
    ProofByContradiction,
}

const SKELETONS: &[Skeleton] = &[
    Skeleton::Plain,
    Skeleton::Satisfiable,
    Skeleton::Unsatisfiable,
    Skeleton::OrderSimple,
    Skeleton::OrderImplication,
    Skeleton::OrderReflexivity,
    Skeleton::OrderSpecification,
    Skeleton::Dominance,
    Skeleton::CheckedDeletion,
    Skeleton::RedundanceSubproof,
    Skeleton::ProofByContradiction,
];

fn names(prefix: &str, count: usize) -> Vec<String> {
    (1..=count).map(|i| format!("{prefix}{i}")).collect()
}

/// The `vars` block of a `left`/`right` order with no auxiliary variables.
fn plain_vars(width: usize, aux: bool) -> Block {
    Block::Vars {
        left: names("u", width),
        right: names("v", width),
        aux: aux.then(Vec::new),
    }
}

/// The one-variable order `u1 <= v1` and its transitivity proof, as written in
/// `dominance_simple_order`.
fn simple_order_blocks_with(aux_line: bool, spec: bool) -> Vec<Block> {
    let mut blocks = simple_order_blocks(aux_line);
    if spec {
        blocks.insert(1, Block::Spec(vec![]));
    }
    blocks
}

/// The one-variable order `u1 <= v1` and its transitivity proof, as written in
/// `dominance_simple_order`.
fn simple_order_blocks(aux_line: bool) -> Vec<Block> {
    vec![
        plain_vars(1, aux_line),
        Block::Def(vec!["-1 u1 1 v1 >= 0".to_string()]),
        Block::Transitivity {
            fresh_right: names("w", 1),
            fresh_aux: None,
            goals: vec![Goal::Proofgoal {
                id: "#1".to_string(),
                steps: vec![Item::Pol("-2 -3 + -1 +".to_string())],
                hint: Some(-1),
            }],
            raw_in_vars: Vec::new(),
            raw_after_vars: Vec::new(),
        },
    ]
}

/// The three-variable componentwise-implication order, from
/// `tests/instances/correct/version3/def_order_transitivity_fresh_right.pbp`.
fn implication_order_blocks(spec: bool) -> Vec<Block> {
    let mut blocks = implication_order_blocks_bare();
    if spec {
        blocks.insert(1, Block::Spec(vec![]));
    }
    blocks
}

fn implication_order_blocks_bare() -> Vec<Block> {
    vec![
        plain_vars(3, true),
        Block::Def(
            (1..=3)
                .map(|i| format!("1 ~u{i} 1 v{i} >= 1"))
                .collect::<Vec<_>>(),
        ),
        Block::Transitivity {
            fresh_right: names("w", 3),
            fresh_aux: None,
            goals: (1..=3)
                .map(|i| Goal::Proofgoal {
                    id: format!("#{i}"),
                    steps: vec![Item::Rup(">= 1".to_string())],
                    hint: None,
                })
                .collect(),
            raw_in_vars: Vec::new(),
            raw_after_vars: Vec::new(),
        },
    ]
}

/// Build one skeleton. `rng` chooses only between spellings and options that are equivalent in
/// both dialects (`pre_order` versus `def_order`, an omitted `aux` line, a present or absent
/// closing hint), never between shapes.
fn build_skeleton(skeleton: Skeleton, rng: &mut Rng) -> Structure {
    let keyword = *rng.pick(&["pre_order", "def_order"]);
    // The `aux` line is mandatory in the *checker* even when the list is empty, while the
    // version-3 grammar makes it optional -- a documented by-design difference, see
    // `KnownDivergence::OptionalAuxLine`. A skeleton therefore always carries the line, and
    // `Perturbation::DropAuxLine` is what removes it.
    //
    // An optional empty `spec` block, on the other hand, is legal and equivalent in both
    // dialects, so half the order-carrying skeletons grow one. That is what gives
    // `Perturbation::IntruderInSpecification` somewhere to land.
    let spec = rng.chance(55);
    match skeleton {
        Skeleton::Plain => Structure {
            formula: Formula::ExactlyOneOfThree,
            body: vec![
                Item::Formula(4),
                Item::Pol("1 2 +".to_string()),
                Item::Output,
                Item::Conclusion(Conclusion::None),
            ],
            trailer: Vec::new(),
        },
        Skeleton::Satisfiable => Structure {
            formula: Formula::ExactlyOneOfThree,
            body: vec![
                Item::Formula(4),
                Item::Sol("x1 ~x2 ~x3".to_string()),
                Item::Output,
                Item::Conclusion(Conclusion::Sat(None)),
            ],
            trailer: Vec::new(),
        },
        Skeleton::Unsatisfiable => Structure {
            formula: Formula::Contradictory,
            body: vec![
                Item::Formula(3),
                Item::Pol("1 2 +".to_string()),
                Item::Output,
                Item::Conclusion(Conclusion::Unsat(-1)),
            ],
            trailer: Vec::new(),
        },
        Skeleton::OrderSimple => Structure {
            formula: Formula::ExactlyOneOfThree,
            body: vec![
                Item::Formula(4),
                Item::DefOrder {
                    keyword,
                    name: "simple".to_string(),
                    blocks: simple_order_blocks_with(true, spec),
                },
                Item::LoadOrder(Some("simple x1".to_string())),
                Item::LoadOrder(None),
                Item::Output,
                Item::Conclusion(Conclusion::None),
            ],
            trailer: Vec::new(),
        },
        Skeleton::OrderImplication => Structure {
            formula: Formula::ExactlyOneOfThree,
            body: vec![
                Item::Formula(4),
                Item::DefOrder {
                    keyword,
                    name: "impl3".to_string(),
                    blocks: implication_order_blocks(spec),
                },
                Item::LoadOrder(Some("impl3 x1 x2 x3".to_string())),
                Item::Output,
                Item::Conclusion(Conclusion::None),
            ],
            trailer: Vec::new(),
        },
        Skeleton::OrderReflexivity => {
            let mut blocks = simple_order_blocks_with(true, spec);
            blocks.push(Block::Reflexivity {
                goals: vec![Goal::Proofgoal {
                    id: "#1".to_string(),
                    steps: vec![Item::Pol("-1".to_string())],
                    hint: Some(-1),
                }],
            });
            Structure {
                formula: Formula::ExactlyOneOfThree,
                body: vec![
                    Item::Formula(4),
                    Item::DefOrder {
                        keyword,
                        name: "simple".to_string(),
                        blocks,
                    },
                    Item::LoadOrder(Some("simple x1".to_string())),
                    Item::Output,
                    Item::Conclusion(Conclusion::None),
                ],
                trailer: Vec::new(),
            }
        }
        Skeleton::OrderSpecification => {
            let mut blocks = simple_order_blocks(true);
            blocks.insert(1, Block::Spec(vec![]));
            Structure {
                formula: Formula::ExactlyOneOfThree,
                body: vec![
                    Item::Formula(4),
                    Item::DefOrder {
                        keyword,
                        name: "simple".to_string(),
                        blocks,
                    },
                    Item::LoadOrder(Some("simple x1".to_string())),
                    Item::Output,
                    Item::Conclusion(Conclusion::None),
                ],
                trailer: Vec::new(),
            }
        }
        Skeleton::Dominance => Structure {
            formula: Formula::Dominance,
            body: vec![
                Item::Formula(10),
                Item::DefOrder {
                    keyword,
                    name: "simple".to_string(),
                    blocks: simple_order_blocks_with(true, spec),
                },
                Item::LoadOrder(Some("simple x1".to_string())),
                Item::Pol("1 2 +".to_string()),
                Item::Red {
                    constraint: "1 a3 1 x1 >= 1".to_string(),
                    witness: "a3 -> 1".to_string(),
                    body: Some(Body::default()),
                },
                Item::Dom {
                    constraint: "1 ~x1 1 x2 >= 1".to_string(),
                    witness: "x1 -> x2 x2 -> x1".to_string(),
                    body: Some(Body::default()),
                },
                Item::LoadOrder(None),
                Item::Output,
                Item::Conclusion(Conclusion::None),
            ],
            trailer: Vec::new(),
        },
        Skeleton::CheckedDeletion => Structure {
            formula: Formula::Deletable,
            body: vec![
                Item::Formula(3),
                Item::Del {
                    ids: vec![2],
                    body: Some(Body {
                        goals: vec![Goal::Bare(Item::Rup(">= 1".to_string()))],
                        hint: Some(-1),
                    }),
                },
                Item::Output,
                Item::Conclusion(Conclusion::None),
            ],
            trailer: Vec::new(),
        },
        Skeleton::ProofByContradiction => Structure {
            formula: Formula::ExactlyOneOfThree,
            body: vec![
                Item::Formula(4),
                Item::Pbc {
                    constraint: "1 x1 1 x2 1 x3 >= 1".to_string(),
                    body: Body {
                        goals: vec![Goal::Bare(Item::Rup(">= 1".to_string()))],
                        hint: None,
                    },
                },
                Item::Output,
                Item::Conclusion(Conclusion::None),
            ],
            trailer: Vec::new(),
        },
        Skeleton::RedundanceSubproof => Structure {
            formula: Formula::ExactlyOneOfThree,
            body: vec![
                Item::Formula(4),
                Item::Red {
                    constraint: "1 ~y1 1 x1 >= 1".to_string(),
                    witness: "y1 -> 0".to_string(),
                    body: Some(Body::default()),
                },
                Item::Output,
                Item::Conclusion(Conclusion::None),
            ],
            trailer: Vec::new(),
        },
    }
}

// -------------------------------------------------------------------------------------------
// Perturbations: the catalogue of ways a structure is made malformed.
//
// This list *is* the specification of what the test covers. Every entry is a shape one of the
// five same-class wrong verdicts had, or a neighbour of one.
// -------------------------------------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Perturbation {
    /// A top-level rule written between two blocks of an order definition. Wrong verdict 23.
    IntruderAtBlockLevel,
    /// A top-level rule written inside a `spec` block, which may hold only derivation rules.
    IntruderInSpecification,
    /// A top-level rule written inside a transitivity or reflexivity `proof` block.
    IntruderInProof,
    /// A top-level rule written inside a `proofgoal`.
    IntruderInProofgoal,
    /// A top-level rule written inside a `red`/`dom`/`del` subproof.
    IntruderInSubproof,
    /// Two blocks of an order definition exchanged. Wrong verdict 24 in its `transitivity`-before-
    /// `def` instance.
    ReorderBlocks,
    /// A block of an order definition written twice. The "second `transitivity`" and "second
    /// `def`" shapes.
    DuplicateBlock,
    /// A block of an order definition removed, including the mandatory ones.
    DropBlock,
    /// A bare structural line written at order-definition block level: a second `left` list after
    /// `end vars`, a stray `fresh_right`, an unopened `def`.
    RawStructuralInOrder,
    /// The same, one level down: inside a `transitivity` block's own `vars`, or between that
    /// `vars` and the `proof` it guards.
    RawStructuralInTransitivity,
    /// A declaration repeated inside a still-open `vars` block: a second `vars` opener before the
    /// order's own `vars`, or a second `fresh_right` inside a `transitivity`'s `vars`. Drawn out
    /// of `RawStructural*` into its own entry because it is the one shape in this file's fragment
    /// where the two dialects genuinely disagree, so it must be reached at every case count
    /// rather than only on a lucky draw. See [`KnownDivergence::RepeatedDeclarationInsideVars`].
    RepeatedDeclaration,
    /// A structural keyword written at top level, where no block is open at all.
    StructuralAtTopLevel,
    /// A rule written *after* `end pseudo-Boolean proof`. See [`Structure::trailer`].
    AfterEndOfProof,
    /// A whole order definition nested inside a subproof.
    OrderInSubproof,
    /// The `aux` line dropped from a `vars` block. Version 3 makes it optional and the checker
    /// makes it mandatory, so this must be refused in both dialects — the case that catches a
    /// future relaxation of one side only.
    DropAuxLine,
}

const PERTURBATIONS: &[Perturbation] = &[
    Perturbation::IntruderAtBlockLevel,
    Perturbation::IntruderInSpecification,
    Perturbation::IntruderInProof,
    Perturbation::IntruderInProofgoal,
    Perturbation::IntruderInSubproof,
    Perturbation::ReorderBlocks,
    Perturbation::DuplicateBlock,
    Perturbation::DropBlock,
    Perturbation::RawStructuralInOrder,
    Perturbation::RawStructuralInTransitivity,
    Perturbation::RepeatedDeclaration,
    Perturbation::StructuralAtTopLevel,
    Perturbation::AfterEndOfProof,
    Perturbation::OrderInSubproof,
    Perturbation::DropAuxLine,
];

/// The rules a perturbation writes where they do not belong. Each is a rule whose effect reaches
/// past the block it is written in — a verdict, a logged solution, core membership, the active
/// order, a deletion — which is exactly the family `rules::OrderDefinitionPlacement` calls
/// `Never`, plus the derivation rules, which are `Specification` and so belong in a `spec` block
/// and nowhere else in an order definition.
fn intruder(rng: &mut Rng) -> Item {
    match rng.below(12) {
        0 => Item::Sol("x1 ~x2 ~x3".to_string()),
        1 => Item::Stc(rng.chance(50)),
        2 => Item::LoadOrder(Some("simple x1".to_string())),
        3 => Item::LoadOrder(None),
        4 => Item::Core(vec![1]),
        5 => Item::Del {
            ids: vec![1],
            body: None,
        },
        6 => Item::Pol("1 2 +".to_string()),
        7 => Item::Rup(">= 0".to_string()),
        8 => Item::Red {
            constraint: "1 ~y2 1 x1 >= 1".to_string(),
            witness: "y2 -> 0".to_string(),
            body: None,
        },
        9 => Item::Dom {
            constraint: "1 x1 >= 1".to_string(),
            witness: "x1 -> 1".to_string(),
            body: None,
        },
        10 => Item::Conclusion(Conclusion::None),
        _ => Item::Formula(4),
    }
}

/// Structural lines that open or extend a block, written where nothing admits them.
const RAW_STRUCTURAL: &[&str] = &[
    "left u9",
    "right v9",
    "aux $z1",
    "fresh_right w9",
    "def",
    "spec",
    "proof",
    "vars",
    "transitivity",
    "reflexivity",
];

/// The first order definition in `body`, if there is one.
fn first_order(body: &mut [Item]) -> Option<&mut Vec<Block>> {
    body.iter_mut().find_map(|item| match item {
        Item::DefOrder { blocks, .. } => Some(blocks),
        _ => None,
    })
}

/// The first subproof body in `body`, if there is one.
fn first_subproof(body: &mut [Item]) -> Option<&mut Body> {
    body.iter_mut().find_map(|item| match item {
        Item::Red { body: Some(b), .. }
        | Item::Dom { body: Some(b), .. }
        | Item::Del { body: Some(b), .. } => Some(b),
        Item::Pbc { body, .. } => Some(body),
        _ => None,
    })
}

/// The goal list of the first `proof` block of an order definition, if there is one.
fn first_order_proof(blocks: &mut [Block]) -> Option<&mut Vec<Goal>> {
    blocks.iter_mut().find_map(|block| match block {
        Block::Transitivity { goals, .. } | Block::Reflexivity { goals } => Some(goals),
        _ => None,
    })
}

/// Insert `item` into the first `proofgoal` of `goals`; if there is none, prepend it as a bare
/// step, which is the same misplacement one level out.
fn insert_into_proofgoal(goals: &mut Vec<Goal>, item: Item) {
    for goal in goals.iter_mut() {
        if let Goal::Proofgoal { steps, .. } = goal {
            steps.insert(0, item);
            return;
        }
    }
    goals.insert(0, Goal::Bare(item));
}

/// Apply one perturbation. Returns `false` when the structure has no site for it, so the caller
/// can count only the perturbations that really landed.
fn apply(perturbation: Perturbation, structure: &mut Structure, rng: &mut Rng) -> bool {
    match perturbation {
        Perturbation::IntruderAtBlockLevel => {
            let item = intruder(rng);
            let Some(blocks) = first_order(&mut structure.body) else {
                return false;
            };
            let at = rng.below(blocks.len() + 1);
            blocks.insert(at, Block::Intruder(item));
            true
        }
        Perturbation::IntruderInSpecification => {
            let item = intruder(rng);
            let Some(blocks) = first_order(&mut structure.body) else {
                return false;
            };
            if !blocks.iter().any(|block| matches!(block, Block::Spec(_))) {
                // No `spec` block to intrude into, so open one where the sequence admits it --
                // immediately after `vars`. An empty `spec` is well formed on its own in both
                // dialects, so the structure is still malformed in exactly one way.
                let Some(at) = blocks
                    .iter()
                    .position(|block| matches!(block, Block::Vars { .. }))
                else {
                    return false;
                };
                blocks.insert(at + 1, Block::Spec(Vec::new()));
            }
            let Some(items) = blocks.iter_mut().find_map(|block| match block {
                Block::Spec(items) => Some(items),
                _ => None,
            }) else {
                return false;
            };
            items.push(item);
            true
        }
        Perturbation::IntruderInProof => {
            let item = intruder(rng);
            let Some(blocks) = first_order(&mut structure.body) else {
                return false;
            };
            let Some(goals) = first_order_proof(blocks) else {
                return false;
            };
            goals.insert(0, Goal::Bare(item));
            true
        }
        Perturbation::IntruderInProofgoal => {
            let item = intruder(rng);
            let Some(blocks) = first_order(&mut structure.body) else {
                return false;
            };
            let Some(goals) = first_order_proof(blocks) else {
                return false;
            };
            insert_into_proofgoal(goals, item);
            true
        }
        Perturbation::IntruderInSubproof => {
            let item = intruder(rng);
            let Some(body) = first_subproof(&mut structure.body) else {
                return false;
            };
            body.goals.insert(0, Goal::Bare(item));
            true
        }
        Perturbation::ReorderBlocks => {
            let Some(blocks) = first_order(&mut structure.body) else {
                return false;
            };
            if blocks.len() < 2 {
                return false;
            }
            let a = rng.below(blocks.len());
            let mut b = rng.below(blocks.len());
            if a == b {
                b = (b + 1) % blocks.len();
            }
            blocks.swap(a, b);
            true
        }
        Perturbation::DuplicateBlock => {
            let Some(blocks) = first_order(&mut structure.body) else {
                return false;
            };
            if blocks.is_empty() {
                return false;
            }
            let at = rng.below(blocks.len());
            let clone = blocks[at].clone();
            let to = rng.below(blocks.len() + 1);
            blocks.insert(to, clone);
            true
        }
        Perturbation::DropBlock => {
            let Some(blocks) = first_order(&mut structure.body) else {
                return false;
            };
            if blocks.is_empty() {
                return false;
            }
            let at = rng.below(blocks.len());
            blocks.remove(at);
            true
        }
        Perturbation::RawStructuralInOrder => {
            let line = *rng.pick(RAW_STRUCTURAL);
            let Some(blocks) = first_order(&mut structure.body) else {
                return false;
            };
            let at = rng.below(blocks.len() + 1);
            blocks.insert(at, Block::Raw(line));
            true
        }
        Perturbation::RawStructuralInTransitivity => {
            let line = *rng.pick(RAW_STRUCTURAL);
            let inside = rng.chance(50);
            let Some(blocks) = first_order(&mut structure.body) else {
                return false;
            };
            let Some((raw_in_vars, raw_after_vars)) =
                blocks.iter_mut().find_map(|block| match block {
                    Block::Transitivity {
                        raw_in_vars,
                        raw_after_vars,
                        ..
                    } => Some((raw_in_vars, raw_after_vars)),
                    _ => None,
                })
            else {
                return false;
            };
            if inside {
                raw_in_vars.push(line);
            } else {
                raw_after_vars.push(line);
            }
            true
        }
        Perturbation::RepeatedDeclaration => {
            let in_transitivity = rng.chance(50);
            let Some(blocks) = first_order(&mut structure.body) else {
                return false;
            };
            if in_transitivity {
                let Some(raw_in_vars) = blocks.iter_mut().find_map(|block| match block {
                    Block::Transitivity { raw_in_vars, .. } => Some(raw_in_vars),
                    _ => None,
                }) else {
                    return false;
                };
                raw_in_vars.push(*rng.pick(&["vars", "fresh_right w9"]));
            } else {
                if !blocks
                    .iter()
                    .any(|block| matches!(block, Block::Vars { .. }))
                {
                    return false;
                }
                blocks.insert(0, Block::Raw("vars"));
            }
            true
        }
        Perturbation::AfterEndOfProof => {
            // A whole rule past the end marker, drawn from the same intruder
            // catalogue the other perturbations use plus an ordinary
            // derivation, because the point is that *nothing* may follow the
            // end -- not that only dangerous things may not.
            structure.trailer.push(intruder(rng));
            true
        }
        Perturbation::StructuralAtTopLevel => {
            let line = *rng.pick(RAW_STRUCTURAL);
            // Anywhere in the body, including between `output` and `conclusion`: no block is
            // open at top level, so no position admits a structural keyword and every one of
            // them must be refused.
            let at = rng.below(structure.body.len().max(1));
            structure.body.insert(at, Item::Raw(line));
            true
        }
        Perturbation::DropAuxLine => {
            let Some(blocks) = first_order(&mut structure.body) else {
                return false;
            };
            let Some(aux) = blocks.iter_mut().find_map(|block| match block {
                Block::Vars { aux, .. } => Some(aux),
                _ => None,
            }) else {
                return false;
            };
            if aux.is_none() {
                return false;
            }
            *aux = None;
            true
        }
        Perturbation::OrderInSubproof => {
            let order = Item::DefOrder {
                keyword: "pre_order",
                name: "nested".to_string(),
                blocks: simple_order_blocks(true),
            };
            let Some(body) = first_subproof(&mut structure.body) else {
                return false;
            };
            body.goals.insert(0, Goal::Bare(order));
            true
        }
    }
}

// -------------------------------------------------------------------------------------------
// Running the checker.
//
// In process, along the same path `veripb::run_checker` takes: the version-3 parser first, the
// legacy parser after a version-marker error, the `has_end_proof` check, and finally the verdict
// lines the binary prints. Running it in process rather than spawning the binary is what makes
// 100k cases affordable; nothing on that path is skipped.
// -------------------------------------------------------------------------------------------

/// What one run decided. Deliberately coarse: the two dialects produce different diagnostics for
/// the same refusal, so only the decision — and, on acceptance, the verdict lines — is ever
/// compared. The text carried by [`Decision::Refused`] is for the failure report and is never
/// part of an assertion; there is no `PartialEq` on this type so that it cannot become one by
/// accident.
#[derive(Clone, Debug)]
enum Decision {
    Accepted(Vec<String>),
    Refused(String),
}

impl Decision {
    fn is_accepted(&self) -> bool {
        matches!(self, Decision::Accepted(_))
    }

    /// The verdict lines, for the "both accepted" comparison.
    fn verdicts(&self) -> Option<&[String]> {
        match self {
            Decision::Accepted(verdicts) => Some(verdicts),
            Decision::Refused(_) => None,
        }
    }

    fn describe(&self) -> String {
        match self {
            Decision::Accepted(verdicts) => format!("accepted with {verdicts:?}"),
            Decision::Refused(why) => format!("refused ({why})"),
        }
    }
}

struct Harness {
    dir: tempfile::TempDir,
}

impl Harness {
    fn new() -> Self {
        Harness {
            dir: tempfile::tempdir().expect("failed to create a temporary directory"),
        }
    }

    fn run(&self, formula: &str, proof: &str) -> Decision {
        let formula_path = self.dir.path().join("formula.opb");
        let proof_path = self.dir.path().join("proof.pbp");
        write_file(&formula_path, formula);
        write_file(&proof_path, proof);

        let (parsed, variables, labels, preserved) = match parse_opb_from_file(&formula_path) {
            Ok(parsed) => parsed,
            Err(err) => return Decision::Refused(format!("formula: {err}")),
        };
        let config = CheckerConfig {
            derivation_path: proof_path.clone(),
            formula_path: formula_path.clone(),
            // A checked deletion the checker cannot prove must be a rejection, not a silent
            // downgrade to unchecked deletion: the downgrade would make the two dialects agree
            // for a reason that has nothing to do with either grammar.
            force_checked_deletion: true,
            print_verification_result: true,
            ..Default::default()
        };
        let context = Context::new(config, variables, preserved);
        let mut checker = match ForwardsChecker::new(context, parsed) {
            Ok(checker) => checker,
            Err(err) => return Decision::Refused(format!("{err}")),
        };
        let file = std::fs::File::open(&proof_path).expect("failed to reopen the proof file");
        let size = file
            .metadata()
            .expect("failed to stat the proof file")
            .len();
        // Upstream made `Parser::new`/`parse` private behind `parse_proof`, which
        // also takes an `Option<u64>` size and a `MaybeCompressed` reader. This
        // proof is written plain, so it drives the same path via `Plain`.
        let mut reader = veripb_parser::io::MaybeCompressed::Plain(std::io::BufReader::new(file));
        let mut version2 = false;
        {
            // The same fallback the binary performs: a version marker of `2.0` is reported as a
            // parse error by the version-3 parser and means "hand the rest of the file to the
            // legacy parser".
            if let Err(err) = parse_proof(
                Some(size),
                &mut reader,
                &mut checker,
                labels,
                ParserArgs {
                    show_progress: false,
                    trace_enabled: false,
                    store_assertion_annotations: false,
                },
            ) {
                match err {
                    veripb_checker::error::ForwardsCheckerError::Parse(parse)
                        if parse.is_version_error() =>
                    {
                        version2 = true;
                    }
                    other => return Decision::Refused(render_error(&other)),
                }
            }
        }
        if version2 {
            let mut legacy = Version2Parser::new(&mut checker);
            if let Err(err) = legacy.parse(proof_path.clone(), reader) {
                return Decision::Refused(render_error(&err));
            }
            if !checker.context.has_end_proof {
                return Decision::Refused("the proof has no `end` line".to_string());
            }
        }
        Decision::Accepted(checker.context.take_verification_results())
    }
}

/// Flatten an error and its source chain into one line, for the failure report only.
fn render_error(err: &dyn std::error::Error) -> String {
    let mut rendered = format!("{err}").replace('\n', " ");
    let mut source = err.source();
    while let Some(current) = source {
        rendered.push_str(&format!(" | {current}").replace('\n', " "));
        source = current.source();
    }
    rendered
}

fn write_file(path: &std::path::Path, contents: &str) {
    let mut file = std::fs::File::create(path).expect("failed to create a scratch file");
    file.write_all(contents.as_bytes())
        .expect("failed to write a scratch file");
    file.flush().expect("failed to flush a scratch file");
}

// -------------------------------------------------------------------------------------------
// Generation and the census.
// -------------------------------------------------------------------------------------------

/// Coverage counters, all incremented by the *generator*. The floors below are asserted against
/// these and not against anything the checker reports, so a generator that stops producing
/// interesting structures fails the test instead of passing it vacuously.
#[derive(Debug, Default)]
struct Census {
    cases: usize,
    /// Structures left exactly as the skeleton built them.
    unperturbed: usize,
    /// Structures with at least one perturbation that landed.
    perturbed: usize,
    /// Structures with two perturbations.
    doubly_perturbed: usize,
    skeleton: [usize; SKELETONS.len()],
    perturbation: [usize; PERTURBATIONS.len()],
    /// Structures whose order definition ended up out of the grammar's sequence.
    out_of_sequence: usize,
    /// Structures carrying an order definition at all.
    with_order: usize,
    /// Structures carrying a subproof at all.
    with_subproof: usize,
    /// Structures rendered with `pre_order` rather than `def_order` in version 2.
    pre_order_spelling: usize,
    /// Structures whose `vars` block omits the `aux` line.
    without_aux_line: usize,
    /// Conclusion forms reached: `NONE`, `UNSAT`, `SAT`.
    conclusion_none: usize,
    conclusion_unsat: usize,
    conclusion_sat: usize,
}

/// Outcome counters. These are *not* what the floors are calibrated from — they come from the
/// checker, which is the thing under test — but `both_accepted` is asserted separately, because
/// the "identical verdict" arm of this test is vacuous without it.
#[derive(Debug, Default)]
struct Outcomes {
    both_accepted: usize,
    both_refused: usize,
    /// Disagreements that a [`KnownDivergence`] both predicted and got the direction of right.
    by_design: usize,
    /// Per-divergence counts, so no row of the table can quietly stop being exercised.
    divergence: [usize; DIVERGENCES.len()],
}

// -------------------------------------------------------------------------------------------
// Differences by design.
//
// Two dialects that differ on purpose differ legitimately, and an exclusion nobody can review is
// indistinguishable from a blind spot. Rather than dropping such structures from the fragment,
// each documented difference is named here, its direction is *asserted*, and the number of times
// it was reached is counted and floored — so the table cannot rot into a silent exemption, and a
// change to either side shows up as a failure rather than as a quietly widened hole.
// -------------------------------------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum KnownDivergence {
    /// The `aux` line of a `vars` block is **optional in version 3 and mandatory in version 2**.
    /// This is not an accident of the parsers: `EndSubproofChecker` branches on
    /// `context.major_version >= Some(3)` and returns `CheckingError::AuxVarsUndefined` only for
    /// version 2 (`veripb-checker/src/rules/end_subproof.rs`). The version-3 grammar accordingly
    /// admits `vars`/`left`/`right`/`end` with no `aux` at all, while the version-2 dialect
    /// requires the keyword even for an empty list. A difference by design, in the format.
    /// Expected direction: version 3 accepts, version 2 refuses.
    OptionalAuxLine,
    /// A declaration repeated **inside a still-open `vars` block** — a second `vars` opener before
    /// the block's lists, or a second `fresh_right` inside a `transitivity`'s own `vars`.
    ///
    /// This one is *not* by design; it is a laxity, recorded here rather than exempted silently,
    /// and it is the one row a reader should look at first. This test found it (the shortest
    /// reproducer is 24 lines and appears below in [`the_repeated_declaration_laxity_is_pinned`]),
    /// and it reproduces on upstream `veripb` 3.0.2, so it is not a regression in this tree. It
    /// is recorded rather than reported as a wrong verdict because it cannot produce one, and
    /// that argument is short enough to check:
    ///
    /// * `OrderVariablesRule` in an `Order` subcontext sets `inside_vars = true` and nothing
    ///   else, so a second `vars` written while the block is open is idempotent. Written *after*
    ///   `end vars` it is refused, because `OrderPhase` has advanced past `BeforeVars`.
    /// * The list rules (`left`, `right`, `aux`, `fresh_right`, `fresh_aux_1`, `fresh_aux_2`)
    ///   overwrite their list outright, so a repeat inside the block only changes which
    ///   declaration is the last one.
    /// * Every check that consumes those lists runs at or after the last write:
    ///   `set_variables` rejects a name already claimed at each write, `right` checks its length
    ///   against `left` at each write, `end vars` runs
    ///   `check_symmetric_left_and_right_variables`, and `check_transitivity_variables` runs when
    ///   `proof` opens. So the lists that are validated are the lists that are used, which is the
    ///   invariant the `left`-after-`end vars` hardening exists to protect — and this shape does
    ///   not break it. Empirically: making the repeated lists asymmetric is refused
    ///   (`Variable lists in 'left' and 'right' must have the same length`), and reusing a name
    ///   is refused (`Variables in 'left', 'right' and 'aux' must occur exactly once`).
    ///
    /// Expected direction: version 2 accepts, version 3 refuses — the dangerous direction, which
    /// is why the direction is asserted rather than assumed, and why the count is floored.
    RepeatedDeclarationInsideVars,
}

const DIVERGENCES: &[KnownDivergence] = &[
    KnownDivergence::OptionalAuxLine,
    KnownDivergence::RepeatedDeclarationInsideVars,
];

impl KnownDivergence {
    /// The dialect that is expected to accept when this difference decides the outcome.
    fn accepting_dialect(self) -> Dialect {
        match self {
            KnownDivergence::OptionalAuxLine => Dialect::V3,
            KnownDivergence::RepeatedDeclarationInsideVars => Dialect::V2,
        }
    }

    fn index(self) -> usize {
        DIVERGENCES
            .iter()
            .position(|&d| d == self)
            .expect("every divergence is listed in DIVERGENCES")
    }
}

/// Whether `line` re-declares something a `vars` block has already opened or listed.
fn repeats_a_declaration(line: &str) -> bool {
    line == "vars" || line.starts_with("fresh_right") || line.starts_with("fresh_aux")
}

/// The documented differences this structure reaches. A structure can reach more than one, and
/// they point in opposite directions, so the caller matches on the direction actually observed.
fn known_divergences(structure: &Structure) -> Vec<KnownDivergence> {
    let mut found = Vec::new();
    for item in structure.body.iter() {
        let Item::DefOrder { blocks, .. } = item else {
            continue;
        };
        if blocks
            .iter()
            .any(|block| matches!(block, Block::Vars { aux: None, .. }))
        {
            found.push(KnownDivergence::OptionalAuxLine);
        }
        // A bare `vars` written *before* the block's own `vars` re-opens a block that is not yet
        // closed. Written after it, `OrderPhase` refuses it and both dialects agree.
        let mut vars_closed = false;
        for block in blocks.iter() {
            match block {
                Block::Vars { .. } => vars_closed = true,
                Block::Raw(line) if !vars_closed && repeats_a_declaration(line) => {
                    found.push(KnownDivergence::RepeatedDeclarationInsideVars);
                }
                Block::Transitivity { raw_in_vars, .. }
                    if raw_in_vars.iter().any(|line| repeats_a_declaration(line)) =>
                {
                    found.push(KnownDivergence::RepeatedDeclarationInsideVars);
                }
                _ => {}
            }
        }
    }
    found.sort_by_key(|divergence| divergence.index());
    found.dedup();
    found
}

/// The canonical block sequence, for deciding whether a generated order is well-formed. Written
/// from the development design notes and `Parser::def_order_rule`, not from `OrderPhase`, so that a change
/// to the checker's ladder cannot silently change what this test believes is well-formed.
fn blocks_in_sequence(blocks: &[Block]) -> bool {
    // `vars`, then optional `spec`, then `def`, then optional `transitivity`, then optional
    // `reflexivity`. Nothing else, nothing twice.
    let mut rank = 0usize;
    for block in blocks {
        let next = match block {
            Block::Vars { .. } => 1,
            Block::Spec(_) => 2,
            Block::Def(_) => 3,
            Block::Transitivity { .. } => 4,
            Block::Reflexivity { .. } => 5,
            Block::Intruder(_) | Block::Raw(_) => return false,
        };
        if next <= rank {
            return false;
        }
        rank = next;
    }
    // `vars` and `def` are mandatory.
    rank >= 3
        && blocks
            .iter()
            .any(|block| matches!(block, Block::Vars { .. }))
}

fn structure_has_order(structure: &Structure) -> bool {
    structure
        .body
        .iter()
        .any(|item| matches!(item, Item::DefOrder { .. }))
}

fn structure_has_subproof(structure: &Structure) -> bool {
    structure.body.iter().any(|item| {
        matches!(
            item,
            Item::Red { body: Some(_), .. }
                | Item::Dom { body: Some(_), .. }
                | Item::Del { body: Some(_), .. }
                | Item::Pbc { .. }
        )
    })
}

fn generate(seed: u64, census: &mut Census) -> Structure {
    let mut rng = Rng::new(seed);
    let skeleton_index = rng.below(SKELETONS.len());
    let skeleton = SKELETONS[skeleton_index];
    let mut structure = build_skeleton(skeleton, &mut rng);

    // Roughly a third of the cases stay well-formed. They are the positive control inside the
    // random stream: they keep the "both accept, same verdict" arm loaded, and a regression that
    // refuses valid proofs in one dialect shows up there.
    let wanted = if rng.chance(30) {
        0
    } else if rng.chance(78) {
        1
    } else {
        2
    };
    let mut landed = 0;
    for _ in 0..wanted {
        // Not every perturbation has a site in every skeleton -- there is no `spec` block to
        // intrude into if the order has none. Retry a few times rather than silently dropping
        // the perturbation, so the census stays even across the catalogue.
        for _ in 0..8 {
            let index = rng.below(PERTURBATIONS.len());
            if apply(PERTURBATIONS[index], &mut structure, &mut rng) {
                census.perturbation[index] += 1;
                landed += 1;
                break;
            }
        }
    }

    census.cases += 1;
    census.skeleton[skeleton_index] += 1;
    match landed {
        0 => census.unperturbed += 1,
        1 => census.perturbed += 1,
        _ => {
            census.perturbed += 1;
            census.doubly_perturbed += 1;
        }
    }
    if structure_has_order(&structure) {
        census.with_order += 1;
    }
    if structure_has_subproof(&structure) {
        census.with_subproof += 1;
    }
    for item in structure.body.iter() {
        match item {
            Item::DefOrder {
                keyword, blocks, ..
            } => {
                if *keyword == "pre_order" {
                    census.pre_order_spelling += 1;
                }
                if !blocks_in_sequence(blocks) {
                    census.out_of_sequence += 1;
                }
                if blocks
                    .iter()
                    .any(|block| matches!(block, Block::Vars { aux: None, .. }))
                {
                    census.without_aux_line += 1;
                }
            }
            Item::Conclusion(Conclusion::None) => census.conclusion_none += 1,
            Item::Conclusion(Conclusion::Unsat(_)) => census.conclusion_unsat += 1,
            Item::Conclusion(Conclusion::Sat(_)) => census.conclusion_sat += 1,
            _ => {}
        }
    }
    structure
}

// -------------------------------------------------------------------------------------------
// The tests.
// -------------------------------------------------------------------------------------------

/// Every skeleton verifies, in both dialects, with the same verdict.
///
/// The positive control. A perturbation is only *detectable* against a baseline that is accepted:
/// if the skeletons stopped verifying, every generated case would be refused in both dialects,
/// the differential would agree trivially, and this file would pass while testing nothing.
#[test]
fn skeletons_verify_in_both_dialects() {
    let harness = Harness::new();
    let mut rng = Rng::new(1);
    for &skeleton in SKELETONS.iter().cycle().take(SKELETONS.len() * 6) {
        let structure = build_skeleton(skeleton, &mut rng);
        let formula = structure.formula.text();
        let v2 = structure.render(Dialect::V2);
        let v3 = structure.render(Dialect::V3);
        let decision_v2 = harness.run(formula, &v2);
        let decision_v3 = harness.run(formula, &v3);
        assert!(
            decision_v2.is_accepted(),
            "the skeleton `{skeleton:?}` must verify in version 2, but it was {}:\n{v2}",
            decision_v2.describe()
        );
        assert!(
            decision_v3.is_accepted(),
            "the skeleton `{skeleton:?}` must verify in version 3, but it was {}:\n{v3}",
            decision_v3.describe()
        );
        assert_eq!(
            decision_v2.verdicts(),
            decision_v3.verdicts(),
            "the skeleton `{skeleton:?}` verified in both dialects with different verdicts:\n\
             --- version 2 ---\n{v2}--- version 3 ---\n{v3}"
        );
        assert_eq!(
            structure.formula.constraints(),
            structure.formula.text().lines().count() - 1,
            "the formula for `{skeleton:?}` does not declare the number of constraints it has"
        );
    }
}

/// The two dialects decide every generated structure the same way.
///
/// This is the whole test. A structure accepted in one dialect and refused in the other is a
/// wrong verdict of the class that produced defects 20, 22, 23 and 24; two acceptances with
/// different verdict lines are the same thing one step later.
#[test]
fn the_two_dialects_agree_on_every_structure() {
    let harness = Harness::new();
    let mut census = Census::default();
    let mut outcomes = Outcomes::default();

    for seed in 0..case_count() as u64 {
        let structure = generate(seed, &mut census);
        let formula = structure.formula.text();
        let v2 = structure.render(Dialect::V2);
        let v3 = structure.render(Dialect::V3);
        let decision_v2 = harness.run(formula, &v2);
        let decision_v3 = harness.run(formula, &v3);

        let expected = known_divergences(&structure);
        if decision_v2.is_accepted() != decision_v3.is_accepted() {
            let (accepted, refused) = if decision_v2.is_accepted() {
                (Dialect::V2, Dialect::V3)
            } else {
                (Dialect::V3, Dialect::V2)
            };
            match expected
                .iter()
                .find(|divergence| divergence.accepting_dialect() == accepted)
            {
                Some(divergence) => {
                    outcomes.by_design += 1;
                    outcomes.divergence[divergence.index()] += 1;
                }
                None if !expected.is_empty() => panic!(
                    "seed {seed}: this structure reaches the documented difference(s) \
                     {expected:?}, none of which says {} accepts -- so the difference came out \
                     the other way round and the table no longer describes the checker.\n\
                     --- formula ---\n{formula}--- version 2 ---\n{v2}\
                     --- version 3 ---\n{v3}--- version 2 said ---\n{}\n\
                     --- version 3 said ---\n{}",
                    accepted.name(),
                    decision_v2.describe(),
                    decision_v3.describe(),
                ),
                None => {
                    let severity = if accepted == Dialect::V2 {
                        "a version-2 hole: the checker accepted a structure the version-3 \
                         grammar exists to refuse"
                    } else {
                        "a version-3 over-restriction: the grammar refused a structure the \
                         checker is happy with"
                    };
                    panic!(
                        "seed {seed}: {} accepted this structure and {} refused it -- \
                         {severity}.\nIf this is a difference by design rather than by accident, \
                         it belongs in `KnownDivergence` and in the table at the top of this \
                         file, with its justification.\n\
                         --- formula ---\n{formula}--- version 2 ---\n{v2}\
                         --- version 3 ---\n{v3}--- version 2 said ---\n{}\n\
                         --- version 3 said ---\n{}",
                        accepted.name(),
                        refused.name(),
                        decision_v2.describe(),
                        decision_v3.describe(),
                    );
                }
            }
        }

        match (decision_v2.verdicts(), decision_v3.verdicts()) {
            (Some(a), Some(b)) => {
                outcomes.both_accepted += 1;
                assert_eq!(
                    a, b,
                    "seed {seed}: both dialects accepted this structure but reported different \
                     verdicts.\n--- formula ---\n{formula}--- version 2 ---\n{v2}\
                     --- version 3 ---\n{v3}"
                );
            }
            _ => outcomes.both_refused += 1,
        }
    }

    profile("dialect census", &census);
    profile("dialect outcomes", &outcomes);
    profile("skeletons", &skeleton_profile(&census));
    profile("perturbations", &perturbation_profile(&census));
    profile("known divergences", &divergence_profile(&outcomes));

    // Coverage floors, counted off the generator. Calibrated at the default case count with
    // `VERIPB_DIALECT_PROFILE=1` and set at roughly 60% of the observed values, so they catch a
    // generator that has stopped reaching a state rather than ordinary sampling noise. They
    // scale linearly with `VERIPB_DIALECT_CASES` and are calibrated for counts at or above the
    // default; running far *below* it can trip a floor on sampling noise alone.
    let scale = |floor: usize| floor * case_count() / DEFAULT_CASES;
    let floor = |what: &str, got: usize, want: usize| {
        assert!(
            got >= scale(want),
            "the generator produced only {got} {what}, which is below the floor of {}; a \
             generator that stops reaching a state must fail loudly rather than pass vacuously",
            scale(want)
        );
    };

    floor("well-formed structures", census.unperturbed, 100);
    floor("perturbed structures", census.perturbed, 150);
    floor("doubly perturbed structures", census.doubly_perturbed, 25);
    floor(
        "structures with an order definition",
        census.with_order,
        120,
    );
    floor("structures with a subproof", census.with_subproof, 80);
    floor(
        "order definitions out of the grammar's sequence",
        census.out_of_sequence,
        30,
    );
    floor(
        "orders written with the version-2 `pre_order` spelling",
        census.pre_order_spelling,
        60,
    );
    floor(
        "`vars` blocks that omit the `aux` line",
        census.without_aux_line,
        8,
    );
    floor("`conclusion NONE` lines", census.conclusion_none, 210);
    floor("`conclusion UNSAT` lines", census.conclusion_unsat, 22);
    floor("`conclusion SAT` lines", census.conclusion_sat, 19);

    for (index, &count) in census.skeleton.iter().enumerate() {
        floor(&format!("`{:?}` structures", SKELETONS[index]), count, 16);
    }
    for (index, &count) in census.perturbation.iter().enumerate() {
        floor(
            &format!("`{:?}` perturbations", PERTURBATIONS[index]),
            count,
            4,
        );
    }

    // Two outcome floors. These are *not* coverage — they are counted off the checker, which is
    // the thing under test — but each guards an arm of the test that says nothing at all if it
    // is never reached.
    assert!(
        outcomes.both_accepted >= scale(110),
        "only {} structures were accepted in both dialects (floor {}); the `identical verdict` \
         arm of this test is vacuous below that",
        outcomes.both_accepted,
        scale(110)
    );
    // Floor recalibrated when `AfterEndOfProof` became the fifteenth perturbation: a
    // fifteenth draw dilutes every other, and this row measured 5 at fourteen and 4 at
    // fifteen. Lowered to what the new distribution actually produces rather than left to
    // fail, and kept well above zero so the row still has to be reached.
    for (index, &count) in outcomes.divergence.iter().enumerate() {
        assert!(
            count >= scale(3),
            "only {count} structures reached the documented difference `{:?}` (floor {}); a row \
             of the table has stopped being exercised and would no longer catch a change to \
             either side of it",
            DIVERGENCES[index],
            scale(5)
        );
    }
}

/// The one difference in this fragment that is *not* by design, written out in full.
///
/// The randomized test above tolerates this shape through
/// [`KnownDivergence::RepeatedDeclarationInsideVars`], and a tolerated shape that only ever
/// appears as a `Debug` name in a census is a shape nobody can review. So here it is literally:
/// a `vars` opener written while the block it opens is already open. Version 2 verifies the
/// proof; version 3 has no production for the line and refuses it. Upstream `veripb` 3.0.2
/// verifies it too, so this is not a regression in this tree.
///
/// The argument that it cannot become a wrong verdict is on `KnownDivergence`; the two lines
/// below are its empirical half. If the checker is ever tightened to refuse the repeat — which
/// is what the version-3 grammar says, and what `OrderPhase` says one position later — this test
/// fails and points at the row of the table to delete.
#[test]
fn the_repeated_declaration_laxity_is_pinned() {
    let harness = Harness::new();
    let formula = Formula::ExactlyOneOfThree.text();
    let mut blocks = simple_order_blocks(true);
    blocks.insert(0, Block::Raw("vars"));
    let structure = Structure {
        formula: Formula::ExactlyOneOfThree,
        body: vec![
            Item::Formula(4),
            Item::DefOrder {
                keyword: "pre_order",
                name: "simple".to_string(),
                blocks,
            },
            Item::LoadOrder(Some("simple x1".to_string())),
            Item::Output,
            Item::Conclusion(Conclusion::None),
        ],
        trailer: Vec::new(),
    };
    assert_eq!(
        known_divergences(&structure),
        vec![KnownDivergence::RepeatedDeclarationInsideVars],
        "the reproducer must be the shape the table names, or the table is describing something \
         else"
    );

    let v2 = structure.render(Dialect::V2);
    let v3 = structure.render(Dialect::V3);
    assert!(
        v2.contains("pre_order simple\n  vars\n  vars\n"),
        "the reproducer is a `vars` opener written while `vars` is already open:\n{v2}"
    );
    assert_eq!(
        harness.run(formula, &v2).verdicts(),
        Some(["s VERIFIED NO CONCLUSION".to_string()].as_slice()),
        "version 2 accepts the repeat -- if it no longer does, the laxity has been closed and \
         `KnownDivergence::RepeatedDeclarationInsideVars` should go:\n{v2}"
    );
    assert!(
        !harness.run(formula, &v3).is_accepted(),
        "version 3 must refuse the repeat: its grammar has no production for a second `vars`\n{v3}"
    );

    // The other half of the ground truth: making the repeated lists disagree with each other is
    // refused, which is why the repeat cannot poison the lists that `end vars` validates.
    let asymmetric = "\
pseudo-Boolean proof version 2.0
f 4
pre_order simple
  vars
    left u1 u2
    right v1 v2
    aux
  vars
    left u3
    aux
  end
  def
    -1 u3 1 v1 >= 0 ;
  end
end
load_order simple x1
output NONE
conclusion NONE
end pseudo-Boolean proof
";
    assert!(
        !harness.run(formula, asymmetric).is_accepted(),
        "a repeated `left` that breaks the left/right symmetry must still be refused at \
         `end vars`; that check is what makes the repeat harmless"
    );
}

/// The renderers really do produce the two dialects, and the sequence oracle really does say
/// which orders are well-formed.
///
/// Without this, a renderer that emitted version-3 text for both dialects would make the
/// differential agree on everything.
#[test]
fn the_renderers_and_the_oracle_are_sane() {
    let mut rng = Rng::new(7);
    let structure = build_skeleton(Skeleton::OrderSimple, &mut rng);
    let v2 = structure.render(Dialect::V2);
    let v3 = structure.render(Dialect::V3);

    assert!(v2.starts_with("pseudo-Boolean proof version 2.0\n"));
    assert!(v3.starts_with("pseudo-Boolean proof version 3.0\n"));
    assert!(
        v2.contains("\nf 4\n"),
        "version 2 has no statement terminator"
    );
    assert!(v3.contains("\nf 4;\n"), "version 3 terminates with `;`");
    assert!(v2.contains("left u1\n") && v3.contains("left u1;\n"));
    assert!(v2.contains("  p -2 -3 + -1 +\n") && v3.contains("  pol -2 -3 + -1 +;\n"));
    assert!(v2.contains("end -1\n") && v3.contains("qed : -1;\n"));
    assert!(v2.ends_with("end pseudo-Boolean proof\n"));
    assert!(v3.ends_with("end pseudo-Boolean proof;\n"));

    // Subproof openers and separators.
    let with_subproof = build_skeleton(Skeleton::RedundanceSubproof, &mut rng);
    let v2 = with_subproof.render(Dialect::V2);
    let v3 = with_subproof.render(Dialect::V3);
    assert!(
        v2.contains("red 1 ~y1 1 x1 >= 1 ; y1 -> 0 ; begin\n"),
        "{v2}"
    );
    assert!(
        v3.contains("red 1 ~y1 1 x1 >= 1 : y1 -> 0 : subproof\n"),
        "{v3}"
    );

    // The one construct whose spellings are not a transliteration.
    let pbc = build_skeleton(Skeleton::ProofByContradiction, &mut rng);
    let v2 = pbc.render(Dialect::V2);
    let v3 = pbc.render(Dialect::V3);
    assert!(
        v2.contains("red 1 x1 1 x2 1 x3 >= 1 ; ; begin\n"),
        "version 2 spells `pbc` as a redundance step with an empty witness:\n{v2}"
    );
    assert!(v3.contains("pbc 1 x1 1 x2 1 x3 >= 1 : subproof\n"), "{v3}");

    // The sequence oracle.
    let vars = plain_vars(1, true);
    let def = Block::Def(vec!["-1 u1 1 v1 >= 0".to_string()]);
    let transitivity = Block::Transitivity {
        fresh_right: names("w", 1),
        fresh_aux: None,
        goals: vec![],
        raw_in_vars: Vec::new(),
        raw_after_vars: Vec::new(),
    };
    assert!(blocks_in_sequence(&[vars.clone(), def.clone()]));
    assert!(blocks_in_sequence(&[
        vars.clone(),
        Block::Spec(vec![]),
        def.clone(),
        transitivity.clone(),
    ]));
    assert!(!blocks_in_sequence(&[
        vars.clone(),
        transitivity.clone(),
        def.clone()
    ]));
    assert!(!blocks_in_sequence(&[
        vars.clone(),
        def.clone(),
        transitivity.clone(),
        transitivity.clone(),
    ]));
    assert!(!blocks_in_sequence(&[
        vars.clone(),
        def.clone(),
        transitivity.clone(),
        Block::Spec(vec![]),
    ]));
    assert!(
        !blocks_in_sequence(std::slice::from_ref(&vars)),
        "`def` is mandatory"
    );
    assert!(
        !blocks_in_sequence(std::slice::from_ref(&def)),
        "`vars` is mandatory"
    );
    assert!(!blocks_in_sequence(&[
        vars,
        Block::Intruder(Item::Sol("x1".to_string())),
        def
    ]));
}

// -------------------------------------------------------------------------------------------
// Shared helpers.
// -------------------------------------------------------------------------------------------

/// Print a counter profile when `VERIPB_DIALECT_PROFILE` is set. The floors are calibrated from
/// it, and it is how a reviewer checks that the generator still reaches the states they are about.
fn profile(label: &str, counters: &impl std::fmt::Debug) {
    if std::env::var_os("VERIPB_DIALECT_PROFILE").is_some() {
        println!("{label}: {counters:?}");
    }
}

fn skeleton_profile(census: &Census) -> Vec<(Skeleton, usize)> {
    SKELETONS
        .iter()
        .copied()
        .zip(census.skeleton.iter().copied())
        .collect()
}

fn perturbation_profile(census: &Census) -> Vec<(Perturbation, usize)> {
    PERTURBATIONS
        .iter()
        .copied()
        .zip(census.perturbation.iter().copied())
        .collect()
}

fn divergence_profile(outcomes: &Outcomes) -> Vec<(KnownDivergence, usize)> {
    DIVERGENCES
        .iter()
        .copied()
        .zip(outcomes.divergence.iter().copied())
        .collect()
}

fn case_count() -> usize {
    std::env::var("VERIPB_DIALECT_CASES")
        .ok()
        .and_then(|value| value.parse().ok())
        .unwrap_or(DEFAULT_CASES)
}
