//! Randomized differential test for the **subproof and obligation bookkeeping**.
//!
//! Every arithmetic acceptance in this checker now has a structural defence: the proved kernel
//! re-derives the rule, `overflow-checks` turns a wrap into an abort, the propagation state
//! machine is driven against a from-scratch reference (`veripb-propagator/tests/engine_differential.rs`),
//! and a second reader re-reads the formula. None of that touches the quadrant the last three
//! wrong verdicts came from: a rule opens a subproof, the subproof *owes* a set of proof
//! obligations, and something — a boolean, a list, a map lookup — is trusted to say that those
//! obligations were met. `--kernel-verify` cannot see it, because the proved kernel models
//! entailment and not the meta-rules (the development design notes section 7.4, boundary note 2).
//!
//! The invariant this test is about:
//!
//! > every proof obligation a rule creates is discharged only by evidence that actually
//! > establishes it, and no obligation is silently dropped.
//!
//! It is checked from five directions, against a reference model written from
//! `proof_format_overview.md` and the development design notes rather than from the code under test. The
//! reference shares no code with the checker: it is a bitmask enumerator over `1 << NUM_VARS`
//! assignments and a hand-transcribed table of which goals each rule owes. It never calls into
//! `veripb-checker` except through the proof text it hands over.
//!
//! One rule is an exception, and it is flagged here rather than buried: `dom` has no side
//! condition anywhere in this repository, so the reference's `dom` clauses are partly transcribed
//! from `veripb-checker/src/rules/dom_strengthening.rs` — the code they are supposed to audit.
//! See [`dominance_licensed`], and the boundary note below.
//!
//! **1. The obligation inventory** (`proofgoal_admission_matches_the_reference_inventory`).
//! The format fixes which goals a subproof owes and how they are named: "if a goal originates
//! from a constraint in the database the `<goalID>` is identical to the ConstraintID ...
//! otherwise the goalID begins with a `#` followed by a number which is increased for each goal
//! in the following order: the constraint to be derived (only redundance), one goal per
//! constraint in the current pre-order, one goal for the negated pre-order (only dominance),
//! objective condition". Scopes restrict which of those may be proven where: `scope leq` "may be
//! used to prove all proof goals except the negated-order goal", `scope geq` "is used exclusively
//! to prove the negated-order proof goal". [`Inventory`] is that paragraph, transcribed. The test
//! writes a `proofgoal <id>` line for a randomly chosen id and asserts that the checker admits
//! exactly the ids the inventory says exist, in exactly the scopes it says.
//!
//! **2. The semantics of an accepted rule** (`accepted_scripts_satisfy_the_reference_semantics`).
//! Over a universe small enough to enumerate (`NUM_VARS` variables, so `1 << NUM_VARS`
//! assignments), the reference decides each strengthening rule's side condition *exactly*, from
//! its definition in the format overview — for `red`, "every assignment satisfying the
//! constraints in the database F but falsifying the to-be-added constraint C can be transformed
//! into an assignment satisfying both by using the witness substitution", i.e.
//! `F /\ ~C |= (F /\ C)|w`, plus the order and objective side conditions (`dom` excepted — see
//! below). If the checker accepts a run, every rule in it must be licensed, and a satisfiable
//! formula must leave a satisfiable database. A dropped obligation shows up here as an accepted
//! rule the reference refuses. Both spellings of the `qed : <hint>` shortcut are generated, with
//! hints that are contradictions and hints that are not, because "discharged by a hint nobody
//! looked at" is exactly the shape of a dropped obligation.
//!
//! **3. Version-2 proof by contradiction**
//! (`version_two_empty_witness_redundance_needs_its_contradiction`). Version 2 spells `pbc` as a
//! `red` with an empty witness, which is the one shape where a subproof is a proof by
//! contradiction *and* carries numbered obligations. Whatever a nested proofgoal proves, the
//! constraint that comes out has to be entailed by the database.
//!
//! **4. Scope premises** (`scope_premises_do_not_license_a_strengthening_step`). A `scope`
//! introduces the loaded order's specification constraints as premises. Those are about the
//! order's auxiliary variables, and the test builds both the case where the database leaves
//! those variables alone and the case where it does not. Either way the `dom` that comes out of
//! the subproof has to satisfy the dominance condition.
//!
//! **5. Orders** (`accepted_orders_are_preorders`). `def_order` demands a preorder: "The order
//! must be a preorder, thus the defined order must be reflexive and transitive." The reference
//! computes the relation the `def` block denotes and checks both properties by enumeration over
//! all tuples. A `def_order` block the checker accepts must denote a preorder — in either
//! dialect, and whichever order its blocks are written in, because wrong verdict 24 was a
//! version-2 order whose `transitivity` block came before `def` and the version-3 grammar cannot
//! express that shape at all.
//!
//! # What this does not model
//!
//! This is a partial defence, and the boundary matters:
//!
//! * **How an obligation is discharged.** The reference has no model of autoproving, RUP, unit
//!   propagation, or cutting-planes arithmetic, and no opinion on whether a particular
//!   `proofgoal` body closes. Those are defended by the proved kernel, `overflow-checks`, and
//!   `veripb-propagator/tests/engine_differential.rs`. Every assertion here is one-sided in the
//!   safe direction: an accepted run must be licensed, a rejected one is never faulted.
//! * **Coefficient magnitude.** Everything is a small clause or cardinality constraint over at
//!   most `NUM_VARS` variables. Width, overflow and normalization are somebody else's test.
//! * **The premise sets, only as far as the reference tracks them.** The reference tracks which
//!   constraints are core and which are derived, and models `red`'s obligations as covering the
//!   derived set only when strengthening-to-core is off, `dom`'s as covering the core set
//!   always, and checked deletion's as proven from the core set alone. What it does not model is
//!   `only_core` deeper inside a subproof, where a checked deletion has already set it.
//! * **The `dom` side condition, which is not transcribed from this repository.** This is the
//!   one leg that is weaker than the other four, and it is weak in a way that matters: a
//!   differential against the code under test is not a differential.
//!   `proof_format_overview.md` gives `dom` a syntax, an example and a citation to [BGMN23], a
//!   paper that is not in this repository; the development design notes gives only the BNF. The parts that
//!   *can* be derived from the repository are derived and cited in [`dominance_licensed`]: the
//!   goal list, and the orientation of the pre-order and negated-pre-order goals, which the
//!   "Scopes Inside Subproofs" section fixes. Two clauses cannot be, and were read off
//!   `dom_strengthening.rs` instead — that the substituted obligations cover the core set rather
//!   than the whole database, and that the objective condition is non-strict under a loaded order
//!   and strict without one. Those two are marked `DomClause::CodeDerived` and counted
//!   (`dom_refused_by_code_derived_clause`) so the weakness is measured rather than assumed away.
//!   What still holds independently for `dom`: an accepted one must leave a satisfiable database,
//!   which is decided by enumeration and owes nothing to the code.
//! * **The `delc` substitution condition.** This reference briefly stated
//!   `order_loaded || strengthening_to_core`, because `proof_format_overview.md` did, and the
//!   checker guards on strengthening-to-core alone -- so the differential reported a
//!   disagreement. Chasing it to the mechanism showed the *document* was wrong: a checked
//!   deletion under a loaded order owes the order's proofgoals just as `red` does, so an
//!   order-worsening witness is already refused. The document has been corrected and the
//!   reference states the corrected condition. Recorded here because it is the failure mode of
//!   a specification-derived reference, and the one this file is otherwise built to avoid: it
//!   can inherit an error from the text instead of catching one in the code.
//! * **Rules outside the obligation quadrant.** `pol`, `obju`, `preserved_add`/`preserved_rm`,
//!   `sol`/`soli`/`solx`, assertions, levels, `output ... FILE` and the conclusion rules are not
//!   generated. Scripts end at `conclusion NONE`, so the verdict path itself is not exercised
//!   here — the wrong verdicts these rules produced show up one step earlier, as a rule the
//!   reference refuses.
//! * **Deep nesting.** Subproofs nest one `proofgoal` deep. A `pbc` inside a `proofgoal` inside a
//!   `red` subproof is legal and is not generated.
//! * **Elaboration.** Every run is a plain check; the elaborated-proof path is not exercised.
//!
//! # Running it
//!
//! `VERIPB_OBLIGATION_CASES` sets the number of cases. Every coverage floor in this file sits
//! behind `if cases >= DEFAULT_CASES`, so a value *below* the default runs the comparisons
//! without the floors — deliberately, because the override exists to replay a single failing seed
//! (`VERIPB_OBLIGATION_CASES=1` reruns seed 0) and a floor calibrated for 300 cases would fire on
//! every such replay. The consequence is worth stating plainly: `VERIPB_OBLIGATION_CASES=10` is a
//! near-vacuous run, and only the default or a larger value is a real one.
//!
//! `VERIPB_OBLIGATION_PROFILE` prints the state-coverage counters the floors are calibrated from.
//! Every counter a *generator-coverage* floor reads is computed from the reference's answer and
//! never from the checker's, so a broken checker cannot satisfy its own floor by misbehaving
//! consistently. The few counters that are read off the checker — `accepted`, `clean_accepted`,
//! `version_two_accepted`, and the legacy family's `accepted` — carry floors of the opposite
//! kind: they fail when the checker starts *rejecting* everything, which is the other way a
//! comparison goes vacuous, and no defect is helped by satisfying them.
//!
//! # Mutations this catches, and where
//!
//! Measured on this file at HEAD, one mutation at a time, reverted afterwards:
//!
//! * dropping the `is_contradicting()` check on the hinted **proofgoal** path
//!   (`rules/end_subproof.rs::end_proofgoal`) — first caught at 70 cases, twice in the default
//!   300. Before the hinted spellings existed this mutation survived 50 000 cases, because the
//!   generator only ever wrote `qed : <hint>` over a hint that was a contradiction;
//! * the same check on the hinted **subproof** path (`::end_subproof`) — first caught at 48
//!   cases, three times in the default 300;
//! * disabling the `OrderPhase` ladder (`order_context.rs`) — caught by
//!   `accepted_orders_are_preorders`, which then accepts `cyc3` (the 3-cycle of wrong verdict 24)
//!   and `nt2` as version-2 orders with `transitivity` before `def`;
//! * removing the auxiliary-variable freshness guard (`rules/scope.rs`) — caught by
//!   `scope_premises_do_not_license_a_strengthening_step` in the first eight cases.

use std::io::Write;

use veripb_checker::{
    checker::ForwardsChecker,
    config::CheckerConfig,
    error::{CheckingError, ForwardsCheckerError},
    prelude::Context,
};
use veripb_parser::{
    io::MaybeCompressed,
    opb_parser::parse_opb_from_file,
    pbp_parser::{
        legacy_v2::parser::Version2Parser,
        parser::{ParserArgs, parse_proof},
    },
};

// -------------------------------------------------------------------------------------------
// Sizing.
// -------------------------------------------------------------------------------------------

/// Problem variables `x1..xP`. Three of them are enough to load the cyclic order that defect 20
/// needs, and four keep the formulas non-trivial while `1 << NUM_VARS` stays tiny.
const NUM_PROBLEM_VARS: usize = 4;
/// One auxiliary variable, `$q`, so that an order with a `spec` block can be built and the
/// freshness premise defect 22 lived in can be reached.
const AUX_VAR: usize = NUM_PROBLEM_VARS;
const NUM_VARS: usize = NUM_PROBLEM_VARS + 1;
const NUM_ASSIGNMENTS: u32 = 1 << NUM_VARS;

const DEFAULT_CASES: usize = 300;

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
// Reference semantics.
//
// A constraint is `sum ci * li >= d` with every `ci > 0`, which is the normalized OPB form the
// format overview describes. An assignment is a bitmask over `NUM_VARS`.
// -------------------------------------------------------------------------------------------

/// `(coefficient, variable, negated)`; the literal is `~x{var}` when `negated`.
type Term = (i64, usize, bool);

#[derive(Clone, Debug, PartialEq, Eq)]
struct Constraint {
    terms: Vec<Term>,
    degree: i64,
}

fn lit_holds(assignment: u32, var: usize, negated: bool) -> bool {
    (((assignment >> var) & 1) == 1) != negated
}

fn var_name(var: usize) -> String {
    if var == AUX_VAR {
        "$q".to_string()
    } else {
        format!("x{}", var + 1)
    }
}

impl Constraint {
    fn holds(&self, assignment: u32) -> bool {
        let mut sum = 0i64;
        for &(coeff, var, negated) in self.terms.iter() {
            if lit_holds(assignment, var, negated) {
                sum += coeff;
            }
        }
        sum >= self.degree
    }

    /// OPB text, as both the formula file and the proof file spell it.
    fn render(&self) -> String {
        let mut out = String::new();
        for &(coeff, var, negated) in self.terms.iter() {
            out.push_str(&format!(
                "+{coeff} {}{} ",
                if negated { "~" } else { "" },
                var_name(var)
            ));
        }
        out.push_str(&format!(">= {}", self.degree));
        out
    }
}

/// The value a witness gives a variable: a constant or another literal.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum WitnessValue {
    Zero,
    One,
    Lit(usize, bool),
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct Witness(Vec<(usize, WitnessValue)>);

impl Witness {
    /// `a . w`: the assignment that reads `w`'s image under `a`. `C|w` is satisfied by `a`
    /// exactly when `C` is satisfied by `a . w`, which is why the reference never has to build a
    /// substituted constraint.
    fn apply(&self, assignment: u32) -> u32 {
        let mut out = assignment;
        for &(var, value) in self.0.iter() {
            let bit = match value {
                WitnessValue::Zero => false,
                WitnessValue::One => true,
                WitnessValue::Lit(source, negated) => lit_holds(assignment, source, negated),
            };
            if bit {
                out |= 1 << var;
            } else {
                out &= !(1 << var);
            }
        }
        out
    }

    fn render(&self) -> String {
        let mut out = String::new();
        for &(var, value) in self.0.iter() {
            out.push_str(&format!(
                "{} -> {} ",
                var_name(var),
                match value {
                    WitnessValue::Zero => "0".to_string(),
                    WitnessValue::One => "1".to_string(),
                    WitnessValue::Lit(source, negated) =>
                        format!("{}{}", if negated { "~" } else { "" }, var_name(source)),
                }
            ));
        }
        out.trim_end().to_string()
    }
}

/// A linear objective `sum ci * li`, minimized.
#[derive(Clone, Debug, Default)]
struct Objective {
    terms: Vec<Term>,
}

impl Objective {
    fn value(&self, assignment: u32) -> i64 {
        self.terms
            .iter()
            .filter(|&&(_, var, negated)| lit_holds(assignment, var, negated))
            .map(|term| term.0)
            .sum()
    }

    fn render(&self) -> String {
        let mut out = String::from("min: ");
        for &(coeff, var, negated) in self.terms.iter() {
            out.push_str(&format!(
                "+{coeff} {}{} ",
                if negated { "~" } else { "" },
                var_name(var)
            ));
        }
        out.push(';');
        out
    }
}

fn satisfies_all(constraints: &[Constraint], assignment: u32) -> bool {
    constraints.iter().all(|c| c.holds(assignment))
}

fn has_model(constraints: &[Constraint]) -> bool {
    (0..NUM_ASSIGNMENTS).any(|a| satisfies_all(constraints, a))
}

// -------------------------------------------------------------------------------------------
// Reference model of an order.
//
// The `def` block's constraints are written over formal variables: left `u1..uk` are reference
// variables `0..k`, right `v1..vk` are `k..2k`. The relation they denote is read off by
// enumeration: `p <= q` iff every definition constraint holds when `u := p` and `v := q`.
// -------------------------------------------------------------------------------------------

#[derive(Clone, Debug)]
struct OrderSpec {
    name: &'static str,
    arity: usize,
    /// Over formal variables: left `i`, right `arity + i`.
    definition: Vec<Constraint>,
    /// Whether the order declares `aux $q` and a `spec` block constraining it.
    with_spec: bool,
    /// The polarity the `spec` block pins `$q` to. Only meaningful with `with_spec`.
    spec_positive: bool,
}

/// How the `transitivity` block's `fresh_right` list is written. The format says the fresh right
/// variables are a vector `w` of the same length as `u` and `v`, distinct from them: "The
/// variables after `fresh_right` are the variables in w and the number of variables in w has to
/// be the same as in u (and v)". Everything but `Correct` is a spelling that violates that.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum FreshRight {
    Correct,
    Empty,
    Short,
    NotFresh,
}

impl OrderSpec {
    fn leq(&self, left: u32, right: u32) -> bool {
        let mut assignment = 0u32;
        for i in 0..self.arity {
            if (left >> i) & 1 == 1 {
                assignment |= 1 << i;
            }
            if (right >> i) & 1 == 1 {
                assignment |= 1 << (self.arity + i);
            }
        }
        self.definition.iter().all(|c| c.holds(assignment))
    }

    fn is_reflexive(&self) -> bool {
        (0..(1u32 << self.arity)).all(|p| self.leq(p, p))
    }

    fn is_transitive(&self) -> bool {
        let bound = 1u32 << self.arity;
        (0..bound).all(|p| {
            (0..bound)
                .all(|q| (0..bound).all(|r| !(self.leq(p, q) && self.leq(q, r)) || self.leq(p, r)))
        })
    }

    fn is_preorder(&self) -> bool {
        self.is_reflexive() && self.is_transitive()
    }

    /// The name a formal variable of the definition renders as.
    fn formal_name(&self, var: usize) -> String {
        if var < self.arity {
            format!("u{}", var + 1)
        } else {
            format!("v{}", var - self.arity + 1)
        }
    }

    fn render_definition(&self, c: &Constraint) -> String {
        let mut out = String::new();
        for &(coeff, var, negated) in c.terms.iter() {
            out.push_str(&format!(
                "+{coeff} {}{} ",
                if negated { "~" } else { "" },
                self.formal_name(var)
            ));
        }
        out.push_str(&format!(">= {}", c.degree));
        out
    }

    fn render(&self, fresh_right: FreshRight) -> Vec<String> {
        self.render_in(Dialect::Version3, BlockLayout::Sequential, fresh_right)
    }

    /// The `def_order` block, in one dialect and one block layout.
    ///
    /// The two axes exist because wrong verdict 24 needed both: a version-2 order whose
    /// `transitivity` block came *before* `def`. The version-3 grammar reads the blocks in
    /// sequence and cannot express that; the version-2 parser dispatches line by line and could,
    /// and `OrderProofRule` then built the transitivity obligations by iterating a definition
    /// that was still empty, proving transitivity of the empty relation and setting the flag the
    /// order's `end` trusts.
    fn render_in(
        &self,
        dialect: Dialect,
        layout: BlockLayout,
        fresh_right: FreshRight,
    ) -> Vec<String> {
        let semi = dialect.block_terminator();
        let mut vars = vec![
            "  vars".to_string(),
            format!(
                "    left {};",
                (0..self.arity)
                    .map(|i| format!("u{}", i + 1))
                    .collect::<Vec<_>>()
                    .join(" ")
            ),
            format!(
                "    right {};",
                (0..self.arity)
                    .map(|i| format!("v{}", i + 1))
                    .collect::<Vec<_>>()
                    .join(" ")
            ),
            format!("    aux{};", if self.with_spec { " $q" } else { "" }),
            format!("  end{semi}"),
        ];
        if dialect == Dialect::Version2 {
            // Version 2 has no statement terminator inside `vars`.
            for line in vars.iter_mut() {
                *line = line.trim_end_matches(';').to_string();
            }
        }

        let mut spec = Vec::new();
        if self.with_spec {
            spec.push("  spec".to_string());
            spec.push(if self.spec_positive {
                "    red +1 $q >= 1 : $q -> 1;".to_string()
            } else {
                "    red +1 ~$q >= 1 : $q -> 0;".to_string()
            });
            spec.push(format!("  end spec{semi}"));
        }

        let mut def = vec!["  def".to_string()];
        for c in self.definition.iter() {
            def.push(format!("    {};", self.render_definition(c)));
        }
        def.push(format!("  end{semi}"));

        let fresh = match fresh_right {
            FreshRight::Correct => (0..self.arity)
                .map(|i| format!("w{}", i + 1))
                .collect::<Vec<_>>(),
            FreshRight::Empty => Vec::new(),
            FreshRight::Short => (0..self.arity.saturating_sub(1))
                .map(|i| format!("w{}", i + 1))
                .collect::<Vec<_>>(),
            FreshRight::NotFresh => (0..self.arity)
                .map(|i| format!("v{}", i + 1))
                .collect::<Vec<_>>(),
        };
        let mut transitivity = vec!["  transitivity".to_string(), "    vars".to_string()];
        transitivity.push(format!(
            "      fresh_right{}{}{}",
            if fresh.is_empty() { "" } else { " " },
            fresh.join(" "),
            if dialect == Dialect::Version3 {
                ";"
            } else {
                ""
            }
        ));
        if self.with_spec {
            transitivity.push(format!("      fresh_aux_1 $b{semi}"));
            transitivity.push(format!("      fresh_aux_2 $c{semi}"));
        }
        transitivity.push(format!("    end{semi}"));
        transitivity.push("    proof".to_string());
        // One goal per definition constraint -- as the *definition stands when `proof` runs*,
        // which under `BlockLayout::TransitivityBeforeDef` is no constraints at all. Writing the
        // goals anyway would be rejected for naming goals that do not exist yet, so the
        // out-of-sequence layout writes the empty proof the defect's shape actually used.
        let goals = match layout {
            BlockLayout::Sequential => self.definition.len(),
            BlockLayout::TransitivityBeforeDef => 0,
        };
        for i in 0..goals {
            transitivity.push(format!("      proofgoal #{}", i + 1));
            transitivity.push(format!(
                "        rup >= 1{}",
                dialect.statement_terminator()
            ));
            transitivity.push(format!("      {}", dialect.proofgoal_end()));
        }
        transitivity.push(format!("    {}", dialect.proofgoal_end()));
        transitivity.push(format!("  end{semi}"));

        let mut lines = vec![format!("def_order {}", self.name)];
        lines.extend(vars);
        match layout {
            BlockLayout::Sequential => {
                lines.extend(spec);
                lines.extend(def);
                lines.extend(transitivity);
            }
            BlockLayout::TransitivityBeforeDef => {
                lines.extend(spec);
                lines.extend(transitivity);
                lines.extend(def);
            }
        }
        lines.push(format!("end{semi}"));
        lines
    }
}

/// Which proof dialect an order definition is written in.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Dialect {
    Version3,
    Version2,
}

impl Dialect {
    fn block_terminator(self) -> &'static str {
        match self {
            Dialect::Version3 => ";",
            Dialect::Version2 => "",
        }
    }

    fn statement_terminator(self) -> &'static str {
        match self {
            Dialect::Version3 => ";",
            Dialect::Version2 => " ;",
        }
    }

    /// How a `proofgoal` and the `proof` block around it are closed.
    fn proofgoal_end(self) -> &'static str {
        match self {
            Dialect::Version3 => "qed;",
            Dialect::Version2 => "end",
        }
    }

    /// The lines around an order definition that make a whole proof of it.
    fn wrap(self, order: Vec<String>) -> String {
        let mut lines = match self {
            Dialect::Version3 => vec![
                "pseudo-Boolean proof version 3.0".to_string(),
                "f 1;".to_string(),
            ],
            Dialect::Version2 => vec![
                "pseudo-Boolean proof version 2.0".to_string(),
                "f 1".to_string(),
            ],
        };
        lines.extend(order);
        let semi = self.block_terminator();
        lines.push(format!("output NONE{semi}"));
        lines.push(format!("conclusion NONE{semi}"));
        lines.push(format!("end pseudo-Boolean proof{semi}"));
        let mut out = lines.join("\n");
        out.push('\n');
        out
    }
}

/// The order the definition's blocks are written in.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum BlockLayout {
    /// `vars`, then `spec` if there is one, then `def`, then `transitivity`: the sequence the
    /// format fixes.
    Sequential,
    /// `transitivity` before `def`, which is wrong verdict 24's shape.
    TransitivityBeforeDef,
}

/// Definition constraint helper: `sum ci li >= d` over formal variables.
fn formal(terms: &[(i64, usize, bool)], degree: i64) -> Constraint {
    Constraint {
        terms: terms.to_vec(),
        degree,
    }
}

/// The order catalogue.
///
/// Hand-written rather than randomized, because a `def_order` block also has to *prove* its
/// transitivity, and only structured relations have a transitivity proof this test can write
/// (one `rup >= 1;` per definition constraint). The relations cover the three verdicts the
/// checker has to reach: a preorder, a reflexive non-transitive relation (the shape defect 20
/// exploited), and a non-reflexive relation.
fn order_catalogue() -> Vec<OrderSpec> {
    vec![
        // u1 -> v1, i.e. u1 <= v1. Reflexive and transitive.
        OrderSpec {
            name: "leq1",
            arity: 1,
            definition: vec![formal(&[(1, 0, true), (1, 1, false)], 1)],
            with_spec: false,
            spec_positive: true,
        },
        // The same order with an auxiliary variable and a specification, which is what makes
        // `scope leq` / `scope geq` legal.
        OrderSpec {
            name: "leq1s",
            arity: 1,
            definition: vec![formal(&[(1, 0, true), (1, 1, false)], 1)],
            with_spec: true,
            spec_positive: true,
        },
        // Componentwise <= on two bits. Reflexive and transitive.
        OrderSpec {
            name: "leq2",
            arity: 2,
            definition: vec![
                formal(&[(1, 0, true), (1, 2, false)], 1),
                formal(&[(1, 1, true), (1, 3, false)], 1),
            ],
            with_spec: false,
            spec_positive: true,
        },
        // Reflexive, NOT transitive: the only excluded pair is (11, 00), so 11 <= 01 <= 00 but
        // 11 </= 00.
        OrderSpec {
            name: "nt2",
            arity: 2,
            definition: vec![formal(
                &[(1, 0, true), (1, 2, false), (1, 1, true), (1, 3, false)],
                1,
            )],
            with_spec: false,
            spec_positive: true,
        },
        // The 3-cycle: reflexive, and orders x1 < x2 < x3 < x1.
        OrderSpec {
            name: "cyc3",
            arity: 3,
            definition: vec![
                formal(&[(1, 0, true), (1, 3, false), (1, 4, false)], 1),
                formal(&[(1, 1, true), (1, 4, false), (1, 5, false)], 1),
                formal(&[(1, 2, true), (1, 5, false), (1, 3, false)], 1),
            ],
            with_spec: false,
            spec_positive: true,
        },
        // Not reflexive: `u1 + v1 >= 1` fails at (0, 0).
        OrderSpec {
            name: "nr1",
            arity: 1,
            definition: vec![formal(&[(1, 0, false), (1, 1, false)], 1)],
            with_spec: false,
            spec_positive: true,
        },
    ]
}

/// An order that has been loaded onto problem literals.
#[derive(Clone, Debug)]
struct LoadedOrder {
    spec: OrderSpec,
    /// `(variable, negated)` per order position.
    lits: Vec<(usize, bool)>,
}

impl LoadedOrder {
    /// The tuple the loaded literals take under `assignment`.
    fn tuple(&self, assignment: u32) -> u32 {
        let mut out = 0u32;
        for (i, &(var, negated)) in self.lits.iter().enumerate() {
            if lit_holds(assignment, var, negated) {
                out |= 1 << i;
            }
        }
        out
    }

    fn render(&self) -> String {
        format!(
            "load_order {} {};",
            self.spec.name,
            self.lits
                .iter()
                .map(|&(var, negated)| format!(
                    "{}{}",
                    if negated { "~" } else { "" },
                    var_name(var)
                ))
                .collect::<Vec<_>>()
                .join(" ")
        )
    }
}

// -------------------------------------------------------------------------------------------
// The obligation inventory: what a subproof owes, transcribed from the format overview.
// -------------------------------------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Scope {
    Leq,
    Geq,
}

impl Scope {
    fn keyword(self) -> &'static str {
        match self {
            Scope::Leq => "leq",
            Scope::Geq => "geq",
        }
    }
}

/// One internal (`#`-numbered) obligation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct InternalGoal {
    /// `None` when the goal may be proven in any scope.
    scope: Option<Scope>,
}

/// What a subproof-opening rule owes.
#[derive(Clone, Debug, Default)]
struct Inventory {
    /// Indexed by goal number, so `internal[1]` is `#1`; slot 0 is the dummy the numbering
    /// starts past.
    internal: Vec<Option<InternalGoal>>,
    /// `Some(scope)` when the rule turns every database constraint into an obligation;
    /// `None` when its obligations are fixed and internal, in which case `proofgoal <id>` for a
    /// database id names nothing.
    database: Option<Scope>,
}

impl Inventory {
    fn new() -> Self {
        Inventory {
            internal: vec![None],
            database: None,
        }
    }

    fn push(&mut self, scope: Option<Scope>) {
        self.internal.push(Some(InternalGoal { scope }));
    }

    /// `red`: the constraint to be derived, then one goal per pre-order constraint, then the
    /// objective condition; and every database constraint is an obligation.
    fn redundance(order: Option<&LoadedOrder>, objective: bool) -> Self {
        let mut inv = Inventory::new();
        inv.push(Some(Scope::Leq));
        if let Some(order) = order {
            for _ in 0..order.spec.definition.len() {
                inv.push(Some(Scope::Leq));
            }
        }
        if objective {
            inv.push(Some(Scope::Leq));
        }
        inv.database = Some(Scope::Leq);
        inv
    }

    /// `dom`: one goal per pre-order constraint, then the negated pre-order goal, then the
    /// objective condition. No goal for the constraint itself.
    fn dominance(order: Option<&LoadedOrder>, objective: bool) -> Self {
        let mut inv = Inventory::new();
        if let Some(order) = order {
            for _ in 0..order.spec.definition.len() {
                inv.push(Some(Scope::Leq));
            }
            inv.push(Some(Scope::Geq));
        }
        if objective {
            inv.push(if order.is_some() {
                Some(Scope::Leq)
            } else {
                None
            });
        }
        inv.database = Some(Scope::Leq);
        inv
    }

    /// `pbc`: "Adding the constraint is successful if a contradiction can be derived from the
    /// current database and the negation of the constraint." One obligation, and it is the
    /// subproof itself — there is nothing a `proofgoal` line can name.
    fn proof_by_contradiction() -> Self {
        Inventory::new()
    }

    /// Checked deletion: "create the same proofgoals as redundance-based strengthening", for the
    /// constraint being deleted. Under strengthening-to-core the deletion instead has to show the
    /// constraint is implied, which is a proof by contradiction and owes nothing per constraint.
    fn checked_deletion(
        order: Option<&LoadedOrder>,
        objective: bool,
        strengthening_to_core: bool,
    ) -> Self {
        if strengthening_to_core {
            Inventory::new()
        } else {
            Inventory::redundance(order, objective)
        }
    }

    fn internal_len(&self) -> usize {
        self.internal.len()
    }
}

/// What the checker must answer for one `proofgoal <id>` line.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Admission {
    Admitted,
    InternalNotExisting,
    InternalAlreadyProven,
    DatabaseNotExisting,
    NotInScope,
}

/// The reference's verdict on `proofgoal <id>` inside `inventory`, with `scope` open.
fn admit(
    inventory: &Inventory,
    goal: GoalId,
    open_scope: Option<Scope>,
    live_database_ids: &[usize],
) -> Admission {
    match goal {
        GoalId::Internal(index) => match inventory.internal.get(index) {
            None => Admission::InternalNotExisting,
            Some(None) => Admission::InternalAlreadyProven,
            Some(Some(goal)) => match (goal.scope, open_scope) {
                (Some(required), Some(open)) if required != open => Admission::NotInScope,
                _ => Admission::Admitted,
            },
        },
        GoalId::Database(id) => match inventory.database {
            None => Admission::DatabaseNotExisting,
            Some(required) => {
                if !live_database_ids.contains(&id) {
                    Admission::DatabaseNotExisting
                } else if open_scope.is_some_and(|open| open != required) {
                    Admission::NotInScope
                } else {
                    Admission::Admitted
                }
            }
        },
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum GoalId {
    Internal(usize),
    Database(usize),
}

impl GoalId {
    fn render(self) -> String {
        match self {
            GoalId::Internal(index) => format!("#{index}"),
            GoalId::Database(id) => id.to_string(),
        }
    }
}

// -------------------------------------------------------------------------------------------
// Running the checker in process.
// -------------------------------------------------------------------------------------------

/// How one run ended. The four goal-lookup rejections the reference has an opinion about are
/// classified into [`Admission`]; every other rejection is kept as text so that a mismatch report
/// still names it.
#[derive(Clone, Debug, PartialEq, Eq)]
enum Outcome {
    Accepted,
    Rejected(Admission),
    OtherRejection(String),
    ParseError(String),
}

impl Outcome {
    fn admission(&self) -> Option<Admission> {
        match self {
            Outcome::Rejected(admission) => Some(*admission),
            _ => None,
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

    fn run(&self, formula: &str, proof: &str) -> Outcome {
        let formula_path = self.dir.path().join("formula.opb");
        let proof_path = self.dir.path().join("proof.pbp");
        write_file(&formula_path, formula);
        write_file(&proof_path, proof);

        let (formula, variables, labels, preserved) = match parse_opb_from_file(&formula_path) {
            Ok(parsed) => parsed,
            Err(err) => return Outcome::ParseError(format!("formula: {err}")),
        };
        let config = CheckerConfig {
            derivation_path: proof_path.clone(),
            formula_path: formula_path.clone(),
            // A checked deletion the checker cannot prove must be a rejection, not a silent
            // downgrade to unchecked deletion: this test is about obligations not being dropped,
            // and the fallback drops one on purpose.
            force_checked_deletion: true,
            print_verification_result: true,
            ..Default::default()
        };
        let context = Context::new(config, variables, preserved);
        let mut checker = match ForwardsChecker::new(context, formula) {
            Ok(checker) => checker,
            Err(err) => return Outcome::OtherRejection(format!("{err}")),
        };
        let file = std::fs::File::open(&proof_path).expect("failed to reopen the proof file");
        let size = file
            .metadata()
            .expect("failed to stat the proof file")
            .len();
        // Upstream made `Parser::new`/`parse` private behind `parse_proof`, which
        // also takes an `Option<u64>` size and a `MaybeCompressed` reader. These
        // proofs are written plain, so `Plain` drives the same code path.
        let mut reader = MaybeCompressed::Plain(std::io::BufReader::new(file));
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
                    ForwardsCheckerError::Parse(parse) if parse.is_version_error() => {
                        version2 = true;
                    }
                    other => return classify(Err(other)),
                }
            }
        }
        if version2 {
            let mut legacy = Version2Parser::new(&mut checker);
            if let Err(err) = legacy.parse(proof_path.clone(), reader) {
                return classify(Err(err));
            }
            if !checker.context.has_end_proof {
                return Outcome::OtherRejection("the proof has no `end` line".to_string());
            }
        }
        Outcome::Accepted
    }
}

fn write_file(path: &std::path::Path, contents: &str) {
    let mut file = std::fs::File::create(path).expect("failed to create a scratch file");
    file.write_all(contents.as_bytes())
        .expect("failed to write a scratch file");
    file.flush().expect("failed to flush a scratch file");
}

fn classify(result: Result<(), ForwardsCheckerError>) -> Outcome {
    let err = match result {
        Ok(()) => return Outcome::Accepted,
        Err(err) => err,
    };
    if let ForwardsCheckerError::Parse(parse) = &err {
        return Outcome::ParseError(format!("{parse}"));
    }
    let mut rendered = format!("{err}");
    let mut source: Option<&(dyn std::error::Error + 'static)> = std::error::Error::source(&err);
    while let Some(current) = source {
        rendered.push_str(&format!(" | {current}"));
        if let Some(checking) = current.downcast_ref::<CheckingError>() {
            let admission = match checking {
                CheckingError::InternalProofgoalNotExisting(_) => {
                    Some(Admission::InternalNotExisting)
                }
                CheckingError::InternalProofgoalAlreadyProven(_) => {
                    Some(Admission::InternalAlreadyProven)
                }
                CheckingError::DatabaseProofgoalNotExisting(_) => {
                    Some(Admission::DatabaseNotExisting)
                }
                CheckingError::ProofgoalNotInScope(_, _) => Some(Admission::NotInScope),
                _ => None,
            };
            if let Some(admission) = admission {
                return Outcome::Rejected(admission);
            }
        }
        source = std::error::Error::source(current);
    }
    Outcome::OtherRejection(rendered)
}

// -------------------------------------------------------------------------------------------
// Formula generation.
// -------------------------------------------------------------------------------------------

/// A formula plus the hidden assignment it was built around, so the reference always knows a
/// satisfiable formula is satisfiable without relying on its own enumeration to say so.
#[derive(Clone, Debug)]
struct Instance {
    constraints: Vec<Constraint>,
    objective: Option<Objective>,
    witness_assignment: u32,
}

impl Instance {
    fn render(&self) -> String {
        let mut out = format!(
            "* #variable= {NUM_VARS} #constraint= {}\n",
            self.constraints.len()
        );
        if let Some(objective) = &self.objective {
            out.push_str(&objective.render());
            out.push('\n');
        }
        for c in self.constraints.iter() {
            out.push_str(&format!("{} ;\n", c.render()));
        }
        out
    }
}

/// A random clause or cardinality constraint over the problem variables, satisfied by
/// `assignment`.
fn random_constraint_satisfied_by(rng: &mut Rng, assignment: u32) -> Constraint {
    loop {
        let arity = 1 + rng.below(3);
        let mut vars: Vec<usize> = (0..NUM_PROBLEM_VARS).collect();
        for i in 0..arity {
            let j = i + rng.below(NUM_PROBLEM_VARS - i);
            vars.swap(i, j);
        }
        let terms: Vec<Term> = vars[..arity]
            .iter()
            .map(|&var| (1, var, rng.chance(50)))
            .collect();
        let satisfied = terms
            .iter()
            .filter(|&&(_, var, negated)| lit_holds(assignment, var, negated))
            .count() as i64;
        if satisfied == 0 {
            continue;
        }
        let degree = 1 + rng.below(satisfied as usize) as i64;
        let candidate = Constraint { terms, degree };
        debug_assert!(candidate.holds(assignment));
        return candidate;
    }
}

fn random_instance(rng: &mut Rng, with_objective: bool) -> Instance {
    let witness_assignment = rng.next_u64() as u32 % (1 << NUM_PROBLEM_VARS);
    let count = 2 + rng.below(3);
    let constraints = (0..count)
        .map(|_| random_constraint_satisfied_by(rng, witness_assignment))
        .collect();
    let objective = with_objective.then(|| {
        let arity = 1 + rng.below(2);
        Objective {
            terms: (0..arity)
                .map(|i| (1 + rng.below(2) as i64, i, rng.chance(30)))
                .collect(),
        }
    });
    Instance {
        constraints,
        objective,
        witness_assignment,
    }
}

fn random_witness(rng: &mut Rng, allow_aux: bool) -> Witness {
    let count = 1 + rng.below(2);
    let mut used = Vec::new();
    let mut entries = Vec::new();
    for _ in 0..count {
        let var = if allow_aux && rng.chance(15) {
            AUX_VAR
        } else {
            rng.below(NUM_PROBLEM_VARS)
        };
        if used.contains(&var) {
            continue;
        }
        used.push(var);
        let value = match rng.below(4) {
            0 => WitnessValue::Zero,
            1 => WitnessValue::One,
            _ => {
                let source = rng.below(NUM_PROBLEM_VARS);
                if source == var {
                    WitnessValue::One
                } else {
                    WitnessValue::Lit(source, rng.chance(40))
                }
            }
        };
        entries.push((var, value));
    }
    if entries.is_empty() {
        entries.push((0, WitnessValue::One));
    }
    Witness(entries)
}

/// A random constraint over the problem variables, with no guarantee that it is licensed.
fn random_target_constraint(rng: &mut Rng) -> Constraint {
    let arity = 1 + rng.below(2);
    let mut vars: Vec<usize> = (0..NUM_PROBLEM_VARS).collect();
    for i in 0..arity {
        let j = i + rng.below(NUM_PROBLEM_VARS - i);
        vars.swap(i, j);
    }
    let terms: Vec<Term> = vars[..arity]
        .iter()
        .map(|&var| (1, var, rng.chance(50)))
        .collect();
    Constraint { terms, degree: 1 }
}

// -------------------------------------------------------------------------------------------
// Reference licensing conditions, straight from the rule definitions.
// -------------------------------------------------------------------------------------------

/// `F /\ ~C |= (F /\ C)|w`, together with the order and objective side conditions
/// ("If the redundance rule is used in the context of optimization and / or dominance breaking,
/// additional conditions are checked").
///
/// `premises` is what the goals may be proven from and `targets` is what has to hold after the
/// substitution: they differ under strengthening-to-core, where the obligations are only
/// generated for the core set.
fn redundance_licensed(
    premises: &[Constraint],
    targets: &[Constraint],
    constraint: &Constraint,
    witness: &Witness,
    order: Option<&LoadedOrder>,
    objective: Option<&Objective>,
) -> bool {
    for a in 0..NUM_ASSIGNMENTS {
        if !satisfies_all(premises, a) || constraint.holds(a) {
            continue;
        }
        let b = witness.apply(a);
        if !satisfies_all(targets, b) {
            return false;
        }
        // Goal `#1`, "the constraint to be derived": the witnessed assignment satisfies it.
        if !constraint.holds(b) {
            return false;
        }
        if let Some(order) = order {
            if !order.spec.leq(order.tuple(b), order.tuple(a)) {
                return false;
            }
        }
        if let Some(objective) = objective {
            if objective.value(b) > objective.value(a) {
                return false;
            }
        }
    }
    true
}

/// Goal `#1` of a `red`, on its own: "the constraint to be derived".
///
/// [`redundance_licensed`] decides the whole side condition; this decides the single obligation
/// the generator's hinted `proofgoal #1` claims to discharge, so that the coverage counter for
/// the hinted-discharge state can say whether that obligation was one the reference refuses.
fn redundance_goal_one_holds(
    premises: &[Constraint],
    constraint: &Constraint,
    w: &Witness,
) -> bool {
    (0..NUM_ASSIGNMENTS)
        .all(|a| !satisfies_all(premises, a) || constraint.holds(a) || constraint.holds(w.apply(a)))
}

/// Whether the format forbids a substitution on a checked deletion here.
///
/// This reference was briefly written as `order_loaded || strengthening_to_core`, because
/// `proof_format_overview.md` said so — and the checker guards on strengthening-to-core alone,
/// so the two disagreed. That disagreement was chased to the mechanism, and the *document* was
/// what was wrong; it has since been corrected, and this now states the corrected condition.
///
/// Under strengthening-to-core the condition is real: a checked deletion generates no
/// substituted proofgoals at all there (it is a proof by contradiction that the deleted
/// constraint follows from the rest of the core), so a witness would go entirely unchecked.
///
/// Under a loaded order it is not. `rules/deletion.rs` calls
/// `active_order.get_proofgoals(&witness)` — the same call `red_strengthening.rs` makes — so the
/// deletion owes one goal per order-definition constraint, instantiated with the witnessed
/// values on the left: the witness may not worsen the order. Making the reference forbid it
/// would have made this test refuse sound proofs and call the checker wrong for accepting them,
/// which is a differential sharing a documentation error rather than catching one.
/// `tests/instances/{correct,incorrect}/version{2,3}/checked_deletion_witness_*` pin both
/// directions: an order-preserving witness verifies, an order-worsening one is refused.
fn delc_substitution_must_be_empty(order_loaded: bool, strengthening_to_core: bool) -> bool {
    let _ = order_loaded;
    strengthening_to_core
}

/// The dominance condition.
///
/// # Provenance
///
/// This is the one rule in the reference that is **not** transcribed from the repository, and it
/// is therefore the weakest of the five legs. `proof_format_overview.md` gives `dom` its syntax,
/// an example and a citation to [BGMN23] -- a paper that is not in this repository -- and
/// the development design notes gives only the BNF. What the repository does fix:
///
/// * the goal list -- "one goal per constraint in the current pre-order, one goal for the negated
///   pre-order (only dominance), objective condition";
/// * the orientation of those goals, from "Scopes Inside Subproofs": `scope leq` introduces
///   `S_<=(z|w, z, a)`, "the specification instantiated with the *witnessed* variables on the
///   left", and `scope geq` introduces `S_<=(z, z|w, a)`, "instantiated with the *original*
///   variables on the left" and "used exclusively to prove the negated-order proof goal".
///   Together those say the pre-order goals assert `z|w <= z` and the negated-order goal asserts
///   `not (z <= z|w)` -- which is the strict improvement below.
///
/// What the repository does **not** fix, and what was therefore read off
/// `veripb-checker/src/rules/dom_strengthening.rs`, the code this test is supposed to audit
/// independently:
///
/// * that the substituted obligations cover the *core* set while the premises are the whole
///   database (`targets` versus `premises` below);
/// * that the objective condition is non-strict when an order is loaded and strict when it is
///   not (`get_proofgoal` versus `get_proofgoal_strict` there).
///
/// A differential against the code under test is not a differential, so those two clauses cannot
/// catch a defect in the code they came from. They are marked [`DomClause::CodeDerived`] and
/// counted, so a reader can see how much of the `dom` leg rests on them. The rest of the leg does
/// not depend on this function at all: an accepted `dom` still has to leave a satisfiable
/// database, and that assertion is decided by enumeration alone.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum DomClause {
    /// Derivable from `proof_format_overview.md` / the development design notes.
    DocDerived,
    /// Transcribed from `veripb-checker/src/rules/dom_strengthening.rs`.
    CodeDerived,
}
/// `None` when the dominance condition holds; otherwise the provenance of the clause that
/// refused. The doc-derived clauses are checked first, so a [`DomClause::CodeDerived`] answer
/// means the refusal rests *only* on a clause transcribed from the code under test.
fn dominance_licensed(
    premises: &[Constraint],
    targets: &[Constraint],
    constraint: &Constraint,
    witness: &Witness,
    order: Option<&LoadedOrder>,
    objective: Option<&Objective>,
) -> Option<DomClause> {
    let counterexamples = || {
        (0..NUM_ASSIGNMENTS)
            .filter(|&a| satisfies_all(premises, a) && !constraint.holds(a))
            .map(|a| (a, witness.apply(a)))
    };
    for (a, b) in counterexamples() {
        // The substituted obligations. That there are obligations per database constraint is the
        // format's ("if a goal originates from a constraint in the database ..."); that `targets`
        // is the *core* set rather than the whole database is the code's reading, and it is the
        // weaker of the two, so it can only make the reference accept more.
        if !satisfies_all(targets, b) {
            return Some(DomClause::DocDerived);
        }
        // `scope leq` introduces the specification with the witnessed variables on the left, so
        // the pre-order goals say `z|w <= z`; `scope geq` puts the original variables on the left
        // and exists only for the negated-order goal, so that one says `not (z <= z|w)`.
        if let Some(order) = order {
            let (before, after) = (order.tuple(a), order.tuple(b));
            if !order.spec.leq(after, before) || order.spec.leq(before, after) {
                return Some(DomClause::DocDerived);
            }
        }
    }
    // The objective condition. The format lists the goal but not its shape; that it is non-strict
    // under a loaded order and strict without one comes from `dom_strengthening.rs`
    // (`get_proofgoal` versus `get_proofgoal_strict`).
    for (a, b) in counterexamples() {
        match (order, objective) {
            (Some(_), Some(objective)) => {
                if objective.value(b) > objective.value(a) {
                    return Some(DomClause::CodeDerived);
                }
            }
            (None, Some(objective)) => {
                if objective.value(b) >= objective.value(a) {
                    return Some(DomClause::CodeDerived);
                }
            }
            (Some(_), None) => (),
            (None, None) => panic!("dominance needs an objective or an order"),
        }
    }
    None
}

// -------------------------------------------------------------------------------------------
// Test 1: the obligation inventory.
// -------------------------------------------------------------------------------------------

/// Which rule opens the subproof the probe writes its `proofgoal` line into.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Opener {
    Pbc,
    Red,
    Dom,
    Delc,
}

struct Probe {
    seed: u64,
    instance: Instance,
    order: Option<LoadedOrder>,
    fresh_right: FreshRight,
    strengthening_to_core: bool,
    opener: Opener,
    target: Constraint,
    witness: Witness,
    delete_id: usize,
    scope: Option<Scope>,
    goal: GoalId,
    hint: bool,
}

impl Probe {
    fn inventory(&self) -> Inventory {
        let order = self.order.as_ref();
        let objective = self.instance.objective.is_some();
        match self.opener {
            Opener::Pbc => Inventory::proof_by_contradiction(),
            Opener::Red => Inventory::redundance(order, objective),
            Opener::Dom => Inventory::dominance(order, objective),
            Opener::Delc => {
                Inventory::checked_deletion(order, objective, self.strengthening_to_core)
            }
        }
    }

    fn live_database_ids(&self) -> Vec<usize> {
        (1..=self.instance.constraints.len())
            .filter(|id| self.opener != Opener::Delc || *id != self.delete_id)
            .collect()
    }

    /// The lines before the subproof body: header, formula, mode switches, order.
    fn prefix(&self) -> Vec<String> {
        let mut lines = vec![
            "pseudo-Boolean proof version 3.0".to_string(),
            format!("f {};", self.instance.constraints.len()),
        ];
        if self.strengthening_to_core {
            lines.push("strengthening_to_core on;".to_string());
        }
        if let Some(order) = &self.order {
            lines.extend(order.spec.render(self.fresh_right));
            lines.push(order.render());
        }
        lines
    }

    fn opening_line(&self) -> String {
        match self.opener {
            Opener::Pbc => format!("pbc {} : subproof", self.target.render()),
            Opener::Red => format!(
                "red {} : {} : subproof",
                self.target.render(),
                self.witness.render()
            ),
            Opener::Dom => format!(
                "dom {} : {} : subproof",
                self.target.render(),
                self.witness.render()
            ),
            Opener::Delc => {
                if delc_substitution_must_be_empty(self.order.is_some(), self.strengthening_to_core)
                {
                    format!("delc {} : : subproof", self.delete_id)
                } else {
                    format!(
                        "delc {} : {} : subproof",
                        self.delete_id,
                        self.witness.render()
                    )
                }
            }
        }
    }

    /// The script, with the probe's `proofgoal` block repeated `goals` times.
    ///
    /// `0` is the companion: it establishes that everything *around* the probe is accepted, so
    /// that whatever the one-goal run reports is attributable to the `proofgoal` line and
    /// nothing else. `2` asks the second half of the bookkeeping question -- whether naming the
    /// same obligation twice is caught.
    fn render(&self, goals: usize) -> String {
        let mut lines = self.prefix();
        lines.push(self.opening_line());
        let mut body = Vec::new();
        for _ in 0..goals {
            body.push(format!("    proofgoal {}", self.goal.render()));
            body.push("      rup >= 1;".to_string());
            body.push(if self.hint {
                "    qed : -1;".to_string()
            } else {
                "    qed;".to_string()
            });
        }
        match self.scope {
            Some(scope) => {
                lines.push(format!("  scope {}", scope.keyword()));
                lines.extend(body);
                lines.push("  end scope;".to_string());
            }
            None => lines.extend(body),
        }
        lines.push("qed;".to_string());
        lines.push("output NONE;".to_string());
        lines.push("conclusion NONE;".to_string());
        lines.push("end pseudo-Boolean proof;".to_string());
        let mut out = lines.join("\n");
        out.push('\n');
        out
    }
}

fn generate_probe(seed: u64) -> Probe {
    let mut rng = Rng::new(seed);
    let with_objective = rng.chance(30);
    let instance = random_instance(&mut rng, with_objective);
    let catalogue = order_catalogue();
    // Only preorders are used here: a probe is about goal *names*, and a rejected `def_order`
    // would make the companion run fail and throw the case away.
    let preorders: Vec<&OrderSpec> = catalogue
        .iter()
        .filter(|spec| spec.is_preorder())
        .collect::<Vec<_>>();
    let order = if rng.chance(55) {
        let spec = (*rng.pick(&preorders)).clone();
        let mut vars: Vec<usize> = (0..NUM_PROBLEM_VARS).collect();
        for i in 0..spec.arity {
            let j = i + rng.below(NUM_PROBLEM_VARS - i);
            vars.swap(i, j);
        }
        let lits = vars[..spec.arity]
            .iter()
            .map(|&var| (var, rng.chance(20)))
            .collect();
        Some(LoadedOrder { spec, lits })
    } else {
        None
    };
    let strengthening_to_core = rng.chance(35);
    let opener = match rng.below(4) {
        0 => Opener::Pbc,
        1 => Opener::Red,
        2 if order.is_some() || instance.objective.is_some() => Opener::Dom,
        2 => Opener::Red,
        _ => Opener::Delc,
    };
    let delete_id = 1 + rng.below(instance.constraints.len());
    // The opener has to be one the checker accepts on its own, or the companion run throws the
    // case away, and a probe that is thrown away compares nothing. So the target constraint and
    // the witness are drawn until the reference licenses the rule -- for `pbc` that just means a
    // constraint the database already entails, and the cheapest such constraint is one of the
    // formula's own. Aiming is the generator's business: what the probe then asserts is about
    // goal *names*, and reads the inventory, not this.
    let reference_db = RefDatabase {
        entries: instance
            .constraints
            .iter()
            .map(|c| (c.clone(), true))
            .collect(),
    };
    let mut target = random_target_constraint(&mut rng);
    let mut witness = random_witness(&mut rng, order.as_ref().is_none_or(|o| o.spec.with_spec));
    for _ in 0..24 {
        target = match opener {
            Opener::Pbc => instance.constraints[rng.below(instance.constraints.len())].clone(),
            _ => random_target_constraint(&mut rng),
        };
        witness = if opener == Opener::Delc
            && delc_substitution_must_be_empty(order.is_some(), strengthening_to_core)
        {
            Witness::default()
        } else {
            random_witness(&mut rng, order.as_ref().is_none_or(|o| o.spec.with_spec))
        };
        let step = match opener {
            Opener::Pbc => Step::Pbc(target.clone()),
            Opener::Red => Step::Red(target.clone(), witness.clone(), SubproofStyle::Autoproved),
            Opener::Dom => Step::Dom(target.clone(), witness.clone(), SubproofStyle::Autoproved),
            Opener::Delc => Step::Delc(delete_id, witness.clone()),
        };
        if license_step(
            &reference_db,
            strengthening_to_core,
            order.as_ref(),
            instance.objective.as_ref(),
            &instance,
            &step,
        )
        .is_none()
        {
            break;
        }
    }
    let scope = match rng.below(6) {
        0 => Some(Scope::Leq),
        1 => Some(Scope::Geq),
        _ => None,
    };
    let inventory = match opener {
        Opener::Pbc => Inventory::proof_by_contradiction(),
        Opener::Red => Inventory::redundance(order.as_ref(), instance.objective.is_some()),
        Opener::Dom => Inventory::dominance(order.as_ref(), instance.objective.is_some()),
        Opener::Delc => Inventory::checked_deletion(
            order.as_ref(),
            instance.objective.is_some(),
            strengthening_to_core,
        ),
    };
    // Two ids are deliberately never generated, because neither asks an obligation question.
    // `#0` is not a proofgoal id at all -- the grammar spells one `"#", positive_integer`, so
    // the parser rejects it before the inventory is consulted. An id outside the database's
    // index range is a database-indexing question, answered by an out-of-bounds error rather
    // than by the goal lookup. What is left is the question this test is about: does *this*
    // subproof owe an obligation for a constraint that is really there.
    let live: Vec<usize> = (1..=instance.constraints.len())
        .filter(|id| opener != Opener::Delc || *id != delete_id)
        .collect();
    let goal = if live.is_empty() || rng.chance(50) {
        GoalId::Internal(1 + rng.below(inventory.internal_len() + 1))
    } else {
        GoalId::Database(*rng.pick(&live))
    };
    Probe {
        seed,
        instance,
        order,
        fresh_right: FreshRight::Correct,
        strengthening_to_core,
        opener,
        target,
        witness,
        delete_id,
        scope,
        goal,
        hint: rng.chance(50),
    }
}

#[derive(Default, Debug)]
struct ProbeCounters {
    probes: usize,
    companion_rejected: usize,
    decided: usize,
    repeat_probed: usize,
    expected_admitted: usize,
    expected_internal_not_existing: usize,
    expected_internal_already_proven: usize,
    expected_database_not_existing: usize,
    expected_not_in_scope: usize,
    opener_pbc: usize,
    opener_red: usize,
    opener_dom: usize,
    opener_delc: usize,
    with_order: usize,
    with_objective: usize,
    with_scope: usize,
    strengthening_to_core: usize,
}

#[test]
fn proofgoal_admission_matches_the_reference_inventory() {
    let cases = case_count();
    let harness = Harness::new();
    let mut counters = ProbeCounters::default();
    let mut failures: Vec<String> = Vec::new();

    for seed in 0..cases as u64 {
        let probe = generate_probe(seed);
        counters.probes += 1;
        match probe.opener {
            Opener::Pbc => counters.opener_pbc += 1,
            Opener::Red => counters.opener_red += 1,
            Opener::Dom => counters.opener_dom += 1,
            Opener::Delc => counters.opener_delc += 1,
        }
        if probe.order.is_some() {
            counters.with_order += 1;
        }
        if probe.instance.objective.is_some() {
            counters.with_objective += 1;
        }
        if probe.scope.is_some() {
            counters.with_scope += 1;
        }
        if probe.strengthening_to_core {
            counters.strengthening_to_core += 1;
        }

        let formula = probe.instance.render();
        // The companion run says whether everything except the `proofgoal` line is accepted.
        let companion = harness.run(&formula, &probe.render(0));
        if companion != Outcome::Accepted {
            counters.companion_rejected += 1;
            continue;
        }
        counters.decided += 1;

        let expected = admit(
            &probe.inventory(),
            probe.goal,
            probe.scope,
            &probe.live_database_ids(),
        );
        match expected {
            Admission::Admitted => counters.expected_admitted += 1,
            Admission::InternalNotExisting => counters.expected_internal_not_existing += 1,
            Admission::InternalAlreadyProven => counters.expected_internal_already_proven += 1,
            Admission::DatabaseNotExisting => counters.expected_database_not_existing += 1,
            Admission::NotInScope => counters.expected_not_in_scope += 1,
        }

        let observed = harness.run(&formula, &probe.render(1));
        let agrees = match expected {
            Admission::Admitted => observed.admission().is_none(),
            other => observed.admission() == Some(other),
        };
        if !agrees {
            failures.push(format!(
                "obligation inventory mismatch in probe seed {}\n  reference says: {:?}\n  \
                 checker says:   {:?}\n  proof:\n{}",
                probe.seed,
                expected,
                observed,
                indent(&probe.render(1))
            ));
            if failures.len() >= 3 {
                break;
            }
            continue;
        }

        // The other half of "no obligation is discharged twice": naming the same goal again.
        // Only asked when the first discharge went through, so that the second `proofgoal` line
        // is definitely reached.
        if expected == Admission::Admitted && observed == Outcome::Accepted {
            counters.repeat_probed += 1;
            let expected_again = match probe.goal {
                // An internal goal is consumed when it is proven.
                GoalId::Internal(_) => Admission::InternalAlreadyProven,
                // A database goal is not: the rule's obligation for a database constraint stands
                // for the whole subproof, and the goal is rebuilt from it on demand, because
                // goal *generation* may have auto-discharged it and the proof is still allowed
                // to discharge it explicitly. Proving it twice is therefore not an error.
                GoalId::Database(_) => Admission::Admitted,
            };
            if expected_again == Admission::InternalAlreadyProven {
                counters.expected_internal_already_proven += 1;
            }
            let again = harness.run(&formula, &probe.render(2));
            let agrees_again = match expected_again {
                Admission::Admitted => again.admission().is_none(),
                other => again.admission() == Some(other),
            };
            if !agrees_again {
                failures.push(format!(
                    "repeated-obligation mismatch in probe seed {}\n  reference says: {:?}\n  \
                     checker says:   {:?}\n  proof:\n{}",
                    probe.seed,
                    expected_again,
                    again,
                    indent(&probe.render(2))
                ));
                if failures.len() >= 3 {
                    break;
                }
            }
        }
    }

    profile("inventory probes", &counters);
    assert!(
        failures.is_empty(),
        "{} of {} obligation-inventory probes disagreed with the reference:\n\n{}",
        failures.len(),
        cases,
        failures.join("\n")
    );

    if cases >= DEFAULT_CASES {
        let floor = |what: &str, got: usize, want: usize| {
            assert!(
                got >= want,
                "the probe generator has stopped exercising {what}: {got} in {cases} probes, \
                 expected at least {want}. Full profile: {counters:?}"
            );
        };
        floor(
            "probes decided by a companion-accepted run",
            counters.decided,
            60,
        );
        floor(
            "goal ids the inventory admits",
            counters.expected_admitted,
            20,
        );
        floor(
            "database ids the inventory does not name",
            counters.expected_database_not_existing,
            15,
        );
        floor(
            "internal ids past the end of the inventory",
            counters.expected_internal_not_existing,
            10,
        );
        floor("`pbc` subproofs", counters.opener_pbc, 40);
        floor("`red` subproofs", counters.opener_red, 40);
        floor("checked-deletion subproofs", counters.opener_delc, 40);
        floor("subproofs with an order loaded", counters.with_order, 80);
        floor(
            "subproofs under strengthening-to-core",
            counters.strengthening_to_core,
            50,
        );
        floor("probes written inside a scope", counters.with_scope, 50);
        floor(
            "goal ids the open scope excludes",
            counters.expected_not_in_scope,
            8,
        );
        floor(
            "obligations named a second time after being discharged",
            counters.repeat_probed,
            40,
        );
        floor(
            "internal obligations named a second time",
            counters.expected_internal_already_proven,
            10,
        );
    }
}

// -------------------------------------------------------------------------------------------
// Test 2: an accepted run's rules are all licensed.
// -------------------------------------------------------------------------------------------

/// How a strengthening step's subproof is written.
///
/// The hinted spellings exist for the `qed : <hint>` shortcut, which both `qed` forms accept: a
/// `proofgoal` may be closed by naming a constraint that discharges it, and so may the subproof
/// as a whole. The only constraint that discharges either is a contradiction -- "Each proofgoal
/// must derive contradiction using the provided constraints", and a subproof is autoproven only
/// when "unit propagation derives contradiction with respect to the database and the additional
/// premises". A checker that takes the hint's word for it, without looking at what the hinted
/// constraint says, discharges every obligation written this way; the reference's opinion of the
/// enclosing rule is unchanged, so the step becomes an accepted rule the reference refuses.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum SubproofStyle {
    /// No `: subproof` at all: every obligation is autoproven.
    NoSubproof,
    /// `: subproof` whose body proves nothing, so every obligation is still autoproven.
    Autoproved,
    /// `: subproof` closing `proofgoal #1` with `qed : <hint>`.
    HintedGoal(Hint),
    /// `: subproof` closing the subproof itself with `qed : <hint>`, which skips every obligation
    /// the subproof still owes.
    HintedSubproof(Hint),
}

/// What the constraint a `qed : <hint>` names actually says.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Hint {
    Contradiction,
    /// Nothing in the format licenses a discharge by this.
    NonContradiction,
}

impl Hint {
    /// The line whose result the hint then names as `-1`. Both spellings are derivations the
    /// checker cannot refuse on their own: `>= 1` is the empty constraint, whose negation reverse
    /// unit propagation refutes vacuously, and `+1 x1 >= 0` has a negation that is contradictory
    /// before propagation even starts. They differ in exactly one respect -- whether the
    /// constraint that lands in the database is itself a contradiction.
    fn derivation(self) -> &'static str {
        match self {
            Hint::Contradiction => "rup >= 1;",
            Hint::NonContradiction => "rup +1 x1 >= 0;",
        }
    }
}

impl SubproofStyle {
    fn has_subproof(self) -> bool {
        self != SubproofStyle::NoSubproof
    }

    fn hint(self) -> Option<Hint> {
        match self {
            SubproofStyle::NoSubproof | SubproofStyle::Autoproved => None,
            SubproofStyle::HintedGoal(hint) | SubproofStyle::HintedSubproof(hint) => Some(hint),
        }
    }

    fn is_bogus(self) -> bool {
        self.hint() == Some(Hint::NonContradiction)
    }
}

/// One top-level step of a soundness script.
#[derive(Clone, Debug)]
enum Step {
    StrengtheningToCore,
    Rup(Constraint),
    Pbc(Constraint),
    Red(Constraint, Witness, SubproofStyle),
    Dom(Constraint, Witness, SubproofStyle),
    Delc(usize, Witness),
}

impl Step {
    fn subproof_style(&self) -> Option<SubproofStyle> {
        match self {
            Step::Red(_, _, style) | Step::Dom(_, _, style) => Some(*style),
            _ => None,
        }
    }
}

struct Script {
    seed: u64,
    instance: Instance,
    order: Option<LoadedOrder>,
    fresh_right: FreshRight,
    strengthening_to_core_first: bool,
    steps: Vec<Step>,
    /// Aligned with `steps`: what the reference concluded about each step. Recorded during
    /// generation, where the database state at that point is still available, so that every
    /// coverage counter below is read off the reference and never off the checker.
    step_facts: Vec<StepFacts>,
}

/// The reference's opinion of one step, kept for the coverage counters.
#[derive(Clone, Debug, Default)]
struct StepFacts {
    refusal: Option<RefusalKind>,
    /// `red` only: goal `#1`, "the constraint to be derived", is one the reference refuses.
    goal_one_fails: bool,
}

impl Script {
    fn render(&self) -> String {
        let mut lines = vec![
            "pseudo-Boolean proof version 3.0".to_string(),
            format!("f {};", self.instance.constraints.len()),
        ];
        if self.strengthening_to_core_first {
            lines.push("strengthening_to_core on;".to_string());
        }
        if let Some(order) = &self.order {
            lines.extend(order.spec.render(self.fresh_right));
            lines.push(order.render());
        }
        for step in self.steps.iter() {
            match step {
                Step::StrengtheningToCore => lines.push("strengthening_to_core on;".to_string()),
                Step::Rup(c) => lines.push(format!("rup {};", c.render())),
                Step::Pbc(c) => lines.push(format!("pbc {};", c.render())),
                Step::Red(c, w, style) => {
                    lines.extend(self.render_strengthening("red", c, w, *style))
                }
                Step::Dom(c, w, style) => {
                    lines.extend(self.render_strengthening("dom", c, w, *style))
                }
                Step::Delc(id, w) => {
                    lines.push(format!("delc {} : {} ;", id, w.render()));
                }
            }
        }
        lines.push("output NONE;".to_string());
        lines.push("conclusion NONE;".to_string());
        lines.push("end pseudo-Boolean proof;".to_string());
        let mut out = lines.join("\n");
        out.push('\n');
        out
    }

    /// One `red` or `dom` step, in the spelling [`SubproofStyle`] asks for.
    ///
    /// `#1` is the one goal id every strengthening rule this generator writes really owns: for
    /// `red` it is "the constraint to be derived", for `dom` it is the first pre-order goal (or,
    /// with no order, the objective goal). Whatever the subproof does not prove explicitly is
    /// autoproven at `qed`, so writing a single `proofgoal #1` is enough to reach the hinted
    /// discharge without the generator having to know the whole inventory.
    fn render_strengthening(
        &self,
        keyword: &str,
        c: &Constraint,
        w: &Witness,
        style: SubproofStyle,
    ) -> Vec<String> {
        if !style.has_subproof() {
            return vec![format!("{keyword} {} : {};", c.render(), w.render())];
        }
        let mut lines = vec![format!(
            "{keyword} {} : {} : subproof",
            c.render(),
            w.render()
        )];
        if let SubproofStyle::HintedGoal(hint) = style {
            lines.push("  proofgoal #1".to_string());
            lines.push(format!("    {}", hint.derivation()));
            lines.push("  qed : -1;".to_string());
        }
        if self
            .order
            .as_ref()
            .is_some_and(|order| order.spec.with_spec)
        {
            lines.push("  scope leq".to_string());
            lines.push("  end scope;".to_string());
            if keyword == "dom" {
                lines.push("  scope geq".to_string());
                lines.push("  end scope;".to_string());
            }
        }
        // The hint is written last so that `-1` names it and nothing a scope introduced.
        if let SubproofStyle::HintedSubproof(hint) = style {
            lines.push(format!("  {}", hint.derivation()));
            lines.push("qed : -1;".to_string());
        } else {
            lines.push("qed;".to_string());
        }
        lines
    }
}

/// The reference's running picture of the database: which constraints are live, and which of
/// them are in the core set.
#[derive(Clone, Debug)]
struct RefDatabase {
    entries: Vec<(Constraint, bool)>,
}

impl RefDatabase {
    fn all(&self) -> Vec<Constraint> {
        self.entries.iter().map(|entry| entry.0.clone()).collect()
    }

    fn core(&self) -> Vec<Constraint> {
        self.entries
            .iter()
            .filter(|entry| entry.1)
            .map(|entry| entry.0.clone())
            .collect()
    }

    fn move_all_to_core(&mut self) {
        for entry in self.entries.iter_mut() {
            entry.1 = true;
        }
    }
}

/// Generate a script and replay it through the reference in one pass, so the generator can aim
/// a step at a licensed or an unlicensed instance and the reference's verdict is recorded as it
/// goes.
///
/// Aiming is the generator's business only: every assertion downstream reads the verdict this
/// function computes from the rule definitions, never the fact that a step was *meant* to be
/// licensed. Without aiming the checker accepts about one script in ten, which would leave the
/// "accepted run" assertions nearly vacuous.
fn generate_script(seed: u64) -> (Script, Vec<Refusal>, RefDatabase) {
    let mut rng = Rng::new(seed.wrapping_mul(0x9E3779B97F4A7C15));
    let with_objective = rng.chance(35);
    let instance = random_instance(&mut rng, with_objective);
    let catalogue = order_catalogue();
    let order = if rng.chance(50) {
        let spec = rng.pick(&catalogue).clone();
        let mut vars: Vec<usize> = (0..NUM_PROBLEM_VARS).collect();
        for i in 0..spec.arity {
            let j = i + rng.below(NUM_PROBLEM_VARS - i);
            vars.swap(i, j);
        }
        let lits = vars[..spec.arity]
            .iter()
            .map(|&var| (var, rng.chance(20)))
            .collect();
        Some(LoadedOrder { spec, lits })
    } else {
        None
    };
    let fresh_right = *rng.pick(&[
        FreshRight::Correct,
        FreshRight::Correct,
        FreshRight::Correct,
        FreshRight::Empty,
        FreshRight::Short,
        FreshRight::NotFresh,
    ]);
    // Strengthening-to-core is drawn independently of the order, so the reference's core set and
    // its full database genuinely come apart: `red` puts a merely satisfiability-preserving
    // constraint into the *derived* set when it is off, and `dom` generates obligations for core
    // constraints only. `license_step` models that difference rather than legislating it away.
    let strengthening_to_core_first = rng.chance(35);

    let mut db = RefDatabase {
        entries: instance
            .constraints
            .iter()
            .map(|c| (c.clone(), true))
            .collect(),
    };
    let mut strengthening_to_core = strengthening_to_core_first;
    if strengthening_to_core || order.is_some() {
        // `strengthening_to_core on` and `load_order` both move every constraint into core.
        db.move_all_to_core();
    }
    let order_ref = order.as_ref();
    let objective = instance.objective.as_ref();

    let mut steps: Vec<Step> = Vec::new();
    let mut step_facts: Vec<StepFacts> = Vec::new();
    let mut refusals: Vec<Refusal> = Vec::new();
    let step_count = 1 + rng.below(3);
    for index in 0..step_count {
        if !strengthening_to_core && rng.chance(8) {
            steps.push(Step::StrengtheningToCore);
            step_facts.push(StepFacts::default());
            strengthening_to_core = true;
            db.move_all_to_core();
            continue;
        }
        let aim_licensed = rng.chance(70);
        let mut chosen: Option<(Step, Option<Refusal>)> = None;
        for attempt in 0..14 {
            let candidate = random_step(
                &mut rng,
                &instance,
                order_ref.is_some(),
                strengthening_to_core,
            );
            let verdict = license_step(
                &db,
                strengthening_to_core,
                order_ref,
                objective,
                &instance,
                &candidate,
            );
            // Aiming asks what the *checker* is likely to do, so a step the reference refuses
            // only because the format forbids its substitution counts as licensed here: the
            // checker accepts those, and a script that stops early on one shows nothing.
            let licensed = verdict
                .as_ref()
                .is_none_or(|refusal| refusal.kind == RefusalKind::DelcSubstitutionForbidden);
            if licensed == aim_licensed || attempt == 13 {
                chosen = Some((candidate, verdict));
                break;
            }
        }
        let (step, verdict) = chosen.expect("the retry loop always keeps its last candidate");
        step_facts.push(StepFacts {
            refusal: verdict.as_ref().map(|refusal| refusal.kind.clone()),
            goal_one_fails: match &step {
                Step::Red(c, w, _) => !redundance_goal_one_holds(&db.all(), c, w),
                _ => false,
            },
        });
        if let Some(mut verdict) = verdict {
            verdict.reason = format!("step {index}: {}", verdict.reason);
            refusals.push(verdict);
        }
        apply_step(&mut db, strengthening_to_core, &instance, &step);
        steps.push(step);
    }

    (
        Script {
            seed,
            instance,
            order,
            fresh_right,
            strengthening_to_core_first,
            steps,
            step_facts,
        },
        refusals,
        db,
    )
}

/// A candidate step, with no claim about whether it is licensed.
fn random_step(
    rng: &mut Rng,
    instance: &Instance,
    has_order: bool,
    strengthening_to_core: bool,
) -> Step {
    // Checked deletion may not carry a witness while strengthening to core -- there the checker
    // refuses one outright, so writing one would only produce parse-adjacent rejections. Under a
    // loaded order the format forbids it too, but the *checker* does not, so half of those
    // deletions carry one anyway: a generator that only ever wrote doc-legal deletions could
    // never watch the checker accept an illegal one.
    let deletion_witness = |rng: &mut Rng| {
        if strengthening_to_core || (has_order && rng.chance(50)) {
            Witness::default()
        } else {
            random_witness(rng, false)
        }
    };
    // How the subproof of a strengthening step is written. The bogus-hint spelling is the one
    // that reaches the `qed : <hint>` shortcut with a hint that is not a contradiction; it is
    // drawn often enough to make that state common and rarely enough that the checker still has
    // plenty of runs it can accept.
    // `HintedSubproof(Contradiction)` is drawn rarely on purpose: deriving `>= 1` at subproof
    // level only succeeds when the premises are already contradictory, so most draws of it would
    // spend a script on a rejection.
    let style = |rng: &mut Rng| match rng.below(20) {
        0..=5 => SubproofStyle::NoSubproof,
        6..=8 => SubproofStyle::Autoproved,
        9..=10 => SubproofStyle::HintedGoal(Hint::Contradiction),
        11..=14 => SubproofStyle::HintedGoal(Hint::NonContradiction),
        15 => SubproofStyle::HintedSubproof(Hint::Contradiction),
        _ => SubproofStyle::HintedSubproof(Hint::NonContradiction),
    };
    match rng.below(10) {
        0..=1 => Step::Rup(random_target_constraint(rng)),
        2 => Step::Pbc(random_target_constraint(rng)),
        3..=6 => {
            let c = random_target_constraint(rng);
            let w = random_witness(rng, false);
            Step::Red(c, w, style(rng))
        }
        7..=8 if has_order || instance.objective.is_some() => {
            let c = random_target_constraint(rng);
            let w = random_witness(rng, false);
            Step::Dom(c, w, style(rng))
        }
        7..=8 => Step::Rup(random_target_constraint(rng)),
        _ => {
            let id = 1 + rng.below(instance.constraints.len());
            Step::Delc(id, deletion_witness(rng))
        }
    }
}

/// Why the reference refuses a step.
///
/// `kind` is what the coverage counters read: the two interesting kinds are refusals that rest
/// only on a clause the reference took from the code under test (which cannot catch a defect in
/// that code) and refusals that rest on the format's checked-deletion substitution rule (where
/// the reference and the checker are known to disagree).
#[derive(Clone, Debug, PartialEq, Eq)]
enum RefusalKind {
    Ordinary,
    /// `dom`, refused only by [`DomClause::CodeDerived`].
    DomCodeDerivedClause,
    /// `delc` carrying a substitution the format says has to be empty here.
    DelcSubstitutionForbidden,
}

#[derive(Clone, Debug)]
struct Refusal {
    reason: String,
    kind: RefusalKind,
}

impl Refusal {
    fn ordinary(reason: String) -> Self {
        Refusal {
            reason,
            kind: RefusalKind::Ordinary,
        }
    }
}

impl std::fmt::Display for Refusal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.reason)
    }
}

/// The reference's verdict on one step: `None` when the rule's side condition holds, and the
/// reason it does not otherwise. Every condition here is the rule's definition, evaluated over
/// every assignment.
fn license_step(
    db: &RefDatabase,
    strengthening_to_core: bool,
    order: Option<&LoadedOrder>,
    objective: Option<&Objective>,
    instance: &Instance,
    step: &Step,
) -> Option<Refusal> {
    let premises = db.all();
    match step {
        Step::StrengtheningToCore => None,
        Step::Rup(c) | Step::Pbc(c) => {
            // Both rules are entailment preserving: `rup` accepts a constraint unit propagation
            // refutes the negation of, `pbc` one whose negation contradicts the database. Either
            // way every model of the database is a model of the constraint.
            if (0..NUM_ASSIGNMENTS).any(|a| satisfies_all(&premises, a) && !c.holds(a)) {
                Some(Refusal::ordinary(format!(
                    "{} {} is not entailed by the database",
                    if matches!(step, Step::Rup(_)) {
                        "rup"
                    } else {
                        "pbc"
                    },
                    c.render()
                )))
            } else {
                None
            }
        }
        Step::Red(c, w, _) => {
            let targets = if strengthening_to_core {
                db.core()
            } else {
                db.all()
            };
            if redundance_licensed(&premises, &targets, c, w, order, objective) {
                None
            } else {
                Some(Refusal::ordinary(format!(
                    "red {} : {} does not satisfy the redundance condition",
                    c.render(),
                    w.render()
                )))
            }
        }
        Step::Dom(c, w, _) => {
            if order.is_some_and(|order| !order.spec.is_preorder()) {
                return Some(Refusal::ordinary(
                    "dom over a relation that is not a preorder".to_string(),
                ));
            }
            dominance_licensed(&premises, &db.core(), c, w, order, objective).map(|clause| {
                Refusal {
                    reason: format!(
                        "dom {} : {} does not satisfy the dominance condition ({clause:?} clause)",
                        c.render(),
                        w.render()
                    ),
                    kind: match clause {
                        DomClause::DocDerived => RefusalKind::Ordinary,
                        DomClause::CodeDerived => RefusalKind::DomCodeDerivedClause,
                    },
                }
            })
        }
        Step::Delc(id, w) => {
            let target = &instance.constraints[*id - 1];
            let Some(position) = db.entries.iter().position(|e| e.1 && &e.0 == target) else {
                // Already deleted, or not a core constraint: the checker rejects on its own and
                // the reference has no obligation to model.
                return None;
            };
            let mut remaining = db.clone();
            remaining.entries.remove(position);
            let core = remaining.core();
            // Checked deletion runs with `only_core`, so its goals are proven from the core set
            // alone. With the substitution forced empty the redundance condition collapses to
            // implication: the deletion has to show the constraint follows from what is left.
            let implied = (0..NUM_ASSIGNMENTS).all(|a| !satisfies_all(&core, a) || target.holds(a));
            let must_be_empty =
                delc_substitution_must_be_empty(order.is_some(), strengthening_to_core);
            if must_be_empty && !w.0.is_empty() {
                let forbidden = Refusal {
                    reason: format!(
                        "delc {id} : {} carries a substitution, but the format says it has to be \
                         empty when an order is loaded or strengthening-to-core is enabled",
                        w.render()
                    ),
                    kind: RefusalKind::DelcSubstitutionForbidden,
                };
                // The step is refused either way. Which reason is reported matters only for the
                // message and the counters: when the deletion would go through but for the
                // substitution rule, say so, because that is the case where the checker and the
                // document part company. When it would fail anyway, the ordinary reason is the
                // one a reader needs, and the checker rejects the step too.
                return if implied || redundance_licensed(&core, &core, target, w, order, objective)
                {
                    Some(forbidden)
                } else {
                    Some(Refusal::ordinary(format!(
                        "delc {id} : {} does not license removing {} (and the format forbids the \
                         substitution here in any case)",
                        w.render(),
                        target.render()
                    )))
                };
            }
            let licensed = if must_be_empty {
                implied
            } else {
                redundance_licensed(&core, &core, target, w, order, objective)
            };
            if licensed {
                None
            } else {
                Some(Refusal::ordinary(format!(
                    "delc {id} : {} does not license removing {}",
                    w.render(),
                    target.render()
                )))
            }
        }
    }
}

/// The effect an accepted step has on the reference's database.
fn apply_step(db: &mut RefDatabase, strengthening_to_core: bool, instance: &Instance, step: &Step) {
    match step {
        Step::StrengtheningToCore => db.move_all_to_core(),
        // `rup` and `pbc` do not override `add_constraints_to_core`, so their constraints land
        // in the derived set; the strengthening rules put theirs in core exactly when
        // strengthening-to-core is on.
        Step::Rup(c) | Step::Pbc(c) => db.entries.push((c.clone(), false)),
        Step::Red(c, _, _) | Step::Dom(c, _, _) => {
            db.entries.push((c.clone(), strengthening_to_core))
        }
        Step::Delc(id, _) => {
            let target = &instance.constraints[*id - 1];
            if let Some(position) = db.entries.iter().position(|e| e.1 && &e.0 == target) {
                db.entries.remove(position);
            }
        }
    }
}

#[derive(Default, Debug)]
struct ScriptCounters {
    scripts: usize,
    accepted: usize,
    reference_licensed: usize,
    reference_refused: usize,
    refused_and_rejected: usize,
    step_rup: usize,
    step_pbc: usize,
    step_red: usize,
    step_red_subproof: usize,
    step_dom: usize,
    step_delc: usize,
    step_stc_midscript: usize,
    /// Strengthening steps whose subproof closes `proofgoal #1` with `qed : <hint>`.
    step_hinted_goal: usize,
    /// Strengthening steps whose subproof closes *itself* with `qed : <hint>`, skipping every
    /// obligation it still owed.
    step_hinted_subproof: usize,
    /// ... either form, where the hinted constraint is not a contradiction.
    step_bogus_hint: usize,
    /// ... and the reference refuses the step it is written inside. This is the state the
    /// `qed : <hint>` shortcut has to be exercised in: a discharge nothing licenses, standing in
    /// for an obligation that really is not met.
    bogus_hint_over_refused_step: usize,
    /// ... of which the hint closes the whole subproof, skipping every obligation at once.
    bogus_subproof_hint_over_refused_step: usize,
    /// ... and, sharper, the obligation `#1` names is itself one the reference refuses, so the
    /// hinted discharge is the only thing between the checker and a rejection.
    bogus_hint_over_failing_goal_one: usize,
    /// `dom` steps the reference refuses only by a clause it transcribed from
    /// `dom_strengthening.rs` -- see [`dominance_licensed`]. These cannot catch a defect in the
    /// code they came from; the counter is here so the weakness is visible rather than implied.
    dom_refused_by_code_derived_clause: usize,
    /// Checked deletions the reference refuses because the format forbids their substitution.
    delc_substitution_forbidden: usize,
    with_order: usize,
    with_spec_order: usize,
    with_objective: usize,
    strengthening_to_core: usize,
    broken_fresh_right: usize,
}

#[test]
fn accepted_scripts_satisfy_the_reference_semantics() {
    let cases = case_count();
    let harness = Harness::new();
    let mut counters = ScriptCounters::default();
    let mut failures: Vec<String> = Vec::new();
    // Kept apart from `failures` on purpose: see the assertion at the end of this test. A
    // divergence the reference is *expected* to report must not consume the three-failure budget
    // the rest of the sweep needs, or one known finding would hide every other regression.

    for seed in 0..cases as u64 {
        let (script, refusals, final_db) = generate_script(seed);
        counters.scripts += 1;
        for (index, step) in script.steps.iter().enumerate() {
            let facts = &script.step_facts[index];
            match step {
                Step::StrengtheningToCore => counters.step_stc_midscript += 1,
                Step::Rup(_) => counters.step_rup += 1,
                Step::Pbc(_) => counters.step_pbc += 1,
                Step::Red(_, _, style) => {
                    counters.step_red += 1;
                    if style.has_subproof() {
                        counters.step_red_subproof += 1;
                    }
                    // Sharpest form of the hinted-discharge state, and the only one this test can
                    // name exactly: the reference decides goal `#1` of a `red` on its own, so it
                    // can say whether the obligation the hint claims to discharge really fails.
                    if *style == SubproofStyle::HintedGoal(Hint::NonContradiction)
                        && facts.goal_one_fails
                    {
                        counters.bogus_hint_over_failing_goal_one += 1;
                    }
                }
                Step::Dom(_, _, _) => counters.step_dom += 1,
                Step::Delc(_, _) => counters.step_delc += 1,
            }
            if let Some(style) = step.subproof_style() {
                match style {
                    SubproofStyle::HintedGoal(_) => counters.step_hinted_goal += 1,
                    SubproofStyle::HintedSubproof(_) => counters.step_hinted_subproof += 1,
                    _ => (),
                }
                if style.is_bogus() {
                    counters.step_bogus_hint += 1;
                    if facts.refusal.is_some() {
                        counters.bogus_hint_over_refused_step += 1;
                        if matches!(style, SubproofStyle::HintedSubproof(_)) {
                            counters.bogus_subproof_hint_over_refused_step += 1;
                        }
                    }
                }
            }
            match &facts.refusal {
                Some(RefusalKind::DomCodeDerivedClause) => {
                    counters.dom_refused_by_code_derived_clause += 1
                }
                Some(RefusalKind::DelcSubstitutionForbidden) => {
                    counters.delc_substitution_forbidden += 1
                }
                _ => (),
            }
        }
        if let Some(order) = &script.order {
            counters.with_order += 1;
            if order.spec.with_spec {
                counters.with_spec_order += 1;
            }
            if script.fresh_right != FreshRight::Correct {
                counters.broken_fresh_right += 1;
            }
        }
        if script.instance.objective.is_some() {
            counters.with_objective += 1;
        }
        if script.strengthening_to_core_first {
            counters.strengthening_to_core += 1;
        }

        if refusals.is_empty() {
            counters.reference_licensed += 1;
        } else {
            counters.reference_refused += 1;
        }
        // Every refusal is treated the same way. There was briefly a partition here, holding
        // `DelcSubstitutionForbidden` aside so that one known disagreement could be asserted
        // separately without masking the rest of the sweep; that disagreement turned out to be an
        // error in the document the reference was transcribed from, not in the checker, so there
        // is nothing left to hold aside.
        let outcome = harness.run(&script.instance.render(), &script.render());
        if outcome == Outcome::Accepted {
            counters.accepted += 1;
            if let Some(refusal) = refusals.first() {
                failures.push(format!(
                    "the checker accepted a run the reference refuses, seed {}\n  {}\n  proof:\n{}",
                    script.seed,
                    refusal,
                    indent(&script.render())
                ));
            } else if !has_model(&final_db.all()) {
                // The formula is satisfiable by construction, so a database with no model means
                // some rule in the run destroyed satisfiability.
                failures.push(format!(
                    "an accepted run left an unsatisfiable database, seed {}\n  the formula \
                     is satisfied by {}\n  proof:\n{}",
                    script.seed,
                    render_assignment(script.instance.witness_assignment),
                    indent(&script.render())
                ));
            }
        } else if !refusals.is_empty() {
            counters.refused_and_rejected += 1;
        }
        if failures.len() >= 3 {
            break;
        }
    }

    profile("obligation scripts", &counters);
    assert!(
        failures.is_empty(),
        "{} of {} randomized obligation scripts disagreed with the reference:\n\n{}",
        failures.len(),
        cases,
        failures.join("\n")
    );

    if cases >= DEFAULT_CASES {
        let floor = |what: &str, got: usize, want: usize| {
            assert!(
                got >= want,
                "the script generator has stopped exercising {what}: {got} in {cases} scripts, \
                 expected at least {want}. Full profile: {counters:?}"
            );
        };
        // Without these the assertions above are satisfied by a generator that produces nothing
        // the checker accepts, or nothing the reference refuses.
        floor("runs the checker accepts", counters.accepted, 30);
        floor(
            "runs the reference licenses",
            counters.reference_licensed,
            30,
        );
        floor("runs the reference refuses", counters.reference_refused, 60);
        floor("`red` steps", counters.step_red, 100);
        floor(
            "`red` steps with an explicit subproof",
            counters.step_red_subproof,
            30,
        );
        floor("`dom` steps", counters.step_dom, 30);
        floor("`pbc` steps", counters.step_pbc, 20);
        floor("checked deletions", counters.step_delc, 20);
        floor("scripts with an order loaded", counters.with_order, 100);
        floor(
            "scripts with a specification order",
            counters.with_spec_order,
            15,
        );
        floor("scripts with an objective", counters.with_objective, 60);
        // Both settings have to stay in play: they decide whether a strengthening rule's
        // constraint lands in the core or the derived set, and therefore whether a later rule
        // owes it an obligation at all.
        floor(
            "scripts under strengthening-to-core",
            counters.strengthening_to_core,
            40,
        );
        floor(
            "scripts with strengthening-to-core off",
            counters.scripts - counters.strengthening_to_core,
            100,
        );
        floor(
            "scripts that turn strengthening-to-core on mid-run",
            counters.step_stc_midscript,
            5,
        );
        // The `qed : <goalID> : <hint>` shortcut. Without the last two floors the hinted
        // discharge is generated but never in the state that matters: a hint that is not a
        // contradiction, standing in for an obligation the reference refuses. Both are counted
        // off the reference -- `bogus_hint_over_failing_goal_one` from `redundance_goal_one_holds`
        // alone -- so a checker that discharges every hint cannot satisfy its own floor.
        floor(
            "subproofs that close a proofgoal with an explicit hint",
            counters.step_hinted_goal,
            30,
        );
        floor(
            "subproofs that close themselves with an explicit hint",
            counters.step_hinted_subproof,
            25,
        );
        floor(
            "hints that are not a contradiction",
            counters.step_bogus_hint,
            25,
        );
        floor(
            "hints that are not a contradiction, inside a step the reference refuses",
            counters.bogus_hint_over_refused_step,
            12,
        );
        floor(
            "hints that are not a contradiction and close the whole subproof, inside a step the \
             reference refuses",
            counters.bogus_subproof_hint_over_refused_step,
            6,
        );
        floor(
            "hints that are not a contradiction, standing in for a `red` goal `#1` the reference \
             refuses",
            counters.bogus_hint_over_failing_goal_one,
            4,
        );
        // Not a floor on a *state* but on the honesty of the profile: the `dom` leg's two
        // code-transcribed clauses (see `dominance_licensed`) do refuse steps, and a reader
        // should be able to see how many.
        floor(
            "`dom` steps refused only by a clause transcribed from the code under test",
            counters.dom_refused_by_code_derived_clause,
            1,
        );
        // No floor on `delc_substitution_forbidden`. With the reference corrected it counts
        // only a witness offered under strengthening-to-core, and `random_step` suppresses the
        // witness there by construction, so the state is unreachable and a floor on it would be
        // a floor of zero -- which measures nothing. The counter stays in the profile because a
        // non-zero value would mean the generator had started producing that shape, and the
        // reference's remaining clause would then be under test rather than merely stated.
    }

    // The `delc` substitution divergence that used to be asserted here is gone: it was a
    // documentation error, not a checker defect. `proof_format_overview.md` said a loaded order
    // forbids a substitution; tracing the mechanism showed the deletion owes the order's
    // proofgoals exactly as `red` does, so an order-worsening witness is already refused. The
    // document has been corrected and the reference states the corrected condition. The episode
    // is worth keeping in view: a differential is only as good as the text it is transcribed
    // from, and this one briefly inherited an error instead of catching one.
}

// -------------------------------------------------------------------------------------------
// Test 3: a version-2 redundance step with an empty witness is a proof by contradiction.
// -------------------------------------------------------------------------------------------

/// Version 2 has no `pbc` rule: "It is no longer allowed to use the redundance-based
/// strengthening rule with an empty witness. The new proof by contradiction should be used
/// instead", says the 3.0 migration guide, which is also the statement of what the version-2
/// spelling means. So `red C ;  ; begin ... end` owes exactly what `pbc C` owes -- a
/// contradiction from the database together with `~C` -- and the constraint it adds must be
/// entailed by the database.
///
/// This is the one shape where a subproof is a proof by contradiction *and* carries numbered
/// obligations, which is why it has its own test: in version 3 the two are mutually exclusive
/// (`pbc` generates no goals at all), so nothing a version-3 script can say reaches the code
/// that decides whether a discharged proofgoal settles the enclosing contradiction.
#[derive(Default, Debug)]
struct LegacyCounters {
    cases: usize,
    accepted: usize,
    entailed: usize,
    not_entailed: usize,
    goal_internal: usize,
    goal_database: usize,
    accepted_with_database_goal: usize,
}

#[test]
fn version_two_empty_witness_redundance_needs_its_contradiction() {
    let cases = case_count();
    let harness = Harness::new();
    let mut counters = LegacyCounters::default();
    let mut failures: Vec<String> = Vec::new();

    for seed in 0..cases as u64 {
        let mut rng = Rng::new(seed.wrapping_mul(0xD1B54A32D192ED03));
        let instance = random_instance(&mut rng, false);
        // Half the cases add a constraint the database entails, so that the test has accepted
        // runs to compare and is not satisfied by a checker that rejects everything.
        let target = if rng.chance(50) {
            instance.constraints[rng.below(instance.constraints.len())].clone()
        } else {
            random_target_constraint(&mut rng)
        };
        let goal = if rng.chance(50) {
            GoalId::Internal(1)
        } else {
            GoalId::Database(1 + rng.below(instance.constraints.len()))
        };

        let entailed = (0..NUM_ASSIGNMENTS)
            .all(|a| !satisfies_all(&instance.constraints, a) || target.holds(a));
        counters.cases += 1;
        if entailed {
            counters.entailed += 1;
        } else {
            counters.not_entailed += 1;
        }
        match goal {
            GoalId::Internal(_) => counters.goal_internal += 1,
            GoalId::Database(_) => counters.goal_database += 1,
        }

        let proof = [
            "pseudo-Boolean proof version 2.0".to_string(),
            format!("f {}", instance.constraints.len()),
            format!("red {} ;  ; begin", target.render()),
            format!("  proofgoal {}", goal.render()),
            "    rup >= 1 ;".to_string(),
            "  end".to_string(),
            "end".to_string(),
            "output NONE".to_string(),
            "conclusion NONE".to_string(),
            "end pseudo-Boolean proof".to_string(),
        ]
        .join("\n")
            + "\n";

        let outcome = harness.run(&instance.render(), &proof);
        if outcome == Outcome::Accepted {
            counters.accepted += 1;
            if matches!(goal, GoalId::Database(_)) {
                counters.accepted_with_database_goal += 1;
            }
            if !entailed {
                failures.push(format!(
                    "a version-2 empty-witness `red` was accepted for a constraint the database \
                     does not entail, seed {seed}\\n  the database is satisfied by {}, which \
                     falsifies {}\\n  proof:\\n{}",
                    render_assignment(
                        (0..NUM_ASSIGNMENTS)
                            .find(|&a| satisfies_all(&instance.constraints, a) && !target.holds(a))
                            .expect("a non-entailed constraint has a counterexample")
                    ),
                    target.render(),
                    indent(&proof)
                ));
                if failures.len() >= 3 {
                    break;
                }
            }
        }
    }

    profile("version-2 proof by contradiction", &counters);
    assert!(
        failures.is_empty(),
        "{} of {} version-2 proof-by-contradiction cases added a constraint without proving \
         it:\\n\\n{}",
        failures.len(),
        cases,
        failures.join("\\n")
    );

    if cases >= DEFAULT_CASES {
        assert!(
            counters.accepted >= 30,
            "no version-2 empty-witness `red` is accepted any more, so this test compares \
             nothing: {counters:?}"
        );
        assert!(
            counters.not_entailed >= 60,
            "the generator has stopped offering constraints the database does not entail, so \
             the assertion above is vacuous: {counters:?}"
        );
        assert!(
            counters.accepted_with_database_goal >= 15,
            "the database-goal spelling of the subproof has stopped being accepted, so the one \
             shape that reaches the proof-by-contradiction discharge is untested: {counters:?}"
        );
    }
}

// -------------------------------------------------------------------------------------------
// Test 4: scope premises do not license a strengthening step.
// -------------------------------------------------------------------------------------------

/// A `scope` inside a strengthening subproof introduces the loaded order's *specification*:
/// "two optional named scopes can appear inside a strengthening-rule subproof to introduce the
/// specification constraints as additional premises". Those constraints were derived inside
/// `def_order`, from the empty formula, about the order's auxiliary variables. Introducing them
/// as premises is a conservative extension only while those auxiliary variables carry no
/// constraint of their own -- otherwise the premises can contradict the database, and every goal
/// inside the scope is then discharged by a contradiction that has nothing to do with the goal.
///
/// This family builds exactly that situation and its innocent twin: an order whose `spec` pins
/// `$q`, optionally a `red` step somewhere in the proof that pins `$q` the other way, and a
/// `dom` whose obligations are all written inside the two scopes. Whatever the scopes do, the
/// `dom` that comes out has to satisfy the dominance condition.
#[derive(Default, Debug)]
struct ScopeCounters {
    cases: usize,
    accepted: usize,
    clean_accepted: usize,
    with_clash: usize,
    clash_and_unlicensed: usize,
    clash_before_load: usize,
    with_database_goals: usize,
    licensed: usize,
}

#[test]
fn scope_premises_do_not_license_a_strengthening_step() {
    let cases = case_count();
    let harness = Harness::new();
    let mut counters = ScopeCounters::default();
    let mut failures: Vec<String> = Vec::new();

    for seed in 0..cases as u64 {
        let mut rng = Rng::new(seed.wrapping_mul(0xA24BAED4963EE407));
        let instance = random_instance(&mut rng, false);
        let spec_positive = rng.chance(50);
        let spec = OrderSpec {
            name: "specorder",
            arity: 1,
            definition: vec![formal(&[(1, 0, true), (1, 1, false)], 1)],
            with_spec: true,
            spec_positive,
        };
        let loaded_var = rng.below(NUM_PROBLEM_VARS);
        let order = LoadedOrder {
            spec,
            lits: vec![(loaded_var, false)],
        };
        // The constraint that clashes with the specification: it pins `$q` to the opposite of
        // what the `spec` block does, so the two together are contradictory.
        let clash = rng.chance(60);
        let clash_before_load = rng.chance(50);
        let clash_constraint = Constraint {
            terms: vec![(1, AUX_VAR, spec_positive)],
            degree: 1,
        };
        let clash_witness = Witness(vec![(
            AUX_VAR,
            if spec_positive {
                WitnessValue::Zero
            } else {
                WitnessValue::One
            },
        )]);
        let strengthening_to_core = rng.chance(50);
        let with_database_goals = rng.chance(50);

        let target = random_target_constraint(&mut rng);
        let witness = random_witness(&mut rng, false);

        // The reference's picture of the database when the `dom` is reached.
        let mut db = RefDatabase {
            entries: instance
                .constraints
                .iter()
                .map(|c| (c.clone(), true))
                .collect(),
        };
        if clash {
            // Wherever it is written, `load_order` moves every constraint into the core set, and
            // the `dom` is written after the `load_order`.
            db.entries.push((clash_constraint.clone(), true));
        }
        let dom = Step::Dom(target.clone(), witness.clone(), SubproofStyle::Autoproved);
        let verdict = license_step(
            &db,
            strengthening_to_core,
            Some(&order),
            None,
            &instance,
            &dom,
        );

        counters.cases += 1;
        if clash {
            counters.with_clash += 1;
            if clash_before_load {
                counters.clash_before_load += 1;
            }
            if verdict.is_some() {
                counters.clash_and_unlicensed += 1;
            }
        }
        if verdict.is_none() {
            counters.licensed += 1;
        }
        if with_database_goals {
            counters.with_database_goals += 1;
        }

        let clash_line = format!(
            "red {} : {} ;",
            clash_constraint.render(),
            clash_witness.render()
        );
        let mut lines = vec![
            "pseudo-Boolean proof version 3.0".to_string(),
            format!("f {};", instance.constraints.len()),
        ];
        if strengthening_to_core {
            lines.push("strengthening_to_core on;".to_string());
        }
        if clash && clash_before_load {
            lines.push(clash_line.clone());
        }
        lines.extend(order.spec.render(FreshRight::Correct));
        lines.push(order.render());
        if clash && !clash_before_load {
            lines.push(clash_line);
        }
        lines.push(format!(
            "dom {} : {} : subproof",
            target.render(),
            witness.render()
        ));
        lines.push("  scope leq".to_string());
        // `#1` is the order goal; `scope leq` "may be used to prove all proof goals except the
        // negated-order goal", and the database obligations are among them.
        lines.push("    proofgoal #1".to_string());
        lines.push("      rup >= 1;".to_string());
        lines.push("    qed;".to_string());
        if with_database_goals {
            for id in 1..=instance.constraints.len() {
                lines.push(format!("    proofgoal {id}"));
                lines.push("      rup >= 1;".to_string());
                lines.push("    qed;".to_string());
            }
        }
        lines.push("  end scope;".to_string());
        lines.push("  scope geq".to_string());
        // `#2` is the negated-order goal, which `scope geq` exists for.
        lines.push("    proofgoal #2".to_string());
        lines.push("      rup >= 1;".to_string());
        lines.push("    qed;".to_string());
        lines.push("  end scope;".to_string());
        lines.push("qed;".to_string());
        lines.push("output NONE;".to_string());
        lines.push("conclusion NONE;".to_string());
        lines.push("end pseudo-Boolean proof;".to_string());
        let proof = lines.join("\n") + "\n";

        let outcome = harness.run(&instance.render(), &proof);
        if outcome == Outcome::Accepted {
            counters.accepted += 1;
            if !clash {
                counters.clean_accepted += 1;
            }
            // There is deliberately no `clash_accepted` counter. At HEAD the state is
            // unreachable by construction, and a counter whose only possible value is zero
            // measures nothing: every clash script writes `scope leq`, the order always has a
            // `spec` block, and `ScopeRule::compute`
            // (`veripb-checker/src/rules/scope.rs`) refuses a scope whose order has an auxiliary
            // variable that occurs in the database. Both placements of the clashing constraint
            // reach it -- before `load_order` and after -- because the guard runs at `scope`,
            // not at `load_order`. That is not a reason to stop generating the clash: removing
            // the guard makes three of the first eight cases here accept a `dom` the reference
            // refuses, which is what the assertion above exists for.
            if let Some(reason) = verdict {
                failures.push(format!(
                    "a `dom` whose obligations were discharged inside a scope was accepted, but \
                     the reference refuses it, seed {seed}\n  {reason}\n  proof:\n{}",
                    indent(&proof)
                ));
                if failures.len() >= 3 {
                    break;
                }
            } else {
                let mut after = db.clone();
                after.entries.push((target.clone(), strengthening_to_core));
                if !has_model(&after.all()) {
                    failures.push(format!(
                        "an accepted `dom` left an unsatisfiable database, seed {seed}\n  \
                         proof:\n{}",
                        indent(&proof)
                    ));
                    if failures.len() >= 3 {
                        break;
                    }
                }
            }
        }
    }

    profile("scope premises", &counters);
    assert!(
        failures.is_empty(),
        "{} of {} scope-premise cases disagreed with the reference:\n\n{}",
        failures.len(),
        cases,
        failures.join("\n")
    );

    if cases >= DEFAULT_CASES {
        assert!(
            counters.clean_accepted >= 10,
            "no scope-premise script without an auxiliary-variable clash is accepted any more, \
             so the template no longer reaches the scopes it is about: {counters:?}"
        );
        assert!(
            counters.clash_and_unlicensed >= 60,
            "the generator has stopped producing the case this test exists for -- an auxiliary \
             variable constrained in the database together with a `dom` the reference refuses: \
             {counters:?}"
        );
        assert!(
            counters.clash_before_load >= 25
                && counters.with_clash - counters.clash_before_load >= 25,
            "both placements of the clashing constraint (before and after `load_order`) have to \
             stay in play, because a `load_order`-time freshness check would only catch one: \
             {counters:?}"
        );
        assert!(
            counters.with_database_goals >= 60,
            "the generator has stopped writing database obligations inside a scope: {counters:?}"
        );
    }
}

// -------------------------------------------------------------------------------------------
// Test 5: an accepted `def_order` denotes a preorder.
// -------------------------------------------------------------------------------------------

#[derive(Default, Debug)]
struct OrderCounters {
    checked: usize,
    accepted: usize,
    non_preorders: usize,
    /// Definitions written in the version-2 dialect, where the block sequence is not enforced by
    /// the grammar and has to be enforced by the checker.
    version_two: usize,
    version_two_accepted: usize,
    /// Definitions whose blocks are out of sequence.
    out_of_sequence: usize,
    /// ... and whose relation is not a preorder. This is wrong verdict 24's shape: the checker
    /// used to accept these, and the relation it then loaded was a 3-cycle.
    out_of_sequence_non_preorder: usize,
}

/// An accepted `def_order` denotes a preorder -- in both dialects, and whatever order its blocks
/// are written in.
///
/// `def_order` demands a preorder: "The order must be a preorder, thus the defined order must be
/// reflexive and transitive." The reference computes the relation the `def` block denotes and
/// checks both properties by enumeration over all tuples.
///
/// The two axes below are not decoration. Wrong verdict 24 was a version-2 order whose
/// `transitivity` block came before `def`, so the property this test checks is exactly the one
/// that defect violated -- in a dialect and a layout a version-3, single-`def` template cannot
/// express. HEAD refuses those layouts (`OrderPhase` in `veripb-checker/src/order_context.rs`);
/// removing that ladder makes this test red again.
#[test]
fn accepted_orders_are_preorders() {
    let harness = Harness::new();
    let formula = Instance {
        constraints: vec![Constraint {
            terms: vec![(1, 0, false), (1, 1, false)],
            degree: 1,
        }],
        objective: None,
        witness_assignment: 0b11,
    };
    let mut counters = OrderCounters::default();
    let mut failures = Vec::new();

    for spec in order_catalogue() {
        for dialect in [Dialect::Version3, Dialect::Version2] {
            // The version-2 spelling of a `spec` block's witness is not the one this file writes,
            // so specification orders are generated in version 3 only. Auxiliary variables are
            // covered by `scope_premises_do_not_license_a_strengthening_step` instead.
            if dialect == Dialect::Version2 && spec.with_spec {
                continue;
            }
            for layout in [BlockLayout::Sequential, BlockLayout::TransitivityBeforeDef] {
                for fresh_right in [
                    FreshRight::Correct,
                    FreshRight::Empty,
                    FreshRight::Short,
                    FreshRight::NotFresh,
                ] {
                    // A one-variable order has no "short" spelling distinct from the empty one.
                    if fresh_right == FreshRight::Short && spec.arity < 2 {
                        continue;
                    }
                    let proof = dialect.wrap(spec.render_in(dialect, layout, fresh_right));

                    counters.checked += 1;
                    if !spec.is_preorder() {
                        counters.non_preorders += 1;
                    }
                    if dialect == Dialect::Version2 {
                        counters.version_two += 1;
                    }
                    if layout != BlockLayout::Sequential {
                        counters.out_of_sequence += 1;
                        if !spec.is_preorder() {
                            counters.out_of_sequence_non_preorder += 1;
                        }
                    }
                    let outcome = harness.run(&formula.render(), &proof);
                    if outcome == Outcome::Accepted {
                        counters.accepted += 1;
                        if dialect == Dialect::Version2 {
                            counters.version_two_accepted += 1;
                        }
                        if !spec.is_preorder() {
                            failures.push(format!(
                                "`def_order {}` was accepted ({dialect:?}, {layout:?}), but the \
                                 relation it denotes is {}{}\n  proof:\n{}",
                                spec.name,
                                if spec.is_reflexive() {
                                    ""
                                } else {
                                    "not reflexive"
                                },
                                if spec.is_transitive() {
                                    ""
                                } else {
                                    " not transitive"
                                },
                                indent(&proof)
                            ));
                        }
                    }
                }
            }
        }
    }

    profile("order definitions", &counters);
    assert!(
        failures.is_empty(),
        "{} `def_order` block(s) denote a relation that is not a preorder and were accepted \
         anyway:\n\n{}",
        failures.len(),
        failures.join("\n")
    );
    // Every floor here is read off the reference: `is_preorder` is computed by enumeration over
    // the definition constraints and never from what the checker said.
    assert!(
        counters.non_preorders >= 6,
        "the order catalogue has stopped offering relations that are not preorders: {counters:?}"
    );
    assert!(
        counters.accepted >= 3,
        "no `def_order` block in the catalogue is accepted any more, so this test compares \
         nothing: {counters:?}"
    );
    assert!(
        // Two: the catalogue holds exactly two preorders without a `spec` block (`leq1`, `leq2`),
        // and only the correctly-spelled `fresh_right` list of each is accepted.
        counters.version_two_accepted >= 2,
        "no version-2 `def_order` block is accepted any more, so the dialect wrong verdict 24 \
         lived in is being refused wholesale and this test compares nothing there: {counters:?}"
    );
    assert!(
        counters.out_of_sequence_non_preorder >= 6,
        "the out-of-sequence layouts have stopped being written over relations that are not \
         preorders, which is the only combination that can reproduce wrong verdict 24: \
         {counters:?}"
    );
}

// -------------------------------------------------------------------------------------------
// The reference has to be right about the answers it gives, or everything above is vacuous.
// -------------------------------------------------------------------------------------------

#[test]
fn reference_model_is_sane() {
    // Evaluation and negation of a constraint.
    let c = Constraint {
        terms: vec![(2, 0, false), (1, 1, true)],
        degree: 2,
    };
    assert!(c.holds(0b00001)); // x1 true (+2), ~x2 true (+1): 3 >= 2
    assert!(!c.holds(0b00010)); // x1 false, x2 true: 0 >= 2 is false
    assert!(!c.holds(0b00000)); // x1 false, ~x2 true: 1 >= 2 is false

    // Witness composition: `C|w` holds at `a` exactly when `C` holds at `a . w`.
    let w = Witness(vec![(0, WitnessValue::One)]);
    assert!(c.holds(w.apply(0b00010)));
    let flip = Witness(vec![(0, WitnessValue::Lit(1, true))]);
    assert_eq!(flip.apply(0b00010) & 1, 0);
    assert_eq!(flip.apply(0b00000) & 1, 1);

    // The order catalogue says what it claims to say.
    let catalogue = order_catalogue();
    let by_name = |name: &str| {
        catalogue
            .iter()
            .find(|spec| spec.name == name)
            .expect("catalogue entry")
            .clone()
    };
    let leq1 = by_name("leq1");
    assert!(leq1.is_preorder());
    assert!(leq1.leq(0, 1) && !leq1.leq(1, 0));
    let nt2 = by_name("nt2");
    assert!(nt2.is_reflexive());
    assert!(!nt2.is_transitive());
    // The only excluded pair is (11, 00), which is what makes it non-transitive.
    assert!(nt2.leq(0b11, 0b01) && nt2.leq(0b01, 0b00) && !nt2.leq(0b11, 0b00));
    let cyc3 = by_name("cyc3");
    assert!(cyc3.is_reflexive());
    assert!(!cyc3.is_transitive());
    let nr1 = by_name("nr1");
    assert!(!nr1.is_reflexive());

    // Redundance: `1 x1 >= 1` with the witness `x1 -> 1` is redundant with respect to any
    // database that the witness does not disturb, and not redundant when the database forbids
    // `x1`.
    let target = Constraint {
        terms: vec![(1, 0, false)],
        degree: 1,
    };
    let witness = Witness(vec![(0, WitnessValue::One)]);
    let empty: Vec<Constraint> = Vec::new();
    assert!(redundance_licensed(
        &empty, &empty, &target, &witness, None, None
    ));
    let forbids = vec![Constraint {
        terms: vec![(1, 0, true)],
        degree: 1,
    }];
    assert!(!redundance_licensed(
        &forbids, &forbids, &target, &witness, None, None
    ));

    // Dominance needs a strict improvement, so the identity witness never licenses it.
    let identity = Witness(vec![(0, WitnessValue::Lit(0, false))]);
    let order = LoadedOrder {
        spec: leq1,
        lits: vec![(0, false)],
    };
    assert_eq!(
        dominance_licensed(&empty, &empty, &target, &identity, Some(&order), None),
        Some(DomClause::DocDerived)
    );

    // The inventory numbering follows the format overview.
    let with_order = LoadedOrder {
        spec: by_name("leq2"),
        lits: vec![(0, false), (1, false)],
    };
    let red = Inventory::redundance(Some(&with_order), true);
    // `#1` the constraint, `#2`/`#3` the two order constraints, `#4` the objective.
    assert_eq!(red.internal_len(), 5);
    assert_eq!(red.internal[4].unwrap().scope, Some(Scope::Leq));
    assert_eq!(red.database, Some(Scope::Leq));
    let dom = Inventory::dominance(Some(&with_order), false);
    // `#1`/`#2` the order constraints, `#3` the negated order.
    assert_eq!(dom.internal_len(), 4);
    assert_eq!(dom.internal[3].unwrap().scope, Some(Scope::Geq));
    let pbc = Inventory::proof_by_contradiction();
    assert_eq!(pbc.internal_len(), 1);
    assert_eq!(pbc.database, None);
    assert_eq!(
        admit(&pbc, GoalId::Database(1), None, &[1]),
        Admission::DatabaseNotExisting
    );
    assert_eq!(
        admit(&dom, GoalId::Internal(3), Some(Scope::Leq), &[1]),
        Admission::NotInScope
    );
    assert_eq!(
        admit(&dom, GoalId::Internal(3), Some(Scope::Geq), &[1]),
        Admission::Admitted
    );
    assert_eq!(
        admit(&dom, GoalId::Internal(0), None, &[1]),
        Admission::InternalAlreadyProven
    );

    // Goal `#1` of a `red` on its own. `1 x1 >= 1` with `x1 -> 1` satisfies it against any
    // database; with `x1 -> 0` it fails, because the witnessed assignment falsifies exactly the
    // constraint the goal is about.
    assert!(redundance_goal_one_holds(&empty, &target, &witness));
    assert!(!redundance_goal_one_holds(
        &empty,
        &target,
        &Witness(vec![(0, WitnessValue::Zero)])
    ));

    // The format's checked-deletion condition, as stated: an order loaded *or*
    // strengthening-to-core on, not only the latter.
    // A loaded order does NOT forbid a substitution: the deletion owes the order's proofgoals,
    // so the witness is checked rather than unchecked. See `delc_substitution_must_be_empty`.
    assert!(!delc_substitution_must_be_empty(false, false));
    assert!(!delc_substitution_must_be_empty(true, false));
    assert!(delc_substitution_must_be_empty(false, true));
    assert!(delc_substitution_must_be_empty(true, true));

    // The dominance clause split. With no order and an objective the only clause is the
    // objective's strictness, which is the one taken from the code; with an order the
    // doc-derived clauses answer first.
    let objective = Objective {
        terms: vec![(1, 0, false)],
    };
    let to_zero = Witness(vec![(0, WitnessValue::Zero)]);
    // `1 ~x1 >= 1` is falsified exactly where `x1` holds, and the witness sends those
    // assignments to `x1 = 0`: a strict improvement in `min: x1`.
    let forbid_x1 = Constraint {
        terms: vec![(1, 0, true)],
        degree: 1,
    };
    assert_eq!(
        dominance_licensed(&empty, &empty, &forbid_x1, &to_zero, None, Some(&objective)),
        None,
        "witnessing `x1 -> 0` strictly lowers `min: x1`, so objective-only dominance holds"
    );
    assert_eq!(
        dominance_licensed(&empty, &empty, &target, &identity, None, Some(&objective)),
        Some(DomClause::CodeDerived),
        "the identity witness does not lower the objective, and strictness is the code-derived \
         clause"
    );
}

// -------------------------------------------------------------------------------------------
// Shared helpers.
// -------------------------------------------------------------------------------------------

/// Print a counter profile when `VERIPB_OBLIGATION_PROFILE` is set. The floors below are
/// calibrated from it, and it is how a reviewer checks that the generator still reaches the
/// states the floors are about.
fn profile(label: &str, counters: &impl std::fmt::Debug) {
    if std::env::var_os("VERIPB_OBLIGATION_PROFILE").is_some() {
        println!("{label}: {counters:?}");
    }
}

fn case_count() -> usize {
    std::env::var("VERIPB_OBLIGATION_CASES")
        .ok()
        .and_then(|value| value.parse().ok())
        .unwrap_or(DEFAULT_CASES)
}

fn indent(text: &str) -> String {
    text.lines()
        .map(|line| format!("    {line}"))
        .collect::<Vec<_>>()
        .join("\n")
}

fn render_assignment(assignment: u32) -> String {
    (0..NUM_VARS)
        .map(|var| {
            format!(
                "{}{}",
                if lit_holds(assignment, var, false) {
                    ""
                } else {
                    "~"
                },
                var_name(var)
            )
        })
        .collect::<Vec<_>>()
        .join(" ")
}
