//! Every rule the version-3 grammar places at the top level is refused inside
//! an order definition — in *both* proof dialects.
//!
//! `def_order`/`pre_order` and `spec` return `true` from
//! `Checkable::swaps_database`: from the line after them until the matching
//! `end`, the checker runs against a fresh, empty sub-database and the
//! problem's is parked in the `OrderContext`. `transitivity` and `reflexivity`
//! run inside that sub-database too. A rule whose effect is a claim about the
//! problem — a verdict, the objective, core membership, the loaded order, a
//! logged solution — has nothing to say against a database that is not the
//! problem's, and letting one run there is not a harmless no-op:
//!
//! * `sol` validates its assignment by iterating the *installed* database, so
//!   against the empty one every assignment passes vacuously and sets
//!   `best_valid_objective_value` — the whole of the evidence a `conclusion
//!   SAT` without a hint rests on. An unsatisfiable formula verified as
//!   satisfiable.
//! * `strengthening_to_core on` moved that empty database to core while
//!   setting the *global* flag that tells every later `red` it need no longer
//!   preserve the derived set, leaving the outer derived set unmoved and the
//!   mode's promise unkept. That is defect 19's payload, reached through
//!   placement instead of set membership.
//!
//! The version-3 parser rules this out with its `Scope` ladder. The version-2
//! parser has one scope flag, `inside_order_definition`, and it covers only the
//! `def ... end` block — everywhere else in an order definition it dispatches
//! lines through one flat match, so any rule at all could be written there. The
//! fix restates the grammar's placement rule in the *checker*
//! (`veripb_checker::rules::OrderDefinitionPlacement`), where it holds for
//! every front end.
//!
//! Three things have to hold together, and there is a test for each:
//!
//! 1. the version-3 grammar refuses each of these rules inside an order
//!    definition — the older defence, pinned here because the placement table
//!    is derived from it;
//! 2. the checker refuses each rule the version-2 dialect can express there —
//!    the new gate, which is what defect 23 needed;
//! 3. the probe table is the grammar's own list, so a rule added at top-level
//!    scope later cannot escape both.
//!
//! Point 3 is the half that `CheckableRule::order_definition_placement` cannot
//! supply on its own. Its `match` is exhaustive over `CheckableRule`, so a new
//! rule *variant* must declare a placement or fail to compile — but a variant
//! that declares the *wrong* placement compiles fine, and that is the mistake
//! this file is here to catch.
//!
//! # What a mis-declaration sweep still survives, and why
//!
//! The measure of this suite is the mutation sweep: each of the table's 46
//! rules moved to each of its 3 wrong placements, 138 mutations, the suite
//! run against every one. The survivors are exactly the mis-declarations **no
//! input from either front end can observe**, and each class is named here so
//! that a future reader can tell a measured limit from a forgotten probe:
//!
//! * `PreservedAddRule`, `PreservedRemoveRule`, `PreservedEqualsRule`,
//!   `ObjectiveValueRule` → `Specification`/`Always` (8): the version-2 lexer
//!   cannot spell them ([`RefusedBy::VersionTwoLexer`]) and the version-3
//!   grammar carries them only to the top level, where those placements and
//!   `Never` all admit. Their `Structure` direction *is* observable and
//!   [`the_version_2_lexer_gaps_are_pinned_at_the_version_3_top_level`]
//!   catches it.
//! * `ScopeRule` → anything (3): the gate never consults its entry. The
//!   version-2 lexer has no token; the version-3 grammar admits `scope` only
//!   inside a subproof (`check_scope_usage`), and subproof contexts are
//!   filtered by `is_subproof_friendly`, not by the placement table.
//! * `UnimplementedRule` → `Never`/`Specification` (2): reachable only at the
//!   version-3 top level (`eord_def` and friends), where both admit; its
//!   `compute` then refuses as unimplemented. The observable `Structure`
//!   direction is caught by
//!   [`an_unimplemented_rule_is_refused_as_unimplemented_not_as_misplaced`].
//! * `ProofByContradiction` → `Always` (1): differs from `Specification` only
//!   in the non-`spec` order contexts, which neither dialect can reach with a
//!   `pbc`. The observable directions are caught by
//!   [`a_version_3_specification_admits_pbc`].
//! * `OrderDefConstraintRule` → `Always` (1): the rule exists only inside a
//!   `def ... end` block — the version-2 parser constructs it nowhere else and
//!   the version-3 grammar parses `def` bodies structurally — and there
//!   `Structure` and `Always` agree.
//!
//! Fifteen survivors, every one argued unobservable rather than merely
//! unprobed. If a probe for one of them ever becomes expressible — a new
//! token, a new scope — the sweep count is the tripwire.

use std::io::Write;
use std::path::PathBuf;
use std::process::Command;

/// What refuses a probe's version-2 spelling.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum RefusedBy {
    /// The line reaches `ForwardsChecker::execute_rule`, which refuses it on
    /// its `OrderDefinitionPlacement`. This is the case the new gate exists
    /// for, and the only one that tests it.
    Placement,
    /// The version-2 lexer has no token for this rule, so the line cannot be
    /// written in a version-2 proof at all: it lexes as some shorter rule
    /// (`obji` as `o`, `preserved_add` as `p`, `epreserved` as `e`) and is
    /// refused on *that* rule's terms, which says nothing about this one.
    ///
    /// The probe still runs — it must not verify — and the rule itself is
    /// covered by the version-3 half, which names it in the refusal. If the
    /// lexer ever gains the token, nothing here breaks; the version-2 half
    /// simply starts testing a rule it previously could not reach.
    ///
    /// The consequence, stated rather than left to be discovered: for these
    /// four rules the *checker's* table entry is untested by the version-2
    /// half, because no version-2 input reaches the gate carrying them. The
    /// version-3 grammar can carry them, but only at the top level — inside
    /// an order its `Scope` ladder refuses them before the checker runs — and
    /// at the top level `Never`, `Specification` and `Always` are
    /// indistinguishable (all admit).
    /// [`the_version_2_lexer_gaps_are_pinned_at_the_version_3_top_level`]
    /// therefore catches the `Structure` mis-declaration of
    /// `PreservedAddRule`, `PreservedRemoveRule`, `PreservedEqualsRule` and
    /// `ObjectiveValueRule`; their `Specification` and `Always`
    /// mis-declarations survive — measured, not assumed — because no input
    /// from either front end can observe them. That is the honest limit of
    /// the two dialects together, not an oversight to be papered over; the
    /// module notes name every such survivor.
    VersionTwoLexer,
}

struct Probe {
    /// The rule's name in the version-3 grammar's dispatch table. Cross-checked
    /// against `veripb-parser` by
    /// [`the_probe_table_is_the_grammars_own_top_level_list`].
    name: &'static str,
    /// The rule as the version-2 dialect spells it, with arguments the
    /// version-2 parser accepts. Several spellings differ from the version-3
    /// name — `wiplvl` is `w`, `setlvl` is `#`, `def_order` is also
    /// `pre_order` — and the version-2 argument grammar differs too
    /// (`obju new ...`).
    v2_line: &'static str,
    refused_by: RefusedBy,
    /// The `CheckableRule` variant the placement gate must *name* when it
    /// refuses this probe. Empty for a rule the version-2 lexer cannot express,
    /// which never reaches the gate.
    ///
    /// Requiring the name is what makes the refusal *this* probe's. Checking
    /// only that some placement refusal appeared anywhere on stderr is
    /// satisfied when the probe's own line is **accepted** and the gate then
    /// refuses the *next* line — which is precisely what a mis-declared
    /// placement produces. Measured: moving `DefineOrderRule` from `Never` to
    /// `Specification` let a `pre_order` open a nested order definition inside
    /// a version-2 `spec` block, and the refusal of the following line kept
    /// every test in this file green, and the whole workspace suite with it.
    blamed: &'static str,
    /// The line opens a block that its own `end` must close, so the top-level
    /// control has to complete it; left open, the *footer* trips the gate and
    /// the control would blame the wrong line.
    opens_a_block: bool,
}

const fn probe(
    name: &'static str,
    v2_line: &'static str,
    refused_by: RefusedBy,
    blamed: &'static str,
) -> Probe {
    Probe {
        name,
        v2_line,
        refused_by,
        blamed,
        opens_a_block: false,
    }
}

/// One probe per rule the version-3 grammar places at `Scope::TopLevel`.
const PROBES: &[Probe] = &[
    probe("core", "core id -1", RefusedBy::Placement, "MoveToCoreRule"),
    Probe {
        opens_a_block: true,
        ..probe(
            "def_order",
            "pre_order inner",
            RefusedBy::Placement,
            "DefineOrderRule",
        )
    },
    probe("del", "del id 1", RefusedBy::Placement, "Deletion"),
    probe("delc", "delc 1", RefusedBy::Placement, "Deletion"),
    probe("deld", "deld 1", RefusedBy::Placement, "Deletion"),
    probe(
        "dom",
        "dom 1 x1 >= 1 ; x1 -> 1 ;",
        RefusedBy::Placement,
        "DominanceBasedStrengtheningRule",
    ),
    probe(
        "epreserved",
        "epreserved x1",
        RefusedBy::VersionTwoLexer,
        "",
    ),
    probe(
        "load_order",
        "load_order simple x1",
        RefusedBy::Placement,
        "LoadOrder",
    ),
    probe("obji", "obji 1 x1 >= 1 ;", RefusedBy::VersionTwoLexer, ""),
    probe(
        "obju",
        "obju new 1 x1 ;",
        RefusedBy::Placement,
        "ObjectiveUpdateRule",
    ),
    probe(
        "preserved_add",
        "preserved_add x1",
        RefusedBy::VersionTwoLexer,
        "",
    ),
    probe(
        "preserved_rm",
        "preserved_rm x1",
        RefusedBy::VersionTwoLexer,
        "",
    ),
    probe("setlvl", "# 1", RefusedBy::Placement, "SetLevelRule"),
    probe("sol", "sol x1 x2", RefusedBy::Placement, "Solution"),
    probe("soli", "soli x1 x2", RefusedBy::Placement, "Solution"),
    probe("solx", "solx x1 x2", RefusedBy::Placement, "Solution"),
    probe(
        "strengthening_to_core",
        "strengthening_to_core on",
        RefusedBy::Placement,
        "StrengtheningToCoreRule",
    ),
    probe("wiplvl", "w 1", RefusedBy::Placement, "Deletion"),
];

/// Satisfiable, with an objective, so that no probe is refused merely because
/// the formula lacks something the rule needs.
const FORMULA: &str = "\
* #variable= 2 #constraint= 2
min: 1 x1 1 x2 ;
1 x1 1 x2 >= 1 ;
1 x1 1 ~x2 >= 1 ;
";

/// A complete, valid version-2 `pre_order` body, minus its opening line.
const ORDER_BODY: &str = "\
    vars
        left u1
        right v1
        aux
    end
    def
        -1 u1 1 v1 >= 0 ;
    end
    transitivity
        vars
            fresh_right w1
        end
        proof
            proofgoal #1
                p -2 -3 + -1 +
            end -1
        end
    end
end
";

/// The same order with an auxiliary variable and a `spec` block, so that a
/// probe can be placed *inside the specification* as well as in the order
/// body. `@PROBE@` marks where the line goes.
///
/// Without this the suite could not tell `OrderDefinitionPlacement::Never`
/// from `Specification`: every probe sat in the `pre_order` body, where both
/// placements are refused and with the same message. A one-token
/// mis-declaration moving `Solution` from `Never` to `Specification` left all
/// five tests green while a `sol` inside a version-2 `spec` block verified the
/// unsatisfiable `1 x1 >= 1 ; 1 ~x1 >= 1 ;` as `s VERIFIED SATISFIABLE` —
/// wrong verdict 23, restored, undetected. The distinction the table draws is
/// only worth drawing if a test can see it.
const ORDER_BODY_WITH_SPEC: &str = "\
    vars
        left u1
        right v1
        aux a1
    end
    spec
@PROBE@
        red 1 ~a1 1 u1 1 ~v1 >= 1 ; a1 -> 0 ;
    end
    def
        -1 u1 1 v1 >= 0 ;
    end
    transitivity
        vars
            fresh_right w1
            fresh_aux_1 b1
            fresh_aux_2 b2
        end
        proof
            proofgoal #1
                p -2 -3 + -1 +
            end -1
        end
    end
end
";

const FOOTER: &str = "\
output NONE
conclusion NONE
end pseudo-Boolean proof
";

/// The probe's line inside the order definition's body, where it must be
/// refused.
fn inside_order(line: &str) -> String {
    format!(
        "pseudo-Boolean proof version 2.0\nf 2\npre_order simple\n    {line}\n{ORDER_BODY}{FOOTER}"
    )
}

/// The probe's line inside the order's `spec` block, where it must also be
/// refused — and where the two non-`Always` placements differ.
fn inside_spec(line: &str) -> String {
    let body = ORDER_BODY_WITH_SPEC.replace("@PROBE@", &format!("        {line}"));
    format!("pseudo-Boolean proof version 2.0\nf 2\npre_order simple\n{body}{FOOTER}")
}

/// The same order with nothing injected: the control that keeps [`inside_spec`]
/// honest. If this stopped verifying, every `inside_spec` probe would be
/// refused for a reason that has nothing to do with the probe, and the test
/// above it would pass for nothing.
fn spec_without_a_probe() -> String {
    let body = ORDER_BODY_WITH_SPEC.replace("@PROBE@\n", "");
    format!("pseudo-Boolean proof version 2.0\nf 2\npre_order simple\n{body}{FOOTER}")
}

/// The same line after the order definition has closed, where the placement
/// gate must not fire.
fn at_top_level(probe: &Probe) -> String {
    let line = if probe.opens_a_block {
        format!("{}\n{ORDER_BODY}", probe.v2_line)
    } else {
        format!("{}\n", probe.v2_line)
    };
    format!("pseudo-Boolean proof version 2.0\nf 2\npre_order simple\n{ORDER_BODY}{line}{FOOTER}")
}

/// The rule inside a version-3 `spec` block. The refusal comes from the parser
/// before the rest of the proof is read, which is why the order needs no `def`
/// or `transitivity` here.
fn inside_version_three_spec(name: &str) -> String {
    format!(
        "pseudo-Boolean proof version 3.0\n\
         f 2;\n\
         def_order simple\n\
         \x20 vars\n\
         \x20   left u1 ;\n\
         \x20   right v1 ;\n\
         \x20   aux ;\n\
         \x20 end vars;\n\
         \x20 spec\n\
         \x20   {name};\n\
         \x20 end spec;\n\
         end def_order;\n\
         output NONE;\n\
         conclusion NONE;\n\
         end pseudo-Boolean proof\n"
    )
}

struct Run {
    stdout: String,
    stderr: String,
    code: Option<i32>,
}

impl Run {
    fn context(&self) -> String {
        format!(
            "--- stdout ---\n{}--- stderr ---\n{}",
            self.stdout, self.stderr
        )
    }

    fn verdicts(&self) -> Vec<&str> {
        self.stdout
            .lines()
            .filter(|line| line.starts_with("s "))
            .collect()
    }

    /// The checker's placement gate refused it. Deliberately distinct from the
    /// parser's wording (`not allowed in a ... context`), so the two halves of
    /// this file cannot be satisfied by the same mechanism.
    fn blamed_placement(&self) -> bool {
        self.stderr.contains("is not allowed in the")
    }

    /// The placement gate refused, blaming *this* rule by name.
    ///
    /// See [`Probe::blamed`] for why the name is load-bearing: without it the
    /// check is satisfied by the gate refusing some *later* line, which is the
    /// signature of the mis-declaration it is supposed to catch.
    fn blamed_rule(&self, rule: &str) -> bool {
        self.stderr
            .contains(&format!("The rule `{rule}` is not allowed in the"))
    }

    /// The proof was refused, without falling over.
    fn assert_refused(&self, what: &str) {
        assert!(
            self.verdicts().is_empty(),
            "{what} produced a verdict:\n{}",
            self.context()
        );
        assert!(
            !self.stderr.contains("INTERNAL ERROR in VeriPB"),
            "{what} crashed instead of being refused:\n{}",
            self.context()
        );
        assert_eq!(
            self.code,
            Some(1),
            "{what} must exit with the ordinary checking-error status, not crash \
             and not exit 0:\n{}",
            self.context()
        );
    }
}

fn run(formula: &str, proof: &str) -> Run {
    let dir = tempfile::tempdir().expect("failed to create temporary directory");
    let write = |name: &str, contents: &str| -> PathBuf {
        let path = dir.path().join(name);
        let mut file = std::fs::File::create(&path).expect("failed to create temporary file");
        file.write_all(contents.as_bytes())
            .expect("failed to write test input");
        path
    };
    let formula = write("f.opb", formula);
    let proof = write("p.pbp", proof);
    let output = Command::new(env!("CARGO_BIN_EXE_veripb"))
        .arg("--opb")
        .arg(&formula)
        .arg(&proof)
        .output()
        .expect("failed to run veripb binary");
    Run {
        stdout: String::from_utf8_lossy(&output.stdout).into_owned(),
        stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
        code: output.status.code(),
    }
}

/// The older defence: the version-3 grammar refuses each of these rules inside
/// an order definition, and names it while doing so.
///
/// Naming matters. It is what makes this a test of eighteen rules rather than
/// of one error path — the message quotes the rule the parser actually read, so
/// a probe whose spelling silently became a different rule fails here instead
/// of passing quietly.
#[test]
fn the_version_3_grammar_refuses_every_top_level_rule_inside_an_order_definition() {
    for probe in PROBES {
        let result = run(FORMULA, &inside_version_three_spec(probe.name));
        result.assert_refused(&format!("`{}` inside a version-3 `spec` block", probe.name));
        assert!(
            result.stderr.contains(&format!(
                "The rule `{}` is not allowed in a specification context",
                probe.name
            )),
            "`{}` inside a version-3 `spec` block was refused, but not by the \
             grammar's scope check — so this probe is no longer testing the rule \
             it names:\n{}",
            probe.name,
            result.context()
        );
    }
}

/// The new gate: the checker refuses each rule the version-2 dialect can
/// express inside an order definition, whatever the parser did or did not do.
/// A named position to inject a probe into: where it is, and how to build the
/// proof that puts it there.
type Template = (&'static str, fn(&str) -> String);

#[test]
fn the_checker_refuses_every_top_level_rule_inside_a_version_2_order_definition() {
    // Two placements, because one could not tell `Never` from `Specification`.
    // The order body refuses both; only the `spec` block separates them, and it
    // is the `spec` block that a mis-declared rule would escape through.
    let templates: [Template; 2] = [
        ("order definition", inside_order as fn(&str) -> String),
        ("`spec` block", inside_spec as fn(&str) -> String),
    ];
    for (where_, build) in templates {
        for probe in PROBES {
            let result = run(FORMULA, &build(probe.v2_line));
            let what = format!("`{}` inside a version-2 {where_}", probe.name);
            result.assert_refused(&what);
            if probe.refused_by == RefusedBy::Placement {
                assert!(
                    result.blamed_rule(probe.blamed),
                    "{what} was refused, but the placement gate did not name \
                     `{}` — so either the probe no longer tests what it is here \
                     to test, or its own line was accepted and a *later* line \
                     was refused, which is the signature of a mis-declared \
                     placement:\n{}",
                    probe.blamed,
                    result.context()
                );
            }
        }
    }
}

/// The derivation rules are refused in the order *body*, where only the order's
/// own structural keywords belong.
///
/// Every probe above is a rule the table calls `Never`, so nothing exercised
/// the boundary between `Specification` and `Always`: relaxing a
/// `Specification` rule to `Always` left the whole suite green, because no
/// probe ever put one of them anywhere a `Specification` rule is refused. The
/// `spec` block admits them (pinned by
/// `a_specification_block_still_admits_its_own_rules`); the surrounding order
/// body does not.
///
/// The table below is every `Specification`-placed rule the version-2 lexer
/// can spell except `pbc`: the version-2 lexer has no token for it (a
/// `ProofByContradiction` only arises from the version-3 grammar's `pbc`,
/// which its `Scope` ladder confines to specifications and subproofs), so no
/// version-2 input reaches the gate carrying one and its table entry is
/// untestable from here — the same honest limit as
/// [`RefusedBy::VersionTwoLexer`], stated rather than papered over.
#[test]
fn the_order_body_refuses_the_rules_that_belong_in_a_spec_block() {
    // (version-2 spelling, `CheckableRule` variant the gate must name)
    const DERIVATIONS: &[(&str, &str)] = &[
        ("p 1 1 +", "PolRule"),
        ("u >= 0 ;", "RUPRule"),
        (
            "red 1 y1 >= 1 ; y1 -> 1 ;",
            "RedundanceBasedStrengtheningRule",
        ),
        ("e 1 x1 >= 1 ; 1", "EqualsRule"),
        ("i 1 x1 >= 1 ; 1", "ImpliesRule"),
        ("a 1 x1 1 ~x1 >= 1 ;", "AssertionRule"),
        ("f 2", "FormulaCheck"),
        ("is_deleted 1 x1 >= 1 ;", "IsDeletedCheck"),
        ("eobj 1 x1 ;", "EqualsObjectiveRule"),
        ("fail", "FailRule"),
    ];
    for (line, blamed) in DERIVATIONS {
        let result = run(FORMULA, &inside_order(line));
        let what = format!("`{line}` in a version-2 order body");
        result.assert_refused(&what);
        assert!(
            result.blamed_rule(blamed),
            "{what} was refused, but the placement gate did not name `{blamed}`. \
             A derivation rule belongs in a `spec` block and nowhere else in an \
             order definition; if this stops holding, `Specification` and \
             `Always` have become indistinguishable:\n{}",
            result.context()
        );
    }
}

/// The control for the `spec` half above.
///
/// Every `inside_spec` probe would be refused for free if the surrounding order
/// did not verify on its own, and the test above would then be measuring
/// nothing. It also pins the other direction of the placement table: a `spec`
/// block still admits the rules it is written with, so tightening every rule to
/// `Never` would fail here rather than look like a stronger checker.
///
/// The loop covers **every** `Specification`-placed rule the version-2 lexer
/// can spell, not just the three the specification grammar is usually written
/// with. It used to probe only `p`, `u` and `a`, and the gap was measured, not
/// hypothetical: `EqualsRule → Never` refused an `e` inside a `spec` block
/// that the shipped binary admits, with this whole suite green. `red` is not
/// in the loop because it is the control's own `spec` line — `Never` or
/// `Structure` for `red` makes `spec_without_a_probe` stop verifying and the
/// assertion above fail. `pbc` is not in the loop because the version-2 lexer
/// has no token for it; its `Specification` entry is reachable only through
/// the version-3 grammar and untestable from this dialect-specific control —
/// the same honest limit as [`RefusedBy::VersionTwoLexer`].
///
/// Whether each injected rule then *succeeds* is deliberately not asserted:
/// `f 2` fails against the order's sub-database, `fail` fails by definition,
/// `eobj` has no objective to equal. The only claim is that *placement* does
/// not refuse them, which is exactly the line between `Specification` and
/// `Never`.
#[test]
fn a_specification_block_still_admits_its_own_rules() {
    let result = run(FORMULA, &spec_without_a_probe());
    assert_eq!(
        result.verdicts(),
        vec!["s VERIFIED NO CONCLUSION"],
        "the version-2 `spec` block this file injects probes into no longer \
         verifies on its own, so every `spec` probe is now passing for free:\n{}",
        result.context()
    );
    assert_eq!(result.code, Some(0));

    // The derivation rules the grammar puts at `Scope::Proofgoal` (plus the
    // checks `e`, `i`, `f`, `is_deleted`, `eobj`, `fail`, which it also
    // admits at every depth) are legal in a specification and must not be
    // refused by placement there.
    for line in [
        "p 1 1 +",
        "u >= 0 ;",
        "a 1 u1 1 ~u1 >= 1 ;",
        "e 1 u1 >= 1 ; 1",
        "i 1 u1 >= 1 ; 1",
        "f 2",
        "is_deleted 1 u1 >= 1 ;",
        "eobj 1 u1 ;",
        "fail",
    ] {
        let result = run(FORMULA, &inside_spec(line));
        assert!(
            !result.blamed_placement(),
            "`{line}` is legal inside a `spec` block, but the placement gate \
             refused it:\n{}",
            result.context()
        );
    }
}

/// The meta and footer rules are refused inside an order definition, and the
/// gate names each one while refusing it.
///
/// These rules have no entry in [`PROBES`] because the version-3 grammar does
/// not dispatch them at `Scope::TopLevel` — the header, the footer
/// (`output`/`conclusion`/`end pseudo-Boolean proof`) and `proofgoal` are
/// parsed structurally there — so the table cross-check cannot demand them.
/// The version-2 dialect has a token for every one of them and dispatches
/// through the same flat match as everything else, so each *can* be written
/// inside a `pre_order` and each carries a `Never` entry in the placement
/// table that nothing else here exercised.
///
/// A second line of defence exists and is not enough: mis-declaring
/// `Conclusion` as `Always` lets a `conclusion` run inside the order and the
/// *footer-ordering* check then refuses the proof anyway — measured, and it
/// kept a blame-free version of this probe green. That refusal does not name
/// the rule and does not fire at the probe's line, which is precisely the
/// signature [`Probe::blamed`] exists to catch, so the assertions here demand
/// the placement gate's own message with the rule's own name.
#[test]
fn the_meta_and_footer_rules_are_refused_inside_an_order_definition() {
    // (version-2 spelling, `CheckableRule` variant the gate must name)
    const META_FOOTER: &[(&str, &str)] = &[
        ("conclusion NONE", "Conclusion"),
        ("end pseudo-Boolean proof", "EndProof"),
        ("pseudo-Boolean proof version 2.0", "HeaderRule"),
        ("output NONE", "OutputRule"),
        ("proofgoal #1", "Proofgoal"),
    ];
    let templates: [Template; 2] = [
        ("order definition", inside_order as fn(&str) -> String),
        ("`spec` block", inside_spec as fn(&str) -> String),
    ];
    for (where_, build) in templates {
        for (line, blamed) in META_FOOTER {
            let result = run(FORMULA, &build(line));
            let what = format!("`{line}` inside a version-2 {where_}");
            result.assert_refused(&what);
            assert!(
                result.blamed_rule(blamed),
                "{what} was refused, but the placement gate did not name \
                 `{blamed}` — so either another mechanism (footer ordering, the \
                 parser) got there first, which says nothing about this rule's \
                 placement entry, or the probe's own line was accepted and a \
                 later line refused, the signature of a mis-declared \
                 placement:\n{}",
                result.context()
            );
        }
    }
}

/// A comment is admitted everywhere an order definition can put one.
///
/// `Comment` is the placement table's `Always`, and this is the only test
/// that can see that: comments never appear in the refusal direction, so
/// every other probe in this file is satisfied whether comments are placed
/// correctly or not. Each comment below sits in a different placement class —
/// top level, order body, `spec` block, `def` block — and the proof must
/// still verify, so tightening `Comment` to `Never` (refused in all four
/// order subcontexts), `Specification` (refused in the order body) or
/// `Structure` (refused at the top level and in the `spec` block) each
/// refuses at least one of them.
#[test]
fn comments_are_admitted_everywhere_an_order_definition_opens() {
    const PROOF: &str = "\
pseudo-Boolean proof version 2.0
* a comment at the top level
f 2
pre_order simple
    * a comment in the order body
    vars
        left u1
        right v1
        aux a1
    end
    spec
        * a comment in the spec block
        red 1 ~a1 1 u1 1 ~v1 >= 1 ; a1 -> 0 ;
    end
    def
        * a comment in the def block
        -1 u1 1 v1 >= 0 ;
    end
    transitivity
        vars
            fresh_right w1
            fresh_aux_1 b1
            fresh_aux_2 b2
        end
        proof
            proofgoal #1
                p -2 -3 + -1 +
            end -1
        end
    end
end
output NONE
conclusion NONE
end pseudo-Boolean proof
";
    let result = run(FORMULA, PROOF);
    assert_eq!(
        result.verdicts(),
        vec!["s VERIFIED NO CONCLUSION"],
        "a version-2 proof with comments in every order placement stopped \
         verifying — a comment is being refused somewhere a comment must be \
         legal:\n{}",
        result.context()
    );
    assert_eq!(result.code, Some(0));
}

/// `reflexivity` is a structural keyword of the order body, and only of the
/// order body — the one `Structure` rule no other test in the workspace's
/// placement suite exercised in both directions.
///
/// Three claims, one per direction a mis-declaration could take it:
///
/// * a valid order **with** a reflexivity block still verifies, so
///   `reflexivity` cannot be quietly tightened out of the body it belongs in
///   (`Never`, or `Specification`, which refuses it everywhere but a `spec`
///   block);
/// * inside a `spec` block it is refused, and the gate names it — under
///   `Always` the gate would admit it and whatever refused it next would not
///   carry the name;
/// * at the top level it is refused, and the gate names it — the
///   `(Structure, None)` arm of `permits`, which no other probe reaches,
///   because every [`PROBES`] entry is a top-level rule asserting the
///   *absence* of a placement refusal there.
#[test]
fn reflexivity_is_a_structural_keyword_confined_to_the_order_body() {
    const ORDER_BODY_WITH_REFLEXIVITY: &str = "\
    vars
        left u1
        right v1
        aux
    end
    def
        -1 u1 1 v1 >= 0 ;
    end
    transitivity
        vars
            fresh_right w1
        end
        proof
            proofgoal #1
                p -2 -3 + -1 +
            end -1
        end
    end
    reflexivity
        proof
            proofgoal #1
                p -1
            end -1
        end
    end
end
";
    let proof = format!(
        "pseudo-Boolean proof version 2.0\nf 2\npre_order simple\n\
         {ORDER_BODY_WITH_REFLEXIVITY}{FOOTER}"
    );
    let result = run(FORMULA, &proof);
    assert_eq!(
        result.verdicts(),
        vec!["s VERIFIED NO CONCLUSION"],
        "a valid version-2 order definition with a reflexivity block stopped \
         verifying:\n{}",
        result.context()
    );
    assert_eq!(result.code, Some(0));

    let result = run(FORMULA, &inside_spec("reflexivity"));
    result.assert_refused("`reflexivity` inside a version-2 `spec` block");
    assert!(
        result.blamed_rule("OrderReflexivityRule"),
        "`reflexivity` inside a `spec` block was refused, but the placement \
         gate did not name `OrderReflexivityRule`:\n{}",
        result.context()
    );

    let proof = format!(
        "pseudo-Boolean proof version 2.0\nf 2\npre_order simple\n{ORDER_BODY}\
         reflexivity\n{FOOTER}"
    );
    let result = run(FORMULA, &proof);
    result.assert_refused("`reflexivity` at the top level");
    assert!(
        result.blamed_rule("OrderReflexivityRule"),
        "`reflexivity` at the top level was refused, but the placement gate \
         did not name `OrderReflexivityRule`:\n{}",
        result.context()
    );
}

/// Every other structural keyword is likewise refused at the top level, by
/// the gate, by name.
///
/// This is the `(Structure, None)` arm of `permits`, and before this test no
/// probe reached it: every [`PROBES`] entry asserts the *absence* of a
/// placement refusal at the top level, and the valid-order controls only ever
/// put these keywords where they belong. Relaxing any one of them from
/// `Structure` to `Always` therefore survived the whole suite — eleven
/// measured survivors of the mutation sweep — because the second defence
/// (each keyword's own `compute` refusing to run without an open order,
/// `VarsNotAllowedHere` and friends) also refuses the proof, just without the
/// gate's message. The by-name assertion is what tells the two apart.
///
/// `OrderDefConstraintRule` is the one `Structure` rule not here: the
/// version-2 parser only constructs it *inside* `def ... end`, where
/// `Structure` and `Always` agree, and the version-3 grammar parses `def`
/// constraints structurally — no front end can carry one to the gate
/// anywhere the two placements differ, so its relaxation is an unobservable
/// survivor, named in the module notes.
#[test]
fn the_structural_keywords_are_refused_at_the_top_level() {
    // (version-2 spelling, `CheckableRule` variant the gate must name)
    const KEYWORDS: &[(&str, &str)] = &[
        ("vars", "OrderVariablesRule"),
        ("left u1", "OrderLeftVariablesRule"),
        ("right v1", "OrderRightVariablesRule"),
        ("aux", "OrderAuxVariablesRule"),
        ("def", "OrderDefRule"),
        ("transitivity", "OrderTransitivityRule"),
        ("proof", "OrderProofRule"),
        ("fresh_right w1", "OrderFreshRightVariablesRule"),
        ("fresh_aux_1 b1", "OrderFreshAux1Rule"),
        ("fresh_aux_2 b2", "OrderFreshAux2Rule"),
        ("spec", "OrderSpecificationRule"),
    ];
    for (line, blamed) in KEYWORDS {
        let proof = format!(
            "pseudo-Boolean proof version 2.0\nf 2\npre_order simple\n{ORDER_BODY}\
             {line}\n{FOOTER}"
        );
        let result = run(FORMULA, &proof);
        let what = format!("`{line}` at the top level");
        result.assert_refused(&what);
        assert!(
            result.blamed_rule(blamed),
            "{what} was refused, but the placement gate did not name \
             `{blamed}` — a structural keyword outside any order must be the \
             gate's refusal, not its own rule's fallback error:\n{}",
            result.context()
        );
    }
}

/// The one `Specification` rule the version-2 lexer cannot spell, pinned from
/// the version-3 side: a `spec` block admits `pbc`.
///
/// The order is `def_order_spec_autoproven_reflexivity` from the corpus with
/// a `pbc` line ahead of its `red`: `1 u1 1 ~u1 >= 1` is a tautology, so its
/// negation is contradicting and the contradiction is auto-proven. The proof
/// *verifies*, so tightening `ProofByContradiction` to `Never` or `Structure`
/// — both of which refuse it inside a specification — fails here. `Always`
/// differs from `Specification` only in the non-`spec` order contexts, which
/// no front end can reach with a `pbc` (the version-2 lexer has no token, the
/// version-3 `Scope` ladder refuses it there before the checker); that one
/// direction is an unobservable survivor, named in the module notes.
#[test]
fn a_version_3_specification_admits_pbc() {
    const PROOF: &str = "\
pseudo-Boolean proof version 3.0
f 2;
def_order simple
  vars
    left u1;
    right v1;
    aux $a1;
  end vars;
  spec
    pbc 1 u1 1 ~u1 >= 1;
    red 1 ~$a1 >= 1 : $a1 -> 0;
  end spec;
  def
    -1 u1 1 v1 >= 0;
  end def;
  transitivity
    vars
      fresh_right w1;
      fresh_aux_1 $b1;
      fresh_aux_2 $c1;
    end vars;
    proof
      proofgoal #1
        pol -2 -3 + -1 +;
      qed : -1;
    qed;
  end transitivity;
end def_order;
load_order simple x1;
pol 1 2 +;
load_order;
output NONE;
conclusion NONE;
end pseudo-Boolean proof;
";
    let result = run(FORMULA, PROOF);
    assert_eq!(
        result.verdicts(),
        vec!["s VERIFIED NO CONCLUSION"],
        "a version-3 `spec` block with a `pbc` derivation stopped verifying — \
         `ProofByContradiction` is being refused somewhere the grammar admits \
         it:\n{}",
        result.context()
    );
    assert_eq!(result.code, Some(0));
}

/// A rule the checker has not implemented is reported as *unimplemented*, not
/// as misplaced.
///
/// `UnimplementedRule` reaches the gate only at the version-3 top level
/// (`eord_def`, `eord_loaded`, and friends), and its `compute`
/// unconditionally errors with "has not been implemented". At the top level
/// every placement except `Structure` admits it, so `Structure` is the one
/// mis-declaration with an observable effect: the refusal would become the
/// gate's message instead of the honest one. The other two directions are
/// unobservable survivors, named in the module notes.
#[test]
fn an_unimplemented_rule_is_refused_as_unimplemented_not_as_misplaced() {
    const PROOF: &str = "\
pseudo-Boolean proof version 3.0
f 2;
eord_def simple
  vars
    left u1;
    right v1;
  end vars;
  def
    -1 u1 1 v1 >= 0;
  end def;
end eord_def;
output NONE;
conclusion NONE;
end pseudo-Boolean proof;
";
    let result = run(FORMULA, PROOF);
    result.assert_refused("`eord_def`, an unimplemented version-3 rule");
    assert!(
        result.stderr.contains("has not been implemented"),
        "`eord_def` must be refused as unimplemented:\n{}",
        result.context()
    );
    assert!(
        !result.blamed_placement(),
        "`eord_def` was refused by the placement gate instead of by its own \
         unimplemented error — `UnimplementedRule` has stopped being placeable \
         at the top level:\n{}",
        result.context()
    );
}

/// The four rules the version-2 lexer cannot spell, pinned from the version-3
/// side: at the version-3 top level none of them is refused by placement.
///
/// This is the strongest claim any input can make about their table entries.
/// [`RefusedBy::VersionTwoLexer`] documents why the version-2 half cannot
/// carry them to the gate; the version-3 grammar can, but only at the top
/// level — inside an order its `Scope` ladder refuses them before the checker
/// runs. At the top level `Never`, `Specification` and `Always` all admit, so
/// only the `Structure` mis-declaration is observable, and this test is what
/// catches it. Whether each rule then succeeds is deliberately not asserted
/// (`preserved_add` fails against this formula's absent preserved set;
/// `obji 77` happens to verify); the claim is only that placement stays out
/// of it.
#[test]
fn the_version_2_lexer_gaps_are_pinned_at_the_version_3_top_level() {
    for line in [
        "preserved_add x1 : 1 x2 >= 1;",
        "preserved_rm x1 : 1 x2 >= 1;",
        "epreserved x1;",
        "obji 77;",
    ] {
        let proof = format!(
            "pseudo-Boolean proof version 3.0\nf 2;\n{line}\noutput NONE;\n\
             conclusion NONE;\nend pseudo-Boolean proof;\n"
        );
        let result = run(FORMULA, &proof);
        assert!(
            !result.blamed_placement(),
            "`{line}` at the version-3 top level was refused by the placement \
             gate — the top level admits every non-structural rule:\n{}",
            result.context()
        );
    }
}

/// The control that makes the refusal tests above mean something.
///
/// A gate that refused every rule everywhere would satisfy
/// `the_checker_refuses_every_top_level_rule_inside_a_version_2_order_definition`
/// completely. What distinguishes the fix from that is *placement*, so each
/// probe runs again after the order definition has closed, where the placement
/// error must not appear. Whether the rule then succeeds is beside the point
/// and deliberately not asserted — `del id 1` fails on its own terms on this
/// formula — which keeps this a check on the gate rather than a second copy of
/// the corpus.
#[test]
fn the_same_rules_are_not_refused_by_placement_at_the_top_level() {
    for probe in PROBES {
        let result = run(FORMULA, &at_top_level(probe));
        assert!(
            !result.blamed_placement(),
            "`{}` is refused by the placement gate even at the top level, so the \
             gate is over-rejecting rather than placing:\n{}",
            probe.name,
            result.context()
        );
    }
}

/// Order definitions still work.
///
/// The cheapest way to "fix" a placement defect is to refuse the construct
/// altogether, so the point of the construct is pinned here: a valid order is
/// defined, loaded, used and unloaded.
#[test]
fn a_valid_order_definition_still_verifies() {
    let proof = format!(
        "pseudo-Boolean proof version 2.0\nf 2\npre_order simple\n{ORDER_BODY}\
         load_order simple x1\nload_order\np 1 2 +\n{FOOTER}"
    );
    let result = run(FORMULA, &proof);
    assert_eq!(
        result.verdicts(),
        vec!["s VERIFIED NO CONCLUSION"],
        "a valid version-2 order definition stopped verifying:\n{}",
        result.context()
    );
    assert_eq!(result.code, Some(0));
}

/// The version-3 grammar's dispatch table, as the names it places at
/// `Scope::TopLevel`.
///
/// Read from source rather than copied, because a copy is what drifts. The
/// scraper handles both shapes the dispatch uses — the guard on the same line
/// as the name, and the guard wrapped onto the next — and a restructuring it
/// cannot read panics here rather than returning a short list that would make
/// the coverage check pass by finding nothing.
fn grammar_top_level_rules() -> Vec<String> {
    const PARSER: &str = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/veripb-parser/src/pbp_parser/parser.rs"
    );
    let source =
        std::fs::read_to_string(PARSER).unwrap_or_else(|e| panic!("cannot read {PARSER}: {e}"));

    /// The `"name"` a match arm opens with, if this line is such an arm.
    fn arm_name(line: &str) -> Option<&str> {
        let rest = line.trim_start().strip_prefix('"')?;
        let (name, _) = rest.split_once('"')?;
        let plausible = !name.is_empty()
            && name
                .chars()
                .all(|c| c.is_ascii_lowercase() || c.is_ascii_digit() || c == '_');
        plausible.then_some(name)
    }

    let lines: Vec<&str> = source.lines().collect();
    let mut found = Vec::new();
    for (index, line) in lines.iter().enumerate() {
        if !(line.contains("check_rule_usage(") && line.contains("Scope::TopLevel)")) {
            continue;
        }
        let name = arm_name(line).or_else(|| {
            lines[..index]
                .iter()
                .rev()
                .find(|previous| !previous.trim().is_empty())
                .and_then(|previous| arm_name(previous))
        });
        match name {
            Some(name) => found.push(name.to_string()),
            None => panic!(
                "found a `Scope::TopLevel` rule guard in parser.rs whose rule name this \
                 test cannot read:\n    {line}\nTeach the scraper the new shape rather \
                 than letting the coverage check go quiet."
            ),
        }
    }
    found.sort();
    found.dedup();
    found
}

/// The probe table and the grammar name the same rules, in both directions.
///
/// A missing probe is how defect 23 would recur: a rule reachable through the
/// version-2 dialect that nothing checks. A stale probe is the other half — it
/// means the grammar moved a rule and
/// `CheckableRule::order_definition_placement` may not have moved with it.
#[test]
fn the_probe_table_is_the_grammars_own_top_level_list() {
    let grammar = grammar_top_level_rules();
    assert!(
        !grammar.is_empty(),
        "read no top-level rules at all out of parser.rs — an empty grammar list \
         would make the comparison below vacuous"
    );

    let mut probed: Vec<String> = PROBES.iter().map(|p| p.name.to_string()).collect();
    probed.sort();
    let named = probed.len();
    probed.dedup();
    assert_eq!(named, probed.len(), "the probe table names a rule twice");

    let missing: Vec<&String> = grammar.iter().filter(|n| !probed.contains(n)).collect();
    let stale: Vec<&String> = probed.iter().filter(|n| !grammar.contains(n)).collect();
    assert!(
        missing.is_empty(),
        "the version-3 grammar places these rules at the top level but no probe \
         checks that an order definition refuses them: {missing:?}. Add a probe — a \
         top-level rule reached through the version-2 dialect is exactly how wrong \
         verdict 23 happened."
    );
    assert!(
        stale.is_empty(),
        "these probes name rules the version-3 grammar no longer places at the top \
         level: {stale:?}. Either the grammar moved them, in which case \
         `CheckableRule::order_definition_placement` must move too, or the probe \
         table is out of date."
    );
}
