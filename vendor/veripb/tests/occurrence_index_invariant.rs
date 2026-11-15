//! The occurrence index must not lose a live constraint.
//!
//! `Database` keeps three lazy indexes over the same `entries` vector, each with its own
//! high-water mark: `unique_constraints` (`next_unique_index_id`), `occurrences`
//! (`next_occurrences_index_id`) and the propagation engine. Each `update_*_index` pass walks
//! only from its own mark to `len()` and then sets the mark to `len()`, so a pass never revisits
//! an id below its mark.
//!
//! `occurrences` is what `Database::get_proofgoals` walks to find the constraints a `red`/`dom`
//! witness touches. A constraint missing from it produces no proof obligation, and a missing
//! obligation is not a checking error — it is a proof that verifies without the step that was
//! supposed to justify it. So the loss is silent by construction and shows up only as a wrong
//! verdict.
//!
//! `update_unique_index` merges a duplicate constraint into the first structurally equal one, and
//! removes the duplicate from `occurrences` when the occurrence index has already passed that id.
//! That removal is by *address*. If the two `Rc`s are the same allocation — which
//! `HashSet::get` on a structurally-keyed set can produce — the removal takes out the survivor,
//! for good, and nothing indexes it again.
//!
//! Reaching that needs the occurrence index to be ahead of the unique index, which is exactly
//! what `Database::var_occurs` (`ScopeRule::compute`'s freshness check on the order's auxiliary
//! variables) does: it calls `update_occurrences_index` with no regard for the unique index.
//! Measured on the shipped corpus, no `update_unique_index` call has ever run in that state, so
//! this is latent rather than live. These tests are what keeps it latent.

use std::rc::Rc;

use veripb_checker::prelude::*;
use veripb_formula::prelude::*;
use veripb_propagator::propagation_engine::PropagationEngine;

const X1: VarIdx = 1;

fn clause_on(var: VarIdx) -> PBConstraintEnum {
    Clause::from_lits(vec![Lit::from_var(var, false)]).into()
}

/// The database, its propagation engine and the constraint stored at id 1.
fn database_with_one_clause() -> (Database, PropagationEngine, Rc<DBConstraint>) {
    let mut database = Database::from_formula(vec![clause_on(X1)]);
    let mut engine = veripb_checker::utils::new_veripb_propagation_engine();
    database
        .update_unique_index(&mut engine)
        .expect("indexing a one-constraint database cannot fail");
    let constraint = database.entries[1]
        .clone()
        .expect("the formula's constraint is stored at id 1");
    (database, engine, constraint)
}

#[test]
fn merging_a_constraint_into_itself_never_silently_unindexes_it() {
    let (mut database, mut engine, constraint) = database_with_one_clause();

    // The same allocation stored a second time. `Database::add_constraint` takes an
    // `Rc<DBConstraint>` and does not care whether the database already holds it, and rules that
    // re-add a constraint they looked up do hand it back verbatim.
    database.add_constraint(Rc::clone(&constraint), true);

    // What `ScopeRule::compute` does before the unique index has caught up: it runs the
    // occurrence index to `len()`, leaving `next_occurrences_index_id` above
    // `next_unique_index_id`. This is the precondition for the removal below, and it is
    // reachable from a proof file.
    assert!(
        database.var_occurs(X1),
        "the clause on x1 is live, so the occurrence index must find it"
    );

    // Now the unique index catches up. Id 2 is a duplicate of id 1 — and, being the same `Rc`,
    // its own survivor.
    match database.update_unique_index(&mut engine) {
        // Refusing is the correct outcome: the merge cannot be completed without dropping a live
        // constraint out of the only index that finds proofgoals.
        Err(error) => assert!(
            error.to_string().contains("occurrence index"),
            "the refusal must say what it is protecting, got: {error}"
        ),
        // Succeeding is only correct if the constraint is still findable.
        Ok(()) => assert!(
            database.var_occurs(X1),
            "the clause on x1 is still live at id 1, but the occurrence index has lost it: \
             every red/dom proofgoal it should generate is now silently dropped"
        ),
    }
}

#[test]
fn merging_two_equal_constraints_keeps_the_survivor_indexed() {
    // The positive control. Two structurally equal but *distinct* allocations is the ordinary
    // duplicate merge — measured to happen 263 times across the corpus — and it must keep
    // working, with the survivor still in the occurrence index afterwards.
    let (mut database, mut engine, _constraint) = database_with_one_clause();

    let duplicate = Rc::new(DBConstraint {
        header: Default::default(),
        constraint: clause_on(X1),
    });
    database.add_constraint(duplicate, true);

    database
        .update_unique_index(&mut engine)
        .expect("merging two distinct but equal constraints must succeed");
    assert!(
        database.var_occurs(X1),
        "after an ordinary duplicate merge the survivor must still be in the occurrence index"
    );
}
