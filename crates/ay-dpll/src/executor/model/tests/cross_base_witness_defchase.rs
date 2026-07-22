// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #qfax-sf-defchase in the CROSS-BASE completed-cells witness resolver
//! (#qf-ax-cross-base-guard).
//!
//! `witness_cell_rec2` threads the asserted-definition map (`build_array_defs`)
//! through its recursion; before the wire-up it never consulted it, unlike the
//! single-base `witness_cell_rec`. Consequences (sound but incomplete — the
//! resolver bailed with `None`, skipping the witness):
//!   * a write VALUE that is a `Var` defined by a top-level asserted equality
//!     as a select over a base-rooted chain never unfolded;
//!   * a select's array chain interrupted by a defined array ALIAS never
//!     walked back to a base.
//! These tests pin the wired behavior: both shapes now resolve to the base
//! interp value exactly as `witness_cell_rec` would in the single-base case.
//! (Chasing is semantics-preserving: each hop is an asserted top-level
//! equality, so the unfolded term denotes the same cell value.)

use super::*;

fn int_array_sort() -> Sort {
    Sort::array(Sort::Int, Sort::Int)
}

/// Write value is a `Var` `e` with the asserted definition
/// `(= e (select B 0))`: previously the resolver saw a non-`App` write value,
/// fell through to generic evaluation (blind: the model assigns `e` nothing)
/// and bailed with `None`. With the def chase it unfolds `e`, recurses into
/// the `B`-rooted read and resolves against `B`'s interp.
#[test]
fn witness_cell_rec2_chases_write_value_alias() {
    let mut exec = Executor::new();
    let base_a = exec.ctx.terms.mk_var("A", int_array_sort());
    let base_b = exec.ctx.terms.mk_var("B", int_array_sort());
    let e = exec.ctx.terms.mk_var("e", Sort::Int);
    let zero = exec.ctx.terms.mk_int(BigInt::from(0));
    let seven = exec.ctx.terms.mk_int(BigInt::from(7));
    let sel_b0 = exec
        .ctx
        .terms
        .mk_app(Symbol::named("select"), vec![base_b, zero], Sort::Int);
    let def = exec.ctx.terms.mk_eq(e, sel_b0);
    exec.ctx.assertions.push(def);
    exec.last_model = Some(empty_model());

    let defs = exec.build_array_defs();
    assert_eq!(
        defs.get(&e),
        Some(&sel_b0),
        "build_array_defs must pick up the asserted (= e (select B 0))"
    );

    let la = |_: &str| -> Option<String> { None };
    let lb = |at: &str| -> Option<String> {
        if at == "0" {
            Some("5".to_string())
        } else {
            None
        }
    };
    // Side-A chain writes `e` at index 7; probing atom "7" must unfold `e`
    // through its definition and read B[0] = "5" from B's interp.
    let writes = vec![(seven, e)];
    let got = exec.witness_cell_rec2(&defs, base_a, &la, base_b, &lb, &writes, base_a, "7", 0);
    assert_eq!(
        got,
        Some("5".to_string()),
        "def-chased write value must resolve against base B's interp \
         (pre-wire-up this bailed with None)"
    );
}

/// The select's array chain is interrupted by a defined array alias:
/// write value `(select M 0)` with the asserted definition
/// `(= M (store B 1 9))`. Previously the chain walk stopped at the `Var` `M`
/// (neither base), so the select never resolved and the cell bailed. With the
/// def chase the walk unfolds `M`, collects the store write and roots at `B`.
#[test]
fn witness_cell_rec2_chases_array_chain_alias() {
    let mut exec = Executor::new();
    let base_a = exec.ctx.terms.mk_var("A", int_array_sort());
    let base_b = exec.ctx.terms.mk_var("B", int_array_sort());
    let m = exec.ctx.terms.mk_var("M", int_array_sort());
    let zero = exec.ctx.terms.mk_int(BigInt::from(0));
    let one = exec.ctx.terms.mk_int(BigInt::from(1));
    let nine = exec.ctx.terms.mk_int(BigInt::from(9));
    let seven = exec.ctx.terms.mk_int(BigInt::from(7));
    let store_b = exec.ctx.terms.mk_app(
        Symbol::named("store"),
        vec![base_b, one, nine],
        int_array_sort(),
    );
    let def = exec.ctx.terms.mk_eq(m, store_b);
    exec.ctx.assertions.push(def);
    let sel_m0 = exec
        .ctx
        .terms
        .mk_app(Symbol::named("select"), vec![m, zero], Sort::Int);
    exec.last_model = Some(empty_model());

    let defs = exec.build_array_defs();
    assert_eq!(
        defs.get(&m),
        Some(&store_b),
        "build_array_defs must pick up the asserted (= M (store B 1 9))"
    );

    let la = |_: &str| -> Option<String> { None };
    let lb = |at: &str| -> Option<String> {
        if at == "0" {
            Some("5".to_string())
        } else {
            None
        }
    };
    // Side-A chain writes `(select M 0)` at index 7: the walk must chase
    // M -> (store B 1 9), see the inner write (1 -> 9) miss atom "0", and
    // fall through to B's interp at "0".
    let writes = vec![(seven, sel_m0)];
    let got = exec.witness_cell_rec2(&defs, base_a, &la, base_b, &lb, &writes, base_a, "7", 0);
    assert_eq!(
        got,
        Some("5".to_string()),
        "def-chased array alias must walk back to base B and read its interp \
         (pre-wire-up this bailed with None)"
    );
}
