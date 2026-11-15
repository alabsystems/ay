// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use crate::{ChcParser, ChcProblem};

#[derive(Clone, Copy)]
pub(crate) enum Site {
    Body,
    Exit,
}

/// AY-authored source shape of the retained W2 fixture, not a recovered
/// consumer transaction. Whole complete arrays cross each original edge.
pub(crate) fn source(site: Site, store: u32, expected: u32) -> String {
    let (predicate, guard) = match site {
        Site::Body => ("B", "true"),
        Site::Exit => ("H", "(bvuge i #x0000000000000004)"),
    };
    format!(
        r#"(set-logic HORN)
(declare-fun H ((Array (_ BitVec 64) (_ BitVec 32)) (_ BitVec 64)) Bool)
(declare-fun B ((Array (_ BitVec 64) (_ BitVec 32)) (_ BitVec 64)) Bool)
(assert (H ((as const (Array (_ BitVec 64) (_ BitVec 32))) #x00000005)
           #x0000000000000000))
(assert (forall ((a (Array (_ BitVec 64) (_ BitVec 32))) (i (_ BitVec 64)))
  (=> (and (H a i) (bvult i #x0000000000000004))
      (B (store a #x0000000000000001 #x{store:08x}) i))))
(assert (forall ((a (Array (_ BitVec 64) (_ BitVec 32))) (i (_ BitVec 64)))
  (=> (B a i) (H a (bvadd i #x0000000000000001)))))
(assert (forall ((a (Array (_ BitVec 64) (_ BitVec 32))) (i (_ BitVec 64)))
  (=> (and ({predicate} a i) {guard}
           (not (= (select a #x0000000000000001) #x{expected:08x}))) false)))
(check-sat)
"#
    )
}

pub(crate) fn problem(site: Site, store: u32, expected: u32) -> ChcProblem {
    ChcParser::parse(&source(site, store, expected)).expect("authored original ground fixture")
}
