// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::{ChcDtConstructor, ChcSort};
use crate::expr::ChcDtSelector;
use crate::ChcDtConstructors;
use crate::ChcParser;

pub(super) const ACYCLIC: &str = "(set-logic HORN) \
    (declare-datatype Leaf ((leaf (payload Int)))) \
    (declare-datatype Pair ((pair (first Leaf) (second Leaf)))) \
    (declare-datatype Outer ((outer (pair-field Pair) (cells (Array Int (Array Bool Leaf)))))) \
    (declare-rel Inv (Leaf Pair Outer)) \
    (declare-var l Leaf) (declare-var p Pair) (declare-var o Outer) \
    (rule (Inv l p o)) (query Inv)";

pub(super) fn feed(parser: &mut ChcParser, input: &str) {
    parser.input = input.to_owned();
    parser.pos = 0;
    while parser.pos < parser.input.len() {
        parser.skip_whitespace_and_comments();
        if parser.pos < parser.input.len() {
            parser.parse_command().unwrap();
        }
    }
}

pub(super) fn parsed(input: &str) -> ChcParser {
    let mut parser = ChcParser::new();
    feed(&mut parser, input);
    parser
}

pub(super) fn metadata(sort: &ChcSort) -> &ChcDtConstructors {
    let ChcSort::Datatype { constructors, .. } = sort else {
        panic!("expected datatype, got {sort:?}");
    };
    constructors
}

pub(super) fn field(sort: &ChcSort, index: usize) -> &ChcSort {
    &metadata(sort)[0].selectors[index].sort
}

pub(super) fn array_value(sort: &ChcSort) -> &ChcSort {
    let ChcSort::Array(_, value) = sort else {
        panic!("expected array, got {sort:?}");
    };
    value
}

pub(super) fn same_metadata(left: &ChcSort, right: &ChcSort) {
    let (
        ChcSort::Datatype {
            name: left_name, ..
        },
        ChcSort::Datatype {
            name: right_name, ..
        },
    ) = (left, right)
    else {
        panic!("expected two datatypes");
    };
    assert_eq!(left_name, right_name);
    // Equal definitions are one interned list, so this checks the definition,
    // not whether resolution rebuilt it; cost is checked by work counts.
    assert!(
        ChcDtConstructors::ptr_eq(metadata(left), metadata(right)),
        "{left_name} definitions differ"
    );
}

pub(super) fn datatype(name: &str, constructor: &str, fields: Vec<ChcSort>) -> ChcSort {
    ChcSort::Datatype {
        name: name.to_owned(),
        constructors: ChcDtConstructors::new(vec![ChcDtConstructor {
            name: constructor.to_owned(),
            selectors: fields
                .into_iter()
                .enumerate()
                .map(|(index, sort)| ChcDtSelector {
                    name: format!("field-{index}"),
                    sort,
                })
                .collect(),
        }]),
    }
}
