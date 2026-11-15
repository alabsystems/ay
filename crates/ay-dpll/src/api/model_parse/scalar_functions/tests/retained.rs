// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn exact_inventory_uses_one_atomic_work_copy_and_output_budget() {
    let text = "(model (define-fun f ((x (_ BitVec 8))) (_ BitVec 8) x)
      (define-fun unused () (_ BitVec 136) (_ bv1 136)))";
    let byte = bv(8);
    let wide = bv(136);
    let args = [byte.clone()];
    let expected = [("f", args.as_slice(), &byte), ("unused", &[][..], &wide)];
    let initial = Budget::new();
    let mut measured = Budget::new();
    let result = parse_inventory(text, &expected, Inventory::Exact, &mut measured)
        .expect("complete retained model");
    let work = initial.work - measured.work;
    let bytes = initial.bytes - measured.bytes;
    let output = initial.output - measured.output;
    let mut exact = Budget {
        work,
        bytes,
        output,
        ..Budget::new()
    };
    assert_eq!(
        parse_inventory(text, &expected, Inventory::Exact, &mut exact),
        Some(result)
    );
    for mut short in [
        Budget {
            work: work - 1,
            ..Budget::new()
        },
        Budget {
            bytes: bytes - 1,
            ..Budget::new()
        },
        Budget {
            output: output - 1,
            ..Budget::new()
        },
    ] {
        assert!(parse_inventory(text, &expected, Inventory::Exact, &mut short).is_none());
        assert!(short.stopped);
        assert!(parse_inventory("(model)", &[], Inventory::Exact, &mut short).is_none());
    }
}

#[test]
fn exact_inventory_refusal_cannot_publish_or_reuse_a_partial_model_prefix() {
    let byte = bv(8);
    let expected = [("f", &[][..], &byte)];
    let text = "(model (define-fun f () (_ BitVec 8) #x00)
      (define-fun unrelated () (_ BitVec 8) #x00))";
    let mut stopped = Budget::new();
    assert!(parse_inventory(text, &expected, Inventory::Exact, &mut stopped).is_none());
    assert!(stopped.stopped);
    assert!(parse_inventory("(model)", &[], Inventory::Exact, &mut stopped).is_none());
    assert!(parse_scalar_function_models(text, &expected).is_some());
    assert!(decode_scalar_function_models("(model)", &[]).is_some());
}
