// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn reader_checks_every_window_and_never_consumes_after_observed_refusal() {
    let limits = WireLimits {
        max_json_bytes: 4096,
        max_rows: 10,
        max_literals: 10,
        max_hints: 10,
        max_work: 100000,
        max_storage_bytes: 100000,
        deadline: Instant::now() + Duration::from_secs(60),
    };
    let mut calls = 0;
    let whitespace = [b' '; 1024];
    {
        let mut poll = || {
            calls += 1;
            calls != 2
        };
        let mut control = Control::new(limits, &mut poll);
        {
            let shared = RefCell::new(&mut control);
            let mut input = Input {
                bytes: &whitespace,
                position: 0,
                grant: 0,
                control: &shared,
            };
            let mut output = [0_u8; 1];
            for _ in 0..lexical::WINDOW {
                assert_eq!(input.read(&mut output).unwrap(), 1);
            }
            assert!(input.read(&mut output).is_err());
            assert_eq!(input.position, lexical::WINDOW);
            assert!(input.read(&mut output).is_err());
            assert_eq!(input.position, lexical::WINDOW);
        }
        assert_eq!(
            control.usage.charged_work,
            (2 * lexical::WINDOW * lexical::PARSER_PASSES) as u128
        );
    }
    assert_eq!(calls, 2);
}

#[test]
fn streaming_decoder_large_whitespace_and_error_positions_remain_bounded() {
    let limits = WireLimits {
        max_json_bytes: 10000,
        max_rows: 10,
        max_literals: 10,
        max_hints: 10,
        max_work: 1_000_000,
        max_storage_bytes: 100000,
        deadline: Instant::now() + Duration::from_secs(60),
    };
    let mut bytes = vec![b' '; 2048];
    bytes.extend_from_slice(
        br#"{"version":1,"rows":[{"id":2,"literals":[],"hints":[1]}],"empty_clause_id":2}"#,
    );
    let mut calls = 0;
    let success_work = {
        let mut poll = || {
            calls += 1;
            true
        };
        let mut control = Control::new(limits, &mut poll);
        read(&bytes, &mut control).unwrap();
        control.usage.charged_work
    };
    assert!(calls > 2 * (2048 / lexical::WINDOW));
    // A lexer-admitted grammar error at the end does not trigger slice-based
    // line/column rescans or refresh grants while container errors unwind.
    let position = bytes.len() - 1;
    bytes[position] = b']';
    let mut poll = || true;
    let mut control = Control::new(limits, &mut poll);
    assert!(read(&bytes, &mut control).is_err());
    assert!(control.usage.charged_work <= success_work);
    assert_eq!(control.usage.returned_owned_bytes, 0);
}
