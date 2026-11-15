// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::CancellationToken;
use ay_core::time::Instant;
use serde::Deserialize;
use std::time::Duration;

const SHARED_BYTES: usize = 64 * 1024 * 1024;

fn control(token: &CancellationToken) -> SourceControl<'_> {
    SourceControl::new(Instant::now() + Duration::from_secs(60), token)
}

#[derive(Debug, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Document {
    text: String,
    indices: Vec<Vec<usize>>,
}

struct NeverDecode;

impl<'de> Deserialize<'de> for NeverDecode {
    fn deserialize<D: serde::Deserializer<'de>>(_: D) -> Result<Self, D::Error> {
        panic!("surface/storage refusal must precede deserialization")
    }
}

#[test]
fn exact_json_roundtrip_preserves_strings_and_ordered_containers() {
    let token = CancellationToken::new();
    let value = Document {
        text: "(forall ((i (_ BitVec 64))) [ { \\\" } ])\n\t😀".into(),
        indices: vec![vec![], vec![7, 7, 1], vec![0]],
    };
    let encoded = encode(&value, &control(&token)).unwrap();
    assert_eq!(encoded, serde_json::to_vec(&value).unwrap());
    assert_eq!(decode::<Document>(&encoded, &control(&token)), Some(value));
    let unicode = br#"{"text":"\uD83D\uDE00","indices":[]}"#;
    let decoded = decode::<Document>(unicode, &control(&token)).unwrap();
    assert_eq!(decoded.text, "😀");
}

#[test]
fn lexical_escape_state_survives_every_chunk_boundary() {
    let token = CancellationToken::new();
    let value = vec!["brackets []{}", r#"quote " slash \"#, "\u{0}😀"];
    let bytes = serde_json::to_vec(&value).unwrap();
    for size in [1, 2, 3, 7, CHUNK] {
        let control = control(&token);
        let mut surface = Surface::default();
        for chunk in bytes.chunks(size) {
            surface.feed(chunk, &control).unwrap();
        }
        surface.finish(&control).unwrap();
        assert_eq!(surface.depth, 0);
        assert_eq!(surface.tokens, 4); // One array and three complete strings.
        assert_eq!(surface.bytes, bytes.len());
    }
    assert_eq!(
        decode::<Vec<String>>(&bytes, &control(&token)).unwrap(),
        value
    );
}

#[test]
fn depth_sixteen_is_exact_and_quoted_delimiters_do_not_count() {
    let token = CancellationToken::new();
    let json = format!(
        "{}\"[{{}}]\"{}",
        "[".repeat(MAX_DEPTH),
        "]".repeat(MAX_DEPTH)
    );
    let parsed = decode::<serde_json::Value>(json.as_bytes(), &control(&token)).unwrap();
    assert_eq!(encode(&parsed, &control(&token)).unwrap(), json.as_bytes());
    let too_deep = format!("[{json}]");
    assert!(decode::<NeverDecode>(too_deep.as_bytes(), &control(&token)).is_none());
    let wrapped = serde_json::Value::Array(vec![parsed]);
    assert!(encode(&wrapped, &control(&token)).is_none());
    for bytes in [b"]".as_slice(), b"[}", b"[[]", b"\"unfinished\\"] {
        assert!(decode::<NeverDecode>(bytes, &control(&token)).is_none());
    }
}

#[test]
fn serde_owns_invalid_grammar_schema_and_trailing_input_refusals() {
    let token = CancellationToken::new();
    for bytes in [
        br#"{"text":"a","indices":[],"extra":0}"#.as_slice(),
        br#"{"text":"a","text":"b","indices":[]}"#,
        br#"{"text":"a","indices":[]} null"#,
        br#"{"text":"\q","indices":[]}"#,
        br#"{"text":"\uD800","indices":[]}"#,
        br#"{"text":"a","indices":[[01]]}"#,
        br#"{"text":"a","indices":[,]}"#,
        b"{\"text\":\"\xff\",\"indices\":[]}",
    ] {
        assert!(decode::<Document>(bytes, &control(&token)).is_none());
    }
    assert_eq!(decode::<usize>(b" 7 \n", &control(&token)), Some(7));
    assert!(decode::<usize>(b"7 8", &control(&token)).is_none());
}

#[test]
fn large_source_strings_have_no_one_megabyte_subcap() {
    let token = CancellationToken::new();
    let source = "s".repeat(2 * 1024 * 1024);
    let bytes = encode(&source, &control(&token)).unwrap();
    assert_eq!(decode::<String>(&bytes, &control(&token)).unwrap(), source);
    // The byte ceiling applies to the entire JSON surface, independently of
    // any tighter cumulative parent copy allowance.
    let mut boundary = vec![b' '; MAX_BYTES];
    boundary[MAX_BYTES - 4..].copy_from_slice(b"null");
    assert_eq!(
        decode::<Option<usize>>(&boundary, &control(&token)),
        Some(None)
    );
    boundary.push(b' ');
    assert!(decode::<NeverDecode>(&boundary, &control(&token)).is_none());
    let exact_output = "s".repeat(MAX_BYTES - 2);
    assert_eq!(
        encode(&exact_output, &control(&token)).unwrap().len(),
        MAX_BYTES
    );
    let oversized_output = "s".repeat(MAX_BYTES - 1);
    assert!(encode(&oversized_output, &control(&token)).is_none());
}

#[test]
fn complete_decode_storage_is_prepaid_with_exact_shared_refusal_boundary() {
    let token = CancellationToken::new();
    // "ok": four surface bytes, two work/token units, six payload/scratch
    // bytes, 192 token-storage bytes, 256 root bytes and one reader work unit.
    let cost = 4 + 2 * 64 + 6 + 192 + 256 + 64;
    let exact = control(&token);
    exact.bytes(SHARED_BYTES - cost).unwrap();
    assert_eq!(decode::<String>(br#""ok""#, &exact).as_deref(), Some("ok"));
    assert!(exact.poll().is_some());
    assert!(decode::<String>(br#""ok""#, &exact).is_none());
    assert!(exact.poll().is_none());
    let short = control(&token);
    short.bytes(SHARED_BYTES - cost + 1).unwrap();
    assert!(decode::<String>(br#""ok""#, &short).is_none());
    assert!(short.poll().is_none());
    let before_serde = control(&token);
    before_serde.bytes(SHARED_BYTES - (cost - 64) + 1).unwrap();
    assert!(decode::<NeverDecode>(br#""ok""#, &before_serde).is_none());
    assert!(decode::<String>(br#""ok""#, &control(&token)).is_some());
}

#[test]
fn container_storage_is_counted_even_when_every_string_is_empty() {
    let token = CancellationToken::new();
    let input = br#"["","","",""]"#;
    let mut surface = Surface::default();
    let allowance = control(&token);
    surface.feed(input, &allowance).unwrap();
    surface.finish(&allowance).unwrap();
    assert_eq!(surface.tokens, 5);
    assert_eq!(surface.payload, 0);
    let before = input.len() + 6 * 64;
    let storage = 5 * 192 + 256;
    let short = control(&token);
    short.bytes(SHARED_BYTES - before - storage + 1).unwrap();
    assert!(decode::<NeverDecode>(input, &short).is_none());
    assert!(short.poll().is_none());
}

#[test]
fn reader_and_writer_refusals_are_latched_nonretryable_and_preallocation() {
    let token = CancellationToken::new();
    let live = control(&token);
    let input = vec![b' '; CHUNK * 2];
    let mut reader = Reader {
        bytes: &input,
        offset: 0,
        window: 0,
        failed: false,
        control: &live,
    };
    let mut buffer = vec![0; CHUNK * 2];
    assert_eq!(reader.read(&mut buffer).unwrap(), CHUNK);
    token.cancel();
    assert_eq!(
        reader.read(&mut buffer).unwrap_err().kind(),
        io::ErrorKind::Other
    );
    token.reset();
    assert_eq!(
        reader.read(&mut buffer).unwrap_err().kind(),
        io::ErrorKind::Other
    );
    let short = control(&token);
    short.bytes(SHARED_BYTES - 200).unwrap();
    let mut writer = Writer {
        bytes: Vec::new(),
        surface: Surface::default(),
        failed: false,
        control: &short,
    };
    assert_eq!(
        writer.write(b"null").unwrap_err().kind(),
        io::ErrorKind::Other
    );
    assert!(writer.bytes.is_empty());
    assert_eq!(writer.bytes.capacity(), 0);
    assert!(writer.write(b"0").is_err());
    assert!(writer.flush().is_err());
}

#[test]
fn final_encode_admission_observes_cancel_after_the_last_successful_write() {
    struct CancelAfter<'a>(&'a CancellationToken);
    impl Serialize for CancelAfter<'_> {
        fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
            let result = serializer.serialize_str("complete")?;
            self.0.cancel();
            Ok(result)
        }
    }
    let token = CancellationToken::new();
    let stopped = control(&token);
    assert!(encode(&CancelAfter(&token), &stopped).is_none());
    token.reset();
    assert!(encode(&"complete", &stopped).is_none());
    assert!(encode(&"complete", &control(&token)).is_some());
    let expired = SourceControl::new(Instant::now(), &token);
    assert!(decode::<String>(br#""complete""#, &expired).is_none());
    assert!(digest(b"complete", &expired).is_none());
}

#[test]
fn digest_is_exact_lowercase_sha256_and_uses_the_same_shared_budget() {
    let token = CancellationToken::new();
    assert_eq!(
        digest(b"abc", &control(&token)).unwrap(),
        "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
    );
    assert_eq!(
        digest(b"", &control(&token)).unwrap(),
        "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
    );
    let exact = control(&token);
    exact.bytes(SHARED_BYTES - 3 - 64 - 128).unwrap();
    assert!(digest(b"abc", &exact).is_some());
    let short = control(&token);
    short.bytes(SHARED_BYTES - 3 - 64 - 128 + 1).unwrap();
    assert!(digest(b"abc", &short).is_none());
    assert!(short.poll().is_none());
    assert!(digest(&vec![0; MAX_BYTES + 1], &control(&token)).is_none());
}
