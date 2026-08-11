// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Resource-boundary tests for text and AST-vector inputs.

use std::{ffi::CString, ptr};

use super::*;

#[test]
fn bounded_ffi_text_readers_enforce_scan_and_file_limits() {
    assert_eq!(MAX_FFI_PARSER_SOURCE_BYTES, 1024 * 1024 * 1024);
    const { assert!(MAX_FFI_PARSER_SOURCE_BYTES > MAX_FFI_TEXT_BYTES) };
    let exact = CString::new("abcd").expect("test text must not contain an interior NUL");
    let oversized = CString::new("abcde").expect("test text must not contain an interior NUL");
    let invalid = CString::from_vec_with_nul(vec![0xff, 0])
        .expect("invalid UTF-8 fixture must still be NUL-terminated");
    // SAFETY: every non-null pointer comes from a live `CString`; the null
    // pointer is supplied deliberately to exercise the function's null guard.
    unsafe {
        assert_eq!(
            ffi_read_utf8_with_limit(exact.as_ptr(), 4),
            Ok("abcd".to_string())
        );
        assert_eq!(
            ffi_read_utf8_with_limit(oversized.as_ptr(), 4),
            Err(FfiTextError::TooLong(4))
        );
        assert_eq!(
            ffi_read_utf8_with_limit(invalid.as_ptr(), 4),
            Err(FfiTextError::InvalidUtf8)
        );
        assert_eq!(
            ffi_read_utf8_with_limit(ptr::null(), 4),
            Err(FfiTextError::Null)
        );
    }

    let file = tempfile::NamedTempFile::new().expect("create bounded-reader test file");
    std::fs::write(file.path(), b"abcde").expect("write bounded-reader test file");
    assert!(ffi_read_text_file_with_limit(
        file.path()
            .to_str()
            .expect("temporary test path must be valid UTF-8"),
        4,
    )
    .expect_err("oversized test file must be rejected")
    .contains("maximum 4 bytes"));
}

#[cfg(unix)]
#[test]
fn bounded_file_reader_rejects_nonregular_sources_without_blocking() {
    use std::os::unix::ffi::OsStrExt as _;
    use std::os::unix::fs::{symlink, OpenOptionsExt as _};
    use std::sync::mpsc;
    use std::time::Duration;

    let temp = tempfile::tempdir().expect("create nonregular-source test directory");
    let regular = temp.path().join("input.smt2");
    let alias = temp.path().join("input-link.smt2");
    std::fs::write(&regular, "(assert true)").expect("write regular source fixture");
    symlink(&regular, &alias).expect("create source symlink fixture");
    assert_eq!(
        ffi_read_text_file_with_limit(
            alias
                .to_str()
                .expect("temporary symlink path must be valid UTF-8"),
            1024,
        )
        .expect("regular symlink target must be readable"),
        "(assert true)"
    );

    let fifo = temp.path().join("input.fifo");
    let fifo_c = CString::new(fifo.as_os_str().as_bytes())
        .expect("temporary FIFO path must not contain an interior NUL");
    // SAFETY: `fifo_c` is a valid NUL-terminated path and the mode is a valid
    // permission bitmask. The fresh temporary path does not already exist.
    assert_eq!(unsafe { libc::mkfifo(fifo_c.as_ptr(), 0o600) }, 0);

    let (sender, receiver) = mpsc::channel();
    let fifo_for_reader = fifo.clone();
    let reader = std::thread::spawn(move || {
        let result = ffi_read_text_file_with_limit(
            fifo_for_reader
                .to_str()
                .expect("temporary FIFO path must be valid UTF-8"),
            1024,
        );
        let _ = sender.send(result);
    });
    let result = match receiver.recv_timeout(Duration::from_secs(2)) {
        Ok(result) => result,
        Err(error) => {
            // Unblock a regressed blocking FIFO open so the spawned thread can
            // terminate before this test reports the timeout.
            let _writer = std::fs::OpenOptions::new()
                .write(true)
                .custom_flags(libc::O_NONBLOCK)
                .open(&fifo);
            let _ = receiver.recv_timeout(Duration::from_secs(2));
            let _ = reader.join();
            panic!("bounded file reader blocked on FIFO: {error}");
        }
    };
    reader.join().expect("bounded-reader worker must not panic");
    assert!(result
        .expect_err("FIFO source must be rejected")
        .contains("not a regular file"));
    assert!(ffi_read_text_file_with_limit("/dev/null", 1024)
        .expect_err("character device source must be rejected")
        .contains("not a regular file"));
}

#[test]
fn parser_source_envelope_is_larger_than_scalar_ffi_text_envelope() {
    // SAFETY: the context is created and destroyed in this block, and the only
    // text pointer comes from a live NUL-terminated `CString`.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);
        let oversized = CString::new(vec![b'x'; MAX_FFI_TEXT_BYTES + 1])
            .expect("generated parser source must not contain an interior NUL");

        let parser_text = ffi_read_bounded_parser_text(oversized.as_ptr())
            .expect("parser envelope must accept the oversized scalar fixture");
        assert_eq!(parser_text.len(), MAX_FFI_TEXT_BYTES + 1);
        drop(parser_text);

        assert_eq!(Z3_mk_string(ctx, oversized.as_ptr()), 0);
        assert_eq!(Z3_get_error_code(ctx), Z3_INVALID_ARG);

        Z3_del_context(ctx);
    }
}

#[test]
fn ast_vector_resize_rejects_unbounded_allocation_without_mutation() {
    // SAFETY: the context and vector handles are created here, remain live for
    // every call, and the context is destroyed after the final observation.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);
        let vector = Z3_mk_ast_vector(ctx);
        Z3_ast_vector_resize(ctx, vector, 2);
        assert_eq!(Z3_ast_vector_size(ctx, vector), 2);

        Z3_ast_vector_resize(ctx, vector, u32::MAX);
        assert_eq!(Z3_get_error_code(ctx), Z3_INVALID_ARG);
        assert_eq!(Z3_ast_vector_size(ctx, vector), 2);

        Z3_del_context(ctx);
    }
}
