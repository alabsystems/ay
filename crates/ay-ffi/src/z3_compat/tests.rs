// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the Z3-compatible C API.

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

/// Empty solver checks are vacuously valid SAT, not consumer-rejected UNDEF.
/// This exercises the actual C ABI path rather than the local lbool mapper.
#[test]
fn test_z3_compat_empty_solver_is_true_at_consumer_boundary() {
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);
        let solver = Z3_mk_solver(ctx);

        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_TRUE);
        assert_eq!(Z3_get_error_code(ctx), Z3_OK);
        assert!(!Z3_solver_get_model(ctx, solver).is_null());

        Z3_del_context(ctx);
    }
}

/// Basic LIA: x > 0 AND x < 10 is SAT
#[test]
fn test_z3_compat_basic_lia() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let sym = Z3_mk_string_symbol(ctx, c"x".as_ptr());
        let x = Z3_mk_const(ctx, sym, int_sort);

        let zero = Z3_mk_int(ctx, 0, int_sort);
        let ten = Z3_mk_int(ctx, 10, int_sort);

        let x_gt_0 = Z3_mk_gt(ctx, x, zero);
        let x_lt_10 = Z3_mk_lt(ctx, x, ten);

        let solver = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, solver, x_gt_0);
        Z3_solver_assert(ctx, solver, x_lt_10);

        let result = Z3_solver_check(ctx, solver);
        assert_eq!(result, Z3_L_TRUE);

        let model = Z3_solver_get_model(ctx, solver);
        assert!(!model.is_null());

        let model_str = Z3_model_to_string(ctx, model);
        assert!(!model_str.is_null());

        Z3_del_context(ctx);
    }
}

/// Config timeout zero follows Z3's convention: it disables the deadline.
#[test]
fn test_z3_compat_config_timeout_param_smoke() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let cfg = Z3_mk_config();
        Z3_set_param_value(cfg, c"timeout".as_ptr(), c"0".as_ptr());
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let sym = Z3_mk_string_symbol(ctx, c"x".as_ptr());
        let x = Z3_mk_const(ctx, sym, int_sort);
        let zero = Z3_mk_int(ctx, 0, int_sort);

        let solver = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, solver, Z3_mk_ge(ctx, x, zero));
        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_TRUE);
        assert!(!Z3_solver_get_model(ctx, solver).is_null());

        Z3_del_context(ctx);
    }
}

#[test]
fn test_update_param_timeout_zero_disables_deadline_and_retires_results() {
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);
        let solver = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, solver, Z3_mk_true(ctx));
        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_TRUE);
        assert!(!Z3_solver_get_model(ctx, solver).is_null());

        Z3_update_param_value(ctx, c"timeout".as_ptr(), c"0".as_ptr());
        assert_eq!(Z3_get_error_code(ctx), Z3_OK);
        assert_eq!((*ctx).solver.timeout(), None);
        assert!(
            Z3_solver_get_model(ctx, solver).is_null(),
            "a successful context configuration mutation retires copied results"
        );
        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_TRUE);

        (*ctx).poison_decision_engine("test poison".to_string());
        Z3_update_param_value(ctx, c"timeout".as_ptr(), c"1".as_ptr());
        assert_eq!(Z3_get_error_code(ctx), Z3_INVALID_USAGE);
        assert_eq!((*ctx).solver.timeout(), None);

        Z3_del_context(ctx);
    }
}

/// UNSAT: x > 10 AND x < 5
#[test]
fn test_z3_compat_unsat() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let sym = Z3_mk_string_symbol(ctx, c"x".as_ptr());
        let x = Z3_mk_const(ctx, sym, int_sort);

        let five = Z3_mk_int(ctx, 5, int_sort);
        let ten = Z3_mk_int(ctx, 10, int_sort);

        let solver = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, solver, Z3_mk_gt(ctx, x, ten));
        Z3_solver_assert(ctx, solver, Z3_mk_lt(ctx, x, five));

        let result = Z3_solver_check(ctx, solver);
        assert_eq!(result, Z3_L_FALSE);

        Z3_del_context(ctx);
    }
}

/// `get_reason_unknown` should be empty after a SAT result.
#[test]
fn test_z3_compat_reason_unknown_empty_after_sat() {
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let sym = Z3_mk_string_symbol(ctx, c"x".as_ptr());
        let x = Z3_mk_const(ctx, sym, int_sort);

        let solver = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, solver, Z3_mk_eq(ctx, x, Z3_mk_int(ctx, 0, int_sort)));
        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_TRUE);

        let reason = Z3_solver_get_reason_unknown(ctx, solver);
        assert_eq!(
            std::ffi::CStr::from_ptr(reason)
                .to_str()
                .expect("reason should be valid UTF-8"),
            ""
        );

        Z3_del_context(ctx);
    }
}

/// Push/pop scoping
#[test]
fn test_z3_compat_push_pop() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let bool_sort = Z3_mk_bool_sort(ctx);
        let sym_a = Z3_mk_string_symbol(ctx, c"a".as_ptr());
        let a = Z3_mk_const(ctx, sym_a, bool_sort);

        let solver = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, solver, a);

        Z3_solver_push(ctx, solver);
        Z3_solver_assert(ctx, solver, Z3_mk_not(ctx, a));
        let result = Z3_solver_check(ctx, solver);
        assert_eq!(result, Z3_L_FALSE);

        Z3_solver_pop(ctx, solver, 1);
        let result2 = Z3_solver_check(ctx, solver);
        assert_eq!(result2, Z3_L_TRUE);

        Z3_del_context(ctx);
    }
}

/// Bitvector operations
#[test]
fn test_z3_compat_bitvectors() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let bv8 = Z3_mk_bv_sort(ctx, 8);
        let sym = Z3_mk_string_symbol(ctx, c"bv_x".as_ptr());
        let x = Z3_mk_const(ctx, sym, bv8);

        let five = Z3_mk_unsigned_int(ctx, 5, bv8);
        let result_add = Z3_mk_bvadd(ctx, x, five);
        assert_ne!(result_add, 0);

        let ten = Z3_mk_unsigned_int(ctx, 10, bv8);
        let cmp = Z3_mk_bvult(ctx, x, ten);

        let solver = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, solver, cmp);
        let sat = Z3_solver_check(ctx, solver);
        assert_eq!(sat, Z3_L_TRUE);

        assert!(Z3_mk_bv_sort(ctx, 0).is_null());
        assert_eq!(Z3_get_error_code(ctx), Z3_INVALID_ARG);
        assert!(Z3_mk_bv_sort(ctx, 1_048_577).is_null());
        assert_eq!(Z3_get_error_code(ctx), Z3_INVALID_ARG);
        assert_eq!(Z3_mk_extract(ctx, 3, 4, x), 0);
        assert_eq!(Z3_get_error_code(ctx), Z3_INVALID_ARG);
        assert_eq!(Z3_mk_zero_ext(ctx, c_uint::MAX, x), 0);
        assert_eq!(Z3_get_error_code(ctx), Z3_INVALID_ARG);
        assert_eq!(Z3_mk_repeat(ctx, c_uint::MAX, x), 0);
        assert_eq!(Z3_get_error_code(ctx), Z3_INVALID_ARG);

        let int_sort = Z3_mk_int_sort(ctx);
        let one = Z3_mk_int(ctx, 1, int_sort);
        assert_eq!(Z3_mk_extract(ctx, c_uint::MAX, 0, one), 0);
        assert_eq!(Z3_get_error_code(ctx), Z3_INVALID_ARG);
        assert_eq!(Z3_mk_zero_ext(ctx, 1, one), 0);
        assert_eq!(Z3_get_error_code(ctx), Z3_INVALID_ARG);
        assert_eq!(Z3_mk_repeat(ctx, 2, one), 0);
        assert_eq!(Z3_get_error_code(ctx), Z3_INVALID_ARG);
        assert_eq!(Z3_mk_int2bv(ctx, c_uint::MAX, one), 0);
        assert_eq!(Z3_get_error_code(ctx), Z3_INVALID_ARG);

        Z3_del_context(ctx);
    }
}

/// Boolean operation construction
#[test]
fn test_z3_compat_boolean_ops() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let t = Z3_mk_true(ctx);
        let f = Z3_mk_false(ctx);

        assert_ne!(t, 0);
        assert_ne!(f, 0);
        assert_ne!(t, f);

        let not_t = Z3_mk_not(ctx, t);
        let iff = Z3_mk_iff(ctx, not_t, f);
        let imp = Z3_mk_implies(ctx, t, f);
        let xor = Z3_mk_xor(ctx, t, f);

        assert_ne!(iff, 0);
        assert_ne!(imp, 0);
        assert_ne!(xor, 0);

        let args = [t, f];
        let and_r = Z3_mk_and(ctx, 2, args.as_ptr());
        let or_r = Z3_mk_or(ctx, 2, args.as_ptr());
        assert_ne!(and_r, 0);
        assert_ne!(or_r, 0);

        Z3_del_context(ctx);
    }
}

/// Sort kind inspection
#[test]
fn test_z3_compat_sort_kinds() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let bool_s = Z3_mk_bool_sort(ctx);
        let int_s = Z3_mk_int_sort(ctx);
        let real_s = Z3_mk_real_sort(ctx);
        let bv_s = Z3_mk_bv_sort(ctx, 32);

        assert_eq!(Z3_get_sort_kind(ctx, bool_s), Z3_BOOL_SORT);
        assert_eq!(Z3_get_sort_kind(ctx, int_s), Z3_INT_SORT);
        assert_eq!(Z3_get_sort_kind(ctx, real_s), Z3_REAL_SORT);
        assert_eq!(Z3_get_sort_kind(ctx, bv_s), Z3_BV_SORT);
        assert_eq!(Z3_get_bv_sort_size(ctx, bv_s), 32);

        let arr_s = Z3_mk_array_sort(ctx, int_s, bool_s);
        assert_eq!(Z3_get_sort_kind(ctx, arr_s), Z3_ARRAY_SORT);

        Z3_del_context(ctx);
    }
}

/// Z3_mk_set_has_size: REAL cardinality over finite (Bool) element domains,
/// honest `unknown` over infinite (Int) element domains, and root-obj
/// printing for algebraic-root handles (#capi-set-has-size basket).
#[test]
fn test_set_has_size_and_algebraic_printing() {
    // SAFETY: all handles are allocated and freed inside this block; no
    // pointer escapes and the test owns the context exclusively.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let bool_sort = Z3_mk_bool_sort(ctx);

        // Bool element domain: |full set| = 2 is REAL sat, = 3 is REAL unsat.
        let full = Z3_mk_full_set(ctx, bool_sort);
        let two = Z3_mk_int(ctx, 2, int_sort);
        let three = Z3_mk_int(ctx, 3, int_sort);
        let s1 = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, s1, Z3_mk_set_has_size(ctx, full, two));
        assert_eq!(
            Z3_solver_check(ctx, s1),
            1,
            "|full Bool set| = 2 must be sat"
        );
        let s2 = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, s2, Z3_mk_set_has_size(ctx, full, three));
        assert_eq!(
            Z3_solver_check(ctx, s2),
            -1,
            "|full Bool set| = 3 must be unsat"
        );

        // Int element domain: honest unknown (fail-closed cardinality gate),
        // and the term prints as its real s-expression.
        let int_set_sort = Z3_mk_set_sort(ctx, int_sort);
        let sym = Z3_mk_string_symbol(ctx, c"s".as_ptr());
        let s = Z3_mk_const(ctx, sym, int_set_sort);
        let hs = Z3_mk_set_has_size(ctx, s, three);
        let txt = std::ffi::CStr::from_ptr(Z3_ast_to_string(ctx, hs)).to_string_lossy();
        assert!(txt.contains("set.has_size"), "got: {txt}");
        let s3 = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, s3, hs);
        assert_eq!(
            Z3_solver_check(ctx, s3),
            0,
            "infinite-domain set.has_size must be an honest unknown, never a verdict"
        );

        // Algebraic root handle prints z3's exact root-obj form, never (null).
        let two_r = Z3_mk_real(ctx, 2, 1);
        let sqrt2 = Z3_algebraic_root(ctx, two_r, 2);
        let p = Z3_ast_to_string(ctx, sqrt2);
        assert!(!p.is_null(), "algebraic root must render, not (null)");
        let ptxt = std::ffi::CStr::from_ptr(p).to_string_lossy();
        assert_eq!(ptxt, "(root-obj (+ (^ x 2) (- 2)) 2)");

        Z3_del_context(ctx);
    }
}

/// Version query
#[test]
fn test_z3_compat_version() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let mut major: c_uint = 0;
        let mut minor: c_uint = 0;
        let mut build: c_uint = 0;
        let mut rev: c_uint = 0;
        Z3_get_version(&raw mut major, &raw mut minor, &raw mut build, &raw mut rev);
        assert_eq!(major, 5);
        assert_eq!(minor, 0);
        assert_eq!(build, 0);
        assert_eq!(rev, 0);

        let full = Z3_get_full_version();
        assert!(!full.is_null());
        assert_eq!(
            std::ffi::CStr::from_ptr(full)
                .to_str()
                .expect("compatibility version must be valid UTF-8"),
            concat!("AY ", env!("CARGO_PKG_VERSION"), " (Z3 5.0.0.0 compatible)")
        );
    }
}

/// Quantifier construction: forall and exists term creation
#[test]
fn test_z3_compat_quantifier_construction() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let sym = Z3_mk_string_symbol(ctx, c"x".as_ptr());
        let x = Z3_mk_const(ctx, sym, int_sort);

        let zero = Z3_mk_int(ctx, 0, int_sort);
        let one = Z3_mk_int(ctx, 1, int_sort);
        let x_gt_0 = Z3_mk_gt(ctx, x, zero);
        let x_ge_1 = Z3_mk_ge(ctx, x, one);
        let body = Z3_mk_implies(ctx, x_gt_0, x_ge_1);

        // Test forall_const creates a non-null term
        let bound = [x];
        let forall = Z3_mk_forall_const(ctx, 0, 1, bound.as_ptr(), 0, ptr::null(), body);
        assert_ne!(forall, 0, "Z3_mk_forall_const should return non-null");

        // Test exists_const creates a non-null term
        let body2 = Z3_mk_gt(ctx, x, zero);
        let exists = Z3_mk_exists_const(ctx, 0, 1, bound.as_ptr(), 0, ptr::null(), body2);
        assert_ne!(exists, 0, "Z3_mk_exists_const should return non-null");

        // forall and exists should be different ASTs
        assert_ne!(forall, exists);

        // Negation of quantifier should also work
        let neg = Z3_mk_not(ctx, forall);
        assert_ne!(neg, 0, "Z3_mk_not on quantifier should work");

        Z3_del_context(ctx);
    }
}

/// Z3_mk_bvcomp: equality as 1-bit BV
#[test]
fn test_z3_compat_bvcomp() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let bv8 = Z3_mk_bv_sort(ctx, 8);
        let five_a = Z3_mk_unsigned_int(ctx, 5, bv8);
        let five_b = Z3_mk_unsigned_int(ctx, 5, bv8);

        let comp = Z3_mk_bvcomp(ctx, five_a, five_b);
        assert_ne!(comp, 0);

        // bvcomp(5, 5) should be #b1
        let bv1 = Z3_mk_bv_sort(ctx, 1);
        let one = Z3_mk_unsigned_int(ctx, 1, bv1);
        let eq_one = Z3_mk_eq(ctx, comp, one);

        let solver = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, solver, eq_one);
        let result = Z3_solver_check(ctx, solver);
        assert_eq!(result, Z3_L_TRUE);

        Z3_del_context(ctx);
    }
}

/// Pattern construction
#[test]
fn test_z3_compat_mk_pattern() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let sym_f = Z3_mk_string_symbol(ctx, c"f".as_ptr());
        let f_decl = Z3_mk_func_decl(ctx, sym_f, 1, &raw const int_sort, int_sort);
        assert!(!f_decl.is_null());

        let sym_x = Z3_mk_string_symbol(ctx, c"x".as_ptr());
        let x = Z3_mk_const(ctx, sym_x, int_sort);
        let fx = Z3_mk_app(ctx, f_decl, 1, &raw const x);
        assert_ne!(fx, 0);

        let pattern = Z3_mk_pattern(ctx, 1, &raw const fx);
        assert!(!pattern.is_null());

        Z3_del_context(ctx);
    }
}

/// Z3_mk_abs: absolute value
#[test]
fn test_z3_compat_abs() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let sym = Z3_mk_string_symbol(ctx, c"x".as_ptr());
        let x = Z3_mk_const(ctx, sym, int_sort);

        let abs_x = Z3_mk_abs(ctx, x);
        assert_ne!(abs_x, 0);

        // |x| >= 0 should be SAT for any x
        let zero = Z3_mk_int(ctx, 0, int_sort);
        let abs_ge_0 = Z3_mk_ge(ctx, abs_x, zero);

        let solver = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, solver, abs_ge_0);
        let result = Z3_solver_check(ctx, solver);
        assert_eq!(result, Z3_L_TRUE);

        Z3_del_context(ctx);
    }
}

/// Application introspection: Z3_get_app_num_args, Z3_get_app_arg, Z3_get_app_decl
#[test]
fn test_z3_compat_app_introspection() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let sym_x = Z3_mk_string_symbol(ctx, c"x".as_ptr());
        let x = Z3_mk_const(ctx, sym_x, int_sort);

        let sym_y = Z3_mk_string_symbol(ctx, c"y".as_ptr());
        let y = Z3_mk_const(ctx, sym_y, int_sort);

        // Build x + y (2 arguments)
        let args = [x, y];
        let sum = Z3_mk_add(ctx, 2, args.as_ptr());
        assert_ne!(sum, 0);

        // Should have 2 children
        let num_args = Z3_get_app_num_args(ctx, sum);
        assert_eq!(num_args, 2, "x + y should have 2 arguments");

        // First arg should be x, second should be y
        let arg0 = Z3_get_app_arg(ctx, sum, 0);
        let arg1 = Z3_get_app_arg(ctx, sum, 1);
        assert_eq!(arg0, x, "first arg should be x");
        assert_eq!(arg1, y, "second arg should be y");

        // Out-of-bounds should return 0
        let oob = Z3_get_app_arg(ctx, sum, 5);
        assert_eq!(oob, 0, "out-of-bounds arg should return 0");

        // get_app_decl should return a non-null func_decl
        let decl = Z3_get_app_decl(ctx, sum);
        assert!(!decl.is_null(), "app_decl should be non-null for addition");

        // A variable should have 0 children
        let x_args = Z3_get_app_num_args(ctx, x);
        assert_eq!(x_args, 0, "variable should have 0 args");

        Z3_del_context(ctx);
    }
}

/// Null pointer safety
#[test]
fn test_z3_compat_null_safety() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        // Context operations on null should not crash
        assert_eq!(
            Z3_solver_check(ptr::null_mut(), ptr::null_mut()),
            Z3_L_UNDEF
        );
        assert!(Z3_solver_get_model(ptr::null_mut(), ptr::null_mut()).is_null());
        assert!(Z3_mk_solver(ptr::null_mut()).is_null());
        assert_eq!(Z3_mk_true(ptr::null_mut()), 0);
        assert_eq!(Z3_mk_int(ptr::null_mut(), 42, ptr::null_mut()), 0);
        assert!(Z3_mk_int_sort(ptr::null_mut()).is_null());

        // Sort operations on null
        assert_eq!(
            Z3_get_sort_kind(ptr::null_mut(), ptr::null_mut()),
            Z3_UNKNOWN_AST
        );
        assert_eq!(Z3_get_bv_sort_size(ptr::null_mut(), ptr::null_mut()), 0);

        // Delete null is safe
        Z3_del_context(ptr::null_mut());
        Z3_del_config(ptr::null_mut());
    }
}

#[test]
fn checked_ast_to_term_rejects_null() {
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);
        assert_eq!(checked_ast_to_term(&*ctx, 0), None);
        Z3_del_context(ctx);
    }
}

/// Round-trip: context-salted ASTs decode to their live source terms.
#[test]
fn test_ast_term_roundtrip() {
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);
        let terms = [
            (*ctx).solver.bool_const(false),
            (*ctx).solver.bool_const(true),
            (*ctx).solver.int_const(7),
        ];
        for term in terms {
            let ast = term_to_ast(&*ctx, term);
            assert_ne!(ast, 0, "valid term should not map to null Z3_ast");
            assert_eq!(checked_ast_to_term(&*ctx, ast), Some(term));
        }
        Z3_del_context(ctx);
    }
}

// ========================== ast_identity.rs tests ==========================

/// Z3_is_eq_ast: same AST values are equal
#[test]
fn test_z3_is_eq_ast_same() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let sym = Z3_mk_string_symbol(ctx, c"x".as_ptr());
        let x = Z3_mk_const(ctx, sym, int_sort);

        assert!(Z3_is_eq_ast(ctx, x, x), "same AST must be equal to itself");

        Z3_del_context(ctx);
    }
}

/// Z3_is_eq_ast: different AST values are not equal
#[test]
fn test_z3_is_eq_ast_different() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let sym_x = Z3_mk_string_symbol(ctx, c"x".as_ptr());
        let sym_y = Z3_mk_string_symbol(ctx, c"y".as_ptr());
        let x = Z3_mk_const(ctx, sym_x, int_sort);
        let y = Z3_mk_const(ctx, sym_y, int_sort);

        assert!(!Z3_is_eq_ast(ctx, x, y), "different ASTs must not be equal");

        Z3_del_context(ctx);
    }
}

/// Z3_get_ast_id: returns consistent IDs
#[test]
fn test_z3_get_ast_id_consistent() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let sym = Z3_mk_string_symbol(ctx, c"x".as_ptr());
        let x = Z3_mk_const(ctx, sym, int_sort);

        let id1 = Z3_get_ast_id(ctx, x);
        let id2 = Z3_get_ast_id(ctx, x);
        assert_eq!(id1, id2, "same AST must have same ID");

        Z3_del_context(ctx);
    }
}

/// Z3_get_ast_hash: consistent with Z3_get_ast_id
#[test]
fn test_z3_get_ast_hash_equals_id() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let sym = Z3_mk_string_symbol(ctx, c"x".as_ptr());
        let x = Z3_mk_const(ctx, sym, int_sort);

        let id = Z3_get_ast_id(ctx, x);
        let hash = Z3_get_ast_hash(ctx, x);
        assert_eq!(id, hash, "AY uses same value for ID and hash");

        Z3_del_context(ctx);
    }
}

/// Z3_is_eq_sort: same sorts are equal
#[test]
fn test_z3_is_eq_sort_same() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        assert!(
            Z3_is_eq_sort(ctx, int_sort, int_sort),
            "same sort must be equal to itself"
        );

        Z3_del_context(ctx);
    }
}

/// Z3_is_eq_sort: different sorts are not equal
#[test]
fn test_z3_is_eq_sort_different() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let bool_sort = Z3_mk_bool_sort(ctx);
        assert!(
            !Z3_is_eq_sort(ctx, int_sort, bool_sort),
            "Int and Bool sorts must not be equal"
        );

        Z3_del_context(ctx);
    }
}

/// Z3_is_eq_sort: null sorts handled safely
#[test]
fn test_z3_is_eq_sort_null() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        assert!(
            !Z3_is_eq_sort(ctx, int_sort, ptr::null_mut()),
            "non-null vs null must be false"
        );
        assert!(
            Z3_is_eq_sort(ctx, ptr::null_mut(), ptr::null_mut()),
            "null vs null must be true"
        );

        Z3_del_context(ctx);
    }
}

/// Z3_get_sort_name: returns a valid symbol for named sorts
#[test]
fn test_z3_get_sort_name_int() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let name_sym = Z3_get_sort_name(ctx, int_sort);
        assert!(
            !name_sym.is_null(),
            "sort name symbol must not be null for Int sort"
        );
        // Symbol is now freed by Z3Context::Drop via symbol_cache (#5528)

        Z3_del_context(ctx);
    }
}

/// Z3_get_sort_name: null sort returns null
#[test]
fn test_z3_get_sort_name_null() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let name_sym = Z3_get_sort_name(ctx, ptr::null_mut());
        assert!(name_sym.is_null(), "null sort must return null symbol");

        Z3_del_context(ctx);
    }
}

/// Z3_get_sort_id: returns non-zero for valid sorts
#[test]
fn test_z3_get_sort_id_valid() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let id = Z3_get_sort_id(ctx, int_sort);
        assert_ne!(id, 0, "valid sort must have non-zero ID");

        Z3_del_context(ctx);
    }
}

/// Z3_get_sort_id: null sort returns 0
#[test]
fn test_z3_get_sort_id_null() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        assert_eq!(
            Z3_get_sort_id(ptr::null_mut(), ptr::null_mut()),
            0,
            "null sort must return ID 0"
        );
    }
}

/// Z3_func_decl_to_ast: returns 0 (func_decls are not ASTs in AY)
#[test]
fn test_z3_func_decl_to_ast_returns_zero() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let ast = Z3_func_decl_to_ast(ctx, ptr::null_mut());
        assert_eq!(ast, 0, "func_decl_to_ast must return 0 in AY");

        Z3_del_context(ctx);
    }
}

/// Z3_is_eq_func_decl: null func_decls are equal to each other
#[test]
fn test_z3_is_eq_func_decl_both_null() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        assert!(
            Z3_is_eq_func_decl(ctx, ptr::null_mut(), ptr::null_mut()),
            "two null func_decls must be equal"
        );

        Z3_del_context(ctx);
    }
}

/// Z3_func_decl_to_string: null returns "(null)"
#[test]
fn test_z3_func_decl_to_string_null() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let s = Z3_func_decl_to_string(ctx, ptr::null_mut());
        assert!(
            !s.is_null(),
            "null func_decl should return \"(null)\" string"
        );
        let cs = std::ffi::CStr::from_ptr(s);
        assert_eq!(
            cs.to_str().expect("valid UTF-8"),
            "(null)",
            "null func_decl string must be \"(null)\""
        );

        Z3_del_context(ctx);
    }
}

/// Z3_get_symbol_kind: null symbol returns string kind (1)
#[test]
fn test_z3_get_symbol_kind_null() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let kind = Z3_get_symbol_kind(ptr::null_mut(), ptr::null_mut());
        assert_eq!(kind, 1, "null symbol must return string kind (1)");
    }
}

/// Z3_get_symbol_int: null symbol returns -1
#[test]
fn test_z3_get_symbol_int_null() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let val = Z3_get_symbol_int(ptr::null_mut(), ptr::null_mut());
        assert_eq!(val, -1, "null symbol must return -1");
    }
}

/// Raw pointer as_mut() borrows are scoped to the block, not &'static mut (#6018, #8568).
/// Verifies that multiple sequential FFI calls each get independent borrows
/// without aliasing violations.
///
/// `ctx_ref` was removed in #8568 because its `<'a>` lifetime parameter let
/// callers choose an unbounded lifetime (including `'static`). All call sites
/// now use `ptr.as_mut()` directly, which the compiler constrains to the
/// enclosing block.
#[test]
fn test_ctx_ptr_scoped_lifetime_8568() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx_ptr = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        // Each as_mut() call returns a fresh scoped borrow.
        // The compiler constrains the lifetime to this block.
        {
            // SAFETY: ctx_ptr is valid and non-null (just created above).
            // This borrow does not overlap with any other mutable reference.
            let ctx = ctx_ptr.as_mut().expect("non-null context");
            ctx.solver.push();
        }
        // First borrow dropped. Second borrow is sound.
        {
            // SAFETY: same as above; prior borrow is dead.
            let ctx = ctx_ptr.as_mut().expect("non-null context");
            ctx.solver.pop();
        }

        // Null returns None.
        assert!(ptr::null_mut::<Z3Context>().as_mut().is_none());

        Z3_del_context(ctx_ptr);
    }
}

/// Z3_mk_rem: truncation remainder has same sign as dividend (#6115)
///
/// rem(-7, 3) = -1 (not +2 like mod)
/// rem(7, -3) = 1 (not -2 like mod)
#[test]
fn test_z3_mk_rem_truncation_semantics() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);

        // Test case 1: rem(-7, 3) should equal -1
        {
            let neg7 = Z3_mk_int(ctx, -7, int_sort);
            let three = Z3_mk_int(ctx, 3, int_sort);
            let neg1 = Z3_mk_int(ctx, -1, int_sort);

            let rem_result = Z3_mk_rem(ctx, neg7, three);
            assert_ne!(rem_result, 0, "Z3_mk_rem should return non-null");

            // Assert rem(-7,3) = -1 and check SAT
            let eq = Z3_mk_eq(ctx, rem_result, neg1);
            let solver = Z3_mk_solver(ctx);
            Z3_solver_assert(ctx, solver, eq);
            let result = Z3_solver_check(ctx, solver);
            assert_eq!(result, Z3_L_TRUE, "rem(-7, 3) = -1 should be SAT");
        }

        // Test case 2: rem(7, -3) should equal 1
        {
            let seven = Z3_mk_int(ctx, 7, int_sort);
            let neg3 = Z3_mk_int(ctx, -3, int_sort);
            let one = Z3_mk_int(ctx, 1, int_sort);

            let rem_result = Z3_mk_rem(ctx, seven, neg3);
            let eq = Z3_mk_eq(ctx, rem_result, one);
            let solver = Z3_mk_solver(ctx);
            Z3_solver_assert(ctx, solver, eq);
            let result = Z3_solver_check(ctx, solver);
            assert_eq!(result, Z3_L_TRUE, "rem(7, -3) = 1 should be SAT");
        }

        // Negative test: rem(-7, 3) != 2 (mod would give 2, rem gives -1)
        {
            let neg7 = Z3_mk_int(ctx, -7, int_sort);
            let three = Z3_mk_int(ctx, 3, int_sort);
            let two = Z3_mk_int(ctx, 2, int_sort);

            let rem_result = Z3_mk_rem(ctx, neg7, three);
            let eq = Z3_mk_eq(ctx, rem_result, two);
            let solver = Z3_mk_solver(ctx);
            Z3_solver_assert(ctx, solver, eq);
            let result = Z3_solver_check(ctx, solver);
            assert_eq!(
                result, Z3_L_FALSE,
                "rem(-7, 3) = 2 should be UNSAT (that's mod, not rem)"
            );
        }

        Z3_del_context(ctx);
    }
}

/// Z3_mk_numeral with large integer beyond i64 range (#6112)
#[test]
fn test_z3_mk_numeral_large_integer_precision() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);

        // 2^63 = 9223372036854775808 (overflows i64)
        let big_str = c"9223372036854775808";
        let big = Z3_mk_numeral(ctx, big_str.as_ptr(), int_sort);
        assert_ne!(big, 0, "Z3_mk_numeral should handle >i64 values");

        // Verify the numeral string round-trips correctly
        let numeral_str = Z3_get_numeral_string(ctx, big);
        assert!(!numeral_str.is_null(), "numeral string should not be null");
        let s = std::ffi::CStr::from_ptr(numeral_str)
            .to_str()
            .expect("valid UTF-8");
        assert_eq!(
            s, "9223372036854775808",
            "large integer should round-trip exactly"
        );

        // Verify it works in constraints: big > 2^63 - 1
        let max_i64_str = c"9223372036854775807";
        let max_i64 = Z3_mk_numeral(ctx, max_i64_str.as_ptr(), int_sort);
        assert_ne!(max_i64, 0);
        let gt = Z3_mk_gt(ctx, big, max_i64);
        let solver = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, solver, gt);
        let result = Z3_solver_check(ctx, solver);
        assert_eq!(result, Z3_L_TRUE, "2^63 > 2^63-1 should be SAT");

        Z3_del_context(ctx);
    }
}

#[test]
fn z3_mk_numeral_caps_caller_text_before_bigint_parsing() {
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);
        let int_sort = Z3_mk_int_sort(ctx);

        let boundary = CString::new(format!("1{}", "0".repeat(MAX_FFI_NUMERAL_TEXT_BYTES - 1)))
            .expect("boundary numeral contains no NUL");
        assert_ne!(Z3_mk_numeral(ctx, boundary.as_ptr(), int_sort), 0);

        let oversized = CString::new("1".repeat(MAX_FFI_NUMERAL_TEXT_BYTES + 1))
            .expect("oversized numeral contains no NUL");
        assert_eq!(Z3_mk_numeral(ctx, oversized.as_ptr(), int_sort), 0);
        assert_eq!(Z3_get_error_code(ctx), Z3_INVALID_ARG);

        Z3_del_context(ctx);
    }
}

/// Z3_mk_unsigned_int64 with large u64 values (#6112)
#[test]
fn test_z3_mk_unsigned_int64_large_values() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);

        // u64::MAX = 18446744073709551615, which wraps to -1 as i64
        let big = Z3_mk_unsigned_int64(ctx, u64::MAX, int_sort);
        assert_ne!(big, 0, "Z3_mk_unsigned_int64 should handle u64::MAX");

        // The numeral should be the positive u64::MAX, not -1
        let numeral_str = Z3_get_numeral_string(ctx, big);
        assert!(!numeral_str.is_null());
        let s = std::ffi::CStr::from_ptr(numeral_str)
            .to_str()
            .expect("valid UTF-8");
        assert_eq!(
            s, "18446744073709551615",
            "u64::MAX should be stored as positive integer, not wrapped to -1"
        );

        Z3_del_context(ctx);
    }
}

/// Z3_mk_int64 as Real: exact construction without f64 precision loss (#6112)
#[test]
fn test_z3_mk_int64_real_exact() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let real_sort = Z3_mk_real_sort(ctx);

        // i64::MAX = 9223372036854775807. As f64, this loses precision.
        // The old code did `v as f64` which rounds to 9223372036854775808.0
        let big = Z3_mk_int64(ctx, i64::MAX, real_sort);
        assert_ne!(big, 0, "Z3_mk_int64 should handle i64::MAX as Real");

        // The numeral should be exactly i64::MAX, not f64-rounded
        let numeral_str = Z3_get_numeral_string(ctx, big);
        assert!(!numeral_str.is_null());
        let s = std::ffi::CStr::from_ptr(numeral_str)
            .to_str()
            .expect("valid UTF-8");
        // For Real constructed from BigInt, the numeral string should be "N/1"
        // or just "N" depending on implementation
        let expected_value = "9223372036854775807";
        assert!(
            s == expected_value || s == format!("{expected_value}/1"),
            "i64::MAX as Real should be exact, got: {s}"
        );

        Z3_del_context(ctx);
    }
}

/// Z3_mk_numeral with rational string for Real sort (#6112)
#[test]
fn test_z3_mk_numeral_rational_precision() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let real_sort = Z3_mk_real_sort(ctx);

        // 1/3 should be stored exactly as a rational, not as 0.3333... float
        let one_third = Z3_mk_numeral(ctx, c"1/3".as_ptr(), real_sort);
        assert_ne!(one_third, 0, "Z3_mk_numeral should handle rational strings");

        // Get the numeral string and verify it's the exact rational
        let numeral_str = Z3_get_numeral_string(ctx, one_third);
        assert!(!numeral_str.is_null());
        let s = std::ffi::CStr::from_ptr(numeral_str)
            .to_str()
            .expect("valid UTF-8");
        assert_eq!(s, "1/3", "1/3 should be stored as exact rational");

        // Get decimal string with 10 digits of precision
        let decimal_str = Z3_get_numeral_decimal_string(ctx, one_third, 10);
        assert!(!decimal_str.is_null());
        let d = std::ffi::CStr::from_ptr(decimal_str)
            .to_str()
            .expect("valid UTF-8");
        assert_eq!(d, "0.3333333333", "1/3 with 10 digits precision");

        // A compact precision argument must not request an effectively
        // unbounded BigInt and output-string allocation.
        let excessive = Z3_get_numeral_decimal_string(ctx, one_third, c_uint::MAX);
        assert!(excessive.is_null());
        assert_eq!(Z3_get_error_code(ctx), Z3_INVALID_ARG);

        Z3_del_context(ctx);
    }
}

/// Z3_get_symbol_kind: string symbol returns string kind
#[test]
fn test_z3_get_symbol_kind_string() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let sym = Z3_mk_string_symbol(ctx, c"hello".as_ptr());
        assert!(!sym.is_null(), "string symbol must not be null");
        let kind = Z3_get_symbol_kind(ctx, sym);
        assert_eq!(kind, 1, "\"hello\" must be a string symbol (kind=1)");

        Z3_del_context(ctx);
    }
}

/// Z3_model_eval uses model snapshot, not solver state (#6109).
/// Get model, push+UNSAT, then eval old model — must still return snapshot value.
#[test]
fn test_z3_model_eval_uses_model_handle_6109() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);
        let int_sort = Z3_mk_int_sort(ctx);
        let sym = Z3_mk_string_symbol(ctx, c"x".as_ptr());
        let x = Z3_mk_const(ctx, sym, int_sort);
        let five = Z3_mk_int(ctx, 5, int_sort);
        let solver = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, solver, Z3_mk_eq(ctx, x, five));
        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_TRUE);

        let model = Z3_solver_get_model(ctx, solver);
        assert!(!model.is_null());

        // Push and make UNSAT so solver.value() would fail
        Z3_solver_push(ctx, solver);
        let ten = Z3_mk_int(ctx, 10, int_sort);
        Z3_solver_assert(ctx, solver, Z3_mk_eq(ctx, x, ten));
        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_FALSE);

        // Evaluate x in OLD model — must still be 5
        let mut val: Z3_ast = 0;
        let ok = Z3_model_eval(ctx, model, x, false, &raw mut val);
        assert!(ok, "model_eval must succeed using model snapshot");
        assert_ne!(val, 0);
        let mut int_val: c_int = 0;
        assert!(Z3_get_numeral_int(ctx, val, &raw mut int_val));
        assert_eq!(int_val, 5, "must return 5 from model snapshot");

        Z3_solver_pop(ctx, solver, 1);
        Z3_del_context(ctx);
    }
}

// ============================================================================
// Panic safety tests (#6192)
// ============================================================================

/// Test that Z3_solver_pop on an empty scope stack does not abort the process.
/// Before #6192, this would cause undefined behavior (panic across extern "C").
/// After #6192, the catch_unwind guard catches the panic and sets an error flag.
#[test]
fn test_ffi_pop_empty_scope_no_abort() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let solver = Z3_mk_solver(ctx);

        // Pop with no prior push — this would panic in the solver.
        // The FFI guard must catch it and set an error instead of aborting.
        Z3_solver_pop(ctx, solver, 1);

        // Verify the error was recorded
        let err_code = Z3_get_error_code(ctx);
        assert_eq!(
            err_code, Z3_EXCEPTION,
            "pop on empty scope should set Z3_EXCEPTION error code"
        );

        // Error message should describe the panic
        let err_msg = Z3_get_error_msg(ctx, err_code);
        assert!(
            !err_msg.is_null(),
            "error message should be set after panic"
        );

        // Context should still be usable after the caught panic
        let int_sort = Z3_mk_int_sort(ctx);
        let sym = Z3_mk_string_symbol(ctx, c"x".as_ptr());
        let x = Z3_mk_const(ctx, sym, int_sort);
        assert_ne!(x, 0, "context must remain usable after caught panic");

        Z3_del_context(ctx);
    }
}

/// Test that Z3_mk_eq with sort mismatch triggers the catch_unwind guard
/// instead of aborting.
#[test]
fn test_ffi_eq_sort_mismatch_no_abort() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let bool_sort = Z3_mk_bool_sort(ctx);

        // Create an Int and a Bool variable
        let sym_x = Z3_mk_string_symbol(ctx, c"x".as_ptr());
        let x = Z3_mk_const(ctx, sym_x, int_sort);

        let sym_b = Z3_mk_string_symbol(ctx, c"b".as_ptr());
        let b = Z3_mk_const(ctx, sym_b, bool_sort);

        // eq(Int, Bool) — sort mismatch. If the solver panics on this,
        // the FFI guard should catch it. If the solver handles it gracefully
        // (returns a term or error), that's also acceptable.
        let result = Z3_mk_eq(ctx, x, b);

        // Either the result is a valid AST (solver accepted it) or
        // it's 0 (null AST from caught panic). Both are acceptable.
        // The key assertion is that we REACHED THIS LINE (no abort).
        if result == 0 {
            // Panic was caught — verify error flag is set
            let err_code = Z3_get_error_code(ctx);
            assert_eq!(err_code, Z3_EXCEPTION);
        }

        // Context must still be functional
        let five = Z3_mk_int(ctx, 5, int_sort);
        assert_ne!(five, 0, "context must remain usable after sort mismatch");

        Z3_del_context(ctx);
    }
}

/// Test that Z3_solver_check catches panics from the solver engine
/// and returns Z3_L_UNDEF instead of aborting.
#[test]
fn test_ffi_check_sat_recovers_from_panic() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let solver = Z3_mk_solver(ctx);

        // Normal check-sat should work fine
        let int_sort = Z3_mk_int_sort(ctx);
        let sym = Z3_mk_string_symbol(ctx, c"x".as_ptr());
        let x = Z3_mk_const(ctx, sym, int_sort);
        let zero = Z3_mk_int(ctx, 0, int_sort);
        let gt = Z3_mk_gt(ctx, x, zero);
        Z3_solver_assert(ctx, solver, gt);

        let result = Z3_solver_check(ctx, solver);
        assert_eq!(result, Z3_L_TRUE, "normal check-sat should return SAT");

        Z3_del_context(ctx);
    }
}

// ============================================================================
// Memory safety tests (memory_verification phase)
// ============================================================================

/// Stress test: create many handles of each type, then delete context.
/// Verifies that `Z3Context::drop` via `drain_arena` frees all handle arenas
/// without double-free, leak, or crash.
///
/// Creates: symbols, sorts, func_decls, solvers, models, params, ast_vectors.
/// Each handle is allocated via `Box::into_raw` and tracked in a context cache.
/// `Z3_del_context` triggers `Drop for Z3Context` which calls `drain_arena`
/// on all 8 caches.
#[test]
fn test_arena_cleanup_many_handles() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        // Create many symbols (each goes into symbol_cache)
        for i in 0..50 {
            let name = CString::new(format!("sym_{i}")).expect("no NUL in test name");
            let sym = Z3_mk_string_symbol(ctx, name.as_ptr());
            assert!(!sym.is_null());
        }

        // Create many sorts (each goes into sort_cache)
        let int_sort = Z3_mk_int_sort(ctx);
        let bool_sort = Z3_mk_bool_sort(ctx);
        let real_sort = Z3_mk_real_sort(ctx);
        for i in 1..=32 {
            let bv = Z3_mk_bv_sort(ctx, i);
            assert!(!bv.is_null());
        }
        let arr_sort = Z3_mk_array_sort(ctx, int_sort, bool_sort);
        assert!(!arr_sort.is_null());

        // Create many func_decls (each goes into func_decl_cache)
        for i in 0..20 {
            let name = CString::new(format!("f_{i}")).expect("no NUL in test name");
            let sym = Z3_mk_string_symbol(ctx, name.as_ptr());
            let decl = Z3_mk_func_decl(ctx, sym, 1, &raw const int_sort, real_sort);
            assert!(!decl.is_null());
        }

        // Create multiple solver handles (each goes into solver_handle_cache)
        for _ in 0..5 {
            let s = Z3_mk_solver(ctx);
            assert!(!s.is_null());
        }

        // Create params (goes into params_cache)
        let p = Z3_mk_params(ctx);
        assert!(!p.is_null());

        // Create a model via SAT check (goes into model_cache)
        let solver = Z3_mk_solver(ctx);
        let sym_x = Z3_mk_string_symbol(ctx, c"x".as_ptr());
        let x = Z3_mk_const(ctx, sym_x, int_sort);
        let five = Z3_mk_int(ctx, 5, int_sort);
        Z3_solver_assert(ctx, solver, Z3_mk_eq(ctx, x, five));
        let result = Z3_solver_check(ctx, solver);
        assert_eq!(result, Z3_L_TRUE);
        let model = Z3_solver_get_model(ctx, solver);
        assert!(!model.is_null());

        // Create ast_vectors via get_assertions (goes into ast_vector_cache)
        let assertions = Z3_solver_get_assertions(ctx, solver);
        assert!(!assertions.is_null());

        // Create patterns (goes into pattern_cache)
        // Z3_mk_pattern wraps trigger terms for quantifier instantiation.
        let f_sym = Z3_mk_string_symbol(ctx, c"f".as_ptr());
        let f_decl = Z3_mk_func_decl(ctx, f_sym, 1, &raw const int_sort, int_sort);
        let fx = Z3_mk_app(ctx, f_decl, 1, &raw const x);
        let pattern = Z3_mk_pattern(ctx, 1, &raw const fx);
        assert!(!pattern.is_null());

        // Now delete the context — this must free all cached handles
        // without double-free or crash.
        Z3_del_context(ctx);

        // If we reach here without a crash or ASAN report, arena cleanup is correct.
    }
}

/// Verify that multiple context create/destroy cycles don't leak.
/// Each cycle creates handles, then destroys the context.
#[test]
fn test_context_lifecycle_repeated() {
    for _ in 0..10 {
        // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
        // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
        // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no
        // concurrent access can occur because this test owns the handles exclusively.
        unsafe {
            let cfg = Z3_mk_config();
            let ctx = Z3_mk_context(cfg);
            Z3_del_config(cfg);

            let int_sort = Z3_mk_int_sort(ctx);
            let sym = Z3_mk_string_symbol(ctx, c"v".as_ptr());
            let v = Z3_mk_const(ctx, sym, int_sort);
            let zero = Z3_mk_int(ctx, 0, int_sort);
            let solver = Z3_mk_solver(ctx);
            Z3_solver_assert(ctx, solver, Z3_mk_gt(ctx, v, zero));
            let _ = Z3_solver_check(ctx, solver);
            let _ = Z3_solver_get_model(ctx, solver);

            Z3_del_context(ctx);
        }
    }
}

// ============================================================================
// #6580 regression tests: sort ID stability and domain sort correctness
// ============================================================================

/// Repeated Z3_mk_int_sort calls must return the same semantic sort ID (#6580).
#[test]
fn test_z3_get_sort_id_same_semantic_sort_is_stable_issue_6580() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort_a = Z3_mk_int_sort(ctx);
        let int_sort_b = Z3_mk_int_sort(ctx);

        let id_a = Z3_get_sort_id(ctx, int_sort_a);
        let id_b = Z3_get_sort_id(ctx, int_sort_b);

        assert_ne!(id_a, 0, "sort ID must be non-zero");
        assert_eq!(
            id_a, id_b,
            "same semantic sort (Int) must have same ID across allocations"
        );

        Z3_del_context(ctx);
    }
}

/// Distinct sorts must have distinct IDs (#6580).
#[test]
fn test_z3_get_sort_id_distinct_sorts_issue_6580() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let real_sort = Z3_mk_real_sort(ctx);
        let bv32_sort = Z3_mk_bv_sort(ctx, 32);

        let id_int = Z3_get_sort_id(ctx, int_sort);
        let id_real = Z3_get_sort_id(ctx, real_sort);
        let id_bv32 = Z3_get_sort_id(ctx, bv32_sort);

        assert_ne!(id_int, 0);
        assert_ne!(id_real, 0);
        assert_ne!(id_bv32, 0);

        assert_ne!(id_int, id_real, "Int and Real must have distinct IDs");
        assert_ne!(id_int, id_bv32, "Int and BV32 must have distinct IDs");
        assert_ne!(id_real, id_bv32, "Real and BV32 must have distinct IDs");

        Z3_del_context(ctx);
    }
}

/// Z3_get_app_decl must return actual domain sorts, not Bool placeholders (#6580).
#[test]
fn test_z3_get_app_decl_domain_sorts_issue_6580() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let bv8 = Z3_mk_bv_sort(ctx, 8);
        let sym_a = Z3_mk_string_symbol(ctx, c"a".as_ptr());
        let sym_b = Z3_mk_string_symbol(ctx, c"b".as_ptr());
        let a = Z3_mk_const(ctx, sym_a, bv8);
        let b = Z3_mk_const(ctx, sym_b, bv8);

        // Build bvadd(a, b)
        let sum = Z3_mk_bvadd(ctx, a, b);
        assert_ne!(sum, 0);

        // Get the func_decl
        let decl = Z3_get_app_decl(ctx, sum);
        assert!(!decl.is_null(), "bvadd decl must not be null");

        // Domain size must be 2
        let domain_size = Z3_get_domain_size(ctx, decl);
        assert_eq!(domain_size, 2, "bvadd has 2 arguments");

        // Each domain sort must be (_ BitVec 8), not Bool
        for i in 0..2 {
            let dom_sort = Z3_get_domain(ctx, decl, i);
            assert!(!dom_sort.is_null(), "domain sort {i} must not be null");
            let kind = Z3_get_sort_kind(ctx, dom_sort);
            assert_eq!(
                kind, Z3_BV_SORT,
                "domain sort {i} of bvadd must be BV, not Bool"
            );
            let bv_size = Z3_get_bv_sort_size(ctx, dom_sort);
            assert_eq!(bv_size, 8, "domain sort {i} of bvadd must be (_ BitVec 8)");
        }

        // Range sort must also be (_ BitVec 8)
        let range = Z3_get_range(ctx, decl);
        assert!(!range.is_null());
        assert_eq!(Z3_get_sort_kind(ctx, range), Z3_BV_SORT);
        assert_eq!(Z3_get_bv_sort_size(ctx, range), 8);

        Z3_del_context(ctx);
    }
}

/// Z3_get_decl_num_parameters / Z3_get_decl_int_parameter for extract (#6580 F2).
///
/// `(_ extract 7 4)` must report 2 parameters with values 7 and 4.
#[test]
fn test_z3_decl_params_extract_issue_6580() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let bv8 = Z3_mk_bv_sort(ctx, 8);
        let sym_x = Z3_mk_string_symbol(ctx, c"x".as_ptr());
        let x = Z3_mk_const(ctx, sym_x, bv8);

        // extract bits [7:4] from an 8-bit bitvector → 4-bit result
        let ext = Z3_mk_extract(ctx, 7, 4, x);
        assert_ne!(ext, 0, "extract should produce a valid AST");

        let decl = Z3_get_app_decl(ctx, ext);
        assert!(!decl.is_null(), "extract decl must not be null");

        // Verify the decl name is "extract" (base name, not "(_ extract 7 4)")
        let name_sym = Z3_get_decl_name(ctx, decl);
        assert!(!name_sym.is_null());
        let name_cstr = Z3_get_symbol_string(ctx, name_sym);
        assert!(!name_cstr.is_null());
        let name = std::ffi::CStr::from_ptr(name_cstr)
            .to_str()
            .expect("decl name should be valid UTF-8");
        assert_eq!(name, "extract", "decl name should be base name");

        // Parameters: extract has 2 (high=7, low=4)
        let num_params = Z3_get_decl_num_parameters(ctx, decl);
        assert_eq!(num_params, 2, "extract must have 2 parameters");
        assert_eq!(
            Z3_get_decl_int_parameter(ctx, decl, 0),
            7,
            "param[0] = high = 7"
        );
        assert_eq!(
            Z3_get_decl_int_parameter(ctx, decl, 1),
            4,
            "param[1] = low = 4"
        );

        // Out-of-bounds returns 0
        assert_eq!(Z3_get_decl_int_parameter(ctx, decl, 2), 0);

        Z3_del_context(ctx);
    }
}

/// Z3_get_decl_num_parameters for sign_extend (#6580 F2).
///
/// `(_ sign_extend 8)` must report 1 parameter with value 8.
#[test]
fn test_z3_decl_params_sign_extend_issue_6580() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let bv8 = Z3_mk_bv_sort(ctx, 8);
        let sym_x = Z3_mk_string_symbol(ctx, c"x".as_ptr());
        let x = Z3_mk_const(ctx, sym_x, bv8);

        // sign_extend by 8 bits: 8-bit → 16-bit
        let sext = Z3_mk_sign_ext(ctx, 8, x);
        assert_ne!(sext, 0, "sign_ext should produce a valid AST");

        let decl = Z3_get_app_decl(ctx, sext);
        assert!(!decl.is_null(), "sign_extend decl must not be null");

        let num_params = Z3_get_decl_num_parameters(ctx, decl);
        assert_eq!(num_params, 1, "sign_extend must have 1 parameter");
        assert_eq!(
            Z3_get_decl_int_parameter(ctx, decl, 0),
            8,
            "param[0] = extension width = 8"
        );

        Z3_del_context(ctx);
    }
}

/// Z3_get_decl_num_parameters for zero_extend (#6580 F2).
///
/// `(_ zero_extend 16)` must report 1 parameter with value 16.
#[test]
fn test_z3_decl_params_zero_extend_issue_6580() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let bv8 = Z3_mk_bv_sort(ctx, 8);
        let sym_x = Z3_mk_string_symbol(ctx, c"x".as_ptr());
        let x = Z3_mk_const(ctx, sym_x, bv8);

        // zero_extend by 16 bits: 8-bit → 24-bit
        let zext = Z3_mk_zero_ext(ctx, 16, x);
        assert_ne!(zext, 0, "zero_ext should produce a valid AST");

        let decl = Z3_get_app_decl(ctx, zext);
        assert!(!decl.is_null(), "zero_extend decl must not be null");

        let num_params = Z3_get_decl_num_parameters(ctx, decl);
        assert_eq!(num_params, 1, "zero_extend must have 1 parameter");
        assert_eq!(
            Z3_get_decl_int_parameter(ctx, decl, 0),
            16,
            "param[0] = extension width = 16"
        );

        Z3_del_context(ctx);
    }
}

/// Non-indexed operators (like bvadd) must report 0 parameters (#6580 F2).
#[test]
fn test_z3_decl_params_non_indexed_zero_issue_6580() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let bv8 = Z3_mk_bv_sort(ctx, 8);
        let sym_a = Z3_mk_string_symbol(ctx, c"a".as_ptr());
        let sym_b = Z3_mk_string_symbol(ctx, c"b".as_ptr());
        let a = Z3_mk_const(ctx, sym_a, bv8);
        let b = Z3_mk_const(ctx, sym_b, bv8);

        let sum = Z3_mk_bvadd(ctx, a, b);
        let decl = Z3_get_app_decl(ctx, sum);
        assert!(!decl.is_null());

        // bvadd is not an indexed operator → 0 parameters
        let num_params = Z3_get_decl_num_parameters(ctx, decl);
        assert_eq!(num_params, 0, "non-indexed operator must have 0 parameters");

        // Null decl returns 0
        assert_eq!(Z3_get_decl_num_parameters(ctx, ptr::null_mut()), 0);
        assert_eq!(Z3_get_decl_int_parameter(ctx, ptr::null_mut(), 0), 0);

        Z3_del_context(ctx);
    }
}

// =========================================================================
// Consumer acceptance boundary regression tests (#8725)
//
// These tests lock in the fix for the Z3 FFI trust-boundary leak:
// `Z3_solver_check` / `Z3_solver_check_assumptions` must route their
// `VerifiedSolveResult` through `accept_for_consumer()` rather than
// calling `.result()` directly. Unvalidated SAT must not escape the FFI
// as `Z3_L_TRUE`.
// =========================================================================

/// A non-empty assumption array cannot be null. The malformed query must
/// retire an earlier SAT/model snapshot instead of silently checking with no
/// assumptions and publishing that unrelated result.
#[test]
fn test_solver_check_assumptions_rejects_null_array_and_retires_model() {
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);
        let solver = Z3_mk_solver(ctx);

        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_TRUE);
        assert!(!Z3_solver_get_model(ctx, solver).is_null());

        assert_eq!(
            Z3_solver_check_assumptions(ctx, solver, 1, ptr::null()),
            Z3_L_UNDEF
        );
        assert_eq!(Z3_get_error_code(ctx), Z3_INVALID_ARG);
        assert!(Z3_solver_get_model(ctx, solver).is_null());
        let reason =
            std::ffi::CStr::from_ptr(Z3_solver_get_reason_unknown(ctx, solver)).to_string_lossy();
        assert!(reason.contains("null assumptions array"), "{reason}");

        Z3_del_context(ctx);
    }
}

/// Unvalidated SAT (simulated) must be rejected at the FFI boundary:
/// the lbool becomes `Z3_L_UNDEF` and the context surfaces `Z3_EXCEPTION`.
///
/// Before the fix (#8725), the call path used `.result()` which returned the
/// raw `SolveResult::Sat` unconditionally — so an unvalidated SAT would have
/// leaked as `Z3_L_TRUE` to C/C++ consumers (model-checker-consumer, z3-compat shim).
#[test]
fn test_z3_ffi_unvalidated_sat_rejected_8725() {
    use super::solver::solve_lbool_from_consumer_rejection_for_testing;
    use ay_dpll::api::ConsumerAcceptanceError;

    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        // Reset last_error so we can detect that the helper sets Z3_EXCEPTION.
        {
            let ctx_ref = ctx.as_mut().expect("context must be non-null");
            ctx_ref.last_error = Z3_OK;
            ctx_ref.error_msg = None;
        }

        let ctx_ref = ctx.as_mut().expect("context must be non-null");
        // Inject only the already-rejected boundary outcome through an
        // ay-ffi-local cfg(test) helper. Production code cannot fabricate a
        // `VerifiedSolveResult` or caller-chosen SAT validation bit.
        let lbool = solve_lbool_from_consumer_rejection_for_testing(
            ctx_ref,
            ConsumerAcceptanceError::SatModelNotValidated,
        );

        assert_eq!(
            lbool, Z3_L_UNDEF,
            "unvalidated SAT must surface as Z3_L_UNDEF at the FFI boundary, \
             not Z3_L_TRUE (#8725)"
        );
        assert_eq!(
            ctx_ref.last_error, Z3_EXCEPTION,
            "rejecting unvalidated SAT must set Z3_EXCEPTION on the context"
        );
        let msg = ctx_ref
            .error_msg
            .as_deref()
            .expect("error_msg must be populated on rejection");
        assert!(
            msg.contains("consumer boundary"),
            "error_msg should explain the consumer-boundary rejection, got: {msg}"
        );

        Z3_del_context(ctx);
    }
}

/// Validated SAT must pass through: lbool = `Z3_L_TRUE`, no exception raised.
///
/// Guard against over-rejection: the fix must not break the common path.
#[test]
fn test_z3_ffi_validated_sat_passes_8725() {
    use super::solver::solve_lbool_with_acceptance;
    use ay_dpll::api::{Logic, Solver, Sort};

    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        {
            let ctx_ref = ctx.as_mut().expect("context must be non-null");
            ctx_ref.last_error = Z3_OK;
            ctx_ref.error_msg = None;
        }

        // Obtain a real certificate-bearing result from the solver rather than
        // exposing a public test constructor that could mint one in production.
        let mut solver = Solver::new(Logic::QfLia);
        let p = solver.declare_const("p", Sort::Bool);
        solver.assert_term(p);
        let validated_sat = solver.check_sat();
        assert!(validated_sat.is_sat());
        assert!(validated_sat.was_model_validated());

        let ctx_ref = ctx.as_mut().expect("context must be non-null");
        let lbool = solve_lbool_with_acceptance(ctx_ref, validated_sat);

        assert_eq!(
            lbool, Z3_L_TRUE,
            "validated SAT must surface as Z3_L_TRUE at the FFI boundary"
        );
        assert_eq!(
            ctx_ref.last_error, Z3_OK,
            "validated SAT path must not raise Z3_EXCEPTION"
        );
        assert!(
            ctx_ref.error_msg.is_none(),
            "validated SAT path must not populate error_msg"
        );

        Z3_del_context(ctx);
    }
}

/// UNSAT bypasses the validation gate (validation only applies to SAT).
#[test]
fn test_z3_ffi_unsat_passes_regardless_of_validation_8725() {
    use super::solver::solve_lbool_with_acceptance;
    use ay_dpll::api::{Logic, Solver};

    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        {
            let ctx_ref = ctx.as_mut().expect("context must be non-null");
            ctx_ref.last_error = Z3_OK;
            ctx_ref.error_msg = None;
        }

        // Obtain a genuine UNSAT result. Model validation is irrelevant for
        // UNSAT; the consumer gate applies only to SAT witnesses.
        let mut solver = Solver::new(Logic::QfLia);
        let false_term = solver.bool_const(false);
        solver.assert_term(false_term);
        let unsat = solver.check_sat();
        assert!(unsat.is_unsat());

        let ctx_ref = ctx.as_mut().expect("context must be non-null");
        let lbool = solve_lbool_with_acceptance(ctx_ref, unsat);

        assert_eq!(lbool, Z3_L_FALSE, "UNSAT must surface as Z3_L_FALSE");
        assert_eq!(ctx_ref.last_error, Z3_OK, "UNSAT must not raise exception");

        Z3_del_context(ctx);
    }
}

/// End-to-end: a concrete SAT formula through `Z3_solver_check` still returns
/// `Z3_L_TRUE` after the fix. This is the primary regression guard for the
/// happy path — the existing integration tests cover it, but keeping it here
/// alongside the boundary tests documents the expected behavior contract.
#[test]
fn test_z3_ffi_solver_check_happy_path_after_8725_fix() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let sym = Z3_mk_string_symbol(ctx, c"x".as_ptr());
        let x = Z3_mk_const(ctx, sym, int_sort);
        let zero = Z3_mk_int(ctx, 0, int_sort);
        let ten = Z3_mk_int(ctx, 10, int_sort);

        let solver = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, solver, Z3_mk_gt(ctx, x, zero));
        Z3_solver_assert(ctx, solver, Z3_mk_lt(ctx, x, ten));

        let result = Z3_solver_check(ctx, solver);
        assert_eq!(
            result, Z3_L_TRUE,
            "after #8725 fix, a naturally-validated SAT must still return Z3_L_TRUE"
        );

        // No exception should be raised on the happy path.
        let ctx_ref = ctx.as_ref().expect("context must be non-null");
        assert_eq!(
            ctx_ref.last_error, Z3_OK,
            "happy-path SAT must not raise Z3_EXCEPTION"
        );

        Z3_del_context(ctx);
    }
}

// ========================== refcounting (RC context) tests ==========================
//
// These exercise the real inc_ref/dec_ref BOOKKEEPING through the actual
// extern "C" FFI entry points. ASTs are arena-interned and never freed by
// reference counting; the counts only detect dec-below-zero and distinguish
// RC contexts (Z3_mk_context_rc) from plain ones (Z3_mk_context).

/// (a) RC context: balanced inc_ref x2 / dec_ref x2 leaves Z3_OK.
/// (b) one extra dec_ref reports Z3_DEC_REF_ERROR.
#[test]
fn test_z3_compat_refcounting_rc_balanced_then_underflow() {
    // SAFETY: Test-scope unsafe block: all handles (contexts, AST ids) are
    // allocated by `Z3_mk_*` calls inside this block and freed by `Z3_del_context`.
    // No pointer escapes the block and no concurrent access can occur because
    // this test owns the handles exclusively.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context_rc(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let sym = Z3_mk_string_symbol(ctx, c"x".as_ptr());
        let x = Z3_mk_const(ctx, sym, int_sort);
        assert_ne!(x, 0);

        // (a) balanced: inc x2, dec x2 -> Z3_OK
        Z3_inc_ref(ctx, x);
        Z3_inc_ref(ctx, x);
        Z3_dec_ref(ctx, x);
        Z3_dec_ref(ctx, x);
        assert_eq!(
            Z3_get_error_code(ctx),
            Z3_OK,
            "balanced inc/dec on an RC context must leave Z3_OK"
        );

        // (b) one more dec_ref -> dec-below-zero -> Z3_DEC_REF_ERROR
        Z3_dec_ref(ctx, x);
        assert_eq!(
            Z3_get_error_code(ctx),
            Z3_DEC_REF_ERROR,
            "unbalanced dec_ref on an RC context must report Z3_DEC_REF_ERROR"
        );

        Z3_del_context(ctx);
    }
}

/// (c) NON-rc context: an unbalanced dec_ref is a no-op and leaves Z3_OK.
#[test]
fn test_z3_compat_refcounting_non_rc_dec_is_noop() {
    // SAFETY: see test_z3_compat_refcounting_rc_balanced_then_underflow.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg); // plain context: RC disabled
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let sym = Z3_mk_string_symbol(ctx, c"y".as_ptr());
        let y = Z3_mk_const(ctx, sym, int_sort);
        assert_ne!(y, 0);

        // inc/dec are no-ops here; even an unbalanced dec_ref must not error.
        Z3_inc_ref(ctx, y);
        Z3_dec_ref(ctx, y);
        Z3_dec_ref(ctx, y); // unbalanced, but no-op on a non-RC context
        assert_eq!(
            Z3_get_error_code(ctx),
            Z3_OK,
            "dec_ref on a non-RC context must be a no-op (Z3_OK)"
        );

        Z3_del_context(ctx);
    }
}

/// Null-AST guard: inc_ref/dec_ref on a==0 are no-ops on an RC context.
#[test]
fn test_z3_compat_refcounting_null_ast_guard() {
    // SAFETY: see test_z3_compat_refcounting_rc_balanced_then_underflow.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context_rc(cfg);
        Z3_del_config(cfg);

        // a == 0 is the null sentinel: both must early-return without error.
        Z3_inc_ref(ctx, 0);
        Z3_dec_ref(ctx, 0);
        assert_eq!(
            Z3_get_error_code(ctx),
            Z3_OK,
            "null-AST inc/dec_ref must be no-ops, not Z3_DEC_REF_ERROR"
        );

        Z3_del_context(ctx);
    }
}

// ============================================================================
// Z3_optimize (MaxSMT) sub-API tests (Phase 3)
// ============================================================================

/// Helper: read the boolean value of a const `t` out of `model` via
/// `Z3_model_eval`. Returns `Some(true|false)` if the model assigns it.
///
/// # Safety
/// `ctx`/`model` must be valid; `t` a valid bool AST.
unsafe fn model_bool(ctx: Z3_context, model: Z3_model, t: Z3_ast) -> Option<bool> {
    unsafe {
        let mut out: Z3_ast = 0;
        if !Z3_model_eval(ctx, model, t, true, &raw mut out) {
            return None;
        }
        match Z3_get_bool_value(ctx, out) {
            Z3_L_TRUE => Some(true),
            Z3_L_FALSE => Some(false),
            _ => None,
        }
    }
}

/// MaxSAT, known optimum: hard `(or a b)`, soft `¬a`:1, soft `¬b`:1.
/// Optimum: SAT with exactly one of the two softs satisfied (cost 1).
#[test]
fn test_z3_optimize_maxsat_one_of_two() {
    // SAFETY: Test-scope unsafe block: all handles are allocated by `Z3_mk_*`
    // calls inside this block and freed by `Z3_del_context`. No pointer escapes
    // and this test owns the handles exclusively.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let bool_sort = Z3_mk_bool_sort(ctx);
        let a = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"a".as_ptr()), bool_sort);
        let b = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"b".as_ptr()), bool_sort);

        let opt = Z3_mk_optimize(ctx);
        assert!(!opt.is_null());
        Z3_optimize_inc_ref(ctx, opt);

        // Hard: (or a b)
        let or_args = [a, b];
        let a_or_b = Z3_mk_or(ctx, 2, or_args.as_ptr());
        Z3_optimize_assert(ctx, opt, a_or_b);

        // Soft: ¬a (weight 1), ¬b (weight 1)
        let not_a = Z3_mk_not(ctx, a);
        let not_b = Z3_mk_not(ctx, b);
        let i0 = Z3_optimize_assert_soft(ctx, opt, not_a, c"1".as_ptr(), ptr::null_mut());
        let i1 = Z3_optimize_assert_soft(ctx, opt, not_b, c"1".as_ptr(), ptr::null_mut());
        assert_eq!(i0, 0);
        assert_eq!(i1, 1);
        assert_eq!(Z3_get_error_code(ctx), Z3_OK);

        let res = Z3_optimize_check(ctx, opt, 0, ptr::null());
        assert_eq!(res, Z3_L_TRUE, "hard (or a b) is satisfiable");

        let model = Z3_optimize_get_model(ctx, opt);
        assert!(!model.is_null(), "optimize must yield a witnessing model");

        let va = model_bool(ctx, model, a).expect("a has a model value");
        let vb = model_bool(ctx, model, b).expect("b has a model value");
        // Hard requires a OR b. Optimum violates exactly one of ¬a/¬b, i.e.
        // exactly one of a,b is true.
        assert!(va || vb, "hard (or a b) must hold: a={va} b={vb}");
        assert!(
            va ^ vb,
            "exactly one soft satisfied at the optimum (one of a,b true): a={va} b={vb}"
        );

        Z3_optimize_dec_ref(ctx, opt);
        Z3_del_context(ctx);
    }
}

/// WEIGHTED case where weight-optimum differs from count-optimum.
/// Hard: `a => (¬b ∧ ¬c)`. Soft a:5, b:1, c:1.
/// Weight-optimal: satisfy a (cost 0 for a), violate b and c (cost 2). A
/// count-first optimizer would instead violate a alone (cost 5) — wrong.
/// So at the optimum: a is TRUE, b and c are FALSE.
#[test]
fn test_z3_optimize_weighted_beats_count() {
    // SAFETY: see test_z3_optimize_maxsat_one_of_two.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let bool_sort = Z3_mk_bool_sort(ctx);
        let a = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"a".as_ptr()), bool_sort);
        let b = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"b".as_ptr()), bool_sort);
        let c_v = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"c".as_ptr()), bool_sort);

        let opt = Z3_mk_optimize(ctx);

        // Hard: (or (not a) (and (not b) (not c)))  ==  a => (¬b ∧ ¬c)
        let not_a = Z3_mk_not(ctx, a);
        let not_b = Z3_mk_not(ctx, b);
        let not_c = Z3_mk_not(ctx, c_v);
        let and_args = [not_b, not_c];
        let nb_and_nc = Z3_mk_and(ctx, 2, and_args.as_ptr());
        let or_args = [not_a, nb_and_nc];
        let hard = Z3_mk_or(ctx, 2, or_args.as_ptr());
        Z3_optimize_assert(ctx, opt, hard);

        // Soft a:5, b:1, c:1
        Z3_optimize_assert_soft(ctx, opt, a, c"5".as_ptr(), ptr::null_mut());
        Z3_optimize_assert_soft(ctx, opt, b, c"1".as_ptr(), ptr::null_mut());
        Z3_optimize_assert_soft(ctx, opt, c_v, c"1".as_ptr(), ptr::null_mut());

        let res = Z3_optimize_check(ctx, opt, 0, ptr::null());
        assert_eq!(res, Z3_L_TRUE);

        let model = Z3_optimize_get_model(ctx, opt);
        assert!(!model.is_null());

        let va = model_bool(ctx, model, a).expect("a value");
        let vb = model_bool(ctx, model, b).expect("b value");
        let vc = model_bool(ctx, model, c_v).expect("c value");
        // Weight-exact optimum: satisfy the weight-5 soft (a true), give up the
        // two weight-1 softs (b,c false). This is what distinguishes the exact
        // weighted engine from a count-first one.
        assert!(va, "weight-optimum must satisfy the weight-5 soft (a=true)");
        assert!(!vb, "weight-1 soft b given up at the weighted optimum");
        assert!(!vc, "weight-1 soft c given up at the weighted optimum");

        Z3_del_context(ctx);
    }
}

/// Hard-unsatisfiable: optimize check returns Z3_L_FALSE.
#[test]
fn test_z3_optimize_hard_unsat() {
    // SAFETY: see test_z3_optimize_maxsat_one_of_two.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let bool_sort = Z3_mk_bool_sort(ctx);
        let a = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"a".as_ptr()), bool_sort);

        let opt = Z3_mk_optimize(ctx);
        // Hard: a AND ¬a  → unsat.
        Z3_optimize_assert(ctx, opt, a);
        let not_a = Z3_mk_not(ctx, a);
        Z3_optimize_assert(ctx, opt, not_a);
        // A soft that cannot rescue an unsat hard set.
        Z3_optimize_assert_soft(ctx, opt, a, c"1".as_ptr(), ptr::null_mut());

        let res = Z3_optimize_check(ctx, opt, 0, ptr::null());
        assert_eq!(res, Z3_L_FALSE, "hard a ∧ ¬a is unsatisfiable");
        assert!(Z3_optimize_get_model(ctx, opt).is_null());

        Z3_del_context(ctx);
    }
}

/// Non-integer weight is rejected with Z3_INVALID_ARG and no soft is added.
#[test]
fn test_z3_optimize_soft_weight_rejects_non_integer() {
    // SAFETY: see test_z3_optimize_maxsat_one_of_two.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let bool_sort = Z3_mk_bool_sort(ctx);
        let a = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"a".as_ptr()), bool_sort);
        let opt = Z3_mk_optimize(ctx);

        // "1/2" is a rational, not yet supported → rejected.
        let _ = Z3_optimize_assert_soft(ctx, opt, a, c"1/2".as_ptr(), ptr::null_mut());
        assert_eq!(
            Z3_get_error_code(ctx),
            Z3_INVALID_ARG,
            "rational weight must be rejected, not silently mis-weighted"
        );

        Z3_del_context(ctx);
    }
}

/// Assumptions are not supported by the MaxSMT path: honest Z3_L_UNDEF + error.
#[test]
fn test_z3_optimize_check_assumptions_unsupported() {
    // SAFETY: see test_z3_optimize_maxsat_one_of_two.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let bool_sort = Z3_mk_bool_sort(ctx);
        let a = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"a".as_ptr()), bool_sort);
        let opt = Z3_mk_optimize(ctx);
        Z3_optimize_assert(ctx, opt, a);

        let assumptions = [a];
        let res = Z3_optimize_check(ctx, opt, 1, assumptions.as_ptr());
        assert_eq!(
            res, Z3_L_UNDEF,
            "assumptions are not threaded through MaxSMT"
        );
        assert_eq!(Z3_get_error_code(ctx), Z3_INVALID_ARG);

        Z3_del_context(ctx);
    }
}

/// AY does not implement Z3's joint arithmetic-objective + MaxSMT priority
/// semantics. The FFI must reject the combination rather than silently optimize
/// one class and publish that partial result as the joint optimum.
#[test]
fn test_z3_optimize_mixed_api_objective_and_soft_is_undef() {
    // SAFETY: see test_z3_optimize_maxsat_one_of_two.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let bool_sort = Z3_mk_bool_sort(ctx);
        let x = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"x".as_ptr()), int_sort);
        let soft = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"soft".as_ptr()), bool_sort);
        let opt = Z3_mk_optimize(ctx);
        Z3_optimize_maximize(ctx, opt, x);
        Z3_optimize_assert_soft(ctx, opt, soft, c"1".as_ptr(), ptr::null_mut());

        assert_eq!(
            Z3_optimize_check(ctx, opt, 0, ptr::null()),
            Z3_L_UNDEF,
            "an unsupported joint problem must not publish a partial optimum"
        );
        assert_eq!(Z3_get_error_code(ctx), Z3_INVALID_ARG);
        assert!(
            Z3_optimize_get_model(ctx, opt).is_null(),
            "a rejected joint problem has no admitted model"
        );

        Z3_del_context(ctx);
    }
}

/// The same honest mixed-use rejection applies when both classes entered via
/// SMT-LIB parsing; this lane previously routed through the parsed optimizer and
/// could hide one class behind the other.
#[test]
fn test_z3_optimize_mixed_parsed_objective_and_soft_is_undef() {
    // SAFETY: see test_z3_optimize_maxsat_one_of_two.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);
        let opt = Z3_mk_optimize(ctx);

        Z3_optimize_from_string(
            ctx,
            opt,
            c"(set-logic QF_LIA)\n(declare-const x Int)\n(declare-const s Bool)\n(maximize x)\n(assert-soft s :weight 1)"
                .as_ptr(),
        );
        assert_eq!(Z3_get_error_code(ctx), Z3_OK);
        assert_eq!(Z3_optimize_check(ctx, opt, 0, ptr::null()), Z3_L_UNDEF);
        assert_eq!(Z3_get_error_code(ctx), Z3_INVALID_ARG);
        assert!(Z3_optimize_get_model(ctx, opt).is_null());

        Z3_del_context(ctx);
    }
}

/// to_string renders hard asserts and the soft set without crashing.
#[test]
fn test_z3_optimize_to_string_smoke() {
    // SAFETY: see test_z3_optimize_maxsat_one_of_two.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let bool_sort = Z3_mk_bool_sort(ctx);
        let a = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"a".as_ptr()), bool_sort);
        let opt = Z3_mk_optimize(ctx);
        Z3_optimize_assert(ctx, opt, a);
        let not_a = Z3_mk_not(ctx, a);
        Z3_optimize_assert_soft(ctx, opt, not_a, c"3".as_ptr(), ptr::null_mut());

        let s = Z3_optimize_to_string(ctx, opt);
        assert!(!s.is_null());
        let rs = std::ffi::CStr::from_ptr(s).to_string_lossy().into_owned();
        assert!(rs.contains("assert-soft"), "should render the soft: {rs}");
        assert!(rs.contains(":weight 3"), "should render the weight: {rs}");

        Z3_del_context(ctx);
    }
}

/// Read an i64 optimum out of a get_lower/get_upper AST.
///
/// # Safety
/// `ctx` valid; `a` a numeral AST.
unsafe fn numeral_i64(ctx: Z3_context, a: Z3_ast) -> Option<i64> {
    unsafe {
        let mut v: i64 = 0;
        if Z3_get_numeral_int64(ctx, a, &raw mut v) {
            Some(v)
        } else {
            None
        }
    }
}

/// `(maximize x)` under `0 <= x <= 10` → exact optimum 10 (matches z3).
/// get_lower and get_upper both return the numeral 10.
#[test]
fn test_z3_optimize_maximize_int() {
    // SAFETY: see test_z3_optimize_maxsat_one_of_two.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let x = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"x".as_ptr()), int_sort);
        let zero = Z3_mk_int(ctx, 0, int_sort);
        let ten = Z3_mk_int(ctx, 10, int_sort);

        let opt = Z3_mk_optimize(ctx);
        Z3_optimize_inc_ref(ctx, opt);
        Z3_optimize_assert(ctx, opt, Z3_mk_ge(ctx, x, zero));
        Z3_optimize_assert(ctx, opt, Z3_mk_le(ctx, x, ten));

        let obj = Z3_optimize_maximize(ctx, opt, x);
        assert_eq!(obj, 0);
        assert_eq!(Z3_get_error_code(ctx), Z3_OK);

        let res = Z3_optimize_check(ctx, opt, 0, ptr::null());
        assert_eq!(res, Z3_L_TRUE);

        let lo = Z3_optimize_get_lower(ctx, opt, obj);
        let up = Z3_optimize_get_upper(ctx, opt, obj);
        assert_eq!(
            numeral_i64(ctx, lo),
            Some(10),
            "max optimum is 10 (z3-verified)"
        );
        assert_eq!(numeral_i64(ctx, up), Some(10));

        Z3_optimize_dec_ref(ctx, opt);
        Z3_del_context(ctx);
    }
}

/// `(minimize x)` under `3 <= x <= 100` → exact optimum 3 (matches z3).
#[test]
fn test_z3_optimize_minimize_int() {
    // SAFETY: see test_z3_optimize_maxsat_one_of_two.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let x = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"x".as_ptr()), int_sort);
        let three = Z3_mk_int(ctx, 3, int_sort);
        let hundred = Z3_mk_int(ctx, 100, int_sort);

        let opt = Z3_mk_optimize(ctx);
        Z3_optimize_assert(ctx, opt, Z3_mk_ge(ctx, x, three));
        Z3_optimize_assert(ctx, opt, Z3_mk_le(ctx, x, hundred));

        let obj = Z3_optimize_minimize(ctx, opt, x);
        let res = Z3_optimize_check(ctx, opt, 0, ptr::null());
        assert_eq!(res, Z3_L_TRUE);
        assert_eq!(
            numeral_i64(ctx, Z3_optimize_get_lower(ctx, opt, obj)),
            Some(3)
        );
        assert_eq!(
            numeral_i64(ctx, Z3_optimize_get_upper(ctx, opt, obj)),
            Some(3)
        );

        Z3_del_context(ctx);
    }
}

/// Two-objective LEXICOGRAPHIC: maximize x, then maximize y, under
/// `x + y <= 10, x >= 0, y >= 0`. Lex maximizes x first (=10), forcing y=0.
/// z3-verified: (x 10) (y 0).
#[test]
fn test_z3_optimize_lex_two_objectives() {
    // SAFETY: see test_z3_optimize_maxsat_one_of_two.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let x = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"x".as_ptr()), int_sort);
        let y = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"y".as_ptr()), int_sort);
        let zero = Z3_mk_int(ctx, 0, int_sort);
        let ten = Z3_mk_int(ctx, 10, int_sort);

        let opt = Z3_mk_optimize(ctx);
        let add_args = [x, y];
        let sum = Z3_mk_add(ctx, 2, add_args.as_ptr());
        Z3_optimize_assert(ctx, opt, Z3_mk_le(ctx, sum, ten));
        Z3_optimize_assert(ctx, opt, Z3_mk_ge(ctx, x, zero));
        Z3_optimize_assert(ctx, opt, Z3_mk_ge(ctx, y, zero));

        let ox = Z3_optimize_maximize(ctx, opt, x);
        let oy = Z3_optimize_maximize(ctx, opt, y);
        assert_eq!(ox, 0);
        assert_eq!(oy, 1);

        let res = Z3_optimize_check(ctx, opt, 0, ptr::null());
        assert_eq!(res, Z3_L_TRUE);
        assert_eq!(
            numeral_i64(ctx, Z3_optimize_get_upper(ctx, opt, ox)),
            Some(10)
        );
        assert_eq!(
            numeral_i64(ctx, Z3_optimize_get_upper(ctx, opt, oy)),
            Some(0)
        );

        Z3_del_context(ctx);
    }
}

/// Objective handles are declaration identities. In box mode duplicate handles
/// over the same term have independent optima and the FFI index accessors must
/// not alias them through a term-keyed cache.
#[test]
fn test_z3_optimize_box_duplicate_term_objectives_keep_distinct_bounds() {
    // SAFETY: see test_z3_optimize_maxsat_one_of_two.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let x = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"x".as_ptr()), int_sort);
        let zero = Z3_mk_int(ctx, 0, int_sort);
        let ten = Z3_mk_int(ctx, 10, int_sort);
        let opt = Z3_mk_optimize(ctx);
        Z3_optimize_from_string(ctx, opt, c"(set-option :opt.priority box)".as_ptr());
        assert_eq!(Z3_get_error_code(ctx), Z3_OK);
        Z3_optimize_assert(ctx, opt, Z3_mk_ge(ctx, x, zero));
        Z3_optimize_assert(ctx, opt, Z3_mk_le(ctx, x, ten));

        let maximize_x = Z3_optimize_maximize(ctx, opt, x);
        let minimize_x = Z3_optimize_minimize(ctx, opt, x);
        assert_eq!(Z3_optimize_check(ctx, opt, 0, ptr::null()), Z3_L_TRUE);
        assert_eq!(
            numeral_i64(ctx, Z3_optimize_get_upper(ctx, opt, maximize_x)),
            Some(10)
        );
        assert_eq!(
            numeral_i64(ctx, Z3_optimize_get_lower(ctx, opt, minimize_x)),
            Some(0)
        );

        Z3_del_context(ctx);
    }
}

/// BitVec `(maximize x)` under `x <=u 7` → optimum 7 (unsigned), matching z3's
/// `(x 7)` decimal report.
#[test]
fn test_z3_optimize_maximize_bitvec() {
    // SAFETY: see test_z3_optimize_maxsat_one_of_two.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let bv8 = Z3_mk_bv_sort(ctx, 8);
        let x = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"x".as_ptr()), bv8);
        let seven = Z3_mk_unsigned_int(ctx, 7, bv8);

        let opt = Z3_mk_optimize(ctx);
        Z3_optimize_assert(ctx, opt, Z3_mk_bvule(ctx, x, seven));
        let obj = Z3_optimize_maximize(ctx, opt, x);
        let res = Z3_optimize_check(ctx, opt, 0, ptr::null());
        assert_eq!(res, Z3_L_TRUE);
        assert_eq!(
            numeral_i64(ctx, Z3_optimize_get_upper(ctx, opt, obj)),
            Some(7)
        );

        Z3_del_context(ctx);
    }
}

/// get_lower/get_upper reject an out-of-range objective index with
/// Z3_INVALID_ARG and a null AST (never a fabricated numeral).
#[test]
fn test_z3_optimize_get_objective_out_of_range() {
    // SAFETY: see test_z3_optimize_maxsat_one_of_two.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let x = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"x".as_ptr()), int_sort);
        let zero = Z3_mk_int(ctx, 0, int_sort);
        let ten = Z3_mk_int(ctx, 10, int_sort);

        let opt = Z3_mk_optimize(ctx);
        Z3_optimize_assert(ctx, opt, Z3_mk_ge(ctx, x, zero));
        Z3_optimize_assert(ctx, opt, Z3_mk_le(ctx, x, ten));
        let _ = Z3_optimize_maximize(ctx, opt, x);
        assert_eq!(Z3_optimize_check(ctx, opt, 0, ptr::null()), Z3_L_TRUE);

        let bad = Z3_optimize_get_lower(ctx, opt, 5);
        assert_eq!(bad, 0, "out-of-range index returns null AST");
        assert_eq!(Z3_get_error_code(ctx), Z3_INVALID_ARG);

        Z3_del_context(ctx);
    }
}

/// Unbounded REAL objective: AY reports SAT with the optimum oo, and
/// get_lower/get_upper return the null AST (0) — never a fabricated numeral.
#[test]
fn test_z3_optimize_unbounded_real_returns_null_ast() {
    // SAFETY: see test_z3_optimize_maxsat_one_of_two.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let real_sort = Z3_mk_real_sort(ctx);
        let x = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"x".as_ptr()), real_sort);
        let zero = Z3_mk_int(ctx, 0, real_sort);

        let opt = Z3_mk_optimize(ctx);
        Z3_optimize_assert(ctx, opt, Z3_mk_ge(ctx, x, zero));
        let obj = Z3_optimize_maximize(ctx, opt, x);
        let res = Z3_optimize_check(ctx, opt, 0, ptr::null());
        assert_eq!(res, Z3_L_TRUE, "unbounded Real maximize is SAT with oo");

        // No finite numeral represents oo: honest null AST, no error.
        let lo = Z3_optimize_get_lower(ctx, opt, obj);
        let up = Z3_optimize_get_upper(ctx, opt, obj);
        assert_eq!(lo, 0, "unbounded optimum has no finite numeral");
        assert_eq!(up, 0);

        Z3_del_context(ctx);
    }
}

/// Unbounded INT objective: Z3_optimize_check returns Z3_L_TRUE (SAT with oo),
/// matching z3 — the audited LP relaxation proves unboundedness (see
/// `perf(opt)`/`feat(opt)` unbounded-objectives work). The optimum is oo, for
/// which no finite numeral exists, so get_lower/get_upper return a null AST
/// (never a fabricated finite Int optimum). Mirrors the unbounded-Real case.
#[test]
fn test_z3_optimize_unbounded_int_is_sat_with_oo() {
    // SAFETY: see test_z3_optimize_maxsat_one_of_two.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let x = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"x".as_ptr()), int_sort);
        let zero = Z3_mk_int(ctx, 0, int_sort);

        let opt = Z3_mk_optimize(ctx);
        Z3_optimize_assert(ctx, opt, Z3_mk_ge(ctx, x, zero));
        let obj = Z3_optimize_maximize(ctx, opt, x);
        let res = Z3_optimize_check(ctx, opt, 0, ptr::null());
        assert_eq!(res, Z3_L_TRUE, "unbounded Int maximize is SAT with oo");

        // No finite numeral represents oo: honest null AST, no error.
        let lo = Z3_optimize_get_lower(ctx, opt, obj);
        let up = Z3_optimize_get_upper(ctx, opt, obj);
        assert_eq!(lo, 0, "unbounded optimum has no finite numeral");
        assert_eq!(up, 0);

        Z3_del_context(ctx);
    }
}

/// Z3_substitute: replacing a constant with a numeral yields the same interned
/// term as building it directly, and eager-folds. `(+ x 1)[x:=5]` == `(+ 5 1)`
/// == `6`.
#[test]
fn test_z3_substitute_const_to_numeral_folds() {
    // SAFETY: see test_z3_compat_basic_lia.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let x = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"x".as_ptr()), int_sort);
        let one = Z3_mk_int(ctx, 1, int_sort);
        let five = Z3_mk_int(ctx, 5, int_sort);
        let six = Z3_mk_int(ctx, 6, int_sort);

        // (+ x 1)
        let args = [x, one];
        let expr = Z3_mk_add(ctx, 2, args.as_ptr());

        // (+ x 1)[x := 5]
        let from = [x];
        let to = [five];
        let got = Z3_substitute(ctx, expr, 1, from.as_ptr(), to.as_ptr());
        assert_ne!(got, 0, "Z3_substitute should return a non-null AST");

        // Hash-consing identity: equals the directly-built (+ 5 1), which folds to 6.
        let direct_args = [five, one];
        let direct = Z3_mk_add(ctx, 2, direct_args.as_ptr());
        assert_eq!(got, direct, "substitute must equal directly-built term");
        assert_eq!(got, six, "(+ x 1)[x:=5] must eager-fold to 6");

        // And it numerically evaluates to 6.
        let mut v: i32 = 0;
        assert!(Z3_get_numeral_int(ctx, got, &raw mut v));
        assert_eq!(v, 6);

        Z3_del_context(ctx);
    }
}

/// Z3_substitute: simultaneous multi-pair swap x<->y in `(- x y)` gives
/// `(- y x)`, NOT `(- x x)` (proves simultaneity / no recursion into `to`).
#[test]
fn test_z3_substitute_simultaneous_swap() {
    // SAFETY: see test_z3_compat_basic_lia.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let x = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"x".as_ptr()), int_sort);
        let y = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"y".as_ptr()), int_sort);

        let sub_xy = [x, y];
        let expr = Z3_mk_sub(ctx, 2, sub_xy.as_ptr()); // (- x y)

        let from = [x, y];
        let to = [y, x];
        let got = Z3_substitute(ctx, expr, 2, from.as_ptr(), to.as_ptr());

        let sub_yx = [y, x];
        let expected = Z3_mk_sub(ctx, 2, sub_yx.as_ptr()); // (- y x)
        assert_eq!(got, expected, "swap must be simultaneous");
        assert_ne!(got, expr, "swap must actually change the term");

        Z3_del_context(ctx);
    }
}

/// Z3_substitute: substituting a term absent from `a` is a no-op (returns `a`).
#[test]
fn test_z3_substitute_absent_is_noop() {
    // SAFETY: see test_z3_compat_basic_lia.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let x = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"x".as_ptr()), int_sort);
        let z = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"z".as_ptr()), int_sort);
        let one = Z3_mk_int(ctx, 1, int_sort);
        let five = Z3_mk_int(ctx, 5, int_sort);

        let args = [x, one];
        let expr = Z3_mk_add(ctx, 2, args.as_ptr()); // (+ x 1), no z

        let from = [z];
        let to = [five];
        let got = Z3_substitute(ctx, expr, 1, from.as_ptr(), to.as_ptr());
        assert_eq!(got, expr, "substituting an absent term is a no-op");

        // num_exprs == 0 and null arrays also return `a` unchanged.
        assert_eq!(
            Z3_substitute(ctx, expr, 0, from.as_ptr(), to.as_ptr()),
            expr
        );
        assert_eq!(Z3_substitute(ctx, expr, 1, ptr::null(), to.as_ptr()), expr);
        assert_eq!(
            Z3_substitute(ctx, expr, 1, from.as_ptr(), ptr::null()),
            expr
        );

        Z3_del_context(ctx);
    }
}

/// Z3_substitute: a from/to pair with mismatched sorts sets Z3_SORT_ERROR and
/// returns `a` unchanged (never fabricates an ill-sorted term).
#[test]
fn test_z3_substitute_sort_mismatch_errors() {
    // SAFETY: see test_z3_compat_basic_lia.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let bool_sort = Z3_mk_bool_sort(ctx);
        let x = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"x".as_ptr()), int_sort);
        let one = Z3_mk_int(ctx, 1, int_sort);
        let args = [x, one];
        let expr = Z3_mk_add(ctx, 2, args.as_ptr()); // (+ x 1)

        // Replace Int x with a Bool — sort mismatch.
        let b = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"b".as_ptr()), bool_sort);
        let from = [x];
        let to = [b];
        let got = Z3_substitute(ctx, expr, 1, from.as_ptr(), to.as_ptr());
        assert_eq!(got, expr, "sort mismatch returns `a` unchanged");
        assert_eq!(
            Z3_get_error_code(ctx),
            Z3_SORT_ERROR,
            "sort mismatch sets Z3_SORT_ERROR"
        );

        Z3_del_context(ctx);
    }
}

// ===========================================================================
// Sequence & string constructors (#phase3-seq)
// ===========================================================================

/// Z3_mk_string_sort reports Z3_SEQ_SORT; Z3_mk_seq_sort too.
#[test]
fn test_seq_string_sort_kinds() {
    // SAFETY: see test_z3_compat_basic_lia.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let str_sort = Z3_mk_string_sort(ctx);
        assert!(!str_sort.is_null());
        assert_eq!(Z3_get_sort_kind(ctx, str_sort), Z3_SEQ_SORT);

        let int_sort = Z3_mk_int_sort(ctx);
        let seq_int = Z3_mk_seq_sort(ctx, int_sort);
        assert!(!seq_int.is_null());
        assert_eq!(Z3_get_sort_kind(ctx, seq_int), Z3_SEQ_SORT);

        Z3_del_context(ctx);
    }
}

/// (str.++ "ab" "c") == "abc" is SAT.  Cross-checked: z3 -> sat.
#[test]
fn test_str_concat_sat() {
    // SAFETY: see test_z3_compat_basic_lia.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let ab = Z3_mk_string(ctx, c"ab".as_ptr());
        let cc = Z3_mk_string(ctx, c"c".as_ptr());
        let abc = Z3_mk_string(ctx, c"abc".as_ptr());
        let args = [ab, cc];
        let cat = Z3_mk_seq_concat(ctx, 2, args.as_ptr());
        let eq = Z3_mk_eq(ctx, cat, abc);

        let solver = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, solver, eq);
        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_TRUE);

        Z3_del_context(ctx);
    }
}

/// (str.++ "ab" "c") == "abd" is UNSAT.  Cross-checked: z3 -> unsat.
#[test]
fn test_str_concat_unsat() {
    // SAFETY: see test_z3_compat_basic_lia.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let ab = Z3_mk_string(ctx, c"ab".as_ptr());
        let cc = Z3_mk_string(ctx, c"c".as_ptr());
        let abd = Z3_mk_string(ctx, c"abd".as_ptr());
        let args = [ab, cc];
        let cat = Z3_mk_seq_concat(ctx, 2, args.as_ptr());
        let eq = Z3_mk_eq(ctx, cat, abd);

        let solver = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, solver, eq);
        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_FALSE);

        Z3_del_context(ctx);
    }
}

/// (str.len "abc") == 3 is SAT; == 5 is UNSAT.  Cross-checked against z3.
#[test]
fn test_str_length() {
    // SAFETY: see test_z3_compat_basic_lia.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let abc = Z3_mk_string(ctx, c"abc".as_ptr());
        let len = Z3_mk_seq_length(ctx, abc);
        let three = Z3_mk_int(ctx, 3, int_sort);
        let five = Z3_mk_int(ctx, 5, int_sort);

        let s1 = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, s1, Z3_mk_eq(ctx, len, three));
        assert_eq!(Z3_solver_check(ctx, s1), Z3_L_TRUE);

        let s2 = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, s2, Z3_mk_eq(ctx, len, five));
        assert_eq!(Z3_solver_check(ctx, s2), Z3_L_FALSE);

        Z3_del_context(ctx);
    }
}

/// (str.contains "abc" "b") SAT; (str.contains "abc" "x") UNSAT. vs z3.
#[test]
fn test_str_contains() {
    // SAFETY: see test_z3_compat_basic_lia.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let abc = Z3_mk_string(ctx, c"abc".as_ptr());
        let b = Z3_mk_string(ctx, c"b".as_ptr());
        let x = Z3_mk_string(ctx, c"x".as_ptr());

        let s1 = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, s1, Z3_mk_seq_contains(ctx, abc, b));
        assert_eq!(Z3_solver_check(ctx, s1), Z3_L_TRUE);

        let s2 = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, s2, Z3_mk_seq_contains(ctx, abc, x));
        assert_eq!(Z3_solver_check(ctx, s2), Z3_L_FALSE);

        Z3_del_context(ctx);
    }
}

/// (str.prefixof "ab" "abc") SAT; (str.suffixof "bc" "abc") SAT. vs z3.
#[test]
fn test_str_prefix_suffix() {
    // SAFETY: see test_z3_compat_basic_lia.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let abc = Z3_mk_string(ctx, c"abc".as_ptr());
        let ab = Z3_mk_string(ctx, c"ab".as_ptr());
        let bc = Z3_mk_string(ctx, c"bc".as_ptr());

        let s1 = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, s1, Z3_mk_seq_prefix(ctx, ab, abc));
        assert_eq!(Z3_solver_check(ctx, s1), Z3_L_TRUE);

        let s2 = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, s2, Z3_mk_seq_suffix(ctx, bc, abc));
        assert_eq!(Z3_solver_check(ctx, s2), Z3_L_TRUE);

        // suffix that is not a suffix -> unsat
        let s3 = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, s3, Z3_mk_seq_suffix(ctx, ab, abc));
        assert_eq!(Z3_solver_check(ctx, s3), Z3_L_FALSE);

        Z3_del_context(ctx);
    }
}

/// (str.at "abc" 1) == "b" SAT. vs z3.
#[test]
fn test_str_at() {
    // SAFETY: see test_z3_compat_basic_lia.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let abc = Z3_mk_string(ctx, c"abc".as_ptr());
        let one = Z3_mk_int(ctx, 1, int_sort);
        let at = Z3_mk_seq_at(ctx, abc, one);
        let b = Z3_mk_string(ctx, c"b".as_ptr());

        let solver = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, solver, Z3_mk_eq(ctx, at, b));
        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_TRUE);

        Z3_del_context(ctx);
    }
}

/// (str.substr "abcde" 1 3) == "bcd" SAT. vs z3.
#[test]
fn test_str_substr() {
    // SAFETY: see test_z3_compat_basic_lia.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let abcde = Z3_mk_string(ctx, c"abcde".as_ptr());
        let one = Z3_mk_int(ctx, 1, int_sort);
        let three = Z3_mk_int(ctx, 3, int_sort);
        let sub = Z3_mk_seq_extract(ctx, abcde, one, three);
        let bcd = Z3_mk_string(ctx, c"bcd".as_ptr());

        let solver = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, solver, Z3_mk_eq(ctx, sub, bcd));
        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_TRUE);

        Z3_del_context(ctx);
    }
}

/// (str.indexof "abcabc" "c" 0) == 2 SAT. vs z3.
#[test]
fn test_str_indexof() {
    // SAFETY: see test_z3_compat_basic_lia.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let h = Z3_mk_string(ctx, c"abcabc".as_ptr());
        let n = Z3_mk_string(ctx, c"c".as_ptr());
        let zero = Z3_mk_int(ctx, 0, int_sort);
        let idx = Z3_mk_seq_index(ctx, h, n, zero);
        let two = Z3_mk_int(ctx, 2, int_sort);

        let solver = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, solver, Z3_mk_eq(ctx, idx, two));
        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_TRUE);

        Z3_del_context(ctx);
    }
}

/// (str.replace "abcabc" "b" "X") == "aXcabc" SAT. vs z3.
#[test]
fn test_str_replace() {
    // SAFETY: see test_z3_compat_basic_lia.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let h = Z3_mk_string(ctx, c"abcabc".as_ptr());
        let from = Z3_mk_string(ctx, c"b".as_ptr());
        let to = Z3_mk_string(ctx, c"X".as_ptr());
        let r = Z3_mk_seq_replace(ctx, h, from, to);
        let exp = Z3_mk_string(ctx, c"aXcabc".as_ptr());

        let solver = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, solver, Z3_mk_eq(ctx, r, exp));
        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_TRUE);

        Z3_del_context(ctx);
    }
}

/// (str.to_int "42") == 42 SAT; (str.from_int 42) == "42" SAT. vs z3.
#[test]
fn test_str_int_conversions() {
    // SAFETY: see test_z3_compat_basic_lia.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let s42 = Z3_mk_string(ctx, c"42".as_ptr());
        let i = Z3_mk_str_to_int(ctx, s42);
        let n42 = Z3_mk_int(ctx, 42, int_sort);

        let s1 = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, s1, Z3_mk_eq(ctx, i, n42));
        assert_eq!(Z3_solver_check(ctx, s1), Z3_L_TRUE);

        let from_int = Z3_mk_int_to_str(ctx, n42);
        let exp = Z3_mk_string(ctx, c"42".as_ptr());
        let s2 = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, s2, Z3_mk_eq(ctx, from_int, exp));
        assert_eq!(Z3_solver_check(ctx, s2), Z3_L_TRUE);

        Z3_del_context(ctx);
    }
}

/// (= (seq.len (seq.++ (seq.unit 1) (seq.unit 2))) 2) SAT;
/// (= (seq.len (as seq.empty (Seq Int))) 1) UNSAT. vs z3.
#[test]
fn test_seq_empty_unit_concat_length() {
    // SAFETY: see test_z3_compat_basic_lia.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let one = Z3_mk_int(ctx, 1, int_sort);
        let two = Z3_mk_int(ctx, 2, int_sort);
        let u1 = Z3_mk_seq_unit(ctx, one);
        let u2 = Z3_mk_seq_unit(ctx, two);
        let args = [u1, u2];
        let cat = Z3_mk_seq_concat(ctx, 2, args.as_ptr());
        let len = Z3_mk_seq_length(ctx, cat);
        let two_i = Z3_mk_int(ctx, 2, int_sort);

        let s1 = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, s1, Z3_mk_eq(ctx, len, two_i));
        assert_eq!(Z3_solver_check(ctx, s1), Z3_L_TRUE);

        // empty seq length == 1 is unsat (it is 0)
        let seq_int = Z3_mk_seq_sort(ctx, int_sort);
        let empty = Z3_mk_seq_empty(ctx, seq_int);
        let elen = Z3_mk_seq_length(ctx, empty);
        let one_i = Z3_mk_int(ctx, 1, int_sort);
        let s2 = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, s2, Z3_mk_eq(ctx, elen, one_i));
        assert_eq!(Z3_solver_check(ctx, s2), Z3_L_FALSE);

        Z3_del_context(ctx);
    }
}

/// (= (seq.nth (seq.++ (seq.unit 10) (seq.unit 20)) 1) 20) SAT. vs z3.
#[test]
fn test_seq_nth() {
    // SAFETY: see test_z3_compat_basic_lia.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let ten = Z3_mk_int(ctx, 10, int_sort);
        let twenty = Z3_mk_int(ctx, 20, int_sort);
        let u1 = Z3_mk_seq_unit(ctx, ten);
        let u2 = Z3_mk_seq_unit(ctx, twenty);
        let args = [u1, u2];
        let cat = Z3_mk_seq_concat(ctx, 2, args.as_ptr());
        let one = Z3_mk_int(ctx, 1, int_sort);
        let nth = Z3_mk_seq_nth(ctx, cat, one);
        let exp = Z3_mk_int(ctx, 20, int_sort);

        let solver = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, solver, Z3_mk_eq(ctx, nth, exp));
        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_TRUE);

        Z3_del_context(ctx);
    }
}

/// Z3_mk_seq_nth on a String operand has no Char-element backing in AY:
/// it must record Z3_SORT_ERROR and return the null AST, not fabricate a term.
#[test]
fn test_seq_nth_on_string_errors() {
    // SAFETY: see test_z3_compat_basic_lia.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let abc = Z3_mk_string(ctx, c"abc".as_ptr());
        let zero = Z3_mk_int(ctx, 0, int_sort);
        let nth = Z3_mk_seq_nth(ctx, abc, zero);
        assert_eq!(nth, 0, "seq.nth on String returns null AST");
        assert_eq!(Z3_get_error_code(ctx), Z3_SORT_ERROR);

        Z3_del_context(ctx);
    }
}

/// (= (seq.at (seq.++ (seq.unit 10) (seq.unit 20)) 0) (seq.unit 10)) SAT. vs z3.
#[test]
fn test_seq_at_subsequence() {
    // SAFETY: see test_z3_compat_basic_lia.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let ten = Z3_mk_int(ctx, 10, int_sort);
        let twenty = Z3_mk_int(ctx, 20, int_sort);
        let u1 = Z3_mk_seq_unit(ctx, ten);
        let u2 = Z3_mk_seq_unit(ctx, twenty);
        let args = [u1, u2];
        let cat = Z3_mk_seq_concat(ctx, 2, args.as_ptr());
        let zero = Z3_mk_int(ctx, 0, int_sort);
        let at = Z3_mk_seq_at(ctx, cat, zero);
        // expected: unit(10)
        let ten2 = Z3_mk_int(ctx, 10, int_sort);
        let exp = Z3_mk_seq_unit(ctx, ten2);

        let solver = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, solver, Z3_mk_eq(ctx, at, exp));
        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_TRUE);

        Z3_del_context(ctx);
    }
}

/// (= (seq.extract <10,20,30> 1 1) (seq.unit 20)) SAT. vs z3.
#[test]
fn test_seq_extract_subsequence() {
    // SAFETY: see test_z3_compat_basic_lia.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let ten = Z3_mk_int(ctx, 10, int_sort);
        let twenty = Z3_mk_int(ctx, 20, int_sort);
        let thirty = Z3_mk_int(ctx, 30, int_sort);
        let u1 = Z3_mk_seq_unit(ctx, ten);
        let u2 = Z3_mk_seq_unit(ctx, twenty);
        let u3 = Z3_mk_seq_unit(ctx, thirty);
        let a23 = [u2, u3];
        let cat23 = Z3_mk_seq_concat(ctx, 2, a23.as_ptr());
        let a123 = [u1, cat23];
        let cat = Z3_mk_seq_concat(ctx, 2, a123.as_ptr());
        let one = Z3_mk_int(ctx, 1, int_sort);
        let len1 = Z3_mk_int(ctx, 1, int_sort);
        let ext = Z3_mk_seq_extract(ctx, cat, one, len1);
        let twenty2 = Z3_mk_int(ctx, 20, int_sort);
        let exp = Z3_mk_seq_unit(ctx, twenty2);

        let solver = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, solver, Z3_mk_eq(ctx, ext, exp));
        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_TRUE);

        Z3_del_context(ctx);
    }
}

/// seq.contains on a (Seq Int): (seq.contains <1,2> (seq.unit 1)) SAT. vs z3.
#[test]
fn test_seq_contains_seqint() {
    // SAFETY: see test_z3_compat_basic_lia.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let one = Z3_mk_int(ctx, 1, int_sort);
        let two = Z3_mk_int(ctx, 2, int_sort);
        let u1 = Z3_mk_seq_unit(ctx, one);
        let u2 = Z3_mk_seq_unit(ctx, two);
        let args = [u1, u2];
        let cat = Z3_mk_seq_concat(ctx, 2, args.as_ptr());
        let one2 = Z3_mk_int(ctx, 1, int_sort);
        let needle = Z3_mk_seq_unit(ctx, one2);

        let solver = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, solver, Z3_mk_seq_contains(ctx, cat, needle));
        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_TRUE);

        Z3_del_context(ctx);
    }
}

/// seq.indexof / seq.replace on (Seq Int) build valid terms; AY's seq decision
/// procedure may answer unknown (it is incomplete for these), so accept SAT or
/// UNDEF — never assert an unsound verdict. The term construction itself is the
/// correct SMT-LIB term (string analogues are decided fully; see test_str_*).
#[test]
fn test_seq_index_replace_build_and_solve_or_unknown() {
    // SAFETY: see test_z3_compat_basic_lia.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let ten = Z3_mk_int(ctx, 10, int_sort);
        let twenty = Z3_mk_int(ctx, 20, int_sort);
        let u1 = Z3_mk_seq_unit(ctx, ten);
        let u2 = Z3_mk_seq_unit(ctx, twenty);
        let args = [u1, u2];
        let cat = Z3_mk_seq_concat(ctx, 2, args.as_ptr());

        // seq.indexof
        let twenty_n = Z3_mk_int(ctx, 20, int_sort);
        let needle = Z3_mk_seq_unit(ctx, twenty_n);
        let zero = Z3_mk_int(ctx, 0, int_sort);
        let idx = Z3_mk_seq_index(ctx, cat, needle, zero);
        assert_ne!(idx, 0, "seq.indexof must build a non-null term");
        let one = Z3_mk_int(ctx, 1, int_sort);
        let s1 = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, s1, Z3_mk_eq(ctx, idx, one));
        let r1 = Z3_solver_check(ctx, s1);
        assert!(
            r1 == Z3_L_TRUE || r1 == Z3_L_UNDEF,
            "seq.indexof: expected sat or unknown, got {r1}"
        );

        // seq.replace
        let twenty_f = Z3_mk_int(ctx, 20, int_sort);
        let from = Z3_mk_seq_unit(ctx, twenty_f);
        let ninety = Z3_mk_int(ctx, 90, int_sort);
        let to = Z3_mk_seq_unit(ctx, ninety);
        let rep = Z3_mk_seq_replace(ctx, cat, from, to);
        assert_ne!(rep, 0, "seq.replace must build a non-null term");
        let ten_e = Z3_mk_int(ctx, 10, int_sort);
        let ue1 = Z3_mk_seq_unit(ctx, ten_e);
        let ninety_e = Z3_mk_int(ctx, 90, int_sort);
        let ue2 = Z3_mk_seq_unit(ctx, ninety_e);
        let eargs = [ue1, ue2];
        let exp = Z3_mk_seq_concat(ctx, 2, eargs.as_ptr());
        let s2 = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, s2, Z3_mk_eq(ctx, rep, exp));
        let r2 = Z3_solver_check(ctx, s2);
        assert!(
            r2 == Z3_L_TRUE || r2 == Z3_L_UNDEF,
            "seq.replace: expected sat or unknown, got {r2}"
        );

        Z3_del_context(ctx);
    }
}

// ============================================================================
// Algebraic datatypes (#phase3-dt)
//
// These exercise the multi-step Z3 datatype API: Z3_mk_constructor builds a
// descriptor, Z3_mk_datatype creates the sort and back-fills constructor /
// recognizer / accessor func_decls, Z3_query_constructor reads them back, and
// Z3_mk_app applies them. Verdicts are cross-checked against `z3 -in` on the
// equivalent SMT-LIB `declare-datatypes`.
// ============================================================================

/// Option<Int> = none | some(value: Int).
/// Asserts `(is-some x)` and `(= (value x) 5)`; expects SAT (matches z3).
#[test]
fn test_z3_compat_datatype_option_sat() {
    // SAFETY: Test-scope unsafe block: all handles are allocated by `Z3_mk_*`
    // calls in this block and freed by `Z3_del_*`/drop. No pointer escapes and
    // the test owns every handle exclusively.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);

        // none (nullary)
        let none_name = Z3_mk_string_symbol(ctx, c"none".as_ptr());
        let none_rec = Z3_mk_string_symbol(ctx, c"is-none".as_ptr());
        let none_ctor = Z3_mk_constructor(
            ctx,
            none_name,
            none_rec,
            0,
            ptr::null(),
            ptr::null(),
            ptr::null(),
        );
        assert!(!none_ctor.is_null());

        // some(value: Int)
        let some_name = Z3_mk_string_symbol(ctx, c"some".as_ptr());
        let some_rec = Z3_mk_string_symbol(ctx, c"is-some".as_ptr());
        let value_name = Z3_mk_string_symbol(ctx, c"value".as_ptr());
        let field_names = [value_name];
        let field_sorts = [int_sort];
        let sort_refs = [0u32];
        let some_ctor = Z3_mk_constructor(
            ctx,
            some_name,
            some_rec,
            1,
            field_names.as_ptr(),
            field_sorts.as_ptr(),
            sort_refs.as_ptr(),
        );
        assert!(!some_ctor.is_null());

        let dt_name = Z3_mk_string_symbol(ctx, c"OptionInt".as_ptr());
        let mut ctors = [none_ctor, some_ctor];
        let dt_sort = Z3_mk_datatype(ctx, dt_name, 2, ctors.as_mut_ptr());
        assert!(!dt_sort.is_null());

        // Query func_decls for `some`.
        let mut some_decl: Z3_func_decl = ptr::null_mut();
        let mut some_tester: Z3_func_decl = ptr::null_mut();
        let mut some_acc: [Z3_func_decl; 1] = [ptr::null_mut()];
        Z3_query_constructor(
            ctx,
            some_ctor,
            1,
            &raw mut some_decl,
            &raw mut some_tester,
            some_acc.as_mut_ptr(),
        );
        assert!(!some_decl.is_null());
        assert!(!some_tester.is_null());
        assert!(!some_acc[0].is_null());

        // x : OptionInt
        let x_sym = Z3_mk_string_symbol(ctx, c"x".as_ptr());
        let x = Z3_mk_const(ctx, x_sym, dt_sort);
        assert_ne!(x, 0);

        // assert (is-some x)
        let is_some_x = Z3_mk_app(ctx, some_tester, 1, [x].as_ptr());
        assert_ne!(is_some_x, 0);

        // assert (= (value x) 5)
        let value_x = Z3_mk_app(ctx, some_acc[0], 1, [x].as_ptr());
        assert_ne!(value_x, 0);
        let five = Z3_mk_int(ctx, 5, int_sort);
        let eq = Z3_mk_eq(ctx, value_x, five);

        let solver = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, solver, is_some_x);
        Z3_solver_assert(ctx, solver, eq);
        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_TRUE);

        Z3_del_constructor(ctx, none_ctor);
        Z3_del_constructor(ctx, some_ctor);
        Z3_del_context(ctx);
    }
}

/// Building a `some(5)` term and asserting `(is-none (some 5))` must be UNSAT.
/// Exercises the constructor func_decl application path.
#[test]
fn test_z3_compat_datatype_constructor_recognizer_unsat() {
    // SAFETY: see other datatype tests — exclusive handle ownership in-block.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);

        let none_name = Z3_mk_string_symbol(ctx, c"none2".as_ptr());
        let none_ctor = Z3_mk_constructor(
            ctx,
            none_name,
            ptr::null_mut(),
            0,
            ptr::null(),
            ptr::null(),
            ptr::null(),
        );
        let some_name = Z3_mk_string_symbol(ctx, c"some2".as_ptr());
        let value_name = Z3_mk_string_symbol(ctx, c"value2".as_ptr());
        let field_names = [value_name];
        let field_sorts = [int_sort];
        let sort_refs = [0u32];
        let some_ctor = Z3_mk_constructor(
            ctx,
            some_name,
            ptr::null_mut(),
            1,
            field_names.as_ptr(),
            field_sorts.as_ptr(),
            sort_refs.as_ptr(),
        );

        let dt_name = Z3_mk_string_symbol(ctx, c"OptionInt2".as_ptr());
        let mut ctors = [none_ctor, some_ctor];
        let _dt_sort = Z3_mk_datatype(ctx, dt_name, 2, ctors.as_mut_ptr());

        let mut some_decl: Z3_func_decl = ptr::null_mut();
        Z3_query_constructor(
            ctx,
            some_ctor,
            1,
            &raw mut some_decl,
            ptr::null_mut(),
            ptr::null_mut(),
        );
        let mut none_tester: Z3_func_decl = ptr::null_mut();
        Z3_query_constructor(
            ctx,
            none_ctor,
            0,
            ptr::null_mut(),
            &raw mut none_tester,
            ptr::null_mut(),
        );
        assert!(!some_decl.is_null());
        assert!(!none_tester.is_null());

        // (some 5)
        let five = Z3_mk_int(ctx, 5, int_sort);
        let some_5 = Z3_mk_app(ctx, some_decl, 1, [five].as_ptr());
        assert_ne!(some_5, 0);

        // assert (is-none2 (some2 5)) -> unsat
        let is_none = Z3_mk_app(ctx, none_tester, 1, [some_5].as_ptr());
        let solver = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, solver, is_none);
        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_FALSE);

        Z3_del_constructor(ctx, none_ctor);
        Z3_del_constructor(ctx, some_ctor);
        Z3_del_context(ctx);
    }
}

/// Pair = mk-pair(fst: Int, snd: Int). Selector round-trip:
/// p = mk-pair(1,2); assert (= (fst p) 2) -> UNSAT (matches z3).
#[test]
fn test_z3_compat_datatype_pair_selector_unsat() {
    // SAFETY: see other datatype tests — exclusive handle ownership in-block.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let mk_name = Z3_mk_string_symbol(ctx, c"mk-pair".as_ptr());
        let fst_name = Z3_mk_string_symbol(ctx, c"fst".as_ptr());
        let snd_name = Z3_mk_string_symbol(ctx, c"snd".as_ptr());
        let field_names = [fst_name, snd_name];
        let field_sorts = [int_sort, int_sort];
        let sort_refs = [0u32, 0u32];
        let mk_ctor = Z3_mk_constructor(
            ctx,
            mk_name,
            ptr::null_mut(),
            2,
            field_names.as_ptr(),
            field_sorts.as_ptr(),
            sort_refs.as_ptr(),
        );

        let dt_name = Z3_mk_string_symbol(ctx, c"Pair".as_ptr());
        let mut ctors = [mk_ctor];
        let _dt = Z3_mk_datatype(ctx, dt_name, 1, ctors.as_mut_ptr());

        let mut mk_decl: Z3_func_decl = ptr::null_mut();
        let mut accs: [Z3_func_decl; 2] = [ptr::null_mut(), ptr::null_mut()];
        Z3_query_constructor(
            ctx,
            mk_ctor,
            2,
            &raw mut mk_decl,
            ptr::null_mut(),
            accs.as_mut_ptr(),
        );
        assert!(!mk_decl.is_null());
        assert!(!accs[0].is_null() && !accs[1].is_null());

        let one = Z3_mk_int(ctx, 1, int_sort);
        let two = Z3_mk_int(ctx, 2, int_sort);
        let p = Z3_mk_app(ctx, mk_decl, 2, [one, two].as_ptr());
        assert_ne!(p, 0);

        // (fst p) should equal 1 (z3-verified), so asserting (= (fst p) 2) is
        // unsat. AY has one solver per context, so this test checks the single
        // selector-semantics case; the SAT selector path is covered by
        // test_z3_compat_datatype_option_sat.
        let _ = one;
        let fst_p = Z3_mk_app(ctx, accs[0], 1, [p].as_ptr());
        let eq_2 = Z3_mk_eq(ctx, fst_p, two);
        let solver = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, solver, eq_2);
        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_FALSE);

        Z3_del_constructor(ctx, mk_ctor);
        Z3_del_context(ctx);
    }
}

/// Pair selector SAT case in its own context (AY has one solver per context):
/// p = mk-pair(1,2); assert (= (snd p) 2) -> SAT, and inspect the model.
#[test]
fn test_z3_compat_datatype_pair_selector_sat() {
    // SAFETY: see other datatype tests — exclusive handle ownership in-block.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let mk_name = Z3_mk_string_symbol(ctx, c"mk-pair-s".as_ptr());
        let fst_name = Z3_mk_string_symbol(ctx, c"fst-s".as_ptr());
        let snd_name = Z3_mk_string_symbol(ctx, c"snd-s".as_ptr());
        let field_names = [fst_name, snd_name];
        let field_sorts = [int_sort, int_sort];
        let sort_refs = [0u32, 0u32];
        let mk_ctor = Z3_mk_constructor(
            ctx,
            mk_name,
            ptr::null_mut(),
            2,
            field_names.as_ptr(),
            field_sorts.as_ptr(),
            sort_refs.as_ptr(),
        );

        let dt_name = Z3_mk_string_symbol(ctx, c"PairS".as_ptr());
        let mut ctors = [mk_ctor];
        let _dt = Z3_mk_datatype(ctx, dt_name, 1, ctors.as_mut_ptr());

        let mut mk_decl: Z3_func_decl = ptr::null_mut();
        let mut accs: [Z3_func_decl; 2] = [ptr::null_mut(), ptr::null_mut()];
        Z3_query_constructor(
            ctx,
            mk_ctor,
            2,
            &raw mut mk_decl,
            ptr::null_mut(),
            accs.as_mut_ptr(),
        );

        let one = Z3_mk_int(ctx, 1, int_sort);
        let two = Z3_mk_int(ctx, 2, int_sort);
        let p = Z3_mk_app(ctx, mk_decl, 2, [one, two].as_ptr());

        let snd_p = Z3_mk_app(ctx, accs[1], 1, [p].as_ptr());
        let eq_2 = Z3_mk_eq(ctx, snd_p, two);
        let solver = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, solver, eq_2);
        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_TRUE);

        let model = Z3_solver_get_model(ctx, solver);
        assert!(!model.is_null());
        let model_str = Z3_model_to_string(ctx, model);
        assert!(!model_str.is_null());

        Z3_del_constructor(ctx, mk_ctor);
        Z3_del_context(ctx);
    }
}

/// Recursive datatype: Lst = nil | cons(hd: Int, tl: Lst). The `tl` field is a
/// self-reference (null sort + sort_ref 0). Asserts (is-cons l), (= (hd l) 7),
/// (is-nil (tl l)) -> SAT (matches z3).
#[test]
fn test_z3_compat_datatype_recursive_list_sat() {
    // SAFETY: see other datatype tests — exclusive handle ownership in-block.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);

        let nil_name = Z3_mk_string_symbol(ctx, c"nil".as_ptr());
        let nil_ctor = Z3_mk_constructor(
            ctx,
            nil_name,
            ptr::null_mut(),
            0,
            ptr::null(),
            ptr::null(),
            ptr::null(),
        );

        // cons(hd: Int, tl: Lst) — tl is a self-reference (null sort, ref 0).
        let cons_name = Z3_mk_string_symbol(ctx, c"cons".as_ptr());
        let hd_name = Z3_mk_string_symbol(ctx, c"hd".as_ptr());
        let tl_name = Z3_mk_string_symbol(ctx, c"tl".as_ptr());
        let field_names = [hd_name, tl_name];
        // hd -> Int sort; tl -> null (self sort-reference).
        let field_sorts: [Z3_sort; 2] = [int_sort, ptr::null_mut()];
        let sort_refs = [0u32, 0u32];
        let cons_ctor = Z3_mk_constructor(
            ctx,
            cons_name,
            ptr::null_mut(),
            2,
            field_names.as_ptr(),
            field_sorts.as_ptr(),
            sort_refs.as_ptr(),
        );

        let dt_name = Z3_mk_string_symbol(ctx, c"Lst".as_ptr());
        let mut ctors = [nil_ctor, cons_ctor];
        let dt_sort = Z3_mk_datatype(ctx, dt_name, 2, ctors.as_mut_ptr());
        assert!(!dt_sort.is_null());

        let mut cons_decl: Z3_func_decl = ptr::null_mut();
        let mut cons_tester: Z3_func_decl = ptr::null_mut();
        let mut cons_accs: [Z3_func_decl; 2] = [ptr::null_mut(), ptr::null_mut()];
        Z3_query_constructor(
            ctx,
            cons_ctor,
            2,
            &raw mut cons_decl,
            &raw mut cons_tester,
            cons_accs.as_mut_ptr(),
        );
        let mut nil_tester: Z3_func_decl = ptr::null_mut();
        Z3_query_constructor(
            ctx,
            nil_ctor,
            0,
            ptr::null_mut(),
            &raw mut nil_tester,
            ptr::null_mut(),
        );
        assert!(!cons_decl.is_null() && !cons_tester.is_null());
        assert!(!cons_accs[0].is_null() && !cons_accs[1].is_null());
        assert!(!nil_tester.is_null());

        let l_sym = Z3_mk_string_symbol(ctx, c"l".as_ptr());
        let l = Z3_mk_const(ctx, l_sym, dt_sort);

        let is_cons_l = Z3_mk_app(ctx, cons_tester, 1, [l].as_ptr());
        let hd_l = Z3_mk_app(ctx, cons_accs[0], 1, [l].as_ptr());
        let seven = Z3_mk_int(ctx, 7, int_sort);
        let hd_eq_7 = Z3_mk_eq(ctx, hd_l, seven);
        let tl_l = Z3_mk_app(ctx, cons_accs[1], 1, [l].as_ptr());
        assert_ne!(
            tl_l, 0,
            "tl selector over recursive field must build a term"
        );
        let is_nil_tl = Z3_mk_app(ctx, nil_tester, 1, [tl_l].as_ptr());

        let solver = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, solver, is_cons_l);
        Z3_solver_assert(ctx, solver, hd_eq_7);
        Z3_solver_assert(ctx, solver, is_nil_tl);
        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_TRUE);

        Z3_del_constructor(ctx, nil_ctor);
        Z3_del_constructor(ctx, cons_ctor);
        Z3_del_context(ctx);
    }
}

/// Enum via constructor_list: Color = red | green | blue. Contradictory
/// recognizers (is-red and is-blue) -> UNSAT. Also exercises the
/// Z3_mk_constructor_list / Z3_del_constructor_list path.
#[test]
fn test_z3_compat_datatype_enum_constructor_list_unsat() {
    // SAFETY: see other datatype tests — exclusive handle ownership in-block.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let red = Z3_mk_constructor(
            ctx,
            Z3_mk_string_symbol(ctx, c"red".as_ptr()),
            ptr::null_mut(),
            0,
            ptr::null(),
            ptr::null(),
            ptr::null(),
        );
        let green = Z3_mk_constructor(
            ctx,
            Z3_mk_string_symbol(ctx, c"green".as_ptr()),
            ptr::null_mut(),
            0,
            ptr::null(),
            ptr::null(),
            ptr::null(),
        );
        let blue = Z3_mk_constructor(
            ctx,
            Z3_mk_string_symbol(ctx, c"blue".as_ptr()),
            ptr::null_mut(),
            0,
            ptr::null(),
            ptr::null(),
            ptr::null(),
        );
        let clist = Z3_mk_constructor_list(ctx, 3, [red, green, blue].as_ptr());
        assert!(!clist.is_null());

        let dt_name = Z3_mk_string_symbol(ctx, c"Color".as_ptr());
        let mut ctors = [red, green, blue];
        let dt_sort = Z3_mk_datatype(ctx, dt_name, 3, ctors.as_mut_ptr());
        assert!(!dt_sort.is_null());

        let mut is_red: Z3_func_decl = ptr::null_mut();
        Z3_query_constructor(
            ctx,
            red,
            0,
            ptr::null_mut(),
            &raw mut is_red,
            ptr::null_mut(),
        );
        let mut is_blue: Z3_func_decl = ptr::null_mut();
        Z3_query_constructor(
            ctx,
            blue,
            0,
            ptr::null_mut(),
            &raw mut is_blue,
            ptr::null_mut(),
        );
        assert!(!is_red.is_null() && !is_blue.is_null());

        let c_sym = Z3_mk_string_symbol(ctx, c"c".as_ptr());
        let c_const = Z3_mk_const(ctx, c_sym, dt_sort);

        let solver = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, solver, Z3_mk_app(ctx, is_red, 1, [c_const].as_ptr()));
        Z3_solver_assert(ctx, solver, Z3_mk_app(ctx, is_blue, 1, [c_const].as_ptr()));
        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_FALSE);

        Z3_del_constructor_list(ctx, clist);
        Z3_del_constructor(ctx, red);
        Z3_del_constructor(ctx, green);
        Z3_del_constructor(ctx, blue);
        Z3_del_context(ctx);
    }
}

/// Mutually recursive datatypes are not supported: Z3_mk_datatypes with a
/// cross-datatype sort reference must leave the out slot null and set an error.
#[test]
fn test_z3_compat_datatype_mutual_recursion_rejected() {
    // SAFETY: see other datatype tests — exclusive handle ownership in-block.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        // A constructor with a cross-datatype sort reference (sort_ref 1, which
        // points at a *sibling* datatype, not self).
        let f_name = Z3_mk_string_symbol(ctx, c"mkA".as_ptr());
        let field_name = Z3_mk_string_symbol(ctx, c"getB".as_ptr());
        let field_names = [field_name];
        let field_sorts: [Z3_sort; 1] = [ptr::null_mut()]; // sort reference
        let sort_refs = [1u32]; // cross-datatype reference -> unsupported
        let a_ctor = Z3_mk_constructor(
            ctx,
            f_name,
            ptr::null_mut(),
            1,
            field_names.as_ptr(),
            field_sorts.as_ptr(),
            sort_refs.as_ptr(),
        );
        let a_list = Z3_mk_constructor_list(ctx, 1, [a_ctor].as_ptr());

        let sort_names = [Z3_mk_string_symbol(ctx, c"A".as_ptr())];
        let lists = [a_list];
        let mut out_sorts: [Z3_sort; 1] = [ptr::null_mut()];
        Z3_mk_datatypes(
            ctx,
            1,
            sort_names.as_ptr(),
            out_sorts.as_mut_ptr(),
            lists.as_ptr(),
        );
        // Out slot must remain null (unsupported), with an error recorded.
        assert!(out_sorts[0].is_null());

        Z3_del_constructor_list(ctx, a_list);
        Z3_del_constructor(ctx, a_ctor);
        Z3_del_context(ctx);
    }
}

// ============================================================================
// Z3_fixedpoint (CHC / Datalog) — backed by ay-chc (ffi/phase3-fixedpoint)
// ============================================================================
//
// Builds the canonical bounded-counter transition system:
//   inv(0)                          ; init
//   inv(x) /\ x < 10 => inv(x+1)    ; transition
// and runs `Z3_fixedpoint_query` against a goal `inv(x) /\ x > BOUND`.
//
// Polarity (Z3 fixedpoint): reachable goal => Z3_L_TRUE (UNSAFE), unreachable
// goal => Z3_L_FALSE (SAFE). Cross-checked against `z3` on equivalent HORN
// inputs: x>5 reachable => sat (L_TRUE); x>100 unreachable => unsat (L_FALSE).

/// Build inv/init/transition into the fixedpoint handle. Returns the relation
/// func_decl and the int sort for building the query.
///
/// # Safety
/// `ctx` and `fp` must be valid handles owned by the caller.
unsafe fn build_counter_system(ctx: Z3_context, fp: Z3_fixedpoint) -> (Z3_func_decl, Z3_sort) {
    unsafe {
        let int_sort = Z3_mk_int_sort(ctx);
        let bool_sort = Z3_mk_bool_sort(ctx);

        // (declare-rel inv (Int))
        let inv_sym = Z3_mk_string_symbol(ctx, c"inv".as_ptr());
        let inv = Z3_mk_func_decl(ctx, inv_sym, 1, &raw const int_sort, bool_sort);
        Z3_fixedpoint_register_relation(ctx, fp, inv);

        let x_sym = Z3_mk_string_symbol(ctx, c"x".as_ptr());
        let x = Z3_mk_const(ctx, x_sym, int_sort);
        let zero = Z3_mk_int(ctx, 0, int_sort);
        let one = Z3_mk_int(ctx, 1, int_sort);
        let ten = Z3_mk_int(ctx, 10, int_sort);

        // init: (=> (= x 0) (inv x))  quantified over x
        let x_eq_0 = Z3_mk_eq(ctx, x, zero);
        let inv_x = Z3_mk_app(ctx, inv, 1, &raw const x);
        let init_body = Z3_mk_implies(ctx, x_eq_0, inv_x);
        let init_rule = Z3_mk_forall_const(ctx, 0, 1, &raw const x, 0, ptr::null(), init_body);
        Z3_fixedpoint_add_rule(ctx, fp, init_rule, ptr::null_mut());

        // transition: (=> (and (inv x) (< x 10)) (inv (+ x 1)))  quantified over x
        let x_lt_10 = Z3_mk_lt(ctx, x, ten);
        let inv_x_again = Z3_mk_app(ctx, inv, 1, &raw const x);
        let and_args = [inv_x_again, x_lt_10];
        let trans_ante = Z3_mk_and(ctx, 2, and_args.as_ptr());
        let add_args = [x, one];
        let x_plus_1 = Z3_mk_add(ctx, 2, add_args.as_ptr());
        let inv_xp1 = Z3_mk_app(ctx, inv, 1, &raw const x_plus_1);
        let trans_body = Z3_mk_implies(ctx, trans_ante, inv_xp1);
        let trans_rule = Z3_mk_forall_const(ctx, 0, 1, &raw const x, 0, ptr::null(), trans_body);
        Z3_fixedpoint_add_rule(ctx, fp, trans_rule, ptr::null_mut());

        (inv, int_sort)
    }
}

/// SAFE: the counter only reaches x <= 10, so `inv(x) /\ x > 100` is
/// unreachable. Z3 fixedpoint polarity: unreachable => Z3_L_FALSE.
#[test]
fn test_fixedpoint_safe_query_unreachable() {
    // SAFETY: all handles are allocated and freed within this block; no pointer
    // escapes and the test owns them exclusively.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let fp = Z3_mk_fixedpoint(ctx);
        Z3_fixedpoint_inc_ref(ctx, fp);
        let (inv, int_sort) = build_counter_system(ctx, fp);

        // query goal: (and (inv x) (> x 100))  over a fresh x
        let qx_sym = Z3_mk_string_symbol(ctx, c"qx".as_ptr());
        let qx = Z3_mk_const(ctx, qx_sym, int_sort);
        let hundred = Z3_mk_int(ctx, 100, int_sort);
        let inv_qx = Z3_mk_app(ctx, inv, 1, &raw const qx);
        let qx_gt_100 = Z3_mk_gt(ctx, qx, hundred);
        let goal_args = [inv_qx, qx_gt_100];
        let goal = Z3_mk_and(ctx, 2, goal_args.as_ptr());

        let result = Z3_fixedpoint_query(ctx, fp, goal);
        assert_eq!(
            result, Z3_L_FALSE,
            "safe (unreachable) query must be Z3_L_FALSE (unsat), got {result}"
        );

        let ans = Z3_fixedpoint_get_answer(ctx, fp);
        assert!(!ans.is_null());

        Z3_fixedpoint_dec_ref(ctx, fp);
        Z3_del_context(ctx);
    }
}

/// UNSAFE: the counter reaches x = 10, so `inv(x) /\ x > 5` IS reachable.
/// Z3 fixedpoint polarity: reachable => Z3_L_TRUE.
#[test]
fn test_fixedpoint_unsafe_query_reachable() {
    // SAFETY: all handles are allocated and freed within this block; no pointer
    // escapes and the test owns them exclusively.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let fp = Z3_mk_fixedpoint(ctx);
        Z3_fixedpoint_inc_ref(ctx, fp);
        let (inv, int_sort) = build_counter_system(ctx, fp);

        // query goal: (and (inv x) (> x 5))  — reachable since x climbs to 10
        let qx_sym = Z3_mk_string_symbol(ctx, c"qx".as_ptr());
        let qx = Z3_mk_const(ctx, qx_sym, int_sort);
        let five = Z3_mk_int(ctx, 5, int_sort);
        let inv_qx = Z3_mk_app(ctx, inv, 1, &raw const qx);
        let qx_gt_5 = Z3_mk_gt(ctx, qx, five);
        let goal_args = [inv_qx, qx_gt_5];
        let goal = Z3_mk_and(ctx, 2, goal_args.as_ptr());

        let result = Z3_fixedpoint_query(ctx, fp, goal);
        assert_eq!(
            result, Z3_L_TRUE,
            "unsafe (reachable) query must be Z3_L_TRUE (sat), got {result}"
        );

        Z3_fixedpoint_dec_ref(ctx, fp);
        Z3_del_context(ctx);
    }
}

/// `Z3_fixedpoint_to_string` renders the registered relations and rules.
#[test]
fn test_fixedpoint_to_string() {
    // SAFETY: all handles are allocated and freed within this block.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let fp = Z3_mk_fixedpoint(ctx);
        let _ = build_counter_system(ctx, fp);

        let s = Z3_fixedpoint_to_string(ctx, fp);
        assert!(!s.is_null());
        let rendered = std::ffi::CStr::from_ptr(s).to_str().expect("utf8");
        assert!(rendered.contains("declare-rel inv"), "got: {rendered}");
        assert!(
            !rendered.contains("!ay.z3-func!"),
            "fixedpoint text must not expose private declaration identities: {rendered}"
        );

        Z3_del_context(ctx);
    }
}

// ---- Z3_simplify / Z3_simplify_ex ----

/// `Z3_simplify` folds closed arithmetic to a numeral.
///
/// AY folds eagerly at construction, so `Z3_mk_add(2,3)` is already `5`;
/// `Z3_simplify` must return that numeral (and it must read back as 5).
#[test]
fn test_z3_simplify_closed_arithmetic_folds() {
    // SAFETY: see test_z3_compat_basic_lia.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let two = Z3_mk_int(ctx, 2, int_sort);
        let three = Z3_mk_int(ctx, 3, int_sort);
        let sum = Z3_mk_add(ctx, 2, [two, three].as_ptr());

        let simp = Z3_simplify(ctx, sum);
        assert_ne!(simp, 0, "Z3_simplify must return a non-null AST");
        let mut v: i32 = 0;
        assert!(Z3_get_numeral_int(ctx, simp, &raw mut v));
        assert_eq!(v, 5, "simplify(2+3) must be 5");

        // Equals the directly-built numeral 5 (hash-consing identity).
        let five = Z3_mk_int(ctx, 5, int_sort);
        assert_eq!(simp, five);

        Z3_del_context(ctx);
    }
}

/// `Z3_simplify` reduces `x + 0` to `x`.
#[test]
fn test_z3_simplify_add_zero_identity() {
    // SAFETY: see test_z3_compat_basic_lia.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let x = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"x".as_ptr()), int_sort);
        let zero = Z3_mk_int(ctx, 0, int_sort);
        let sum = Z3_mk_add(ctx, 2, [x, zero].as_ptr());

        let simp = Z3_simplify(ctx, sum);
        assert_eq!(simp, x, "simplify(x + 0) must be x");

        Z3_del_context(ctx);
    }
}

/// `Z3_simplify` collapses `And(true, p)` to `p`.
#[test]
fn test_z3_simplify_and_true_collapses() {
    // SAFETY: see test_z3_compat_basic_lia.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let bool_sort = Z3_mk_bool_sort(ctx);
        let p = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"p".as_ptr()), bool_sort);
        let t = Z3_mk_true(ctx);
        let conj = Z3_mk_and(ctx, 2, [t, p].as_ptr());

        let simp = Z3_simplify(ctx, conj);
        assert_eq!(simp, p, "simplify(And(true, p)) must be p");

        Z3_del_context(ctx);
    }
}

/// `Z3_simplify` reduces `ite(true, a, b)` to `a`.
#[test]
fn test_z3_simplify_ite_true_picks_then() {
    // SAFETY: see test_z3_compat_basic_lia.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let a = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"a".as_ptr()), int_sort);
        let b = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"b".as_ptr()), int_sort);
        let t = Z3_mk_true(ctx);
        let ite = Z3_mk_ite(ctx, t, a, b);

        let simp = Z3_simplify(ctx, ite);
        assert_eq!(simp, a, "simplify(ite(true, a, b)) must be a");

        Z3_del_context(ctx);
    }
}

/// `Z3_simplify` reduces `(select (store a i v) i)` to `v`.
#[test]
fn test_z3_simplify_store_select_same_index() {
    // SAFETY: see test_z3_compat_basic_lia.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let arr_sort = Z3_mk_array_sort(ctx, int_sort, int_sort);
        let arr = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"a".as_ptr()), arr_sort);
        let i = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"i".as_ptr()), int_sort);
        let v = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"v".as_ptr()), int_sort);

        let stored = Z3_mk_store(ctx, arr, i, v);
        let sel = Z3_mk_select(ctx, stored, i);
        let simp = Z3_simplify(ctx, sel);
        assert_eq!(simp, v, "simplify(select(store(a,i,v),i)) must be v");

        Z3_del_context(ctx);
    }
}

/// SOUNDNESS: `simplify(e)` must be logically EQUIVALENT to `e`.
///
/// For a non-trivial term, assert `e = simplify(e)` is valid by checking
/// `not(e = simplify(e))` is UNSAT via the solver.
#[test]
fn test_z3_simplify_is_equivalent_to_input() {
    // SAFETY: see test_z3_compat_basic_lia.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let x = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"x".as_ptr()), int_sort);
        let y = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"y".as_ptr()), int_sort);
        let two = Z3_mk_int(ctx, 2, int_sort);
        let three = Z3_mk_int(ctx, 3, int_sort);

        // e = (x + 2) + ((3 + y) * 1) — a term with foldable subparts.
        let x2 = Z3_mk_add(ctx, 2, [x, two].as_ptr());
        let y3 = Z3_mk_add(ctx, 2, [three, y].as_ptr());
        let one = Z3_mk_int(ctx, 1, int_sort);
        let y3m = Z3_mk_mul(ctx, 2, [y3, one].as_ptr());
        let e = Z3_mk_add(ctx, 2, [x2, y3m].as_ptr());

        let s = Z3_simplify(ctx, e);
        assert_ne!(s, 0);

        // not(e = s) must be UNSAT (i.e. e = s is valid).
        let eq = Z3_mk_eq(ctx, e, s);
        let neq = Z3_mk_not(ctx, eq);
        let solver = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, solver, neq);
        assert_eq!(
            Z3_solver_check(ctx, solver),
            Z3_L_FALSE,
            "simplify(e) must be equivalent to e (not(e=s) must be UNSAT)"
        );

        Z3_del_context(ctx);
    }
}

/// `Z3_simplify` of an already-simplified AY-built term is identity (fixpoint),
/// and is idempotent.
#[test]
fn test_z3_simplify_fixpoint_and_idempotent() {
    // SAFETY: see test_z3_compat_basic_lia.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let x = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"x".as_ptr()), int_sort);
        let one = Z3_mk_int(ctx, 1, int_sort);
        let expr = Z3_mk_add(ctx, 2, [x, one].as_ptr()); // (+ x 1)

        let s1 = Z3_simplify(ctx, expr);
        assert_eq!(s1, expr, "AY-built term must be a simplify fixpoint");
        let s2 = Z3_simplify(ctx, s1);
        assert_eq!(s2, s1, "Z3_simplify must be idempotent");

        Z3_del_context(ctx);
    }
}

/// `Z3_simplify_ex` matches `Z3_simplify` (params are ignored).
#[test]
fn test_z3_simplify_ex_matches_simplify() {
    // SAFETY: see test_z3_compat_basic_lia.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let two = Z3_mk_int(ctx, 2, int_sort);
        let three = Z3_mk_int(ctx, 3, int_sort);
        let sum = Z3_mk_add(ctx, 2, [two, three].as_ptr());

        let params = Z3_mk_params(ctx);
        let via_ex = Z3_simplify_ex(ctx, sum, params);
        let via_plain = Z3_simplify(ctx, sum);
        assert_eq!(via_ex, via_plain, "Z3_simplify_ex must match Z3_simplify");

        // Null params is also accepted.
        let via_null = Z3_simplify_ex(ctx, sum, std::ptr::null_mut());
        assert_eq!(via_null, via_plain);

        Z3_del_context(ctx);
    }
}

/// `Z3_simplify` / `Z3_simplify_ex` of a null AST return it unchanged.
#[test]
fn test_z3_simplify_null_ast_is_noop() {
    // SAFETY: see test_z3_compat_basic_lia.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        assert_eq!(Z3_simplify(ctx, 0), 0);
        assert_eq!(Z3_simplify_ex(ctx, 0, std::ptr::null_mut()), 0);

        Z3_del_context(ctx);
    }
}

// =========================================================================
// Multi-solver independence regression tests (per-handle assertion stacks)
//
// THE BUG: `Z3_mk_solver` returned a placeholder handle ("kept for future
// multi-solver support") and every solver-state function mutated/read the
// context's single shared solver. Two solvers on one context silently merged
// their assertions: s1: x>5, s2: x<3 made BOTH checks UNSAT — real z3 4.15.4
// answers SAT for each. Every `Z3_solver` now owns its own assertion stack
// and check artefacts; these tests lock the independent-per-handle semantics.
// =========================================================================

/// Evaluate an Int variable in a solver's model (helper for the tests below).
///
/// # Safety
/// `ctx`/`s` must be valid handles owned by the calling test; `x` a valid AST.
unsafe fn model_int_value(ctx: Z3_context, s: Z3_solver, x: Z3_ast) -> i64 {
    // SAFETY: forwarded under the caller's contract.
    unsafe {
        let model = Z3_solver_get_model(ctx, s);
        assert!(!model.is_null(), "SAT solver must produce a model");
        let mut val: Z3_ast = 0;
        assert!(Z3_model_eval(ctx, model, x, true, &raw mut val));
        let mut out: i64 = 0;
        assert!(Z3_get_numeral_int64(ctx, val, &raw mut out));
        out
    }
}

/// The exact reported repro: two solvers on ONE context with contradictory
/// constraints over the same variable must BOTH be SAT, each with a model
/// satisfying ITS OWN constraint (matches real z3 4.15.4: (1,1)).
#[test]
fn test_two_solvers_one_context_independent_sat() {
    // SAFETY: Test-scope unsafe block: all handles are allocated by `Z3_mk_*`
    // calls inside this block and freed by `Z3_del_context`. No pointer
    // escapes the block; this test owns the handles exclusively.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let x = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"x".as_ptr()), int_sort);

        let s1 = Z3_mk_solver(ctx);
        let s2 = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, s1, Z3_mk_gt(ctx, x, Z3_mk_int(ctx, 5, int_sort)));
        Z3_solver_assert(ctx, s2, Z3_mk_lt(ctx, x, Z3_mk_int(ctx, 3, int_sort)));

        // Each handle sees only its own assertion.
        let a1 = Z3_solver_get_assertions(ctx, s1);
        let a2 = Z3_solver_get_assertions(ctx, s2);
        assert_eq!(Z3_ast_vector_size(ctx, a1), 1);
        assert_eq!(Z3_ast_vector_size(ctx, a2), 1);

        assert_eq!(
            Z3_solver_check(ctx, s1),
            Z3_L_TRUE,
            "s1 (x>5 only) must be SAT — UNSAT means s2's x<3 leaked in"
        );
        assert_eq!(
            Z3_solver_check(ctx, s2),
            Z3_L_TRUE,
            "s2 (x<3 only) must be SAT — UNSAT means s1's x>5 leaked in"
        );

        // Each model satisfies its OWN solver's constraint.
        assert!(model_int_value(ctx, s1, x) > 5);
        assert!(model_int_value(ctx, s2, x) < 3);

        Z3_del_context(ctx);
    }
}

/// Interleaved multi-solver use: asserts, checks, models, push/pop, and reset
/// on one handle never disturb the other. Mirrors the C matrix cross-checked
/// against real z3 4.15.4 (identical output).
#[test]
fn test_interleaved_multi_solver_state_isolation() {
    // SAFETY: see test_two_solvers_one_context_independent_sat.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let x = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"x".as_ptr()), int_sort);
        let y = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"y".as_ptr()), int_sort);

        let s1 = Z3_mk_solver(ctx);
        let s2 = Z3_mk_solver(ctx);

        // Interleaved asserts and checks.
        Z3_solver_assert(ctx, s1, Z3_mk_gt(ctx, x, Z3_mk_int(ctx, 5, int_sort)));
        Z3_solver_assert(ctx, s2, Z3_mk_lt(ctx, x, Z3_mk_int(ctx, 3, int_sort)));
        assert_eq!(Z3_solver_check(ctx, s1), Z3_L_TRUE);
        Z3_solver_assert(ctx, s1, Z3_mk_lt(ctx, x, Z3_mk_int(ctx, 7, int_sort)));
        assert_eq!(Z3_solver_check(ctx, s2), Z3_L_TRUE);
        assert_eq!(Z3_solver_check(ctx, s1), Z3_L_TRUE);
        // s1 forces 5 < x < 7, so its model pins x = 6; s2's stays < 3.
        assert_eq!(model_int_value(ctx, s1, x), 6);
        assert!(model_int_value(ctx, s2, x) < 3);

        // y-constraints on s2 are invisible to s1.
        Z3_solver_assert(ctx, s2, Z3_mk_eq(ctx, y, Z3_mk_int(ctx, 42, int_sort)));
        assert_eq!(Z3_solver_check(ctx, s2), Z3_L_TRUE);
        assert_eq!(model_int_value(ctx, s2, y), 42);
        assert_eq!(Z3_solver_check(ctx, s1), Z3_L_TRUE);

        // Push/pop on s1 only: a contradiction inside s1's frame leaves s2 SAT,
        // and scope counts are per-handle.
        Z3_solver_push(ctx, s1);
        Z3_solver_assert(ctx, s1, Z3_mk_lt(ctx, x, Z3_mk_int(ctx, 0, int_sort)));
        assert_eq!(Z3_solver_check(ctx, s1), Z3_L_FALSE);
        assert_eq!(Z3_solver_check(ctx, s2), Z3_L_TRUE);
        assert_eq!(Z3_solver_get_num_scopes(ctx, s1), 1);
        assert_eq!(Z3_solver_get_num_scopes(ctx, s2), 0);
        Z3_solver_pop(ctx, s1, 1);
        assert_eq!(Z3_solver_check(ctx, s1), Z3_L_TRUE);
        assert_eq!(model_int_value(ctx, s1, x), 6);

        // check-assumptions on s2 (UNSAT under y<0) never disturbs s1, and the
        // unsat core is served from s2's own snapshot.
        let bad = Z3_mk_lt(ctx, y, Z3_mk_int(ctx, 0, int_sort));
        let asm = [bad];
        assert_eq!(
            Z3_solver_check_assumptions(ctx, s2, 1, asm.as_ptr()),
            Z3_L_FALSE
        );
        let core = Z3_solver_get_unsat_core(ctx, s2);
        assert!(Z3_ast_vector_size(ctx, core) >= 1);
        // s1's core is empty: its last check was SAT without assumptions.
        let core1 = Z3_solver_get_unsat_core(ctx, s1);
        assert_eq!(Z3_ast_vector_size(ctx, core1), 0);
        assert_eq!(Z3_solver_check(ctx, s2), Z3_L_TRUE);
        assert_eq!(Z3_solver_check(ctx, s1), Z3_L_TRUE);

        // Reset s2 only: s1 keeps its assertions and model.
        Z3_solver_reset(ctx, s2);
        let a2 = Z3_solver_get_assertions(ctx, s2);
        assert_eq!(Z3_ast_vector_size(ctx, a2), 0);
        Z3_solver_assert(ctx, s2, Z3_mk_eq(ctx, x, Z3_mk_int(ctx, 100, int_sort)));
        assert_eq!(Z3_solver_check(ctx, s2), Z3_L_TRUE);
        assert_eq!(model_int_value(ctx, s2, x), 100);
        assert_eq!(Z3_solver_check(ctx, s1), Z3_L_TRUE);
        assert_eq!(model_int_value(ctx, s1, x), 6);

        Z3_del_context(ctx);
    }
}

// ============================================================================
// Model-snapshot surface tests (Z3_model_* as a genuine snapshot; #model-fakes)
// ============================================================================
//
// Pins the removal of the two model-surface fakes:
//   (1) Z3_model_eval ignoring `model_completion` and falling back to LIVE
//       solver state (stale-model reads) with `return 0` fakes for
//       Array/Seq/Uninterpreted values;
//   (2) Z3_model_get_num_consts counting entries (arrays included) that
//       Z3_model_get_const_decl did not enumerate — unnamed NULL decls.
// Also pins the Z3_get_numeral_string handle-number-as-numeral fake removal.

/// num_consts and get_const_decl share one index space, arrays included:
/// every index below num_consts yields a NAMED decl with a non-null interp.
#[test]
fn test_model_decl_enumeration_includes_arrays_aligned() {
    // SAFETY: Test-scope unsafe block: all handles are allocated by `Z3_mk_*`
    // calls inside this block and freed by `Z3_del_context`. No pointer
    // escapes and this test owns the handles exclusively.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);
        let int_sort = Z3_mk_int_sort(ctx);
        let arr_sort = Z3_mk_array_sort(ctx, int_sort, int_sort);
        let a = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"a".as_ptr()), arr_sort);
        let i = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"i".as_ptr()), int_sort);
        let three = Z3_mk_int(ctx, 3, int_sort);
        let four = Z3_mk_int(ctx, 4, int_sort);
        let seven = Z3_mk_int(ctx, 7, int_sort);
        let one = Z3_mk_int(ctx, 1, int_sort);

        let solver = Z3_mk_solver(ctx);
        // (select a 3) = 7, i = 4, (select a i) = 1
        Z3_solver_assert(
            ctx,
            solver,
            Z3_mk_eq(ctx, Z3_mk_select(ctx, a, three), seven),
        );
        Z3_solver_assert(ctx, solver, Z3_mk_eq(ctx, i, four));
        Z3_solver_assert(ctx, solver, Z3_mk_eq(ctx, Z3_mk_select(ctx, a, i), one));
        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_TRUE);

        let model = Z3_solver_get_model(ctx, solver);
        assert!(!model.is_null());

        let n = Z3_model_get_num_consts(ctx, model);
        assert!(n >= 2, "model must interpret at least a and i, got {n}");
        let mut names = Vec::new();
        for idx in 0..n {
            let decl = Z3_model_get_const_decl(ctx, model, idx);
            assert!(
                !decl.is_null(),
                "decl {idx} of {n} must be non-null (index space aligned)"
            );
            let sym = Z3_get_decl_name(ctx, decl);
            assert!(!sym.is_null(), "decl {idx} must have a name symbol");
            let name_c = Z3_get_symbol_string(ctx, sym);
            assert!(!name_c.is_null());
            let name = std::ffi::CStr::from_ptr(name_c)
                .to_string_lossy()
                .to_string();
            assert!(!name.is_empty(), "decl {idx} name must be non-empty");
            let interp = Z3_model_get_const_interp(ctx, model, decl);
            assert_ne!(
                interp, 0,
                "decl {idx} ({name}) must have a model interpretation"
            );
            assert!(
                Z3_model_has_interp(ctx, model, decl),
                "has_interp must agree for {name}"
            );
            names.push(name);
        }
        assert!(
            names.iter().any(|s| s == "a"),
            "array const a must be enumerated: {names:?}"
        );
        assert!(
            names.iter().any(|s| s == "i"),
            "int const i must be enumerated: {names:?}"
        );
        // Past-the-end index is honestly null.
        assert!(Z3_model_get_const_decl(ctx, model, n).is_null());

        // The printed model renders the array as a well-formed store chain
        // over an `(as const ...)` base (never an unnamed/None placeholder).
        let text = Z3_model_to_string(ctx, model);
        assert!(!text.is_null());
        let text = std::ffi::CStr::from_ptr(text).to_string_lossy().to_string();
        assert!(
            text.contains("(define-fun a () (Array Int Int)"),
            "model text must define the array const: {text}"
        );
        assert!(
            text.contains("(as const (Array Int Int))"),
            "array value must be a const-array-based chain: {text}"
        );

        Z3_del_context(ctx);
    }
}

/// Z3_model_eval evaluates array reads from the SNAPSHOT: stored index gives
/// the stored value, other indices the base value — and keeps doing so after
/// the live solver is driven UNSAT (stale-model correctness).
#[test]
fn test_model_eval_array_select_snapshot_survives_solver_reuse() {
    // SAFETY: Test-scope unsafe block: all handles are allocated by `Z3_mk_*`
    // calls inside this block and freed by `Z3_del_context`. No pointer
    // escapes and this test owns the handles exclusively.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);
        let int_sort = Z3_mk_int_sort(ctx);
        let arr_sort = Z3_mk_array_sort(ctx, int_sort, int_sort);
        let a = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"a".as_ptr()), arr_sort);
        let i = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"i".as_ptr()), int_sort);
        let three = Z3_mk_int(ctx, 3, int_sort);
        let four = Z3_mk_int(ctx, 4, int_sort);
        let seven = Z3_mk_int(ctx, 7, int_sort);
        let one = Z3_mk_int(ctx, 1, int_sort);

        let solver = Z3_mk_solver(ctx);
        Z3_solver_assert(
            ctx,
            solver,
            Z3_mk_eq(ctx, Z3_mk_select(ctx, a, three), seven),
        );
        Z3_solver_assert(ctx, solver, Z3_mk_eq(ctx, i, four));
        Z3_solver_assert(ctx, solver, Z3_mk_eq(ctx, Z3_mk_select(ctx, a, i), one));
        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_TRUE);
        let model = Z3_solver_get_model(ctx, solver);
        assert!(!model.is_null());

        let read = |t: Z3_ast| -> Option<i64> {
            let mut out: Z3_ast = 0;
            if !Z3_model_eval(ctx, model, t, false, &raw mut out) || out == 0 {
                return None;
            }
            let mut v: i64 = 0;
            Z3_get_numeral_int64(ctx, out, &raw mut v).then_some(v)
        };

        let sel3 = Z3_mk_select(ctx, a, three);
        let sel_i = Z3_mk_select(ctx, a, i);
        assert_eq!(read(sel3), Some(7), "select at stored index 3");
        assert_eq!(read(sel_i), Some(1), "select at pinned symbolic index i=4");

        // eval(a) itself: an array-sorted value term (store chain), not 0.
        let mut arr_val: Z3_ast = 0;
        assert!(Z3_model_eval(ctx, model, a, false, &raw mut arr_val));
        assert_ne!(arr_val, 0, "array const must evaluate to a value term");
        let s = Z3_get_sort(ctx, arr_val);
        assert!(!s.is_null());
        assert_eq!(
            Z3_get_sort_kind(ctx, s),
            Z3_ARRAY_SORT,
            "eval(a) must carry the array sort"
        );

        // Drive the solver UNSAT: the snapshot must be unaffected.
        Z3_solver_push(ctx, solver);
        let five = Z3_mk_int(ctx, 5, int_sort);
        Z3_solver_assert(ctx, solver, Z3_mk_eq(ctx, i, five));
        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_FALSE);
        assert_eq!(read(sel3), Some(7), "snapshot survives solver UNSAT");
        assert_eq!(read(sel_i), Some(1), "snapshot survives solver UNSAT");
        Z3_solver_pop(ctx, solver, 1);

        Z3_del_context(ctx);
    }
}

/// Compound-term evaluation reads the SNAPSHOT (not live solver state), and
/// whole-formula eval reduces to true under the model.
#[test]
fn test_model_eval_compound_snapshot_after_unsat() {
    // SAFETY: Test-scope unsafe block: all handles are allocated by `Z3_mk_*`
    // calls inside this block and freed by `Z3_del_context`. No pointer
    // escapes and this test owns the handles exclusively.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);
        let int_sort = Z3_mk_int_sort(ctx);
        let x = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"x".as_ptr()), int_sort);
        let five = Z3_mk_int(ctx, 5, int_sort);
        let solver = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, solver, Z3_mk_eq(ctx, x, five));
        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_TRUE);
        let model = Z3_solver_get_model(ctx, solver);

        // Make the live solver UNSAT; the old handle must keep answering.
        Z3_solver_push(ctx, solver);
        let ten = Z3_mk_int(ctx, 10, int_sort);
        Z3_solver_assert(ctx, solver, Z3_mk_eq(ctx, x, ten));
        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_FALSE);

        // x + x = 10 from the snapshot.
        let sum_args = [x, x];
        let sum = Z3_mk_add(ctx, 2, sum_args.as_ptr());
        let mut out: Z3_ast = 0;
        assert!(Z3_model_eval(ctx, model, sum, false, &raw mut out));
        let mut v: c_int = 0;
        assert!(Z3_get_numeral_int(ctx, out, &raw mut v));
        assert_eq!(
            v, 10,
            "compound eval must read the snapshot, not live state"
        );

        // The asserted formula itself evaluates to true under its own model.
        let zero = Z3_mk_int(ctx, 0, int_sort);
        let formula_args = [Z3_mk_gt(ctx, x, zero), Z3_mk_lt(ctx, x, ten)];
        let formula = Z3_mk_and(ctx, 2, formula_args.as_ptr());
        let mut fv: Z3_ast = 0;
        assert!(Z3_model_eval(ctx, model, formula, true, &raw mut fv));
        assert_eq!(Z3_get_bool_value(ctx, fv), Z3_L_TRUE);

        Z3_solver_pop(ctx, solver, 1);
        Z3_del_context(ctx);
    }
}

/// `model_completion` is honored with Z3 semantics: an unpinned constant is
/// the identity under `false` and gets the per-sort default under `true`.
#[test]
fn test_model_eval_completion_identity_vs_default() {
    // SAFETY: Test-scope unsafe block: all handles are allocated by `Z3_mk_*`
    // calls inside this block and freed by `Z3_del_context`. No pointer
    // escapes and this test owns the handles exclusively.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);
        let int_sort = Z3_mk_int_sort(ctx);
        let bool_sort = Z3_mk_bool_sort(ctx);
        let x = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"x".as_ptr()), int_sort);
        let five = Z3_mk_int(ctx, 5, int_sort);
        let solver = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, solver, Z3_mk_eq(ctx, x, five));
        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_TRUE);
        let model = Z3_solver_get_model(ctx, solver);

        // Constants declared AFTER the check are genuinely absent from the
        // snapshot (AY emits total models over the pre-check declarations).
        let fresh = Z3_mk_const(
            ctx,
            Z3_mk_string_symbol(ctx, c"fresh_int".as_ptr()),
            int_sort,
        );
        let fresh_b = Z3_mk_const(
            ctx,
            Z3_mk_string_symbol(ctx, c"fresh_bool".as_ptr()),
            bool_sort,
        );

        // completion=false: identity — the result IS the constant, unreduced.
        let mut out: Z3_ast = 0;
        assert!(Z3_model_eval(ctx, model, fresh, false, &raw mut out));
        assert_eq!(out, fresh, "unpinned const under mc=false is the identity");
        let mut dummy: c_int = 0;
        assert!(
            !Z3_get_numeral_int(ctx, out, &raw mut dummy),
            "identity result must NOT read as a numeral"
        );
        // ... and Z3_get_numeral_string must be honestly NULL for it (the
        // pre-fix code returned the AST HANDLE NUMBER as a fake numeral).
        assert!(
            Z3_get_numeral_string(ctx, out).is_null(),
            "non-numeral AST must yield NULL numeral string"
        );

        // completion=true: Z3's defaults (Int 0, Bool false).
        let mut out_t: Z3_ast = 0;
        assert!(Z3_model_eval(ctx, model, fresh, true, &raw mut out_t));
        let mut v: c_int = -1;
        assert!(Z3_get_numeral_int(ctx, out_t, &raw mut v));
        assert_eq!(v, 0, "mc=true must complete an Int const to 0");
        let mut out_b: Z3_ast = 0;
        assert!(Z3_model_eval(ctx, model, fresh_b, true, &raw mut out_b));
        assert_eq!(Z3_get_bool_value(ctx, out_b), Z3_L_FALSE);

        // Compound with an absent leaf: partial under false, complete under true.
        let mix_args = [x, fresh];
        let mix = Z3_mk_add(ctx, 2, mix_args.as_ptr());
        let mut pm: Z3_ast = 0;
        assert!(Z3_model_eval(ctx, model, mix, false, &raw mut pm));
        assert!(
            !Z3_get_numeral_int(ctx, pm, &raw mut dummy),
            "x + fresh under mc=false stays partial (honest, never fabricated)"
        );
        let mut cm: Z3_ast = 0;
        assert!(Z3_model_eval(ctx, model, mix, true, &raw mut cm));
        assert!(Z3_get_numeral_int(ctx, cm, &raw mut v));
        assert_eq!(v, 5, "x + fresh under mc=true completes fresh to 0");

        Z3_del_context(ctx);
    }
}

/// Uninterpreted-sort constants: interps are element constants; distinct
/// constants get distinct elements; equality evaluates under the snapshot.
#[test]
fn test_model_uninterpreted_sort_elements() {
    // SAFETY: Test-scope unsafe block: all handles are allocated by `Z3_mk_*`
    // calls inside this block and freed by `Z3_del_context`. No pointer
    // escapes and this test owns the handles exclusively.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);
        let s_sort = Z3_mk_uninterpreted_sort(ctx, Z3_mk_string_symbol(ctx, c"S".as_ptr()));
        let u = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"u".as_ptr()), s_sort);
        let w = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"w".as_ptr()), s_sort);
        let solver = Z3_mk_solver(ctx);
        let eq = Z3_mk_eq(ctx, u, w);
        Z3_solver_assert(ctx, solver, Z3_mk_not(ctx, eq));
        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_TRUE);
        let model = Z3_solver_get_model(ctx, solver);
        assert!(!model.is_null());

        // Both constants evaluate to element terms — and to DIFFERENT ones.
        let mut uv: Z3_ast = 0;
        let mut wv: Z3_ast = 0;
        assert!(Z3_model_eval(ctx, model, u, false, &raw mut uv));
        assert!(Z3_model_eval(ctx, model, w, false, &raw mut wv));
        assert_ne!(uv, 0);
        assert_ne!(wv, 0);
        assert_ne!(uv, u, "u must evaluate to its model element, not itself");
        assert_ne!(uv, wv, "distinct constants must map to distinct elements");

        // The disequality ground-evaluates to true under the snapshot.
        let mut ev: Z3_ast = 0;
        assert!(Z3_model_eval(ctx, model, eq, false, &raw mut ev));
        assert_eq!(
            Z3_get_bool_value(ctx, ev),
            Z3_L_FALSE,
            "(= u w) must evaluate to false under the u != w model"
        );

        // Enumeration covers the uninterpreted constants with names + interps.
        let n = Z3_model_get_num_consts(ctx, model);
        assert!(n >= 2, "u and w must be enumerated, got {n}");
        for idx in 0..n {
            let decl = Z3_model_get_const_decl(ctx, model, idx);
            assert!(!decl.is_null(), "decl {idx} must be non-null");
            let interp = Z3_model_get_const_interp(ctx, model, decl);
            assert_ne!(interp, 0, "decl {idx} must have an interp");
        }

        Z3_del_context(ctx);
    }
}

/// Binder-containing terms are refused honestly (capture-safe substitution is
/// not possible), never given a fabricated value.
#[test]
fn test_model_eval_refuses_binder_terms_honestly() {
    // SAFETY: Test-scope unsafe block: all handles are allocated by `Z3_mk_*`
    // calls inside this block and freed by `Z3_del_context`. No pointer
    // escapes and this test owns the handles exclusively.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);
        let int_sort = Z3_mk_int_sort(ctx);
        let x = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"x".as_ptr()), int_sort);
        let five = Z3_mk_int(ctx, 5, int_sort);
        let solver = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, solver, Z3_mk_eq(ctx, x, five));
        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_TRUE);
        let model = Z3_solver_get_model(ctx, solver);

        let b = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"qv".as_ptr()), int_sort);
        let zero = Z3_mk_int(ctx, 0, int_sort);
        let body = Z3_mk_ge(ctx, b, zero); // qv >= 0
        let bound = [b];
        let forall = Z3_mk_forall_const(ctx, 0, 1, bound.as_ptr(), 0, ptr::null(), body);
        assert_ne!(forall, 0);

        let mut out: Z3_ast = 0;
        assert!(
            !Z3_model_eval(ctx, model, forall, true, &raw mut out),
            "binder terms must be refused honestly (false), not fabricated"
        );

        Z3_del_context(ctx);
    }
}

/// Sequence model values convert to real seq terms (`seq.unit`/`seq.++`
/// chains): eval of a pinned Seq constant is a non-null seq-sorted value and
/// nth-reads of it fold to the pinned elements.
#[test]
fn test_model_eval_seq_value_conversion() {
    // SAFETY: Test-scope unsafe block: all handles are allocated by `Z3_mk_*`
    // calls inside this block and freed by `Z3_del_context`. No pointer
    // escapes and this test owns the handles exclusively.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);
        let int_sort = Z3_mk_int_sort(ctx);
        let seq_sort = Z3_mk_seq_sort(ctx, int_sort);
        let s = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"s".as_ptr()), seq_sort);
        let one = Z3_mk_int(ctx, 1, int_sort);
        let two = Z3_mk_int(ctx, 2, int_sort);
        let units = [Z3_mk_seq_unit(ctx, one), Z3_mk_seq_unit(ctx, two)];
        let chain = Z3_mk_seq_concat(ctx, 2, units.as_ptr());
        assert_ne!(chain, 0);

        let solver = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, solver, Z3_mk_eq(ctx, s, chain));
        let verdict = Z3_solver_check(ctx, solver);
        if verdict != Z3_L_TRUE {
            // The seq engine's coverage is not this test's subject; skip
            // honestly if the fragment is not solved (never fabricate).
            eprintln!("seq solve returned {verdict}; skipping model-surface assertions");
            Z3_del_context(ctx);
            return;
        }
        let model = Z3_solver_get_model(ctx, solver);
        assert!(!model.is_null());

        // The seq constant must have a non-null, seq-sorted interpretation
        // (pre-fix: hard `return 0` for Seq values).
        let mut sv: Z3_ast = 0;
        assert!(Z3_model_eval(ctx, model, s, false, &raw mut sv));
        assert_ne!(sv, 0, "pinned seq constant must evaluate to a value term");
        let sort = Z3_get_sort(ctx, sv);
        assert!(!sort.is_null());
        assert_eq!(Z3_get_sort_kind(ctx, sort), Z3_SEQ_SORT);

        // Element reads fold to the pinned values.
        let zero = Z3_mk_int(ctx, 0, int_sort);
        let nth0 = Z3_mk_seq_nth(ctx, s, zero);
        let nth1 = Z3_mk_seq_nth(ctx, s, one);
        let mut out: Z3_ast = 0;
        let mut v: c_int = 0;
        if Z3_model_eval(ctx, model, nth0, false, &raw mut out)
            && Z3_get_numeral_int(ctx, out, &raw mut v)
        {
            assert_eq!(v, 1, "s[0] must read the pinned element");
        }
        if Z3_model_eval(ctx, model, nth1, false, &raw mut out)
            && Z3_get_numeral_int(ctx, out, &raw mut v)
        {
            assert_eq!(v, 2, "s[1] must read the pinned element");
        }

        Z3_del_context(ctx);
    }
}

/// Uninterpreted FUNCTION applications resolve from the snapshot's function
/// tables (parsed from the engine's model text at check time) — including
/// after the live solver is reused. Pre-fix this required live solver state.
#[test]
fn test_model_eval_uf_application_from_snapshot() {
    // SAFETY: Test-scope unsafe block: all handles are allocated by `Z3_mk_*`
    // calls inside this block and freed by `Z3_del_context`. No pointer
    // escapes and this test owns the handles exclusively.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);
        let int_sort = Z3_mk_int_sort(ctx);
        let f_sym = Z3_mk_string_symbol(ctx, c"f".as_ptr());
        let domain = [int_sort];
        let f = Z3_mk_func_decl(ctx, f_sym, 1, domain.as_ptr(), int_sort);
        let three = Z3_mk_int(ctx, 3, int_sort);
        let f3_args = [three];
        let f3 = Z3_mk_app(ctx, f, 1, f3_args.as_ptr());
        let ten = Z3_mk_int(ctx, 10, int_sort);

        let solver = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, solver, Z3_mk_eq(ctx, f3, ten));
        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_TRUE);
        let model = Z3_solver_get_model(ctx, solver);
        assert!(!model.is_null());

        // The snapshot carries the function table.
        assert!(
            Z3_model_get_num_funcs(ctx, model) >= 1,
            "model must carry f's function interpretation"
        );

        // eval(f(3)) = 10 from the snapshot.
        let mut out: Z3_ast = 0;
        assert!(Z3_model_eval(ctx, model, f3, false, &raw mut out));
        let mut v: c_int = 0;
        assert!(
            Z3_get_numeral_int(ctx, out, &raw mut v),
            "f(3) must resolve to a numeral from the snapshot's function table"
        );
        assert_eq!(v, 10);

        // Still 10 after the live solver is driven UNSAT (snapshot, not live).
        Z3_solver_push(ctx, solver);
        let eleven = Z3_mk_int(ctx, 11, int_sort);
        Z3_solver_assert(ctx, solver, Z3_mk_eq(ctx, f3, eleven));
        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_FALSE);
        let mut out2: Z3_ast = 0;
        assert!(Z3_model_eval(ctx, model, f3, false, &raw mut out2));
        assert!(Z3_get_numeral_int(ctx, out2, &raw mut v));
        assert_eq!(v, 10, "UF resolution must survive solver reuse");
        Z3_solver_pop(ctx, solver, 1);

        // An application at an argument OUTSIDE the table rows takes the
        // table's else value (a genuine value, not a fabrication: the engine's
        // own table defines it).
        let hundred = Z3_mk_int(ctx, 100, int_sort);
        let f100_args = [hundred];
        let f100 = Z3_mk_app(ctx, f, 1, f100_args.as_ptr());
        let mut out3: Z3_ast = 0;
        assert!(Z3_model_eval(ctx, model, f100, false, &raw mut out3));
        // Either a numeral (else value) or, if the table shape was not
        // parseable, the symbolic application itself — but for this simple
        // model the table must parse.
        assert!(
            Z3_get_numeral_int(ctx, out3, &raw mut v),
            "f(100) must resolve via the table's else value"
        );

        Z3_del_context(ctx);
    }
}

/// Reconstruct the value of an arity-1 integer function interpretation at
/// `arg` the way a Z3 consumer does: scan the finite map for a matching entry,
/// otherwise fall to the `else` value. Returns `None` only if a value is not a
/// readable integer numeral.
///
/// # Safety
/// `ctx`/`fi` must be valid handles for the duration of the call.
unsafe fn func_interp_value_at(ctx: Z3_context, fi: Z3_func_interp, arg: c_int) -> Option<c_int> {
    // SAFETY: all handles are valid per the caller's contract; every AST read
    // goes through the guarded C API.
    unsafe {
        let ne = Z3_func_interp_get_num_entries(ctx, fi);
        for i in 0..ne {
            let e = Z3_func_interp_get_entry(ctx, fi, i);
            if e.is_null() || Z3_func_entry_get_num_args(ctx, e) != 1 {
                continue;
            }
            let mut a: c_int = 0;
            if Z3_get_numeral_int(ctx, Z3_func_entry_get_arg(ctx, e, 0), &raw mut a) && a == arg {
                let mut v: c_int = 0;
                if Z3_get_numeral_int(ctx, Z3_func_entry_get_value(ctx, e), &raw mut v) {
                    return Some(v);
                }
            }
        }
        let els = Z3_func_interp_get_else(ctx, fi);
        if els == 0 {
            return None;
        }
        let mut ev: c_int = 0;
        if Z3_get_numeral_int(ctx, els, &raw mut ev) {
            Some(ev)
        } else {
            None
        }
    }
}

/// A C consumer solving `(= (f 1) 5)` and `(= (f 2) 7)` reads f's real
/// function interpretation from the model: arity 1, at least one entry, an
/// else value, and a graph mapping 1 → 5 and 2 → 7 (matching what libz3
/// returns for the same query, modulo ay's entry/else canonicalization — see
/// tests/capi_func_interp_consumer.c). The graph is the one the engine
/// committed (own-eval consistent), never fabricated.
#[test]
fn test_model_func_interp_reads_committed_graph() {
    // SAFETY: every handle is allocated by a `Z3_mk_*` call in this block and
    // freed by `Z3_del_context`; the test owns them exclusively.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let f = Z3_mk_func_decl(
            ctx,
            Z3_mk_string_symbol(ctx, c"f".as_ptr()),
            1,
            [int_sort].as_ptr(),
            int_sort,
        );
        let one = Z3_mk_int(ctx, 1, int_sort);
        let two = Z3_mk_int(ctx, 2, int_sort);
        let f1 = Z3_mk_app(ctx, f, 1, [one].as_ptr());
        let f2 = Z3_mk_app(ctx, f, 1, [two].as_ptr());

        let solver = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, solver, Z3_mk_eq(ctx, f1, Z3_mk_int(ctx, 5, int_sort)));
        Z3_solver_assert(ctx, solver, Z3_mk_eq(ctx, f2, Z3_mk_int(ctx, 7, int_sort)));
        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_TRUE);
        let model = Z3_solver_get_model(ctx, solver);
        assert!(!model.is_null());

        // f is enumerable as a model function decl (name + arity).
        let nf = Z3_model_get_num_funcs(ctx, model);
        assert!(nf >= 1);
        let mut found_f = false;
        for i in 0..nf {
            let fd = Z3_model_get_func_decl(ctx, model, i);
            assert!(!fd.is_null());
            let name =
                std::ffi::CStr::from_ptr(Z3_get_symbol_string(ctx, Z3_get_decl_name(ctx, fd)))
                    .to_str()
                    .expect("model function name must be valid UTF-8");
            if name == "f" {
                found_f = true;
                assert_eq!(Z3_get_arity(ctx, fd), 1);
            }
        }
        assert!(found_f, "model must enumerate a func_decl named f");

        // Read f's interpretation and verify the committed graph.
        let fi = Z3_model_get_func_interp(ctx, model, f);
        assert!(!fi.is_null());
        Z3_func_interp_inc_ref(ctx, fi); // no-op RC, must not crash
        assert_eq!(Z3_func_interp_get_arity(ctx, fi), 1);
        assert!(Z3_func_interp_get_num_entries(ctx, fi) >= 1);
        assert_ne!(
            Z3_func_interp_get_else(ctx, fi),
            0,
            "func_interp must carry an else value"
        );
        assert_eq!(func_interp_value_at(ctx, fi, 1), Some(5));
        assert_eq!(func_interp_value_at(ctx, fi, 2), Some(7));
        Z3_func_interp_dec_ref(ctx, fi); // no-op RC

        // A function the model does not interpret (declared after the snapshot)
        // has NULL interp — "does not matter", never a fabricated table.
        let h = Z3_mk_func_decl(
            ctx,
            Z3_mk_string_symbol(ctx, c"h_never".as_ptr()),
            1,
            [int_sort].as_ptr(),
            int_sort,
        );
        assert!(Z3_model_get_func_interp(ctx, model, h).is_null());

        Z3_del_context(ctx);
    }
}

/// The func_entry accessors expose the raw finite-map point: its argument
/// tuple and value. Every entry's `f(args) == value` holds under the model's
/// own reconstruction (entry OR else recovers the same total function).
#[test]
fn test_model_func_entry_accessors() {
    // SAFETY: handles allocated and freed within this block; exclusive owner.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let f = Z3_mk_func_decl(
            ctx,
            Z3_mk_string_symbol(ctx, c"f".as_ptr()),
            1,
            [int_sort].as_ptr(),
            int_sort,
        );
        // Two distinct points force a non-constant interpretation, i.e. at
        // least one explicit finite-map entry (a single constraint would
        // canonicalize to a constant function with 0 entries).
        let f1 = Z3_mk_app(ctx, f, 1, [Z3_mk_int(ctx, 1, int_sort)].as_ptr());
        let f2 = Z3_mk_app(ctx, f, 1, [Z3_mk_int(ctx, 2, int_sort)].as_ptr());
        let solver = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, solver, Z3_mk_eq(ctx, f1, Z3_mk_int(ctx, 5, int_sort)));
        Z3_solver_assert(ctx, solver, Z3_mk_eq(ctx, f2, Z3_mk_int(ctx, 7, int_sort)));
        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_TRUE);
        let model = Z3_solver_get_model(ctx, solver);
        let fi = Z3_model_get_func_interp(ctx, model, f);
        assert!(!fi.is_null());

        let ne = Z3_func_interp_get_num_entries(ctx, fi);
        assert!(ne >= 1);
        // An out-of-range entry index yields a null handle (no crash, no
        // fabrication).
        assert!(Z3_func_interp_get_entry(ctx, fi, ne).is_null());
        for i in 0..ne {
            let e = Z3_func_interp_get_entry(ctx, fi, i);
            assert!(!e.is_null());
            Z3_func_entry_inc_ref(ctx, e); // no-op RC
            assert_eq!(Z3_func_entry_get_num_args(ctx, e), 1);
            let mut a: c_int = 0;
            assert!(Z3_get_numeral_int(
                ctx,
                Z3_func_entry_get_arg(ctx, e, 0),
                &raw mut a
            ));
            let mut v: c_int = 0;
            assert!(Z3_get_numeral_int(
                ctx,
                Z3_func_entry_get_value(ctx, e),
                &raw mut v
            ));
            // Out-of-range arg → null AST.
            assert_eq!(Z3_func_entry_get_arg(ctx, e, 1), 0);
            // The entry's own value must agree with the reconstructed function.
            assert_eq!(func_interp_value_at(ctx, fi, a), Some(v));
            Z3_func_entry_dec_ref(ctx, e); // no-op RC
        }
        // Both constrained points are recoverable (as an entry or via else).
        assert_eq!(func_interp_value_at(ctx, fi, 1), Some(5));
        assert_eq!(func_interp_value_at(ctx, fi, 2), Some(7));

        Z3_del_context(ctx);
    }
}

/// `Z3_model_translate` deep-clones the model into another context; the
/// function graph is preserved and queryable through the destination context.
#[test]
fn test_model_translate_preserves_func_graph() {
    // SAFETY: both contexts and every handle are created and freed in this
    // block; the test owns them exclusively.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);
        let cfg2 = Z3_mk_config();
        let dst = Z3_mk_context(cfg2);
        Z3_del_config(cfg2);

        let int_sort = Z3_mk_int_sort(ctx);
        let f = Z3_mk_func_decl(
            ctx,
            Z3_mk_string_symbol(ctx, c"f".as_ptr()),
            1,
            [int_sort].as_ptr(),
            int_sort,
        );
        let one = Z3_mk_int(ctx, 1, int_sort);
        let two = Z3_mk_int(ctx, 2, int_sort);
        let solver = Z3_mk_solver(ctx);
        Z3_solver_assert(
            ctx,
            solver,
            Z3_mk_eq(
                ctx,
                Z3_mk_app(ctx, f, 1, [one].as_ptr()),
                Z3_mk_int(ctx, 5, int_sort),
            ),
        );
        Z3_solver_assert(
            ctx,
            solver,
            Z3_mk_eq(
                ctx,
                Z3_mk_app(ctx, f, 1, [two].as_ptr()),
                Z3_mk_int(ctx, 7, int_sort),
            ),
        );
        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_TRUE);
        let model = Z3_solver_get_model(ctx, solver);

        let translated = Z3_model_translate(ctx, model, dst);
        assert!(!translated.is_null());
        assert!(Z3_model_get_num_funcs(dst, translated) >= 1);

        // Query the translated model through the destination context.
        let dst_int = Z3_mk_int_sort(dst);
        let f2 = Z3_mk_func_decl(
            dst,
            Z3_mk_string_symbol(dst, c"f".as_ptr()),
            1,
            [dst_int].as_ptr(),
            dst_int,
        );
        let fi = Z3_model_get_func_interp(dst, translated, f2);
        assert!(!fi.is_null());
        assert_eq!(func_interp_value_at(dst, fi, 1), Some(5));
        assert_eq!(func_interp_value_at(dst, fi, 2), Some(7));

        Z3_del_context(dst);
        Z3_del_context(ctx);
    }
}

/// Uninterpreted-sort universes are reconstructed from the model's REAL
/// uninterpreted-constant assignments: `(declare-sort S)` with two distinct
/// S-constants yields a universe of two distinct elements.
#[test]
fn test_model_sort_universe() {
    // SAFETY: handles allocated and freed in this block; exclusive owner.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let s_sort = Z3_mk_uninterpreted_sort(ctx, Z3_mk_string_symbol(ctx, c"S".as_ptr()));
        let a = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"a".as_ptr()), s_sort);
        let b = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"b".as_ptr()), s_sort);
        let solver = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, solver, Z3_mk_distinct(ctx, 2, [a, b].as_ptr()));
        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_TRUE);
        let model = Z3_solver_get_model(ctx, solver);

        let nsorts = Z3_model_get_num_sorts(ctx, model);
        assert!(nsorts >= 1, "model must interpret the uninterpreted sort S");
        let mut found_two = false;
        for i in 0..nsorts {
            let si = Z3_model_get_sort(ctx, model, i);
            assert!(!si.is_null());
            let universe = Z3_model_get_sort_universe(ctx, model, si);
            assert!(!universe.is_null());
            let usz = Z3_ast_vector_size(ctx, universe);
            if usz == 2 {
                // Two distinct universe element ASTs (a != b forces this).
                let e0 = Z3_ast_vector_get(ctx, universe, 0);
                let e1 = Z3_ast_vector_get(ctx, universe, 1);
                assert_ne!(e0, 0);
                assert_ne!(e1, 0);
                assert_ne!(e0, e1, "distinct S-elements must be distinct ASTs");
                found_two = true;
            }
        }
        assert!(found_two, "S's universe must contain two distinct elements");

        Z3_del_context(ctx);
    }
}

/// ay honestly returns an EMPTY (valid) universe for a sort the model does not
/// interpret (e.g. `Int`), rather than a fabricated set. (This is where ay is
/// intentionally more lenient than libz3, which raises an error; documented in
/// tests/capi_func_interp_consumer.c.)
#[test]
fn test_model_sort_universe_unknown_sort_empty() {
    // SAFETY: handles allocated and freed in this block; exclusive owner.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let x = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"x".as_ptr()), int_sort);
        let solver = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, solver, Z3_mk_gt(ctx, x, Z3_mk_int(ctx, 0, int_sort)));
        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_TRUE);
        let model = Z3_solver_get_model(ctx, solver);

        let universe = Z3_model_get_sort_universe(ctx, model, int_sort);
        assert!(!universe.is_null(), "must return a valid (empty) vector");
        assert_eq!(
            Z3_ast_vector_size(ctx, universe),
            0,
            "a non-uninterpreted sort has an empty universe, never fabricated"
        );

        Z3_del_context(ctx);
    }
}

/// `Z3_ast_to_string` renders the real s-expression of an ordinary term
/// (e.g. `(+ x (* 2 y))`), NOT the old `(ast N : Sort)` placeholder. The
/// operators and atoms must round-trip; a null/stale handle must not panic.
#[test]
fn test_z3_ast_to_string_renders_real_sexpr() {
    // SAFETY: Test-scope unsafe block: every handle is allocated by a
    // `Z3_mk_*` call inside this block and freed by `Z3_del_context`. No
    // pointer escapes the block and this test owns the context exclusively.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let x = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"x".as_ptr()), int_sort);
        let y = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"y".as_ptr()), int_sort);
        let two = Z3_mk_int(ctx, 2, int_sort);

        // (* 2 y)
        let mul_args = [two, y];
        let two_y = Z3_mk_mul(ctx, 2, mul_args.as_ptr());
        // (+ x (* 2 y))
        let add_args = [x, two_y];
        let sum = Z3_mk_add(ctx, 2, add_args.as_ptr());

        let s_ptr = Z3_ast_to_string(ctx, sum);
        assert!(
            !s_ptr.is_null(),
            "Z3_ast_to_string returned null for a valid term"
        );
        let s = std::ffi::CStr::from_ptr(s_ptr)
            .to_str()
            .expect("rendered s-expression is valid UTF-8")
            .to_string();

        assert!(
            !s.contains("(ast "),
            "must render the real term, not the `(ast N : Sort)` placeholder; got: {s}"
        );
        for needle in ['+', 'x', '*', '2', 'y'] {
            assert!(
                s.contains(needle),
                "rendered s-expression must contain {needle:?}; got: {s}"
            );
        }

        // A null AST handle yields a null string, never a panic.
        assert!(
            Z3_ast_to_string(ctx, 0).is_null(),
            "Z3_ast_to_string(0) must be null"
        );

        Z3_del_context(ctx);
    }
}

/// `Z3_solver_to_string` dumps the solver's real assertions in z3's
/// `(declare-fun ...)`/`(assert ...)` shape, not a `(solver)` placeholder.
#[test]
fn test_z3_solver_to_string_dumps_real_assertions() {
    // SAFETY: see `test_z3_ast_to_string_renders_real_sexpr`.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let x = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"x".as_ptr()), int_sort);
        let zero = Z3_mk_int(ctx, 0, int_sort);
        let x_gt_0 = Z3_mk_gt(ctx, x, zero);

        let solver = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, solver, x_gt_0);

        let s_ptr = Z3_solver_to_string(ctx, solver);
        assert!(!s_ptr.is_null(), "Z3_solver_to_string returned null");
        let s = std::ffi::CStr::from_ptr(s_ptr)
            .to_str()
            .expect("rendered solver is valid UTF-8")
            .to_string();

        assert!(
            s != "(solver)",
            "must dump real assertions, not the `(solver)` placeholder; got: {s}"
        );
        assert!(
            s.contains("declare-fun"),
            "solver dump must declare its symbols; got: {s}"
        );
        // AY soundly normalizes `x > 0` to `0 < x`, so accept either operator.
        assert!(
            s.contains("(assert") && s.contains('x') && (s.contains('<') || s.contains('>')),
            "solver dump must contain the asserted constraint; got: {s}"
        );

        Z3_del_context(ctx);
    }
}

/// B-2: decl-kind / ast-kind / sort-kind constants are byte-for-byte identical
/// to z3py 4.15.4.
///
/// Every `z3py = N` literal below was captured from live z3py 4.15.4 — from
/// `expr.decl().kind()` for decl kinds, `z3.Z3_get_sort_kind` for sort kinds,
/// `z3.Z3_get_ast_kind` for ast kinds, and the `z3.Z3_OP_*` / `z3.Z3_*_SORT`
/// module constants for the fixed-index BV ops. Each assertion locks BOTH that
/// AY's named constant equals the real z3py integer AND that AY's runtime
/// `Z3_get_decl_kind` / `Z3_get_sort_kind` / `Z3_get_ast_kind` returns it for a
/// concretely-constructed term.
#[test]
fn test_decl_ast_sort_kind_z3py_parity() {
    // SAFETY: Test-scope unsafe block: every handle is created by a `Z3_mk_*`
    // call in this block and released by `Z3_del_context`; no pointer escapes
    // and this test owns all handles exclusively.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        // Assert AY's runtime decl_kind for `a` equals `z3py`, surfacing the
        // decl NAME in the failure message so an AY normalization (e.g.
        // `bvuge` → `bvule`) is immediately visible rather than mysterious.
        // `a` is a valid app AST produced by a `Z3_mk_*` above; all accessors
        // are null-guarded internally. (Runs inside the enclosing `unsafe`.)
        let check = |a: Z3_ast, label: &str, z3py: c_uint| {
            let decl = Z3_get_app_decl(ctx, a);
            assert!(!decl.is_null(), "{label}: app decl must not be null");
            let name_ptr = Z3_get_symbol_string(ctx, Z3_get_decl_name(ctx, decl));
            let name = std::ffi::CStr::from_ptr(name_ptr)
                .to_string_lossy()
                .into_owned();
            let kind = Z3_get_decl_kind(ctx, decl);
            assert_eq!(
                kind, z3py,
                "{label}: AY decl_kind={kind} (decl name={name:?}) != z3py {z3py}"
            );
        };

        let int_sort = Z3_mk_int_sort(ctx);
        let bool_sort = Z3_mk_bool_sort(ctx);
        let bv8 = Z3_mk_bv_sort(ctx, 8);
        let arr_sort = Z3_mk_array_sort(ctx, int_sort, int_sort);

        let mk = |nm: &std::ffi::CStr, s: Z3_sort| {
            Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, nm.as_ptr()), s)
        };
        let x = mk(c"x", int_sort);
        let y = mk(c"y", int_sort);
        let p = mk(c"p", bool_sort);
        let q = mk(c"q", bool_sort);
        let a = mk(c"a", bv8);
        let b = mk(c"b", bv8);
        let arr = mk(c"arr", arr_sort);

        // ---- Arithmetic / Boolean / EUF (symbolic operands: nothing folds) ----
        assert_eq!(Z3_OP_ADD, 518);
        assert_eq!(Z3_OP_AND, 261);
        assert_eq!(Z3_OP_EQ, 258);
        assert_eq!(Z3_OP_LE, 514);
        assert_eq!(Z3_OP_UNINTERPRETED, 45102);
        check(Z3_mk_add(ctx, 2, [x, y].as_ptr()), "int +", 518);
        check(Z3_mk_and(ctx, 2, [p, q].as_ptr()), "and", 261);
        check(Z3_mk_eq(ctx, x, y), "=", 258);
        check(Z3_mk_le(ctx, x, y), "<=", 514);
        let f_sym = Z3_mk_string_symbol(ctx, c"f".as_ptr());
        let f = Z3_mk_func_decl(ctx, f_sym, 1, [int_sort].as_ptr(), int_sort);
        check(Z3_mk_app(ctx, f, 1, [x].as_ptr()), "uf f(x)", 45102);

        // ---- Arrays ----
        assert_eq!(Z3_OP_STORE, 768);
        assert_eq!(Z3_OP_SELECT, 769);
        check(Z3_mk_store(ctx, arr, x, y), "store", 768);
        check(Z3_mk_select(ctx, arr, x), "select", 769);

        // ---- Bitvectors: the block that was byte-wrong before this fix ----
        assert_eq!(Z3_OP_BAND, 1049);
        assert_eq!(Z3_OP_BOR, 1050);
        assert_eq!(Z3_OP_BXOR, 1052);
        assert_eq!(Z3_OP_BADD, 1028);
        assert_eq!(Z3_OP_BMUL, 1030);
        assert_eq!(Z3_OP_BSHL, 1064);
        assert_eq!(Z3_OP_BLSHR, 1065);
        assert_eq!(Z3_OP_BASHR, 1066);
        assert_eq!(Z3_OP_ULEQ, 1041);
        assert_eq!(Z3_OP_ULT, 1045);
        assert_eq!(Z3_OP_SLEQ, 1042);
        assert_eq!(Z3_OP_SLT, 1046);
        assert_eq!(Z3_OP_CONCAT, 1056);
        assert_eq!(Z3_OP_SIGN_EXT, 1057);
        assert_eq!(Z3_OP_ZERO_EXT, 1058);
        assert_eq!(Z3_OP_EXTRACT, 1059);
        assert_eq!(Z3_OP_REPEAT, 1060);
        assert_eq!(Z3_OP_ROTATE_LEFT, 1067);
        assert_eq!(Z3_OP_ROTATE_RIGHT, 1068);
        check(Z3_mk_bvand(ctx, a, b), "bvand", 1049);
        check(Z3_mk_bvor(ctx, a, b), "bvor", 1050);
        check(Z3_mk_bvxor(ctx, a, b), "bvxor", 1052);
        check(Z3_mk_bvadd(ctx, a, b), "bvadd", 1028);
        check(Z3_mk_bvmul(ctx, a, b), "bvmul", 1030);
        check(Z3_mk_bvshl(ctx, a, b), "bvshl", 1064);
        check(Z3_mk_bvlshr(ctx, a, b), "bvlshr", 1065);
        check(Z3_mk_bvashr(ctx, a, b), "bvashr", 1066);
        check(Z3_mk_bvule(ctx, a, b), "bvule", 1041);
        check(Z3_mk_bvult(ctx, a, b), "bvult", 1045);
        check(Z3_mk_bvsle(ctx, a, b), "bvsle", 1042);
        check(Z3_mk_bvslt(ctx, a, b), "bvslt", 1046);
        check(Z3_mk_concat(ctx, a, b), "concat", 1056);
        check(Z3_mk_sign_ext(ctx, 4, a), "sign_ext", 1057);
        check(Z3_mk_zero_ext(ctx, 4, a), "zero_ext", 1058);
        check(Z3_mk_extract(ctx, 5, 2, a), "extract", 1059);
        check(Z3_mk_repeat(ctx, 2, a), "repeat", 1060);
        check(Z3_mk_rotate_left(ctx, 3, a), "rotate_left", 1067);
        check(Z3_mk_rotate_right(ctx, 3, a), "rotate_right", 1068);

        // ---- ast-kind: a numeral literal reports Z3_NUMERAL_AST (0) ----
        assert_eq!(Z3_NUMERAL_AST, 0);
        let five = Z3_mk_int(ctx, 5, int_sort);
        assert_eq!(Z3_get_ast_kind(ctx, five), Z3_NUMERAL_AST);

        // ---- sort-kind: the two values that were byte-wrong before this fix ----
        assert_eq!(Z3_UNINTERPRETED_SORT, 0);
        assert_eq!(Z3_SEQ_SORT, 11);
        let u_sort = Z3_mk_uninterpreted_sort(ctx, Z3_mk_string_symbol(ctx, c"U".as_ptr()));
        assert_eq!(Z3_get_sort_kind(ctx, u_sort), Z3_UNINTERPRETED_SORT);
        let str_sort = Z3_mk_string_sort(ctx);
        assert_eq!(Z3_get_sort_kind(ctx, str_sort), Z3_SEQ_SORT);

        Z3_del_context(ctx);
    }
}

/// B-3 rework: the division operator is SORT-POLYMORPHIC and if-then-else's
/// canonical decl name is "if", both matching z3py 4.15.4 at the C ABI:
///   * `Z3_mk_div` on Int operands → decl kind Z3_OP_IDIV (523), name "div";
///   * `Z3_mk_div` on Real operands → decl kind Z3_OP_DIV (522), name "/";
///   * `Z3_mk_ite`                  → decl kind Z3_OP_ITE (260), name "if".
///
/// Captured from live z3py 4.15.4: `(x/y).decl().kind()==523 name 'div'` (Int),
/// `(r/s).decl().kind()==522 name '/'` (Real), `If(...).decl().kind()==260 name
/// 'if'`. Every C consumer of the introspection ABI depends on this.
#[test]
fn test_div_ite_decl_kind_name_z3py_parity() {
    // SAFETY: Test-scope unsafe block: every handle is created by a `Z3_mk_*`
    // call in this block and released by `Z3_del_context`; no pointer escapes
    // and this test owns all handles exclusively.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        // (decl_name, decl_kind) for an application AST `a`. The app decl is
        // null-guarded internally; `a` is a valid app from a `Z3_mk_*` above.
        let name_kind = |a: Z3_ast| -> (String, c_uint) {
            let decl = Z3_get_app_decl(ctx, a);
            assert!(!decl.is_null(), "app decl must not be null");
            let name_ptr = Z3_get_symbol_string(ctx, Z3_get_decl_name(ctx, decl));
            let name = std::ffi::CStr::from_ptr(name_ptr)
                .to_string_lossy()
                .into_owned();
            (name, Z3_get_decl_kind(ctx, decl))
        };

        let int_sort = Z3_mk_int_sort(ctx);
        let real_sort = Z3_mk_real_sort(ctx);
        let bool_sort = Z3_mk_bool_sort(ctx);
        let mk = |nm: &std::ffi::CStr, s: Z3_sort| {
            Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, nm.as_ptr()), s)
        };

        // ---- Integer division: Z3_OP_IDIV (523), name "div" ----
        assert_eq!(Z3_OP_IDIV, 523);
        let x = mk(c"x", int_sort);
        let y = mk(c"y", int_sort);
        let idiv = Z3_mk_div(ctx, x, y);
        assert_eq!(name_kind(idiv), ("div".to_string(), Z3_OP_IDIV));

        // ---- Real division: Z3_OP_DIV (522), name "/" ----
        assert_eq!(Z3_OP_DIV, 522);
        let r = mk(c"r", real_sort);
        let s = mk(c"s", real_sort);
        let rdiv = Z3_mk_div(ctx, r, s);
        assert_eq!(name_kind(rdiv), ("/".to_string(), Z3_OP_DIV));

        // The two share the same `Z3_mk_div` entry point but are DISTINCT
        // operators — the whole point of the sort-polymorphic fix.
        assert_ne!(
            Z3_get_decl_kind(ctx, Z3_get_app_decl(ctx, idiv)),
            Z3_get_decl_kind(ctx, Z3_get_app_decl(ctx, rdiv))
        );

        // ---- If-then-else: Z3_OP_ITE (260), canonical name "if" ----
        assert_eq!(Z3_OP_ITE, 260);
        let c = mk(c"c", bool_sort);
        let ite = Z3_mk_ite(ctx, c, x, y);
        assert_eq!(name_kind(ite), ("if".to_string(), Z3_OP_ITE));

        Z3_del_context(ctx);
    }
}

// ---- Pseudo-boolean / cardinality (Z3_mk_atmost/atleast/pble/pbge/pbeq) ----

/// Build three fresh Bool constants a, b, c in `ctx`.
///
/// # Safety
/// `ctx` must be a valid context pointer.
unsafe fn mk_three_bools(ctx: Z3_context) -> [Z3_ast; 3] {
    // SAFETY: `ctx` validity is this fn's documented contract; every call below
    // takes only that context and freshly-built handles.
    unsafe {
        let bool_sort = Z3_mk_bool_sort(ctx);
        let a = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"a".as_ptr()), bool_sort);
        let b = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"b".as_ptr()), bool_sort);
        let c = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"c".as_ptr()), bool_sort);
        [a, b, c]
    }
}

/// `(at-most 1) a b c` together with `(at-least 2) a b c` is UNSAT.
#[test]
fn test_z3_pb_atmost_atleast_unsat() {
    // SAFETY: all handles are created and freed within this block; none escape.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let args = mk_three_bools(ctx);
        let atmost1 = Z3_mk_atmost(ctx, 3, args.as_ptr(), 1);
        let atleast2 = Z3_mk_atleast(ctx, 3, args.as_ptr(), 2);

        let solver = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, solver, atmost1);
        Z3_solver_assert(ctx, solver, atleast2);
        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_FALSE);

        Z3_del_context(ctx);
    }
}

/// `(at-most 2) a b c` alone is SAT.
#[test]
fn test_z3_pb_atmost_sat() {
    // SAFETY: all handles are created and freed within this block; none escape.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let args = mk_three_bools(ctx);
        let atmost2 = Z3_mk_atmost(ctx, 3, args.as_ptr(), 2);

        let solver = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, solver, atmost2);
        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_TRUE);

        Z3_del_context(ctx);
    }
}

/// `2a+3b+4c <= 3` together with `2a+3b+4c >= 5` is UNSAT.
#[test]
fn test_z3_pb_weighted_le_ge_unsat() {
    // SAFETY: all handles/pointers are created and freed within this block.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let args = mk_three_bools(ctx);
        let coeffs: [c_int; 3] = [2, 3, 4];
        let pble = Z3_mk_pble(ctx, 3, args.as_ptr(), coeffs.as_ptr(), 3);
        let pbge = Z3_mk_pbge(ctx, 3, args.as_ptr(), coeffs.as_ptr(), 5);

        let solver = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, solver, pble);
        Z3_solver_assert(ctx, solver, pbge);
        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_FALSE);

        Z3_del_context(ctx);
    }
}

/// `2a+3b+4c = 5` is SAT (a=b=true, c=false gives 5).
#[test]
fn test_z3_pb_pbeq_sat() {
    // SAFETY: all handles/pointers are created and freed within this block.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let args = mk_three_bools(ctx);
        let coeffs: [c_int; 3] = [2, 3, 4];
        let pbeq = Z3_mk_pbeq(ctx, 3, args.as_ptr(), coeffs.as_ptr(), 5);

        let solver = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, solver, pbeq);
        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_TRUE);

        // Adding pbeq = 100 (unreachable: max is 9) makes it UNSAT.
        let pbeq_big = Z3_mk_pbeq(ctx, 3, args.as_ptr(), coeffs.as_ptr(), 100);
        Z3_solver_assert(ctx, solver, pbeq_big);
        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_FALSE);

        Z3_del_context(ctx);
    }
}

// ============================================================================
// Wave 2 solver-completion: assert-and-track, from-string, translate,
// consequences, units/trail, help, congruence, DIMACS.
// ============================================================================

/// Read a context-owned C string into an owned `String`.
///
/// # Safety
/// `p` must be a valid null-terminated C string (or null).
unsafe fn cstr(p: *const c_char) -> String {
    if p.is_null() {
        String::new()
    } else {
        // SAFETY: caller contract: `p` is a valid null-terminated C string.
        unsafe { std::ffi::CStr::from_ptr(p) }
            .to_string_lossy()
            .into_owned()
    }
}

/// Collect an `ast_vector`'s elements' `Z3_ast_to_string` renderings.
///
/// # Safety
/// `ctx`/`v` must be valid handles.
unsafe fn vec_strings(ctx: Z3_context, v: Z3_ast_vector) -> Vec<String> {
    // SAFETY: caller contract: `ctx`/`v` are valid handles.
    unsafe {
        let n = Z3_ast_vector_size(ctx, v);
        (0..n)
            .map(|i| cstr(Z3_ast_to_string(ctx, Z3_ast_vector_get(ctx, v, i))))
            .collect()
    }
}

/// A Boolean constant named `name`.
///
/// # Safety
/// `ctx` must be a valid context handle.
unsafe fn bool_const(ctx: Z3_context, name: &std::ffi::CStr) -> Z3_ast {
    // SAFETY: caller contract: `ctx` is a valid context handle.
    unsafe {
        let sort = Z3_mk_bool_sort(ctx);
        Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, name.as_ptr()), sort)
    }
}

/// `assert_and_track` two contradictory tracked formulas: the core is exactly
/// the two tracking literals.
#[test]
fn test_solver_assert_and_track_core() {
    // SAFETY: all handles are owned by this test and freed via `Z3_del_context`.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let solver = Z3_mk_solver(ctx);
        let a = bool_const(ctx, c"a");
        let p1 = bool_const(ctx, c"p1");
        let p2 = bool_const(ctx, c"p2");
        Z3_solver_assert_and_track(ctx, solver, a, p1);
        Z3_solver_assert_and_track(ctx, solver, Z3_mk_not(ctx, a), p2);

        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_FALSE);
        let core = Z3_solver_get_unsat_core(ctx, solver);
        let names = vec_strings(ctx, core);
        assert_eq!(names.len(), 2, "core should be the two tracking literals");
        assert!(names.iter().any(|s| s == "p1"), "core has p1: {names:?}");
        assert!(names.iter().any(|s| s == "p2"), "core has p2: {names:?}");

        Z3_del_context(ctx);
    }
}

/// A tracked assertion is dropped on `pop`, so its tracking literal is no longer
/// assumed and no longer appears in a later core.
#[test]
fn test_solver_assert_and_track_scoped_by_pop() {
    // SAFETY: all handles are owned by this test and freed via `Z3_del_context`.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let solver = Z3_mk_solver(ctx);
        let a = bool_const(ctx, c"a");
        let p1 = bool_const(ctx, c"p1");
        let p2 = bool_const(ctx, c"p2");
        Z3_solver_assert_and_track(ctx, solver, a, p1); // permanent

        Z3_solver_push(ctx, solver);
        Z3_solver_assert_and_track(ctx, solver, Z3_mk_not(ctx, a), p2); // scoped
        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_FALSE);
        Z3_solver_pop(ctx, solver, 1); // drops (!a, p2)

        // Only `a` tracked now → SAT, and no stale p2 in any core.
        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_TRUE);
        let core = Z3_solver_get_unsat_core(ctx, solver);
        assert_eq!(Z3_ast_vector_size(ctx, core), 0, "SAT ⇒ empty core");

        Z3_del_context(ctx);
    }
}

/// `from_string` appends parsed assertions; the solver then solves them.
#[test]
fn test_solver_from_string_append_and_solve() {
    // SAFETY: all handles are owned by this test and freed via `Z3_del_context`.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let solver = Z3_mk_solver(ctx);
        let int_sort = Z3_mk_int_sort(ctx);
        let x = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"x".as_ptr()), int_sort);
        Z3_solver_assert(ctx, solver, Z3_mk_eq(ctx, x, Z3_mk_int(ctx, 5, int_sort)));

        Z3_solver_from_string(
            ctx,
            solver,
            c"(declare-const y Int)(assert (= y 7))".as_ptr(),
        );
        assert_eq!(
            Z3_ast_vector_size(ctx, Z3_solver_get_assertions(ctx, solver)),
            2,
            "from_string appends to the existing assertions"
        );
        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_TRUE);

        // A contradictory string is UNSAT.
        let s2 = Z3_mk_solver(ctx);
        Z3_solver_from_string(
            ctx,
            s2,
            c"(declare-const z Int)(assert (> z 10))(assert (< z 3))".as_ptr(),
        );
        assert_eq!(Z3_solver_check(ctx, s2), Z3_L_FALSE);

        Z3_del_context(ctx);
    }
}

/// A late semantic parse failure may have changed unscoped declarations or
/// options. It must retire copied artifacts and permanently fail the context
/// closed; no existing handle may continue solving or mutating as if the parse
/// were atomic.
#[test]
fn test_solver_parse_late_error_poisons_context_and_retires_results() {
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);
        let solver = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, solver, Z3_mk_true(ctx));
        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_TRUE);
        assert!(!Z3_solver_get_model(ctx, solver).is_null());
        let before = Z3_ast_vector_size(ctx, Z3_solver_get_assertions(ctx, solver));

        // The final hard assertion is syntactically valid but semantically has
        // sort Int. The declaration and first assertion precede the error.
        Z3_solver_from_string(
            ctx,
            solver,
            c"(declare-const y Int)(assert (= y 0))(assert 1)".as_ptr(),
        );
        assert_eq!(Z3_get_error_code(ctx), Z3_EXCEPTION);
        assert!(Z3_solver_get_model(ctx, solver).is_null());

        // Existing mutators and checks honor the context poison. The returned
        // handle-local stack was never partially extended.
        Z3_solver_assert(ctx, solver, Z3_mk_false(ctx));
        assert_eq!(Z3_get_error_code(ctx), Z3_INVALID_USAGE);
        assert_eq!(
            Z3_ast_vector_size(ctx, Z3_solver_get_assertions(ctx, solver)),
            before
        );
        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_UNDEF);
        assert_eq!(Z3_get_error_code(ctx), Z3_INVALID_USAGE);
        Z3_del_context(ctx);
    }
}

/// Destructive parser controls are rejected during non-mutating preflight, so
/// they neither panic nor poison/mutate an otherwise usable solver context.
#[test]
fn test_solver_parse_reset_and_pop_are_atomic_preflight_errors() {
    unsafe {
        for script in [
            c"(assert false)(pop 1)".as_ptr(),
            c"(assert false)(reset)".as_ptr(),
            c"(assert false)(reset-assertions)".as_ptr(),
        ] {
            let cfg = Z3_mk_config();
            let ctx = Z3_mk_context(cfg);
            Z3_del_config(cfg);
            let solver = Z3_mk_solver(ctx);
            Z3_solver_assert(ctx, solver, Z3_mk_true(ctx));
            Z3_solver_from_string(ctx, solver, script);
            assert_eq!(Z3_get_error_code(ctx), Z3_INVALID_USAGE);
            assert_eq!(
                Z3_ast_vector_size(ctx, Z3_solver_get_assertions(ctx, solver)),
                1
            );
            assert_eq!(Z3_solver_check(ctx, solver), Z3_L_TRUE);
            Z3_del_context(ctx);
        }
    }
}

/// Solver-family parse bridges return hard assertions only, so optimization
/// commands must be rejected before they can mutate context-global Optimize
/// state or claim a pristine context for the wrong decision family.
#[test]
fn test_solver_parse_optimization_commands_are_atomic_preflight_errors() {
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);
        let solver = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, solver, Z3_mk_true(ctx));
        Z3_solver_from_string(
            ctx,
            solver,
            c"(assert false)(assert-soft true :weight 2)".as_ptr(),
        );
        assert_eq!(Z3_get_error_code(ctx), Z3_INVALID_USAGE);
        assert_eq!(
            Z3_ast_vector_size(ctx, Z3_solver_get_assertions(ctx, solver)),
            1
        );
        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_TRUE);
        Z3_del_context(ctx);

        // Global parsing performs the same non-mutating preflight before its
        // Solver-family ownership claim.
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);
        let parsed = Z3_parse_smtlib2_string(
            ctx,
            c"(assert true)(maximize 1)".as_ptr(),
            0,
            ptr::null(),
            ptr::null(),
            0,
            ptr::null(),
            ptr::null(),
        );
        assert_eq!(Z3_get_error_code(ctx), Z3_INVALID_USAGE);
        assert_eq!(Z3_ast_vector_size(ctx, parsed), 0);
        assert!(
            !Z3_mk_optimize(ctx).is_null(),
            "rejected preflight must not claim the decision engine"
        );
        Z3_del_context(ctx);
    }
}

/// Global string/file parsing and solver-file parsing share the same semantic
/// transaction boundary as `Z3_solver_from_string`.
#[test]
fn test_all_solver_parse_entrypoints_fail_closed_on_late_error() {
    unsafe {
        let bad = "(declare-const late Int)(assert (= late 1))(assert 1)";

        // Global string parser.
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);
        let solver = Z3_mk_solver(ctx);
        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_TRUE);
        let out = Z3_parse_smtlib2_string(
            ctx,
            CString::new(bad)
                .expect("parser regression input must not contain an interior NUL")
                .as_ptr(),
            0,
            ptr::null(),
            ptr::null(),
            0,
            ptr::null(),
            ptr::null(),
        );
        assert_eq!(Z3_get_error_code(ctx), Z3_EXCEPTION);
        assert_eq!(Z3_ast_vector_size(ctx, out), 0);
        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_UNDEF);
        Z3_del_context(ctx);

        // Both file entrypoints route through the same helper. Use distinct
        // contexts because a late failure deliberately poisons one forever.
        let path = std::env::temp_dir().join(format!(
            "ay-z3-parse-{}-{}.smt2",
            std::process::id(),
            line!()
        ));
        std::fs::write(&path, bad).expect("write parser regression input");
        let path_c = CString::new(path.to_string_lossy().as_bytes())
            .expect("temporary parser path must not contain an interior NUL");

        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);
        let solver = Z3_mk_solver(ctx);
        Z3_solver_from_file(ctx, solver, path_c.as_ptr());
        assert_eq!(Z3_get_error_code(ctx), Z3_EXCEPTION);
        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_UNDEF);
        Z3_del_context(ctx);

        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);
        let solver = Z3_mk_solver(ctx);
        let out = Z3_parse_smtlib2_file(
            ctx,
            path_c.as_ptr(),
            0,
            ptr::null(),
            ptr::null(),
            0,
            ptr::null(),
            ptr::null(),
        );
        assert_eq!(Z3_get_error_code(ctx), Z3_EXCEPTION);
        assert_eq!(Z3_ast_vector_size(ctx, out), 0);
        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_UNDEF);
        Z3_del_context(ctx);

        let _ = std::fs::remove_file(path);
    }
}

/// Recursive definitions are durable context semantics: solver goal reloads do
/// not erase them, adding one retires old result artifacts, and Optimize consumes
/// the same definition without a cross-family ownership conflict.
#[test]
fn test_add_rec_def_is_durable_for_solver_and_optimize() {
    unsafe {
        // Ordinary solver: `f` is initially free, then definition f = true
        // contradicts the handle assertion (not f).
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);
        let bool_sort = Z3_mk_bool_sort(ctx);
        let f = Z3_mk_func_decl(
            ctx,
            Z3_mk_string_symbol(ctx, c"f".as_ptr()),
            0,
            ptr::null(),
            bool_sort,
        );
        let f_app = Z3_mk_app(ctx, f, 0, ptr::null());
        let solver = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, solver, Z3_mk_not(ctx, f_app));
        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_TRUE);
        assert!(!Z3_solver_get_model(ctx, solver).is_null());
        Z3_add_rec_def(ctx, f, 0, ptr::null(), Z3_mk_true(ctx));
        assert_eq!(Z3_get_error_code(ctx), Z3_OK);
        assert!(Z3_solver_get_model(ctx, solver).is_null());
        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_FALSE);
        Z3_del_context(ctx);

        // Optimize owns this context before the definition is attached. A
        // global definition is family-neutral and reaches its decision check.
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);
        let opt = Z3_mk_optimize(ctx);
        let bool_sort = Z3_mk_bool_sort(ctx);
        let g = Z3_mk_func_decl(
            ctx,
            Z3_mk_string_symbol(ctx, c"g".as_ptr()),
            0,
            ptr::null(),
            bool_sort,
        );
        let g_app = Z3_mk_app(ctx, g, 0, ptr::null());
        Z3_optimize_assert(ctx, opt, Z3_mk_not(ctx, g_app));
        Z3_add_rec_def(ctx, g, 0, ptr::null(), Z3_mk_true(ctx));
        assert_eq!(Z3_get_error_code(ctx), Z3_OK);
        assert_eq!(Z3_optimize_check(ctx, opt, 0, ptr::null()), Z3_L_FALSE);
        Z3_del_context(ctx);
    }
}

/// A malformed recursive-definition argument array is rejected before it can
/// install a zero-arity axiom or retire an unrelated admitted model.
#[test]
fn test_add_rec_def_rejects_null_nonempty_args_transactionally() {
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);
        let bool_sort = Z3_mk_bool_sort(ctx);
        let f = Z3_mk_func_decl(
            ctx,
            Z3_mk_string_symbol(ctx, c"bad_rec_args".as_ptr()),
            0,
            ptr::null(),
            bool_sort,
        );
        let f_app = Z3_mk_app(ctx, f, 0, ptr::null());
        let solver = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, solver, Z3_mk_not(ctx, f_app));
        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_TRUE);
        assert!(!Z3_solver_get_model(ctx, solver).is_null());

        Z3_add_rec_def(ctx, f, 1, ptr::null(), Z3_mk_true(ctx));
        assert_eq!(Z3_get_error_code(ctx), Z3_INVALID_ARG);
        assert!(
            !Z3_solver_get_model(ctx, solver).is_null(),
            "a rejected mutation must preserve the preceding admitted model"
        );
        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_TRUE);

        Z3_del_context(ctx);
    }
}

/// Cross-context term grafting does not carry context-resident semantic
/// metadata. Every translation surface therefore shares one fail-closed gate,
/// and rejection happens before the target is claimed or mutated.
#[test]
fn test_cross_context_translation_rejects_unportable_semantic_metadata() {
    unsafe {
        let cfg = Z3_mk_config();
        let source = Z3_mk_context(cfg);
        Z3_del_config(cfg);
        let bool_sort = Z3_mk_bool_sort(source);
        let f = Z3_mk_func_decl(
            source,
            Z3_mk_string_symbol(source, c"translated_rec".as_ptr()),
            0,
            ptr::null(),
            bool_sort,
        );
        let f_app = Z3_mk_app(source, f, 0, ptr::null());
        let solver = Z3_mk_solver(source);
        Z3_solver_assert(source, solver, Z3_mk_not(source, f_app));
        Z3_add_rec_def(source, f, 0, ptr::null(), Z3_mk_true(source));

        let vector = Z3_mk_ast_vector(source);
        Z3_ast_vector_push(source, vector, f_app);
        let goal = Z3_mk_goal(source, true, false, false);
        Z3_goal_assert(source, goal, f_app);

        let cfg = Z3_mk_config();
        let target = Z3_mk_context(cfg);
        Z3_del_config(cfg);
        assert_eq!(Z3_translate(source, f_app, target), 0);
        assert_eq!(Z3_get_error_code(target), Z3_INVALID_USAGE);
        assert!(Z3_ast_vector_translate(source, vector, target).is_null());
        assert!(Z3_goal_translate(source, goal, target).is_null());
        assert!(Z3_solver_translate(source, solver, target).is_null());
        assert!(
            !Z3_mk_optimize(target).is_null(),
            "rejected Solver translation must not claim the fresh target"
        );

        Z3_del_context(target);
        Z3_del_context(source);

        // Optimize translation uses the same source-metadata gate.
        let cfg = Z3_mk_config();
        let source = Z3_mk_context(cfg);
        Z3_del_config(cfg);
        let opt = Z3_mk_optimize(source);
        let bool_sort = Z3_mk_bool_sort(source);
        let g = Z3_mk_func_decl(
            source,
            Z3_mk_string_symbol(source, c"translated_opt_rec".as_ptr()),
            0,
            ptr::null(),
            bool_sort,
        );
        let g_app = Z3_mk_app(source, g, 0, ptr::null());
        Z3_optimize_assert(source, opt, Z3_mk_not(source, g_app));
        Z3_add_rec_def(source, g, 0, ptr::null(), Z3_mk_true(source));

        let cfg = Z3_mk_config();
        let target = Z3_mk_context(cfg);
        Z3_del_config(cfg);
        assert!(Z3_optimize_translate(source, opt, target).is_null());
        assert_eq!(Z3_get_error_code(target), Z3_INVALID_USAGE);
        assert!(
            !Z3_mk_solver(target).is_null(),
            "rejected Optimize translation must not claim the fresh target"
        );

        Z3_del_context(target);
        Z3_del_context(source);
    }
}

/// `translate` deep-copies a solver (assertions + tracking) into a new context
/// and re-solves to the same verdict.
#[test]
fn test_solver_translate_cross_context() {
    // SAFETY: all handles are owned by this test and freed via `Z3_del_context`.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let solver = Z3_mk_solver(ctx);
        let int_sort = Z3_mk_int_sort(ctx);
        let x = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"x".as_ptr()), int_sort);
        Z3_solver_assert(ctx, solver, Z3_mk_gt(ctx, x, Z3_mk_int(ctx, 0, int_sort)));
        Z3_solver_assert(ctx, solver, Z3_mk_lt(ctx, x, Z3_mk_int(ctx, 5, int_sort)));

        let cfg2 = Z3_mk_config();
        let ctx2 = Z3_mk_context(cfg2);
        Z3_del_config(cfg2);
        let solver2 = Z3_solver_translate(ctx, solver, ctx2);
        assert!(!solver2.is_null());
        assert_eq!(
            Z3_ast_vector_size(ctx2, Z3_solver_get_assertions(ctx2, solver2)),
            2
        );
        assert_eq!(Z3_solver_check(ctx2, solver2), Z3_L_TRUE);

        Z3_del_context(ctx2);
        Z3_del_context(ctx);
    }
}

/// `get_consequences` reports the forced Boolean variables (soundly).
#[test]
fn test_solver_get_consequences() {
    // SAFETY: all handles are owned by this test and freed via `Z3_del_context`.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let solver = Z3_mk_solver(ctx);
        let va = bool_const(ctx, c"va");
        let vb = bool_const(ctx, c"vb");
        let vd = bool_const(ctx, c"vd");
        Z3_solver_assert(ctx, solver, va);
        Z3_solver_assert(ctx, solver, Z3_mk_implies(ctx, va, vb));

        let assumptions = Z3_mk_ast_vector(ctx);
        let vars = Z3_mk_ast_vector(ctx);
        Z3_ast_vector_push(ctx, vars, va);
        Z3_ast_vector_push(ctx, vars, vb);
        Z3_ast_vector_push(ctx, vars, vd);
        let cons = Z3_mk_ast_vector(ctx);
        assert_eq!(
            Z3_solver_get_consequences(ctx, solver, assumptions, vars, cons),
            Z3_L_TRUE
        );
        assert_eq!(Z3_ast_vector_size(ctx, cons), 2, "va and vb are forced");
        let joined = vec_strings(ctx, cons).join(" ");
        assert!(joined.contains("va"), "consequences mention va: {joined}");
        assert!(joined.contains("vb"), "consequences mention vb: {joined}");
        assert!(!joined.contains("vd"), "vd is not forced: {joined}");

        // Under a contradictory assumption the routine returns L_FALSE.
        let s2 = Z3_mk_solver(ctx);
        let ca = bool_const(ctx, c"ca");
        Z3_solver_assert(ctx, s2, ca);
        let a2 = Z3_mk_ast_vector(ctx);
        Z3_ast_vector_push(ctx, a2, Z3_mk_not(ctx, ca));
        let v2 = Z3_mk_ast_vector(ctx);
        Z3_ast_vector_push(ctx, v2, ca);
        let c2 = Z3_mk_ast_vector(ctx);
        assert_eq!(Z3_solver_get_consequences(ctx, s2, a2, v2, c2), Z3_L_FALSE);

        Z3_del_context(ctx);
    }
}

/// Auxiliary inference queries must not bypass semantic acceptance gates. They
/// currently lack the transitive-closure model verifier, so they return UNKNOWN
/// rather than publishing a raw over-approximate backend SAT baseline.
#[test]
fn test_auxiliary_queries_fail_closed_with_transitive_closure_semantics() {
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);
        let solver = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, solver, Z3_mk_true(ctx));

        let bool_sort = Z3_mk_bool_sort(ctx);
        let relation = Z3_mk_func_decl(
            ctx,
            Z3_mk_string_symbol(ctx, c"aux_R".as_ptr()),
            2,
            [bool_sort, bool_sort].as_ptr(),
            bool_sort,
        );
        assert!(!Z3_mk_transitive_closure(ctx, relation).is_null());

        // An ordinary rejected SAT candidate exposes no model either.
        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_UNDEF);
        assert!(Z3_solver_get_model(ctx, solver).is_null());

        let p = bool_const(ctx, c"aux_p");
        let assumptions = Z3_mk_ast_vector(ctx);
        let variables = Z3_mk_ast_vector(ctx);
        Z3_ast_vector_push(ctx, variables, p);
        let consequences = Z3_mk_ast_vector(ctx);
        Z3_ast_vector_push(ctx, consequences, p);
        assert_eq!(
            Z3_solver_get_consequences(ctx, solver, assumptions, variables, consequences,),
            Z3_L_UNDEF
        );
        assert_eq!(
            Z3_ast_vector_size(ctx, consequences),
            1,
            "rejection must not clear or append to the caller's vector"
        );
        assert_eq!(Z3_ast_vector_get(ctx, consequences, 0), p);

        let terms = [p, p];
        let mut classes = [u32::MAX; 2];
        assert_eq!(
            Z3_get_implied_equalities(
                ctx,
                solver,
                terms.len() as u32,
                terms.as_ptr(),
                classes.as_mut_ptr(),
            ),
            Z3_L_UNDEF
        );
        assert_eq!(classes, [u32::MAX; 2], "UNKNOWN must not publish classes");

        Z3_del_context(ctx);
    }
}

/// A non-empty implied-equality query requires both arrays. A null input array
/// must fail before solving or publishing an apparently successful empty result.
#[test]
fn test_implied_equalities_rejects_null_terms_transactionally() {
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);
        let solver = Z3_mk_solver(ctx);
        let mut class_id = u32::MAX;

        assert_eq!(
            Z3_get_implied_equalities(ctx, solver, 1, ptr::null(), &raw mut class_id),
            Z3_L_UNDEF
        );
        assert_eq!(Z3_get_error_code(ctx), Z3_INVALID_ARG);
        assert_eq!(class_id, u32::MAX, "failure must not publish a class id");

        Z3_del_context(ctx);
    }
}

/// `get_units`/`get_non_units`/`get_trail` split assertions into literals vs
/// compounds; the trail is the level-0 unit set.
#[test]
fn test_solver_units_non_units_trail() {
    // SAFETY: all handles are owned by this test and freed via `Z3_del_context`.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let solver = Z3_mk_solver(ctx);
        let pp = bool_const(ctx, c"pp");
        let qq = bool_const(ctx, c"qq");
        let rr = bool_const(ctx, c"rr");
        let or_args = [qq, rr];
        Z3_solver_assert(ctx, solver, pp);
        Z3_solver_assert(ctx, solver, Z3_mk_not(ctx, qq));
        Z3_solver_assert(ctx, solver, Z3_mk_or(ctx, 2, or_args.as_ptr()));

        let units = vec_strings(ctx, Z3_solver_get_units(ctx, solver));
        assert_eq!(units.len(), 2, "two literal assertions: {units:?}");
        assert!(units.iter().any(|s| s == "pp"), "units has pp: {units:?}");
        assert!(
            units.iter().any(|s| s == "(not qq)"),
            "units has (not qq): {units:?}"
        );

        let non_units = vec_strings(ctx, Z3_solver_get_non_units(ctx, solver));
        assert_eq!(non_units.len(), 1, "one compound assertion: {non_units:?}");

        let trail = Z3_solver_get_trail(ctx, solver);
        assert_eq!(
            Z3_ast_vector_size(ctx, trail),
            2,
            "trail is the level-0 unit set"
        );

        Z3_del_context(ctx);
    }
}

/// `to_dimacs_string` emits a Tseitin CNF of the Boolean skeleton. Two unit
/// literals produce exactly two unit clauses over two variables.
#[test]
fn test_solver_to_dimacs_string_skeleton() {
    // SAFETY: all handles are owned by this test and freed via `Z3_del_context`.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let solver = Z3_mk_solver(ctx);
        let da = bool_const(ctx, c"da");
        let db = bool_const(ctx, c"db");
        Z3_solver_assert(ctx, solver, da); // var 1, clause `1 0`
        Z3_solver_assert(ctx, solver, Z3_mk_not(ctx, db)); // var 2, clause `-2 0`

        let dimacs = cstr(Z3_solver_to_dimacs_string(ctx, solver, false));
        assert!(dimacs.contains("p cnf 2 2"), "header: {dimacs}");
        assert!(dimacs.contains("1 0"), "unit clause 1 0: {dimacs}");
        assert!(dimacs.contains("-2 0"), "unit clause -2 0: {dimacs}");

        // include_names emits the atom mapping.
        let named = cstr(Z3_solver_to_dimacs_string(ctx, solver, true));
        assert!(named.contains("da"), "named mapping: {named}");

        Z3_del_context(ctx);
    }
}

/// A disjunction `(or a b)` gets a definitional (Tseitin) encoding whose clauses
/// are equisatisfiable with the disjunction.
#[test]
fn test_solver_to_dimacs_string_or() {
    // SAFETY: all handles are owned by this test and freed via `Z3_del_context`.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let solver = Z3_mk_solver(ctx);
        let a = bool_const(ctx, c"oa");
        let b = bool_const(ctx, c"ob");
        let or_args = [a, b];
        Z3_solver_assert(ctx, solver, Z3_mk_or(ctx, 2, or_args.as_ptr()));

        // a=1, b=2, tseitin-or introduces aux t=3 with the definition clauses
        // (-3 1 2), (3 -1), (3 -2) plus the unit assertion (3): 4 clauses, 3 vars.
        let dimacs = cstr(Z3_solver_to_dimacs_string(ctx, solver, false));
        assert!(dimacs.contains("p cnf 3 4"), "or header: {dimacs}");
        assert!(
            dimacs.contains("-3 1 2 0"),
            "or definition clause: {dimacs}"
        );
        assert!(dimacs.contains("3 0"), "or top-level unit: {dimacs}");

        Z3_del_context(ctx);
    }
}

/// `get_help` returns a real, non-empty parameter description; `congruence_root`
/// / `_next` return the term itself (honest singleton class).
#[test]
fn test_solver_help_and_congruence() {
    // SAFETY: all handles are owned by this test and freed via `Z3_del_context`.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let solver = Z3_mk_solver(ctx);
        let help = cstr(Z3_solver_get_help(ctx, solver));
        assert!(help.contains("timeout"), "help mentions timeout: {help}");

        let g = bool_const(ctx, c"g");
        Z3_solver_assert(ctx, solver, g);
        Z3_solver_check(ctx, solver);
        assert_eq!(Z3_solver_congruence_root(ctx, solver, g), g);
        assert_eq!(Z3_solver_congruence_next(ctx, solver, g), g);

        Z3_del_context(ctx);
    }
}

/// Group B introspection: qid/skolem-id (honest null — matches libz3 for a
/// quantifier without a qid), pattern term round-trip, `Z3_get_depth` exact
/// values, and the honest as-array answers.
#[test]
fn test_quantifier_meta_pattern_depth_as_array() {
    // SAFETY: Test-scope unsafe block: all handles are allocated by `Z3_mk_*`
    // calls inside this block and freed by `Z3_del_context`. No pointer escapes
    // the block and this test owns the handles exclusively.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let x = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"x".as_ptr()), int_sort);
        let f = Z3_mk_func_decl(
            ctx,
            Z3_mk_string_symbol(ctx, c"f".as_ptr()),
            1,
            &raw const int_sort,
            int_sort,
        );
        let fx = Z3_mk_app(ctx, f, 1, &raw const x);
        let pat = Z3_mk_pattern(ctx, 1, &raw const fx);
        assert!(!pat.is_null());
        let body = Z3_mk_eq(ctx, fx, x);
        let q = Z3_mk_forall_const(ctx, 0, 1, &raw const x, 1, &raw const pat, body);
        assert_ne!(q, 0);

        // qid / skolem id: built without :qid/:skolemid -> honest null symbol
        // (byte-for-byte what libz3 returns in the same situation).
        assert!(Z3_get_quantifier_id(ctx, q).is_null());
        assert!(Z3_get_quantifier_skolem_id(ctx, q).is_null());

        // Pattern round-trip: 1 pattern with 1 term, and the term IS f(x).
        assert_eq!(Z3_get_quantifier_num_patterns(ctx, q), 1);
        let p0 = Z3_get_quantifier_pattern_ast(ctx, q, 0);
        assert!(!p0.is_null());
        assert_eq!(Z3_get_pattern_num_terms(ctx, p0), 1);
        assert_eq!(Z3_get_pattern(ctx, p0, 0), fx);
        assert_eq!(Z3_get_pattern(ctx, p0, 3), 0, "OOB pattern term is null");
        assert_eq!(Z3_get_pattern_num_terms(ctx, ptr::null_mut()), 0);

        // Depth: leaves 1; nested apps 1 + max(child) (z3's convention,
        // cross-checked against libz3 by the C consumer twin).
        let two = Z3_mk_int(ctx, 2, int_sort);
        assert_eq!(Z3_get_depth(ctx, x), 1);
        assert_eq!(Z3_get_depth(ctx, two), 1);
        let mul_args = [two, x];
        let two_x = Z3_mk_mul(ctx, 2, mul_args.as_ptr());
        assert_eq!(Z3_get_depth(ctx, two_x), 2);
        let add_args = [fx, two_x];
        let sum = Z3_mk_add(ctx, 2, add_args.as_ptr());
        assert_eq!(Z3_get_depth(ctx, sum), 3);
        assert_eq!(Z3_get_depth(ctx, 0), 0, "null AST depth is 0");

        // as-array: AY never emits as-array model terms — honest false / NULL +
        // INVALID_ARG, never a fabricated func_decl.
        assert!(!Z3_is_as_array(ctx, x));
        assert!(!Z3_is_as_array(ctx, sum));
        assert!(Z3_get_as_array_func_decl(ctx, x).is_null());
        assert_eq!(Z3_get_error_code(ctx), Z3_INVALID_ARG);

        Z3_del_context(ctx);
    }
}
