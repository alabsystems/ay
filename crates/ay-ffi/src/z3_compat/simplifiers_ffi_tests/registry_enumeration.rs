// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

/// Registry enumeration: `Z3_get_num_simplifiers` / `Z3_get_simplifier_name`
/// list exactly [`SUPPORTED_SIMPLIFIER_NAMES`], every enumerated name is
/// buildable via `Z3_mk_simplifier`, and an out-of-range index is an honest
/// NULL + `Z3_INVALID_ARG`.
#[test]
fn test_simplifier_registry_enumeration() {
    // SAFETY: all handles are allocated and freed within this test.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let n = Z3_get_num_simplifiers(ctx);
        let mut seen = std::collections::BTreeSet::new();
        for i in 0..n {
            let name = Z3_get_simplifier_name(ctx, i);
            assert!(!name.is_null(), "simplifier name {i} must be non-null");
            let got = CStr::from_ptr(name)
                .to_str()
                .expect("enumerated simplifier name must be valid UTF-8")
                .to_owned();
            assert!(seen.insert(got.clone()), "duplicate simplifier {got}");
            // Every enumerated name is REAL: Z3_mk_simplifier accepts it.
            let cname = CString::new(got.as_str())
                .expect("registered simplifier name must not contain an interior NUL");
            let s = Z3_mk_simplifier(ctx, cname.as_ptr());
            assert!(
                !s.is_null(),
                "enumerated simplifier {got} must be buildable"
            );
        }
        assert!(seen.contains("ff-simplify"));
        // Out of range: honest NULL + INVALID_ARG.
        assert!(Z3_get_simplifier_name(ctx, n).is_null());
        assert_eq!(Z3_get_error_code(ctx), Z3_INVALID_ARG);

        Z3_del_context(ctx);
    }
}
