#!/usr/bin/env python3
# ay-script: z3py-cascade-check
# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0
#
# Stock-z3py cascade verification (the burndown's requested "stock-z3py, not
# ayz3, CI job"). Points UNMODIFIED z3py at AY's libz3-compatible dylib
# (`libay_ffi.dylib`) and exercises the AST-introspection cascade the audit
# reported broken when a declared constant was typed `Z3_VAR_AST` instead of a
# nullary `Z3_APP_AST` (m[x], decl(), children(), to_app, ForAll, sort(),
# simplify, substitute). Exits non-zero if any op fails OR if z3py did not
# actually load AY's dylib.
#
# Usage: python3 scripts/verify_z3py_cascade.py [path/to/libay_ffi.dylib]
# Requires: stock `z3` python package installed (pip install z3-solver).

import os
import sys
import tempfile


def find_dylib(argv):
    if len(argv) > 1:
        return os.path.abspath(argv[1])
    for ext in ("dylib", "so"):
        for prof in ("release", "debug"):
            cand = os.path.join("target", prof, f"libay_ffi.{ext}")
            if os.path.exists(cand):
                return os.path.abspath(cand)
    return None


def main():
    dylib = find_dylib(sys.argv)
    if not dylib or not os.path.exists(dylib):
        print("SKIP: libay_ffi dylib not found (build with `cargo build --release -p ay-ffi`)")
        return 0

    workdir = tempfile.mkdtemp(prefix="ay_z3py_")
    libname = "libz3.dylib" if dylib.endswith(".dylib") else "libz3.so"
    link = os.path.join(workdir, libname)
    os.symlink(dylib, link)
    os.environ["Z3_LIBRARY_PATH"] = workdir

    try:
        import z3
    except ImportError:
        print("SKIP: stock z3py not installed (pip install z3-solver)")
        return 0

    # Confirm z3py actually loaded AY's dylib, not a system z3. AY's z3-compat
    # full-version string is distinguished by the "AY" prefix.
    full = z3.Z3_get_full_version()
    if "AY" not in full:
        print(f"FAIL: z3py did NOT load AY's dylib (Z3_get_full_version={full!r}); "
              f"check Z3_LIBRARY_PATH handling")
        return 1
    print(f"z3py loaded AY dylib: {full}")

    results = {}

    def check(name, fn):
        try:
            fn()
            results[name] = True
        except Exception as e:  # noqa: BLE001 — report any failure verbatim
            results[name] = False
            print(f"  FAIL {name}: {type(e).__name__}: {str(e)[:80]}")

    x = z3.Int("x")
    check("x.sort()", lambda: x.sort())
    check("x.decl()", lambda: x.decl())
    check("x.children()", lambda: x.children())
    check("to_app/decl.name()", lambda: x.decl().name())
    solver = z3.Solver()
    solver.add(x > 0)
    solver.check()
    check("m[x] model lookup", lambda: solver.model()[x])
    check("ForAll", lambda: z3.ForAll([x], x >= 0))
    check("simplify", lambda: z3.simplify(x + 0))
    check("substitute", lambda: z3.substitute(x + 1, (x, z3.IntVal(5))))

    ok = sum(1 for v in results.values() if v)
    total = len(results)
    print(f"CASCADE: {ok}/{total} stock-z3py ops OK against AY dylib")
    return 0 if ok == total else 1


if __name__ == "__main__":
    sys.exit(main())
