/*
 * Copyright 2026 Andrew Yates
 * Author: Andrew Yates
 * Licensed under the Apache License, Version 2.0
 */

package ay.z3;

import java.lang.foreign.AddressLayout;
import java.lang.foreign.Arena;
import java.lang.foreign.FunctionDescriptor;
import java.lang.foreign.Linker;
import java.lang.foreign.MemorySegment;
import java.lang.foreign.SymbolLookup;
import java.lang.foreign.ValueLayout;
import java.lang.invoke.MethodHandle;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;

/**
 * Low-level Java FFM binding to AY's Z3-shaped C API (libay_ffi).
 *
 * <p>This class loads the cdylib with the {@code java.lang.foreign} API (pure
 * Java, no JNI stubs) and binds a solid CORE set of {@code Z3_*} functions to
 * {@link MethodHandle}s. It is the direct analogue of ayz3's {@code _lib.py}.
 *
 * <p>IMPORTANT ABI NOTE: AY's C ABI is NOT libz3-ABI-compatible. In particular
 * {@code Z3_ast} is a {@code uint64_t} <em>handle</em> (not a {@code void*}), so
 * it maps to {@link ValueLayout#JAVA_LONG} here — <em>not</em> {@code ADDRESS}.
 * Every other opaque handle (context, solver, sort, model, symbol, func_decl,
 * config) is a real pointer and maps to {@code ADDRESS}. {@code c_int}/
 * {@code c_uint} map to {@code JAVA_INT}, {@code bool} to {@code JAVA_BOOLEAN},
 * {@code const char*} to {@code ADDRESS}, {@code double} to {@code JAVA_DOUBLE}.
 *
 * <p>Adding a new function is mechanical: translate its C prototype to a
 * {@link FunctionDescriptor} and add one {@code h(name, desc)} field below.
 */
public final class Native {

    private Native() {}

    // ----- FFM machinery ---------------------------------------------------

    private static final Linker LINKER = Linker.nativeLinker();
    /** Global arena keeping the loaded library (and its symbols) alive. */
    private static final Arena LIB_ARENA = Arena.ofShared();
    private static final SymbolLookup LOOKUP = loadLibrary();

    // ----- layout aliases (see ABI note above) -----------------------------

    /** Z3_ast: a 64-bit handle, NOT a pointer. */
    static final ValueLayout.OfLong AST = ValueLayout.JAVA_LONG;
    /** Any opaque pointer handle (context/sort/solver/model/symbol/...). */
    static final AddressLayout PTR = ValueLayout.ADDRESS;
    /** c_int / c_uint. */
    static final ValueLayout.OfInt I32 = ValueLayout.JAVA_INT;
    /** int64_t / uint64_t (out-params, mk_int64). */
    static final ValueLayout.OfLong I64 = ValueLayout.JAVA_LONG;
    /** C bool. */
    static final ValueLayout.OfBoolean BOOL = ValueLayout.JAVA_BOOLEAN;
    /** C double. */
    static final ValueLayout.OfDouble DBL = ValueLayout.JAVA_DOUBLE;

    // ----- library loading -------------------------------------------------

    private static String platformBasename() {
        String os = System.getProperty("os.name", "").toLowerCase();
        if (os.contains("mac") || os.contains("darwin")) return "libay_ffi.dylib";
        if (os.contains("win")) return "ay_ffi.dll";
        return "libay_ffi.so";
    }

    private static SymbolLookup loadLibrary() {
        List<String> tried = new ArrayList<>();
        String basename = platformBasename();

        // 1. Explicit override via AYZ3_LIB (highest priority).
        String env = System.getenv("AYZ3_LIB");
        if (env != null && !env.isEmpty()) {
            tried.add(env);
            Path p = Path.of(env);
            if (Files.isRegularFile(p)) {
                return SymbolLookup.libraryLookup(p, LIB_ARENA);
            }
        }

        // 2. Walk up from the working directory looking for a Cargo workspace
        //    root (target/{debug,release}/<basename>). This is the in-tree
        //    dev workflow: `cargo build -p ay-ffi` first.
        Path here = Path.of(System.getProperty("user.dir", ".")).toAbsolutePath();
        for (Path dir = here; dir != null; dir = dir.getParent()) {
            for (String profile : new String[] {"debug", "release"}) {
                Path cand = dir.resolve("target").resolve(profile).resolve(basename);
                tried.add(cand.toString());
                if (Files.isRegularFile(cand)) {
                    return SymbolLookup.libraryLookup(cand, LIB_ARENA);
                }
            }
        }

        throw new AyZ3Exception(
            "Could not locate libay_ffi shared library. Build it with "
            + "`cargo build -p ay-ffi`, or set AYZ3_LIB to its full path.\n"
            + "Tried:\n  " + String.join("\n  ", tried));
    }

    /** Bind a {@code Z3_*} function by name and descriptor to a MethodHandle. */
    static MethodHandle h(String name, FunctionDescriptor desc) {
        MemorySegment sym = LOOKUP.find(name).orElseThrow(
            () -> new AyZ3Exception("symbol not found in libay_ffi: " + name));
        return LINKER.downcallHandle(sym, desc);
    }

    // ----- string marshalling ----------------------------------------------

    /** Java String -> NUL-terminated C string in {@code arena} (null -> NULL). */
    static MemorySegment cstr(Arena arena, String s) {
        return s == null ? MemorySegment.NULL : arena.allocateFrom(s);
    }

    /** C {@code const char*} (returned as a bare address) -> Java String. */
    static String jstr(MemorySegment seg) {
        if (seg == null || seg.address() == 0) return null;
        // A returned pointer is a zero-length segment; widen it so the
        // NUL-terminated scan can proceed, then decode as UTF-8.
        return seg.reinterpret(Long.MAX_VALUE).getString(0);
    }

    // =======================================================================
    // Bound CORE functions. Each is one field: h(<name>, descriptor).
    // Grouped to mirror ayz3._lib._SIGS.
    // =======================================================================

    // --- Config & context ---
    public static final MethodHandle mk_config =
        h("Z3_mk_config", FunctionDescriptor.of(PTR));
    public static final MethodHandle del_config =
        h("Z3_del_config", FunctionDescriptor.ofVoid(PTR));
    public static final MethodHandle set_param_value =
        h("Z3_set_param_value", FunctionDescriptor.ofVoid(PTR, PTR, PTR));
    public static final MethodHandle mk_context =
        h("Z3_mk_context", FunctionDescriptor.of(PTR, PTR));
    public static final MethodHandle del_context =
        h("Z3_del_context", FunctionDescriptor.ofVoid(PTR));
    public static final MethodHandle get_error_code =
        h("Z3_get_error_code", FunctionDescriptor.of(I32, PTR));
    public static final MethodHandle get_error_msg =
        h("Z3_get_error_msg", FunctionDescriptor.of(PTR, PTR, I32));
    public static final MethodHandle get_version =
        h("Z3_get_version", FunctionDescriptor.ofVoid(PTR, PTR, PTR, PTR));

    // --- Symbols ---
    public static final MethodHandle mk_string_symbol =
        h("Z3_mk_string_symbol", FunctionDescriptor.of(PTR, PTR, PTR));

    // --- Sorts ---
    public static final MethodHandle mk_bool_sort =
        h("Z3_mk_bool_sort", FunctionDescriptor.of(PTR, PTR));
    public static final MethodHandle mk_int_sort =
        h("Z3_mk_int_sort", FunctionDescriptor.of(PTR, PTR));
    public static final MethodHandle mk_real_sort =
        h("Z3_mk_real_sort", FunctionDescriptor.of(PTR, PTR));
    public static final MethodHandle mk_bv_sort =
        h("Z3_mk_bv_sort", FunctionDescriptor.of(PTR, PTR, I32));
    public static final MethodHandle get_sort =
        h("Z3_get_sort", FunctionDescriptor.of(PTR, PTR, AST));
    public static final MethodHandle get_sort_kind =
        h("Z3_get_sort_kind", FunctionDescriptor.of(I32, PTR, PTR));
    public static final MethodHandle get_bv_sort_size =
        h("Z3_get_bv_sort_size", FunctionDescriptor.of(I32, PTR, PTR));

    // --- Constants & numerals ---
    public static final MethodHandle mk_const =
        h("Z3_mk_const", FunctionDescriptor.of(AST, PTR, PTR, PTR));
    public static final MethodHandle mk_int =
        h("Z3_mk_int", FunctionDescriptor.of(AST, PTR, I32, PTR));
    public static final MethodHandle mk_int64 =
        h("Z3_mk_int64", FunctionDescriptor.of(AST, PTR, I64, PTR));
    public static final MethodHandle mk_unsigned_int64 =
        h("Z3_mk_unsigned_int64", FunctionDescriptor.of(AST, PTR, I64, PTR));
    public static final MethodHandle mk_numeral =
        h("Z3_mk_numeral", FunctionDescriptor.of(AST, PTR, PTR, PTR));
    public static final MethodHandle mk_true =
        h("Z3_mk_true", FunctionDescriptor.of(AST, PTR));
    public static final MethodHandle mk_false =
        h("Z3_mk_false", FunctionDescriptor.of(AST, PTR));

    // --- Boolean ops ---
    public static final MethodHandle mk_eq =
        h("Z3_mk_eq", FunctionDescriptor.of(AST, PTR, AST, AST));
    public static final MethodHandle mk_distinct =
        h("Z3_mk_distinct", FunctionDescriptor.of(AST, PTR, I32, PTR));
    public static final MethodHandle mk_not =
        h("Z3_mk_not", FunctionDescriptor.of(AST, PTR, AST));
    public static final MethodHandle mk_ite =
        h("Z3_mk_ite", FunctionDescriptor.of(AST, PTR, AST, AST, AST));
    public static final MethodHandle mk_implies =
        h("Z3_mk_implies", FunctionDescriptor.of(AST, PTR, AST, AST));
    public static final MethodHandle mk_iff =
        h("Z3_mk_iff", FunctionDescriptor.of(AST, PTR, AST, AST));
    public static final MethodHandle mk_xor =
        h("Z3_mk_xor", FunctionDescriptor.of(AST, PTR, AST, AST));
    public static final MethodHandle mk_and =
        h("Z3_mk_and", FunctionDescriptor.of(AST, PTR, I32, PTR));
    public static final MethodHandle mk_or =
        h("Z3_mk_or", FunctionDescriptor.of(AST, PTR, I32, PTR));

    // --- Arithmetic ---
    public static final MethodHandle mk_add =
        h("Z3_mk_add", FunctionDescriptor.of(AST, PTR, I32, PTR));
    public static final MethodHandle mk_sub =
        h("Z3_mk_sub", FunctionDescriptor.of(AST, PTR, I32, PTR));
    public static final MethodHandle mk_mul =
        h("Z3_mk_mul", FunctionDescriptor.of(AST, PTR, I32, PTR));
    public static final MethodHandle mk_unary_minus =
        h("Z3_mk_unary_minus", FunctionDescriptor.of(AST, PTR, AST));
    public static final MethodHandle mk_div =
        h("Z3_mk_div", FunctionDescriptor.of(AST, PTR, AST, AST));
    public static final MethodHandle mk_mod =
        h("Z3_mk_mod", FunctionDescriptor.of(AST, PTR, AST, AST));
    public static final MethodHandle mk_lt =
        h("Z3_mk_lt", FunctionDescriptor.of(AST, PTR, AST, AST));
    public static final MethodHandle mk_le =
        h("Z3_mk_le", FunctionDescriptor.of(AST, PTR, AST, AST));
    public static final MethodHandle mk_gt =
        h("Z3_mk_gt", FunctionDescriptor.of(AST, PTR, AST, AST));
    public static final MethodHandle mk_ge =
        h("Z3_mk_ge", FunctionDescriptor.of(AST, PTR, AST, AST));

    // --- Bitvector core ---
    public static final MethodHandle mk_bvadd =
        h("Z3_mk_bvadd", FunctionDescriptor.of(AST, PTR, AST, AST));
    public static final MethodHandle mk_bvsub =
        h("Z3_mk_bvsub", FunctionDescriptor.of(AST, PTR, AST, AST));
    public static final MethodHandle mk_bvmul =
        h("Z3_mk_bvmul", FunctionDescriptor.of(AST, PTR, AST, AST));
    public static final MethodHandle mk_bvudiv =
        h("Z3_mk_bvudiv", FunctionDescriptor.of(AST, PTR, AST, AST));
    public static final MethodHandle mk_bvurem =
        h("Z3_mk_bvurem", FunctionDescriptor.of(AST, PTR, AST, AST));
    public static final MethodHandle mk_bvand =
        h("Z3_mk_bvand", FunctionDescriptor.of(AST, PTR, AST, AST));
    public static final MethodHandle mk_bvor =
        h("Z3_mk_bvor", FunctionDescriptor.of(AST, PTR, AST, AST));
    public static final MethodHandle mk_bvxor =
        h("Z3_mk_bvxor", FunctionDescriptor.of(AST, PTR, AST, AST));
    public static final MethodHandle mk_bvshl =
        h("Z3_mk_bvshl", FunctionDescriptor.of(AST, PTR, AST, AST));
    public static final MethodHandle mk_bvlshr =
        h("Z3_mk_bvlshr", FunctionDescriptor.of(AST, PTR, AST, AST));
    public static final MethodHandle mk_bvnot =
        h("Z3_mk_bvnot", FunctionDescriptor.of(AST, PTR, AST));
    public static final MethodHandle mk_bvneg =
        h("Z3_mk_bvneg", FunctionDescriptor.of(AST, PTR, AST));
    public static final MethodHandle mk_bvult =
        h("Z3_mk_bvult", FunctionDescriptor.of(AST, PTR, AST, AST));
    public static final MethodHandle mk_bvule =
        h("Z3_mk_bvule", FunctionDescriptor.of(AST, PTR, AST, AST));
    public static final MethodHandle mk_bvugt =
        h("Z3_mk_bvugt", FunctionDescriptor.of(AST, PTR, AST, AST));
    public static final MethodHandle mk_bvuge =
        h("Z3_mk_bvuge", FunctionDescriptor.of(AST, PTR, AST, AST));
    public static final MethodHandle mk_bvslt =
        h("Z3_mk_bvslt", FunctionDescriptor.of(AST, PTR, AST, AST));
    public static final MethodHandle mk_bvsle =
        h("Z3_mk_bvsle", FunctionDescriptor.of(AST, PTR, AST, AST));
    public static final MethodHandle mk_bvsgt =
        h("Z3_mk_bvsgt", FunctionDescriptor.of(AST, PTR, AST, AST));
    public static final MethodHandle mk_bvsge =
        h("Z3_mk_bvsge", FunctionDescriptor.of(AST, PTR, AST, AST));

    // --- Solver ---
    public static final MethodHandle mk_solver =
        h("Z3_mk_solver", FunctionDescriptor.of(PTR, PTR));
    public static final MethodHandle solver_assert =
        h("Z3_solver_assert", FunctionDescriptor.ofVoid(PTR, PTR, AST));
    public static final MethodHandle solver_push =
        h("Z3_solver_push", FunctionDescriptor.ofVoid(PTR, PTR));
    public static final MethodHandle solver_pop =
        h("Z3_solver_pop", FunctionDescriptor.ofVoid(PTR, PTR, I32));
    public static final MethodHandle solver_reset =
        h("Z3_solver_reset", FunctionDescriptor.ofVoid(PTR, PTR));
    public static final MethodHandle solver_check =
        h("Z3_solver_check", FunctionDescriptor.of(I32, PTR, PTR));
    public static final MethodHandle solver_get_model =
        h("Z3_solver_get_model", FunctionDescriptor.of(PTR, PTR, PTR));
    public static final MethodHandle solver_to_string =
        h("Z3_solver_to_string", FunctionDescriptor.of(PTR, PTR, PTR));

    // --- Model ---
    public static final MethodHandle model_to_string =
        h("Z3_model_to_string", FunctionDescriptor.of(PTR, PTR, PTR));
    public static final MethodHandle model_eval =
        h("Z3_model_eval", FunctionDescriptor.of(BOOL, PTR, PTR, AST, BOOL, PTR));

    // --- Stringify / numeral read / bool value / error ---
    public static final MethodHandle ast_to_string =
        h("Z3_ast_to_string", FunctionDescriptor.of(PTR, PTR, AST));
    public static final MethodHandle get_numeral_string =
        h("Z3_get_numeral_string", FunctionDescriptor.of(PTR, PTR, AST));
    public static final MethodHandle get_numeral_int64 =
        h("Z3_get_numeral_int64", FunctionDescriptor.of(BOOL, PTR, AST, PTR));
    public static final MethodHandle get_bool_value =
        h("Z3_get_bool_value", FunctionDescriptor.of(I32, PTR, AST));

    /**
     * Number of {@code Z3_*} functions bound above — computed reflectively from
     * the public {@code MethodHandle} fields so it can never drift as functions
     * are added.
     */
    public static final int BOUND_FUNCTION_COUNT = countBoundHandles();

    private static int countBoundHandles() {
        int n = 0;
        for (java.lang.reflect.Field f : Native.class.getDeclaredFields()) {
            if (f.getType() == MethodHandle.class
                    && java.lang.reflect.Modifier.isStatic(f.getModifiers())) {
                n++;
            }
        }
        return n;
    }
}
