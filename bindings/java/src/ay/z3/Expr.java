/*
 * Copyright 2026 Andrew Yates
 * Author: Andrew Yates
 * Licensed under the Apache License, Version 2.0
 */

package ay.z3;

import java.lang.foreign.MemorySegment;
import java.lang.foreign.ValueLayout;

/**
 * An SMT expression (term), wrapping a native {@code Z3_ast} handle. Mirrors
 * {@code com.microsoft.z3.Expr}. Concrete subtypes are {@link BoolExpr},
 * {@link ArithExpr} (Int/Real) and {@link BitVecExpr}. Build expressions via
 * the {@code mk*} methods on {@link Context}.
 *
 * <p>NOTE: {@code Z3_ast} is a 64-bit handle, not a pointer, so it is carried
 * here as a plain {@code long}.
 */
public class Expr {

    final Context ctx;
    /** Native {@code Z3_ast} handle (a uint64, NOT a pointer). */
    final long ast;

    Expr(Context ctx, long ast) {
        this.ctx = ctx;
        this.ast = ast;
    }

    /** The context that owns this expression. */
    public Context getContext() {
        return ctx;
    }

    /** The raw native {@code Z3_ast} handle. */
    public long ast() {
        return ast;
    }

    /** SMT-LIB rendering via {@code Z3_ast_to_string}. */
    @Override
    public String toString() {
        try {
            MemorySegment s = (MemorySegment) Native.ast_to_string.invoke(ctx.ref(), ast);
            return Native.jstr(s);
        } catch (Throwable t) {
            throw AyZ3Exception.wrap(t);
        }
    }

    /**
     * Read this term as a 64-bit integer via {@code Z3_get_numeral_int64}.
     * Valid only when the term is a concrete integer/bitvector numeral (e.g. a
     * value returned by {@link Model#eval}); throws otherwise.
     */
    public long asLong() {
        try {
            MemorySegment out = ctx.arena().allocate(ValueLayout.JAVA_LONG);
            boolean ok = (boolean) Native.get_numeral_int64.invoke(ctx.ref(), ast, out);
            if (!ok) {
                throw new AyZ3Exception("not an integer numeral: " + this);
            }
            return out.get(ValueLayout.JAVA_LONG, 0);
        } catch (Throwable t) {
            throw AyZ3Exception.wrap(t);
        }
    }

    /** Read this term's numeral rendering via {@code Z3_get_numeral_string}. */
    public String numeralString() {
        try {
            MemorySegment s = (MemorySegment) Native.get_numeral_string.invoke(ctx.ref(), ast);
            return Native.jstr(s);
        } catch (Throwable t) {
            throw AyZ3Exception.wrap(t);
        }
    }

    /**
     * Wrap a raw {@code Z3_ast} handle in the most specific {@code Expr}
     * subtype, dispatching on its sort kind ({@code Z3_get_sort_kind}).
     */
    static Expr wrap(Context ctx, long ast) {
        try {
            MemorySegment sort = (MemorySegment) Native.get_sort.invoke(ctx.ref(), ast);
            int kind = (int) Native.get_sort_kind.invoke(ctx.ref(), sort);
            // Z3_sort_kind: BOOL=1, INT=2, REAL=3, BV=4.
            return switch (kind) {
                case 1 -> new BoolExpr(ctx, ast);
                case 2, 3 -> new ArithExpr(ctx, ast);
                case 4 -> new BitVecExpr(ctx, ast);
                default -> new Expr(ctx, ast);
            };
        } catch (Throwable t) {
            throw AyZ3Exception.wrap(t);
        }
    }
}
