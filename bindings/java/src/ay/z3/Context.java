/*
 * Copyright 2026 Andrew Yates
 * Author: Andrew Yates
 * Licensed under the Apache License, Version 2.0
 */

package ay.z3;

import java.lang.foreign.Arena;
import java.lang.foreign.MemorySegment;
import java.lang.foreign.ValueLayout;
import java.lang.invoke.MethodHandle;

/**
 * An SMT context — the factory for sorts, expressions and solvers, mirroring
 * {@code com.microsoft.z3.Context}. Owns the native {@code Z3_config} and
 * {@code Z3_context} handles plus an {@link Arena} for all native scratch
 * allocations (C strings, argument arrays, out-params). Everything allocated
 * lives until {@link #close()}, which tears down the context.
 *
 * <p>Use with try-with-resources:
 * <pre>{@code
 * try (Context ctx = new Context()) {
 *     ArithExpr x = ctx.mkIntConst("x");
 *     Solver s = ctx.mkSolver();
 *     s.add(ctx.mkGt(x, ctx.mkInt(3)));
 *     ...
 * }
 * }</pre>
 */
public final class Context implements AutoCloseable {

    private final Arena arena = Arena.ofShared();
    private final MemorySegment cfg;
    private final MemorySegment ctx;
    private boolean closed = false;

    public Context() {
        try {
            this.cfg = (MemorySegment) Native.mk_config.invoke();
            this.ctx = (MemorySegment) Native.mk_context.invoke(cfg);
        } catch (Throwable t) {
            throw AyZ3Exception.wrap(t);
        }
    }

    /** The native {@code Z3_context} handle. */
    MemorySegment ref() {
        return ctx;
    }

    /** The context-owned arena for native scratch allocations. */
    Arena arena() {
        return arena;
    }

    // ----- internal call helpers (each wraps the Throwable once) -----------

    private MemorySegment cstr(String s) {
        return Native.cstr(arena, s);
    }

    private long unop(MethodHandle mh, long a) {
        try {
            return (long) mh.invoke(ctx, a);
        } catch (Throwable t) {
            throw AyZ3Exception.wrap(t);
        }
    }

    private long binop(MethodHandle mh, long a, long b) {
        try {
            return (long) mh.invoke(ctx, a, b);
        } catch (Throwable t) {
            throw AyZ3Exception.wrap(t);
        }
    }

    private long ternop(MethodHandle mh, long a, long b, long c) {
        try {
            return (long) mh.invoke(ctx, a, b, c);
        } catch (Throwable t) {
            throw AyZ3Exception.wrap(t);
        }
    }

    /** n-ary op: marshals the args into a native {@code Z3_ast[]} then calls. */
    private long naryop(MethodHandle mh, Expr[] args) {
        try {
            int n = args.length;
            MemorySegment arr = arena.allocate(8L * Math.max(1, n), 8);
            for (int i = 0; i < n; i++) {
                arr.setAtIndex(ValueLayout.JAVA_LONG, i, args[i].ast);
            }
            return (long) mh.invoke(ctx, n, arr);
        } catch (Throwable t) {
            throw AyZ3Exception.wrap(t);
        }
    }

    private MemorySegment sortCall(MethodHandle mh) {
        try {
            return (MemorySegment) mh.invoke(ctx);
        } catch (Throwable t) {
            throw AyZ3Exception.wrap(t);
        }
    }

    // ----- Sorts -----------------------------------------------------------

    public Sort mkBoolSort() {
        return new Sort(this, sortCall(Native.mk_bool_sort));
    }

    public Sort mkIntSort() {
        return new Sort(this, sortCall(Native.mk_int_sort));
    }

    public Sort mkRealSort() {
        return new Sort(this, sortCall(Native.mk_real_sort));
    }

    public Sort mkBVSort(int size) {
        try {
            return new Sort(this, (MemorySegment) Native.mk_bv_sort.invoke(ctx, size));
        } catch (Throwable t) {
            throw AyZ3Exception.wrap(t);
        }
    }

    // ----- Constants -------------------------------------------------------

    private MemorySegment symbol(String name) {
        try {
            return (MemorySegment) Native.mk_string_symbol.invoke(ctx, cstr(name));
        } catch (Throwable t) {
            throw AyZ3Exception.wrap(t);
        }
    }

    private long constRaw(String name, MemorySegment sort) {
        try {
            return (long) Native.mk_const.invoke(ctx, symbol(name), sort);
        } catch (Throwable t) {
            throw AyZ3Exception.wrap(t);
        }
    }

    /** A named constant of an arbitrary sort. */
    public Expr mkConst(String name, Sort sort) {
        return Expr.wrap(this, constRaw(name, sort.seg));
    }

    public BoolExpr mkBoolConst(String name) {
        return new BoolExpr(this, constRaw(name, mkBoolSort().seg));
    }

    public ArithExpr mkIntConst(String name) {
        return new ArithExpr(this, constRaw(name, mkIntSort().seg));
    }

    public ArithExpr mkRealConst(String name) {
        return new ArithExpr(this, constRaw(name, mkRealSort().seg));
    }

    public BitVecExpr mkBVConst(String name, int size) {
        return new BitVecExpr(this, constRaw(name, mkBVSort(size).seg));
    }

    // ----- Numerals & literals ---------------------------------------------

    public BoolExpr mkTrue() {
        try {
            return new BoolExpr(this, (long) Native.mk_true.invoke(ctx));
        } catch (Throwable t) {
            throw AyZ3Exception.wrap(t);
        }
    }

    public BoolExpr mkFalse() {
        try {
            return new BoolExpr(this, (long) Native.mk_false.invoke(ctx));
        } catch (Throwable t) {
            throw AyZ3Exception.wrap(t);
        }
    }

    public BoolExpr mkBool(boolean b) {
        return b ? mkTrue() : mkFalse();
    }

    /** An Int numeral. */
    public ArithExpr mkInt(long value) {
        try {
            return new ArithExpr(this,
                (long) Native.mk_int64.invoke(ctx, value, mkIntSort().seg));
        } catch (Throwable t) {
            throw AyZ3Exception.wrap(t);
        }
    }

    /** A Real numeral from an SMT-LIB decimal/rational string, e.g. "3/2". */
    public ArithExpr mkReal(String rep) {
        try {
            return new ArithExpr(this,
                (long) Native.mk_numeral.invoke(ctx, cstr(rep), mkRealSort().seg));
        } catch (Throwable t) {
            throw AyZ3Exception.wrap(t);
        }
    }

    /** A numeral of an arbitrary sort from an SMT-LIB string. */
    public Expr mkNumeral(String rep, Sort sort) {
        try {
            return Expr.wrap(this,
                (long) Native.mk_numeral.invoke(ctx, cstr(rep), sort.seg));
        } catch (Throwable t) {
            throw AyZ3Exception.wrap(t);
        }
    }

    /** A bitvector numeral of the given width. */
    public BitVecExpr mkBV(long value, int size) {
        try {
            return new BitVecExpr(this,
                (long) Native.mk_int64.invoke(ctx, value, mkBVSort(size).seg));
        } catch (Throwable t) {
            throw AyZ3Exception.wrap(t);
        }
    }

    // ----- Boolean ops -----------------------------------------------------

    public BoolExpr mkEq(Expr l, Expr r) {
        return new BoolExpr(this, binop(Native.mk_eq, l.ast, r.ast));
    }

    public BoolExpr mkNot(Expr a) {
        return new BoolExpr(this, unop(Native.mk_not, a.ast));
    }

    public BoolExpr mkImplies(Expr a, Expr b) {
        return new BoolExpr(this, binop(Native.mk_implies, a.ast, b.ast));
    }

    public BoolExpr mkIff(Expr a, Expr b) {
        return new BoolExpr(this, binop(Native.mk_iff, a.ast, b.ast));
    }

    public BoolExpr mkXor(Expr a, Expr b) {
        return new BoolExpr(this, binop(Native.mk_xor, a.ast, b.ast));
    }

    public BoolExpr mkAnd(Expr... args) {
        return new BoolExpr(this, naryop(Native.mk_and, args));
    }

    public BoolExpr mkOr(Expr... args) {
        return new BoolExpr(this, naryop(Native.mk_or, args));
    }

    public BoolExpr mkDistinct(Expr... args) {
        return new BoolExpr(this, naryop(Native.mk_distinct, args));
    }

    public Expr mkITE(Expr cond, Expr t, Expr e) {
        return Expr.wrap(this, ternop(Native.mk_ite, cond.ast, t.ast, e.ast));
    }

    // ----- Arithmetic ------------------------------------------------------

    public ArithExpr mkAdd(Expr... args) {
        return new ArithExpr(this, naryop(Native.mk_add, args));
    }

    public ArithExpr mkSub(Expr... args) {
        return new ArithExpr(this, naryop(Native.mk_sub, args));
    }

    public ArithExpr mkMul(Expr... args) {
        return new ArithExpr(this, naryop(Native.mk_mul, args));
    }

    public ArithExpr mkUnaryMinus(Expr a) {
        return new ArithExpr(this, unop(Native.mk_unary_minus, a.ast));
    }

    public ArithExpr mkDiv(Expr a, Expr b) {
        return new ArithExpr(this, binop(Native.mk_div, a.ast, b.ast));
    }

    public ArithExpr mkMod(Expr a, Expr b) {
        return new ArithExpr(this, binop(Native.mk_mod, a.ast, b.ast));
    }

    public BoolExpr mkLt(Expr a, Expr b) {
        return new BoolExpr(this, binop(Native.mk_lt, a.ast, b.ast));
    }

    public BoolExpr mkLe(Expr a, Expr b) {
        return new BoolExpr(this, binop(Native.mk_le, a.ast, b.ast));
    }

    public BoolExpr mkGt(Expr a, Expr b) {
        return new BoolExpr(this, binop(Native.mk_gt, a.ast, b.ast));
    }

    public BoolExpr mkGe(Expr a, Expr b) {
        return new BoolExpr(this, binop(Native.mk_ge, a.ast, b.ast));
    }

    // ----- Bitvector core --------------------------------------------------

    public BitVecExpr mkBVAdd(Expr a, Expr b) {
        return new BitVecExpr(this, binop(Native.mk_bvadd, a.ast, b.ast));
    }

    public BitVecExpr mkBVSub(Expr a, Expr b) {
        return new BitVecExpr(this, binop(Native.mk_bvsub, a.ast, b.ast));
    }

    public BitVecExpr mkBVMul(Expr a, Expr b) {
        return new BitVecExpr(this, binop(Native.mk_bvmul, a.ast, b.ast));
    }

    public BitVecExpr mkBVUDiv(Expr a, Expr b) {
        return new BitVecExpr(this, binop(Native.mk_bvudiv, a.ast, b.ast));
    }

    public BitVecExpr mkBVURem(Expr a, Expr b) {
        return new BitVecExpr(this, binop(Native.mk_bvurem, a.ast, b.ast));
    }

    public BitVecExpr mkBVAnd(Expr a, Expr b) {
        return new BitVecExpr(this, binop(Native.mk_bvand, a.ast, b.ast));
    }

    public BitVecExpr mkBVOr(Expr a, Expr b) {
        return new BitVecExpr(this, binop(Native.mk_bvor, a.ast, b.ast));
    }

    public BitVecExpr mkBVXor(Expr a, Expr b) {
        return new BitVecExpr(this, binop(Native.mk_bvxor, a.ast, b.ast));
    }

    public BitVecExpr mkBVShl(Expr a, Expr b) {
        return new BitVecExpr(this, binop(Native.mk_bvshl, a.ast, b.ast));
    }

    public BitVecExpr mkBVLshr(Expr a, Expr b) {
        return new BitVecExpr(this, binop(Native.mk_bvlshr, a.ast, b.ast));
    }

    public BitVecExpr mkBVNot(Expr a) {
        return new BitVecExpr(this, unop(Native.mk_bvnot, a.ast));
    }

    public BitVecExpr mkBVNeg(Expr a) {
        return new BitVecExpr(this, unop(Native.mk_bvneg, a.ast));
    }

    public BoolExpr mkBVULT(Expr a, Expr b) {
        return new BoolExpr(this, binop(Native.mk_bvult, a.ast, b.ast));
    }

    public BoolExpr mkBVULE(Expr a, Expr b) {
        return new BoolExpr(this, binop(Native.mk_bvule, a.ast, b.ast));
    }

    public BoolExpr mkBVUGT(Expr a, Expr b) {
        return new BoolExpr(this, binop(Native.mk_bvugt, a.ast, b.ast));
    }

    public BoolExpr mkBVUGE(Expr a, Expr b) {
        return new BoolExpr(this, binop(Native.mk_bvuge, a.ast, b.ast));
    }

    public BoolExpr mkBVSLT(Expr a, Expr b) {
        return new BoolExpr(this, binop(Native.mk_bvslt, a.ast, b.ast));
    }

    public BoolExpr mkBVSLE(Expr a, Expr b) {
        return new BoolExpr(this, binop(Native.mk_bvsle, a.ast, b.ast));
    }

    public BoolExpr mkBVSGT(Expr a, Expr b) {
        return new BoolExpr(this, binop(Native.mk_bvsgt, a.ast, b.ast));
    }

    public BoolExpr mkBVSGE(Expr a, Expr b) {
        return new BoolExpr(this, binop(Native.mk_bvsge, a.ast, b.ast));
    }

    // ----- Solver factory --------------------------------------------------

    public Solver mkSolver() {
        return new Solver(this);
    }

    // ----- Introspection ---------------------------------------------------

    /** The last error code recorded on this context ({@code Z3_get_error_code}). */
    public int getErrorCode() {
        try {
            return (int) Native.get_error_code.invoke(ctx);
        } catch (Throwable t) {
            throw AyZ3Exception.wrap(t);
        }
    }

    // ----- Lifecycle -------------------------------------------------------

    @Override
    public void close() {
        if (closed) return;
        closed = true;
        try {
            Native.del_context.invoke(ctx);
            Native.del_config.invoke(cfg);
        } catch (Throwable t) {
            throw AyZ3Exception.wrap(t);
        } finally {
            arena.close();
        }
    }
}
