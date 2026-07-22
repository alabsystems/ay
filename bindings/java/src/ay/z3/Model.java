/*
 * Copyright 2026 Andrew Yates
 * Author: Andrew Yates
 * Licensed under the Apache License, Version 2.0
 */

package ay.z3;

import java.lang.foreign.MemorySegment;
import java.lang.foreign.ValueLayout;

/**
 * A satisfying assignment produced by {@link Solver#getModel()}, mirroring
 * {@code com.microsoft.z3.Model}.
 */
public final class Model {

    private final Context ctx;
    private final MemorySegment handle;

    Model(Context ctx, MemorySegment handle) {
        this.ctx = ctx;
        this.handle = handle;
    }

    /**
     * Evaluate {@code expr} in this model ({@code Z3_model_eval}). When
     * {@code modelCompletion} is true, unconstrained variables are assigned a
     * value; otherwise an unconstrained term may come back unreduced. The result
     * is wrapped in the most specific {@link Expr} subtype for its sort.
     *
     * @throws AyZ3Exception if AY cannot interpret the term in this model.
     */
    public Expr eval(Expr expr, boolean modelCompletion) {
        try {
            MemorySegment out = ctx.arena().allocate(ValueLayout.JAVA_LONG);
            boolean ok = (boolean) Native.model_eval.invoke(
                ctx.ref(), handle, expr.ast, modelCompletion, out);
            long resultAst = out.get(ValueLayout.JAVA_LONG, 0);
            if (!ok || resultAst == 0) {
                throw new AyZ3Exception(
                    "Z3_model_eval failed (expression not interpretable in model)");
            }
            return Expr.wrap(ctx, resultAst);
        } catch (Throwable t) {
            throw AyZ3Exception.wrap(t);
        }
    }

    /** SMT-LIB rendering of the model ({@code Z3_model_to_string}). */
    @Override
    public String toString() {
        try {
            MemorySegment s = (MemorySegment) Native.model_to_string.invoke(ctx.ref(), handle);
            return Native.jstr(s);
        } catch (Throwable t) {
            throw AyZ3Exception.wrap(t);
        }
    }
}
