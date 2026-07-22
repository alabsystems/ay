/*
 * Copyright 2026 Andrew Yates
 * Author: Andrew Yates
 * Licensed under the Apache License, Version 2.0
 */

package ay.z3;

/**
 * An arithmetic (Int or Real) expression. Mirrors
 * {@code com.microsoft.z3.ArithExpr}; AY does not distinguish IntExpr/RealExpr
 * subclasses at the binding level, so both live here.
 */
public final class ArithExpr extends Expr {
    ArithExpr(Context ctx, long ast) {
        super(ctx, ast);
    }
}
