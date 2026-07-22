/*
 * Copyright 2026 Andrew Yates
 * Author: Andrew Yates
 * Licensed under the Apache License, Version 2.0
 */

package ay.z3;

/** Unchecked exception for AY/Z3 binding failures (mirrors z3py's Z3Exception). */
public final class AyZ3Exception extends RuntimeException {

    public AyZ3Exception(String message) {
        super(message);
    }

    public AyZ3Exception(String message, Throwable cause) {
        super(message, cause);
    }

    /** Wrap a {@link Throwable} raised by a {@link java.lang.invoke.MethodHandle}
     *  downcall (which is declared to throw {@code Throwable}). */
    static AyZ3Exception wrap(Throwable t) {
        if (t instanceof AyZ3Exception a) return a;
        return new AyZ3Exception("native call failed: " + t, t);
    }
}
