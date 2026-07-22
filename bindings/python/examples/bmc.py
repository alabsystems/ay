# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0
#
# Bounded Model Checking (BMC) of a tiny reactive system in IDIOMATIC z3py.
#
# System: a bounded counter that increments each step but RESETS to 0 when it
# would exceed CAP. We unroll the transition relation over a fixed horizon and
# ask whether a bad state (counter > CAP) is reachable. The invariant holds, so
# the BMC query is UNSAT (no counterexample). We also run a deliberately broken
# variant (no reset) whose bad state IS reachable -> SAT (a real counterexample
# trace). The same body runs on `import ayz3 as z` or `import z3 as z`.
#
# Run directly on ayz3:
#     python -m examples.bmc

CAP = 5
STEPS = 12


def solve(z, steps=STEPS, cap=CAP, buggy=False):
    """BMC: is a bad state reachable within `steps` steps?

    Returns (result_str, trace) where trace is the list of counter values along
    a counterexample path when sat (bad state reachable), else None.

    With `buggy=False` the system clamps via reset and the invariant
    `counter <= cap` holds -> UNSAT. With `buggy=True` the reset is dropped, so
    the counter overflows the cap -> SAT with a concrete counterexample trace.
    """
    c = [z.Int("c_%d" % t) for t in range(steps + 1)]

    s = z.Solver()

    # Initial state.
    s.add(c[0] == 0)

    # Transition relation.
    for t in range(steps):
        nxt = c[t] + 1
        if buggy:
            # BROKEN: always increment, never reset.
            s.add(c[t + 1] == nxt)
        else:
            # Correct: reset to 0 when the increment would exceed the cap.
            s.add(c[t + 1] == z.If(nxt > cap, 0, nxt))

    # Bad state: counter exceeds the cap at some step. BMC asks if it is
    # reachable; an unsat answer proves the invariant over this horizon.
    s.add(z.Or([c[t] > cap for t in range(steps + 1)]))

    res = s.check()
    if str(res) != "sat":
        return str(res), None
    m = s.model()
    trace = [m[c[t]].as_long() for t in range(steps + 1)]
    return "sat", trace


def reaches_bad(trace, cap=CAP):
    """Independently VALIDATE that a counterexample trace really hits a bad state."""
    if trace is None:
        return False
    return any(v > cap for v in trace)


if __name__ == "__main__":
    import ayz3 as z

    # ayz3 shares one assertion stack per Context, so scope each independent
    # problem in its own Context (z3py gives independent solvers for free). The
    # `solve` body stays z3py-identical.
    with z._ctx_scope(z.Context()):
        res, _ = solve(z, buggy=False)
    print("invariant check (correct system):", res, "(expected unsat)")
    with z._ctx_scope(z.Context()):
        res, trace = solve(z, buggy=True)
    print("invariant check (buggy system):  ", res, "(expected sat)")
    if trace:
        print("  counterexample trace:", trace)
        print("  reaches bad state:", reaches_bad(trace))
