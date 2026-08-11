# UnsatCore reduction reproducers (2026-08-08)

Minimal discriminating triples for the two core-reduction defects. All three
share the SAME purely-Boolean contradiction (`p` and `(not p)`); only the
declared logic and whether the third assert is `:named` differ.

    file                              expected core   ay --z3-mode actual
    uf_logic_control.smt2             (a1 a2)         (a1 a2)      OK
    fp_logic_unnamed_theory_atom.smt2 (a1 a2)         (a1 a2)      OK
    fp_logic_named_theory_atom.smt2   (a1 a2)         (a1 a2 a3)   BUG

The third file is the regression: a single named theory atom under a declared
FP-family logic pads the core to the full named set, i.e. reduction 0.

Reproduce:
    ay --z3-mode -T:20 <file>            # prints the core
    AY_PHASE_TRACE=1 ay --z3-mode ...    # `uc-minimize` lines never appear
