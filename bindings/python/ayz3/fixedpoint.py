# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0
#
# z3py-compatible `Fixedpoint` (CHC / Horn-clause) surface for ayz3, backed by
# AY's Spacer-class CHC engine (ay-chc) through the dylib's Z3_fixedpoint_* C
# entry points.
#
# ============================================================================
# WHAT IS BACKED (verified against the exported C surface via nm)
# ============================================================================
#
# The dylib exports exactly 8 Z3_fixedpoint_* functions:
#
#   Z3_mk_fixedpoint, Z3_fixedpoint_inc_ref, Z3_fixedpoint_dec_ref,
#   Z3_fixedpoint_register_relation, Z3_fixedpoint_add_rule,
#   Z3_fixedpoint_query, Z3_fixedpoint_get_answer, Z3_fixedpoint_to_string
#
# That is a complete declare-relations / add-Horn-rules / query-reachability
# CHC surface, so the core z3py Fixedpoint workflow is fully functional:
#
#   fp = Fixedpoint()
#   P  = Function('P', IntSort(), BoolSort())
#   x  = Int('x')
#   fp.register_relation(P)
#   fp.declare_var(x)
#   fp.rule(P(0))                    # fact
#   fp.rule(P(x + 1), P(x))         # forall x. P(x) => P(x+1)
#   fp.query(P(5))                  # -> sat (reachable), matching z3py
#
# Every verdict is a real ay-chc portfolio solve on the Rust side (see
# crates/ay-ffi/src/z3_compat/fixedpoint.rs); a SAFE answer additionally passes
# the engine's invariant-discharge soundness gate. A rule/query shape the
# C-side translator cannot handle exactly yields `unknown` — never a wrong
# verdict.
#
# Query polarity matches z3py exactly: `sat` = the query is reachable /
# derivable (system UNSAFE), `unsat` = unreachable (SAFE).
#
# ============================================================================
# HONEST DIVERGENCES / NOT BACKED (the C function is absent from the dylib)
# ============================================================================
#
#   - get_answer(): Z3 returns a derivation/answer AST; AY's C surface returns
#     the verdict text ("sat"/"unsat"/"unknown"). This binding returns that
#     Python str (documented divergence — AY does not synthesize an answer
#     relation, and fabricating one would be a fake).
#   - set()/help()/param_descrs(): Z3_fixedpoint_set_params / _get_help /
#     _get_param_descrs are not exported -> NotImplementedError. Silently
#     ignoring engine parameters would be a stopgap, so we refuse loudly.
#   - add()/assert_exprs() (background assertions): Z3_fixedpoint_assert is
#     not exported -> NotImplementedError. (Rules go through rule()/add_rule(),
#     which IS backed.)
#   - update_rule, query_from_lvl, get_num_levels, get_cover_delta, add_cover,
#     register_variable, set_predicate_representation, parse_string,
#     parse_file, get_rules, get_assertions, get_ground_sat_answer,
#     get_rules_along_trace, get_rule_names_along_trace, to_string(queries):
#     the corresponding Z3_fixedpoint_* C functions are not exported ->
#     NotImplementedError naming the missing entry point.

import ctypes

from . import _lib
from ._lib import lib


class Fixedpoint:
    """z3py-compatible Fixedpoint (CHC/Datalog) engine over ay-chc.

    Supports `register_relation`, `declare_var`, `rule`/`add_rule`/`fact`,
    `query`, `get_answer` (verdict text) and `__repr__`/`sexpr`. See the module
    docstring for the honest list of unbacked z3py methods.
    """

    def __init__(self, fixedpoint=None, ctx=None):
        from . import _current_ctx, AyZ3Exception
        if fixedpoint is not None:
            raise NotImplementedError(
                "Fixedpoint(fixedpoint=...) wrapping a raw handle is not "
                "supported; construct with Fixedpoint(ctx=ctx)")
        self.ctx = ctx if ctx is not None else _current_ctx()
        self.handle = lib.Z3_mk_fixedpoint(self.ctx.ref)
        if not self.handle:
            self.ctx.check_error("Fixedpoint creation")
            raise AyZ3Exception("AY returned a null fixedpoint handle")
        self.vars = []          # declare_var order, like z3py Fixedpoint.vars
        self._relations = []    # FuncDeclRefs, for introspection/repr parity

    # ---- registration -----------------------------------------------------

    def register_relation(self, *relations):
        """Register one or more Bool-range FuncDeclRefs as CHC relations."""
        from . import FuncDeclRef, AyZ3Exception
        for f in relations:
            if not isinstance(f, FuncDeclRef):
                raise AyZ3Exception(
                    f"register_relation expects FuncDeclRef, got {f!r}")
            if f.range_sort.kind != "Bool":
                raise AyZ3Exception(
                    f"relation {f.name()} must have Bool range, "
                    f"got {f.range_sort}")
            lib.Z3_fixedpoint_register_relation(
                self.ctx.ref, self.handle, f.handle)
            self.ctx.check_error("Fixedpoint.register_relation")
            self._relations.append(f)

    def declare_var(self, *vars):
        """Declare universally-quantified rule variables (z3py declare_var).

        Rules and queries added afterwards are automatically abstracted over
        these variables (rules universally; queries keep z3py's existential
        reachability semantics — see `query`).
        """
        from . import AstRef, AyZ3Exception
        for v in vars:
            if not isinstance(v, AstRef):
                raise AyZ3Exception(f"declare_var expects an expression, got {v!r}")
            self.vars.append(v)

    def abstract(self, fml, is_forall=True):
        """Close `fml` over the declared variables (z3py Fixedpoint.abstract)."""
        from . import ForAll, Exists
        if not self.vars:
            return fml
        return ForAll(self.vars, fml) if is_forall else Exists(self.vars, fml)

    # ---- rules ------------------------------------------------------------

    def add_rule(self, head, body=None, name=None):
        """Add the Horn rule `body => head` (or the fact/formula `head`).

        `body` may be a single Bool expression, a list/tuple of them (conjoined),
        or None. Declared variables (declare_var) are universally closed over,
        exactly like z3py. `head` may also be an already-quantified full rule
        `ForAll(vs, Implies(body, head))` when no variables are declared.
        """
        from . import And, Implies, _coerce, _bool_sort
        fml = _coerce(head, _bool_sort(self.ctx), self.ctx)
        if body is not None:
            if isinstance(body, (list, tuple)):
                if len(body) == 0:
                    pass  # empty body: bare fact
                elif len(body) == 1:
                    fml = Implies(body[0], fml)
                else:
                    fml = Implies(And(*body), fml)
            else:
                fml = Implies(body, fml)
        fml = self.abstract(fml, is_forall=True)
        sym = None
        if name:
            sym = lib.Z3_mk_string_symbol(self.ctx.ref, str(name).encode())
        lib.Z3_fixedpoint_add_rule(self.ctx.ref, self.handle, fml.ast, sym)
        self.ctx.check_error("Fixedpoint.add_rule")

    def rule(self, head, body=None, name=None):
        """Alias of add_rule (z3py)."""
        self.add_rule(head, body, name)

    def fact(self, head, name=None):
        """Add `head` as an unconditional fact (z3py Fixedpoint.fact)."""
        self.add_rule(head, None, name)

    # ---- query ------------------------------------------------------------

    def query(self, *query):
        """Query reachability of the goal; returns sat/unsat/unknown.

        `sat`  — the goal is derivable from the rules (system UNSAFE),
        `unsat` — the goal is unreachable (SAFE; the engine's proof-checked
                  invariant discharge gate has confirmed the invariant),
        `unknown` — inconclusive, or a rule/goal shape the CHC translator
                  cannot express exactly (never a guessed verdict).

        Multiple arguments are conjoined, like z3py. Declared variables in the
        goal keep z3py's existential reachability reading: the goal
        `And(P(x), x > 200)` asks whether SOME x with x > 200 makes P(x)
        derivable. (Internally the goal is closed universally and lowered to
        the safety clause `goal => false`, which is the same existential
        reachability question — verdicts cross-check against real z3py.)
        """
        from . import (And, _coerce, _bool_sort, sat, unsat, unknown,
                       AyZ3Exception)
        if len(query) == 0:
            raise AyZ3Exception("query expects at least one goal expression")
        goals = [_coerce(q, _bool_sort(self.ctx), self.ctx) for q in query]
        goal = goals[0] if len(goals) == 1 else And(*goals)
        # Close over declared vars. The C side strips the quantifier and treats
        # the body as the safety-clause body (implicitly quantified clause
        # variables), which is exactly the existential reachability query.
        goal = self.abstract(goal, is_forall=True)
        r = lib.Z3_fixedpoint_query(self.ctx.ref, self.handle, goal.ast)
        self.ctx.check_error("Fixedpoint.query")
        if r == _lib.Z3_L_TRUE:
            return sat
        if r == _lib.Z3_L_FALSE:
            return unsat
        return unknown

    def get_answer(self):
        """The last query's verdict as a str ("sat"/"unsat"/"unknown").

        DOCUMENTED DIVERGENCE from z3py: Z3 returns a derivation/answer AST
        here. AY's C surface (Z3_fixedpoint_get_answer) reports the verdict
        text because ay-chc does not synthesize a Datalog answer relation;
        fabricating an AST would be a fake, so the honest str is returned.
        """
        s = lib.Z3_fixedpoint_get_answer(self.ctx.ref, self.handle)
        return s.decode() if s else "unknown"

    # ---- printing ---------------------------------------------------------

    def sexpr(self):
        """The rule set in SMT-LIB-ish (declare-rel ...) (rule ...) form."""
        s = lib.Z3_fixedpoint_to_string(self.ctx.ref, self.handle)
        return s.decode() if s else ""

    def to_string(self, queries=None):
        """z3py Fixedpoint.to_string. Extra query serialization is unbacked."""
        if queries:
            raise NotImplementedError(
                "Fixedpoint.to_string(queries): Z3_fixedpoint_to_string with "
                "a query array is not exported by libay_ffi")
        return self.sexpr()

    def __repr__(self):
        return self.sexpr()

    def __del__(self):
        # Handle is arena-owned by the context (dec_ref is bookkeeping-only).
        pass

    # ---- honest NotImplementedError surface (C fn absent from the dylib) ---

    def _absent(self, method, cfn):
        raise NotImplementedError(
            f"Fixedpoint.{method} is not supported: {cfn} is not exported by "
            f"libay_ffi (the dylib exports only mk/inc_ref/dec_ref/"
            f"register_relation/add_rule/query/get_answer/to_string)")

    def set(self, *args, **keys):
        """Unbacked: Z3_fixedpoint_set_params is not exported.

        Silently ignoring engine parameters would be a stopgap, so this raises
        instead. AY always runs its best adaptive CHC portfolio by default.
        """
        self._absent("set", "Z3_fixedpoint_set_params")

    def help(self):
        self._absent("help", "Z3_fixedpoint_get_help")

    def param_descrs(self):
        self._absent("param_descrs", "Z3_fixedpoint_get_param_descrs")

    def assert_exprs(self, *args):
        self._absent("assert_exprs", "Z3_fixedpoint_assert")

    def add(self, *args):
        self._absent("add", "Z3_fixedpoint_assert")

    def append(self, *args):
        self._absent("append", "Z3_fixedpoint_assert")

    def insert(self, *args):
        self._absent("insert", "Z3_fixedpoint_assert")

    def update_rule(self, head, body, name):
        self._absent("update_rule", "Z3_fixedpoint_update_rule")

    def query_from_lvl(self, lvl, *query):
        self._absent("query_from_lvl", "Z3_fixedpoint_query_from_lvl")

    def get_num_levels(self, predicate):
        self._absent("get_num_levels", "Z3_fixedpoint_get_num_levels")

    def get_cover_delta(self, level, predicate):
        self._absent("get_cover_delta", "Z3_fixedpoint_get_cover_delta")

    def add_cover(self, level, predicate, property):
        self._absent("add_cover", "Z3_fixedpoint_add_cover")

    def register_variable(self, *vars):
        self._absent("register_variable", "Z3_fixedpoint_register_variable")

    def set_predicate_representation(self, f, *representations):
        self._absent("set_predicate_representation",
                     "Z3_fixedpoint_set_predicate_representation")

    def parse_string(self, s):
        self._absent("parse_string", "Z3_fixedpoint_from_string")

    def parse_file(self, f):
        self._absent("parse_file", "Z3_fixedpoint_from_file")

    def get_rules(self):
        self._absent("get_rules", "Z3_fixedpoint_get_rules")

    def get_assertions(self):
        self._absent("get_assertions", "Z3_fixedpoint_get_assertions")

    def get_ground_sat_answer(self):
        self._absent("get_ground_sat_answer",
                     "Z3_fixedpoint_get_ground_sat_answer")

    def get_rules_along_trace(self):
        self._absent("get_rules_along_trace",
                     "Z3_fixedpoint_get_rules_along_trace")

    def get_rule_names_along_trace(self):
        self._absent("get_rule_names_along_trace",
                     "Z3_fixedpoint_get_rule_names_along_trace")

    def statistics(self):
        self._absent("statistics", "Z3_fixedpoint_get_statistics")

    def reason_unknown(self):
        self._absent("reason_unknown", "Z3_fixedpoint_get_reason_unknown")
