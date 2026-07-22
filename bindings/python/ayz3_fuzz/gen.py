# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0
#
# Random well-typed SMT formula generator for the differential fuzzer.
#
# DESIGN: a generated formula is a module-AGNOSTIC AST -- a small tree of
# `Node(op, sort, children, payload)` records built from a seeded PRNG. A single
# `build(node, m)` function then realizes that tree through ANY z3py-shaped
# module `m` (either `ayz3` or `z3`). Because both sides walk the *same* tree,
# the two formulas are guaranteed structurally identical -- which both stresses
# binding API fidelity and gives the differential cross-check a fair comparison.
#
# Generation is deterministic: `generate(fragment, seed)` always yields the same
# tree, so a failing (fragment, seed) reproduces exactly.
#
# Fragments are deliberately bounded in depth/size so checks stay fast and the
# distribution is dominated by decidable, in-fragment formulas (where a
# sat-vs-unsat split would be a real wrong answer rather than expected
# incompleteness).

import os
import random
from dataclasses import dataclass, field
from typing import Any, List


# Sorts (module-agnostic tags). BV carries its width.
SORT_INT = "Int"
SORT_REAL = "Real"
SORT_BOOL = "Bool"


@dataclass
class BV:
    width: int

    def __eq__(self, other):
        return isinstance(other, BV) and other.width == self.width

    def __hash__(self):
        return hash(("BV", self.width))


@dataclass
class ArrSort:
    dom: Any
    rng: Any


# --- sequences (module-agnostic sort tag) ----------------------------------
# A `(Seq elem)` sort over a primitive element sort tag (SORT_INT / SORT_BOOL).
# NOTE (rendering): AY's *sequence theory* (the `(Seq Int)` / `(Seq Bool)` axioms
# where the recent wrong-verdict bugs lived) is reachable through ayz3's SMT-LIB
# PARSER but NOT through ayz3's in-memory term builders — `Concat`/`Length`/... on
# ayz3 only accept the String sort (AY models String as its concrete char
# sequence). So the `sequences` fragment renders each formula to canonical
# SMT-LIB (via z3py, the reference renderer) and checks the SAME text through
# `from_string` on BOTH modules (see differential.SMT2_FRAGMENTS). That keeps the
# comparison faithful (identical text -> identical formula) while still exercising
# the exact `(Seq Int)`/`(Seq Bool)` decision procedure that had the bugs.
@dataclass
class SeqS:
    elem: Any  # element sort tag: SORT_INT or SORT_BOOL

    def __eq__(self, other):
        return isinstance(other, SeqS) and other.elem == self.elem

    def __hash__(self):
        return hash(("Seq", self.elem))


# --- floating point (module-agnostic sort tags) ----------------------------
# `FPSortTag(ebits, sbits)` is a concrete IEEE format (Float32 = (8, 24),
# Float64 = (11, 53)); `SORT_RM` is the rounding-mode sort. FP builds identically
# in-memory on BOTH ayz3 and z3py (including a *symbolic* RoundingMode const), so
# the qf_fp fragment uses the ordinary in-memory build path.
SORT_RM = "RoundingMode"


@dataclass
class FPSortTag:
    ebits: int
    sbits: int

    def __eq__(self, other):
        return (isinstance(other, FPSortTag)
                and (other.ebits, other.sbits) == (self.ebits, self.sbits))

    def __hash__(self):
        return hash(("FP", self.ebits, self.sbits))


# --- algebraic datatypes (module-agnostic spec) ----------------------------
# A generated formula declares exactly ONE datatype, described by a module-
# AGNOSTIC recipe so BOTH `ayz3` and `z3` can replay the identical declaration
# (via their shared z3py-style Datatype builder). A constructor field sort is a
# primitive sort tag (SORT_INT / SORT_BOOL / ...) OR the sentinel string "self"
# for a self-reference (recursive datatypes like List/Tree).
DT_SELF = "self"


@dataclass
class DTCtor:
    name: str
    # list of (field_name, field_sort) where field_sort is a primitive sort tag
    # or DT_SELF.
    fields: list = field(default_factory=list)


@dataclass
class DTSpec:
    name: str
    ctors: List["DTCtor"] = field(default_factory=list)


class DTSort:
    """A datatype-sort tag carrying the (module-agnostic) DTSpec. Two DTSorts
    are equal iff their datatype names match, so it can be compared against the
    string sort tags (SORT_BOOL etc.) safely and hashed for var pooling."""

    __slots__ = ("spec",)

    def __init__(self, spec: "DTSpec"):
        self.spec = spec

    def __eq__(self, other):
        return isinstance(other, DTSort) and other.spec.name == self.spec.name

    def __hash__(self):
        return hash(("DT", self.spec.name))

    def __repr__(self):
        return f"DTSort({self.spec.name})"


def _dt_is_recursive_ctor(ctor: "DTCtor") -> bool:
    return any(fs == DT_SELF for _, fs in ctor.fields)


@dataclass
class Node:
    op: str
    sort: Any
    children: List["Node"] = field(default_factory=list)
    payload: Any = None  # literals / var names / widths / func signatures


# A declared uninterpreted function: name + (domain sorts, range sort). Carried
# on an "app" Node's payload so the SAME decl object is reused across both
# modules (each `build` re-declares it once per module via a small cache).
@dataclass
class FuncSig:
    name: str
    domain: tuple
    rng: Any

    def key(self):
        return self.name


# --- recursive function definitions (module-agnostic spec) ------------------
# A recursively defined function (z3py RecFunction/RecAddDefinition; AY's
# check-time-expanded rec defs). `body` is a Node over `var` Nodes named
# exactly the params; a recursive occurrence (self OR mutual partner) is a
# `recapp` Node whose payload is the (name, domain, range) triple — by-name so
# mutual pairs need no cyclic Node references. The whole formula is wrapped in
# ONE `recgroup` Node carrying every spec plus the definition ORDER
# ("def_first": define before building the goal's applications; "def_after":
# declare only, build the applications, then define — the z3py
# build-apps-before-RecAddDefinition idiom).
@dataclass
class RecSpec:
    name: str
    params: list  # [(param_name, sort_tag)]
    rng: Any      # range sort tag
    body: Node

    def domain(self):
        return tuple(s for _, s in self.params)


# ---------------------------------------------------------------------------
# Builder: realize a Node tree through a z3py-shaped module `m`.
# ---------------------------------------------------------------------------

def _sort_obj(m, sort):
    if sort == SORT_INT:
        return m.IntSort()
    if sort == SORT_REAL:
        return m.RealSort()
    if sort == SORT_BOOL:
        return m.BoolSort()
    if isinstance(sort, BV):
        return m.BitVecSort(sort.width)
    if isinstance(sort, ArrSort):
        return m.ArraySort(_sort_obj(m, sort.dom), _sort_obj(m, sort.rng))
    if isinstance(sort, SeqS):
        return m.SeqSort(_sort_obj(m, sort.elem))
    if isinstance(sort, FPSortTag):
        return m.FPSort(sort.ebits, sort.sbits)
    if sort == SORT_RM:
        # Both modules expose the RoundingMode sort as the sort of any RM value.
        return m.RNE().sort()
    raise AssertionError(f"unknown sort {sort!r}")


def _declare_func(m, sig: FuncSig, cache):
    """Declare `sig` as an uninterpreted function through module `m`, memoizing
    by name in `cache` so the same name always maps to ONE decl per build."""
    fd = cache.get(sig.name)
    if fd is not None:
        return fd
    arg_sorts = [_sort_obj(m, s) for s in sig.domain]
    fd = m.Function(sig.name, *arg_sorts, _sort_obj(m, sig.rng))
    cache[sig.name] = fd
    return fd


def _rec_declare(m, name, domain, rng_sort, cache):
    """Declare rec function `name` through module `m` (RecFunction), memoized
    by name in `cache` so every occurrence maps to ONE decl per build."""
    key = ("__rec__", name)
    fd = cache.get(key)
    if fd is None:
        sig = [_sort_obj(m, s) for s in domain] + [_sort_obj(m, rng_sort)]
        fd = m.RecFunction(name, *sig)
        cache[key] = fd
    return fd


def _rec_define(m, spec: "RecSpec", cache):
    """Attach `spec`'s recursive definition through module `m` (once per
    build). Mutual partners must already be DECLARED (recgroup declares every
    spec of the group up front), so a partner occurrence in the body resolves
    to the memoized decl."""
    fd = _rec_declare(m, spec.name, spec.domain(), spec.rng, cache)
    done = cache.setdefault("__recdef_done__", set())
    if spec.name in done:
        return fd
    done.add(spec.name)
    args = [build(Node("var", s, [], pn), m, cache) for pn, s in spec.params]
    body = build(spec.body, m, cache)
    try:
        m.RecAddDefinition(fd, args, body)
    except Exception as e:
        # Two rejections are swallowed BY DESIGN — any other failure must
        # surface (as a SKIP or a loud crash), never be masked:
        # 1. "already been given a definition": BOTH registries are
        #    context-global and add-only (z3 always; AY since the
        #    redefinition-rejection repair). The cross-check rebuilds the SAME
        #    node several times through the same module/context (verdict
        #    check, model pin, SMT-LIB render), and every replay carries the
        #    IDENTICAL body for this per-case-unique name, so that duplicate
        #    is semantically a no-op.
        # 2. "builtin operator name": AY REJECTS a rec def whose name it
        #    matches structurally as a builtin (`+`, `-`, `*`, …) — the
        #    builtin_shadow shape registers such a def on purpose and then
        #    probes ONLY builtin arithmetic, so a future regression to
        #    silent acceptance-and-corruption shows up as a DISAGREE (z3
        #    accepts the nominal def but its builtin `+` is untouched).
        s = str(e)
        if ("already been given a definition" not in s
                and "builtin operator name" not in s):
            raise
    return fd


def _dt_build(m, spec: DTSpec, cache):
    """Declare `spec`'s datatype through module `m` and return the created
    DatatypeSortRef, memoized per build in `cache` under a reserved key so BOTH
    modules build ONE shared sort (with the SAME constructor/accessor/recognizer
    decls) per formula.

    Both `ayz3` and `z3` expose the identical z3py Datatype builder API:
    `m.Datatype(name)`, `.declare(ctor, (field, sort), ...)` (a field sort of the
    builder itself marks a self-reference), `.create()`. The resulting
    DatatypeSortRef exposes `constructor(i)/recognizer(i)/accessor(i,j)` on both,
    which we drive by INDEX (constructor/recognizer/accessor *names* can differ
    across modules -- e.g. the recognizer prints as `is-cons` on ayz3 vs `is` on
    z3 -- so building by decl index keeps the two terms structurally identical)."""
    reg = cache.setdefault("__dt__", {})
    ds = reg.get(spec.name)
    if ds is not None:
        return ds
    builder = m.Datatype(spec.name)
    for ctor in spec.ctors:
        args = []
        for fname, fsort in ctor.fields:
            if fsort == DT_SELF:
                args.append((fname, builder))  # self-reference
            else:
                args.append((fname, _sort_obj(m, fsort)))
        builder.declare(ctor.name, *args)
    ds = builder.create()
    reg[spec.name] = ds
    return ds


def build(node: Node, m, _fcache=None):
    """Construct `node` as a z3py expression through module `m`.

    Any unsupported op surfaces as the module's own exception (e.g. ayz3's
    NotImplementedError); the differential runner treats that as a SKIP.

    `_fcache` memoizes uninterpreted-function declarations by name within a
    single build so every application of `f` refers to the same decl (and so the
    two modules build the structurally identical term).
    """
    if _fcache is None:
        _fcache = {}
    op = node.op

    # Quantifiers and UF applications need custom child handling, so dispatch
    # them BEFORE the generic child-build below.
    if op in ("forall", "exists"):
        # children: [bound_var_0, ..., body]; bound vars are plain `var` Nodes.
        *bound_nodes, body_node = node.children
        bound = [build(b, m, _fcache) for b in bound_nodes]
        body = build(body_node, m, _fcache)
        mk = m.ForAll if op == "forall" else m.Exists
        return mk(bound, body)
    if op == "app":
        sig = node.payload  # FuncSig
        fd = _declare_func(m, sig, _fcache)
        args = [build(c, m, _fcache) for c in node.children]
        return fd(*args)

    # Recursive function definitions: `recgroup` wraps the whole formula and
    # owns declaration/definition ORDER; `recapp` applies a rec decl by name.
    if op == "recgroup":
        specs, order = node.payload  # (tuple[RecSpec], "def_first"|"def_after")
        # Declare EVERY spec of the group first so mutual partners resolve.
        for sp in specs:
            _rec_declare(m, sp.name, sp.domain(), sp.rng, _fcache)
        if order == "def_first":
            for sp in specs:
                _rec_define(m, sp, _fcache)
        formula = build(node.children[0], m, _fcache)
        if order != "def_first":
            # z3py's build-applications-before-RecAddDefinition idiom: the
            # goal's rec applications were built while the decl had no body.
            for sp in specs:
                _rec_define(m, sp, _fcache)
        return formula
    if op == "recapp":
        rname, rdomain, rrng = node.payload
        fd = _rec_declare(m, rname, rdomain, rrng, _fcache)
        args = [build(c, m, _fcache) for c in node.children]
        return fd(*args)

    # Algebraic-datatype ops: build the (cached) datatype sort, then apply the
    # constructor / accessor / recognizer decl BY INDEX so both modules build the
    # structurally identical term. Dispatched before the generic child-build so
    # the decls are resolved from the shared DatatypeSortRef.
    if op == "dt_ctor":
        spec, ci = node.payload
        ds = _dt_build(m, spec, _fcache)
        args = [build(c, m, _fcache) for c in node.children]
        return ds.constructor(ci)(*args)
    if op == "dt_acc":
        spec, ci, fj = node.payload
        ds = _dt_build(m, spec, _fcache)
        arg = build(node.children[0], m, _fcache)
        return ds.accessor(ci, fj)(arg)
    if op == "dt_is":
        spec, ci = node.payload
        ds = _dt_build(m, spec, _fcache)
        arg = build(node.children[0], m, _fcache)
        return ds.recognizer(ci)(arg)

    ch = [build(c, m, _fcache) for c in node.children]

    # --- leaves -----------------------------------------------------------
    if op == "var":
        name = node.payload
        s = node.sort
        if s == SORT_INT:
            return m.Int(name)
        if s == SORT_REAL:
            return m.Real(name)
        if s == SORT_BOOL:
            return m.Bool(name)
        if isinstance(s, BV):
            return m.BitVec(name, s.width)
        if isinstance(s, ArrSort):
            return m.Array(name, _sort_obj(m, s.dom), _sort_obj(m, s.rng))
        if isinstance(s, DTSort):
            return m.Const(name, _dt_build(m, s.spec, _fcache))
        if isinstance(s, SeqS):
            return m.Const(name, _sort_obj(m, s))
        if isinstance(s, FPSortTag):
            return m.FP(name, _sort_obj(m, s))
        if s == SORT_RM:
            return m.Const(name, _sort_obj(m, s))
        raise AssertionError(f"var of unknown sort {s!r}")
    if op == "intval":
        return m.IntVal(node.payload)
    if op == "realval":
        n, d = node.payload
        return m.RealVal(n) / m.RealVal(d) if d != 1 else m.RealVal(n)
    if op == "bvval":
        v, w = node.payload
        return m.BitVecVal(v, w)
    if op == "boolval":
        return m.BoolVal(node.payload)

    # --- arithmetic (Int/Real) -------------------------------------------
    if op == "+":
        return ch[0] + ch[1]
    if op == "-":
        return ch[0] - ch[1]
    if op == "neg":
        return -ch[0]
    if op == "*const":
        # multiply a term by an integer constant (keeps QF_LIA linear)
        return node.payload * ch[0]
    if op == "*":
        # term * term (used by the recfun fragment's factorial body; the
        # product folds to a constant once the ground recursion expands)
        return ch[0] * ch[1]
    if op == "<":
        return ch[0] < ch[1]
    if op == "<=":
        return ch[0] <= ch[1]
    if op == ">":
        return ch[0] > ch[1]
    if op == ">=":
        return ch[0] >= ch[1]
    if op == "=":
        return ch[0] == ch[1]
    if op == "!=":
        return ch[0] != ch[1]

    # --- integrality predicate (is_int over a Real term) ------------------
    if op == "is_int":
        return m.IsInt(ch[0])

    # --- bitvector --------------------------------------------------------
    if op == "bvadd":
        return ch[0] + ch[1]
    if op == "bvsub":
        return ch[0] - ch[1]
    if op == "bvmul":
        return ch[0] * ch[1]
    if op == "bvand":
        return ch[0] & ch[1]
    if op == "bvor":
        return ch[0] | ch[1]
    if op == "bvxor":
        return ch[0] ^ ch[1]
    if op == "bvneg":
        return -ch[0]
    if op == "bvnot":
        return ~ch[0]
    if op == "bvslt":
        return ch[0] < ch[1]
    if op == "bvsle":
        return ch[0] <= ch[1]
    if op == "bvsgt":
        return ch[0] > ch[1]
    if op == "bvsge":
        return ch[0] >= ch[1]
    if op == "bvult":
        return m.ULT(ch[0], ch[1])
    if op == "bvule":
        return m.ULE(ch[0], ch[1])
    if op == "bvugt":
        return m.UGT(ch[0], ch[1])
    if op == "bvuge":
        return m.UGE(ch[0], ch[1])

    # --- arrays -----------------------------------------------------------
    if op == "select":
        return m.Select(ch[0], ch[1])
    if op == "store":
        return m.Store(ch[0], ch[1], ch[2])

    # --- sequences ((Seq Int) / (Seq Bool)) -------------------------------
    # These build in-memory only on z3py (the reference renderer); on ayz3 the
    # `sequences` fragment goes through the SMT-LIB parser instead (its in-memory
    # seq builders accept only the String sort). Every op below maps to the SAME
    # SMT operator (seq.++, seq.len, ...) that z3py's canonical `sexpr()` emits,
    # so the text fed to both parsers is identical.
    if op == "seq_concat":
        return m.Concat(ch[0], ch[1])
    if op == "seq_len":
        return m.Length(ch[0])
    if op == "seq_unit":
        return m.Unit(ch[0])
    if op == "seq_empty":
        return m.Empty(_sort_obj(m, node.sort))
    if op == "seq_nth":
        return ch[0][ch[1]]
    if op == "seq_at":
        return ch[0].at(ch[1])
    if op == "seq_extract":
        return m.Extract(ch[0], ch[1], ch[2])
    if op == "seq_contains":
        return m.Contains(ch[0], ch[1])
    if op == "seq_prefixof":
        return m.PrefixOf(ch[0], ch[1])
    if op == "seq_suffixof":
        return m.SuffixOf(ch[0], ch[1])
    if op == "seq_indexof":
        return m.IndexOf(ch[0], ch[1], ch[2])
    if op == "seq_replace":
        return m.Replace(ch[0], ch[1], ch[2])

    # --- floating point ---------------------------------------------------
    # Literal + special values.
    if op == "fp_val":
        return m.FPVal(node.payload, _sort_obj(m, node.sort))
    if op == "fp_nan":
        return m.fpNaN(_sort_obj(m, node.sort))
    if op == "fp_pinf":
        return m.fpPlusInfinity(_sort_obj(m, node.sort))
    if op == "fp_ninf":
        return m.fpMinusInfinity(_sort_obj(m, node.sort))
    if op == "fp_pzero":
        return m.fpPlusZero(_sort_obj(m, node.sort))
    if op == "fp_mzero":
        return m.fpMinusZero(_sort_obj(m, node.sort))
    # Literal rounding modes.
    if op == "rm_rne":
        return m.RNE()
    if op == "rm_rna":
        return m.RNA()
    if op == "rm_rtp":
        return m.RTP()
    if op == "rm_rtn":
        return m.RTN()
    if op == "rm_rtz":
        return m.RTZ()
    # Arithmetic that rounds with a rounding mode (ch[0] is the RM term).
    if op == "fp_add":
        return m.fpAdd(ch[0], ch[1], ch[2])
    if op == "fp_sub":
        return m.fpSub(ch[0], ch[1], ch[2])
    if op == "fp_mul":
        return m.fpMul(ch[0], ch[1], ch[2])
    if op == "fp_div":
        return m.fpDiv(ch[0], ch[1], ch[2])
    if op == "fp_sqrt":
        return m.fpSqrt(ch[0], ch[1])
    if op == "fp_fma":
        return m.fpFMA(ch[0], ch[1], ch[2], ch[3])
    if op == "fp_rti":
        return m.fpRoundToIntegral(ch[0], ch[1])
    # Arithmetic without a rounding mode.
    if op == "fp_neg":
        return m.fpNeg(ch[0])
    if op == "fp_abs":
        return m.fpAbs(ch[0])
    if op == "fp_rem":
        return m.fpRem(ch[0], ch[1])
    if op == "fp_min":
        return m.fpMin(ch[0], ch[1])
    if op == "fp_max":
        return m.fpMax(ch[0], ch[1])
    # IEEE comparisons / classification predicates (-> Bool).
    if op == "fp_eq":
        return m.fpEQ(ch[0], ch[1])
    if op == "fp_lt":
        return m.fpLT(ch[0], ch[1])
    if op == "fp_leq":
        return m.fpLEQ(ch[0], ch[1])
    if op == "fp_gt":
        return m.fpGT(ch[0], ch[1])
    if op == "fp_geq":
        return m.fpGEQ(ch[0], ch[1])
    if op == "fp_isnan":
        return m.fpIsNaN(ch[0])
    if op == "fp_isinf":
        return m.fpIsInf(ch[0])
    if op == "fp_iszero":
        return m.fpIsZero(ch[0])
    if op == "fp_isnormal":
        return m.fpIsNormal(ch[0])
    if op == "fp_issubnormal":
        return m.fpIsSubnormal(ch[0])
    if op == "fp_isneg":
        return m.fpIsNegative(ch[0])
    if op == "fp_ispos":
        return m.fpIsPositive(ch[0])
    # Conversions to FP (ch[0] is the RM term for real->fp; bv->fp is IEEE bits).
    if op == "fp_from_real":
        return m.fpToFP(ch[0], ch[1], _sort_obj(m, node.sort))
    if op == "fp_from_bv":
        return m.fpToFP(ch[0], _sort_obj(m, node.sort))

    # --- boolean ----------------------------------------------------------
    if op == "and":
        return m.And(*ch)
    if op == "or":
        return m.Or(*ch)
    if op == "not":
        return m.Not(ch[0])
    if op == "implies":
        return m.Implies(ch[0], ch[1])
    if op == "xor":
        return m.Xor(ch[0], ch[1])
    if op == "ite":
        return m.If(ch[0], ch[1], ch[2])
    if op == "distinct":
        return m.Distinct(*ch)

    raise AssertionError(f"unknown op {op!r}")


# ---------------------------------------------------------------------------
# Generator core
# ---------------------------------------------------------------------------

class _Gen:
    """Per-formula generator state (vars, PRNG, fragment knobs)."""

    def __init__(self, rng: random.Random, fragment: str, bv_width: int):
        self.rng = rng
        self.fragment = fragment
        self.bv_width = bv_width
        # Reusable variable pool keyed by sort so the formula refers to the
        # same vars repeatedly (creates real constraints, not trivially-sat).
        self._vars = {}  # sort-key -> [Node, ...]
        # Reusable uninterpreted-function pool (for UF fragments), keyed by
        # (domain-key-tuple, range-key) so applications of the SAME f recur.
        self._funcs = {}  # sig-key -> [FuncSig, ...]
        # When set, `int_term` may emit uninterpreted-function applications
        # (used by the UF+LIA fragment). Off by default so the original
        # fragments regenerate byte-identical trees.
        self.use_uf = False
        # Datatype fragment state. `dt_spec` is the single datatype declared for
        # this formula; when `use_dt` is set, `int_term` may recurse into Int-
        # sorted accessor applications over datatype terms (tying LIA into the
        # datatype theory). Off by default so other fragments are byte-identical.
        self.use_dt = False
        self.dt_spec = None
        # Sequence fragment state. When `use_seq` is set, `int_term` may recurse
        # into Int-sorted sequence terms (seq.len / seq.nth over a (Seq Int)),
        # tying LIA into the sequence theory. `seq_elem` is the single element
        # sort of every sequence in the formula (SORT_INT or SORT_BOOL). Off by
        # default so other fragments regenerate byte-identical trees.
        self.use_seq = False
        self.seq_elem = None
        # Floating-point fragment state. `fp_sort` is the single IEEE format of
        # every FP term in the formula. Off by default.
        self.use_fp = False
        self.fp_sort = None

    # -- variables ---------------------------------------------------------

    def _sort_key(self, sort):
        if isinstance(sort, BV):
            return ("BV", sort.width)
        if isinstance(sort, ArrSort):
            return ("Arr", self._sort_key(sort.dom), self._sort_key(sort.rng))
        if isinstance(sort, DTSort):
            return ("DT", sort.spec.name)
        if isinstance(sort, SeqS):
            return ("Seq", self._sort_key(sort.elem))
        if isinstance(sort, FPSortTag):
            return ("FP", sort.ebits, sort.sbits)
        return sort

    def var(self, sort, max_pool):
        key = self._sort_key(sort)
        pool = self._vars.setdefault(key, [])
        # Either reuse an existing var or (sometimes) introduce a new one.
        if pool and (len(pool) >= max_pool or self.rng.random() < 0.6):
            return self.rng.choice(pool)
        name = self._var_name(sort, len(pool))
        node = Node("var", sort, [], name)
        pool.append(node)
        return node

    def _var_name(self, sort, idx):
        if sort == SORT_INT:
            return f"i{idx}"
        if sort == SORT_REAL:
            return f"r{idx}"
        if sort == SORT_BOOL:
            return f"b{idx}"
        if isinstance(sort, BV):
            return f"v{sort.width}_{idx}"
        if isinstance(sort, ArrSort):
            return f"A{idx}"
        if isinstance(sort, DTSort):
            return f"d{idx}"
        if isinstance(sort, SeqS):
            return (f"sq{idx}" if sort.elem == SORT_INT else f"sqb{idx}")
        if isinstance(sort, FPSortTag):
            return f"fp{idx}"
        if sort == SORT_RM:
            return f"rm{idx}"
        return f"x{idx}"

    # -- uninterpreted functions ------------------------------------------

    def func(self, domain, rng, max_pool=3):
        """Pick (or sometimes create) an uninterpreted-function declaration with
        the given domain sorts and range sort. Reused like variables so multiple
        applications of the same `f` create real congruence constraints.

        Names are GLOBALLY unique across all signatures (the builder caches
        decls by name, so two distinct sigs must never share a name) and encode
        the arity to keep them readable.
        """
        key = (tuple(self._sort_key(s) for s in domain), self._sort_key(rng))
        pool = self._funcs.setdefault(key, [])
        if pool and (len(pool) >= max_pool or self.rng.random() < 0.6):
            return self.rng.choice(pool)
        # Globally-unique name: total sig count so far + arity tag.
        total = sum(len(p) for p in self._funcs.values())
        name = f"f{len(domain)}a_{total}"
        sig = FuncSig(name, tuple(domain), rng)
        pool.append(sig)
        return sig

    def uf_int_app(self, depth):
        """An Int-sorted application f(args...) of an uninterpreted function
        whose args are Int terms (UF + LIA)."""
        r = self.rng
        arity = r.randint(1, 2)
        sig = self.func([SORT_INT] * arity, SORT_INT)
        args = [self.int_term(max(0, depth - 1)) for _ in range(arity)]
        return Node("app", SORT_INT, args, sig)

    # -- integer / real terms ---------------------------------------------

    def int_term(self, depth):
        r = self.rng
        if depth <= 0 or r.random() < 0.35:
            if r.random() < 0.4:
                return Node("intval", SORT_INT, [], r.randint(-6, 6))
            # In UF mode, sometimes the "leaf" is an f(...) application instead
            # of a bare variable -- this is what makes the fragment exercise UF.
            if self.use_uf and r.random() < 0.45:
                return self.uf_int_app(depth)
            # In datatype mode, sometimes the "leaf" is an Int-sorted accessor
            # applied to a datatype term (e.g. hd(cons(..)) / val(x)) -- this
            # ties linear-int reasoning into the datatype theory. Guarded by
            # depth >= 1 so the int_term <-> dt_term mutual recursion strictly
            # decreases (a depth-0 accessor over a ground ctor would re-enter
            # int_term at depth 0 and could diverge).
            if (depth >= 1 and self.use_dt and self.dt_spec is not None
                    and self._dt_int_accessors(self.dt_spec)
                    and r.random() < 0.5):
                return self.dt_int_accessor(self.dt_spec, depth)
            # In sequence mode over (Seq Int), an Int "leaf" can be seq.len or
            # seq.nth of a sequence term -- this creates real Int constraints on
            # sequence lengths/elements (the LIA<->seq combination). Guarded by
            # depth >= 1 so the int_term <-> seq_term mutual recursion strictly
            # decreases. `use_seq` is checked BEFORE r.random() so other
            # fragments draw no extra RNG and regenerate identically.
            if (depth >= 1 and self.use_seq and self.seq_elem == SORT_INT
                    and r.random() < 0.4):
                if r.random() < 0.6:
                    return Node("seq_len", SORT_INT, [self.seq_term(depth - 1)])
                return Node("seq_nth", SORT_INT,
                            [self.seq_term(depth - 1), self.int_term(0)])
            return self.var(SORT_INT, max_pool=4)
        choice = r.random()
        if choice < 0.30:
            return Node("+", SORT_INT, [self.int_term(depth - 1),
                                        self.int_term(depth - 1)])
        if choice < 0.55:
            return Node("-", SORT_INT, [self.int_term(depth - 1),
                                        self.int_term(depth - 1)])
        if choice < 0.75:
            # linear: constant * term  (keeps it QF_LIA)
            return Node("*const", SORT_INT, [self.int_term(depth - 1)],
                        r.randint(-4, 4))
        if choice < 0.88:
            return Node("neg", SORT_INT, [self.int_term(depth - 1)])
        # ite over Int (condition is an Int/QF_LIA boolean)
        return Node("ite", SORT_INT, [self.bool_term(depth - 1, "lia"),
                                      self.int_term(depth - 1),
                                      self.int_term(depth - 1)])

    def real_term(self, depth):
        r = self.rng
        if depth <= 0 or r.random() < 0.35:
            if r.random() < 0.4:
                num = r.randint(-6, 6)
                den = r.choice([1, 1, 2, 3, 4])
                return Node("realval", SORT_REAL, [], (num, den))
            return self.var(SORT_REAL, max_pool=4)
        choice = r.random()
        if choice < 0.32:
            return Node("+", SORT_REAL, [self.real_term(depth - 1),
                                         self.real_term(depth - 1)])
        if choice < 0.60:
            return Node("-", SORT_REAL, [self.real_term(depth - 1),
                                         self.real_term(depth - 1)])
        if choice < 0.82:
            return Node("*const", SORT_REAL,
                        [self.real_term(depth - 1)],
                        Node("realval", SORT_REAL, [], (r.randint(-4, 4), 1)).payload[0])
        if choice < 0.92:
            return Node("neg", SORT_REAL, [self.real_term(depth - 1)])
        return Node("ite", SORT_REAL, [self.bool_term(depth - 1, "lra"),
                                       self.real_term(depth - 1),
                                       self.real_term(depth - 1)])

    # -- bitvector terms ---------------------------------------------------

    def bv_term(self, depth, width=None):
        r = self.rng
        w = width or self.bv_width
        sort = BV(w)
        if depth <= 0 or r.random() < 0.35:
            if r.random() < 0.4:
                return Node("bvval", sort, [], (r.randint(0, (1 << w) - 1), w))
            return self.var(sort, max_pool=4)
        binops = ["bvadd", "bvsub", "bvmul", "bvand", "bvor", "bvxor"]
        choice = r.random()
        if choice < 0.7:
            op = r.choice(binops)
            return Node(op, sort, [self.bv_term(depth - 1, w),
                                   self.bv_term(depth - 1, w)])
        if choice < 0.82:
            return Node("bvneg", sort, [self.bv_term(depth - 1, w)])
        if choice < 0.92:
            return Node("bvnot", sort, [self.bv_term(depth - 1, w)])
        return Node("ite", sort, [self.bool_term(depth - 1, "bv", w),
                                  self.bv_term(depth - 1, w),
                                  self.bv_term(depth - 1, w)])

    # -- array terms (Int -> Int) -----------------------------------------

    def arr_sort(self):
        return ArrSort(SORT_INT, SORT_INT)

    def arr_term(self, depth):
        r = self.rng
        sort = self.arr_sort()
        if depth <= 0 or r.random() < 0.5:
            return self.var(sort, max_pool=3)
        # store(a, i, v)
        return Node("store", sort, [self.arr_term(depth - 1),
                                    self.int_term(depth - 1),
                                    self.int_term(depth - 1)])

    # -- algebraic-datatype terms -----------------------------------------

    def _dt_int_accessors(self, spec):
        """(ctor_index, field_index) of every Int-sorted accessor of `spec`."""
        return [(ci, fj) for ci, c in enumerate(spec.ctors)
                for fj, (_, fs) in enumerate(c.fields) if fs == SORT_INT]

    def _dt_self_accessors(self, spec):
        """(ctor_index, field_index) of every self-typed accessor (recursive)."""
        return [(ci, fj) for ci, c in enumerate(spec.ctors)
                for fj, (_, fs) in enumerate(c.fields) if fs == DT_SELF]

    def _dt_ctor_app(self, spec, ci, depth):
        """A constructor application `ctor(field0, field1, ...)`. Int/Bool fields
        become linear-int / boolean terms; a self-field recurses (depth-bounded)."""
        ctor = spec.ctors[ci]
        children = []
        for _fname, fsort in ctor.fields:
            if fsort == DT_SELF:
                children.append(self.dt_term(spec, depth - 1))
            elif fsort == SORT_BOOL:
                children.append(self.bool_term(max(0, depth - 1), domain="lia"))
            else:  # SORT_INT (the only scalar field sort we generate)
                children.append(self.int_term(max(0, depth - 1)))
        return Node("dt_ctor", DTSort(spec), children, (spec, ci))

    def dt_term(self, spec, depth):
        """A datatype-sorted term: a reused var, a constructor application, a
        self-typed accessor over a datatype term, or an ite. Depth-bounded so
        recursive datatypes (List/Tree) never diverge; the base case always has a
        non-recursive constructor available (declared for every recursive spec)."""
        r = self.rng
        nonrec = [i for i, c in enumerate(spec.ctors)
                  if not _dt_is_recursive_ctor(c)]
        if depth <= 0 or r.random() < 0.4:
            # Leaf: a reused datatype var, or a GROUND non-recursive constructor.
            if r.random() < 0.5 or not nonrec:
                return self.var(DTSort(spec), max_pool=3)
            return self._dt_ctor_app(spec, r.choice(nonrec), 0)
        choice = r.random()
        self_accs = self._dt_self_accessors(spec)
        if choice < 0.6:
            # Any constructor (recursive ones recurse into dt_term, bounded).
            ci = r.randrange(len(spec.ctors))
            return self._dt_ctor_app(spec, ci, depth)
        if choice < 0.82 and self_accs:
            ci, fj = r.choice(self_accs)
            base = self.dt_term(spec, depth - 1)
            return Node("dt_acc", DTSort(spec), [base], (spec, ci, fj))
        # ite over the datatype, guarded by a tester on a SMALLER datatype term.
        # The condition uses depth-1 (not a full atom) so dt_term's recursion is
        # STRUCTURALLY depth-decreasing and generation always terminates.
        ci = r.randrange(len(spec.ctors))
        cond = Node("dt_is", SORT_BOOL,
                    [self.dt_term(spec, depth - 1)], (spec, ci))
        return Node("ite", DTSort(spec),
                    [cond, self.dt_term(spec, depth - 1),
                     self.dt_term(spec, depth - 1)])

    def dt_int_accessor(self, spec, depth):
        """An Int-sorted accessor applied to a datatype term (e.g. `hd(x)`)."""
        r = self.rng
        ci, fj = r.choice(self._dt_int_accessors(spec))
        base = self.dt_term(spec, max(0, depth - 1))
        return Node("dt_acc", SORT_INT, [base], (spec, ci, fj))

    # -- boolean / atom terms ---------------------------------------------

    def bool_term(self, depth, domain="lia", width=None):
        """Generate a Bool node. `domain` selects which atoms we build:
        'lia' (Int), 'lra' (Real), 'bv', 'arr', 'mixed'."""
        r = self.rng
        if depth <= 0 or r.random() < 0.45:
            return self.atom(domain, width)
        choice = r.random()
        if choice < 0.30:
            k = r.randint(2, 3)
            return Node("and", SORT_BOOL,
                        [self.bool_term(depth - 1, domain, width) for _ in range(k)])
        if choice < 0.55:
            k = r.randint(2, 3)
            return Node("or", SORT_BOOL,
                        [self.bool_term(depth - 1, domain, width) for _ in range(k)])
        if choice < 0.72:
            return Node("not", SORT_BOOL, [self.bool_term(depth - 1, domain, width)])
        if choice < 0.84:
            return Node("implies", SORT_BOOL,
                        [self.bool_term(depth - 1, domain, width),
                         self.bool_term(depth - 1, domain, width)])
        if choice < 0.92:
            return Node("xor", SORT_BOOL,
                        [self.bool_term(depth - 1, domain, width),
                         self.bool_term(depth - 1, domain, width)])
        return Node("ite", SORT_BOOL, [self.bool_term(depth - 1, domain, width),
                                       self.bool_term(depth - 1, domain, width),
                                       self.bool_term(depth - 1, domain, width)])

    def atom(self, domain, width=None):
        r = self.rng
        if domain == "lia":
            return self._arith_atom(self.int_term, SORT_INT)
        if domain == "lra":
            return self._arith_atom(self.real_term, SORT_REAL)
        if domain == "bv":
            return self._bv_atom(width)
        if domain == "arr":
            return self._arr_atom()
        if domain == "mixed":
            # occasional plain boolean variable
            if r.random() < 0.2:
                return self.var(SORT_BOOL, max_pool=4)
            return self._arith_atom(self.int_term, SORT_INT)
        if domain == "uflia":
            return self._uflia_atom()
        if domain == "arr_lia":
            return self._arr_lia_atom()
        if domain == "bv_bool":
            return self._bv_atom(width)
        if domain == "datatypes":
            return self._dt_atom(self.dt_spec)
        if domain == "sequences":
            return self._seq_atom()
        if domain == "qf_fp":
            return self._fp_atom()
        raise AssertionError(domain)

    def _arith_atom(self, term_fn, sort):
        r = self.rng
        # mix in a bare boolean variable sometimes for boolean structure
        if r.random() < 0.12:
            return self.var(SORT_BOOL, max_pool=4)
        op = r.choice(["<", "<=", ">", ">=", "=", "!="])
        a = term_fn(2)
        b = term_fn(2)
        return Node(op, SORT_BOOL, [a, b])

    def _bv_atom(self, width=None):
        r = self.rng
        if r.random() < 0.12:
            return self.var(SORT_BOOL, max_pool=4)
        op = r.choice(["bvslt", "bvsle", "bvsgt", "bvsge",
                       "bvult", "bvule", "bvugt", "bvuge", "=", "!="])
        a = self.bv_term(2, width)
        b = self.bv_term(2, width)
        return Node(op, SORT_BOOL, [a, b])

    def _arr_atom(self):
        r = self.rng
        if r.random() < 0.5:
            # select equality / inequality
            op = r.choice(["=", "!=", "<", "<=", ">", ">="])
            a = Node("select", SORT_INT, [self.arr_term(2), self.int_term(2)])
            if r.random() < 0.5:
                b = Node("select", SORT_INT, [self.arr_term(2), self.int_term(2)])
            else:
                b = self.int_term(2)
            return Node(op, SORT_BOOL, [a, b])
        # plain Int atom mixed in
        return self._arith_atom(self.int_term, SORT_INT)

    def _uflia_atom(self):
        """UF+LIA atom: a comparison whose operands mix uninterpreted-function
        applications f(...) with ordinary linear-int terms. `use_uf` must be set
        so `int_term` can recurse into applications."""
        r = self.rng
        if r.random() < 0.10:
            return self.var(SORT_BOOL, max_pool=4)
        op = r.choice(["=", "!=", "<", "<=", ">", ">="])
        # At least one side is a function application (the UF content).
        a = self.uf_int_app(2)
        if r.random() < 0.55:
            b = self.uf_int_app(2)
        else:
            b = self.int_term(2)
        return Node(op, SORT_BOOL, [a, b])

    def _dt_atom(self, spec):
        """A datatype atom exercising the datatype theory's core reasoning:

          * TESTER          `is-ctor(t)`  (+ disjointness/exhaustiveness once the
                            boolean skeleton combines several testers of one term)
          * (DIS)EQUALITY   `t1 = t2` / `t1 != t2` between datatype terms -- with
                            constructor applications on both sides this forces
                            CONSTRUCTOR INJECTIVITY (equal ctor apps => equal
                            fields) and DISJOINTNESS (distinct ctors are unequal).
          * ACCESSOR + LIA  `acc(t) OP <int term>` -- accessor value tangled with
                            linear arithmetic (accessor semantics + LIA cooperate).
        """
        r = self.rng
        int_accs = self._dt_int_accessors(spec)
        c = r.random()
        if c < 0.30:
            # Tester over a datatype term.
            ci = r.randrange(len(spec.ctors))
            return Node("dt_is", SORT_BOOL, [self.dt_term(spec, 2)], (spec, ci))
        if c < 0.62:
            # Equality / disequality of two datatype terms (injectivity /
            # disjointness reasoning when the sides are constructor apps).
            op = "=" if r.random() < 0.55 else "!="
            a = self.dt_term(spec, 2)
            b = self.dt_term(spec, 2)
            return Node(op, SORT_BOOL, [a, b])
        if c < 0.85 and int_accs:
            # Accessor value compared against a linear-int term.
            op = r.choice(["=", "!=", "<", "<=", ">", ">="])
            a = self.dt_int_accessor(spec, 2)
            b = self.dt_int_accessor(spec, 2) if r.random() < 0.5 else self.int_term(2)
            return Node(op, SORT_BOOL, [a, b])
        # Fallback: a plain boolean var or linear-int atom for propositional
        # structure (kept so formulas are not ALL datatype atoms).
        if r.random() < 0.25:
            return self.var(SORT_BOOL, max_pool=3)
        return self._arith_atom(self.int_term, SORT_INT)

    def _arr_lia_atom(self):
        """Arrays+LIA combined atom: select reads tangled with linear-int
        arithmetic on both the indices and the compared values, so the array
        theory and LIA must cooperate (not just array-vs-array equalities)."""
        r = self.rng
        if r.random() < 0.10:
            return self.var(SORT_BOOL, max_pool=4)
        op = r.choice(["=", "!=", "<", "<=", ">", ">="])
        # LHS: a select whose VALUE is wrapped in linear arithmetic.
        sel = Node("select", SORT_INT, [self.arr_term(2), self.int_term(2)])
        a = Node("+", SORT_INT, [sel, self.int_term(1)])
        # RHS: either another (arith-wrapped) select or a plain linear-int term.
        if r.random() < 0.6:
            sel2 = Node("select", SORT_INT, [self.arr_term(2), self.int_term(2)])
            b = Node("-", SORT_INT, [sel2, self.int_term(1)])
        else:
            b = self.int_term(2)
        return Node(op, SORT_BOOL, [a, b])

    # -- sequence terms ((Seq Int) / (Seq Bool)) --------------------------

    def seq_elem_term(self):
        """A single element for `seq.unit` / an `(Seq Bool)` element atom: an Int
        term (Seq Int) or a Bool leaf (Seq Bool). Uses int_term(0) so it can never
        re-enter the seq<->int recursion (keeps generation terminating)."""
        r = self.rng
        if self.seq_elem == SORT_INT:
            return self.int_term(0)
        if r.random() < 0.5:
            return Node("boolval", SORT_BOOL, [], r.random() < 0.5)
        return self.var(SORT_BOOL, max_pool=3)

    def seq_term(self, depth):
        """A `(Seq elem)`-sorted term: a reused seq var, empty, unit(elem), or a
        seq.++/extract/at/replace composition. Depth-bounded so generation
        terminates; offsets/lengths use int_term(0) to avoid unbounded
        seq<->int mutual recursion."""
        r = self.rng
        S = SeqS(self.seq_elem)
        if depth <= 0 or r.random() < 0.4:
            c = r.random()
            if c < 0.6:
                return self.var(S, max_pool=4)
            if c < 0.8:
                return Node("seq_empty", S, [], None)
            return Node("seq_unit", S, [self.seq_elem_term()])
        c = r.random()
        if c < 0.4:
            return Node("seq_concat", S,
                        [self.seq_term(depth - 1), self.seq_term(depth - 1)])
        if c < 0.6:
            # extract(seq, off, len). Half the time build the EXTRACT-WHOLE shape
            # extract(s, 0, seq.len s) (a bug shape), reusing the same subterm.
            s = self.seq_term(depth - 1)
            if r.random() < 0.5:
                off = Node("intval", SORT_INT, [], 0)
                length = Node("seq_len", SORT_INT, [s])
            else:
                off = self.int_term(0)
                length = self.int_term(0)
            return Node("seq_extract", S, [s, off, length])
        if c < 0.75:
            return Node("seq_at", S, [self.seq_term(depth - 1), self.int_term(0)])
        if c < 0.9:
            return Node("seq_replace", S,
                        [self.seq_term(depth - 1), self.seq_term(depth - 1),
                         self.seq_term(depth - 1)])
        return self.var(S, max_pool=4)

    def seq_int_term(self, depth):
        """An Int from a sequence: seq.len or seq.indexof (LIA<->seq bridge)."""
        r = self.rng
        if r.random() < 0.6:
            return Node("seq_len", SORT_INT, [self.seq_term(max(0, depth - 1))])
        return Node("seq_indexof", SORT_INT,
                    [self.seq_term(max(0, depth - 1)),
                     self.seq_term(max(0, depth - 1)), self.int_term(0)])

    def _seq_atom(self):
        """A sequence atom over reused seq/int vars, covering the shapes the
        recent (Seq Int) wrong-verdict bugs were in: extract-whole identity,
        at/nth linkage, contains chains (transitivity), concatenation, plus
        prefix/suffix/indexof and Int constraints on seq.len."""
        r = self.rng
        E = self.seq_elem
        S = SeqS(E)
        c = r.random()
        if c < 0.16:
            return Node("seq_contains", SORT_BOOL,
                        [self.seq_term(2), self.seq_term(2)])
        if c < 0.28:
            # explicit 2-hop contains chain (contains transitivity trigger).
            a = self.var(S, max_pool=4)
            b = self.var(S, max_pool=4)
            d = self.var(S, max_pool=4)
            return Node("and", SORT_BOOL,
                        [Node("seq_contains", SORT_BOOL, [a, b]),
                         Node("seq_contains", SORT_BOOL, [b, d])])
        if c < 0.38:
            return Node("seq_prefixof", SORT_BOOL,
                        [self.seq_term(2), self.seq_term(2)])
        if c < 0.48:
            return Node("seq_suffixof", SORT_BOOL,
                        [self.seq_term(2), self.seq_term(2)])
        if c < 0.60:
            # seq (dis)equality (extensionality / concatenation reasoning).
            op = "=" if r.random() < 0.6 else "!="
            return Node(op, SORT_BOOL, [self.seq_term(2), self.seq_term(2)])
        if c < 0.72:
            # extract-whole identity shape: extract(s, 0, seq.len s) (=/!=) s.
            s = self.var(S, max_pool=4)
            whole = Node("seq_extract", S,
                         [s, Node("intval", SORT_INT, [], 0),
                          Node("seq_len", SORT_INT, [s])])
            op = "=" if r.random() < 0.7 else "!="
            return Node(op, SORT_BOOL, [whole, s])
        if c < 0.85:
            # at/nth linkage.
            if E == SORT_INT:
                if r.random() < 0.35:
                    # POINT-READ shape (P0.1 phase-2a): two arithmetic bounds and
                    # (often) a disequality on the SAME bare-var `seq.nth` cell —
                    # the `4 < (seq.nth s 0) < 6 ∧ != 5` family the point-read
                    # reduction routes into the LIA core (a mix of sat and the
                    # integer-gap unsat, both z3-decided).
                    s = self.var(S, max_pool=4)
                    idx = Node("intval", SORT_INT, [], r.randint(0, 2))
                    nth = Node("seq_nth", SORT_INT, [s, idx])
                    lo = r.randint(-4, 4)
                    hi = lo + r.randint(1, 4)
                    atoms = [
                        Node(">", SORT_BOOL, [nth, Node("intval", SORT_INT, [], lo)]),
                        Node("<", SORT_BOOL, [nth, Node("intval", SORT_INT, [], hi)]),
                    ]
                    if r.random() < 0.6:
                        atoms.append(
                            Node("!=", SORT_BOOL,
                                 [nth, Node("intval", SORT_INT, [], r.randint(lo, hi))]))
                    return Node("and", SORT_BOOL, atoms)
                nth = Node("seq_nth", SORT_INT, [self.seq_term(2), self.int_term(0)])
                op = r.choice(["=", "!=", "<", "<=", ">", ">="])
                return Node(op, SORT_BOOL, [nth, self.int_term(1)])
            # (Seq Bool): seq.nth is itself a Bool atom.
            return Node("seq_nth", SORT_BOOL, [self.seq_term(2), self.int_term(0)])
        # Int atom over seq.len / seq.indexof (LIA<->seq combination).
        op = r.choice(["=", "!=", "<", "<=", ">", ">="])
        a = self.seq_int_term(2)
        b = self.seq_int_term(2) if r.random() < 0.4 else self.int_term(2)
        return Node(op, SORT_BOOL, [a, b])

    # -- floating-point terms ---------------------------------------------

    # A spread of literal values (exact + rounding-sensitive + specials) that
    # FPVal rounds to the target format with RNE identically on both modules.
    _FP_VALUES = [0.0, -0.0, 1.0, -1.0, 0.5, -0.5, 1.5, 2.0, -2.25, 3.5,
                  0.1, -0.1, 100.0, -128.0, "1/3", "2/7", 1e6, 1e-6]

    def rm_term(self):
        """A rounding-mode term: a reused SYMBOLIC RoundingMode var (the bug
        class), one of the five literal modes RNE/RNA/RTP/RTN/RTZ, or (rarely)
        an ite between two simple rounding-mode terms (#P0.2: an RM-sorted ite
        as a rounding-op operand is AY's documented fail-closed residue today
        -- `unknown` counts as a skip, never a disagreement -- while in an
        equality atom the EUF-lane domain axioms decide it)."""
        r = self.rng
        if r.random() < 0.06:
            return Node("ite", SORT_RM,
                        [self.var(SORT_BOOL, max_pool=4),
                         self._rm_simple(), self._rm_simple()])
        return self._rm_simple()

    def _rm_simple(self):
        """A symbolic RoundingMode var or one of the five literal modes."""
        r = self.rng
        if r.random() < 0.45:
            return self.var(SORT_RM, max_pool=6)  # symbolic rounding mode
        op = r.choice(["rm_rne", "rm_rna", "rm_rtp", "rm_rtn", "rm_rtz"])
        return Node(op, SORT_RM, [], None)

    def fp_leaf(self):
        r = self.rng
        c = r.random()
        if c < 0.45:
            return self.var(self.fp_sort, max_pool=4)
        if c < 0.70:
            return Node("fp_val", self.fp_sort, [], r.choice(self._FP_VALUES))
        # special values: NaN / +oo / -oo / +0 / -0
        op = r.choice(["fp_nan", "fp_pinf", "fp_ninf", "fp_pzero", "fp_mzero"])
        return Node(op, self.fp_sort, [], None)

    def fp_term(self, depth):
        """An FP-sorted term over reused FP vars, literals and special values,
        composed with add/sub/mul/div/sqrt/fma/roundToIntegral (each with a
        literal-or-symbolic rounding mode), neg/abs/rem/min/max, and to_fp from
        real / IEEE-bits bitvector."""
        r = self.rng
        S = self.fp_sort
        if depth <= 0 or r.random() < 0.4:
            return self.fp_leaf()
        c = r.random()
        if c < 0.34:
            op = r.choice(["fp_add", "fp_sub", "fp_mul", "fp_div"])
            return Node(op, S, [self.rm_term(), self.fp_term(depth - 1),
                                self.fp_term(depth - 1)])
        if c < 0.46:
            return Node("fp_sqrt", S, [self.rm_term(), self.fp_term(depth - 1)])
        if c < 0.58:
            return Node("fp_fma", S,
                        [self.rm_term(), self.fp_term(depth - 1),
                         self.fp_term(depth - 1), self.fp_term(depth - 1)])
        if c < 0.70:
            return Node("fp_rti", S, [self.rm_term(), self.fp_term(depth - 1)])
        if c < 0.80:
            op = r.choice(["fp_neg", "fp_abs"])
            return Node(op, S, [self.fp_term(depth - 1)])
        if c < 0.90:
            op = r.choice(["fp_rem", "fp_min", "fp_max"])
            return Node(op, S, [self.fp_term(depth - 1), self.fp_term(depth - 1)])
        # to_fp conversions.
        if r.random() < 0.5:
            return Node("fp_from_real", S, [self.rm_term(), self.real_term(1)])
        return Node("fp_from_bv", S, [self.bv_term(1, S.ebits + S.sbits)])

    def _fp_atom(self):
        """An FP atom: a RoundingMode domain atom (=/!= over rounding-mode
        terms, or a Distinct over 3-6 RM vars -- the #P0.2 5-element-domain
        bug class, unsat iff more than 5 pairwise-distinct), an IEEE
        comparison (fp.eq/lt/leq/gt/geq), a classification predicate
        (isNaN/isInfinite/isZero/isNormal/isSubnormal/isNeg/isPos), or a
        structural (dis)equality between FP terms."""
        r = self.rng
        c = r.random()
        if c < 0.15:
            if r.random() < 0.25:
                n = r.randint(3, 6)
                return Node("distinct", SORT_BOOL,
                            [self.var(SORT_RM, max_pool=6) for _ in range(n)])
            op = "=" if r.random() < 0.6 else "!="
            return Node(op, SORT_BOOL, [self.rm_term(), self.rm_term()])
        if c < 0.51:
            op = r.choice(["fp_eq", "fp_lt", "fp_leq", "fp_gt", "fp_geq"])
            return Node(op, SORT_BOOL, [self.fp_term(2), self.fp_term(2)])
        if c < 0.80:
            op = r.choice(["fp_isnan", "fp_isinf", "fp_iszero", "fp_isnormal",
                           "fp_issubnormal", "fp_isneg", "fp_ispos"])
            return Node(op, SORT_BOOL, [self.fp_term(2)])
        op = "=" if r.random() < 0.6 else "!="
        return Node(op, SORT_BOOL, [self.fp_term(2), self.fp_term(2)])


# ---------------------------------------------------------------------------
# Fragment entry points
# ---------------------------------------------------------------------------

# Optional global depth bump. The DEFAULT is 0 (no change), so the original
# fragments regenerate byte-identical trees and existing seeds reproduce. Set
# AYZ3_FUZZ_DEPTH=N to deepen every fragment's term generation by N levels for a
# heavier "deeper terms" campaign. Read once at import for determinism within a
# process.
_DEPTH_BUMP = int(os.environ.get("AYZ3_FUZZ_DEPTH", "0"))


def _gen_qf_lia(rng):
    g = _Gen(rng, "qf_lia", bv_width=0)
    depth = rng.randint(2, 4) + _DEPTH_BUMP
    return g.bool_term(depth, domain="lia")


def _gen_qf_nia(rng):
    """Quantifier-free NONLINEAR integer arithmetic: degree-<=2 polynomials over
    a few Int vars, combined by a small boolean skeleton, with one-sided and
    two-sided bounds. Exercises the NIA capped-model-search completeness path
    (`x*x = k*y`-style unbounded-but-satisfiable queries) added in
    `nia/{bounded_enum,check_loop}.rs`.

    QF_NIA is undecidable in general, so many formulas are `unknown` on one or
    both solvers; the differential comparison's `unknown`->SKIP rule keeps this
    honest — only a real sat-vs-unsat split (DISAGREE) is a soundness finding,
    and every AY `sat` must carry a model the cross-check re-validates (model_BAD).
    """
    g = _Gen(rng, "qf_nia", bv_width=0)

    def poly(depth):
        # A degree-limited integer polynomial. `depth` caps the nesting so the
        # product degree stays small (2-3), keeping z3 mostly-decidable.
        r = rng
        if depth <= 0 or r.random() < 0.4:
            if r.random() < 0.35:
                return Node("intval", SORT_INT, [], r.randint(-4, 6))
            return g.var(SORT_INT, max_pool=3)
        c = r.random()
        if c < 0.30:
            return Node("+", SORT_INT, [poly(depth - 1), poly(depth - 1)])
        if c < 0.50:
            return Node("-", SORT_INT, [poly(depth - 1), poly(depth - 1)])
        if c < 0.80:
            # nonlinear product of two sub-polynomials (the NIA heart)
            return Node("*", SORT_INT, [poly(depth - 1), poly(depth - 1)])
        # linear scaling by a small constant
        return Node("*const", SORT_INT, [poly(depth - 1)], r.randint(-4, 4))

    def atom():
        op = rng.choice(["=", "!=", "<", "<=", ">", ">="])
        return Node(op, SORT_BOOL, [poly(rng.randint(1, 2)), poly(rng.randint(1, 2))])

    # A handful of atoms plus 1-2 one-sided bounds, ANDed (with occasional OR)
    # so the query has the "unbounded box, small witness" shape the search
    # targets.
    natoms = rng.randint(2, 4)
    atoms = [atom() for _ in range(natoms)]
    for _ in range(rng.randint(0, 2)):
        v = g.var(SORT_INT, max_pool=3)
        op = rng.choice([">", ">=", "<", "<="])
        atoms.append(Node(op, SORT_BOOL, [v, Node("intval", SORT_INT, [], rng.randint(-3, 5))]))
    node = atoms[0]
    for a in atoms[1:]:
        connective = "or" if rng.random() < 0.2 else "and"
        node = Node(connective, SORT_BOOL, [node, a])
    return node


def _gen_qf_lra(rng):
    g = _Gen(rng, "qf_lra", bv_width=0)
    depth = rng.randint(2, 4) + _DEPTH_BUMP
    return g.bool_term(depth, domain="lra")


def _gen_qf_bv(rng):
    width = rng.choice([2, 3, 4, 6, 8])
    g = _Gen(rng, "qf_bv", bv_width=width)
    depth = rng.randint(2, 4) + _DEPTH_BUMP
    return g.bool_term(depth, domain="bv", width=width)


def _gen_arrays(rng):
    g = _Gen(rng, "arrays", bv_width=0)
    depth = rng.randint(2, 3) + _DEPTH_BUMP
    return g.bool_term(depth, domain="arr")


# --- broadened coverage: combined / mixed-theory fragments -----------------

def _gen_qf_uflia(rng):
    """UF + LIA: linear integer arithmetic tangled with uninterpreted-function
    applications (congruence + arithmetic must cooperate)."""
    g = _Gen(rng, "qf_uflia", bv_width=0)
    g.use_uf = True
    depth = rng.randint(2, 4) + _DEPTH_BUMP
    return g.bool_term(depth, domain="uflia")


def _gen_arr_lia(rng):
    """Arrays + LIA: select reads wrapped in linear arithmetic on indices and
    values, so the array theory and LIA combine (vs. plain array equalities)."""
    g = _Gen(rng, "arr_lia", bv_width=0)
    depth = rng.randint(2, 3) + _DEPTH_BUMP
    return g.bool_term(depth, domain="arr_lia")


def _gen_qf_bv_bool(rng):
    """BV + Bool: bitvector comparisons under a deeper propositional skeleton
    (and/or/not/implies/xor/ite), with plain boolean variables mixed in."""
    width = rng.choice([2, 3, 4, 6, 8])
    g = _Gen(rng, "qf_bv_bool", bv_width=width)
    # A deeper boolean structure than qf_bv, to stress BV<->Bool interaction.
    depth = rng.randint(3, 5) + _DEPTH_BUMP
    return g.bool_term(depth, domain="bv_bool", width=width)


def _gen_quant_lia(rng):
    """Quantified LIA: a small forall/exists prefix over a linear-int body.

    Bound vars are ordinary declared Int consts (constant-style quantifiers, as
    AY's binding builds them). Decidability is not guaranteed for arbitrary
    quantified LIA, so the comparison's `unknown`->SKIP rule keeps this honest: only
    a real sat-vs-unsat split is a finding.
    """
    g = _Gen(rng, "quant_lia", bv_width=0)
    depth = rng.randint(1, 2) + _DEPTH_BUMP
    body = g.bool_term(depth, domain="lia")
    # Quantify over 1-2 fresh bound Int variables that appear in the body.
    nq = rng.randint(1, 2)
    bound = []
    for k in range(nq):
        bound.append(Node("var", SORT_INT, [], f"q{k}"))
    # Tie the bound vars into the body so the quantifier is meaningful: AND an
    # atom constraining each bound var against an existing int term.
    extra = []
    for bv in bound:
        op = rng.choice(["<", "<=", ">", ">=", "=", "!="])
        extra.append(Node(op, SORT_BOOL, [bv, g.int_term(1)]))
    full_body = Node("and", SORT_BOOL, [body] + extra)
    op = "forall" if rng.random() < 0.5 else "exists"
    return Node(op, SORT_BOOL, bound + [full_body])


def _gen_quant_lra_isint(rng):
    """Quantified LRA with `is_int` over the bound Real variable.

    The bound Real var `qx` occurs in 1-4 `is_int(qx + c)` atoms (random
    rational offsets `c`), combined by a small and/or/not skeleton, optionally
    conjoined with x-FREE linear-real side constraints over other Real vars.
    Occasionally `qx` also escapes into a plain LRA atom (deliberately OUT of
    the dedicated `is_int` eliminator's fragment) so both the deciding and the
    fail-closing paths of `qe/isint.rs` are exercised. Quantified LRA+is_int is
    not universally decidable, so the differential comparison's `unknown`->SKIP rule
    keeps this honest: only a real sat-vs-unsat split is a soundness finding.
    """
    g = _Gen(rng, "quant_lra_isint", bv_width=0)
    x = Node("var", SORT_REAL, [], "qx")
    natoms = rng.randint(1, 4)
    # ~30% of formulas SHADOW `is_int`: emit it as a user uninterpreted function
    # `(declare-fun is_int (Real) Bool)` (a plain "app" over a `FuncSig`,
    # rendered as `m.Function("is_int", RealSort(), BoolSort())` on BOTH modules)
    # instead of the builtin integrality predicate. z3 and AY both treat the UF
    # as a free predicate, so the whole formula is genuinely uninterpreted and
    # the dedicated `is_int` quantifier eliminator (`qe/isint.rs`) MUST stand
    # down (fail-closed) rather than forge integrality semantics — the exact
    # wrong-UNSAT this guards. Without this the fragment only ever generates the
    # builtin `m.IsInt` and structurally cannot reach the shadow defect
    # (#isint-shadow coverage blind spot). The differential comparison is the gate:
    # a shadowed formula that AY decides `unsat` where z3 is `sat` is a DISAGREE.
    shadow_isint = rng.random() < 0.3
    isint_sig = FuncSig("is_int", (SORT_REAL,), SORT_BOOL)
    lits = []
    for _ in range(natoms):
        num = rng.randint(-4, 4)
        den = rng.choice([1, 2, 3, 4])
        if num == 0:
            arg = x
        else:
            c = Node("realval", SORT_REAL, [], (num, den))
            arg = Node("+", SORT_REAL, [x, c])
        if shadow_isint:
            atom = Node("app", SORT_BOOL, [arg], isint_sig)
        else:
            atom = Node("is_int", SORT_BOOL, [arg])
        if rng.random() < 0.3:
            atom = Node("not", SORT_BOOL, [atom])
        lits.append(atom)
    # Optional x-free LRA side constraint (over other Real vars from the pool).
    if rng.random() < 0.5:
        lits.append(g._arith_atom(g.real_term, SORT_REAL))
    # Occasionally let `qx` escape into a plain LRA atom (fail-close path).
    if rng.random() < 0.25:
        bound = Node("realval", SORT_REAL, [], (rng.randint(-3, 3), 1))
        lits.append(Node(rng.choice(["<", "<=", ">", ">="]), SORT_BOOL, [x, bound]))
    rng.shuffle(lits)
    body = lits[0]
    for lit in lits[1:]:
        body = Node(rng.choice(["and", "or"]), SORT_BOOL, [body, lit])
    op = "forall" if rng.random() < 0.5 else "exists"
    return Node(op, SORT_BOOL, [x, body])


# --- datatypes --------------------------------------------------------------
# ayz3 now exposes the z3py-style algebraic `Datatype` builder (EnumSort /
# TupleSort / Datatype.declare/.create, with constructor / accessor / recognizer
# decls), wired onto AY's verified datatype theory. z3py exposes the identical
# surface, so a datatype declaration + its terms render IDENTICALLY on both
# modules and the differential soundness comparison is valid.

def _datatypes_supported():
    """Datatypes need the z3py-style `Datatype` builder on BOTH modules. ayz3
    now exposes it (see ayz3/datatypes.py); z3py always has it. We gate on ayz3
    since z3 is a hard dependency of the differential run."""
    try:
        import ayz3
    except Exception:
        return False
    return all(hasattr(ayz3, nm) for nm in ("Datatype", "EnumSort", "Const"))


def _make_dt_spec(rng):
    """Pick ONE simple, well-typed datatype family for a formula (deterministic
    per `rng`). Each has a small, fixed constructor/field shape with stable SMT
    identifiers so the SAME declaration replays on ayz3 and z3. Recursive
    families (list/tree) always include a nullary base constructor so term
    generation terminates."""
    fam = rng.choice(["enum", "option", "pair", "record", "list", "tree"])
    if fam == "enum":
        n = rng.randint(2, 4)
        names = ["red", "green", "blue", "amber"][:n]
        return DTSpec("Color", [DTCtor(nm, []) for nm in names])
    if fam == "option":
        return DTSpec("Opt", [DTCtor("some", [("val", SORT_INT)]),
                              DTCtor("none", [])])
    if fam == "pair":
        return DTSpec("Pair", [DTCtor("mk", [("fst", SORT_INT),
                                             ("snd", SORT_INT)])])
    if fam == "record":
        return DTSpec("Rec", [DTCtor("rec", [("ra", SORT_INT),
                                             ("rb", SORT_INT),
                                             ("rc", SORT_BOOL)])])
    if fam == "list":
        return DTSpec("Lst", [DTCtor("cons", [("hd", SORT_INT), ("tl", DT_SELF)]),
                              DTCtor("nil", [])])
    # tree
    return DTSpec("Tree", [DTCtor("node", [("lt", DT_SELF), ("v", SORT_INT),
                                           ("rt", DT_SELF)]),
                           DTCtor("leaf", [])])


def _gen_datatypes(rng):
    """Quantifier-free algebraic-datatype formulas (decidable, so a sat-vs-unsat
    split is a real wrong answer). One datatype is declared per formula and terms
    are built over reused datatype/int vars: constructor apps, accessors,
    testers, (dis)equalities and accessor-vs-linear-int comparisons, wrapped in a
    boolean skeleton. Exercises constructor injectivity, accessor semantics,
    tester disjointness/exhaustiveness and cross-constructor distinctness."""
    g = _Gen(rng, "datatypes", bv_width=0)
    g.dt_spec = _make_dt_spec(rng)
    g.use_dt = True
    depth = rng.randint(2, 3) + _DEPTH_BUMP
    return g.bool_term(depth, domain="datatypes")


# --- sequences --------------------------------------------------------------
# Quantifier-free (Seq Int) / (Seq Bool) formulas over AY's non-string sequence
# theory -- exactly where the recent 5 wrong-verdict soundness bugs lived. AY's
# in-memory ayz3 seq builders accept only the String sort, so this fragment is
# rendered to canonical SMT-LIB (by z3py) and checked through `from_string` on
# BOTH modules (see `differential.SMT2_FRAGMENTS`); the identical text keeps the
# comparison faithful while exercising the genuine (Seq Int)/(Seq Bool) decision
# procedure. Covers seq.++/len/unit/empty/nth/at/extract/contains/prefixof/
# suffixof/indexof/replace, (dis)equalities, the extract-whole / at-nth-linkage /
# contains-chain bug shapes, and Int constraints on seq.len.

def _sequences_supported():
    """The sequences fragment needs z3py's seq builders (reference renderer) and
    ayz3's SMT-LIB parser (the check path). z3 is a hard dependency of the run;
    we gate on ayz3 exposing the seq surface + a `from_string` solver."""
    try:
        import ayz3
    except Exception:
        return False
    if not all(hasattr(ayz3, nm) for nm in
               ("SeqSort", "Concat", "Length", "Contains", "Const")):
        return False
    return hasattr(ayz3, "Solver") and hasattr(ayz3.Solver, "from_string")


def _gen_sequences(rng):
    """One quantifier-free sequence formula over a single element sort ((Seq Int)
    or (Seq Bool)) with reused seq/int vars and a boolean skeleton."""
    g = _Gen(rng, "sequences", bv_width=0)
    g.seq_elem = rng.choice([SORT_INT, SORT_BOOL])
    g.use_seq = True
    depth = rng.randint(2, 3) + _DEPTH_BUMP
    return g.bool_term(depth, domain="sequences")


# --- floating point ---------------------------------------------------------
# Quantifier-free Float32/Float64 formulas over fp.add/sub/mul/div/sqrt/fma/
# roundToIntegral (with BOTH literal rounding modes RNE/RNA/RTP/RTN/RTZ and
# declared SYMBOLIC RoundingMode vars -- the RoundingMode bug class), the IEEE
# comparisons/classification predicates, to_fp from real/bv, and the special
# values NaN/+oo/-oo/+0/-0 over reused FP vars. FP builds identically in-memory
# on both modules, so this fragment uses the ordinary build path.

def _qf_fp_supported():
    """qf_fp needs ayz3's z3py-style FP surface (z3py always has it)."""
    try:
        import ayz3
    except Exception:
        return False
    return all(hasattr(ayz3, nm) for nm in
               ("FPSort", "Float32", "Float64", "FP", "FPVal", "RNE",
                "fpAdd", "fpSub", "fpMul", "fpDiv", "fpSqrt", "fpFMA",
                "fpRoundToIntegral", "fpEQ", "fpLT", "fpIsNaN", "fpIsInf",
                "fpIsZero", "fpIsNormal", "fpToFP", "fpNaN"))


def _gen_qf_fp(rng):
    """One quantifier-free floating-point formula over a single IEEE format."""
    g = _Gen(rng, "qf_fp", bv_width=0)
    g.use_fp = True
    eb, sb = rng.choice([(8, 24), (11, 53)])  # Float32 / Float64
    g.fp_sort = FPSortTag(eb, sb)
    depth = rng.randint(2, 3) + _DEPTH_BUMP
    return g.bool_term(depth, domain="qf_fp")


# --- recursive function definitions ----------------------------------------
# RecFunction/RecAddDefinition differential coverage (P1.1): linear recursion,
# triangular sums, factorial, mutual even/odd pairs, 0-ary defs, and BOTH
# definition orders (define-then-use and the z3py build-apps-then-define
# idiom). Ground probes are half true-fact / half perturbed wrong-fact, so
# roughly half the formulas are unsat and a wrong verdict in EITHER direction
# is caught. Occasional bounded symbolic-argument probes exercise AY's
# fail-closed residual path: AY answers `unknown` there (SKIP), and the comparison
# guarantees it never disagrees with a z3 verdict it does decide against.
#
# Names are made unique per case (rng-derived 48-bit tag) because real z3's
# rec-def registry is context-global for the process: reusing a name across
# cases with a different body would either error or silently apply a STALE
# definition — a fuzzer artifact, not a solver verdict.

def _recfun_supported():
    """The recfun fragment needs ayz3's RecFunction surface (z3py always has
    it). Gate like datatypes/sequences so `--fragment all` on a stripped build
    skips cleanly."""
    try:
        import ayz3
    except Exception:
        return False
    return all(hasattr(ayz3, nm) for nm in ("RecFunction", "RecAddDefinition"))


def _iv(v):
    return Node("intval", SORT_INT, [], v)


def _gen_recfun(rng):
    """One formula over 1-2 recursively defined functions (see block comment)."""
    uid = f"{rng.getrandbits(48):012x}"
    shape = rng.choice(["linear", "sum", "fact", "mutual", "zeroary",
                        "builtin_shadow"])
    order = rng.choice(["def_first", "def_after"])

    if shape == "builtin_shadow":
        # Skeptic reproducer class: a rec def whose NAME is a builtin
        # operator. AY rejects the definition (swallowed in _rec_define); z3
        # accepts a NOMINAL recfun that never touches its builtin. The
        # formula probes ONLY builtin arithmetic ground facts, so any
        # regression to silent acceptance-and-corruption (the '+':='*'
        # wrong-sat) flips a verdict and the comparison reports DISAGREE.
        opname = rng.choice(["+", "-", "*"])
        x = Node("var", SORT_INT, [], "rx")
        y = Node("var", SORT_INT, [], "ry")
        # A body DIFFERENT from the builtin so corruption would flip facts.
        wrong_op = {"+": "*", "-": "+", "*": "-"}[opname]
        spec = RecSpec(opname, [("rx", SORT_INT), ("ry", SORT_INT)], SORT_INT,
                       Node(wrong_op, SORT_INT, [x, y]))
        a = rng.randint(-9, 9)
        b = rng.randint(-9, 9)
        truth = {"+": a + b, "-": a - b, "*": a * b}[opname]
        target = truth if rng.random() < 0.5 else truth + rng.choice([1, -1, 2])
        av = Node("var", SORT_INT, [], f"ba{uid}")
        bv = Node("var", SORT_INT, [], f"bb{uid}")
        formula = Node("and", SORT_BOOL, [
            Node("=", SORT_BOOL, [av, _iv(a)]),
            Node("=", SORT_BOOL, [bv, _iv(b)]),
            Node("=", SORT_BOOL,
                 [Node(opname, SORT_INT, [av, bv]), _iv(target)]),
        ])
        return Node("recgroup", SORT_BOOL, [formula], ((spec,), order))

    if shape == "mutual":
        evn, odn = f"ev{uid}", f"od{uid}"
        x = Node("var", SORT_INT, [], "rx")
        sig = ((SORT_INT,), SORT_BOOL)

        def evapp(a):
            return Node("recapp", SORT_BOOL, [a], (evn,) + sig)

        def odapp(a):
            return Node("recapp", SORT_BOOL, [a], (odn,) + sig)

        ev_body = Node("ite", SORT_BOOL,
                       [Node("<=", SORT_BOOL, [x, _iv(0)]),
                        Node("boolval", SORT_BOOL, [], True),
                        odapp(Node("-", SORT_INT, [x, _iv(1)]))])
        od_body = Node("ite", SORT_BOOL,
                       [Node("<=", SORT_BOOL, [x, _iv(0)]),
                        Node("boolval", SORT_BOOL, [], False),
                        evapp(Node("-", SORT_INT, [x, _iv(1)]))])
        specs = (RecSpec(evn, [("rx", SORT_INT)], SORT_BOOL, ev_body),
                 RecSpec(odn, [("rx", SORT_INT)], SORT_BOOL, od_body))
        conj = []
        for _ in range(rng.randint(1, 3)):
            k = rng.randint(0, 9)
            pick_ev = rng.random() < 0.5
            app = evapp(_iv(k)) if pick_ev else odapp(_iv(k))
            truth = (k % 2 == 0) if pick_ev else (k % 2 == 1)
            claim = truth if rng.random() < 0.5 else not truth  # wrong-fact half
            conj.append(app if claim else Node("not", SORT_BOOL, [app]))
        formula = conj[0] if len(conj) == 1 else Node("and", SORT_BOOL, conj)
        return Node("recgroup", SORT_BOOL, [formula], (specs, order))

    if shape == "zeroary":
        name = f"rc{uid}"
        v0 = rng.randint(-20, 20)
        spec = RecSpec(name, [], SORT_INT, _iv(v0))
        app = Node("recapp", SORT_INT, [], (name, (), SORT_INT))
        conj = []
        for _ in range(rng.randint(1, 2)):
            tv = v0 if rng.random() < 0.5 else v0 + rng.choice([1, -1, 2, 5])
            op = rng.choice(["=", "=", "<=", ">"])
            conj.append(Node(op, SORT_BOOL, [app, _iv(tv)]))
        formula = conj[0] if len(conj) == 1 else Node("and", SORT_BOOL, conj)
        return Node("recgroup", SORT_BOOL, [formula], ((spec,), order))

    # Int -> Int single recursion: linear / triangular sum / factorial.
    name = f"rf{uid}"
    x = Node("var", SORT_INT, [], "rx")

    def fapp(a):
        return Node("recapp", SORT_INT, [a], (name, (SORT_INT,), SORT_INT))

    xm = lambda d: Node("-", SORT_INT, [x, _iv(d)])
    if shape == "linear":
        b, c, d = rng.randint(-3, 3), rng.randint(1, 4), rng.randint(1, 3)
        body = Node("ite", SORT_INT,
                    [Node("<=", SORT_BOOL, [x, _iv(0)]), _iv(b),
                     Node("+", SORT_INT, [_iv(c), fapp(xm(d))])])

        def val(k):
            acc = 0
            while k > 0:
                acc += c
                k -= d
            return acc + b
        kmax = 8
    elif shape == "sum":
        body = Node("ite", SORT_INT,
                    [Node("<=", SORT_BOOL, [x, _iv(0)]), _iv(0),
                     Node("+", SORT_INT, [x, fapp(xm(1))])])

        def val(k):
            return k * (k + 1) // 2 if k > 0 else 0
        kmax = 8
    else:  # fact
        body = Node("ite", SORT_INT,
                    [Node("<=", SORT_BOOL, [x, _iv(1)]), _iv(1),
                     Node("*", SORT_INT, [x, fapp(xm(1))])])

        def val(k):
            out = 1
            while k > 1:
                out *= k
                k -= 1
            return out
        kmax = 6

    spec = RecSpec(name, [("rx", SORT_INT)], SORT_INT, body)
    conj = []
    for i in range(rng.randint(1, 3)):
        k = rng.randint(0, kmax)
        v = val(k)
        app = fapp(_iv(k))
        style = rng.random()
        if style < 0.45:
            # Direct ground fact, half perturbed (wrong-fact probe).
            tv = v if rng.random() < 0.5 else v + rng.choice([1, -1, 2, 5])
            conj.append(Node("=", SORT_BOOL, [app, _iv(tv)]))
        elif style < 0.75:
            # Free-var linkage y == f(k): puts f's value INTO the model, so
            # the cross-check's model pin (CAT_B detection) covers rec expansion.
            y = Node("var", SORT_INT, [], f"ry{i}")
            w = v if rng.random() < 0.5 else v + rng.choice([1, -1, 3])
            conj.append(Node("and", SORT_BOOL, [
                Node("=", SORT_BOOL, [y, app]),
                Node(rng.choice(["=", "<=", ">="]), SORT_BOOL, [y, _iv(w)])]))
        else:
            # Inequality probe around the true value.
            conj.append(Node(rng.choice(["<", "<=", ">", ">="]), SORT_BOOL,
                             [app, _iv(v + rng.randint(-2, 2))]))
    if rng.random() < 0.10:
        # Bounded SYMBOLIC argument: AY fail-closes to unknown (SKIP); z3
        # usually decides. The comparison flags any AY disagreement.
        nv = Node("var", SORT_INT, [], "rn")
        reachable = rng.random() < 0.5
        tk = rng.randint(0, 3)
        target = val(tk) if reachable else max(val(j) for j in range(4)) + 1
        conj.append(Node("and", SORT_BOOL, [
            Node(">=", SORT_BOOL, [nv, _iv(0)]),
            Node("<=", SORT_BOOL, [nv, _iv(3)]),
            Node("=", SORT_BOOL, [fapp(nv), _iv(target)])]))
    formula = conj[0] if len(conj) == 1 else Node("and", SORT_BOOL, conj)
    return Node("recgroup", SORT_BOOL, [formula], ((spec,), order))


FRAGMENTS = {
    "qf_lia": _gen_qf_lia,
    "qf_nia": _gen_qf_nia,
    "qf_lra": _gen_qf_lra,
    "qf_bv": _gen_qf_bv,
    "arrays": _gen_arrays,
    # Broadened, combined-theory / quantified fragments:
    "qf_uflia": _gen_qf_uflia,
    "arr_lia": _gen_arr_lia,
    "qf_bv_bool": _gen_qf_bv_bool,
    "quant_lia": _gen_quant_lia,
    "quant_lra_isint": _gen_quant_lra_isint,
}

# Sequences + floating point: theory fragments for the sequence and FP decision
# procedures. Registered only when ayz3 exposes the necessary surface (like the
# datatypes support gate), so `--fragment all` on a stripped build skips them
# cleanly instead of crashing.
if _sequences_supported():
    FRAGMENTS["sequences"] = _gen_sequences
if _qf_fp_supported():
    FRAGMENTS["qf_fp"] = _gen_qf_fp
# Recursive function definitions (RecFunction/RecAddDefinition, P1.1): gated on
# ayz3 exposing the rec surface, like the sequences/qf_fp gates above.
if _recfun_supported():
    FRAGMENTS["recfun"] = _gen_recfun

# Fragments whose formulas are checked by rendering to canonical SMT-LIB and
# parsing the SAME text through BOTH modules (`from_string`), rather than the
# in-memory term builder. The `sequences` fragment uses this because AY's
# in-memory ayz3 seq builders accept only the String sort, while its SMT-LIB
# parser handles the genuine (Seq Int)/(Seq Bool) theory that had the bugs.
# The identical text guarantees both modules decide the identical formula.
SMT2_FRAGMENTS = {"sequences"}

# `datatypes` is deliberately NOT registered: ayz3 now has a real `Datatype`
# builder, but `_gen_datatypes` is an unimplemented placeholder — registering
# it would make `--fragment all` runs crash on its NotImplementedError instead
# of skipping the fragment. Register it here once it generates real formulas.


def generate(fragment: str, seed: int) -> Node:
    """Deterministically generate one formula (a Bool `Node`) for `fragment`.

    The same (fragment, seed) always yields the identical tree.
    """
    if fragment not in FRAGMENTS:
        raise ValueError(f"unknown fragment {fragment!r}; choose from {sorted(FRAGMENTS)}")
    # Seed deterministically from the (fragment, seed) pair so a single
    # (fragment, seed) regenerates the identical tree across processes.
    rng = random.Random()
    rng.seed(f"{fragment}:{seed}")
    return FRAGMENTS[fragment](rng)
