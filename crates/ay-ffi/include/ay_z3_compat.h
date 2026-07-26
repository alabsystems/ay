// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// AY Z3-Compatible C API Header
//
// Drop-in replacement for a subset of z3.h (Z3 C API).
// Link against libay_ffi (cdylib or staticlib) to use.
//
// Functions covering: context, solver, sorts, terms, arithmetic,
// bitvectors, arrays, quantifiers, model, AST inspection, error handling,
// and parsing.

#ifndef AY_Z3_COMPAT_H
#define AY_Z3_COMPAT_H

#include <stdbool.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

// ============================================================================
// Opaque Types
// ============================================================================

typedef void* Z3_context;
typedef void* Z3_config;
typedef void* Z3_sort;
typedef void* Z3_func_decl;
typedef void* Z3_solver;
typedef void* Z3_optimize;
typedef void* Z3_fixedpoint;
typedef void* Z3_tactic;
typedef void* Z3_simplifier;
typedef void* Z3_goal;
typedef void* Z3_apply_result;
typedef void* Z3_probe;
typedef void* Z3_model;
typedef void* Z3_func_interp;
typedef void* Z3_func_entry;
typedef void* Z3_symbol;
typedef void* Z3_params;
typedef void* Z3_param_descrs;
typedef void* Z3_stats;
typedef void* Z3_ast_vector;
typedef void* Z3_ast_map;
typedef void* Z3_pattern;
typedef void* Z3_constructor;
typedef void* Z3_constructor_list;
typedef void* Z3_parser_context;

// Model-event handler callback (Z3_optimize_register_model_eh). AY never invokes
// it (honest no-op; see the optimize section) but the type is declared for
// source compatibility.
typedef void (*Z3_model_eh)(void* ctx);

// Z3_ast is a 64-bit handle (not a pointer)
typedef uint64_t Z3_ast;
// An application AST. In z3 `Z3_app` is a subtype of `Z3_ast`; here it is the
// same 64-bit handle, so `Z3_to_app`/`Z3_mk_*_const` interoperate with `Z3_ast`
// exactly as a consumer expects.
typedef Z3_ast Z3_app;
// Opaque exact real-closed-field numeral handle (z3_rcf.h surface).
typedef void* Z3_rcf_num;

// Z3 string type
typedef const char* Z3_string;
typedef const char* Z3_char_ptr;

// ============================================================================
// Constants
// ============================================================================

// Z3_lbool
#define Z3_L_FALSE (-1)
#define Z3_L_UNDEF 0
#define Z3_L_TRUE  1

// Z3_sort_kind
#define Z3_BOOL_SORT          1
#define Z3_INT_SORT           2
#define Z3_REAL_SORT          3
#define Z3_BV_SORT            4
#define Z3_ARRAY_SORT         5
// Z3 API values (verified vs z3py 4.15.4): Z3_UNINTERPRETED_SORT is 0 (6 is
// Z3_DATATYPE_SORT) and Z3_SEQ_SORT is 11 (7 is Z3_RELATION_SORT).
#define Z3_UNINTERPRETED_SORT 0
// An algebraic datatype (declare-datatypes / Z3_mk_datatype) reports
// Z3_DATATYPE_SORT.
#define Z3_DATATYPE_SORT      6
// A String is a sequence (of characters) in Z3's model, so Z3_get_sort_kind
// reports Z3_SEQ_SORT for both (Seq T) and the String sort.
#define Z3_SEQ_SORT           11
// The Unicode character sort: the basis of the String sort
// (Z3_get_seq_sort_basis) and what Z3_is_char_sort accepts.
#define Z3_CHAR_SORT          13

// Z3_ast_kind
#define Z3_NUMERAL_AST    0
#define Z3_APP_AST        1
#define Z3_VAR_AST        2
#define Z3_QUANTIFIER_AST 3
#define Z3_UNKNOWN_AST    1000

// Z3_symbol_kind
#define Z3_INT_SYMBOL    0
#define Z3_STRING_SYMBOL 1

// Z3_error_code
#define Z3_OK               0
#define Z3_SORT_ERROR       1
#define Z3_IOB              2
#define Z3_INVALID_ARG      3
#define Z3_PARSER_ERROR     4
#define Z3_NO_PARSER        5
#define Z3_INVALID_PATTERN  6
#define Z3_MEMOUT_FAIL      7
#define Z3_FILE_ACCESS_ERROR 8
#define Z3_INTERNAL_FATAL   9
#define Z3_INVALID_USAGE    10
#define Z3_DEC_REF_ERROR    11
#define Z3_EXCEPTION        12
// z3 declares `Z3_error_code` as an enum of the codes above; the values are
// identical, so an `unsigned` alias lets the same consumer source compile and
// interoperate with `Z3_get_error_code` (which returns these values).
typedef unsigned Z3_error_code;
// Error-handler callback shape (Z3_set_error_handler).
typedef void (*Z3_error_handler)(Z3_context c, Z3_error_code e);

// Z3_param_kind (matches z3_api.h enum ordering). In twin mode these names come
// from z3.h's enum; here they are plain macros so the same consumer source
// compiles against both.
#ifndef AY_TWIN_USE_Z3
#define Z3_PK_UINT    0
#define Z3_PK_BOOL    1
#define Z3_PK_DOUBLE  2
#define Z3_PK_SYMBOL  3
#define Z3_PK_STRING  4
#define Z3_PK_OTHER   5
#define Z3_PK_INVALID 6
#endif

// Z3_parameter_kind (matches z3_api.h enum ordering, verified vs z3 4.15.4).
// Classifies a function declaration's indexed parameters
// (Z3_get_decl_parameter_kind). AY produces only integer indexed parameters, so
// that accessor always returns Z3_PARAMETER_INT; the rest are declared for
// completeness. In twin mode these come from z3.h's enum.
#ifndef AY_TWIN_USE_Z3
#define Z3_PARAMETER_INT       0
#define Z3_PARAMETER_DOUBLE    1
#define Z3_PARAMETER_RATIONAL  2
#define Z3_PARAMETER_SYMBOL    3
#define Z3_PARAMETER_SORT      4
#define Z3_PARAMETER_AST       5
#define Z3_PARAMETER_FUNC_DECL 6
#endif

// ============================================================================
// Config & Context
// ============================================================================

Z3_config    Z3_mk_config(void);
void         Z3_del_config(Z3_config c);
void         Z3_set_param_value(Z3_config c, Z3_string param_id, Z3_string param_value);
Z3_context   Z3_mk_context(Z3_config c);
Z3_context   Z3_mk_context_rc(Z3_config c);
void         Z3_del_context(Z3_context c);
// Apply a per-context runtime/frontend option. timeout=0 means no deadline.
// Successful updates retire copied Solver/Optimize result artifacts.
void         Z3_update_param_value(Z3_context c, Z3_string param_id,
                                   Z3_string param_value);

// ============================================================================
// Version
// ============================================================================

void Z3_get_version(unsigned int* major, unsigned int* minor,
                    unsigned int* build_number, unsigned int* revision_number);
// Human-readable version string, e.g. "AY <ver> (Z3 5.0.0.0 compatible)".
// Owned by the library; valid for the program lifetime.
Z3_string    Z3_get_full_version(void);

// ============================================================================
// Global Parameters
// ============================================================================
//
// AY has no process-global parameters (all config is per-solver), so these are
// sound no-ops mirroring Z3's "unknown global params are silently ignored".

void         Z3_global_param_set(Z3_string param_id, Z3_string param_value);
void         Z3_global_param_reset_all(void);

// ============================================================================
// Reference Counting (no-op in AY)
// ============================================================================

void Z3_inc_ref(Z3_context c, Z3_ast a);
void Z3_dec_ref(Z3_context c, Z3_ast a);

// ============================================================================
// Interrupt
// ============================================================================

void Z3_interrupt(Z3_context c);

// ============================================================================
// Symbols
// ============================================================================

Z3_symbol    Z3_mk_int_symbol(Z3_context c, int i);
Z3_symbol    Z3_mk_string_symbol(Z3_context c, Z3_string s);
Z3_string    Z3_get_symbol_string(Z3_context c, Z3_symbol s);
unsigned int Z3_get_symbol_kind(Z3_context c, Z3_symbol s);
int          Z3_get_symbol_int(Z3_context c, Z3_symbol s);

// ============================================================================
// Sorts
// ============================================================================

Z3_sort      Z3_mk_bool_sort(Z3_context c);
Z3_sort      Z3_mk_int_sort(Z3_context c);
Z3_sort      Z3_mk_real_sort(Z3_context c);
Z3_sort      Z3_mk_bv_sort(Z3_context c, unsigned int sz);
Z3_sort      Z3_mk_array_sort(Z3_context c, Z3_sort domain, Z3_sort range);
Z3_sort      Z3_mk_uninterpreted_sort(Z3_context c, Z3_symbol s);
Z3_sort      Z3_mk_seq_sort(Z3_context c, Z3_sort elem);
Z3_sort      Z3_mk_re_sort(Z3_context c, Z3_sort basis);
Z3_sort      Z3_mk_string_sort(Z3_context c);
unsigned int Z3_get_sort_kind(Z3_context c, Z3_sort t);
unsigned int Z3_get_bv_sort_size(Z3_context c, Z3_sort t);
Z3_sort      Z3_get_array_sort_domain(Z3_context c, Z3_sort t);
Z3_sort      Z3_get_array_sort_range(Z3_context c, Z3_sort t);
Z3_string    Z3_sort_to_string(Z3_context c, Z3_sort s);
Z3_symbol    Z3_get_sort_name(Z3_context c, Z3_sort s);
bool         Z3_is_eq_sort(Z3_context c, Z3_sort s1, Z3_sort s2);
bool         Z3_is_char_sort(Z3_context c, Z3_sort s);
unsigned int Z3_get_sort_id(Z3_context c, Z3_sort s);

// Sort structure getters (group A). AY canonicalizes n-domain arrays to the
// curried SMT-LIB form (Array D0 (Array D1 ... R)): Z3_mk_array_sort_n builds
// that nesting, Z3_get_array_arity reports the full curried depth (2 for the
// example — agreeing with libz3 for mk_array_sort_n-built sorts; a hand-nested
// array-of-array reports its depth too, where libz3 reports 1), and
// Z3_get_array_sort_domain_n walks the curried domains. Z3_get_seq_sort_basis
// of (Seq T) is T; on the String sort it is the Char sort (Z3_CHAR_SORT), the
// same answer libz3 gives. Z3_get_re_sort_basis is the String sort (AY regexes
// are string regexes, the only regex domain AY supports).
// Z3_get_finite_domain_sort_size stores the cardinality of a sort built by
// Z3_mk_finite_domain_sort and returns true; for any other sort it stores 0 and
// returns false, matching libz3 (which also zeroes the out-param on failure).
Z3_sort      Z3_mk_array_sort_n(Z3_context c, unsigned int n, const Z3_sort* domain,
                                Z3_sort range);
unsigned int Z3_get_array_arity(Z3_context c, Z3_sort s);
Z3_sort      Z3_get_array_sort_domain_n(Z3_context c, Z3_sort t, unsigned int idx);
Z3_sort      Z3_get_seq_sort_basis(Z3_context c, Z3_sort s);
Z3_sort      Z3_get_re_sort_basis(Z3_context c, Z3_sort s);
bool         Z3_get_finite_domain_sort_size(Z3_context c, Z3_sort s, uint64_t* r);

// ============================================================================
// Terms: Constants, Functions, Numerals, Boolean
// ============================================================================

Z3_func_decl Z3_mk_func_decl(Z3_context c, Z3_symbol s, unsigned int domain_size,
                             const Z3_sort* domain, Z3_sort range);
// Install a durable defining equation for `f`. The axiom is context-global
// declaration semantics and is replayed by every Solver/Optimize check after
// handle-local goal reloads. Adding it retires all copied decision artifacts.
// A non-zero n requires a non-null args array; rejection is transactional.
void         Z3_add_rec_def(Z3_context c, Z3_func_decl f, unsigned int n,
                            const Z3_ast* args, Z3_ast body);
Z3_ast       Z3_mk_const(Z3_context c, Z3_symbol s, Z3_sort ty);
Z3_ast       Z3_mk_fresh_const(Z3_context c, Z3_string prefix, Z3_sort ty);
Z3_ast       Z3_mk_app(Z3_context c, Z3_func_decl d, unsigned int num_args,
                        const Z3_ast* args);
// Same-context is an identity. Cross-context deep copy is rejected when the
// source owns context-resident semantic metadata (background/range/order
// axioms, recursive definitions, or transitive-closure verifier state), since
// the term-DAG graft alone cannot transfer those obligations soundly.
Z3_ast       Z3_translate(Z3_context source, Z3_ast a, Z3_context target);

Z3_ast       Z3_mk_numeral(Z3_context c, Z3_string numeral, Z3_sort ty);
Z3_ast       Z3_mk_int(Z3_context c, int v, Z3_sort ty);
Z3_ast       Z3_mk_unsigned_int(Z3_context c, unsigned int v, Z3_sort ty);
Z3_ast       Z3_mk_int64(Z3_context c, int64_t v, Z3_sort ty);
Z3_ast       Z3_mk_unsigned_int64(Z3_context c, uint64_t v, Z3_sort ty);
Z3_ast       Z3_mk_real(Z3_context c, int num, int den);

Z3_ast       Z3_mk_true(Z3_context c);
Z3_ast       Z3_mk_false(Z3_context c);
Z3_ast       Z3_mk_eq(Z3_context c, Z3_ast l, Z3_ast r);
Z3_ast       Z3_mk_distinct(Z3_context c, unsigned int num_args, const Z3_ast* args);
Z3_ast       Z3_mk_not(Z3_context c, Z3_ast a);
Z3_ast       Z3_mk_ite(Z3_context c, Z3_ast t1, Z3_ast t2, Z3_ast t3);
Z3_ast       Z3_mk_iff(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast       Z3_mk_implies(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast       Z3_mk_xor(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast       Z3_mk_and(Z3_context c, unsigned int num_args, const Z3_ast* args);
Z3_ast       Z3_mk_or(Z3_context c, unsigned int num_args, const Z3_ast* args);

// ============================================================================
// Arithmetic
// ============================================================================

Z3_ast       Z3_mk_add(Z3_context c, unsigned int num_args, const Z3_ast* args);
Z3_ast       Z3_mk_mul(Z3_context c, unsigned int num_args, const Z3_ast* args);
Z3_ast       Z3_mk_sub(Z3_context c, unsigned int num_args, const Z3_ast* args);
Z3_ast       Z3_mk_unary_minus(Z3_context c, Z3_ast arg);
Z3_ast       Z3_mk_div(Z3_context c, Z3_ast arg1, Z3_ast arg2);
Z3_ast       Z3_mk_mod(Z3_context c, Z3_ast arg1, Z3_ast arg2);
Z3_ast       Z3_mk_rem(Z3_context c, Z3_ast arg1, Z3_ast arg2);
Z3_ast       Z3_mk_abs(Z3_context c, Z3_ast arg);
Z3_ast       Z3_mk_power(Z3_context c, Z3_ast arg1, Z3_ast arg2);

Z3_ast       Z3_mk_lt(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast       Z3_mk_le(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast       Z3_mk_gt(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast       Z3_mk_ge(Z3_context c, Z3_ast t1, Z3_ast t2);

Z3_ast       Z3_mk_int2real(Z3_context c, Z3_ast t1);
Z3_ast       Z3_mk_real2int(Z3_context c, Z3_ast t1);
Z3_ast       Z3_mk_is_int(Z3_context c, Z3_ast t1);

// ============================================================================
// Arrays
// ============================================================================

Z3_ast       Z3_mk_select(Z3_context c, Z3_ast a, Z3_ast i);
Z3_ast       Z3_mk_store(Z3_context c, Z3_ast a, Z3_ast i, Z3_ast v);
Z3_ast       Z3_mk_const_array(Z3_context c, Z3_sort domain, Z3_ast v);

// ============================================================================
// Sets (modelled as (Array elem Bool), matching Z3)
// ============================================================================
//
// Z3 models (Set T) as (Array T Bool). The pointwise set operations
// (union/intersect/complement/...) are intentionally omitted: AY has no
// pointwise array combinator, so no sound mapping exists.

Z3_sort      Z3_mk_set_sort(Z3_context c, Z3_sort elem);
Z3_ast       Z3_mk_empty_set(Z3_context c, Z3_sort domain);
Z3_ast       Z3_mk_full_set(Z3_context c, Z3_sort domain);
Z3_ast       Z3_mk_set_add(Z3_context c, Z3_ast set, Z3_ast elem);
Z3_ast       Z3_mk_set_del(Z3_context c, Z3_ast set, Z3_ast elem);
Z3_ast       Z3_mk_set_member(Z3_context c, Z3_ast elem, Z3_ast set);
// Cardinality predicate |set| = k (k Int-sorted). Finite element domains AY
// can enumerate (Bool, BitVec w <= 8) build the REAL constraint
// (= (+ (ite (select set e_i) 1 0) ...) k); any other element domain builds
// the real (set.has_size set k) term and every solve over it is an honest
// `unknown` (documented divergence: AY has no infinite-domain cardinality
// procedure), never a wrong verdict.
Z3_ast       Z3_mk_set_has_size(Z3_context c, Z3_ast set, Z3_ast k);

// ============================================================================
// Sequences & Strings
// ============================================================================
//
// The Z3_mk_seq_* constructors are polymorphic over (Seq T) and the String
// sort, matching Z3. AY models strings as a first-class String sort with a
// dedicated str.* theory; each constructor dispatches accordingly.
//
// Z3_mk_seq_nth returns the element (only valid for (Seq T): AY has no Char
// element sort, so it errors on String operands). Z3_mk_seq_at returns the
// length-1 subsequence at the index (str.at / seq.extract(s,i,1)).

Z3_ast       Z3_mk_string(Z3_context c, Z3_string s);
Z3_ast       Z3_mk_seq_empty(Z3_context c, Z3_sort seq);
Z3_ast       Z3_mk_seq_unit(Z3_context c, Z3_ast a);
Z3_ast       Z3_mk_seq_concat(Z3_context c, unsigned int n, const Z3_ast* args);
Z3_ast       Z3_mk_seq_length(Z3_context c, Z3_ast s);
Z3_ast       Z3_mk_seq_at(Z3_context c, Z3_ast s, Z3_ast index);
Z3_ast       Z3_mk_seq_nth(Z3_context c, Z3_ast s, Z3_ast index);
Z3_ast       Z3_mk_seq_extract(Z3_context c, Z3_ast s, Z3_ast offset, Z3_ast length);
Z3_ast       Z3_mk_seq_contains(Z3_context c, Z3_ast container, Z3_ast containee);
Z3_ast       Z3_mk_seq_prefix(Z3_context c, Z3_ast prefix, Z3_ast s);
Z3_ast       Z3_mk_seq_suffix(Z3_context c, Z3_ast suffix, Z3_ast s);
Z3_ast       Z3_mk_seq_index(Z3_context c, Z3_ast s, Z3_ast substr, Z3_ast offset);
Z3_ast       Z3_mk_seq_replace(Z3_context c, Z3_ast s, Z3_ast src, Z3_ast dst);
Z3_ast       Z3_mk_str_to_int(Z3_context c, Z3_ast s);
Z3_ast       Z3_mk_int_to_str(Z3_context c, Z3_ast s);

// String-literal accessors. Z3_is_string/Z3_get_string/Z3_get_string_length
// inspect a string *literal* (a (str) constant); non-literals report
// false/NULL/0 rather than guessing.
bool         Z3_is_string(Z3_context c, Z3_ast a);
Z3_string    Z3_get_string(Z3_context c, Z3_ast a);
unsigned int Z3_get_string_length(Z3_context c, Z3_ast a);
// Z3_get_string_contents fills Unicode code points (one unsigned per char,
// consistent with Z3_get_string_length's code-point count); Z3_get_lstring
// returns the raw UTF-8 bytes and stores the BYTE length. For ASCII literals
// both agree exactly with libz3. Non-literals: no write / NULL with length 0.
void         Z3_get_string_contents(Z3_context c, Z3_ast s, unsigned int length,
                                    unsigned int contents[]);
Z3_char_ptr  Z3_get_lstring(Z3_context c, Z3_ast s, unsigned int* length);

// ============================================================================
// Regular Expressions (RegLan)
// ============================================================================
//
// Builders return the RegLan sort; Z3_mk_seq_in_re returns Bool. The n-ary
// union/concat/intersect left-fold AY's binary re.union/re.++/re.inter; n==0 is
// an honest Z3_INVALID_ARG (returns 0). Z3_mk_re_full/empty/allchar take a
// regex sort (from Z3_mk_re_sort) — AY's RegLan is monomorphic so the sort is
// validated but does not parameterize the result.

Z3_ast       Z3_mk_seq_to_re(Z3_context c, Z3_ast seq);
Z3_ast       Z3_mk_seq_in_re(Z3_context c, Z3_ast seq, Z3_ast re);
Z3_ast       Z3_mk_re_star(Z3_context c, Z3_ast re);
Z3_ast       Z3_mk_re_plus(Z3_context c, Z3_ast re);
Z3_ast       Z3_mk_re_option(Z3_context c, Z3_ast re);
Z3_ast       Z3_mk_re_complement(Z3_context c, Z3_ast re);
Z3_ast       Z3_mk_re_union(Z3_context c, unsigned int n, const Z3_ast* args);
Z3_ast       Z3_mk_re_concat(Z3_context c, unsigned int n, const Z3_ast* args);
Z3_ast       Z3_mk_re_intersect(Z3_context c, unsigned int n, const Z3_ast* args);
Z3_ast       Z3_mk_re_range(Z3_context c, Z3_ast lo, Z3_ast hi);
Z3_ast       Z3_mk_re_loop(Z3_context c, Z3_ast re, unsigned int lo, unsigned int hi);
Z3_ast       Z3_mk_re_full(Z3_context c, Z3_sort re_sort);
Z3_ast       Z3_mk_re_empty(Z3_context c, Z3_sort re_sort);
Z3_ast       Z3_mk_re_allchar(Z3_context c, Z3_sort re_sort);

// ============================================================================
// Bitvectors
// ============================================================================

// Binary BV operations
Z3_ast       Z3_mk_bvand(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast       Z3_mk_bvor(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast       Z3_mk_bvxor(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast       Z3_mk_bvadd(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast       Z3_mk_bvsub(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast       Z3_mk_bvmul(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast       Z3_mk_bvudiv(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast       Z3_mk_bvsdiv(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast       Z3_mk_bvurem(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast       Z3_mk_bvsrem(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast       Z3_mk_bvsmod(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast       Z3_mk_bvshl(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast       Z3_mk_bvlshr(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast       Z3_mk_bvashr(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast       Z3_mk_bvnand(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast       Z3_mk_bvnor(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast       Z3_mk_bvxnor(Z3_context c, Z3_ast t1, Z3_ast t2);

// BV comparison operations
Z3_ast       Z3_mk_bvult(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast       Z3_mk_bvslt(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast       Z3_mk_bvule(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast       Z3_mk_bvsle(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast       Z3_mk_bvugt(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast       Z3_mk_bvuge(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast       Z3_mk_bvsgt(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast       Z3_mk_bvsge(Z3_context c, Z3_ast t1, Z3_ast t2);

// BV unary operations
Z3_ast       Z3_mk_bvnot(Z3_context c, Z3_ast t1);
Z3_ast       Z3_mk_bvneg(Z3_context c, Z3_ast t1);

// BV width-changing operations
Z3_ast       Z3_mk_concat(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast       Z3_mk_extract(Z3_context c, unsigned int high, unsigned int low, Z3_ast t1);
Z3_ast       Z3_mk_sign_ext(Z3_context c, unsigned int i, Z3_ast t1);
Z3_ast       Z3_mk_zero_ext(Z3_context c, unsigned int i, Z3_ast t1);
Z3_ast       Z3_mk_repeat(Z3_context c, unsigned int i, Z3_ast t1);
Z3_ast       Z3_mk_rotate_left(Z3_context c, unsigned int i, Z3_ast t1);
Z3_ast       Z3_mk_rotate_right(Z3_context c, unsigned int i, Z3_ast t1);

// BV-Int conversions
Z3_ast       Z3_mk_bv2int(Z3_context c, Z3_ast t1, bool is_signed);
Z3_ast       Z3_mk_int2bv(Z3_context c, unsigned int n, Z3_ast t1);

// BV overflow/underflow checks
Z3_ast       Z3_mk_bvadd_no_overflow(Z3_context c, Z3_ast t1, Z3_ast t2, bool is_signed);
Z3_ast       Z3_mk_bvadd_no_underflow(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast       Z3_mk_bvsub_no_overflow(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast       Z3_mk_bvsub_no_underflow(Z3_context c, Z3_ast t1, Z3_ast t2, bool is_signed);
Z3_ast       Z3_mk_bvsdiv_no_overflow(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast       Z3_mk_bvneg_no_overflow(Z3_context c, Z3_ast t1);
Z3_ast       Z3_mk_bvmul_no_overflow(Z3_context c, Z3_ast t1, Z3_ast t2, bool is_signed);
Z3_ast       Z3_mk_bvmul_no_underflow(Z3_context c, Z3_ast t1, Z3_ast t2);

// BV reduction operations
Z3_ast       Z3_mk_bvredand(Z3_context c, Z3_ast t1);
Z3_ast       Z3_mk_bvredor(Z3_context c, Z3_ast t1);

// BV equality comparison (returns 1-bit BV)
Z3_ast       Z3_mk_bvcomp(Z3_context c, Z3_ast t1, Z3_ast t2);

// ============================================================================
// Floating-Point (IEEE-754 / FPA)
// ============================================================================
//
// Every Z3_mk_fpa_* term constructor below delegates to AY's PROVEN-CORRECT
// floating-point Solver builders (the same ones AY's SMT-LIB elaborator and
// model reconstruction use). NO FP semantics are defined in the FFI layer: the
// IEEE-754 meaning (rounding, NaN/inf/zero, bit-blasting) comes entirely from
// AY's core FP theory. A constructor handed an ill-sorted operand returns the
// null AST and sets Z3_SORT_ERROR (or Z3_INVALID_ARG for an unsupported width),
// never a silently-wrong term.
//
// An FP sort is (_ FloatingPoint ebits sbits) where `sbits` INCLUDES the hidden
// bit (exactly as Z3): half=(5,11), single=(8,24), double=(11,53),
// quadruple=(15,113).
//
// A rounding mode is a value consumed by the rounded arithmetic ops. AY models
// it as a named term recognized by the FP solver; Z3_mk_fpa_rounding_mode_sort
// is provided for API completeness (a sentinel RoundingMode sort handle).
//
// NOTE (numerals): Z3_mk_fpa_numeral_double/_int support the standard half,
// single, and double precisions, where the value is encoded via the hardware's
// correctly-rounded conversion (the same bit-pattern path the Python binding
// validated against z3py). Other precisions are rejected with Z3_INVALID_ARG;
// build their (fp #b.. #b.. #b..) literal via Z3_parse_smtlib2_string instead.
//
// NOT exposed here (no validated low-level backing): Z3_mk_fpa_to_fp_real
// (Real->FP; AY has no Real->FP builder), Z3_mk_fpa_to_fp_unsigned, the FP->BV
// conversions, and Z3_fpa_get_numeral_double (model-value readout). These are
// reachable today only via Z3_parse_smtlib2_string / the Rust API.

// FP sorts
Z3_sort      Z3_mk_fpa_sort(Z3_context c, unsigned int ebits, unsigned int sbits);
Z3_sort      Z3_mk_fpa_sort_half(Z3_context c);
Z3_sort      Z3_mk_fpa_sort_single(Z3_context c);
Z3_sort      Z3_mk_fpa_sort_double(Z3_context c);
Z3_sort      Z3_mk_fpa_sort_quadruple(Z3_context c);
Z3_sort      Z3_mk_fpa_rounding_mode_sort(Z3_context c);

// Rounding-mode constants (with z3py-style short aliases)
Z3_ast       Z3_mk_fpa_round_nearest_ties_to_even(Z3_context c);
Z3_ast       Z3_mk_fpa_rne(Z3_context c);
Z3_ast       Z3_mk_fpa_round_nearest_ties_to_away(Z3_context c);
Z3_ast       Z3_mk_fpa_rna(Z3_context c);
Z3_ast       Z3_mk_fpa_round_toward_positive(Z3_context c);
Z3_ast       Z3_mk_fpa_rtp(Z3_context c);
Z3_ast       Z3_mk_fpa_round_toward_negative(Z3_context c);
Z3_ast       Z3_mk_fpa_rtn(Z3_context c);
Z3_ast       Z3_mk_fpa_round_toward_zero(Z3_context c);
Z3_ast       Z3_mk_fpa_rtz(Z3_context c);

// FP constants / literals
Z3_ast       Z3_mk_fpa_nan(Z3_context c, Z3_sort sort);
Z3_ast       Z3_mk_fpa_inf(Z3_context c, Z3_sort sort, bool negative);
Z3_ast       Z3_mk_fpa_zero(Z3_context c, Z3_sort sort, bool negative);
Z3_ast       Z3_mk_fpa_numeral_double(Z3_context c, double value, Z3_sort sort);
Z3_ast       Z3_mk_fpa_numeral_int(Z3_context c, int value, Z3_sort sort);

// FP unary operations
Z3_ast       Z3_mk_fpa_abs(Z3_context c, Z3_ast t);
Z3_ast       Z3_mk_fpa_neg(Z3_context c, Z3_ast t);

// FP rounded arithmetic (take a rounding mode)
Z3_ast       Z3_mk_fpa_add(Z3_context c, Z3_ast rm, Z3_ast t1, Z3_ast t2);
Z3_ast       Z3_mk_fpa_sub(Z3_context c, Z3_ast rm, Z3_ast t1, Z3_ast t2);
Z3_ast       Z3_mk_fpa_mul(Z3_context c, Z3_ast rm, Z3_ast t1, Z3_ast t2);
Z3_ast       Z3_mk_fpa_div(Z3_context c, Z3_ast rm, Z3_ast t1, Z3_ast t2);
Z3_ast       Z3_mk_fpa_fma(Z3_context c, Z3_ast rm, Z3_ast t1, Z3_ast t2, Z3_ast t3);
Z3_ast       Z3_mk_fpa_sqrt(Z3_context c, Z3_ast rm, Z3_ast t);
Z3_ast       Z3_mk_fpa_round_to_integral(Z3_context c, Z3_ast rm, Z3_ast t);

// FP arithmetic without a rounding mode
Z3_ast       Z3_mk_fpa_rem(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast       Z3_mk_fpa_min(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast       Z3_mk_fpa_max(Z3_context c, Z3_ast t1, Z3_ast t2);

// FP comparison predicates (return Bool)
Z3_ast       Z3_mk_fpa_eq(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast       Z3_mk_fpa_lt(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast       Z3_mk_fpa_leq(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast       Z3_mk_fpa_gt(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast       Z3_mk_fpa_geq(Z3_context c, Z3_ast t1, Z3_ast t2);

// FP classification predicates (return Bool)
Z3_ast       Z3_mk_fpa_is_nan(Z3_context c, Z3_ast t);
Z3_ast       Z3_mk_fpa_is_infinite(Z3_context c, Z3_ast t);
Z3_ast       Z3_mk_fpa_is_zero(Z3_context c, Z3_ast t);
Z3_ast       Z3_mk_fpa_is_normal(Z3_context c, Z3_ast t);
Z3_ast       Z3_mk_fpa_is_subnormal(Z3_context c, Z3_ast t);
Z3_ast       Z3_mk_fpa_is_negative(Z3_context c, Z3_ast t);
Z3_ast       Z3_mk_fpa_is_positive(Z3_context c, Z3_ast t);

// FP conversions
Z3_ast       Z3_mk_fpa_to_fp_float(Z3_context c, Z3_ast rm, Z3_ast t, Z3_sort sort);
Z3_ast       Z3_mk_fpa_to_fp_signed(Z3_context c, Z3_ast rm, Z3_ast t, Z3_sort sort);

// ============================================================================
// Quantifiers
// ============================================================================

// Patterns (triggers) for quantifier instantiation
Z3_pattern   Z3_mk_pattern(Z3_context c, unsigned int num_patterns,
                            const Z3_ast* terms);

// De Bruijn indexed bound variable
Z3_ast       Z3_mk_bound(Z3_context c, unsigned int index, Z3_sort ty);

// De Bruijn style quantifiers
Z3_ast       Z3_mk_forall(Z3_context c, unsigned int weight,
                           unsigned int num_patterns, const Z3_pattern* patterns,
                           unsigned int num_decls, const Z3_sort* sorts,
                           const Z3_symbol* decl_names, Z3_ast body);
Z3_ast       Z3_mk_exists(Z3_context c, unsigned int weight,
                           unsigned int num_patterns, const Z3_pattern* patterns,
                           unsigned int num_decls, const Z3_sort* sorts,
                           const Z3_symbol* decl_names, Z3_ast body);

// Constant-style quantifiers (preferred — uses term constants as bound vars)
Z3_ast       Z3_mk_forall_const(Z3_context c, unsigned int weight,
                                 unsigned int num_bound, const Z3_ast* bound,
                                 unsigned int num_patterns, const Z3_pattern* patterns,
                                 Z3_ast body);
Z3_ast       Z3_mk_exists_const(Z3_context c, unsigned int weight,
                                 unsigned int num_bound, const Z3_ast* bound,
                                 unsigned int num_patterns, const Z3_pattern* patterns,
                                 Z3_ast body);

// Quantifier introspection
bool         Z3_is_quantifier_forall(Z3_context c, Z3_ast a);
bool         Z3_is_quantifier_exists(Z3_context c, Z3_ast a);
Z3_ast       Z3_get_quantifier_body(Z3_context c, Z3_ast a);
unsigned int Z3_get_quantifier_num_bound(Z3_context c, Z3_ast a);
Z3_symbol    Z3_get_quantifier_bound_name(Z3_context c, Z3_ast a, unsigned int i);
Z3_sort      Z3_get_quantifier_bound_sort(Z3_context c, Z3_ast a, unsigned int i);
unsigned int Z3_get_quantifier_num_patterns(Z3_context c, Z3_ast a);
Z3_pattern   Z3_get_quantifier_pattern_ast(Z3_context c, Z3_ast a, unsigned int i);
unsigned int Z3_get_quantifier_weight(Z3_context c, Z3_ast a);
unsigned int Z3_get_quantifier_num_no_patterns(Z3_context c, Z3_ast a);
Z3_ast       Z3_get_quantifier_no_pattern_ast(Z3_context c, Z3_ast a, unsigned int i);
// Quantifier metadata. AY does not track :qid/:skolemid annotations, so both
// return the null symbol (HONEST "none set" — exactly what libz3 returns for
// a quantifier built without a qid/skolemid).
Z3_symbol    Z3_get_quantifier_id(Z3_context c, Z3_ast a);
Z3_symbol    Z3_get_quantifier_skolem_id(Z3_context c, Z3_ast a);
// Pattern (multi-trigger) introspection: number of terms and the i-th term.
unsigned int Z3_get_pattern_num_terms(Z3_context c, Z3_pattern p);
Z3_ast       Z3_get_pattern(Z3_context c, Z3_pattern p, unsigned int i);

// ============================================================================
// AST Inspection
// ============================================================================

unsigned int Z3_get_ast_kind(Z3_context c, Z3_ast a);
// Depth of an AST: leaves have depth 1, applications 1 + max(child depths)
// (z3's convention).
unsigned int Z3_get_depth(Z3_context c, Z3_ast a);
// as-array model terms. AY models never emit (_ as-array f) terms (array
// interpretations are store/const chains + the func_interp surface), so
// Z3_is_as_array is HONESTLY false for every AY AST and
// Z3_get_as_array_func_decl returns NULL + Z3_INVALID_ARG (never fabricated).
bool         Z3_is_as_array(Z3_context c, Z3_ast a);
Z3_func_decl Z3_get_as_array_func_decl(Z3_context c, Z3_ast a);
bool         Z3_is_numeral_ast(Z3_context c, Z3_ast a);
bool         Z3_is_eq_ast(Z3_context c, Z3_ast t1, Z3_ast t2);
bool         Z3_is_app(Z3_context c, Z3_ast a);
Z3_ast       Z3_to_app(Z3_context c, Z3_ast a);
unsigned int Z3_get_ast_id(Z3_context c, Z3_ast a);
unsigned int Z3_get_ast_hash(Z3_context c, Z3_ast a);
Z3_string    Z3_get_numeral_string(Z3_context c, Z3_ast a);
Z3_string    Z3_get_numeral_decimal_string(Z3_context c, Z3_ast a, unsigned int precision);
Z3_string    Z3_ast_to_string(Z3_context c, Z3_ast a);
int          Z3_get_bool_value(Z3_context c, Z3_ast a);
bool         Z3_get_numeral_int(Z3_context c, Z3_ast a, int* v);
bool         Z3_get_numeral_uint(Z3_context c, Z3_ast a, unsigned int* v);
bool         Z3_get_numeral_int64(Z3_context c, Z3_ast a, int64_t* v);
bool         Z3_get_numeral_uint64(Z3_context c, Z3_ast a, uint64_t* v);
// Numeral introspection (group A). Every value is read from the REAL stored
// constant. numerator/denominator return Int-sorted numeral ASTs (Int numeral
// n -> n and 1); NULL/0 for non-numerals. Z3_get_numeral_double is the nearest
// double of the exact rational (BV/non-numeral -> 0.0, libz3's error answer).
// rational_int64/small succeed iff numerator and denominator fit in int64
// (BV numerals report (value, 1), as libz3 does). binary_string is the value
// in binary without leading zeros ("1010" for BV 10, "0" for zero); defined
// for BV numerals and non-negative Int numerals, NULL otherwise.
Z3_ast       Z3_get_numerator(Z3_context c, Z3_ast a);
Z3_ast       Z3_get_denominator(Z3_context c, Z3_ast a);
double       Z3_get_numeral_double(Z3_context c, Z3_ast a);
bool         Z3_get_numeral_rational_int64(Z3_context c, Z3_ast v, int64_t* num,
                                           int64_t* den);
bool         Z3_get_numeral_small(Z3_context c, Z3_ast a, int64_t* num, int64_t* den);
Z3_string    Z3_get_numeral_binary_string(Z3_context c, Z3_ast a);
Z3_sort      Z3_get_sort(Z3_context c, Z3_ast a);
unsigned int Z3_get_app_num_args(Z3_context c, Z3_ast a);
Z3_ast       Z3_get_app_arg(Z3_context c, Z3_ast a, unsigned int i);
Z3_func_decl Z3_get_app_decl(Z3_context c, Z3_ast a);

// Simplification
// Return a logically-equivalent simplified term: closed arithmetic folds to a
// numeral, And/Or with true/false collapse, x+0 -> x, x*1 -> x,
// ite(true,a,b) -> a, (select (store a i v) i) -> v, etc.
Z3_ast       Z3_simplify(Z3_context c, Z3_ast a);
// Same as Z3_simplify; the Z3_params argument is accepted for API
// compatibility and ignored (AY's simplifier is parameter-free).
Z3_ast       Z3_simplify_ex(Z3_context c, Z3_ast a, Z3_params p);

// Substitution
// Return `a` with each from[i] subterm simultaneously replaced by to[i].
// from[i] and to[i] must share a sort (mismatch sets Z3_SORT_ERROR and
// returns `a`). A null from/to array or num_exprs==0 returns `a` unchanged.
Z3_ast       Z3_substitute(Z3_context c, Z3_ast a, unsigned int num_exprs,
                           Z3_ast const from[], Z3_ast const to[]);

// ============================================================================
// Function Declaration Inspection
// ============================================================================

Z3_symbol    Z3_get_decl_name(Z3_context c, Z3_func_decl d);
unsigned int Z3_get_arity(Z3_context c, Z3_func_decl d);
unsigned int Z3_get_domain_size(Z3_context c, Z3_func_decl d);
Z3_sort      Z3_get_range(Z3_context c, Z3_func_decl d);
Z3_sort      Z3_get_domain(Z3_context c, Z3_func_decl d, unsigned int i);
unsigned int Z3_get_decl_kind(Z3_context c, Z3_func_decl d);
unsigned int Z3_get_decl_num_parameters(Z3_context c, Z3_func_decl d);
int          Z3_get_decl_int_parameter(Z3_context c, Z3_func_decl d, unsigned int idx);
// Z3_parameter_kind of the idx-th decl parameter. AY's indexed operators carry
// only integer parameters, so this returns Z3_PARAMETER_INT for every in-range
// idx (idx >= num_parameters sets Z3_IOB and returns Z3_PARAMETER_INT).
unsigned int Z3_get_decl_parameter_kind(Z3_context c, Z3_func_decl d, unsigned int idx);
Z3_ast       Z3_func_decl_to_ast(Z3_context c, Z3_func_decl d);
bool         Z3_is_eq_func_decl(Z3_context c, Z3_func_decl f1, Z3_func_decl f2);
Z3_string    Z3_func_decl_to_string(Z3_context c, Z3_func_decl d);

// ============================================================================
// Error Handling
// ============================================================================

unsigned int Z3_get_error_code(Z3_context c);
Z3_string    Z3_get_error_msg(Z3_context c, unsigned int err);
void         Z3_set_error_handler(Z3_context c, void (*h)(Z3_context, unsigned int));

// ============================================================================
// AST Vectors
// ============================================================================

Z3_ast_vector Z3_mk_ast_vector(Z3_context c);
void          Z3_ast_vector_inc_ref(Z3_context c, Z3_ast_vector v);
void          Z3_ast_vector_dec_ref(Z3_context c, Z3_ast_vector v);
unsigned int  Z3_ast_vector_size(Z3_context c, Z3_ast_vector v);
Z3_ast        Z3_ast_vector_get(Z3_context c, Z3_ast_vector v, unsigned int i);
void          Z3_ast_vector_push(Z3_context c, Z3_ast_vector v, Z3_ast a);
void          Z3_ast_vector_set(Z3_context c, Z3_ast_vector v, unsigned int i, Z3_ast a);
void          Z3_ast_vector_resize(Z3_context c, Z3_ast_vector v, unsigned int n);
// Translate v from context s into a fresh AST vector in context t (deep-copies
// each element's term DAG when s != t; a plain copy when s == t). The shared
// semantic-metadata portability gate described on Z3_translate applies.
Z3_ast_vector Z3_ast_vector_translate(Z3_context s, Z3_ast_vector v, Z3_context t);
// Render as `(ast-vector\n  e1\n  ...)` (empty: `(ast-vector)`).
Z3_string     Z3_ast_vector_to_string(Z3_context c, Z3_ast_vector v);

// ============================================================================
// AST Maps (a mapping from Z3_ast key to Z3_ast value)
// ============================================================================

Z3_ast_map    Z3_mk_ast_map(Z3_context c);
void          Z3_ast_map_inc_ref(Z3_context c, Z3_ast_map m);
void          Z3_ast_map_dec_ref(Z3_context c, Z3_ast_map m);
bool          Z3_ast_map_contains(Z3_context c, Z3_ast_map m, Z3_ast k);
// Value for key k. If k is absent, sets Z3_INVALID_ARG and returns the null AST
// 0 (Z3 "invokes the error handler if k is not in the map").
Z3_ast        Z3_ast_map_find(Z3_context c, Z3_ast_map m, Z3_ast k);
void          Z3_ast_map_insert(Z3_context c, Z3_ast_map m, Z3_ast k, Z3_ast v);
void          Z3_ast_map_erase(Z3_context c, Z3_ast_map m, Z3_ast k);
void          Z3_ast_map_reset(Z3_context c, Z3_ast_map m);
unsigned int  Z3_ast_map_size(Z3_context c, Z3_ast_map m);
// Fresh AST vector of the map's keys (insertion order).
Z3_ast_vector Z3_ast_map_keys(Z3_context c, Z3_ast_map m);
// Render as `(ast-map\n  (k1\n   v1)\n  ...)` (empty: `(ast-map)`).
Z3_string     Z3_ast_map_to_string(Z3_context c, Z3_ast_map m);

// ============================================================================
// Solver
// ============================================================================
//
// Every Z3_solver owns its OWN assertion stack (with per-handle push/pop
// scopes) and its own last-check artefacts (model, unsat core, reason-unknown,
// proof), matching Z3: several solvers on one context are fully independent
// and share only the context's term arena.

Z3_solver     Z3_mk_solver(Z3_context c);
Z3_solver     Z3_mk_solver_for_logic(Z3_context c, Z3_symbol logic);
void          Z3_solver_inc_ref(Z3_context c, Z3_solver s);
void          Z3_solver_dec_ref(Z3_context c, Z3_solver s);
void          Z3_solver_push(Z3_context c, Z3_solver s);
void          Z3_solver_pop(Z3_context c, Z3_solver s, unsigned int n);
void          Z3_solver_reset(Z3_context c, Z3_solver s);
void          Z3_solver_assert(Z3_context c, Z3_solver s, Z3_ast a);
void          Z3_solver_set_params(Z3_context c, Z3_solver s, Z3_params p);
int           Z3_solver_check(Z3_context c, Z3_solver s);
// A non-zero count requires a non-null array. Malformed calls return UNDEF,
// set INVALID_ARG, and retire stale decision artifacts.
int           Z3_solver_check_assumptions(Z3_context c, Z3_solver s,
                                          unsigned int num_assumptions,
                                          const Z3_ast* assumptions);
Z3_model      Z3_solver_get_model(Z3_context c, Z3_solver s);
Z3_string     Z3_solver_to_string(Z3_context c, Z3_solver s);
Z3_ast_vector Z3_solver_get_assertions(Z3_context c, Z3_solver s);
Z3_ast_vector Z3_solver_get_unsat_core(Z3_context c, Z3_solver s);
Z3_string     Z3_solver_get_reason_unknown(Z3_context c, Z3_solver s);
unsigned int  Z3_solver_get_num_scopes(Z3_context c, Z3_solver s);
void          Z3_solver_interrupt(Z3_context c, Z3_solver s);

// ----------------------------------------------------------------------------
// Solver completion wave 2 (assert-and-track cores, consequences, from
// string/file, translate, trail/units, help, congruence, DIMACS)
// ----------------------------------------------------------------------------
//
// assert_and_track: asserts `a` tracked by the Boolean literal `p`. AY encodes
// this exactly as Z3: it asserts (=> p a) and records `p`; every tracking
// literal is passed as an assumption at the next check, so Z3_solver_get_unsat_core
// returns the subset of tracking literals (plus any check-assumptions) that
// caused UNSAT. Both `a` and `p` must be Boolean. DEVIATION: Z3 additionally
// requires `p` to be an atomic Boolean *constant*; AY accepts any Boolean `p`
// (the (=> p a) encoding is sound for any Boolean p). The core AY returns is an
// over-approximation (sound: every returned literal is a real tracking/assumption
// literal) and may be non-minimal, matching Z3's default non-minimized cores.
void          Z3_solver_assert_and_track(Z3_context c, Z3_solver s, Z3_ast a, Z3_ast p);

// from_string / from_file: parse SMT-LIB2 declarations+assertions through AY's
// real front-end and APPEND them to the solver's assertion stack (query commands
// like check-sat/get-model are ignored). push/pop/reset/reset-assertions and
// assert-soft/maximize/minimize are rejected before execution. Once semantic execution begins, any late error
// permanently fails the context's decision engine closed (unscoped options or
// declarations may already have changed), retires copied models/cores/proofs/
// statistics, and makes existing solver checks/mutators report INVALID_USAGE.
// A subsequent Z3_solver_check solves assertions from a successful parse.
void          Z3_solver_from_string(Z3_context c, Z3_solver s, Z3_string str);
void          Z3_solver_from_file(Z3_context c, Z3_solver s, Z3_string file_name);

// translate: copy solver `s` from `source` into `target`, returning a NEW handle
// carrying a faithful copy of the assertion stack (scopes + assert-and-track
// pairs + tactic). Cross-context copies re-intern the whole term DAG, subject
// to the shared semantic-metadata portability gate on Z3_translate.
Z3_solver     Z3_solver_translate(Z3_context source, Z3_solver s, Z3_context target);

// get_consequences: for each Boolean variable in `variables`, determine whether
// the assertions + `assumptions` force it true/false (checking assumptions ∧ ¬v
// / assumptions ∧ v for UNSAT). Each forced literal is appended to `consequences`
// as the implication (=> (and assumptions) lit). SOUND: a consequence is emitted
// only on a definitive UNSAT probe (only truly-implied values reported); may be
// incomplete under `unknown`. The baseline passes the consumer SAT-acceptance
// boundary. With a user propagator or transitive-closure metadata, this API has
// no corresponding final-check/model-verifier path and returns Z3_L_UNDEF
// fail-closed. Returns Z3_L_FALSE if UNSAT under assumptions, Z3_L_UNDEF if the
// baseline is not publicly admitted, else Z3_L_TRUE.
int           Z3_solver_get_consequences(Z3_context c, Z3_solver s,
                                         Z3_ast_vector assumptions,
                                         Z3_ast_vector variables,
                                         Z3_ast_vector consequences);

// Compute all-model equality classes by definitive UNSAT disequality probes.
// First establishes the same accepted SAT baseline as get_consequences; returns
// FALSE for an inconsistent baseline and UNDEF when its auxiliary acceptance
// path cannot represent active user-propagator/transitive-closure semantics.
// With num_terms > 0, both arrays are required; malformed calls return
// UNDEF/INVALID_ARG without modifying class_ids.
int           Z3_get_implied_equalities(Z3_context c, Z3_solver s,
                                        unsigned int num_terms,
                                        const Z3_ast* terms,
                                        unsigned int* class_ids);

// get_units / get_non_units / get_trail: AY reports the INPUT-level split of the
// solver's assertions — units are the assertions that are literals (an atom or a
// negated atom), non_units are the compound assertions, and get_trail returns the
// level-0 trail (= the input units, which are exactly the level-0 assignments).
// Every returned literal is real; AY does not surface learned/derived units or
// deeper decision-level trail entries through this stable API (a SOUND subset).
Z3_ast_vector Z3_solver_get_units(Z3_context c, Z3_solver s);
Z3_ast_vector Z3_solver_get_non_units(Z3_context c, Z3_solver s);
Z3_ast_vector Z3_solver_get_trail(Z3_context c, Z3_solver s);

// get_help: human-readable description of the parameters AY's solver honors
// (timeout, proof).
Z3_string     Z3_solver_get_help(Z3_context c, Z3_solver s);

// congruence_root / congruence_next: AY does not expose its internal e-graph
// congruence ring through a stable API. HONEST behavior: each term is modeled as
// its own singleton congruence class, so root(a)==a and next(a)==a (a one-element
// cyclic list). SOUND (never claims two distinct terms are congruent when they are
// not); may miss congruences the engine internally knows. Never a fabricated rep.
Z3_ast        Z3_solver_congruence_root(Z3_context c, Z3_solver s, Z3_ast a);
Z3_ast        Z3_solver_congruence_next(Z3_context c, Z3_solver s, Z3_ast a);

// to_dimacs_string: emit the solver's Boolean SKELETON as a Tseitin DIMACS CNF.
// Each distinct Boolean atom (including theory atoms, treated as opaque
// propositional variables) becomes one DIMACS variable; the Boolean connectives
// are encoded with standard definitional clauses. The CNF is equisatisfiable with
// the skeleton. DEVIATION: AY does NOT bit-blast theory atoms (so the DIMACS is
// the propositional skeleton only, unlike libz3), and variable numbering differs
// from libz3's. `include_names` emits a `c <var> <atom>` mapping comment per atom.
Z3_string     Z3_solver_to_dimacs_string(Z3_context c, Z3_solver s, bool include_names);

// ----------------------------------------------------------------------------
// Proof production / retrieval (Alethe) (#phase3-proof)
// ----------------------------------------------------------------------------
//
// AY produces real Alethe proofs after an UNSAT check when proof production is
// enabled. Enable it EITHER via Z3_solver_set_proof_production below, OR via the
// Z3 global config param before context creation:
//     Z3_set_param_value(cfg, "proof", "true");
//
// HONESTY CONTRACT: every retrieval below is fail-closed. They return NULL and
// set Z3_INVALID_USAGE unless the last Z3_solver_check was UNSAT *and* proof
// production was enabled before that check. They NEVER return a proof for a
// SAT/Unknown result or when production is off, and the text is always the
// solver's own Alethe exporter output — never fabricated.
//
// DEVIATION FROM Z3: in real Z3, Z3_solver_get_proof returns a Z3_ast whose
// Z3_ast_to_string yields the proof. AY's proof is a separate Alethe DAG, not a
// term, and Z3_ast is a 32-bit term index, so a proof cannot be encoded as an
// ordinary term handle. Z3_solver_get_proof therefore returns an OPAQUE
// proof-AST handle (high-bit tagged); Z3_ast_to_string on it returns the real
// Alethe text, but it is NOT a valid term and must not be passed to term
// inspection functions (Z3_get_ast_kind, Z3_get_app_*, etc.). Consumers wanting
// the text directly should prefer Z3_solver_get_proof_string.
void          Z3_solver_set_proof_production(Z3_context c, Z3_solver s, bool enabled);
bool          Z3_solver_get_proof_production(Z3_context c, Z3_solver s);
Z3_ast        Z3_solver_get_proof(Z3_context c, Z3_solver s);
Z3_string     Z3_solver_get_proof_string(Z3_context c, Z3_solver s);

// ============================================================================
// Optimize (MaxSMT + arithmetic objectives)
// ============================================================================
//
// Two optimization mechanisms:
//   * MaxSAT / weighted partial MaxSMT: hard constraints (assert) plus weighted
//     soft constraints (assert_soft), solved by AY's weight-exact engine.
//   * Arithmetic objectives: Z3_optimize_maximize / Z3_optimize_minimize over
//     Int / Real / BitVec terms, with optima read via get_lower / get_upper.
//
// The optimize handle aliases the context's single solve engine (UNLIKE
// Z3_solver handles, which each own an independent replayable assertion stack).
// AY ENFORCES exactly one optimize handle per context and rejects mixing it with
// solver or global-parser semantic state (NULL + Z3_INVALID_USAGE). Use one
// context per Z3_optimize. Fixedpoint may coexist because it solves in its own
// CHC engine. inc_ref/dec_ref are bookkeeping-only no-ops.
//
// ROUTING (Z3_optimize_check): objectives-only -> objective optimizer;
// softs-only -> MaxSMT; neither -> plain check-sat. A joint objective+soft
// problem is rejected as Z3_L_UNDEF + Z3_INVALID_ARG rather than silently
// ignoring either class. num_assumptions must be zero (non-zero is likewise
// rejected honestly).
//
// get_lower / get_upper: AY's optimum is EXACT (not an interval), so both return
// the same value — the optimum as a numeral AST in the objective's sort.
// Unbounded objectives (+oo / -oo) return the NULL AST (0): AY has no first-class
// oo numeral and never fabricates one (divergence from Z3's structured oo AST).
// An unbounded Int objective makes Z3_optimize_check return Z3_L_UNDEF (honest —
// AY never fabricates a finite Int optimum); an unbounded Real objective is SAT
// with the optimum reported as oo, where get_lower/get_upper return null.

Z3_optimize   Z3_mk_optimize(Z3_context c);
void          Z3_optimize_inc_ref(Z3_context c, Z3_optimize o);
void          Z3_optimize_dec_ref(Z3_context c, Z3_optimize o);
void          Z3_optimize_assert(Z3_context c, Z3_optimize o, Z3_ast a);
unsigned int  Z3_optimize_assert_soft(Z3_context c, Z3_optimize o, Z3_ast a,
                                      Z3_string weight, Z3_symbol id);
// AY rejects every non-empty check-time assumption set with UNDEF/INVALID_ARG;
// it never dereferences or silently ignores a non-empty array.
int           Z3_optimize_check(Z3_context c, Z3_optimize o,
                                unsigned int num_assumptions,
                                const Z3_ast* assumptions);
Z3_model      Z3_optimize_get_model(Z3_context c, Z3_optimize o);
Z3_string     Z3_optimize_to_string(Z3_context c, Z3_optimize o);
// Arithmetic objectives: register and read back the exact optimum.
unsigned int  Z3_optimize_maximize(Z3_context c, Z3_optimize o, Z3_ast t);
unsigned int  Z3_optimize_minimize(Z3_context c, Z3_optimize o, Z3_ast t);
Z3_ast        Z3_optimize_get_lower(Z3_context c, Z3_optimize o, unsigned int idx);
Z3_ast        Z3_optimize_get_upper(Z3_context c, Z3_optimize o, unsigned int idx);

// Backtracking scopes: push/pop scope the hard assertions, objectives, and soft
// constraints. Z3_optimize_pop backtracks ONE level (scope underflow ->
// Z3_EXCEPTION). One level per call, matching z3.
void          Z3_optimize_push(Z3_context c, Z3_optimize o);
void          Z3_optimize_pop(Z3_context c, Z3_optimize o);

// Tracked hard assertion + unsat core. assert_and_track asserts `a` as a REAL
// hard constraint (unconditional; optima/verdict unaffected) and remembers the
// Boolean tracking literal `t`.
// HONEST DIVERGENCE FROM Z3: Z3_optimize_get_unsat_core returns an EMPTY vector.
// AY's Optimize engine cannot extract a participating-only core — it does not
// thread check-time assumptions through the optimization loop, and the tracked
// constraints are asserted unconditionally, so there is no sound way to tell
// which tracked literals actually participate. Returning the full tracked set
// would report NON-participating literals (a wrong value per Z3's contract), so
// AY returns an empty core instead. The tracked constraint IS still enforced
// (the UNSAT verdict/optimum are correct); only participating-core extraction is
// unsupported. (Z3 returns the participating core here.)
void          Z3_optimize_assert_and_track(Z3_context c, Z3_optimize o, Z3_ast a, Z3_ast t);
Z3_ast_vector Z3_optimize_get_unsat_core(Z3_context c, Z3_optimize o);

// Introspection: the objective expressions (as registered — DIVERGENCE from z3,
// which normalizes to a minimization objective) and the hard assertions.
Z3_ast_vector Z3_optimize_get_objectives(Z3_context c, Z3_optimize o);
Z3_ast_vector Z3_optimize_get_assertions(Z3_context c, Z3_optimize o);

// Bound as a length-3 numeral vector [a, b, c] = a*infinity + b + c*epsilon
// (z3's rep). AY's optima are EXACT and ATTAINED, so a finite optimum v ->
// [0, v, 0]; +oo -> [1, 0, 0]; -oo -> [-1, 0, 0]; epsilon coeff c is always 0
// (AY never fabricates an infinitesimal). Empty vector when no optimum is
// available (last check not SAT).
Z3_ast_vector Z3_optimize_get_lower_as_vector(Z3_context c, Z3_optimize o, unsigned int idx);
Z3_ast_vector Z3_optimize_get_upper_as_vector(Z3_context c, Z3_optimize o, unsigned int idx);

// Reason-unknown and REAL statistics from the last Z3_optimize_check (the stats
// reuse the Z3_solver_get_statistics machinery).
Z3_string     Z3_optimize_get_reason_unknown(Z3_context c, Z3_optimize o);
Z3_stats      Z3_optimize_get_statistics(Z3_context c, Z3_optimize o);

// Parse an SMT-LIB2 spec (assert / assert-soft / maximize / minimize) into the
// optimize context. Semantic execution is transactional. push/pop/reset inside
// the script are rejected; a late execution error rolls back scoped formula /
// objective / soft state and permanently fails the handle closed because
// unscoped options may already have changed. Parsing while a user-visible
// Optimize push scope is open is rejected so hidden transaction scopes cannot
// corrupt the user scope stack. from_file read failure -> Z3_FILE_ACCESS_ERROR.
void          Z3_optimize_from_string(Z3_context c, Z3_optimize o, Z3_string s);
void          Z3_optimize_from_file(Z3_context c, Z3_optimize o, Z3_string s);

// Cross-context translation supports hard constraints, API soft constraints
// (including :id groups), and tracked assertions into a fresh target context.
// Same-context translation, arithmetic objectives, parsed assert-soft state, or
// a target with a solver/optimize owner, or unportable source semantic metadata
// are rejected up front; partial translation is never returned.
Z3_optimize   Z3_optimize_translate(Z3_context source, Z3_optimize o,
                                    Z3_context target);

// Params / help / param descriptors. set_params honors timeout + produce_proofs
// and priority=lex|box|pareto; invalid priority is rejected transactionally.
// get_help / get_param_descrs describe exactly what AY honors.
void          Z3_optimize_set_params(Z3_context c, Z3_optimize o, Z3_params p);
Z3_string     Z3_optimize_get_help(Z3_context c, Z3_optimize o);
Z3_param_descrs Z3_optimize_get_param_descrs(Z3_context c, Z3_optimize o);

// HONEST NO-OPS (documented, never fake state): AY's optimizer takes no
// initialization hint (a hint never changes the optimum), and exposes no
// incremental model-event callback (the final model is available via
// Z3_optimize_get_model).
void          Z3_optimize_set_initial_value(Z3_context c, Z3_optimize o, Z3_ast v, Z3_ast val);
void          Z3_optimize_register_model_eh(Z3_context c, Z3_optimize o, Z3_model m,
                                            void* ctx, Z3_model_eh model_eh);

// Statistics accessors (shared with Z3_solver_get_statistics).
void          Z3_stats_inc_ref(Z3_context c, Z3_stats s);
void          Z3_stats_dec_ref(Z3_context c, Z3_stats s);
unsigned int  Z3_stats_size(Z3_context c, Z3_stats s);
Z3_string     Z3_stats_get_key(Z3_context c, Z3_stats s, unsigned int idx);
Z3_string     Z3_stats_to_string(Z3_context c, Z3_stats s);

// Parameter-descriptor set accessors.
void          Z3_param_descrs_inc_ref(Z3_context c, Z3_param_descrs p);
void          Z3_param_descrs_dec_ref(Z3_context c, Z3_param_descrs p);
unsigned int  Z3_param_descrs_size(Z3_context c, Z3_param_descrs p);
Z3_symbol     Z3_param_descrs_get_name(Z3_context c, Z3_param_descrs p, unsigned int i);
unsigned int  Z3_param_descrs_get_kind(Z3_context c, Z3_param_descrs p, Z3_symbol n);
Z3_string     Z3_param_descrs_get_documentation(Z3_context c, Z3_param_descrs p, Z3_symbol s);
Z3_string     Z3_param_descrs_to_string(Z3_context c, Z3_param_descrs p);

// ============================================================================
// Tactics (goal-to-goal transformations) — backed by AY's tactic framework
// ============================================================================
//
// A tactic transforms a goal (the set of assertions) into an equivalent goal,
// then the result is solved normally. Every tactic AY exposes here is
// EQUIVALENCE-PRESERVING: it rewrites the goal into one with exactly the same
// set of models, so solving via Z3_mk_solver_from_tactic yields the SAME
// SAT/UNSAT verdict and a VALID model as solving the original goal.
//
// Z3_mk_tactic recognizes the tactic by NAME (the same real-z3 name set the
// SMT-LIB `(apply <name>)` surface accepts). Supported names:
//   * "skip"             — identity.
//   * "simplify"         — simplify each formula; split top-level conjunctions.
//   * "solve-eqs"        — solve variable equalities and eliminate them.
//   * "propagate-values" — propagate ground (= expr const) equalities.
//   * "elim-and"         — z3's and-elimination: (and (and a b) c) => {a, b, c}.
//   * "qe-light"         — Cooper LIA elimination of in-fragment existentials.
//
// UNKNOWN / UNSUPPORTED NAMES (honest handling), including names z3 itself does
// not have such as "flatten-and": Z3_mk_tactic returns NULL and
// sets the error code to Z3_INVALID_ARG. It NEVER silently returns a no-op that
// pretends to be the requested tactic, and never maps a name to a transform
// whose soundness is unknown. Check Z3_get_error_code after Z3_mk_tactic.
//
// Z3_tactic_and_then / Z3_tactic_or_else compose tactics (null operand -> NULL +
// Z3_INVALID_ARG). Z3_tactic_inc_ref / Z3_tactic_dec_ref are bookkeeping-only
// no-ops (the handle is arena-owned and freed by Z3_del_context), matching
// Z3_solver_inc_ref / Z3_optimize_inc_ref.
//
// TACTIC-COMBINATOR COMPLETION (over the same real engine):
//   * Z3_tactic_skip / Z3_tactic_fail            — the identity / always-fail
//                                                  primitives.
//   * Z3_tactic_fail_if(p)                        — fail iff probe p HOLDS on the
//                                                  goal (matches libz3's actual
//                                                  behavior; the z3.h comment is
//                                                  inverted), else skip.
//   * Z3_tactic_fail_if_not_decided               — fail unless the goal is
//                                                  trivially decided (empty, or
//                                                  contains false), else skip.
//   * Z3_tactic_when(p, t)                         — apply t iff p holds, else skip.
//   * Z3_tactic_cond(p, t1, t2)                    — apply t1 iff p holds, else t2
//                                                  (a real primitive: a failure of
//                                                  the chosen branch propagates —
//                                                  it does NOT fall through).
//   * Z3_tactic_try_for(t, ms)                     — HONEST: AY's passes are already
//                                                  bounded and terminate, so the ms
//                                                  deadline is never hit and this
//                                                  behaves exactly like t (never a
//                                                  fabricated timeout).
//   * Z3_tactic_par_and_then / Z3_tactic_par_or    — HONEST: AY has no parallel goal
//                                                  engine, so these compose
//                                                  SEQUENTIALLY (then / or-else) —
//                                                  the SAME apply-result set, serial.
//   * Z3_tactic_get_descr(name)                    — an honest per-name description of
//                                                  AY's real realization of the named
//                                                  tactic (NULL + Z3_INVALID_ARG for
//                                                  an unknown name).
//   * Z3_tactic_get_param_descrs(t)                — HONEST-EMPTY: AY's tactics expose
//                                                  no per-tactic params that change
//                                                  the model set, so a REAL size-0
//                                                  Z3_param_descrs (never a fake set).
// Every constructed tactic ACTUALLY RUNS through the same ay_dpll apply engine as
// Z3_tactic_apply / Z3_mk_solver_from_tactic (null operand -> NULL + Z3_INVALID_ARG).

Z3_tactic     Z3_mk_tactic(Z3_context c, Z3_string name);
void          Z3_tactic_inc_ref(Z3_context c, Z3_tactic t);
void          Z3_tactic_dec_ref(Z3_context c, Z3_tactic t);
Z3_tactic     Z3_tactic_and_then(Z3_context c, Z3_tactic t1, Z3_tactic t2);
Z3_tactic     Z3_tactic_or_else(Z3_context c, Z3_tactic t1, Z3_tactic t2);
Z3_tactic     Z3_tactic_skip(Z3_context c);
Z3_tactic     Z3_tactic_fail(Z3_context c);
Z3_tactic     Z3_tactic_fail_if(Z3_context c, Z3_probe p);
Z3_tactic     Z3_tactic_fail_if_not_decided(Z3_context c);
Z3_tactic     Z3_tactic_when(Z3_context c, Z3_probe p, Z3_tactic t);
Z3_tactic     Z3_tactic_cond(Z3_context c, Z3_probe p, Z3_tactic t1, Z3_tactic t2);
Z3_tactic     Z3_tactic_try_for(Z3_context c, Z3_tactic t, unsigned int ms);
Z3_tactic     Z3_tactic_par_and_then(Z3_context c, Z3_tactic t1, Z3_tactic t2);
Z3_tactic     Z3_tactic_par_or(Z3_context c, unsigned int num, Z3_tactic const ts[]);
Z3_string     Z3_tactic_get_descr(Z3_context c, Z3_string name);
Z3_param_descrs Z3_tactic_get_param_descrs(Z3_context c, Z3_tactic t);
Z3_solver     Z3_mk_solver_from_tactic(Z3_context c, Z3_tactic t);
Z3_string     Z3_tactic_get_help(Z3_context c);
// Registry enumeration: AY's REAL supported tactic set (the exact names
// Z3_mk_tactic accepts — a documented subset of z3's 100+ builtin tactics;
// every enumerated name is backed by a real verdict-preserving pass).
// Z3_get_tactic_name returns NULL + Z3_INVALID_ARG for an out-of-range index.
unsigned int  Z3_get_num_tactics(Z3_context c);
Z3_string     Z3_get_tactic_name(Z3_context c, unsigned int i);

// ----------------------------------------------------------------------------
// Simplifiers (incremental preprocessing transformers attached to a solver)
// ----------------------------------------------------------------------------
//
// A SIMPLIFIER is a preprocessing goal-to-goal transformer — like a tactic, but
// attached to a solver (Z3_solver_add_simplifier) so the solver runs it as a
// pre-processing step before each check-sat. AY realizes each simplifier over its
// real preprocess passes through the SAME name->transform mapping the tactic
// surface uses, so every simplifier is VERDICT-PRESERVING: solving via a solver
// with a simplifier attached yields the SAME SAT/UNSAT verdict as solving the
// original assertions — a simplifier can never change the answer.
//
// Z3_mk_simplifier recognizes the simplifier by NAME. Supported names:
//   simplify, solve-eqs, propagate-values, qe-light, bit-blast  (real z3
//     simplifier names, each backed by a real AY pass), plus the documented AY
//     superset elim-and, nnf. Any other name (including z3-superset names on the
//     twin, and unknown names) -> Z3_mk_simplifier returns NULL + Z3_INVALID_ARG
//     (honest; never a silent no-op pretending to be the requested simplifier).
//     Check Z3_get_error_code after Z3_mk_simplifier.
//
// Z3_simplifier_and_then(s1, s2) composes two simplifiers sequentially (null
// operand -> NULL + Z3_INVALID_ARG). Z3_simplifier_using_params(s, p) attaches a
// param set: HONEST — AY's simplifiers are the verdict-preserving transform, so p
// (which in z3 only tunes output shape, never the verdict) is accepted for API
// compatibility and does not change the transform. Z3_simplifier_inc_ref /
// Z3_simplifier_dec_ref are bookkeeping-only no-ops (handles are arena-owned by
// the context and freed by Z3_del_context).
//
// Z3_solver_add_simplifier(solver, simp) returns a NEW solver (matching z3, which
// returns a fresh solver rather than mutating the input) that copies the source
// solver's current assertion state and runs simp — composed after any existing
// preprocessing — before each check (null solver/simplifier -> NULL +
// Z3_INVALID_ARG).
//
// Introspection: Z3_simplifier_get_descr(name) returns an honest per-name
// description of AY's real transform (unknown name -> NULL + Z3_INVALID_ARG).
// Z3_simplifier_get_help(s) returns a real non-empty help string (AY simplifiers
// are parameter-free). Z3_simplifier_get_param_descrs(s) is HONEST-EMPTY: a REAL,
// queryable descriptor set of size 0 (AY simplifiers expose no verdict-changing
// params), never a fabricated set (null s -> NULL + Z3_INVALID_ARG).
Z3_simplifier   Z3_mk_simplifier(Z3_context c, Z3_string name);
void            Z3_simplifier_inc_ref(Z3_context c, Z3_simplifier t);
void            Z3_simplifier_dec_ref(Z3_context c, Z3_simplifier t);
Z3_simplifier   Z3_simplifier_and_then(Z3_context c, Z3_simplifier t1, Z3_simplifier t2);
Z3_simplifier   Z3_simplifier_using_params(Z3_context c, Z3_simplifier t, Z3_params p);
Z3_solver       Z3_solver_add_simplifier(Z3_context c, Z3_solver solver, Z3_simplifier simplifier);
Z3_string       Z3_simplifier_get_descr(Z3_context c, Z3_string name);
Z3_string       Z3_simplifier_get_help(Z3_context c, Z3_simplifier t);
Z3_param_descrs Z3_simplifier_get_param_descrs(Z3_context c, Z3_simplifier t);
// Registry enumeration: AY's REAL supported simplifier set (the exact names
// Z3_mk_simplifier accepts — a documented subset of z3's builtin simplifiers).
// Z3_get_simplifier_name returns NULL + Z3_INVALID_ARG for an out-of-range index.
unsigned int    Z3_get_num_simplifiers(Z3_context c);
Z3_string       Z3_get_simplifier_name(Z3_context c, unsigned int i);

// ============================================================================
// Goals & apply-results (the object a tactic transforms) + Probes
// ============================================================================
//
// A GOAL is a set (implicit conjunction) of assertion formulas. Z3_mk_goal
// builds an empty goal; Z3_goal_assert appends a formula; Z3_goal_size /
// Z3_goal_formula read the formulas back. Z3_tactic_apply(c, t, g) runs a tactic
// on a goal and returns an APPLY-RESULT holding the produced subgoals (each a
// Z3_goal), read via Z3_apply_result_get_num_subgoals / _get_subgoal.
//
// AY's tactics are all EQUIVALENCE-PRESERVING, so every goal AY produces is
// Z3_GOAL_PRECISE (Z3_goal_precision) — AY never manufactures an approximated
// goal. Z3_goal_is_decided_sat is true for an empty goal; Z3_goal_is_decided_unsat
// / Z3_goal_inconsistent are true for a goal containing `false`. Z3_goal_num_exprs,
// Z3_goal_depth and Z3_goal_to_string match libz3's values/format on the same goal.
//
// A PROBE is a numeric (or boolean, 1.0/0.0) query over a goal. Z3_mk_probe(name)
// builds a named probe; Z3_probe_apply(c, p, g) returns the REAL double AY's
// engine computes over the goal — the SAME computation the SMT-LIB
// `(apply (when <probe> ...))` surface uses, matching libz3 exactly on the
// supported set. Z3_probe_const / _lt / _le / _gt / _ge / _eq / _and / _or / _not
// build the constant/comparison/boolean combinators. Supported names (via
// Z3_get_num_probes / Z3_get_probe_name / Z3_probe_get_descr): size, num-exprs,
// num-consts, num-bool-consts, num-arith-consts, num-bv-consts, depth,
// has-quantifiers, is-propositional, is-qfbv, is-qflia, is-qflra, is-qflira,
// is-lia, is-lra, is-lira, is-qfnia, is-qfnra, is-nia, is-nra. An unsupported
// name -> Z3_mk_probe returns NULL + Z3_INVALID_ARG (honest; never a fake probe).
//
// Ref-counting (Z3_goal_inc_ref/_dec_ref, Z3_apply_result_inc_ref/_dec_ref,
// Z3_probe_inc_ref/_dec_ref) is bookkeeping-only: the handles are arena-owned by
// the context and freed by Z3_del_context.

// Z3_goal_prec: AY goals are always Z3_GOAL_PRECISE (no over/under approximation).
typedef enum {
    Z3_GOAL_PRECISE,
    Z3_GOAL_UNDER,
    Z3_GOAL_OVER,
    Z3_GOAL_UNDER_OVER
} Z3_goal_prec;

Z3_goal        Z3_mk_goal(Z3_context c, bool models, bool unsat_cores, bool proofs);
void           Z3_goal_inc_ref(Z3_context c, Z3_goal g);
void           Z3_goal_dec_ref(Z3_context c, Z3_goal g);
void           Z3_goal_assert(Z3_context c, Z3_goal g, Z3_ast a);
Z3_goal_prec   Z3_goal_precision(Z3_context c, Z3_goal g);
unsigned int   Z3_goal_size(Z3_context c, Z3_goal g);
Z3_ast         Z3_goal_formula(Z3_context c, Z3_goal g, unsigned int idx);
unsigned int   Z3_goal_num_exprs(Z3_context c, Z3_goal g);
unsigned int   Z3_goal_depth(Z3_context c, Z3_goal g);
bool           Z3_goal_inconsistent(Z3_context c, Z3_goal g);
bool           Z3_goal_is_decided_sat(Z3_context c, Z3_goal g);
bool           Z3_goal_is_decided_unsat(Z3_context c, Z3_goal g);
void           Z3_goal_reset(Z3_context c, Z3_goal g);
// Cross-context copy is subject to Z3_translate's semantic-metadata gate.
Z3_goal        Z3_goal_translate(Z3_context source, Z3_goal g, Z3_context target);
Z3_model       Z3_goal_convert_model(Z3_context c, Z3_goal g, Z3_model m);
Z3_string      Z3_goal_to_string(Z3_context c, Z3_goal g);

Z3_apply_result Z3_tactic_apply(Z3_context c, Z3_tactic t, Z3_goal g);
// Z3_tactic_apply_ex applies t to g "using" the param set p; AY always applies the
// equivalence-preserving transform, so p (which in z3 only tunes output shape,
// never the verdict/model set) is honestly ignored — the subgoals are identical to
// Z3_tactic_apply on the same goal.
Z3_apply_result Z3_tactic_apply_ex(Z3_context c, Z3_tactic t, Z3_goal g, Z3_params p);
void            Z3_apply_result_inc_ref(Z3_context c, Z3_apply_result r);
void            Z3_apply_result_dec_ref(Z3_context c, Z3_apply_result r);
unsigned int    Z3_apply_result_get_num_subgoals(Z3_context c, Z3_apply_result r);
Z3_goal         Z3_apply_result_get_subgoal(Z3_context c, Z3_apply_result r, unsigned int i);

Z3_probe       Z3_mk_probe(Z3_context c, Z3_string name);
void           Z3_probe_inc_ref(Z3_context c, Z3_probe p);
void           Z3_probe_dec_ref(Z3_context c, Z3_probe p);
Z3_probe       Z3_probe_const(Z3_context c, double val);
Z3_probe       Z3_probe_lt(Z3_context c, Z3_probe p1, Z3_probe p2);
Z3_probe       Z3_probe_le(Z3_context c, Z3_probe p1, Z3_probe p2);
Z3_probe       Z3_probe_gt(Z3_context c, Z3_probe p1, Z3_probe p2);
Z3_probe       Z3_probe_ge(Z3_context c, Z3_probe p1, Z3_probe p2);
Z3_probe       Z3_probe_eq(Z3_context c, Z3_probe p1, Z3_probe p2);
Z3_probe       Z3_probe_and(Z3_context c, Z3_probe p1, Z3_probe p2);
Z3_probe       Z3_probe_or(Z3_context c, Z3_probe p1, Z3_probe p2);
Z3_probe       Z3_probe_not(Z3_context c, Z3_probe p);
double         Z3_probe_apply(Z3_context c, Z3_probe p, Z3_goal g);
unsigned int   Z3_get_num_probes(Z3_context c);
Z3_string      Z3_get_probe_name(Z3_context c, unsigned int i);
Z3_string      Z3_probe_get_descr(Z3_context c, Z3_string name);

// ============================================================================
// Fixedpoint (CHC / Datalog) — backed by AY's ay-chc Spacer-class engine
// ============================================================================
//
// Declare relations, add Horn rules, and query reachability. CHC is solved by
// AY's proof-validated CHC portfolio (the same engine the ay CLI uses for HORN
// inputs); there is no hard-coded answer.
//
// QUERY POLARITY (matches Z3 exactly, INVERSE of SMT-LIB HORN sat/unsat):
//   Z3_fixedpoint_query returns Z3_L_TRUE  if the query is REACHABLE (UNSAFE),
//                               Z3_L_FALSE if it is UNREACHABLE (SAFE),
//                               Z3_L_UNDEF if inconclusive / untranslatable.
//
// A rule is typically (forall vars (=> body head)), a fact, or a bare relation
// head. The query is the goal whose reachability is tested (a relation
// application, possibly conjoined with constraints). The translator covers the
// LIA/LRA/Bool transition-system fragment; an untranslatable rule/query yields
// Z3_L_UNDEF rather than a wrong verdict.

Z3_fixedpoint Z3_mk_fixedpoint(Z3_context c);
void          Z3_fixedpoint_inc_ref(Z3_context c, Z3_fixedpoint d);
void          Z3_fixedpoint_dec_ref(Z3_context c, Z3_fixedpoint d);
void          Z3_fixedpoint_register_relation(Z3_context c, Z3_fixedpoint d, Z3_func_decl f);
void          Z3_fixedpoint_add_rule(Z3_context c, Z3_fixedpoint d, Z3_ast rule,
                                     Z3_symbol name);
int           Z3_fixedpoint_query(Z3_context c, Z3_fixedpoint d, Z3_ast query);
Z3_string     Z3_fixedpoint_to_string(Z3_context c, Z3_fixedpoint d);
Z3_string     Z3_fixedpoint_get_answer(Z3_context c, Z3_fixedpoint d);

// ============================================================================
// Model
// ============================================================================

void          Z3_model_inc_ref(Z3_context c, Z3_model m);
void          Z3_model_dec_ref(Z3_context c, Z3_model m);
unsigned int  Z3_model_get_num_consts(Z3_context c, Z3_model m);
Z3_string     Z3_model_to_string(Z3_context c, Z3_model m);
Z3_func_decl  Z3_model_get_const_decl(Z3_context c, Z3_model m, unsigned int i);
Z3_ast        Z3_model_get_const_interp(Z3_context c, Z3_model m, Z3_func_decl a);
unsigned int  Z3_model_get_num_funcs(Z3_context c, Z3_model m);
bool          Z3_model_has_interp(Z3_context c, Z3_model m, Z3_func_decl d);
bool          Z3_model_eval(Z3_context c, Z3_model m, Z3_ast t, bool model_completion,
                            Z3_ast* v);
Z3_func_decl  Z3_model_get_func_decl(Z3_context c, Z3_model m, unsigned int i);
Z3_func_interp Z3_model_get_func_interp(Z3_context c, Z3_model m, Z3_func_decl f);
Z3_model      Z3_model_translate(Z3_context c, Z3_model m, Z3_context dst);
unsigned int  Z3_model_get_num_sorts(Z3_context c, Z3_model m);
Z3_sort       Z3_model_get_sort(Z3_context c, Z3_model m, unsigned int i);
Z3_ast_vector Z3_model_get_sort_universe(Z3_context c, Z3_model m, Z3_sort s);

// ============================================================================
// Function interpretations (arity > 0 model function tables)
// ============================================================================

void          Z3_func_interp_inc_ref(Z3_context c, Z3_func_interp f);
void          Z3_func_interp_dec_ref(Z3_context c, Z3_func_interp f);
unsigned int  Z3_func_interp_get_num_entries(Z3_context c, Z3_func_interp f);
Z3_func_entry Z3_func_interp_get_entry(Z3_context c, Z3_func_interp f, unsigned int i);
Z3_ast        Z3_func_interp_get_else(Z3_context c, Z3_func_interp f);
unsigned int  Z3_func_interp_get_arity(Z3_context c, Z3_func_interp f);
void          Z3_func_entry_inc_ref(Z3_context c, Z3_func_entry e);
void          Z3_func_entry_dec_ref(Z3_context c, Z3_func_entry e);
Z3_ast        Z3_func_entry_get_value(Z3_context c, Z3_func_entry e);
unsigned int  Z3_func_entry_get_num_args(Z3_context c, Z3_func_entry e);
Z3_ast        Z3_func_entry_get_arg(Z3_context c, Z3_func_entry e, unsigned int i);

// ============================================================================
// Parameters
// ============================================================================

Z3_params     Z3_mk_params(Z3_context c);
void          Z3_params_inc_ref(Z3_context c, Z3_params p);
void          Z3_params_dec_ref(Z3_context c, Z3_params p);
void          Z3_params_set_bool(Z3_context c, Z3_params p, Z3_symbol k, bool v);
void          Z3_params_set_uint(Z3_context c, Z3_params p, Z3_symbol k, unsigned int v);
void          Z3_params_set_double(Z3_context c, Z3_params p, Z3_symbol k, double v);
void          Z3_params_set_symbol(Z3_context c, Z3_params p, Z3_symbol k, Z3_symbol v);

// ============================================================================
// Algebraic Datatypes (constructors / recognizers / accessors)
// ============================================================================
//
// Multi-step Z3 datatype workflow:
//   1. Z3_mk_constructor builds a constructor DESCRIPTOR (caller-owned; free
//      with Z3_del_constructor). `sorts[i]` may be NULL to denote a sort
//      reference, with `sort_refs[i]` selecting the referenced datatype
//      (0 == the datatype under construction; i.e. a self/recursive reference).
//   2. Z3_mk_datatype creates the datatype sort, declares it, and fills each
//      descriptor's constructor/recognizer/accessor func_decls.
//   3. Z3_query_constructor reads those func_decls back out.
//   4. Apply them with Z3_mk_app to build constructor / (_ is C) / selector
//      terms.
//
// AY models a datatype as an uninterpreted sort with the constructor, the
// recognizer `is-C`, and the selectors as theory-backed functions, matching its
// SMT-LIB `declare-datatypes` elaboration. Self-recursive datatypes (e.g. List)
// are supported; mutually recursive datatypes (Z3_mk_datatypes with
// cross-datatype sort references) are NOT yet supported and are rejected
// (the out sort is left NULL and an error is recorded).
//
// The supplied `recognizer` symbol is accepted for API compatibility but the
// recognizer is canonically `is-<constructor>` in AY.

Z3_constructor      Z3_mk_constructor(Z3_context c, Z3_symbol name,
                                      Z3_symbol recognizer, unsigned int num_fields,
                                      const Z3_symbol* field_names,
                                      const Z3_sort* sorts,
                                      const unsigned int* sort_refs);
Z3_constructor_list Z3_mk_constructor_list(Z3_context c, unsigned int num_constructors,
                                           const Z3_constructor* constructors);
Z3_sort             Z3_mk_datatype(Z3_context c, Z3_symbol name,
                                   unsigned int num_constructors,
                                   Z3_constructor* constructors);
void                Z3_mk_datatypes(Z3_context c, unsigned int num_sorts,
                                    const Z3_symbol* sort_names, Z3_sort* sorts,
                                    const Z3_constructor_list* constructor_lists);
void                Z3_query_constructor(Z3_context c, Z3_constructor constr,
                                         unsigned int num_fields,
                                         Z3_func_decl* constructor,
                                         Z3_func_decl* tester,
                                         Z3_func_decl* accessors);
void                Z3_del_constructor(Z3_context c, Z3_constructor constr);
void                Z3_del_constructor_list(Z3_context c, Z3_constructor_list clist);

// Datatype sort introspection: read a datatype sort (as returned by
// Z3_mk_datatype) back out. Each getter returns REAL data — the func_decls are
// usable with Z3_mk_app. NOTE: the recognizer's decl NAME is `is-<ctor>` in AY
// (its canonical SMT-LIB form) vs `is` in libz3; both are arity-1 DT->Bool
// recognizers, so cross-check the recognizer by arity/range, not name.
unsigned int Z3_get_datatype_sort_num_constructors(Z3_context c, Z3_sort t);
Z3_func_decl Z3_get_datatype_sort_constructor(Z3_context c, Z3_sort t, unsigned int idx);
Z3_func_decl Z3_get_datatype_sort_recognizer(Z3_context c, Z3_sort t, unsigned int idx);
Z3_func_decl Z3_get_datatype_sort_constructor_accessor(Z3_context c, Z3_sort t,
                                                       unsigned int idx_c, unsigned int idx_a);

// Tuple introspection (group A): a "tuple" is a datatype sort with exactly one
// constructor (libz3's precondition too). num_fields is the field count of
// that constructor; field_decl(i) the i-th accessor (DT -> field sort);
// mk_decl the constructor ((fields...) -> DT). All decls are REAL and usable
// with Z3_mk_app. Non-tuples (incl. multi-constructor datatypes) get 0/NULL.
unsigned int Z3_get_tuple_sort_num_fields(Z3_context c, Z3_sort t);
Z3_func_decl Z3_get_tuple_sort_field_decl(Z3_context c, Z3_sort t, unsigned int i);
Z3_func_decl Z3_get_tuple_sort_mk_decl(Z3_context c, Z3_sort t);

// ============================================================================
// Incremental SMT-LIB2 Parser Context
// ============================================================================
//
// Z3_mk_parser_context creates a parser with a PERSISTENT symbol table: sorts
// and decls added via Z3_parser_context_add_sort / _add_decl, and declarations
// introduced by an earlier Z3_parser_context_from_string, stay in scope for
// later parses. Routes through AY's real SMT-LIB2 front-end
// (Solver::parse_smtlib2); the returned assertions are real terms interned in —
// and valid against — the parent Z3_context (inspect and solve them normally).
// AY has one solver per context, so the parser context threads its declarations
// into that context's shared symbol table (documented, honest). add_sort/add_decl
// report an error and do not record an entry when its declaration cannot be
// threaded. from_string uses the same destructive-control preflight and
// permanent late-error fail-closed transaction as the other solver parsers.

Z3_parser_context Z3_mk_parser_context(Z3_context c);
void          Z3_parser_context_inc_ref(Z3_context c, Z3_parser_context pc);
void          Z3_parser_context_dec_ref(Z3_context c, Z3_parser_context pc);
void          Z3_parser_context_add_sort(Z3_context c, Z3_parser_context pc, Z3_sort s);
void          Z3_parser_context_add_decl(Z3_context c, Z3_parser_context pc, Z3_func_decl f);
Z3_ast_vector Z3_parser_context_from_string(Z3_context c, Z3_parser_context pc, Z3_string s);

// ============================================================================
// SMT-LIB2 Parsing
// ============================================================================

// The assertion-returning parser bridge rejects push/pop/reset/reset-assertions
// before execution. A semantic execution error permanently poisons the context
// rather than exposing partially changed declarations/options or stale copied
// solver artifacts. String and file entrypoints share the same transaction.

Z3_ast_vector Z3_parse_smtlib2_string(Z3_context c, Z3_string str,
                                      unsigned int num_sorts,
                                      const Z3_symbol* sort_names,
                                      const Z3_sort* sorts,
                                      unsigned int num_decls,
                                      const Z3_symbol* decl_names,
                                      const Z3_func_decl* decls);
Z3_ast_vector Z3_parse_smtlib2_file(Z3_context c, Z3_string file_name,
                                    unsigned int num_sorts,
                                    const Z3_symbol* sort_names,
                                    const Z3_sort* sorts,
                                    unsigned int num_decls,
                                    const Z3_symbol* decl_names,
                                    const Z3_func_decl* decls);

// ============================================================================
// Real Closed Fields (z3_rcf.h surface)
// ============================================================================
//
// Exact symbolic arithmetic over Q extended by pi, e, one infinitesimal, and
// real algebraic roots. Every unsupported/uncomputable mixed operation raises
// an honest Z3_EXCEPTION (readable via Z3_get_error_msg) instead of guessing —
// see the documented divergences in the implementation.

void         Z3_rcf_del(Z3_context c, Z3_rcf_num a);
Z3_rcf_num   Z3_rcf_mk_rational(Z3_context c, Z3_string val);
Z3_rcf_num   Z3_rcf_mk_small_int(Z3_context c, int val);
Z3_rcf_num   Z3_rcf_mk_pi(Z3_context c);
Z3_rcf_num   Z3_rcf_mk_e(Z3_context c);
Z3_rcf_num   Z3_rcf_mk_infinitesimal(Z3_context c);
unsigned int Z3_rcf_mk_roots(Z3_context c, unsigned int n,
                             const Z3_rcf_num* a, Z3_rcf_num* roots);
Z3_rcf_num   Z3_rcf_add(Z3_context c, Z3_rcf_num a, Z3_rcf_num b);
Z3_rcf_num   Z3_rcf_sub(Z3_context c, Z3_rcf_num a, Z3_rcf_num b);
Z3_rcf_num   Z3_rcf_mul(Z3_context c, Z3_rcf_num a, Z3_rcf_num b);
Z3_rcf_num   Z3_rcf_div(Z3_context c, Z3_rcf_num a, Z3_rcf_num b);
Z3_rcf_num   Z3_rcf_neg(Z3_context c, Z3_rcf_num a);
Z3_rcf_num   Z3_rcf_inv(Z3_context c, Z3_rcf_num a);
Z3_rcf_num   Z3_rcf_power(Z3_context c, Z3_rcf_num a, unsigned int k);
bool         Z3_rcf_lt(Z3_context c, Z3_rcf_num a, Z3_rcf_num b);
bool         Z3_rcf_gt(Z3_context c, Z3_rcf_num a, Z3_rcf_num b);
bool         Z3_rcf_le(Z3_context c, Z3_rcf_num a, Z3_rcf_num b);
bool         Z3_rcf_ge(Z3_context c, Z3_rcf_num a, Z3_rcf_num b);
bool         Z3_rcf_eq(Z3_context c, Z3_rcf_num a, Z3_rcf_num b);
bool         Z3_rcf_neq(Z3_context c, Z3_rcf_num a, Z3_rcf_num b);
Z3_string    Z3_rcf_num_to_string(Z3_context c, Z3_rcf_num a, bool compact, bool html);
Z3_string    Z3_rcf_num_to_decimal_string(Z3_context c, Z3_rcf_num a, unsigned int prec);
void         Z3_rcf_get_numerator_denominator(Z3_context c, Z3_rcf_num a,
                                              Z3_rcf_num* n, Z3_rcf_num* d);
bool         Z3_rcf_is_rational(Z3_context c, Z3_rcf_num a);
bool         Z3_rcf_is_algebraic(Z3_context c, Z3_rcf_num a);
bool         Z3_rcf_is_infinitesimal(Z3_context c, Z3_rcf_num a);
bool         Z3_rcf_is_transcendental(Z3_context c, Z3_rcf_num a);
unsigned int Z3_rcf_extension_index(Z3_context c, Z3_rcf_num a);
Z3_symbol    Z3_rcf_transcendental_name(Z3_context c, Z3_rcf_num a);
Z3_symbol    Z3_rcf_infinitesimal_name(Z3_context c, Z3_rcf_num a);
unsigned int Z3_rcf_num_coefficients(Z3_context c, Z3_rcf_num a);
Z3_rcf_num   Z3_rcf_coefficient(Z3_context c, Z3_rcf_num a, unsigned int i);
int          Z3_rcf_interval(Z3_context c, Z3_rcf_num a,
                             bool* lower_is_inf, bool* lower_is_open, Z3_rcf_num* lower,
                             bool* upper_is_inf, bool* upper_is_open, Z3_rcf_num* upper);
unsigned int Z3_rcf_num_sign_conditions(Z3_context c, Z3_rcf_num a);
int          Z3_rcf_sign_condition_sign(Z3_context c, Z3_rcf_num a, unsigned int i);
unsigned int Z3_rcf_num_sign_condition_coefficients(Z3_context c, Z3_rcf_num a,
                                                    unsigned int i);
Z3_rcf_num   Z3_rcf_sign_condition_coefficient(Z3_context c, Z3_rcf_num a,
                                               unsigned int i, unsigned int j);

// ============================================================================
// Algebraic Numbers (z3_algebraic.h surface)
// ============================================================================
//
// Exact real algebraic arithmetic over ordinary numeral / algebraic-root AST
// handles. Non-value operands record Z3_INVALID_ARG; results the exact engine
// cannot compute record an honest error instead of a fabricated value.

bool          Z3_algebraic_is_value(Z3_context c, Z3_ast a);
int           Z3_algebraic_sign(Z3_context c, Z3_ast a);
bool          Z3_algebraic_is_pos(Z3_context c, Z3_ast a);
bool          Z3_algebraic_is_neg(Z3_context c, Z3_ast a);
bool          Z3_algebraic_is_zero(Z3_context c, Z3_ast a);
Z3_ast        Z3_algebraic_add(Z3_context c, Z3_ast a, Z3_ast b);
Z3_ast        Z3_algebraic_sub(Z3_context c, Z3_ast a, Z3_ast b);
Z3_ast        Z3_algebraic_mul(Z3_context c, Z3_ast a, Z3_ast b);
Z3_ast        Z3_algebraic_div(Z3_context c, Z3_ast a, Z3_ast b);
Z3_ast        Z3_algebraic_root(Z3_context c, Z3_ast a, unsigned int k);
Z3_ast        Z3_algebraic_power(Z3_context c, Z3_ast a, unsigned int k);
bool          Z3_algebraic_lt(Z3_context c, Z3_ast a, Z3_ast b);
bool          Z3_algebraic_gt(Z3_context c, Z3_ast a, Z3_ast b);
bool          Z3_algebraic_le(Z3_context c, Z3_ast a, Z3_ast b);
bool          Z3_algebraic_ge(Z3_context c, Z3_ast a, Z3_ast b);
bool          Z3_algebraic_eq(Z3_context c, Z3_ast a, Z3_ast b);
bool          Z3_algebraic_neq(Z3_context c, Z3_ast a, Z3_ast b);
Z3_ast_vector Z3_algebraic_roots(Z3_context c, Z3_ast p, unsigned int n, const Z3_ast* a);
int           Z3_algebraic_eval(Z3_context c, Z3_ast p, unsigned int n, const Z3_ast* a);
Z3_ast_vector Z3_algebraic_get_poly(Z3_context c, Z3_ast a);
unsigned int  Z3_algebraic_get_i(Z3_context c, Z3_ast a);

#ifdef __cplusplus
}
#endif

#endif // AY_Z3_COMPAT_H
