// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// AY C++ API (ay.hpp) — a header-only, z3++.h-style C++ wrapper over AY's
// Z3-shaped AY C API (crates/ay-ffi/include/ay_z3_compat.h).
//
// USAGE
//   #include "ay.hpp"          // pulls in ay_z3_compat.h (and ay.h)
//   using namespace ay;
//   context c;
//   expr x = c.int_const("x");
//   solver s(c);
//   s.add(x > 0 && x < 10);
//   if (s.check() == sat) { model m = s.get_model(); ... }
//
//   Link the consumer against libay_ffi (cdylib or staticlib), exactly as for
//   the C API.
//
// DESIGN / CORRECTNESS BOUNDARY
//   * This wrapper adds no independent solving logic or term-rewriting pass.
//     After it has encoded a request through Z3_* C entry points, AY's core
//     computes the verdict and model. Correctness still depends on selecting
//     the right entry points and preserving sorts, handles, ABI conventions,
//     and lifetimes at the wrapper boundary.
//   * Memory: a `context` owns its Z3_context and frees it in ~context via
//     Z3_del_context, which frees every sort/ast/solver/model derived from it
//     (matching AY's arena ownership). `Z3_ast` is a 64-bit arena-interned
//     handle that is never individually freed, so expr/sort/func_decl/model are
//     trivially copyable value handles — no per-AST reference counting is done
//     (the underlying context is a non-RC context, where inc/dec_ref are no-ops,
//     exactly as the C consumer test documents).
//   * Lifetime contract: handles (expr, sort, solver, model, ...) borrow their
//     context and must NOT outlive it — identical to z3++'s contract.
//   * Errors: constructors that the C API can fail (returning a null handle and
//     setting an error code) surface that as an `ay::exception` carrying the C
//     error message, so a C++ consumer never silently builds on a null term.

#ifndef AY_HPP
#define AY_HPP

#include "ay.h"
#include "ay_z3_compat.h"

#include <cstdint>
#include <stdexcept>
#include <string>
#include <vector>

namespace ay {

// ---------------------------------------------------------------------------
// Result of a satisfiability check (mirrors Z3_lbool / z3++ check_result).
// ---------------------------------------------------------------------------
enum check_result { unsat = 0, sat = 1, unknown = 2 };

// ---------------------------------------------------------------------------
// Exception carrying a C-API error message.
// ---------------------------------------------------------------------------
class exception : public std::runtime_error {
 public:
  explicit exception(const std::string& msg) : std::runtime_error(msg) {}
};

class context;
class sort;
class expr;
class func_decl;
class model;
class solver;

// ---------------------------------------------------------------------------
// config — owns a Z3_config; pass to a context to configure it.
// ---------------------------------------------------------------------------
class config {
  Z3_config cfg_;

 public:
  config() : cfg_(Z3_mk_config()) {}
  ~config() {
    if (cfg_) Z3_del_config(cfg_);
  }
  // Non-copyable, movable.
  config(const config&) = delete;
  config& operator=(const config&) = delete;
  config(config&& o) noexcept : cfg_(o.cfg_) { o.cfg_ = nullptr; }

  void set(const char* param, const char* value) {
    Z3_set_param_value(cfg_, param, value);
  }

  Z3_config get() const { return cfg_; }
};

// ---------------------------------------------------------------------------
// context — owns a Z3_context. The root of all handles; freeing it frees every
// sort/ast/solver/model created from it. Borrowed (by reference) everywhere.
// ---------------------------------------------------------------------------
class context {
  Z3_context ctx_;

  friend class sort;
  friend class expr;
  friend class func_decl;
  friend class model;
  friend class solver;

 public:
  context() {
    config cfg;
    ctx_ = Z3_mk_context(cfg.get());
  }
  explicit context(config& cfg) : ctx_(Z3_mk_context(cfg.get())) {}
  ~context() {
    if (ctx_) Z3_del_context(ctx_);
  }
  // Non-copyable, movable.
  context(const context&) = delete;
  context& operator=(const context&) = delete;
  context(context&& o) noexcept : ctx_(o.ctx_) { o.ctx_ = nullptr; }

  Z3_context get() const { return ctx_; }

  // Throw an ay::exception if the C API recorded an error, clearing nothing
  // (the C API keeps the last code). Used by fallible constructors.
  void check_error() const {
    unsigned code = Z3_get_error_code(ctx_);
    if (code != Z3_OK) {
      Z3_string msg = Z3_get_error_msg(ctx_, code);
      throw exception(msg ? std::string(msg)
                          : ("AY error code " + std::to_string(code)));
    }
  }

  // --- Sorts ---
  sort bool_sort();
  sort int_sort();
  sort real_sort();
  sort bv_sort(unsigned sz);
  sort array_sort(const sort& domain, const sort& range);
  sort uninterpreted_sort(const char* name);

  // --- Constants & literals ---
  expr bool_const(const char* name);
  expr int_const(const char* name);
  expr real_const(const char* name);
  expr bv_const(const char* name, unsigned sz);
  expr constant(const char* name, const sort& s);

  expr bool_val(bool b);
  expr int_val(int v);
  expr int_val(int64_t v);
  expr real_val(int num, int den);
  expr bv_val(int64_t v, unsigned sz);

  // --- Function declarations ---
  func_decl function(const char* name, const std::vector<sort>& domain,
                     const sort& range);

  // --- Variadic boolean/arith combinators (mirror z3++ free functions) ---
  expr bool_const_array_and(const std::vector<expr>& args);
};

// ---------------------------------------------------------------------------
// sort — a value handle to a Z3_sort (borrows its context).
// ---------------------------------------------------------------------------
class sort {
  context* ctx_;
  Z3_sort sort_;

  friend class context;
  friend class expr;
  friend class func_decl;

 public:
  sort(context& c, Z3_sort s) : ctx_(&c), sort_(s) {}

  context& ctx() const { return *ctx_; }
  Z3_sort get() const { return sort_; }

  unsigned kind() const { return Z3_get_sort_kind(ctx_->get(), sort_); }
  bool is_bool() const { return kind() == Z3_BOOL_SORT; }
  bool is_int() const { return kind() == Z3_INT_SORT; }
  bool is_real() const { return kind() == Z3_REAL_SORT; }
  bool is_bv() const { return kind() == Z3_BV_SORT; }
  bool is_array() const { return kind() == Z3_ARRAY_SORT; }

  unsigned bv_size() const { return Z3_get_bv_sort_size(ctx_->get(), sort_); }

  std::string to_string() const {
    Z3_string s = Z3_sort_to_string(ctx_->get(), sort_);
    return s ? std::string(s) : std::string();
  }

  bool operator==(const sort& o) const {
    return Z3_is_eq_sort(ctx_->get(), sort_, o.sort_);
  }
  bool operator!=(const sort& o) const { return !(*this == o); }
};

// ---------------------------------------------------------------------------
// func_decl — a value handle to a Z3_func_decl. Call with operator() to build
// applications (z3++ style).
// ---------------------------------------------------------------------------
class func_decl {
  context* ctx_;
  Z3_func_decl decl_;

  friend class context;

 public:
  func_decl(context& c, Z3_func_decl d) : ctx_(&c), decl_(d) {}

  context& ctx() const { return *ctx_; }
  Z3_func_decl get() const { return decl_; }

  unsigned arity() const { return Z3_get_arity(ctx_->get(), decl_); }

  // Application: f(args...).
  expr operator()(const std::vector<expr>& args) const;
  expr operator()() const;
  expr operator()(const expr& a) const;
  expr operator()(const expr& a, const expr& b) const;

  std::string to_string() const {
    Z3_string s = Z3_func_decl_to_string(ctx_->get(), decl_);
    return s ? std::string(s) : std::string();
  }
};

// ---------------------------------------------------------------------------
// expr — a value handle to a Z3_ast (borrows its context). The workhorse type;
// carries operator overloads for the common SMT operators.
// ---------------------------------------------------------------------------
class expr {
  context* ctx_;
  Z3_ast ast_;

  friend class context;
  friend class func_decl;
  friend class model;
  friend class solver;

 public:
  // Helper: throw if a builder returned the null AST after setting an error.
  // Public so the free combinator functions below can reuse it.
  static Z3_ast checked(context& c, Z3_ast a) {
    if (a == 0) c.check_error();
    return a;
  }

  expr(context& c, Z3_ast a) : ctx_(&c), ast_(a) {}

  context& ctx() const { return *ctx_; }
  Z3_ast get() const { return ast_; }

  sort get_sort() const {
    return sort(*ctx_, Z3_get_sort(ctx_->get(), ast_));
  }

  bool is_bool() const { return get_sort().is_bool(); }
  bool is_int() const { return get_sort().is_int(); }
  bool is_real() const { return get_sort().is_real(); }
  bool is_bv() const { return get_sort().is_bv(); }

  bool is_numeral() const { return Z3_is_numeral_ast(ctx_->get(), ast_); }

  // Numeric readout (only meaningful on a numeral). Returns false if the term
  // is not an integer numeral that fits, matching the C accessor's contract.
  bool as_int64(int64_t* out) const {
    return Z3_get_numeral_int64(ctx_->get(), ast_, out);
  }
  // Boolean value of a constant-folded term: Z3_L_TRUE / Z3_L_FALSE / undef.
  int bool_value() const { return Z3_get_bool_value(ctx_->get(), ast_); }

  std::string to_string() const {
    Z3_string s = Z3_ast_to_string(ctx_->get(), ast_);
    return s ? std::string(s) : std::string();
  }

  // Structural identity (hash-consed terms share a handle). Named, not an
  // operator: in z3++ `a == b` builds an *equality term* (see the free
  // operator== below), so structural identity gets its own method to avoid
  // overload ambiguity / silently meaning the wrong thing.
  bool eq_ast(const expr& o) const {
    return Z3_is_eq_ast(ctx_->get(), ast_, o.ast_);
  }

  // --- arithmetic operators (build terms) ---
  expr operator+(const expr& o) const {
    Z3_ast args[2] = {ast_, o.ast_};
    return expr(*ctx_, checked(*ctx_, Z3_mk_add(ctx_->get(), 2, args)));
  }
  expr operator-(const expr& o) const {
    Z3_ast args[2] = {ast_, o.ast_};
    return expr(*ctx_, checked(*ctx_, Z3_mk_sub(ctx_->get(), 2, args)));
  }
  expr operator*(const expr& o) const {
    Z3_ast args[2] = {ast_, o.ast_};
    return expr(*ctx_, checked(*ctx_, Z3_mk_mul(ctx_->get(), 2, args)));
  }
  expr operator/(const expr& o) const {
    return expr(*ctx_,
                checked(*ctx_, Z3_mk_div(ctx_->get(), ast_, o.ast_)));
  }
  expr operator-() const {  // unary minus
    return expr(*ctx_, checked(*ctx_, Z3_mk_unary_minus(ctx_->get(), ast_)));
  }

  // --- comparison operators (build Bool terms) ---
  expr operator<(const expr& o) const {
    return expr(*ctx_, checked(*ctx_, Z3_mk_lt(ctx_->get(), ast_, o.ast_)));
  }
  expr operator<=(const expr& o) const {
    return expr(*ctx_, checked(*ctx_, Z3_mk_le(ctx_->get(), ast_, o.ast_)));
  }
  expr operator>(const expr& o) const {
    return expr(*ctx_, checked(*ctx_, Z3_mk_gt(ctx_->get(), ast_, o.ast_)));
  }
  expr operator>=(const expr& o) const {
    return expr(*ctx_, checked(*ctx_, Z3_mk_ge(ctx_->get(), ast_, o.ast_)));
  }

  // --- boolean operators (build Bool terms) ---
  expr operator&&(const expr& o) const {
    Z3_ast args[2] = {ast_, o.ast_};
    return expr(*ctx_, checked(*ctx_, Z3_mk_and(ctx_->get(), 2, args)));
  }
  expr operator||(const expr& o) const {
    Z3_ast args[2] = {ast_, o.ast_};
    return expr(*ctx_, checked(*ctx_, Z3_mk_or(ctx_->get(), 2, args)));
  }
  expr operator!() const {
    return expr(*ctx_, checked(*ctx_, Z3_mk_not(ctx_->get(), ast_)));
  }

  // --- bitvector operators (build BV terms) ---
  expr operator&(const expr& o) const {
    return expr(*ctx_, checked(*ctx_, Z3_mk_bvand(ctx_->get(), ast_, o.ast_)));
  }
  expr operator|(const expr& o) const {
    return expr(*ctx_, checked(*ctx_, Z3_mk_bvor(ctx_->get(), ast_, o.ast_)));
  }
  expr operator^(const expr& o) const {
    return expr(*ctx_, checked(*ctx_, Z3_mk_bvxor(ctx_->get(), ast_, o.ast_)));
  }
};

// --- free functions building Bool/term combinators (z3++ style) ---

inline expr operator==(const expr& a, const expr& b) {
  return expr(a.ctx(),
              expr::checked(a.ctx(),
                            Z3_mk_eq(a.ctx().get(), a.get(), b.get())));
}
inline expr operator!=(const expr& a, const expr& b) {
  return !(a == b);
}

inline expr implies(const expr& a, const expr& b) {
  return expr(a.ctx(), expr::checked(a.ctx(), Z3_mk_implies(a.ctx().get(),
                                                            a.get(), b.get())));
}
inline expr ite(const expr& cond, const expr& t, const expr& e) {
  return expr(cond.ctx(),
              expr::checked(cond.ctx(),
                            Z3_mk_ite(cond.ctx().get(), cond.get(), t.get(),
                                      e.get())));
}
inline expr distinct(const std::vector<expr>& args) {
  if (args.empty()) throw exception("distinct requires >= 1 argument");
  context& c = args.front().ctx();
  std::vector<Z3_ast> raw;
  raw.reserve(args.size());
  for (const auto& a : args) raw.push_back(a.get());
  return expr(c, expr::checked(c, Z3_mk_distinct(c.get(),
                                                 (unsigned)raw.size(),
                                                 raw.data())));
}
inline expr mk_and(const std::vector<expr>& args) {
  if (args.empty()) throw exception("mk_and requires >= 1 argument");
  context& c = args.front().ctx();
  std::vector<Z3_ast> raw;
  raw.reserve(args.size());
  for (const auto& a : args) raw.push_back(a.get());
  return expr(c, expr::checked(c, Z3_mk_and(c.get(), (unsigned)raw.size(),
                                            raw.data())));
}
inline expr mk_or(const std::vector<expr>& args) {
  if (args.empty()) throw exception("mk_or requires >= 1 argument");
  context& c = args.front().ctx();
  std::vector<Z3_ast> raw;
  raw.reserve(args.size());
  for (const auto& a : args) raw.push_back(a.get());
  return expr(c, expr::checked(c, Z3_mk_or(c.get(), (unsigned)raw.size(),
                                           raw.data())));
}

// Array select / store.
inline expr select(const expr& a, const expr& i) {
  return expr(a.ctx(),
              expr::checked(a.ctx(),
                            Z3_mk_select(a.ctx().get(), a.get(), i.get())));
}
inline expr store(const expr& a, const expr& i, const expr& v) {
  return expr(a.ctx(),
              expr::checked(a.ctx(),
                            Z3_mk_store(a.ctx().get(), a.get(), i.get(),
                                        v.get())));
}

// ---------------------------------------------------------------------------
// model — a value handle to a Z3_model. Evaluate terms against it.
// ---------------------------------------------------------------------------
class model {
  context* ctx_;
  Z3_model model_;

  friend class solver;

 public:
  model(context& c, Z3_model m) : ctx_(&c), model_(m) {}

  context& ctx() const { return *ctx_; }
  Z3_model get() const { return model_; }
  bool valid() const { return model_ != nullptr; }

  unsigned num_consts() const {
    return Z3_model_get_num_consts(ctx_->get(), model_);
  }

  // Evaluate `t`. With model_completion, unconstrained terms get a default.
  // Throws ay::exception if evaluation fails (matches Z3_model_eval's bool).
  expr eval(const expr& t, bool model_completion = true) const {
    Z3_ast out = 0;
    bool ok = Z3_model_eval(ctx_->get(), model_, t.get(), model_completion,
                            &out);
    if (!ok) throw exception("model evaluation failed");
    return expr(*ctx_, out);
  }

  std::string to_string() const {
    Z3_string s = Z3_model_to_string(ctx_->get(), model_);
    return s ? std::string(s) : std::string();
  }
};

// ---------------------------------------------------------------------------
// solver — a value handle to a Z3_solver. add/check/get_model/push/pop.
// ---------------------------------------------------------------------------
class solver {
  context* ctx_;
  Z3_solver solver_;

 public:
  explicit solver(context& c)
      : ctx_(&c), solver_(Z3_mk_solver(c.get())) {}

  context& ctx() const { return *ctx_; }
  Z3_solver get() const { return solver_; }

  void add(const expr& e) { Z3_solver_assert(ctx_->get(), solver_, e.get()); }
  void reset() { Z3_solver_reset(ctx_->get(), solver_); }
  void push() { Z3_solver_push(ctx_->get(), solver_); }
  void pop(unsigned n = 1) { Z3_solver_pop(ctx_->get(), solver_, n); }

  check_result check() {
    int r = Z3_solver_check(ctx_->get(), solver_);
    if (r == Z3_L_TRUE) return sat;
    if (r == Z3_L_FALSE) return unsat;
    return unknown;
  }

  check_result check(const std::vector<expr>& assumptions) {
    std::vector<Z3_ast> raw;
    raw.reserve(assumptions.size());
    for (const auto& a : assumptions) raw.push_back(a.get());
    int r = Z3_solver_check_assumptions(ctx_->get(), solver_,
                                        (unsigned)raw.size(), raw.data());
    if (r == Z3_L_TRUE) return sat;
    if (r == Z3_L_FALSE) return unsat;
    return unknown;
  }

  model get_model() {
    return model(*ctx_, Z3_solver_get_model(ctx_->get(), solver_));
  }

  std::string to_string() const {
    Z3_string s = Z3_solver_to_string(ctx_->get(), solver_);
    return s ? std::string(s) : std::string();
  }
};

// ===========================================================================
// context member definitions (deferred until sort/expr/func_decl are complete).
// ===========================================================================

inline sort context::bool_sort() { return sort(*this, Z3_mk_bool_sort(ctx_)); }
inline sort context::int_sort() { return sort(*this, Z3_mk_int_sort(ctx_)); }
inline sort context::real_sort() { return sort(*this, Z3_mk_real_sort(ctx_)); }
inline sort context::bv_sort(unsigned sz) {
  return sort(*this, Z3_mk_bv_sort(ctx_, sz));
}
inline sort context::array_sort(const sort& domain, const sort& range) {
  return sort(*this, Z3_mk_array_sort(ctx_, domain.get(), range.get()));
}
inline sort context::uninterpreted_sort(const char* name) {
  Z3_symbol s = Z3_mk_string_symbol(ctx_, name);
  return sort(*this, Z3_mk_uninterpreted_sort(ctx_, s));
}

inline expr context::constant(const char* name, const sort& s) {
  Z3_symbol sym = Z3_mk_string_symbol(ctx_, name);
  return expr(*this, expr::checked(*this, Z3_mk_const(ctx_, sym, s.get())));
}
inline expr context::bool_const(const char* name) {
  return constant(name, bool_sort());
}
inline expr context::int_const(const char* name) {
  return constant(name, int_sort());
}
inline expr context::real_const(const char* name) {
  return constant(name, real_sort());
}
inline expr context::bv_const(const char* name, unsigned sz) {
  return constant(name, bv_sort(sz));
}

inline expr context::bool_val(bool b) {
  return expr(*this, b ? Z3_mk_true(ctx_) : Z3_mk_false(ctx_));
}
inline expr context::int_val(int v) {
  return expr(*this, expr::checked(*this, Z3_mk_int(ctx_, v,
                                                    int_sort().get())));
}
inline expr context::int_val(int64_t v) {
  return expr(*this, expr::checked(*this, Z3_mk_int64(ctx_, v,
                                                      int_sort().get())));
}
inline expr context::real_val(int num, int den) {
  return expr(*this, expr::checked(*this, Z3_mk_real(ctx_, num, den)));
}
inline expr context::bv_val(int64_t v, unsigned sz) {
  return expr(*this, expr::checked(*this, Z3_mk_int64(ctx_, v,
                                                      bv_sort(sz).get())));
}

inline func_decl context::function(const char* name,
                                   const std::vector<sort>& domain,
                                   const sort& range) {
  Z3_symbol sym = Z3_mk_string_symbol(ctx_, name);
  std::vector<Z3_sort> dom;
  dom.reserve(domain.size());
  for (const auto& d : domain) dom.push_back(d.get());
  Z3_func_decl d = Z3_mk_func_decl(ctx_, sym, (unsigned)dom.size(),
                                   dom.empty() ? nullptr : dom.data(),
                                   range.get());
  if (d == nullptr) check_error();
  return func_decl(*this, d);
}

// ---------------------------------------------------------------------------
// func_decl application definitions (deferred until expr is complete).
// ---------------------------------------------------------------------------
inline expr func_decl::operator()(const std::vector<expr>& args) const {
  std::vector<Z3_ast> raw;
  raw.reserve(args.size());
  for (const auto& a : args) raw.push_back(a.get());
  Z3_ast r = Z3_mk_app(ctx_->get(), decl_, (unsigned)raw.size(),
                       raw.empty() ? nullptr : raw.data());
  return expr(*ctx_, expr::checked(*ctx_, r));
}
inline expr func_decl::operator()() const {
  return (*this)(std::vector<expr>{});
}
inline expr func_decl::operator()(const expr& a) const {
  return (*this)(std::vector<expr>{a});
}
inline expr func_decl::operator()(const expr& a, const expr& b) const {
  return (*this)(std::vector<expr>{a, b});
}

}  // namespace ay

#endif  // AY_HPP
