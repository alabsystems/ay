// Generated from Z3 5.0.0 commit 8e3402b215a810a4154eb183a7dfc4e853eb2f52.
// Canonical declaration manifest SHA-256: d4447ff654fd3b6bc6102d8e4959c5f12fb3b0d643f85bd7c4262167130ba2a0
// Do not hand-edit; z3_abi_500.rs authenticates the source header graph.
#include "z3.h"

typedef void (*ay_sig_Z3_add_const_interp)(Z3_context, Z3_model, Z3_func_decl, Z3_ast);
ay_sig_Z3_add_const_interp const ay_link_Z3_add_const_interp = &Z3_add_const_interp;
void ay_call_Z3_add_const_interp(Z3_context ay_a0, Z3_model ay_a1, Z3_func_decl ay_a2, Z3_ast ay_a3) {
    Z3_add_const_interp(ay_a0, ay_a1, ay_a2, ay_a3);
}

typedef Z3_func_interp (*ay_sig_Z3_add_func_interp)(Z3_context, Z3_model, Z3_func_decl, Z3_ast);
ay_sig_Z3_add_func_interp const ay_link_Z3_add_func_interp = &Z3_add_func_interp;
Z3_func_interp ay_call_Z3_add_func_interp(Z3_context ay_a0, Z3_model ay_a1, Z3_func_decl ay_a2, Z3_ast ay_a3) {
    return Z3_add_func_interp(ay_a0, ay_a1, ay_a2, ay_a3);
}

typedef void (*ay_sig_Z3_add_rec_def)(Z3_context, Z3_func_decl, unsigned int, Z3_ast *, Z3_ast);
ay_sig_Z3_add_rec_def const ay_link_Z3_add_rec_def = &Z3_add_rec_def;
void ay_call_Z3_add_rec_def(Z3_context ay_a0, Z3_func_decl ay_a1, unsigned int ay_a2, Z3_ast * ay_a3, Z3_ast ay_a4) {
    Z3_add_rec_def(ay_a0, ay_a1, ay_a2, ay_a3, ay_a4);
}

typedef Z3_ast (*ay_sig_Z3_algebraic_add)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_algebraic_add const ay_link_Z3_algebraic_add = &Z3_algebraic_add;
Z3_ast ay_call_Z3_algebraic_add(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_algebraic_add(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_algebraic_div)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_algebraic_div const ay_link_Z3_algebraic_div = &Z3_algebraic_div;
Z3_ast ay_call_Z3_algebraic_div(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_algebraic_div(ay_a0, ay_a1, ay_a2);
}

typedef bool (*ay_sig_Z3_algebraic_eq)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_algebraic_eq const ay_link_Z3_algebraic_eq = &Z3_algebraic_eq;
bool ay_call_Z3_algebraic_eq(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_algebraic_eq(ay_a0, ay_a1, ay_a2);
}

typedef int (*ay_sig_Z3_algebraic_eval)(Z3_context, Z3_ast, unsigned int, Z3_ast *);
ay_sig_Z3_algebraic_eval const ay_link_Z3_algebraic_eval = &Z3_algebraic_eval;
int ay_call_Z3_algebraic_eval(Z3_context ay_a0, Z3_ast ay_a1, unsigned int ay_a2, Z3_ast * ay_a3) {
    return Z3_algebraic_eval(ay_a0, ay_a1, ay_a2, ay_a3);
}

typedef unsigned int (*ay_sig_Z3_algebraic_get_i)(Z3_context, Z3_ast);
ay_sig_Z3_algebraic_get_i const ay_link_Z3_algebraic_get_i = &Z3_algebraic_get_i;
unsigned int ay_call_Z3_algebraic_get_i(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_algebraic_get_i(ay_a0, ay_a1);
}

typedef Z3_ast_vector (*ay_sig_Z3_algebraic_get_poly)(Z3_context, Z3_ast);
ay_sig_Z3_algebraic_get_poly const ay_link_Z3_algebraic_get_poly = &Z3_algebraic_get_poly;
Z3_ast_vector ay_call_Z3_algebraic_get_poly(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_algebraic_get_poly(ay_a0, ay_a1);
}

typedef bool (*ay_sig_Z3_algebraic_ge)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_algebraic_ge const ay_link_Z3_algebraic_ge = &Z3_algebraic_ge;
bool ay_call_Z3_algebraic_ge(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_algebraic_ge(ay_a0, ay_a1, ay_a2);
}

typedef bool (*ay_sig_Z3_algebraic_gt)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_algebraic_gt const ay_link_Z3_algebraic_gt = &Z3_algebraic_gt;
bool ay_call_Z3_algebraic_gt(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_algebraic_gt(ay_a0, ay_a1, ay_a2);
}

typedef bool (*ay_sig_Z3_algebraic_is_neg)(Z3_context, Z3_ast);
ay_sig_Z3_algebraic_is_neg const ay_link_Z3_algebraic_is_neg = &Z3_algebraic_is_neg;
bool ay_call_Z3_algebraic_is_neg(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_algebraic_is_neg(ay_a0, ay_a1);
}

typedef bool (*ay_sig_Z3_algebraic_is_pos)(Z3_context, Z3_ast);
ay_sig_Z3_algebraic_is_pos const ay_link_Z3_algebraic_is_pos = &Z3_algebraic_is_pos;
bool ay_call_Z3_algebraic_is_pos(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_algebraic_is_pos(ay_a0, ay_a1);
}

typedef bool (*ay_sig_Z3_algebraic_is_value)(Z3_context, Z3_ast);
ay_sig_Z3_algebraic_is_value const ay_link_Z3_algebraic_is_value = &Z3_algebraic_is_value;
bool ay_call_Z3_algebraic_is_value(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_algebraic_is_value(ay_a0, ay_a1);
}

typedef bool (*ay_sig_Z3_algebraic_is_zero)(Z3_context, Z3_ast);
ay_sig_Z3_algebraic_is_zero const ay_link_Z3_algebraic_is_zero = &Z3_algebraic_is_zero;
bool ay_call_Z3_algebraic_is_zero(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_algebraic_is_zero(ay_a0, ay_a1);
}

typedef bool (*ay_sig_Z3_algebraic_le)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_algebraic_le const ay_link_Z3_algebraic_le = &Z3_algebraic_le;
bool ay_call_Z3_algebraic_le(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_algebraic_le(ay_a0, ay_a1, ay_a2);
}

typedef bool (*ay_sig_Z3_algebraic_lt)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_algebraic_lt const ay_link_Z3_algebraic_lt = &Z3_algebraic_lt;
bool ay_call_Z3_algebraic_lt(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_algebraic_lt(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_algebraic_mul)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_algebraic_mul const ay_link_Z3_algebraic_mul = &Z3_algebraic_mul;
Z3_ast ay_call_Z3_algebraic_mul(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_algebraic_mul(ay_a0, ay_a1, ay_a2);
}

typedef bool (*ay_sig_Z3_algebraic_neq)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_algebraic_neq const ay_link_Z3_algebraic_neq = &Z3_algebraic_neq;
bool ay_call_Z3_algebraic_neq(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_algebraic_neq(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_algebraic_power)(Z3_context, Z3_ast, unsigned int);
ay_sig_Z3_algebraic_power const ay_link_Z3_algebraic_power = &Z3_algebraic_power;
Z3_ast ay_call_Z3_algebraic_power(Z3_context ay_a0, Z3_ast ay_a1, unsigned int ay_a2) {
    return Z3_algebraic_power(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast_vector (*ay_sig_Z3_algebraic_roots)(Z3_context, Z3_ast, unsigned int, Z3_ast *);
ay_sig_Z3_algebraic_roots const ay_link_Z3_algebraic_roots = &Z3_algebraic_roots;
Z3_ast_vector ay_call_Z3_algebraic_roots(Z3_context ay_a0, Z3_ast ay_a1, unsigned int ay_a2, Z3_ast * ay_a3) {
    return Z3_algebraic_roots(ay_a0, ay_a1, ay_a2, ay_a3);
}

typedef Z3_ast (*ay_sig_Z3_algebraic_root)(Z3_context, Z3_ast, unsigned int);
ay_sig_Z3_algebraic_root const ay_link_Z3_algebraic_root = &Z3_algebraic_root;
Z3_ast ay_call_Z3_algebraic_root(Z3_context ay_a0, Z3_ast ay_a1, unsigned int ay_a2) {
    return Z3_algebraic_root(ay_a0, ay_a1, ay_a2);
}

typedef int (*ay_sig_Z3_algebraic_sign)(Z3_context, Z3_ast);
ay_sig_Z3_algebraic_sign const ay_link_Z3_algebraic_sign = &Z3_algebraic_sign;
int ay_call_Z3_algebraic_sign(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_algebraic_sign(ay_a0, ay_a1);
}

typedef Z3_ast (*ay_sig_Z3_algebraic_sub)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_algebraic_sub const ay_link_Z3_algebraic_sub = &Z3_algebraic_sub;
Z3_ast ay_call_Z3_algebraic_sub(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_algebraic_sub(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_app_to_ast)(Z3_context, Z3_app);
ay_sig_Z3_app_to_ast const ay_link_Z3_app_to_ast = &Z3_app_to_ast;
Z3_ast ay_call_Z3_app_to_ast(Z3_context ay_a0, Z3_app ay_a1) {
    return Z3_app_to_ast(ay_a0, ay_a1);
}

typedef void (*ay_sig_Z3_append_log)(Z3_string);
ay_sig_Z3_append_log const ay_link_Z3_append_log = &Z3_append_log;
void ay_call_Z3_append_log(Z3_string ay_a0) {
    Z3_append_log(ay_a0);
}

typedef void (*ay_sig_Z3_apply_result_dec_ref)(Z3_context, Z3_apply_result);
ay_sig_Z3_apply_result_dec_ref const ay_link_Z3_apply_result_dec_ref = &Z3_apply_result_dec_ref;
void ay_call_Z3_apply_result_dec_ref(Z3_context ay_a0, Z3_apply_result ay_a1) {
    Z3_apply_result_dec_ref(ay_a0, ay_a1);
}

typedef unsigned int (*ay_sig_Z3_apply_result_get_num_subgoals)(Z3_context, Z3_apply_result);
ay_sig_Z3_apply_result_get_num_subgoals const ay_link_Z3_apply_result_get_num_subgoals = &Z3_apply_result_get_num_subgoals;
unsigned int ay_call_Z3_apply_result_get_num_subgoals(Z3_context ay_a0, Z3_apply_result ay_a1) {
    return Z3_apply_result_get_num_subgoals(ay_a0, ay_a1);
}

typedef Z3_goal (*ay_sig_Z3_apply_result_get_subgoal)(Z3_context, Z3_apply_result, unsigned int);
ay_sig_Z3_apply_result_get_subgoal const ay_link_Z3_apply_result_get_subgoal = &Z3_apply_result_get_subgoal;
Z3_goal ay_call_Z3_apply_result_get_subgoal(Z3_context ay_a0, Z3_apply_result ay_a1, unsigned int ay_a2) {
    return Z3_apply_result_get_subgoal(ay_a0, ay_a1, ay_a2);
}

typedef void (*ay_sig_Z3_apply_result_inc_ref)(Z3_context, Z3_apply_result);
ay_sig_Z3_apply_result_inc_ref const ay_link_Z3_apply_result_inc_ref = &Z3_apply_result_inc_ref;
void ay_call_Z3_apply_result_inc_ref(Z3_context ay_a0, Z3_apply_result ay_a1) {
    Z3_apply_result_inc_ref(ay_a0, ay_a1);
}

typedef Z3_string (*ay_sig_Z3_apply_result_to_string)(Z3_context, Z3_apply_result);
ay_sig_Z3_apply_result_to_string const ay_link_Z3_apply_result_to_string = &Z3_apply_result_to_string;
Z3_string ay_call_Z3_apply_result_to_string(Z3_context ay_a0, Z3_apply_result ay_a1) {
    return Z3_apply_result_to_string(ay_a0, ay_a1);
}

typedef bool (*ay_sig_Z3_ast_map_contains)(Z3_context, Z3_ast_map, Z3_ast);
ay_sig_Z3_ast_map_contains const ay_link_Z3_ast_map_contains = &Z3_ast_map_contains;
bool ay_call_Z3_ast_map_contains(Z3_context ay_a0, Z3_ast_map ay_a1, Z3_ast ay_a2) {
    return Z3_ast_map_contains(ay_a0, ay_a1, ay_a2);
}

typedef void (*ay_sig_Z3_ast_map_dec_ref)(Z3_context, Z3_ast_map);
ay_sig_Z3_ast_map_dec_ref const ay_link_Z3_ast_map_dec_ref = &Z3_ast_map_dec_ref;
void ay_call_Z3_ast_map_dec_ref(Z3_context ay_a0, Z3_ast_map ay_a1) {
    Z3_ast_map_dec_ref(ay_a0, ay_a1);
}

typedef void (*ay_sig_Z3_ast_map_erase)(Z3_context, Z3_ast_map, Z3_ast);
ay_sig_Z3_ast_map_erase const ay_link_Z3_ast_map_erase = &Z3_ast_map_erase;
void ay_call_Z3_ast_map_erase(Z3_context ay_a0, Z3_ast_map ay_a1, Z3_ast ay_a2) {
    Z3_ast_map_erase(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_ast_map_find)(Z3_context, Z3_ast_map, Z3_ast);
ay_sig_Z3_ast_map_find const ay_link_Z3_ast_map_find = &Z3_ast_map_find;
Z3_ast ay_call_Z3_ast_map_find(Z3_context ay_a0, Z3_ast_map ay_a1, Z3_ast ay_a2) {
    return Z3_ast_map_find(ay_a0, ay_a1, ay_a2);
}

typedef void (*ay_sig_Z3_ast_map_inc_ref)(Z3_context, Z3_ast_map);
ay_sig_Z3_ast_map_inc_ref const ay_link_Z3_ast_map_inc_ref = &Z3_ast_map_inc_ref;
void ay_call_Z3_ast_map_inc_ref(Z3_context ay_a0, Z3_ast_map ay_a1) {
    Z3_ast_map_inc_ref(ay_a0, ay_a1);
}

typedef void (*ay_sig_Z3_ast_map_insert)(Z3_context, Z3_ast_map, Z3_ast, Z3_ast);
ay_sig_Z3_ast_map_insert const ay_link_Z3_ast_map_insert = &Z3_ast_map_insert;
void ay_call_Z3_ast_map_insert(Z3_context ay_a0, Z3_ast_map ay_a1, Z3_ast ay_a2, Z3_ast ay_a3) {
    Z3_ast_map_insert(ay_a0, ay_a1, ay_a2, ay_a3);
}

typedef Z3_ast_vector (*ay_sig_Z3_ast_map_keys)(Z3_context, Z3_ast_map);
ay_sig_Z3_ast_map_keys const ay_link_Z3_ast_map_keys = &Z3_ast_map_keys;
Z3_ast_vector ay_call_Z3_ast_map_keys(Z3_context ay_a0, Z3_ast_map ay_a1) {
    return Z3_ast_map_keys(ay_a0, ay_a1);
}

typedef void (*ay_sig_Z3_ast_map_reset)(Z3_context, Z3_ast_map);
ay_sig_Z3_ast_map_reset const ay_link_Z3_ast_map_reset = &Z3_ast_map_reset;
void ay_call_Z3_ast_map_reset(Z3_context ay_a0, Z3_ast_map ay_a1) {
    Z3_ast_map_reset(ay_a0, ay_a1);
}

typedef unsigned int (*ay_sig_Z3_ast_map_size)(Z3_context, Z3_ast_map);
ay_sig_Z3_ast_map_size const ay_link_Z3_ast_map_size = &Z3_ast_map_size;
unsigned int ay_call_Z3_ast_map_size(Z3_context ay_a0, Z3_ast_map ay_a1) {
    return Z3_ast_map_size(ay_a0, ay_a1);
}

typedef Z3_string (*ay_sig_Z3_ast_map_to_string)(Z3_context, Z3_ast_map);
ay_sig_Z3_ast_map_to_string const ay_link_Z3_ast_map_to_string = &Z3_ast_map_to_string;
Z3_string ay_call_Z3_ast_map_to_string(Z3_context ay_a0, Z3_ast_map ay_a1) {
    return Z3_ast_map_to_string(ay_a0, ay_a1);
}

typedef Z3_string (*ay_sig_Z3_ast_to_string)(Z3_context, Z3_ast);
ay_sig_Z3_ast_to_string const ay_link_Z3_ast_to_string = &Z3_ast_to_string;
Z3_string ay_call_Z3_ast_to_string(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_ast_to_string(ay_a0, ay_a1);
}

typedef void (*ay_sig_Z3_ast_vector_dec_ref)(Z3_context, Z3_ast_vector);
ay_sig_Z3_ast_vector_dec_ref const ay_link_Z3_ast_vector_dec_ref = &Z3_ast_vector_dec_ref;
void ay_call_Z3_ast_vector_dec_ref(Z3_context ay_a0, Z3_ast_vector ay_a1) {
    Z3_ast_vector_dec_ref(ay_a0, ay_a1);
}

typedef Z3_ast (*ay_sig_Z3_ast_vector_get)(Z3_context, Z3_ast_vector, unsigned int);
ay_sig_Z3_ast_vector_get const ay_link_Z3_ast_vector_get = &Z3_ast_vector_get;
Z3_ast ay_call_Z3_ast_vector_get(Z3_context ay_a0, Z3_ast_vector ay_a1, unsigned int ay_a2) {
    return Z3_ast_vector_get(ay_a0, ay_a1, ay_a2);
}

typedef void (*ay_sig_Z3_ast_vector_inc_ref)(Z3_context, Z3_ast_vector);
ay_sig_Z3_ast_vector_inc_ref const ay_link_Z3_ast_vector_inc_ref = &Z3_ast_vector_inc_ref;
void ay_call_Z3_ast_vector_inc_ref(Z3_context ay_a0, Z3_ast_vector ay_a1) {
    Z3_ast_vector_inc_ref(ay_a0, ay_a1);
}

typedef void (*ay_sig_Z3_ast_vector_push)(Z3_context, Z3_ast_vector, Z3_ast);
ay_sig_Z3_ast_vector_push const ay_link_Z3_ast_vector_push = &Z3_ast_vector_push;
void ay_call_Z3_ast_vector_push(Z3_context ay_a0, Z3_ast_vector ay_a1, Z3_ast ay_a2) {
    Z3_ast_vector_push(ay_a0, ay_a1, ay_a2);
}

typedef void (*ay_sig_Z3_ast_vector_resize)(Z3_context, Z3_ast_vector, unsigned int);
ay_sig_Z3_ast_vector_resize const ay_link_Z3_ast_vector_resize = &Z3_ast_vector_resize;
void ay_call_Z3_ast_vector_resize(Z3_context ay_a0, Z3_ast_vector ay_a1, unsigned int ay_a2) {
    Z3_ast_vector_resize(ay_a0, ay_a1, ay_a2);
}

typedef void (*ay_sig_Z3_ast_vector_set)(Z3_context, Z3_ast_vector, unsigned int, Z3_ast);
ay_sig_Z3_ast_vector_set const ay_link_Z3_ast_vector_set = &Z3_ast_vector_set;
void ay_call_Z3_ast_vector_set(Z3_context ay_a0, Z3_ast_vector ay_a1, unsigned int ay_a2, Z3_ast ay_a3) {
    Z3_ast_vector_set(ay_a0, ay_a1, ay_a2, ay_a3);
}

typedef unsigned int (*ay_sig_Z3_ast_vector_size)(Z3_context, Z3_ast_vector);
ay_sig_Z3_ast_vector_size const ay_link_Z3_ast_vector_size = &Z3_ast_vector_size;
unsigned int ay_call_Z3_ast_vector_size(Z3_context ay_a0, Z3_ast_vector ay_a1) {
    return Z3_ast_vector_size(ay_a0, ay_a1);
}

typedef Z3_string (*ay_sig_Z3_ast_vector_to_string)(Z3_context, Z3_ast_vector);
ay_sig_Z3_ast_vector_to_string const ay_link_Z3_ast_vector_to_string = &Z3_ast_vector_to_string;
Z3_string ay_call_Z3_ast_vector_to_string(Z3_context ay_a0, Z3_ast_vector ay_a1) {
    return Z3_ast_vector_to_string(ay_a0, ay_a1);
}

typedef Z3_ast_vector (*ay_sig_Z3_ast_vector_translate)(Z3_context, Z3_ast_vector, Z3_context);
ay_sig_Z3_ast_vector_translate const ay_link_Z3_ast_vector_translate = &Z3_ast_vector_translate;
Z3_ast_vector ay_call_Z3_ast_vector_translate(Z3_context ay_a0, Z3_ast_vector ay_a1, Z3_context ay_a2) {
    return Z3_ast_vector_translate(ay_a0, ay_a1, ay_a2);
}

typedef Z3_string (*ay_sig_Z3_benchmark_to_smtlib_string)(Z3_context, Z3_string, Z3_string, Z3_string, Z3_string, unsigned int, const Z3_ast *, Z3_ast);
ay_sig_Z3_benchmark_to_smtlib_string const ay_link_Z3_benchmark_to_smtlib_string = &Z3_benchmark_to_smtlib_string;
Z3_string ay_call_Z3_benchmark_to_smtlib_string(Z3_context ay_a0, Z3_string ay_a1, Z3_string ay_a2, Z3_string ay_a3, Z3_string ay_a4, unsigned int ay_a5, const Z3_ast * ay_a6, Z3_ast ay_a7) {
    return Z3_benchmark_to_smtlib_string(ay_a0, ay_a1, ay_a2, ay_a3, ay_a4, ay_a5, ay_a6, ay_a7);
}

typedef void (*ay_sig_Z3_close_log)(void);
ay_sig_Z3_close_log const ay_link_Z3_close_log = &Z3_close_log;
void ay_call_Z3_close_log(void) {
    Z3_close_log();
}

typedef unsigned int (*ay_sig_Z3_constructor_num_fields)(Z3_context, Z3_constructor);
ay_sig_Z3_constructor_num_fields const ay_link_Z3_constructor_num_fields = &Z3_constructor_num_fields;
unsigned int ay_call_Z3_constructor_num_fields(Z3_context ay_a0, Z3_constructor ay_a1) {
    return Z3_constructor_num_fields(ay_a0, ay_a1);
}

typedef Z3_ast (*ay_sig_Z3_datatype_update_field)(Z3_context, Z3_func_decl, Z3_ast, Z3_ast);
ay_sig_Z3_datatype_update_field const ay_link_Z3_datatype_update_field = &Z3_datatype_update_field;
Z3_ast ay_call_Z3_datatype_update_field(Z3_context ay_a0, Z3_func_decl ay_a1, Z3_ast ay_a2, Z3_ast ay_a3) {
    return Z3_datatype_update_field(ay_a0, ay_a1, ay_a2, ay_a3);
}

typedef void (*ay_sig_Z3_dec_ref)(Z3_context, Z3_ast);
ay_sig_Z3_dec_ref const ay_link_Z3_dec_ref = &Z3_dec_ref;
void ay_call_Z3_dec_ref(Z3_context ay_a0, Z3_ast ay_a1) {
    Z3_dec_ref(ay_a0, ay_a1);
}

typedef void (*ay_sig_Z3_del_config)(Z3_config);
ay_sig_Z3_del_config const ay_link_Z3_del_config = &Z3_del_config;
void ay_call_Z3_del_config(Z3_config ay_a0) {
    Z3_del_config(ay_a0);
}

typedef void (*ay_sig_Z3_del_constructor_list)(Z3_context, Z3_constructor_list);
ay_sig_Z3_del_constructor_list const ay_link_Z3_del_constructor_list = &Z3_del_constructor_list;
void ay_call_Z3_del_constructor_list(Z3_context ay_a0, Z3_constructor_list ay_a1) {
    Z3_del_constructor_list(ay_a0, ay_a1);
}

typedef void (*ay_sig_Z3_del_constructor)(Z3_context, Z3_constructor);
ay_sig_Z3_del_constructor const ay_link_Z3_del_constructor = &Z3_del_constructor;
void ay_call_Z3_del_constructor(Z3_context ay_a0, Z3_constructor ay_a1) {
    Z3_del_constructor(ay_a0, ay_a1);
}

typedef void (*ay_sig_Z3_del_context)(Z3_context);
ay_sig_Z3_del_context const ay_link_Z3_del_context = &Z3_del_context;
void ay_call_Z3_del_context(Z3_context ay_a0) {
    Z3_del_context(ay_a0);
}

typedef void (*ay_sig_Z3_disable_trace)(Z3_string);
ay_sig_Z3_disable_trace const ay_link_Z3_disable_trace = &Z3_disable_trace;
void ay_call_Z3_disable_trace(Z3_string ay_a0) {
    Z3_disable_trace(ay_a0);
}

typedef void (*ay_sig_Z3_enable_concurrent_dec_ref)(Z3_context);
ay_sig_Z3_enable_concurrent_dec_ref const ay_link_Z3_enable_concurrent_dec_ref = &Z3_enable_concurrent_dec_ref;
void ay_call_Z3_enable_concurrent_dec_ref(Z3_context ay_a0) {
    Z3_enable_concurrent_dec_ref(ay_a0);
}

typedef void (*ay_sig_Z3_enable_trace)(Z3_string);
ay_sig_Z3_enable_trace const ay_link_Z3_enable_trace = &Z3_enable_trace;
void ay_call_Z3_enable_trace(Z3_string ay_a0) {
    Z3_enable_trace(ay_a0);
}

typedef Z3_string (*ay_sig_Z3_eval_smtlib2_string)(Z3_context, Z3_string);
ay_sig_Z3_eval_smtlib2_string const ay_link_Z3_eval_smtlib2_string = &Z3_eval_smtlib2_string;
Z3_string ay_call_Z3_eval_smtlib2_string(Z3_context ay_a0, Z3_string ay_a1) {
    return Z3_eval_smtlib2_string(ay_a0, ay_a1);
}

typedef void (*ay_sig_Z3_finalize_memory)(void);
ay_sig_Z3_finalize_memory const ay_link_Z3_finalize_memory = &Z3_finalize_memory;
void ay_call_Z3_finalize_memory(void) {
    Z3_finalize_memory();
}

typedef void (*ay_sig_Z3_fixedpoint_add_callback)(Z3_context, Z3_fixedpoint, void *, Z3_fixedpoint_new_lemma_eh, Z3_fixedpoint_predecessor_eh, Z3_fixedpoint_unfold_eh);
ay_sig_Z3_fixedpoint_add_callback const ay_link_Z3_fixedpoint_add_callback = &Z3_fixedpoint_add_callback;
void ay_call_Z3_fixedpoint_add_callback(Z3_context ay_a0, Z3_fixedpoint ay_a1, void * ay_a2, Z3_fixedpoint_new_lemma_eh ay_a3, Z3_fixedpoint_predecessor_eh ay_a4, Z3_fixedpoint_unfold_eh ay_a5) {
    Z3_fixedpoint_add_callback(ay_a0, ay_a1, ay_a2, ay_a3, ay_a4, ay_a5);
}

typedef void (*ay_sig_Z3_fixedpoint_add_constraint)(Z3_context, Z3_fixedpoint, Z3_ast, unsigned int);
ay_sig_Z3_fixedpoint_add_constraint const ay_link_Z3_fixedpoint_add_constraint = &Z3_fixedpoint_add_constraint;
void ay_call_Z3_fixedpoint_add_constraint(Z3_context ay_a0, Z3_fixedpoint ay_a1, Z3_ast ay_a2, unsigned int ay_a3) {
    Z3_fixedpoint_add_constraint(ay_a0, ay_a1, ay_a2, ay_a3);
}

typedef void (*ay_sig_Z3_fixedpoint_add_cover)(Z3_context, Z3_fixedpoint, int, Z3_func_decl, Z3_ast);
ay_sig_Z3_fixedpoint_add_cover const ay_link_Z3_fixedpoint_add_cover = &Z3_fixedpoint_add_cover;
void ay_call_Z3_fixedpoint_add_cover(Z3_context ay_a0, Z3_fixedpoint ay_a1, int ay_a2, Z3_func_decl ay_a3, Z3_ast ay_a4) {
    Z3_fixedpoint_add_cover(ay_a0, ay_a1, ay_a2, ay_a3, ay_a4);
}

typedef void (*ay_sig_Z3_fixedpoint_add_fact)(Z3_context, Z3_fixedpoint, Z3_func_decl, unsigned int, unsigned int *);
ay_sig_Z3_fixedpoint_add_fact const ay_link_Z3_fixedpoint_add_fact = &Z3_fixedpoint_add_fact;
void ay_call_Z3_fixedpoint_add_fact(Z3_context ay_a0, Z3_fixedpoint ay_a1, Z3_func_decl ay_a2, unsigned int ay_a3, unsigned int * ay_a4) {
    Z3_fixedpoint_add_fact(ay_a0, ay_a1, ay_a2, ay_a3, ay_a4);
}

typedef void (*ay_sig_Z3_fixedpoint_add_invariant)(Z3_context, Z3_fixedpoint, Z3_func_decl, Z3_ast);
ay_sig_Z3_fixedpoint_add_invariant const ay_link_Z3_fixedpoint_add_invariant = &Z3_fixedpoint_add_invariant;
void ay_call_Z3_fixedpoint_add_invariant(Z3_context ay_a0, Z3_fixedpoint ay_a1, Z3_func_decl ay_a2, Z3_ast ay_a3) {
    Z3_fixedpoint_add_invariant(ay_a0, ay_a1, ay_a2, ay_a3);
}

typedef void (*ay_sig_Z3_fixedpoint_add_rule)(Z3_context, Z3_fixedpoint, Z3_ast, Z3_symbol);
ay_sig_Z3_fixedpoint_add_rule const ay_link_Z3_fixedpoint_add_rule = &Z3_fixedpoint_add_rule;
void ay_call_Z3_fixedpoint_add_rule(Z3_context ay_a0, Z3_fixedpoint ay_a1, Z3_ast ay_a2, Z3_symbol ay_a3) {
    Z3_fixedpoint_add_rule(ay_a0, ay_a1, ay_a2, ay_a3);
}

typedef void (*ay_sig_Z3_fixedpoint_assert)(Z3_context, Z3_fixedpoint, Z3_ast);
ay_sig_Z3_fixedpoint_assert const ay_link_Z3_fixedpoint_assert = &Z3_fixedpoint_assert;
void ay_call_Z3_fixedpoint_assert(Z3_context ay_a0, Z3_fixedpoint ay_a1, Z3_ast ay_a2) {
    Z3_fixedpoint_assert(ay_a0, ay_a1, ay_a2);
}

typedef void (*ay_sig_Z3_fixedpoint_dec_ref)(Z3_context, Z3_fixedpoint);
ay_sig_Z3_fixedpoint_dec_ref const ay_link_Z3_fixedpoint_dec_ref = &Z3_fixedpoint_dec_ref;
void ay_call_Z3_fixedpoint_dec_ref(Z3_context ay_a0, Z3_fixedpoint ay_a1) {
    Z3_fixedpoint_dec_ref(ay_a0, ay_a1);
}

typedef Z3_ast_vector (*ay_sig_Z3_fixedpoint_from_file)(Z3_context, Z3_fixedpoint, Z3_string);
ay_sig_Z3_fixedpoint_from_file const ay_link_Z3_fixedpoint_from_file = &Z3_fixedpoint_from_file;
Z3_ast_vector ay_call_Z3_fixedpoint_from_file(Z3_context ay_a0, Z3_fixedpoint ay_a1, Z3_string ay_a2) {
    return Z3_fixedpoint_from_file(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast_vector (*ay_sig_Z3_fixedpoint_from_string)(Z3_context, Z3_fixedpoint, Z3_string);
ay_sig_Z3_fixedpoint_from_string const ay_link_Z3_fixedpoint_from_string = &Z3_fixedpoint_from_string;
Z3_ast_vector ay_call_Z3_fixedpoint_from_string(Z3_context ay_a0, Z3_fixedpoint ay_a1, Z3_string ay_a2) {
    return Z3_fixedpoint_from_string(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_fixedpoint_get_answer)(Z3_context, Z3_fixedpoint);
ay_sig_Z3_fixedpoint_get_answer const ay_link_Z3_fixedpoint_get_answer = &Z3_fixedpoint_get_answer;
Z3_ast ay_call_Z3_fixedpoint_get_answer(Z3_context ay_a0, Z3_fixedpoint ay_a1) {
    return Z3_fixedpoint_get_answer(ay_a0, ay_a1);
}

typedef Z3_ast_vector (*ay_sig_Z3_fixedpoint_get_assertions)(Z3_context, Z3_fixedpoint);
ay_sig_Z3_fixedpoint_get_assertions const ay_link_Z3_fixedpoint_get_assertions = &Z3_fixedpoint_get_assertions;
Z3_ast_vector ay_call_Z3_fixedpoint_get_assertions(Z3_context ay_a0, Z3_fixedpoint ay_a1) {
    return Z3_fixedpoint_get_assertions(ay_a0, ay_a1);
}

typedef Z3_ast (*ay_sig_Z3_fixedpoint_get_cover_delta)(Z3_context, Z3_fixedpoint, int, Z3_func_decl);
ay_sig_Z3_fixedpoint_get_cover_delta const ay_link_Z3_fixedpoint_get_cover_delta = &Z3_fixedpoint_get_cover_delta;
Z3_ast ay_call_Z3_fixedpoint_get_cover_delta(Z3_context ay_a0, Z3_fixedpoint ay_a1, int ay_a2, Z3_func_decl ay_a3) {
    return Z3_fixedpoint_get_cover_delta(ay_a0, ay_a1, ay_a2, ay_a3);
}

typedef Z3_ast (*ay_sig_Z3_fixedpoint_get_ground_sat_answer)(Z3_context, Z3_fixedpoint);
ay_sig_Z3_fixedpoint_get_ground_sat_answer const ay_link_Z3_fixedpoint_get_ground_sat_answer = &Z3_fixedpoint_get_ground_sat_answer;
Z3_ast ay_call_Z3_fixedpoint_get_ground_sat_answer(Z3_context ay_a0, Z3_fixedpoint ay_a1) {
    return Z3_fixedpoint_get_ground_sat_answer(ay_a0, ay_a1);
}

typedef Z3_string (*ay_sig_Z3_fixedpoint_get_help)(Z3_context, Z3_fixedpoint);
ay_sig_Z3_fixedpoint_get_help const ay_link_Z3_fixedpoint_get_help = &Z3_fixedpoint_get_help;
Z3_string ay_call_Z3_fixedpoint_get_help(Z3_context ay_a0, Z3_fixedpoint ay_a1) {
    return Z3_fixedpoint_get_help(ay_a0, ay_a1);
}

typedef unsigned int (*ay_sig_Z3_fixedpoint_get_num_levels)(Z3_context, Z3_fixedpoint, Z3_func_decl);
ay_sig_Z3_fixedpoint_get_num_levels const ay_link_Z3_fixedpoint_get_num_levels = &Z3_fixedpoint_get_num_levels;
unsigned int ay_call_Z3_fixedpoint_get_num_levels(Z3_context ay_a0, Z3_fixedpoint ay_a1, Z3_func_decl ay_a2) {
    return Z3_fixedpoint_get_num_levels(ay_a0, ay_a1, ay_a2);
}

typedef Z3_param_descrs (*ay_sig_Z3_fixedpoint_get_param_descrs)(Z3_context, Z3_fixedpoint);
ay_sig_Z3_fixedpoint_get_param_descrs const ay_link_Z3_fixedpoint_get_param_descrs = &Z3_fixedpoint_get_param_descrs;
Z3_param_descrs ay_call_Z3_fixedpoint_get_param_descrs(Z3_context ay_a0, Z3_fixedpoint ay_a1) {
    return Z3_fixedpoint_get_param_descrs(ay_a0, ay_a1);
}

typedef Z3_ast (*ay_sig_Z3_fixedpoint_get_reachable)(Z3_context, Z3_fixedpoint, Z3_func_decl);
ay_sig_Z3_fixedpoint_get_reachable const ay_link_Z3_fixedpoint_get_reachable = &Z3_fixedpoint_get_reachable;
Z3_ast ay_call_Z3_fixedpoint_get_reachable(Z3_context ay_a0, Z3_fixedpoint ay_a1, Z3_func_decl ay_a2) {
    return Z3_fixedpoint_get_reachable(ay_a0, ay_a1, ay_a2);
}

typedef Z3_string (*ay_sig_Z3_fixedpoint_get_reason_unknown)(Z3_context, Z3_fixedpoint);
ay_sig_Z3_fixedpoint_get_reason_unknown const ay_link_Z3_fixedpoint_get_reason_unknown = &Z3_fixedpoint_get_reason_unknown;
Z3_string ay_call_Z3_fixedpoint_get_reason_unknown(Z3_context ay_a0, Z3_fixedpoint ay_a1) {
    return Z3_fixedpoint_get_reason_unknown(ay_a0, ay_a1);
}

typedef Z3_symbol (*ay_sig_Z3_fixedpoint_get_rule_names_along_trace)(Z3_context, Z3_fixedpoint);
ay_sig_Z3_fixedpoint_get_rule_names_along_trace const ay_link_Z3_fixedpoint_get_rule_names_along_trace = &Z3_fixedpoint_get_rule_names_along_trace;
Z3_symbol ay_call_Z3_fixedpoint_get_rule_names_along_trace(Z3_context ay_a0, Z3_fixedpoint ay_a1) {
    return Z3_fixedpoint_get_rule_names_along_trace(ay_a0, ay_a1);
}

typedef Z3_ast_vector (*ay_sig_Z3_fixedpoint_get_rules_along_trace)(Z3_context, Z3_fixedpoint);
ay_sig_Z3_fixedpoint_get_rules_along_trace const ay_link_Z3_fixedpoint_get_rules_along_trace = &Z3_fixedpoint_get_rules_along_trace;
Z3_ast_vector ay_call_Z3_fixedpoint_get_rules_along_trace(Z3_context ay_a0, Z3_fixedpoint ay_a1) {
    return Z3_fixedpoint_get_rules_along_trace(ay_a0, ay_a1);
}

typedef Z3_ast_vector (*ay_sig_Z3_fixedpoint_get_rules)(Z3_context, Z3_fixedpoint);
ay_sig_Z3_fixedpoint_get_rules const ay_link_Z3_fixedpoint_get_rules = &Z3_fixedpoint_get_rules;
Z3_ast_vector ay_call_Z3_fixedpoint_get_rules(Z3_context ay_a0, Z3_fixedpoint ay_a1) {
    return Z3_fixedpoint_get_rules(ay_a0, ay_a1);
}

typedef Z3_stats (*ay_sig_Z3_fixedpoint_get_statistics)(Z3_context, Z3_fixedpoint);
ay_sig_Z3_fixedpoint_get_statistics const ay_link_Z3_fixedpoint_get_statistics = &Z3_fixedpoint_get_statistics;
Z3_stats ay_call_Z3_fixedpoint_get_statistics(Z3_context ay_a0, Z3_fixedpoint ay_a1) {
    return Z3_fixedpoint_get_statistics(ay_a0, ay_a1);
}

typedef void (*ay_sig_Z3_fixedpoint_inc_ref)(Z3_context, Z3_fixedpoint);
ay_sig_Z3_fixedpoint_inc_ref const ay_link_Z3_fixedpoint_inc_ref = &Z3_fixedpoint_inc_ref;
void ay_call_Z3_fixedpoint_inc_ref(Z3_context ay_a0, Z3_fixedpoint ay_a1) {
    Z3_fixedpoint_inc_ref(ay_a0, ay_a1);
}

typedef void (*ay_sig_Z3_fixedpoint_init)(Z3_context, Z3_fixedpoint, void *);
ay_sig_Z3_fixedpoint_init const ay_link_Z3_fixedpoint_init = &Z3_fixedpoint_init;
void ay_call_Z3_fixedpoint_init(Z3_context ay_a0, Z3_fixedpoint ay_a1, void * ay_a2) {
    Z3_fixedpoint_init(ay_a0, ay_a1, ay_a2);
}

typedef Z3_lbool (*ay_sig_Z3_fixedpoint_query_from_lvl)(Z3_context, Z3_fixedpoint, Z3_ast, unsigned int);
ay_sig_Z3_fixedpoint_query_from_lvl const ay_link_Z3_fixedpoint_query_from_lvl = &Z3_fixedpoint_query_from_lvl;
Z3_lbool ay_call_Z3_fixedpoint_query_from_lvl(Z3_context ay_a0, Z3_fixedpoint ay_a1, Z3_ast ay_a2, unsigned int ay_a3) {
    return Z3_fixedpoint_query_from_lvl(ay_a0, ay_a1, ay_a2, ay_a3);
}

typedef Z3_lbool (*ay_sig_Z3_fixedpoint_query_relations)(Z3_context, Z3_fixedpoint, unsigned int, const Z3_func_decl *);
ay_sig_Z3_fixedpoint_query_relations const ay_link_Z3_fixedpoint_query_relations = &Z3_fixedpoint_query_relations;
Z3_lbool ay_call_Z3_fixedpoint_query_relations(Z3_context ay_a0, Z3_fixedpoint ay_a1, unsigned int ay_a2, const Z3_func_decl * ay_a3) {
    return Z3_fixedpoint_query_relations(ay_a0, ay_a1, ay_a2, ay_a3);
}

typedef Z3_lbool (*ay_sig_Z3_fixedpoint_query)(Z3_context, Z3_fixedpoint, Z3_ast);
ay_sig_Z3_fixedpoint_query const ay_link_Z3_fixedpoint_query = &Z3_fixedpoint_query;
Z3_lbool ay_call_Z3_fixedpoint_query(Z3_context ay_a0, Z3_fixedpoint ay_a1, Z3_ast ay_a2) {
    return Z3_fixedpoint_query(ay_a0, ay_a1, ay_a2);
}

typedef void (*ay_sig_Z3_fixedpoint_register_relation)(Z3_context, Z3_fixedpoint, Z3_func_decl);
ay_sig_Z3_fixedpoint_register_relation const ay_link_Z3_fixedpoint_register_relation = &Z3_fixedpoint_register_relation;
void ay_call_Z3_fixedpoint_register_relation(Z3_context ay_a0, Z3_fixedpoint ay_a1, Z3_func_decl ay_a2) {
    Z3_fixedpoint_register_relation(ay_a0, ay_a1, ay_a2);
}

typedef void (*ay_sig_Z3_fixedpoint_set_params)(Z3_context, Z3_fixedpoint, Z3_params);
ay_sig_Z3_fixedpoint_set_params const ay_link_Z3_fixedpoint_set_params = &Z3_fixedpoint_set_params;
void ay_call_Z3_fixedpoint_set_params(Z3_context ay_a0, Z3_fixedpoint ay_a1, Z3_params ay_a2) {
    Z3_fixedpoint_set_params(ay_a0, ay_a1, ay_a2);
}

typedef void (*ay_sig_Z3_fixedpoint_set_predicate_representation)(Z3_context, Z3_fixedpoint, Z3_func_decl, unsigned int, const Z3_symbol *);
ay_sig_Z3_fixedpoint_set_predicate_representation const ay_link_Z3_fixedpoint_set_predicate_representation = &Z3_fixedpoint_set_predicate_representation;
void ay_call_Z3_fixedpoint_set_predicate_representation(Z3_context ay_a0, Z3_fixedpoint ay_a1, Z3_func_decl ay_a2, unsigned int ay_a3, const Z3_symbol * ay_a4) {
    Z3_fixedpoint_set_predicate_representation(ay_a0, ay_a1, ay_a2, ay_a3, ay_a4);
}

typedef void (*ay_sig_Z3_fixedpoint_set_reduce_app_callback)(Z3_context, Z3_fixedpoint, Z3_fixedpoint_reduce_app_callback_fptr *);
ay_sig_Z3_fixedpoint_set_reduce_app_callback const ay_link_Z3_fixedpoint_set_reduce_app_callback = &Z3_fixedpoint_set_reduce_app_callback;
void ay_call_Z3_fixedpoint_set_reduce_app_callback(Z3_context ay_a0, Z3_fixedpoint ay_a1, Z3_fixedpoint_reduce_app_callback_fptr * ay_a2) {
    Z3_fixedpoint_set_reduce_app_callback(ay_a0, ay_a1, ay_a2);
}

typedef void (*ay_sig_Z3_fixedpoint_set_reduce_assign_callback)(Z3_context, Z3_fixedpoint, Z3_fixedpoint_reduce_assign_callback_fptr *);
ay_sig_Z3_fixedpoint_set_reduce_assign_callback const ay_link_Z3_fixedpoint_set_reduce_assign_callback = &Z3_fixedpoint_set_reduce_assign_callback;
void ay_call_Z3_fixedpoint_set_reduce_assign_callback(Z3_context ay_a0, Z3_fixedpoint ay_a1, Z3_fixedpoint_reduce_assign_callback_fptr * ay_a2) {
    Z3_fixedpoint_set_reduce_assign_callback(ay_a0, ay_a1, ay_a2);
}

typedef Z3_string (*ay_sig_Z3_fixedpoint_to_string)(Z3_context, Z3_fixedpoint, unsigned int, Z3_ast *);
ay_sig_Z3_fixedpoint_to_string const ay_link_Z3_fixedpoint_to_string = &Z3_fixedpoint_to_string;
Z3_string ay_call_Z3_fixedpoint_to_string(Z3_context ay_a0, Z3_fixedpoint ay_a1, unsigned int ay_a2, Z3_ast * ay_a3) {
    return Z3_fixedpoint_to_string(ay_a0, ay_a1, ay_a2, ay_a3);
}

typedef void (*ay_sig_Z3_fixedpoint_update_rule)(Z3_context, Z3_fixedpoint, Z3_ast, Z3_symbol);
ay_sig_Z3_fixedpoint_update_rule const ay_link_Z3_fixedpoint_update_rule = &Z3_fixedpoint_update_rule;
void ay_call_Z3_fixedpoint_update_rule(Z3_context ay_a0, Z3_fixedpoint ay_a1, Z3_ast ay_a2, Z3_symbol ay_a3) {
    Z3_fixedpoint_update_rule(ay_a0, ay_a1, ay_a2, ay_a3);
}

typedef unsigned int (*ay_sig_Z3_fpa_get_ebits)(Z3_context, Z3_sort);
ay_sig_Z3_fpa_get_ebits const ay_link_Z3_fpa_get_ebits = &Z3_fpa_get_ebits;
unsigned int ay_call_Z3_fpa_get_ebits(Z3_context ay_a0, Z3_sort ay_a1) {
    return Z3_fpa_get_ebits(ay_a0, ay_a1);
}

typedef Z3_ast (*ay_sig_Z3_fpa_get_numeral_exponent_bv)(Z3_context, Z3_ast, bool);
ay_sig_Z3_fpa_get_numeral_exponent_bv const ay_link_Z3_fpa_get_numeral_exponent_bv = &Z3_fpa_get_numeral_exponent_bv;
Z3_ast ay_call_Z3_fpa_get_numeral_exponent_bv(Z3_context ay_a0, Z3_ast ay_a1, bool ay_a2) {
    return Z3_fpa_get_numeral_exponent_bv(ay_a0, ay_a1, ay_a2);
}

typedef bool (*ay_sig_Z3_fpa_get_numeral_exponent_int64)(Z3_context, Z3_ast, int64_t *, bool);
ay_sig_Z3_fpa_get_numeral_exponent_int64 const ay_link_Z3_fpa_get_numeral_exponent_int64 = &Z3_fpa_get_numeral_exponent_int64;
bool ay_call_Z3_fpa_get_numeral_exponent_int64(Z3_context ay_a0, Z3_ast ay_a1, int64_t * ay_a2, bool ay_a3) {
    return Z3_fpa_get_numeral_exponent_int64(ay_a0, ay_a1, ay_a2, ay_a3);
}

typedef Z3_string (*ay_sig_Z3_fpa_get_numeral_exponent_string)(Z3_context, Z3_ast, bool);
ay_sig_Z3_fpa_get_numeral_exponent_string const ay_link_Z3_fpa_get_numeral_exponent_string = &Z3_fpa_get_numeral_exponent_string;
Z3_string ay_call_Z3_fpa_get_numeral_exponent_string(Z3_context ay_a0, Z3_ast ay_a1, bool ay_a2) {
    return Z3_fpa_get_numeral_exponent_string(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_fpa_get_numeral_sign_bv)(Z3_context, Z3_ast);
ay_sig_Z3_fpa_get_numeral_sign_bv const ay_link_Z3_fpa_get_numeral_sign_bv = &Z3_fpa_get_numeral_sign_bv;
Z3_ast ay_call_Z3_fpa_get_numeral_sign_bv(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_fpa_get_numeral_sign_bv(ay_a0, ay_a1);
}

typedef Z3_ast (*ay_sig_Z3_fpa_get_numeral_significand_bv)(Z3_context, Z3_ast);
ay_sig_Z3_fpa_get_numeral_significand_bv const ay_link_Z3_fpa_get_numeral_significand_bv = &Z3_fpa_get_numeral_significand_bv;
Z3_ast ay_call_Z3_fpa_get_numeral_significand_bv(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_fpa_get_numeral_significand_bv(ay_a0, ay_a1);
}

typedef Z3_string (*ay_sig_Z3_fpa_get_numeral_significand_string)(Z3_context, Z3_ast);
ay_sig_Z3_fpa_get_numeral_significand_string const ay_link_Z3_fpa_get_numeral_significand_string = &Z3_fpa_get_numeral_significand_string;
Z3_string ay_call_Z3_fpa_get_numeral_significand_string(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_fpa_get_numeral_significand_string(ay_a0, ay_a1);
}

typedef bool (*ay_sig_Z3_fpa_get_numeral_significand_uint64)(Z3_context, Z3_ast, uint64_t *);
ay_sig_Z3_fpa_get_numeral_significand_uint64 const ay_link_Z3_fpa_get_numeral_significand_uint64 = &Z3_fpa_get_numeral_significand_uint64;
bool ay_call_Z3_fpa_get_numeral_significand_uint64(Z3_context ay_a0, Z3_ast ay_a1, uint64_t * ay_a2) {
    return Z3_fpa_get_numeral_significand_uint64(ay_a0, ay_a1, ay_a2);
}

typedef bool (*ay_sig_Z3_fpa_get_numeral_sign)(Z3_context, Z3_ast, bool *);
ay_sig_Z3_fpa_get_numeral_sign const ay_link_Z3_fpa_get_numeral_sign = &Z3_fpa_get_numeral_sign;
bool ay_call_Z3_fpa_get_numeral_sign(Z3_context ay_a0, Z3_ast ay_a1, bool * ay_a2) {
    return Z3_fpa_get_numeral_sign(ay_a0, ay_a1, ay_a2);
}

typedef unsigned int (*ay_sig_Z3_fpa_get_sbits)(Z3_context, Z3_sort);
ay_sig_Z3_fpa_get_sbits const ay_link_Z3_fpa_get_sbits = &Z3_fpa_get_sbits;
unsigned int ay_call_Z3_fpa_get_sbits(Z3_context ay_a0, Z3_sort ay_a1) {
    return Z3_fpa_get_sbits(ay_a0, ay_a1);
}

typedef bool (*ay_sig_Z3_fpa_is_numeral_inf)(Z3_context, Z3_ast);
ay_sig_Z3_fpa_is_numeral_inf const ay_link_Z3_fpa_is_numeral_inf = &Z3_fpa_is_numeral_inf;
bool ay_call_Z3_fpa_is_numeral_inf(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_fpa_is_numeral_inf(ay_a0, ay_a1);
}

typedef bool (*ay_sig_Z3_fpa_is_numeral_nan)(Z3_context, Z3_ast);
ay_sig_Z3_fpa_is_numeral_nan const ay_link_Z3_fpa_is_numeral_nan = &Z3_fpa_is_numeral_nan;
bool ay_call_Z3_fpa_is_numeral_nan(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_fpa_is_numeral_nan(ay_a0, ay_a1);
}

typedef bool (*ay_sig_Z3_fpa_is_numeral_negative)(Z3_context, Z3_ast);
ay_sig_Z3_fpa_is_numeral_negative const ay_link_Z3_fpa_is_numeral_negative = &Z3_fpa_is_numeral_negative;
bool ay_call_Z3_fpa_is_numeral_negative(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_fpa_is_numeral_negative(ay_a0, ay_a1);
}

typedef bool (*ay_sig_Z3_fpa_is_numeral_normal)(Z3_context, Z3_ast);
ay_sig_Z3_fpa_is_numeral_normal const ay_link_Z3_fpa_is_numeral_normal = &Z3_fpa_is_numeral_normal;
bool ay_call_Z3_fpa_is_numeral_normal(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_fpa_is_numeral_normal(ay_a0, ay_a1);
}

typedef bool (*ay_sig_Z3_fpa_is_numeral_positive)(Z3_context, Z3_ast);
ay_sig_Z3_fpa_is_numeral_positive const ay_link_Z3_fpa_is_numeral_positive = &Z3_fpa_is_numeral_positive;
bool ay_call_Z3_fpa_is_numeral_positive(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_fpa_is_numeral_positive(ay_a0, ay_a1);
}

typedef bool (*ay_sig_Z3_fpa_is_numeral_subnormal)(Z3_context, Z3_ast);
ay_sig_Z3_fpa_is_numeral_subnormal const ay_link_Z3_fpa_is_numeral_subnormal = &Z3_fpa_is_numeral_subnormal;
bool ay_call_Z3_fpa_is_numeral_subnormal(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_fpa_is_numeral_subnormal(ay_a0, ay_a1);
}

typedef bool (*ay_sig_Z3_fpa_is_numeral_zero)(Z3_context, Z3_ast);
ay_sig_Z3_fpa_is_numeral_zero const ay_link_Z3_fpa_is_numeral_zero = &Z3_fpa_is_numeral_zero;
bool ay_call_Z3_fpa_is_numeral_zero(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_fpa_is_numeral_zero(ay_a0, ay_a1);
}

typedef bool (*ay_sig_Z3_fpa_is_numeral)(Z3_context, Z3_ast);
ay_sig_Z3_fpa_is_numeral const ay_link_Z3_fpa_is_numeral = &Z3_fpa_is_numeral;
bool ay_call_Z3_fpa_is_numeral(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_fpa_is_numeral(ay_a0, ay_a1);
}

typedef Z3_ast (*ay_sig_Z3_func_decl_to_ast)(Z3_context, Z3_func_decl);
ay_sig_Z3_func_decl_to_ast const ay_link_Z3_func_decl_to_ast = &Z3_func_decl_to_ast;
Z3_ast ay_call_Z3_func_decl_to_ast(Z3_context ay_a0, Z3_func_decl ay_a1) {
    return Z3_func_decl_to_ast(ay_a0, ay_a1);
}

typedef Z3_string (*ay_sig_Z3_func_decl_to_string)(Z3_context, Z3_func_decl);
ay_sig_Z3_func_decl_to_string const ay_link_Z3_func_decl_to_string = &Z3_func_decl_to_string;
Z3_string ay_call_Z3_func_decl_to_string(Z3_context ay_a0, Z3_func_decl ay_a1) {
    return Z3_func_decl_to_string(ay_a0, ay_a1);
}

typedef void (*ay_sig_Z3_func_entry_dec_ref)(Z3_context, Z3_func_entry);
ay_sig_Z3_func_entry_dec_ref const ay_link_Z3_func_entry_dec_ref = &Z3_func_entry_dec_ref;
void ay_call_Z3_func_entry_dec_ref(Z3_context ay_a0, Z3_func_entry ay_a1) {
    Z3_func_entry_dec_ref(ay_a0, ay_a1);
}

typedef Z3_ast (*ay_sig_Z3_func_entry_get_arg)(Z3_context, Z3_func_entry, unsigned int);
ay_sig_Z3_func_entry_get_arg const ay_link_Z3_func_entry_get_arg = &Z3_func_entry_get_arg;
Z3_ast ay_call_Z3_func_entry_get_arg(Z3_context ay_a0, Z3_func_entry ay_a1, unsigned int ay_a2) {
    return Z3_func_entry_get_arg(ay_a0, ay_a1, ay_a2);
}

typedef unsigned int (*ay_sig_Z3_func_entry_get_num_args)(Z3_context, Z3_func_entry);
ay_sig_Z3_func_entry_get_num_args const ay_link_Z3_func_entry_get_num_args = &Z3_func_entry_get_num_args;
unsigned int ay_call_Z3_func_entry_get_num_args(Z3_context ay_a0, Z3_func_entry ay_a1) {
    return Z3_func_entry_get_num_args(ay_a0, ay_a1);
}

typedef Z3_ast (*ay_sig_Z3_func_entry_get_value)(Z3_context, Z3_func_entry);
ay_sig_Z3_func_entry_get_value const ay_link_Z3_func_entry_get_value = &Z3_func_entry_get_value;
Z3_ast ay_call_Z3_func_entry_get_value(Z3_context ay_a0, Z3_func_entry ay_a1) {
    return Z3_func_entry_get_value(ay_a0, ay_a1);
}

typedef void (*ay_sig_Z3_func_entry_inc_ref)(Z3_context, Z3_func_entry);
ay_sig_Z3_func_entry_inc_ref const ay_link_Z3_func_entry_inc_ref = &Z3_func_entry_inc_ref;
void ay_call_Z3_func_entry_inc_ref(Z3_context ay_a0, Z3_func_entry ay_a1) {
    Z3_func_entry_inc_ref(ay_a0, ay_a1);
}

typedef void (*ay_sig_Z3_func_interp_add_entry)(Z3_context, Z3_func_interp, Z3_ast_vector, Z3_ast);
ay_sig_Z3_func_interp_add_entry const ay_link_Z3_func_interp_add_entry = &Z3_func_interp_add_entry;
void ay_call_Z3_func_interp_add_entry(Z3_context ay_a0, Z3_func_interp ay_a1, Z3_ast_vector ay_a2, Z3_ast ay_a3) {
    Z3_func_interp_add_entry(ay_a0, ay_a1, ay_a2, ay_a3);
}

typedef void (*ay_sig_Z3_func_interp_dec_ref)(Z3_context, Z3_func_interp);
ay_sig_Z3_func_interp_dec_ref const ay_link_Z3_func_interp_dec_ref = &Z3_func_interp_dec_ref;
void ay_call_Z3_func_interp_dec_ref(Z3_context ay_a0, Z3_func_interp ay_a1) {
    Z3_func_interp_dec_ref(ay_a0, ay_a1);
}

typedef unsigned int (*ay_sig_Z3_func_interp_get_arity)(Z3_context, Z3_func_interp);
ay_sig_Z3_func_interp_get_arity const ay_link_Z3_func_interp_get_arity = &Z3_func_interp_get_arity;
unsigned int ay_call_Z3_func_interp_get_arity(Z3_context ay_a0, Z3_func_interp ay_a1) {
    return Z3_func_interp_get_arity(ay_a0, ay_a1);
}

typedef Z3_ast (*ay_sig_Z3_func_interp_get_else)(Z3_context, Z3_func_interp);
ay_sig_Z3_func_interp_get_else const ay_link_Z3_func_interp_get_else = &Z3_func_interp_get_else;
Z3_ast ay_call_Z3_func_interp_get_else(Z3_context ay_a0, Z3_func_interp ay_a1) {
    return Z3_func_interp_get_else(ay_a0, ay_a1);
}

typedef Z3_func_entry (*ay_sig_Z3_func_interp_get_entry)(Z3_context, Z3_func_interp, unsigned int);
ay_sig_Z3_func_interp_get_entry const ay_link_Z3_func_interp_get_entry = &Z3_func_interp_get_entry;
Z3_func_entry ay_call_Z3_func_interp_get_entry(Z3_context ay_a0, Z3_func_interp ay_a1, unsigned int ay_a2) {
    return Z3_func_interp_get_entry(ay_a0, ay_a1, ay_a2);
}

typedef unsigned int (*ay_sig_Z3_func_interp_get_num_entries)(Z3_context, Z3_func_interp);
ay_sig_Z3_func_interp_get_num_entries const ay_link_Z3_func_interp_get_num_entries = &Z3_func_interp_get_num_entries;
unsigned int ay_call_Z3_func_interp_get_num_entries(Z3_context ay_a0, Z3_func_interp ay_a1) {
    return Z3_func_interp_get_num_entries(ay_a0, ay_a1);
}

typedef void (*ay_sig_Z3_func_interp_inc_ref)(Z3_context, Z3_func_interp);
ay_sig_Z3_func_interp_inc_ref const ay_link_Z3_func_interp_inc_ref = &Z3_func_interp_inc_ref;
void ay_call_Z3_func_interp_inc_ref(Z3_context ay_a0, Z3_func_interp ay_a1) {
    Z3_func_interp_inc_ref(ay_a0, ay_a1);
}

typedef void (*ay_sig_Z3_func_interp_set_else)(Z3_context, Z3_func_interp, Z3_ast);
ay_sig_Z3_func_interp_set_else const ay_link_Z3_func_interp_set_else = &Z3_func_interp_set_else;
void ay_call_Z3_func_interp_set_else(Z3_context ay_a0, Z3_func_interp ay_a1, Z3_ast ay_a2) {
    Z3_func_interp_set_else(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_get_algebraic_number_lower)(Z3_context, Z3_ast, unsigned int);
ay_sig_Z3_get_algebraic_number_lower const ay_link_Z3_get_algebraic_number_lower = &Z3_get_algebraic_number_lower;
Z3_ast ay_call_Z3_get_algebraic_number_lower(Z3_context ay_a0, Z3_ast ay_a1, unsigned int ay_a2) {
    return Z3_get_algebraic_number_lower(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_get_algebraic_number_upper)(Z3_context, Z3_ast, unsigned int);
ay_sig_Z3_get_algebraic_number_upper const ay_link_Z3_get_algebraic_number_upper = &Z3_get_algebraic_number_upper;
Z3_ast ay_call_Z3_get_algebraic_number_upper(Z3_context ay_a0, Z3_ast ay_a1, unsigned int ay_a2) {
    return Z3_get_algebraic_number_upper(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_get_app_arg)(Z3_context, Z3_app, unsigned int);
ay_sig_Z3_get_app_arg const ay_link_Z3_get_app_arg = &Z3_get_app_arg;
Z3_ast ay_call_Z3_get_app_arg(Z3_context ay_a0, Z3_app ay_a1, unsigned int ay_a2) {
    return Z3_get_app_arg(ay_a0, ay_a1, ay_a2);
}

typedef Z3_func_decl (*ay_sig_Z3_get_app_decl)(Z3_context, Z3_app);
ay_sig_Z3_get_app_decl const ay_link_Z3_get_app_decl = &Z3_get_app_decl;
Z3_func_decl ay_call_Z3_get_app_decl(Z3_context ay_a0, Z3_app ay_a1) {
    return Z3_get_app_decl(ay_a0, ay_a1);
}

typedef unsigned int (*ay_sig_Z3_get_app_num_args)(Z3_context, Z3_app);
ay_sig_Z3_get_app_num_args const ay_link_Z3_get_app_num_args = &Z3_get_app_num_args;
unsigned int ay_call_Z3_get_app_num_args(Z3_context ay_a0, Z3_app ay_a1) {
    return Z3_get_app_num_args(ay_a0, ay_a1);
}

typedef unsigned int (*ay_sig_Z3_get_arity)(Z3_context, Z3_func_decl);
ay_sig_Z3_get_arity const ay_link_Z3_get_arity = &Z3_get_arity;
unsigned int ay_call_Z3_get_arity(Z3_context ay_a0, Z3_func_decl ay_a1) {
    return Z3_get_arity(ay_a0, ay_a1);
}

typedef unsigned int (*ay_sig_Z3_get_array_arity)(Z3_context, Z3_sort);
ay_sig_Z3_get_array_arity const ay_link_Z3_get_array_arity = &Z3_get_array_arity;
unsigned int ay_call_Z3_get_array_arity(Z3_context ay_a0, Z3_sort ay_a1) {
    return Z3_get_array_arity(ay_a0, ay_a1);
}

typedef Z3_sort (*ay_sig_Z3_get_array_sort_domain_n)(Z3_context, Z3_sort, unsigned int);
ay_sig_Z3_get_array_sort_domain_n const ay_link_Z3_get_array_sort_domain_n = &Z3_get_array_sort_domain_n;
Z3_sort ay_call_Z3_get_array_sort_domain_n(Z3_context ay_a0, Z3_sort ay_a1, unsigned int ay_a2) {
    return Z3_get_array_sort_domain_n(ay_a0, ay_a1, ay_a2);
}

typedef Z3_sort (*ay_sig_Z3_get_array_sort_domain)(Z3_context, Z3_sort);
ay_sig_Z3_get_array_sort_domain const ay_link_Z3_get_array_sort_domain = &Z3_get_array_sort_domain;
Z3_sort ay_call_Z3_get_array_sort_domain(Z3_context ay_a0, Z3_sort ay_a1) {
    return Z3_get_array_sort_domain(ay_a0, ay_a1);
}

typedef Z3_sort (*ay_sig_Z3_get_array_sort_range)(Z3_context, Z3_sort);
ay_sig_Z3_get_array_sort_range const ay_link_Z3_get_array_sort_range = &Z3_get_array_sort_range;
Z3_sort ay_call_Z3_get_array_sort_range(Z3_context ay_a0, Z3_sort ay_a1) {
    return Z3_get_array_sort_range(ay_a0, ay_a1);
}

typedef Z3_func_decl (*ay_sig_Z3_get_as_array_func_decl)(Z3_context, Z3_ast);
ay_sig_Z3_get_as_array_func_decl const ay_link_Z3_get_as_array_func_decl = &Z3_get_as_array_func_decl;
Z3_func_decl ay_call_Z3_get_as_array_func_decl(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_get_as_array_func_decl(ay_a0, ay_a1);
}

typedef unsigned int (*ay_sig_Z3_get_ast_hash)(Z3_context, Z3_ast);
ay_sig_Z3_get_ast_hash const ay_link_Z3_get_ast_hash = &Z3_get_ast_hash;
unsigned int ay_call_Z3_get_ast_hash(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_get_ast_hash(ay_a0, ay_a1);
}

typedef unsigned int (*ay_sig_Z3_get_ast_id)(Z3_context, Z3_ast);
ay_sig_Z3_get_ast_id const ay_link_Z3_get_ast_id = &Z3_get_ast_id;
unsigned int ay_call_Z3_get_ast_id(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_get_ast_id(ay_a0, ay_a1);
}

typedef Z3_ast_kind (*ay_sig_Z3_get_ast_kind)(Z3_context, Z3_ast);
ay_sig_Z3_get_ast_kind const ay_link_Z3_get_ast_kind = &Z3_get_ast_kind;
Z3_ast_kind ay_call_Z3_get_ast_kind(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_get_ast_kind(ay_a0, ay_a1);
}

typedef Z3_lbool (*ay_sig_Z3_get_bool_value)(Z3_context, Z3_ast);
ay_sig_Z3_get_bool_value const ay_link_Z3_get_bool_value = &Z3_get_bool_value;
Z3_lbool ay_call_Z3_get_bool_value(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_get_bool_value(ay_a0, ay_a1);
}

typedef unsigned int (*ay_sig_Z3_get_bv_sort_size)(Z3_context, Z3_sort);
ay_sig_Z3_get_bv_sort_size const ay_link_Z3_get_bv_sort_size = &Z3_get_bv_sort_size;
unsigned int ay_call_Z3_get_bv_sort_size(Z3_context ay_a0, Z3_sort ay_a1) {
    return Z3_get_bv_sort_size(ay_a0, ay_a1);
}

typedef Z3_func_decl (*ay_sig_Z3_get_datatype_sort_constructor_accessor)(Z3_context, Z3_sort, unsigned int, unsigned int);
ay_sig_Z3_get_datatype_sort_constructor_accessor const ay_link_Z3_get_datatype_sort_constructor_accessor = &Z3_get_datatype_sort_constructor_accessor;
Z3_func_decl ay_call_Z3_get_datatype_sort_constructor_accessor(Z3_context ay_a0, Z3_sort ay_a1, unsigned int ay_a2, unsigned int ay_a3) {
    return Z3_get_datatype_sort_constructor_accessor(ay_a0, ay_a1, ay_a2, ay_a3);
}

typedef Z3_func_decl (*ay_sig_Z3_get_datatype_sort_constructor)(Z3_context, Z3_sort, unsigned int);
ay_sig_Z3_get_datatype_sort_constructor const ay_link_Z3_get_datatype_sort_constructor = &Z3_get_datatype_sort_constructor;
Z3_func_decl ay_call_Z3_get_datatype_sort_constructor(Z3_context ay_a0, Z3_sort ay_a1, unsigned int ay_a2) {
    return Z3_get_datatype_sort_constructor(ay_a0, ay_a1, ay_a2);
}

typedef unsigned int (*ay_sig_Z3_get_datatype_sort_num_constructors)(Z3_context, Z3_sort);
ay_sig_Z3_get_datatype_sort_num_constructors const ay_link_Z3_get_datatype_sort_num_constructors = &Z3_get_datatype_sort_num_constructors;
unsigned int ay_call_Z3_get_datatype_sort_num_constructors(Z3_context ay_a0, Z3_sort ay_a1) {
    return Z3_get_datatype_sort_num_constructors(ay_a0, ay_a1);
}

typedef Z3_func_decl (*ay_sig_Z3_get_datatype_sort_recognizer)(Z3_context, Z3_sort, unsigned int);
ay_sig_Z3_get_datatype_sort_recognizer const ay_link_Z3_get_datatype_sort_recognizer = &Z3_get_datatype_sort_recognizer;
Z3_func_decl ay_call_Z3_get_datatype_sort_recognizer(Z3_context ay_a0, Z3_sort ay_a1, unsigned int ay_a2) {
    return Z3_get_datatype_sort_recognizer(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_get_decl_ast_parameter)(Z3_context, Z3_func_decl, unsigned int);
ay_sig_Z3_get_decl_ast_parameter const ay_link_Z3_get_decl_ast_parameter = &Z3_get_decl_ast_parameter;
Z3_ast ay_call_Z3_get_decl_ast_parameter(Z3_context ay_a0, Z3_func_decl ay_a1, unsigned int ay_a2) {
    return Z3_get_decl_ast_parameter(ay_a0, ay_a1, ay_a2);
}

typedef double (*ay_sig_Z3_get_decl_double_parameter)(Z3_context, Z3_func_decl, unsigned int);
ay_sig_Z3_get_decl_double_parameter const ay_link_Z3_get_decl_double_parameter = &Z3_get_decl_double_parameter;
double ay_call_Z3_get_decl_double_parameter(Z3_context ay_a0, Z3_func_decl ay_a1, unsigned int ay_a2) {
    return Z3_get_decl_double_parameter(ay_a0, ay_a1, ay_a2);
}

typedef Z3_func_decl (*ay_sig_Z3_get_decl_func_decl_parameter)(Z3_context, Z3_func_decl, unsigned int);
ay_sig_Z3_get_decl_func_decl_parameter const ay_link_Z3_get_decl_func_decl_parameter = &Z3_get_decl_func_decl_parameter;
Z3_func_decl ay_call_Z3_get_decl_func_decl_parameter(Z3_context ay_a0, Z3_func_decl ay_a1, unsigned int ay_a2) {
    return Z3_get_decl_func_decl_parameter(ay_a0, ay_a1, ay_a2);
}

typedef int (*ay_sig_Z3_get_decl_int_parameter)(Z3_context, Z3_func_decl, unsigned int);
ay_sig_Z3_get_decl_int_parameter const ay_link_Z3_get_decl_int_parameter = &Z3_get_decl_int_parameter;
int ay_call_Z3_get_decl_int_parameter(Z3_context ay_a0, Z3_func_decl ay_a1, unsigned int ay_a2) {
    return Z3_get_decl_int_parameter(ay_a0, ay_a1, ay_a2);
}

typedef Z3_decl_kind (*ay_sig_Z3_get_decl_kind)(Z3_context, Z3_func_decl);
ay_sig_Z3_get_decl_kind const ay_link_Z3_get_decl_kind = &Z3_get_decl_kind;
Z3_decl_kind ay_call_Z3_get_decl_kind(Z3_context ay_a0, Z3_func_decl ay_a1) {
    return Z3_get_decl_kind(ay_a0, ay_a1);
}

typedef Z3_symbol (*ay_sig_Z3_get_decl_name)(Z3_context, Z3_func_decl);
ay_sig_Z3_get_decl_name const ay_link_Z3_get_decl_name = &Z3_get_decl_name;
Z3_symbol ay_call_Z3_get_decl_name(Z3_context ay_a0, Z3_func_decl ay_a1) {
    return Z3_get_decl_name(ay_a0, ay_a1);
}

typedef unsigned int (*ay_sig_Z3_get_decl_num_parameters)(Z3_context, Z3_func_decl);
ay_sig_Z3_get_decl_num_parameters const ay_link_Z3_get_decl_num_parameters = &Z3_get_decl_num_parameters;
unsigned int ay_call_Z3_get_decl_num_parameters(Z3_context ay_a0, Z3_func_decl ay_a1) {
    return Z3_get_decl_num_parameters(ay_a0, ay_a1);
}

typedef Z3_parameter_kind (*ay_sig_Z3_get_decl_parameter_kind)(Z3_context, Z3_func_decl, unsigned int);
ay_sig_Z3_get_decl_parameter_kind const ay_link_Z3_get_decl_parameter_kind = &Z3_get_decl_parameter_kind;
Z3_parameter_kind ay_call_Z3_get_decl_parameter_kind(Z3_context ay_a0, Z3_func_decl ay_a1, unsigned int ay_a2) {
    return Z3_get_decl_parameter_kind(ay_a0, ay_a1, ay_a2);
}

typedef Z3_string (*ay_sig_Z3_get_decl_rational_parameter)(Z3_context, Z3_func_decl, unsigned int);
ay_sig_Z3_get_decl_rational_parameter const ay_link_Z3_get_decl_rational_parameter = &Z3_get_decl_rational_parameter;
Z3_string ay_call_Z3_get_decl_rational_parameter(Z3_context ay_a0, Z3_func_decl ay_a1, unsigned int ay_a2) {
    return Z3_get_decl_rational_parameter(ay_a0, ay_a1, ay_a2);
}

typedef Z3_sort (*ay_sig_Z3_get_decl_sort_parameter)(Z3_context, Z3_func_decl, unsigned int);
ay_sig_Z3_get_decl_sort_parameter const ay_link_Z3_get_decl_sort_parameter = &Z3_get_decl_sort_parameter;
Z3_sort ay_call_Z3_get_decl_sort_parameter(Z3_context ay_a0, Z3_func_decl ay_a1, unsigned int ay_a2) {
    return Z3_get_decl_sort_parameter(ay_a0, ay_a1, ay_a2);
}

typedef Z3_symbol (*ay_sig_Z3_get_decl_symbol_parameter)(Z3_context, Z3_func_decl, unsigned int);
ay_sig_Z3_get_decl_symbol_parameter const ay_link_Z3_get_decl_symbol_parameter = &Z3_get_decl_symbol_parameter;
Z3_symbol ay_call_Z3_get_decl_symbol_parameter(Z3_context ay_a0, Z3_func_decl ay_a1, unsigned int ay_a2) {
    return Z3_get_decl_symbol_parameter(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_get_denominator)(Z3_context, Z3_ast);
ay_sig_Z3_get_denominator const ay_link_Z3_get_denominator = &Z3_get_denominator;
Z3_ast ay_call_Z3_get_denominator(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_get_denominator(ay_a0, ay_a1);
}

typedef unsigned int (*ay_sig_Z3_get_depth)(Z3_context, Z3_ast);
ay_sig_Z3_get_depth const ay_link_Z3_get_depth = &Z3_get_depth;
unsigned int ay_call_Z3_get_depth(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_get_depth(ay_a0, ay_a1);
}

typedef unsigned int (*ay_sig_Z3_get_domain_size)(Z3_context, Z3_func_decl);
ay_sig_Z3_get_domain_size const ay_link_Z3_get_domain_size = &Z3_get_domain_size;
unsigned int ay_call_Z3_get_domain_size(Z3_context ay_a0, Z3_func_decl ay_a1) {
    return Z3_get_domain_size(ay_a0, ay_a1);
}

typedef Z3_sort (*ay_sig_Z3_get_domain)(Z3_context, Z3_func_decl, unsigned int);
ay_sig_Z3_get_domain const ay_link_Z3_get_domain = &Z3_get_domain;
Z3_sort ay_call_Z3_get_domain(Z3_context ay_a0, Z3_func_decl ay_a1, unsigned int ay_a2) {
    return Z3_get_domain(ay_a0, ay_a1, ay_a2);
}

typedef Z3_error_code (*ay_sig_Z3_get_error_code)(Z3_context);
ay_sig_Z3_get_error_code const ay_link_Z3_get_error_code = &Z3_get_error_code;
Z3_error_code ay_call_Z3_get_error_code(Z3_context ay_a0) {
    return Z3_get_error_code(ay_a0);
}

typedef Z3_string (*ay_sig_Z3_get_error_msg)(Z3_context, Z3_error_code);
ay_sig_Z3_get_error_msg const ay_link_Z3_get_error_msg = &Z3_get_error_msg;
Z3_string ay_call_Z3_get_error_msg(Z3_context ay_a0, Z3_error_code ay_a1) {
    return Z3_get_error_msg(ay_a0, ay_a1);
}

typedef uint64_t (*ay_sig_Z3_get_estimated_alloc_size)(void);
ay_sig_Z3_get_estimated_alloc_size const ay_link_Z3_get_estimated_alloc_size = &Z3_get_estimated_alloc_size;
uint64_t ay_call_Z3_get_estimated_alloc_size(void) {
    return Z3_get_estimated_alloc_size();
}

typedef bool (*ay_sig_Z3_get_finite_domain_sort_size)(Z3_context, Z3_sort, uint64_t *);
ay_sig_Z3_get_finite_domain_sort_size const ay_link_Z3_get_finite_domain_sort_size = &Z3_get_finite_domain_sort_size;
bool ay_call_Z3_get_finite_domain_sort_size(Z3_context ay_a0, Z3_sort ay_a1, uint64_t * ay_a2) {
    return Z3_get_finite_domain_sort_size(ay_a0, ay_a1, ay_a2);
}

typedef Z3_sort (*ay_sig_Z3_get_finite_set_sort_basis)(Z3_context, Z3_sort);
ay_sig_Z3_get_finite_set_sort_basis const ay_link_Z3_get_finite_set_sort_basis = &Z3_get_finite_set_sort_basis;
Z3_sort ay_call_Z3_get_finite_set_sort_basis(Z3_context ay_a0, Z3_sort ay_a1) {
    return Z3_get_finite_set_sort_basis(ay_a0, ay_a1);
}

typedef Z3_string (*ay_sig_Z3_get_full_version)(void);
ay_sig_Z3_get_full_version const ay_link_Z3_get_full_version = &Z3_get_full_version;
Z3_string ay_call_Z3_get_full_version(void) {
    return Z3_get_full_version();
}

typedef unsigned int (*ay_sig_Z3_get_func_decl_id)(Z3_context, Z3_func_decl);
ay_sig_Z3_get_func_decl_id const ay_link_Z3_get_func_decl_id = &Z3_get_func_decl_id;
unsigned int ay_call_Z3_get_func_decl_id(Z3_context ay_a0, Z3_func_decl ay_a1) {
    return Z3_get_func_decl_id(ay_a0, ay_a1);
}

typedef Z3_param_descrs (*ay_sig_Z3_get_global_param_descrs)(Z3_context);
ay_sig_Z3_get_global_param_descrs const ay_link_Z3_get_global_param_descrs = &Z3_get_global_param_descrs;
Z3_param_descrs ay_call_Z3_get_global_param_descrs(Z3_context ay_a0) {
    return Z3_get_global_param_descrs(ay_a0);
}

typedef Z3_lbool (*ay_sig_Z3_get_implied_equalities)(Z3_context, Z3_solver, unsigned int, const Z3_ast *, unsigned int *);
ay_sig_Z3_get_implied_equalities const ay_link_Z3_get_implied_equalities = &Z3_get_implied_equalities;
Z3_lbool ay_call_Z3_get_implied_equalities(Z3_context ay_a0, Z3_solver ay_a1, unsigned int ay_a2, const Z3_ast * ay_a3, unsigned int * ay_a4) {
    return Z3_get_implied_equalities(ay_a0, ay_a1, ay_a2, ay_a3, ay_a4);
}

typedef unsigned int (*ay_sig_Z3_get_index_value)(Z3_context, Z3_ast);
ay_sig_Z3_get_index_value const ay_link_Z3_get_index_value = &Z3_get_index_value;
unsigned int ay_call_Z3_get_index_value(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_get_index_value(ay_a0, ay_a1);
}

typedef Z3_char_ptr (*ay_sig_Z3_get_lstring)(Z3_context, Z3_ast, unsigned int *);
ay_sig_Z3_get_lstring const ay_link_Z3_get_lstring = &Z3_get_lstring;
Z3_char_ptr ay_call_Z3_get_lstring(Z3_context ay_a0, Z3_ast ay_a1, unsigned int * ay_a2) {
    return Z3_get_lstring(ay_a0, ay_a1, ay_a2);
}

typedef unsigned int (*ay_sig_Z3_get_num_probes)(Z3_context);
ay_sig_Z3_get_num_probes const ay_link_Z3_get_num_probes = &Z3_get_num_probes;
unsigned int ay_call_Z3_get_num_probes(Z3_context ay_a0) {
    return Z3_get_num_probes(ay_a0);
}

typedef unsigned int (*ay_sig_Z3_get_num_simplifiers)(Z3_context);
ay_sig_Z3_get_num_simplifiers const ay_link_Z3_get_num_simplifiers = &Z3_get_num_simplifiers;
unsigned int ay_call_Z3_get_num_simplifiers(Z3_context ay_a0) {
    return Z3_get_num_simplifiers(ay_a0);
}

typedef unsigned int (*ay_sig_Z3_get_num_tactics)(Z3_context);
ay_sig_Z3_get_num_tactics const ay_link_Z3_get_num_tactics = &Z3_get_num_tactics;
unsigned int ay_call_Z3_get_num_tactics(Z3_context ay_a0) {
    return Z3_get_num_tactics(ay_a0);
}

typedef Z3_string (*ay_sig_Z3_get_numeral_binary_string)(Z3_context, Z3_ast);
ay_sig_Z3_get_numeral_binary_string const ay_link_Z3_get_numeral_binary_string = &Z3_get_numeral_binary_string;
Z3_string ay_call_Z3_get_numeral_binary_string(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_get_numeral_binary_string(ay_a0, ay_a1);
}

typedef Z3_string (*ay_sig_Z3_get_numeral_decimal_string)(Z3_context, Z3_ast, unsigned int);
ay_sig_Z3_get_numeral_decimal_string const ay_link_Z3_get_numeral_decimal_string = &Z3_get_numeral_decimal_string;
Z3_string ay_call_Z3_get_numeral_decimal_string(Z3_context ay_a0, Z3_ast ay_a1, unsigned int ay_a2) {
    return Z3_get_numeral_decimal_string(ay_a0, ay_a1, ay_a2);
}

typedef double (*ay_sig_Z3_get_numeral_double)(Z3_context, Z3_ast);
ay_sig_Z3_get_numeral_double const ay_link_Z3_get_numeral_double = &Z3_get_numeral_double;
double ay_call_Z3_get_numeral_double(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_get_numeral_double(ay_a0, ay_a1);
}

typedef bool (*ay_sig_Z3_get_numeral_int64)(Z3_context, Z3_ast, int64_t *);
ay_sig_Z3_get_numeral_int64 const ay_link_Z3_get_numeral_int64 = &Z3_get_numeral_int64;
bool ay_call_Z3_get_numeral_int64(Z3_context ay_a0, Z3_ast ay_a1, int64_t * ay_a2) {
    return Z3_get_numeral_int64(ay_a0, ay_a1, ay_a2);
}

typedef bool (*ay_sig_Z3_get_numeral_int)(Z3_context, Z3_ast, int *);
ay_sig_Z3_get_numeral_int const ay_link_Z3_get_numeral_int = &Z3_get_numeral_int;
bool ay_call_Z3_get_numeral_int(Z3_context ay_a0, Z3_ast ay_a1, int * ay_a2) {
    return Z3_get_numeral_int(ay_a0, ay_a1, ay_a2);
}

typedef bool (*ay_sig_Z3_get_numeral_rational_int64)(Z3_context, Z3_ast, int64_t *, int64_t *);
ay_sig_Z3_get_numeral_rational_int64 const ay_link_Z3_get_numeral_rational_int64 = &Z3_get_numeral_rational_int64;
bool ay_call_Z3_get_numeral_rational_int64(Z3_context ay_a0, Z3_ast ay_a1, int64_t * ay_a2, int64_t * ay_a3) {
    return Z3_get_numeral_rational_int64(ay_a0, ay_a1, ay_a2, ay_a3);
}

typedef bool (*ay_sig_Z3_get_numeral_small)(Z3_context, Z3_ast, int64_t *, int64_t *);
ay_sig_Z3_get_numeral_small const ay_link_Z3_get_numeral_small = &Z3_get_numeral_small;
bool ay_call_Z3_get_numeral_small(Z3_context ay_a0, Z3_ast ay_a1, int64_t * ay_a2, int64_t * ay_a3) {
    return Z3_get_numeral_small(ay_a0, ay_a1, ay_a2, ay_a3);
}

typedef Z3_string (*ay_sig_Z3_get_numeral_string)(Z3_context, Z3_ast);
ay_sig_Z3_get_numeral_string const ay_link_Z3_get_numeral_string = &Z3_get_numeral_string;
Z3_string ay_call_Z3_get_numeral_string(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_get_numeral_string(ay_a0, ay_a1);
}

typedef bool (*ay_sig_Z3_get_numeral_uint64)(Z3_context, Z3_ast, uint64_t *);
ay_sig_Z3_get_numeral_uint64 const ay_link_Z3_get_numeral_uint64 = &Z3_get_numeral_uint64;
bool ay_call_Z3_get_numeral_uint64(Z3_context ay_a0, Z3_ast ay_a1, uint64_t * ay_a2) {
    return Z3_get_numeral_uint64(ay_a0, ay_a1, ay_a2);
}

typedef bool (*ay_sig_Z3_get_numeral_uint)(Z3_context, Z3_ast, unsigned int *);
ay_sig_Z3_get_numeral_uint const ay_link_Z3_get_numeral_uint = &Z3_get_numeral_uint;
bool ay_call_Z3_get_numeral_uint(Z3_context ay_a0, Z3_ast ay_a1, unsigned int * ay_a2) {
    return Z3_get_numeral_uint(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_get_numerator)(Z3_context, Z3_ast);
ay_sig_Z3_get_numerator const ay_link_Z3_get_numerator = &Z3_get_numerator;
Z3_ast ay_call_Z3_get_numerator(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_get_numerator(ay_a0, ay_a1);
}

typedef unsigned int (*ay_sig_Z3_get_pattern_num_terms)(Z3_context, Z3_pattern);
ay_sig_Z3_get_pattern_num_terms const ay_link_Z3_get_pattern_num_terms = &Z3_get_pattern_num_terms;
unsigned int ay_call_Z3_get_pattern_num_terms(Z3_context ay_a0, Z3_pattern ay_a1) {
    return Z3_get_pattern_num_terms(ay_a0, ay_a1);
}

typedef Z3_ast (*ay_sig_Z3_get_pattern)(Z3_context, Z3_pattern, unsigned int);
ay_sig_Z3_get_pattern const ay_link_Z3_get_pattern = &Z3_get_pattern;
Z3_ast ay_call_Z3_get_pattern(Z3_context ay_a0, Z3_pattern ay_a1, unsigned int ay_a2) {
    return Z3_get_pattern(ay_a0, ay_a1, ay_a2);
}

typedef Z3_string (*ay_sig_Z3_get_probe_name)(Z3_context, unsigned int);
ay_sig_Z3_get_probe_name const ay_link_Z3_get_probe_name = &Z3_get_probe_name;
Z3_string ay_call_Z3_get_probe_name(Z3_context ay_a0, unsigned int ay_a1) {
    return Z3_get_probe_name(ay_a0, ay_a1);
}

typedef Z3_ast (*ay_sig_Z3_get_quantifier_body)(Z3_context, Z3_ast);
ay_sig_Z3_get_quantifier_body const ay_link_Z3_get_quantifier_body = &Z3_get_quantifier_body;
Z3_ast ay_call_Z3_get_quantifier_body(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_get_quantifier_body(ay_a0, ay_a1);
}

typedef Z3_symbol (*ay_sig_Z3_get_quantifier_bound_name)(Z3_context, Z3_ast, unsigned int);
ay_sig_Z3_get_quantifier_bound_name const ay_link_Z3_get_quantifier_bound_name = &Z3_get_quantifier_bound_name;
Z3_symbol ay_call_Z3_get_quantifier_bound_name(Z3_context ay_a0, Z3_ast ay_a1, unsigned int ay_a2) {
    return Z3_get_quantifier_bound_name(ay_a0, ay_a1, ay_a2);
}

typedef Z3_sort (*ay_sig_Z3_get_quantifier_bound_sort)(Z3_context, Z3_ast, unsigned int);
ay_sig_Z3_get_quantifier_bound_sort const ay_link_Z3_get_quantifier_bound_sort = &Z3_get_quantifier_bound_sort;
Z3_sort ay_call_Z3_get_quantifier_bound_sort(Z3_context ay_a0, Z3_ast ay_a1, unsigned int ay_a2) {
    return Z3_get_quantifier_bound_sort(ay_a0, ay_a1, ay_a2);
}

typedef Z3_symbol (*ay_sig_Z3_get_quantifier_id)(Z3_context, Z3_ast);
ay_sig_Z3_get_quantifier_id const ay_link_Z3_get_quantifier_id = &Z3_get_quantifier_id;
Z3_symbol ay_call_Z3_get_quantifier_id(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_get_quantifier_id(ay_a0, ay_a1);
}

typedef Z3_ast (*ay_sig_Z3_get_quantifier_no_pattern_ast)(Z3_context, Z3_ast, unsigned int);
ay_sig_Z3_get_quantifier_no_pattern_ast const ay_link_Z3_get_quantifier_no_pattern_ast = &Z3_get_quantifier_no_pattern_ast;
Z3_ast ay_call_Z3_get_quantifier_no_pattern_ast(Z3_context ay_a0, Z3_ast ay_a1, unsigned int ay_a2) {
    return Z3_get_quantifier_no_pattern_ast(ay_a0, ay_a1, ay_a2);
}

typedef unsigned int (*ay_sig_Z3_get_quantifier_num_bound)(Z3_context, Z3_ast);
ay_sig_Z3_get_quantifier_num_bound const ay_link_Z3_get_quantifier_num_bound = &Z3_get_quantifier_num_bound;
unsigned int ay_call_Z3_get_quantifier_num_bound(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_get_quantifier_num_bound(ay_a0, ay_a1);
}

typedef unsigned int (*ay_sig_Z3_get_quantifier_num_no_patterns)(Z3_context, Z3_ast);
ay_sig_Z3_get_quantifier_num_no_patterns const ay_link_Z3_get_quantifier_num_no_patterns = &Z3_get_quantifier_num_no_patterns;
unsigned int ay_call_Z3_get_quantifier_num_no_patterns(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_get_quantifier_num_no_patterns(ay_a0, ay_a1);
}

typedef unsigned int (*ay_sig_Z3_get_quantifier_num_patterns)(Z3_context, Z3_ast);
ay_sig_Z3_get_quantifier_num_patterns const ay_link_Z3_get_quantifier_num_patterns = &Z3_get_quantifier_num_patterns;
unsigned int ay_call_Z3_get_quantifier_num_patterns(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_get_quantifier_num_patterns(ay_a0, ay_a1);
}

typedef Z3_pattern (*ay_sig_Z3_get_quantifier_pattern_ast)(Z3_context, Z3_ast, unsigned int);
ay_sig_Z3_get_quantifier_pattern_ast const ay_link_Z3_get_quantifier_pattern_ast = &Z3_get_quantifier_pattern_ast;
Z3_pattern ay_call_Z3_get_quantifier_pattern_ast(Z3_context ay_a0, Z3_ast ay_a1, unsigned int ay_a2) {
    return Z3_get_quantifier_pattern_ast(ay_a0, ay_a1, ay_a2);
}

typedef Z3_symbol (*ay_sig_Z3_get_quantifier_skolem_id)(Z3_context, Z3_ast);
ay_sig_Z3_get_quantifier_skolem_id const ay_link_Z3_get_quantifier_skolem_id = &Z3_get_quantifier_skolem_id;
Z3_symbol ay_call_Z3_get_quantifier_skolem_id(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_get_quantifier_skolem_id(ay_a0, ay_a1);
}

typedef unsigned int (*ay_sig_Z3_get_quantifier_weight)(Z3_context, Z3_ast);
ay_sig_Z3_get_quantifier_weight const ay_link_Z3_get_quantifier_weight = &Z3_get_quantifier_weight;
unsigned int ay_call_Z3_get_quantifier_weight(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_get_quantifier_weight(ay_a0, ay_a1);
}

typedef Z3_sort (*ay_sig_Z3_get_range)(Z3_context, Z3_func_decl);
ay_sig_Z3_get_range const ay_link_Z3_get_range = &Z3_get_range;
Z3_sort ay_call_Z3_get_range(Z3_context ay_a0, Z3_func_decl ay_a1) {
    return Z3_get_range(ay_a0, ay_a1);
}

typedef Z3_sort (*ay_sig_Z3_get_re_sort_basis)(Z3_context, Z3_sort);
ay_sig_Z3_get_re_sort_basis const ay_link_Z3_get_re_sort_basis = &Z3_get_re_sort_basis;
Z3_sort ay_call_Z3_get_re_sort_basis(Z3_context ay_a0, Z3_sort ay_a1) {
    return Z3_get_re_sort_basis(ay_a0, ay_a1);
}

typedef unsigned int (*ay_sig_Z3_get_relation_arity)(Z3_context, Z3_sort);
ay_sig_Z3_get_relation_arity const ay_link_Z3_get_relation_arity = &Z3_get_relation_arity;
unsigned int ay_call_Z3_get_relation_arity(Z3_context ay_a0, Z3_sort ay_a1) {
    return Z3_get_relation_arity(ay_a0, ay_a1);
}

typedef Z3_sort (*ay_sig_Z3_get_relation_column)(Z3_context, Z3_sort, unsigned int);
ay_sig_Z3_get_relation_column const ay_link_Z3_get_relation_column = &Z3_get_relation_column;
Z3_sort ay_call_Z3_get_relation_column(Z3_context ay_a0, Z3_sort ay_a1, unsigned int ay_a2) {
    return Z3_get_relation_column(ay_a0, ay_a1, ay_a2);
}

typedef Z3_sort (*ay_sig_Z3_get_seq_sort_basis)(Z3_context, Z3_sort);
ay_sig_Z3_get_seq_sort_basis const ay_link_Z3_get_seq_sort_basis = &Z3_get_seq_sort_basis;
Z3_sort ay_call_Z3_get_seq_sort_basis(Z3_context ay_a0, Z3_sort ay_a1) {
    return Z3_get_seq_sort_basis(ay_a0, ay_a1);
}

typedef Z3_string (*ay_sig_Z3_get_simplifier_name)(Z3_context, unsigned int);
ay_sig_Z3_get_simplifier_name const ay_link_Z3_get_simplifier_name = &Z3_get_simplifier_name;
Z3_string ay_call_Z3_get_simplifier_name(Z3_context ay_a0, unsigned int ay_a1) {
    return Z3_get_simplifier_name(ay_a0, ay_a1);
}

typedef unsigned int (*ay_sig_Z3_get_sort_id)(Z3_context, Z3_sort);
ay_sig_Z3_get_sort_id const ay_link_Z3_get_sort_id = &Z3_get_sort_id;
unsigned int ay_call_Z3_get_sort_id(Z3_context ay_a0, Z3_sort ay_a1) {
    return Z3_get_sort_id(ay_a0, ay_a1);
}

typedef Z3_sort_kind (*ay_sig_Z3_get_sort_kind)(Z3_context, Z3_sort);
ay_sig_Z3_get_sort_kind const ay_link_Z3_get_sort_kind = &Z3_get_sort_kind;
Z3_sort_kind ay_call_Z3_get_sort_kind(Z3_context ay_a0, Z3_sort ay_a1) {
    return Z3_get_sort_kind(ay_a0, ay_a1);
}

typedef Z3_symbol (*ay_sig_Z3_get_sort_name)(Z3_context, Z3_sort);
ay_sig_Z3_get_sort_name const ay_link_Z3_get_sort_name = &Z3_get_sort_name;
Z3_symbol ay_call_Z3_get_sort_name(Z3_context ay_a0, Z3_sort ay_a1) {
    return Z3_get_sort_name(ay_a0, ay_a1);
}

typedef Z3_sort (*ay_sig_Z3_get_sort)(Z3_context, Z3_ast);
ay_sig_Z3_get_sort const ay_link_Z3_get_sort = &Z3_get_sort;
Z3_sort ay_call_Z3_get_sort(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_get_sort(ay_a0, ay_a1);
}

typedef void (*ay_sig_Z3_get_string_contents)(Z3_context, Z3_ast, unsigned int, unsigned int *);
ay_sig_Z3_get_string_contents const ay_link_Z3_get_string_contents = &Z3_get_string_contents;
void ay_call_Z3_get_string_contents(Z3_context ay_a0, Z3_ast ay_a1, unsigned int ay_a2, unsigned int * ay_a3) {
    Z3_get_string_contents(ay_a0, ay_a1, ay_a2, ay_a3);
}

typedef unsigned int (*ay_sig_Z3_get_string_length)(Z3_context, Z3_ast);
ay_sig_Z3_get_string_length const ay_link_Z3_get_string_length = &Z3_get_string_length;
unsigned int ay_call_Z3_get_string_length(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_get_string_length(ay_a0, ay_a1);
}

typedef Z3_string (*ay_sig_Z3_get_string)(Z3_context, Z3_ast);
ay_sig_Z3_get_string const ay_link_Z3_get_string = &Z3_get_string;
Z3_string ay_call_Z3_get_string(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_get_string(ay_a0, ay_a1);
}

typedef int (*ay_sig_Z3_get_symbol_int)(Z3_context, Z3_symbol);
ay_sig_Z3_get_symbol_int const ay_link_Z3_get_symbol_int = &Z3_get_symbol_int;
int ay_call_Z3_get_symbol_int(Z3_context ay_a0, Z3_symbol ay_a1) {
    return Z3_get_symbol_int(ay_a0, ay_a1);
}

typedef Z3_symbol_kind (*ay_sig_Z3_get_symbol_kind)(Z3_context, Z3_symbol);
ay_sig_Z3_get_symbol_kind const ay_link_Z3_get_symbol_kind = &Z3_get_symbol_kind;
Z3_symbol_kind ay_call_Z3_get_symbol_kind(Z3_context ay_a0, Z3_symbol ay_a1) {
    return Z3_get_symbol_kind(ay_a0, ay_a1);
}

typedef Z3_string (*ay_sig_Z3_get_symbol_string)(Z3_context, Z3_symbol);
ay_sig_Z3_get_symbol_string const ay_link_Z3_get_symbol_string = &Z3_get_symbol_string;
Z3_string ay_call_Z3_get_symbol_string(Z3_context ay_a0, Z3_symbol ay_a1) {
    return Z3_get_symbol_string(ay_a0, ay_a1);
}

typedef Z3_string (*ay_sig_Z3_get_tactic_name)(Z3_context, unsigned int);
ay_sig_Z3_get_tactic_name const ay_link_Z3_get_tactic_name = &Z3_get_tactic_name;
Z3_string ay_call_Z3_get_tactic_name(Z3_context ay_a0, unsigned int ay_a1) {
    return Z3_get_tactic_name(ay_a0, ay_a1);
}

typedef Z3_func_decl (*ay_sig_Z3_get_tuple_sort_field_decl)(Z3_context, Z3_sort, unsigned int);
ay_sig_Z3_get_tuple_sort_field_decl const ay_link_Z3_get_tuple_sort_field_decl = &Z3_get_tuple_sort_field_decl;
Z3_func_decl ay_call_Z3_get_tuple_sort_field_decl(Z3_context ay_a0, Z3_sort ay_a1, unsigned int ay_a2) {
    return Z3_get_tuple_sort_field_decl(ay_a0, ay_a1, ay_a2);
}

typedef Z3_func_decl (*ay_sig_Z3_get_tuple_sort_mk_decl)(Z3_context, Z3_sort);
ay_sig_Z3_get_tuple_sort_mk_decl const ay_link_Z3_get_tuple_sort_mk_decl = &Z3_get_tuple_sort_mk_decl;
Z3_func_decl ay_call_Z3_get_tuple_sort_mk_decl(Z3_context ay_a0, Z3_sort ay_a1) {
    return Z3_get_tuple_sort_mk_decl(ay_a0, ay_a1);
}

typedef unsigned int (*ay_sig_Z3_get_tuple_sort_num_fields)(Z3_context, Z3_sort);
ay_sig_Z3_get_tuple_sort_num_fields const ay_link_Z3_get_tuple_sort_num_fields = &Z3_get_tuple_sort_num_fields;
unsigned int ay_call_Z3_get_tuple_sort_num_fields(Z3_context ay_a0, Z3_sort ay_a1) {
    return Z3_get_tuple_sort_num_fields(ay_a0, ay_a1);
}

typedef void (*ay_sig_Z3_get_version)(unsigned int *, unsigned int *, unsigned int *, unsigned int *);
ay_sig_Z3_get_version const ay_link_Z3_get_version = &Z3_get_version;
void ay_call_Z3_get_version(unsigned int * ay_a0, unsigned int * ay_a1, unsigned int * ay_a2, unsigned int * ay_a3) {
    Z3_get_version(ay_a0, ay_a1, ay_a2, ay_a3);
}

typedef bool (*ay_sig_Z3_global_param_get)(Z3_string, Z3_string_ptr);
ay_sig_Z3_global_param_get const ay_link_Z3_global_param_get = &Z3_global_param_get;
bool ay_call_Z3_global_param_get(Z3_string ay_a0, Z3_string_ptr ay_a1) {
    return Z3_global_param_get(ay_a0, ay_a1);
}

typedef void (*ay_sig_Z3_global_param_reset_all)(void);
ay_sig_Z3_global_param_reset_all const ay_link_Z3_global_param_reset_all = &Z3_global_param_reset_all;
void ay_call_Z3_global_param_reset_all(void) {
    Z3_global_param_reset_all();
}

typedef void (*ay_sig_Z3_global_param_set)(Z3_string, Z3_string);
ay_sig_Z3_global_param_set const ay_link_Z3_global_param_set = &Z3_global_param_set;
void ay_call_Z3_global_param_set(Z3_string ay_a0, Z3_string ay_a1) {
    Z3_global_param_set(ay_a0, ay_a1);
}

typedef void (*ay_sig_Z3_goal_assert)(Z3_context, Z3_goal, Z3_ast);
ay_sig_Z3_goal_assert const ay_link_Z3_goal_assert = &Z3_goal_assert;
void ay_call_Z3_goal_assert(Z3_context ay_a0, Z3_goal ay_a1, Z3_ast ay_a2) {
    Z3_goal_assert(ay_a0, ay_a1, ay_a2);
}

typedef Z3_model (*ay_sig_Z3_goal_convert_model)(Z3_context, Z3_goal, Z3_model);
ay_sig_Z3_goal_convert_model const ay_link_Z3_goal_convert_model = &Z3_goal_convert_model;
Z3_model ay_call_Z3_goal_convert_model(Z3_context ay_a0, Z3_goal ay_a1, Z3_model ay_a2) {
    return Z3_goal_convert_model(ay_a0, ay_a1, ay_a2);
}

typedef void (*ay_sig_Z3_goal_dec_ref)(Z3_context, Z3_goal);
ay_sig_Z3_goal_dec_ref const ay_link_Z3_goal_dec_ref = &Z3_goal_dec_ref;
void ay_call_Z3_goal_dec_ref(Z3_context ay_a0, Z3_goal ay_a1) {
    Z3_goal_dec_ref(ay_a0, ay_a1);
}

typedef unsigned int (*ay_sig_Z3_goal_depth)(Z3_context, Z3_goal);
ay_sig_Z3_goal_depth const ay_link_Z3_goal_depth = &Z3_goal_depth;
unsigned int ay_call_Z3_goal_depth(Z3_context ay_a0, Z3_goal ay_a1) {
    return Z3_goal_depth(ay_a0, ay_a1);
}

typedef Z3_ast (*ay_sig_Z3_goal_formula)(Z3_context, Z3_goal, unsigned int);
ay_sig_Z3_goal_formula const ay_link_Z3_goal_formula = &Z3_goal_formula;
Z3_ast ay_call_Z3_goal_formula(Z3_context ay_a0, Z3_goal ay_a1, unsigned int ay_a2) {
    return Z3_goal_formula(ay_a0, ay_a1, ay_a2);
}

typedef void (*ay_sig_Z3_goal_inc_ref)(Z3_context, Z3_goal);
ay_sig_Z3_goal_inc_ref const ay_link_Z3_goal_inc_ref = &Z3_goal_inc_ref;
void ay_call_Z3_goal_inc_ref(Z3_context ay_a0, Z3_goal ay_a1) {
    Z3_goal_inc_ref(ay_a0, ay_a1);
}

typedef bool (*ay_sig_Z3_goal_inconsistent)(Z3_context, Z3_goal);
ay_sig_Z3_goal_inconsistent const ay_link_Z3_goal_inconsistent = &Z3_goal_inconsistent;
bool ay_call_Z3_goal_inconsistent(Z3_context ay_a0, Z3_goal ay_a1) {
    return Z3_goal_inconsistent(ay_a0, ay_a1);
}

typedef bool (*ay_sig_Z3_goal_is_decided_sat)(Z3_context, Z3_goal);
ay_sig_Z3_goal_is_decided_sat const ay_link_Z3_goal_is_decided_sat = &Z3_goal_is_decided_sat;
bool ay_call_Z3_goal_is_decided_sat(Z3_context ay_a0, Z3_goal ay_a1) {
    return Z3_goal_is_decided_sat(ay_a0, ay_a1);
}

typedef bool (*ay_sig_Z3_goal_is_decided_unsat)(Z3_context, Z3_goal);
ay_sig_Z3_goal_is_decided_unsat const ay_link_Z3_goal_is_decided_unsat = &Z3_goal_is_decided_unsat;
bool ay_call_Z3_goal_is_decided_unsat(Z3_context ay_a0, Z3_goal ay_a1) {
    return Z3_goal_is_decided_unsat(ay_a0, ay_a1);
}

typedef unsigned int (*ay_sig_Z3_goal_num_exprs)(Z3_context, Z3_goal);
ay_sig_Z3_goal_num_exprs const ay_link_Z3_goal_num_exprs = &Z3_goal_num_exprs;
unsigned int ay_call_Z3_goal_num_exprs(Z3_context ay_a0, Z3_goal ay_a1) {
    return Z3_goal_num_exprs(ay_a0, ay_a1);
}

typedef Z3_goal_prec (*ay_sig_Z3_goal_precision)(Z3_context, Z3_goal);
ay_sig_Z3_goal_precision const ay_link_Z3_goal_precision = &Z3_goal_precision;
Z3_goal_prec ay_call_Z3_goal_precision(Z3_context ay_a0, Z3_goal ay_a1) {
    return Z3_goal_precision(ay_a0, ay_a1);
}

typedef void (*ay_sig_Z3_goal_reset)(Z3_context, Z3_goal);
ay_sig_Z3_goal_reset const ay_link_Z3_goal_reset = &Z3_goal_reset;
void ay_call_Z3_goal_reset(Z3_context ay_a0, Z3_goal ay_a1) {
    Z3_goal_reset(ay_a0, ay_a1);
}

typedef unsigned int (*ay_sig_Z3_goal_size)(Z3_context, Z3_goal);
ay_sig_Z3_goal_size const ay_link_Z3_goal_size = &Z3_goal_size;
unsigned int ay_call_Z3_goal_size(Z3_context ay_a0, Z3_goal ay_a1) {
    return Z3_goal_size(ay_a0, ay_a1);
}

typedef Z3_string (*ay_sig_Z3_goal_to_dimacs_string)(Z3_context, Z3_goal, bool);
ay_sig_Z3_goal_to_dimacs_string const ay_link_Z3_goal_to_dimacs_string = &Z3_goal_to_dimacs_string;
Z3_string ay_call_Z3_goal_to_dimacs_string(Z3_context ay_a0, Z3_goal ay_a1, bool ay_a2) {
    return Z3_goal_to_dimacs_string(ay_a0, ay_a1, ay_a2);
}

typedef Z3_string (*ay_sig_Z3_goal_to_string)(Z3_context, Z3_goal);
ay_sig_Z3_goal_to_string const ay_link_Z3_goal_to_string = &Z3_goal_to_string;
Z3_string ay_call_Z3_goal_to_string(Z3_context ay_a0, Z3_goal ay_a1) {
    return Z3_goal_to_string(ay_a0, ay_a1);
}

typedef Z3_goal (*ay_sig_Z3_goal_translate)(Z3_context, Z3_goal, Z3_context);
ay_sig_Z3_goal_translate const ay_link_Z3_goal_translate = &Z3_goal_translate;
Z3_goal ay_call_Z3_goal_translate(Z3_context ay_a0, Z3_goal ay_a1, Z3_context ay_a2) {
    return Z3_goal_translate(ay_a0, ay_a1, ay_a2);
}

typedef void (*ay_sig_Z3_inc_ref)(Z3_context, Z3_ast);
ay_sig_Z3_inc_ref const ay_link_Z3_inc_ref = &Z3_inc_ref;
void ay_call_Z3_inc_ref(Z3_context ay_a0, Z3_ast ay_a1) {
    Z3_inc_ref(ay_a0, ay_a1);
}

typedef void (*ay_sig_Z3_interrupt)(Z3_context);
ay_sig_Z3_interrupt const ay_link_Z3_interrupt = &Z3_interrupt;
void ay_call_Z3_interrupt(Z3_context ay_a0) {
    Z3_interrupt(ay_a0);
}

typedef bool (*ay_sig_Z3_is_algebraic_number)(Z3_context, Z3_ast);
ay_sig_Z3_is_algebraic_number const ay_link_Z3_is_algebraic_number = &Z3_is_algebraic_number;
bool ay_call_Z3_is_algebraic_number(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_is_algebraic_number(ay_a0, ay_a1);
}

typedef bool (*ay_sig_Z3_is_app)(Z3_context, Z3_ast);
ay_sig_Z3_is_app const ay_link_Z3_is_app = &Z3_is_app;
bool ay_call_Z3_is_app(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_is_app(ay_a0, ay_a1);
}

typedef bool (*ay_sig_Z3_is_as_array)(Z3_context, Z3_ast);
ay_sig_Z3_is_as_array const ay_link_Z3_is_as_array = &Z3_is_as_array;
bool ay_call_Z3_is_as_array(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_is_as_array(ay_a0, ay_a1);
}

typedef bool (*ay_sig_Z3_is_char_sort)(Z3_context, Z3_sort);
ay_sig_Z3_is_char_sort const ay_link_Z3_is_char_sort = &Z3_is_char_sort;
bool ay_call_Z3_is_char_sort(Z3_context ay_a0, Z3_sort ay_a1) {
    return Z3_is_char_sort(ay_a0, ay_a1);
}

typedef bool (*ay_sig_Z3_is_eq_ast)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_is_eq_ast const ay_link_Z3_is_eq_ast = &Z3_is_eq_ast;
bool ay_call_Z3_is_eq_ast(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_is_eq_ast(ay_a0, ay_a1, ay_a2);
}

typedef bool (*ay_sig_Z3_is_eq_func_decl)(Z3_context, Z3_func_decl, Z3_func_decl);
ay_sig_Z3_is_eq_func_decl const ay_link_Z3_is_eq_func_decl = &Z3_is_eq_func_decl;
bool ay_call_Z3_is_eq_func_decl(Z3_context ay_a0, Z3_func_decl ay_a1, Z3_func_decl ay_a2) {
    return Z3_is_eq_func_decl(ay_a0, ay_a1, ay_a2);
}

typedef bool (*ay_sig_Z3_is_eq_sort)(Z3_context, Z3_sort, Z3_sort);
ay_sig_Z3_is_eq_sort const ay_link_Z3_is_eq_sort = &Z3_is_eq_sort;
bool ay_call_Z3_is_eq_sort(Z3_context ay_a0, Z3_sort ay_a1, Z3_sort ay_a2) {
    return Z3_is_eq_sort(ay_a0, ay_a1, ay_a2);
}

typedef bool (*ay_sig_Z3_is_finite_set_sort)(Z3_context, Z3_sort);
ay_sig_Z3_is_finite_set_sort const ay_link_Z3_is_finite_set_sort = &Z3_is_finite_set_sort;
bool ay_call_Z3_is_finite_set_sort(Z3_context ay_a0, Z3_sort ay_a1) {
    return Z3_is_finite_set_sort(ay_a0, ay_a1);
}

typedef bool (*ay_sig_Z3_is_ground)(Z3_context, Z3_ast);
ay_sig_Z3_is_ground const ay_link_Z3_is_ground = &Z3_is_ground;
bool ay_call_Z3_is_ground(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_is_ground(ay_a0, ay_a1);
}

typedef bool (*ay_sig_Z3_is_lambda)(Z3_context, Z3_ast);
ay_sig_Z3_is_lambda const ay_link_Z3_is_lambda = &Z3_is_lambda;
bool ay_call_Z3_is_lambda(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_is_lambda(ay_a0, ay_a1);
}

typedef bool (*ay_sig_Z3_is_numeral_ast)(Z3_context, Z3_ast);
ay_sig_Z3_is_numeral_ast const ay_link_Z3_is_numeral_ast = &Z3_is_numeral_ast;
bool ay_call_Z3_is_numeral_ast(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_is_numeral_ast(ay_a0, ay_a1);
}

typedef bool (*ay_sig_Z3_is_quantifier_exists)(Z3_context, Z3_ast);
ay_sig_Z3_is_quantifier_exists const ay_link_Z3_is_quantifier_exists = &Z3_is_quantifier_exists;
bool ay_call_Z3_is_quantifier_exists(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_is_quantifier_exists(ay_a0, ay_a1);
}

typedef bool (*ay_sig_Z3_is_quantifier_forall)(Z3_context, Z3_ast);
ay_sig_Z3_is_quantifier_forall const ay_link_Z3_is_quantifier_forall = &Z3_is_quantifier_forall;
bool ay_call_Z3_is_quantifier_forall(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_is_quantifier_forall(ay_a0, ay_a1);
}

typedef bool (*ay_sig_Z3_is_re_sort)(Z3_context, Z3_sort);
ay_sig_Z3_is_re_sort const ay_link_Z3_is_re_sort = &Z3_is_re_sort;
bool ay_call_Z3_is_re_sort(Z3_context ay_a0, Z3_sort ay_a1) {
    return Z3_is_re_sort(ay_a0, ay_a1);
}

typedef bool (*ay_sig_Z3_is_recursive_datatype_sort)(Z3_context, Z3_sort);
ay_sig_Z3_is_recursive_datatype_sort const ay_link_Z3_is_recursive_datatype_sort = &Z3_is_recursive_datatype_sort;
bool ay_call_Z3_is_recursive_datatype_sort(Z3_context ay_a0, Z3_sort ay_a1) {
    return Z3_is_recursive_datatype_sort(ay_a0, ay_a1);
}

typedef bool (*ay_sig_Z3_is_seq_sort)(Z3_context, Z3_sort);
ay_sig_Z3_is_seq_sort const ay_link_Z3_is_seq_sort = &Z3_is_seq_sort;
bool ay_call_Z3_is_seq_sort(Z3_context ay_a0, Z3_sort ay_a1) {
    return Z3_is_seq_sort(ay_a0, ay_a1);
}

typedef bool (*ay_sig_Z3_is_string_sort)(Z3_context, Z3_sort);
ay_sig_Z3_is_string_sort const ay_link_Z3_is_string_sort = &Z3_is_string_sort;
bool ay_call_Z3_is_string_sort(Z3_context ay_a0, Z3_sort ay_a1) {
    return Z3_is_string_sort(ay_a0, ay_a1);
}

typedef bool (*ay_sig_Z3_is_string)(Z3_context, Z3_ast);
ay_sig_Z3_is_string const ay_link_Z3_is_string = &Z3_is_string;
bool ay_call_Z3_is_string(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_is_string(ay_a0, ay_a1);
}

typedef bool (*ay_sig_Z3_is_well_sorted)(Z3_context, Z3_ast);
ay_sig_Z3_is_well_sorted const ay_link_Z3_is_well_sorted = &Z3_is_well_sorted;
bool ay_call_Z3_is_well_sorted(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_is_well_sorted(ay_a0, ay_a1);
}

typedef Z3_ast (*ay_sig_Z3_mk_abs)(Z3_context, Z3_ast);
ay_sig_Z3_mk_abs const ay_link_Z3_mk_abs = &Z3_mk_abs;
Z3_ast ay_call_Z3_mk_abs(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_mk_abs(ay_a0, ay_a1);
}

typedef Z3_ast (*ay_sig_Z3_mk_add)(Z3_context, unsigned int, const Z3_ast *);
ay_sig_Z3_mk_add const ay_link_Z3_mk_add = &Z3_mk_add;
Z3_ast ay_call_Z3_mk_add(Z3_context ay_a0, unsigned int ay_a1, const Z3_ast * ay_a2) {
    return Z3_mk_add(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_and)(Z3_context, unsigned int, const Z3_ast *);
ay_sig_Z3_mk_and const ay_link_Z3_mk_and = &Z3_mk_and;
Z3_ast ay_call_Z3_mk_and(Z3_context ay_a0, unsigned int ay_a1, const Z3_ast * ay_a2) {
    return Z3_mk_and(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_app)(Z3_context, Z3_func_decl, unsigned int, const Z3_ast *);
ay_sig_Z3_mk_app const ay_link_Z3_mk_app = &Z3_mk_app;
Z3_ast ay_call_Z3_mk_app(Z3_context ay_a0, Z3_func_decl ay_a1, unsigned int ay_a2, const Z3_ast * ay_a3) {
    return Z3_mk_app(ay_a0, ay_a1, ay_a2, ay_a3);
}

typedef Z3_ast (*ay_sig_Z3_mk_array_default)(Z3_context, Z3_ast);
ay_sig_Z3_mk_array_default const ay_link_Z3_mk_array_default = &Z3_mk_array_default;
Z3_ast ay_call_Z3_mk_array_default(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_mk_array_default(ay_a0, ay_a1);
}

typedef Z3_ast (*ay_sig_Z3_mk_array_ext)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_mk_array_ext const ay_link_Z3_mk_array_ext = &Z3_mk_array_ext;
Z3_ast ay_call_Z3_mk_array_ext(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_mk_array_ext(ay_a0, ay_a1, ay_a2);
}

typedef Z3_sort (*ay_sig_Z3_mk_array_sort_n)(Z3_context, unsigned int, const Z3_sort *, Z3_sort);
ay_sig_Z3_mk_array_sort_n const ay_link_Z3_mk_array_sort_n = &Z3_mk_array_sort_n;
Z3_sort ay_call_Z3_mk_array_sort_n(Z3_context ay_a0, unsigned int ay_a1, const Z3_sort * ay_a2, Z3_sort ay_a3) {
    return Z3_mk_array_sort_n(ay_a0, ay_a1, ay_a2, ay_a3);
}

typedef Z3_sort (*ay_sig_Z3_mk_array_sort)(Z3_context, Z3_sort, Z3_sort);
ay_sig_Z3_mk_array_sort const ay_link_Z3_mk_array_sort = &Z3_mk_array_sort;
Z3_sort ay_call_Z3_mk_array_sort(Z3_context ay_a0, Z3_sort ay_a1, Z3_sort ay_a2) {
    return Z3_mk_array_sort(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_as_array)(Z3_context, Z3_func_decl);
ay_sig_Z3_mk_as_array const ay_link_Z3_mk_as_array = &Z3_mk_as_array;
Z3_ast ay_call_Z3_mk_as_array(Z3_context ay_a0, Z3_func_decl ay_a1) {
    return Z3_mk_as_array(ay_a0, ay_a1);
}

typedef Z3_ast_map (*ay_sig_Z3_mk_ast_map)(Z3_context);
ay_sig_Z3_mk_ast_map const ay_link_Z3_mk_ast_map = &Z3_mk_ast_map;
Z3_ast_map ay_call_Z3_mk_ast_map(Z3_context ay_a0) {
    return Z3_mk_ast_map(ay_a0);
}

typedef Z3_ast_vector (*ay_sig_Z3_mk_ast_vector)(Z3_context);
ay_sig_Z3_mk_ast_vector const ay_link_Z3_mk_ast_vector = &Z3_mk_ast_vector;
Z3_ast_vector ay_call_Z3_mk_ast_vector(Z3_context ay_a0) {
    return Z3_mk_ast_vector(ay_a0);
}

typedef Z3_ast (*ay_sig_Z3_mk_atleast)(Z3_context, unsigned int, const Z3_ast *, unsigned int);
ay_sig_Z3_mk_atleast const ay_link_Z3_mk_atleast = &Z3_mk_atleast;
Z3_ast ay_call_Z3_mk_atleast(Z3_context ay_a0, unsigned int ay_a1, const Z3_ast * ay_a2, unsigned int ay_a3) {
    return Z3_mk_atleast(ay_a0, ay_a1, ay_a2, ay_a3);
}

typedef Z3_ast (*ay_sig_Z3_mk_atmost)(Z3_context, unsigned int, const Z3_ast *, unsigned int);
ay_sig_Z3_mk_atmost const ay_link_Z3_mk_atmost = &Z3_mk_atmost;
Z3_ast ay_call_Z3_mk_atmost(Z3_context ay_a0, unsigned int ay_a1, const Z3_ast * ay_a2, unsigned int ay_a3) {
    return Z3_mk_atmost(ay_a0, ay_a1, ay_a2, ay_a3);
}

typedef Z3_ast (*ay_sig_Z3_mk_bit2bool)(Z3_context, unsigned int, Z3_ast);
ay_sig_Z3_mk_bit2bool const ay_link_Z3_mk_bit2bool = &Z3_mk_bit2bool;
Z3_ast ay_call_Z3_mk_bit2bool(Z3_context ay_a0, unsigned int ay_a1, Z3_ast ay_a2) {
    return Z3_mk_bit2bool(ay_a0, ay_a1, ay_a2);
}

typedef Z3_sort (*ay_sig_Z3_mk_bool_sort)(Z3_context);
ay_sig_Z3_mk_bool_sort const ay_link_Z3_mk_bool_sort = &Z3_mk_bool_sort;
Z3_sort ay_call_Z3_mk_bool_sort(Z3_context ay_a0) {
    return Z3_mk_bool_sort(ay_a0);
}

typedef Z3_ast (*ay_sig_Z3_mk_bound)(Z3_context, unsigned int, Z3_sort);
ay_sig_Z3_mk_bound const ay_link_Z3_mk_bound = &Z3_mk_bound;
Z3_ast ay_call_Z3_mk_bound(Z3_context ay_a0, unsigned int ay_a1, Z3_sort ay_a2) {
    return Z3_mk_bound(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_bv2int)(Z3_context, Z3_ast, bool);
ay_sig_Z3_mk_bv2int const ay_link_Z3_mk_bv2int = &Z3_mk_bv2int;
Z3_ast ay_call_Z3_mk_bv2int(Z3_context ay_a0, Z3_ast ay_a1, bool ay_a2) {
    return Z3_mk_bv2int(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_bv_numeral)(Z3_context, unsigned int, const bool *);
ay_sig_Z3_mk_bv_numeral const ay_link_Z3_mk_bv_numeral = &Z3_mk_bv_numeral;
Z3_ast ay_call_Z3_mk_bv_numeral(Z3_context ay_a0, unsigned int ay_a1, const bool * ay_a2) {
    return Z3_mk_bv_numeral(ay_a0, ay_a1, ay_a2);
}

typedef Z3_sort (*ay_sig_Z3_mk_bv_sort)(Z3_context, unsigned int);
ay_sig_Z3_mk_bv_sort const ay_link_Z3_mk_bv_sort = &Z3_mk_bv_sort;
Z3_sort ay_call_Z3_mk_bv_sort(Z3_context ay_a0, unsigned int ay_a1) {
    return Z3_mk_bv_sort(ay_a0, ay_a1);
}

typedef Z3_ast (*ay_sig_Z3_mk_bvadd_no_overflow)(Z3_context, Z3_ast, Z3_ast, bool);
ay_sig_Z3_mk_bvadd_no_overflow const ay_link_Z3_mk_bvadd_no_overflow = &Z3_mk_bvadd_no_overflow;
Z3_ast ay_call_Z3_mk_bvadd_no_overflow(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2, bool ay_a3) {
    return Z3_mk_bvadd_no_overflow(ay_a0, ay_a1, ay_a2, ay_a3);
}

typedef Z3_ast (*ay_sig_Z3_mk_bvadd_no_underflow)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_mk_bvadd_no_underflow const ay_link_Z3_mk_bvadd_no_underflow = &Z3_mk_bvadd_no_underflow;
Z3_ast ay_call_Z3_mk_bvadd_no_underflow(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_mk_bvadd_no_underflow(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_bvadd)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_mk_bvadd const ay_link_Z3_mk_bvadd = &Z3_mk_bvadd;
Z3_ast ay_call_Z3_mk_bvadd(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_mk_bvadd(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_bvand)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_mk_bvand const ay_link_Z3_mk_bvand = &Z3_mk_bvand;
Z3_ast ay_call_Z3_mk_bvand(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_mk_bvand(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_bvashr)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_mk_bvashr const ay_link_Z3_mk_bvashr = &Z3_mk_bvashr;
Z3_ast ay_call_Z3_mk_bvashr(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_mk_bvashr(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_bvlshr)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_mk_bvlshr const ay_link_Z3_mk_bvlshr = &Z3_mk_bvlshr;
Z3_ast ay_call_Z3_mk_bvlshr(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_mk_bvlshr(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_bvmul_no_overflow)(Z3_context, Z3_ast, Z3_ast, bool);
ay_sig_Z3_mk_bvmul_no_overflow const ay_link_Z3_mk_bvmul_no_overflow = &Z3_mk_bvmul_no_overflow;
Z3_ast ay_call_Z3_mk_bvmul_no_overflow(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2, bool ay_a3) {
    return Z3_mk_bvmul_no_overflow(ay_a0, ay_a1, ay_a2, ay_a3);
}

typedef Z3_ast (*ay_sig_Z3_mk_bvmul_no_underflow)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_mk_bvmul_no_underflow const ay_link_Z3_mk_bvmul_no_underflow = &Z3_mk_bvmul_no_underflow;
Z3_ast ay_call_Z3_mk_bvmul_no_underflow(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_mk_bvmul_no_underflow(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_bvmul)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_mk_bvmul const ay_link_Z3_mk_bvmul = &Z3_mk_bvmul;
Z3_ast ay_call_Z3_mk_bvmul(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_mk_bvmul(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_bvnand)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_mk_bvnand const ay_link_Z3_mk_bvnand = &Z3_mk_bvnand;
Z3_ast ay_call_Z3_mk_bvnand(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_mk_bvnand(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_bvneg_no_overflow)(Z3_context, Z3_ast);
ay_sig_Z3_mk_bvneg_no_overflow const ay_link_Z3_mk_bvneg_no_overflow = &Z3_mk_bvneg_no_overflow;
Z3_ast ay_call_Z3_mk_bvneg_no_overflow(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_mk_bvneg_no_overflow(ay_a0, ay_a1);
}

typedef Z3_ast (*ay_sig_Z3_mk_bvneg)(Z3_context, Z3_ast);
ay_sig_Z3_mk_bvneg const ay_link_Z3_mk_bvneg = &Z3_mk_bvneg;
Z3_ast ay_call_Z3_mk_bvneg(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_mk_bvneg(ay_a0, ay_a1);
}

typedef Z3_ast (*ay_sig_Z3_mk_bvnor)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_mk_bvnor const ay_link_Z3_mk_bvnor = &Z3_mk_bvnor;
Z3_ast ay_call_Z3_mk_bvnor(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_mk_bvnor(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_bvnot)(Z3_context, Z3_ast);
ay_sig_Z3_mk_bvnot const ay_link_Z3_mk_bvnot = &Z3_mk_bvnot;
Z3_ast ay_call_Z3_mk_bvnot(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_mk_bvnot(ay_a0, ay_a1);
}

typedef Z3_ast (*ay_sig_Z3_mk_bvor)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_mk_bvor const ay_link_Z3_mk_bvor = &Z3_mk_bvor;
Z3_ast ay_call_Z3_mk_bvor(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_mk_bvor(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_bvredand)(Z3_context, Z3_ast);
ay_sig_Z3_mk_bvredand const ay_link_Z3_mk_bvredand = &Z3_mk_bvredand;
Z3_ast ay_call_Z3_mk_bvredand(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_mk_bvredand(ay_a0, ay_a1);
}

typedef Z3_ast (*ay_sig_Z3_mk_bvredor)(Z3_context, Z3_ast);
ay_sig_Z3_mk_bvredor const ay_link_Z3_mk_bvredor = &Z3_mk_bvredor;
Z3_ast ay_call_Z3_mk_bvredor(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_mk_bvredor(ay_a0, ay_a1);
}

typedef Z3_ast (*ay_sig_Z3_mk_bvsdiv_no_overflow)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_mk_bvsdiv_no_overflow const ay_link_Z3_mk_bvsdiv_no_overflow = &Z3_mk_bvsdiv_no_overflow;
Z3_ast ay_call_Z3_mk_bvsdiv_no_overflow(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_mk_bvsdiv_no_overflow(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_bvsdiv)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_mk_bvsdiv const ay_link_Z3_mk_bvsdiv = &Z3_mk_bvsdiv;
Z3_ast ay_call_Z3_mk_bvsdiv(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_mk_bvsdiv(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_bvsge)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_mk_bvsge const ay_link_Z3_mk_bvsge = &Z3_mk_bvsge;
Z3_ast ay_call_Z3_mk_bvsge(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_mk_bvsge(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_bvsgt)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_mk_bvsgt const ay_link_Z3_mk_bvsgt = &Z3_mk_bvsgt;
Z3_ast ay_call_Z3_mk_bvsgt(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_mk_bvsgt(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_bvshl)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_mk_bvshl const ay_link_Z3_mk_bvshl = &Z3_mk_bvshl;
Z3_ast ay_call_Z3_mk_bvshl(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_mk_bvshl(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_bvsle)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_mk_bvsle const ay_link_Z3_mk_bvsle = &Z3_mk_bvsle;
Z3_ast ay_call_Z3_mk_bvsle(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_mk_bvsle(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_bvslt)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_mk_bvslt const ay_link_Z3_mk_bvslt = &Z3_mk_bvslt;
Z3_ast ay_call_Z3_mk_bvslt(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_mk_bvslt(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_bvsmod)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_mk_bvsmod const ay_link_Z3_mk_bvsmod = &Z3_mk_bvsmod;
Z3_ast ay_call_Z3_mk_bvsmod(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_mk_bvsmod(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_bvsrem)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_mk_bvsrem const ay_link_Z3_mk_bvsrem = &Z3_mk_bvsrem;
Z3_ast ay_call_Z3_mk_bvsrem(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_mk_bvsrem(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_bvsub_no_overflow)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_mk_bvsub_no_overflow const ay_link_Z3_mk_bvsub_no_overflow = &Z3_mk_bvsub_no_overflow;
Z3_ast ay_call_Z3_mk_bvsub_no_overflow(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_mk_bvsub_no_overflow(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_bvsub_no_underflow)(Z3_context, Z3_ast, Z3_ast, bool);
ay_sig_Z3_mk_bvsub_no_underflow const ay_link_Z3_mk_bvsub_no_underflow = &Z3_mk_bvsub_no_underflow;
Z3_ast ay_call_Z3_mk_bvsub_no_underflow(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2, bool ay_a3) {
    return Z3_mk_bvsub_no_underflow(ay_a0, ay_a1, ay_a2, ay_a3);
}

typedef Z3_ast (*ay_sig_Z3_mk_bvsub)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_mk_bvsub const ay_link_Z3_mk_bvsub = &Z3_mk_bvsub;
Z3_ast ay_call_Z3_mk_bvsub(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_mk_bvsub(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_bvudiv)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_mk_bvudiv const ay_link_Z3_mk_bvudiv = &Z3_mk_bvudiv;
Z3_ast ay_call_Z3_mk_bvudiv(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_mk_bvudiv(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_bvuge)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_mk_bvuge const ay_link_Z3_mk_bvuge = &Z3_mk_bvuge;
Z3_ast ay_call_Z3_mk_bvuge(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_mk_bvuge(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_bvugt)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_mk_bvugt const ay_link_Z3_mk_bvugt = &Z3_mk_bvugt;
Z3_ast ay_call_Z3_mk_bvugt(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_mk_bvugt(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_bvule)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_mk_bvule const ay_link_Z3_mk_bvule = &Z3_mk_bvule;
Z3_ast ay_call_Z3_mk_bvule(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_mk_bvule(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_bvult)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_mk_bvult const ay_link_Z3_mk_bvult = &Z3_mk_bvult;
Z3_ast ay_call_Z3_mk_bvult(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_mk_bvult(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_bvurem)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_mk_bvurem const ay_link_Z3_mk_bvurem = &Z3_mk_bvurem;
Z3_ast ay_call_Z3_mk_bvurem(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_mk_bvurem(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_bvxnor)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_mk_bvxnor const ay_link_Z3_mk_bvxnor = &Z3_mk_bvxnor;
Z3_ast ay_call_Z3_mk_bvxnor(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_mk_bvxnor(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_bvxor)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_mk_bvxor const ay_link_Z3_mk_bvxor = &Z3_mk_bvxor;
Z3_ast ay_call_Z3_mk_bvxor(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_mk_bvxor(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_char_from_bv)(Z3_context, Z3_ast);
ay_sig_Z3_mk_char_from_bv const ay_link_Z3_mk_char_from_bv = &Z3_mk_char_from_bv;
Z3_ast ay_call_Z3_mk_char_from_bv(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_mk_char_from_bv(ay_a0, ay_a1);
}

typedef Z3_ast (*ay_sig_Z3_mk_char_is_digit)(Z3_context, Z3_ast);
ay_sig_Z3_mk_char_is_digit const ay_link_Z3_mk_char_is_digit = &Z3_mk_char_is_digit;
Z3_ast ay_call_Z3_mk_char_is_digit(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_mk_char_is_digit(ay_a0, ay_a1);
}

typedef Z3_ast (*ay_sig_Z3_mk_char_le)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_mk_char_le const ay_link_Z3_mk_char_le = &Z3_mk_char_le;
Z3_ast ay_call_Z3_mk_char_le(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_mk_char_le(ay_a0, ay_a1, ay_a2);
}

typedef Z3_sort (*ay_sig_Z3_mk_char_sort)(Z3_context);
ay_sig_Z3_mk_char_sort const ay_link_Z3_mk_char_sort = &Z3_mk_char_sort;
Z3_sort ay_call_Z3_mk_char_sort(Z3_context ay_a0) {
    return Z3_mk_char_sort(ay_a0);
}

typedef Z3_ast (*ay_sig_Z3_mk_char_to_bv)(Z3_context, Z3_ast);
ay_sig_Z3_mk_char_to_bv const ay_link_Z3_mk_char_to_bv = &Z3_mk_char_to_bv;
Z3_ast ay_call_Z3_mk_char_to_bv(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_mk_char_to_bv(ay_a0, ay_a1);
}

typedef Z3_ast (*ay_sig_Z3_mk_char_to_int)(Z3_context, Z3_ast);
ay_sig_Z3_mk_char_to_int const ay_link_Z3_mk_char_to_int = &Z3_mk_char_to_int;
Z3_ast ay_call_Z3_mk_char_to_int(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_mk_char_to_int(ay_a0, ay_a1);
}

typedef Z3_ast (*ay_sig_Z3_mk_char)(Z3_context, unsigned int);
ay_sig_Z3_mk_char const ay_link_Z3_mk_char = &Z3_mk_char;
Z3_ast ay_call_Z3_mk_char(Z3_context ay_a0, unsigned int ay_a1) {
    return Z3_mk_char(ay_a0, ay_a1);
}

typedef Z3_ast (*ay_sig_Z3_mk_concat)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_mk_concat const ay_link_Z3_mk_concat = &Z3_mk_concat;
Z3_ast ay_call_Z3_mk_concat(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_mk_concat(ay_a0, ay_a1, ay_a2);
}

typedef Z3_config (*ay_sig_Z3_mk_config)(void);
ay_sig_Z3_mk_config const ay_link_Z3_mk_config = &Z3_mk_config;
Z3_config ay_call_Z3_mk_config(void) {
    return Z3_mk_config();
}

typedef Z3_ast (*ay_sig_Z3_mk_const_array)(Z3_context, Z3_sort, Z3_ast);
ay_sig_Z3_mk_const_array const ay_link_Z3_mk_const_array = &Z3_mk_const_array;
Z3_ast ay_call_Z3_mk_const_array(Z3_context ay_a0, Z3_sort ay_a1, Z3_ast ay_a2) {
    return Z3_mk_const_array(ay_a0, ay_a1, ay_a2);
}

typedef Z3_constructor_list (*ay_sig_Z3_mk_constructor_list)(Z3_context, unsigned int, const Z3_constructor *);
ay_sig_Z3_mk_constructor_list const ay_link_Z3_mk_constructor_list = &Z3_mk_constructor_list;
Z3_constructor_list ay_call_Z3_mk_constructor_list(Z3_context ay_a0, unsigned int ay_a1, const Z3_constructor * ay_a2) {
    return Z3_mk_constructor_list(ay_a0, ay_a1, ay_a2);
}

typedef Z3_constructor (*ay_sig_Z3_mk_constructor)(Z3_context, Z3_symbol, Z3_symbol, unsigned int, const Z3_symbol *, const Z3_sort *, unsigned int *);
ay_sig_Z3_mk_constructor const ay_link_Z3_mk_constructor = &Z3_mk_constructor;
Z3_constructor ay_call_Z3_mk_constructor(Z3_context ay_a0, Z3_symbol ay_a1, Z3_symbol ay_a2, unsigned int ay_a3, const Z3_symbol * ay_a4, const Z3_sort * ay_a5, unsigned int * ay_a6) {
    return Z3_mk_constructor(ay_a0, ay_a1, ay_a2, ay_a3, ay_a4, ay_a5, ay_a6);
}

typedef Z3_ast (*ay_sig_Z3_mk_const)(Z3_context, Z3_symbol, Z3_sort);
ay_sig_Z3_mk_const const ay_link_Z3_mk_const = &Z3_mk_const;
Z3_ast ay_call_Z3_mk_const(Z3_context ay_a0, Z3_symbol ay_a1, Z3_sort ay_a2) {
    return Z3_mk_const(ay_a0, ay_a1, ay_a2);
}

typedef Z3_context (*ay_sig_Z3_mk_context_rc)(Z3_config);
ay_sig_Z3_mk_context_rc const ay_link_Z3_mk_context_rc = &Z3_mk_context_rc;
Z3_context ay_call_Z3_mk_context_rc(Z3_config ay_a0) {
    return Z3_mk_context_rc(ay_a0);
}

typedef Z3_context (*ay_sig_Z3_mk_context)(Z3_config);
ay_sig_Z3_mk_context const ay_link_Z3_mk_context = &Z3_mk_context;
Z3_context ay_call_Z3_mk_context(Z3_config ay_a0) {
    return Z3_mk_context(ay_a0);
}

typedef Z3_sort (*ay_sig_Z3_mk_datatype_sort)(Z3_context, Z3_symbol, unsigned int, const Z3_sort *);
ay_sig_Z3_mk_datatype_sort const ay_link_Z3_mk_datatype_sort = &Z3_mk_datatype_sort;
Z3_sort ay_call_Z3_mk_datatype_sort(Z3_context ay_a0, Z3_symbol ay_a1, unsigned int ay_a2, const Z3_sort * ay_a3) {
    return Z3_mk_datatype_sort(ay_a0, ay_a1, ay_a2, ay_a3);
}

typedef void (*ay_sig_Z3_mk_datatypes)(Z3_context, unsigned int, const Z3_symbol *, Z3_sort *, Z3_constructor_list *);
ay_sig_Z3_mk_datatypes const ay_link_Z3_mk_datatypes = &Z3_mk_datatypes;
void ay_call_Z3_mk_datatypes(Z3_context ay_a0, unsigned int ay_a1, const Z3_symbol * ay_a2, Z3_sort * ay_a3, Z3_constructor_list * ay_a4) {
    Z3_mk_datatypes(ay_a0, ay_a1, ay_a2, ay_a3, ay_a4);
}

typedef Z3_sort (*ay_sig_Z3_mk_datatype)(Z3_context, Z3_symbol, unsigned int, Z3_constructor *);
ay_sig_Z3_mk_datatype const ay_link_Z3_mk_datatype = &Z3_mk_datatype;
Z3_sort ay_call_Z3_mk_datatype(Z3_context ay_a0, Z3_symbol ay_a1, unsigned int ay_a2, Z3_constructor * ay_a3) {
    return Z3_mk_datatype(ay_a0, ay_a1, ay_a2, ay_a3);
}

typedef Z3_ast (*ay_sig_Z3_mk_distinct)(Z3_context, unsigned int, const Z3_ast *);
ay_sig_Z3_mk_distinct const ay_link_Z3_mk_distinct = &Z3_mk_distinct;
Z3_ast ay_call_Z3_mk_distinct(Z3_context ay_a0, unsigned int ay_a1, const Z3_ast * ay_a2) {
    return Z3_mk_distinct(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_divides)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_mk_divides const ay_link_Z3_mk_divides = &Z3_mk_divides;
Z3_ast ay_call_Z3_mk_divides(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_mk_divides(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_div)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_mk_div const ay_link_Z3_mk_div = &Z3_mk_div;
Z3_ast ay_call_Z3_mk_div(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_mk_div(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_empty_set)(Z3_context, Z3_sort);
ay_sig_Z3_mk_empty_set const ay_link_Z3_mk_empty_set = &Z3_mk_empty_set;
Z3_ast ay_call_Z3_mk_empty_set(Z3_context ay_a0, Z3_sort ay_a1) {
    return Z3_mk_empty_set(ay_a0, ay_a1);
}

typedef Z3_sort (*ay_sig_Z3_mk_enumeration_sort)(Z3_context, Z3_symbol, unsigned int, const Z3_symbol *, Z3_func_decl *, Z3_func_decl *);
ay_sig_Z3_mk_enumeration_sort const ay_link_Z3_mk_enumeration_sort = &Z3_mk_enumeration_sort;
Z3_sort ay_call_Z3_mk_enumeration_sort(Z3_context ay_a0, Z3_symbol ay_a1, unsigned int ay_a2, const Z3_symbol * ay_a3, Z3_func_decl * ay_a4, Z3_func_decl * ay_a5) {
    return Z3_mk_enumeration_sort(ay_a0, ay_a1, ay_a2, ay_a3, ay_a4, ay_a5);
}

typedef Z3_ast (*ay_sig_Z3_mk_eq)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_mk_eq const ay_link_Z3_mk_eq = &Z3_mk_eq;
Z3_ast ay_call_Z3_mk_eq(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_mk_eq(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_exists_const)(Z3_context, unsigned int, unsigned int, const Z3_app *, unsigned int, const Z3_pattern *, Z3_ast);
ay_sig_Z3_mk_exists_const const ay_link_Z3_mk_exists_const = &Z3_mk_exists_const;
Z3_ast ay_call_Z3_mk_exists_const(Z3_context ay_a0, unsigned int ay_a1, unsigned int ay_a2, const Z3_app * ay_a3, unsigned int ay_a4, const Z3_pattern * ay_a5, Z3_ast ay_a6) {
    return Z3_mk_exists_const(ay_a0, ay_a1, ay_a2, ay_a3, ay_a4, ay_a5, ay_a6);
}

typedef Z3_ast (*ay_sig_Z3_mk_exists)(Z3_context, unsigned int, unsigned int, const Z3_pattern *, unsigned int, const Z3_sort *, const Z3_symbol *, Z3_ast);
ay_sig_Z3_mk_exists const ay_link_Z3_mk_exists = &Z3_mk_exists;
Z3_ast ay_call_Z3_mk_exists(Z3_context ay_a0, unsigned int ay_a1, unsigned int ay_a2, const Z3_pattern * ay_a3, unsigned int ay_a4, const Z3_sort * ay_a5, const Z3_symbol * ay_a6, Z3_ast ay_a7) {
    return Z3_mk_exists(ay_a0, ay_a1, ay_a2, ay_a3, ay_a4, ay_a5, ay_a6, ay_a7);
}

typedef Z3_ast (*ay_sig_Z3_mk_ext_rotate_left)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_mk_ext_rotate_left const ay_link_Z3_mk_ext_rotate_left = &Z3_mk_ext_rotate_left;
Z3_ast ay_call_Z3_mk_ext_rotate_left(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_mk_ext_rotate_left(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_ext_rotate_right)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_mk_ext_rotate_right const ay_link_Z3_mk_ext_rotate_right = &Z3_mk_ext_rotate_right;
Z3_ast ay_call_Z3_mk_ext_rotate_right(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_mk_ext_rotate_right(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_extract)(Z3_context, unsigned int, unsigned int, Z3_ast);
ay_sig_Z3_mk_extract const ay_link_Z3_mk_extract = &Z3_mk_extract;
Z3_ast ay_call_Z3_mk_extract(Z3_context ay_a0, unsigned int ay_a1, unsigned int ay_a2, Z3_ast ay_a3) {
    return Z3_mk_extract(ay_a0, ay_a1, ay_a2, ay_a3);
}

typedef Z3_ast (*ay_sig_Z3_mk_false)(Z3_context);
ay_sig_Z3_mk_false const ay_link_Z3_mk_false = &Z3_mk_false;
Z3_ast ay_call_Z3_mk_false(Z3_context ay_a0) {
    return Z3_mk_false(ay_a0);
}

typedef Z3_sort (*ay_sig_Z3_mk_finite_domain_sort)(Z3_context, Z3_symbol, uint64_t);
ay_sig_Z3_mk_finite_domain_sort const ay_link_Z3_mk_finite_domain_sort = &Z3_mk_finite_domain_sort;
Z3_sort ay_call_Z3_mk_finite_domain_sort(Z3_context ay_a0, Z3_symbol ay_a1, uint64_t ay_a2) {
    return Z3_mk_finite_domain_sort(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_finite_set_difference)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_mk_finite_set_difference const ay_link_Z3_mk_finite_set_difference = &Z3_mk_finite_set_difference;
Z3_ast ay_call_Z3_mk_finite_set_difference(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_mk_finite_set_difference(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_finite_set_empty)(Z3_context, Z3_sort);
ay_sig_Z3_mk_finite_set_empty const ay_link_Z3_mk_finite_set_empty = &Z3_mk_finite_set_empty;
Z3_ast ay_call_Z3_mk_finite_set_empty(Z3_context ay_a0, Z3_sort ay_a1) {
    return Z3_mk_finite_set_empty(ay_a0, ay_a1);
}

typedef Z3_ast (*ay_sig_Z3_mk_finite_set_filter)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_mk_finite_set_filter const ay_link_Z3_mk_finite_set_filter = &Z3_mk_finite_set_filter;
Z3_ast ay_call_Z3_mk_finite_set_filter(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_mk_finite_set_filter(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_finite_set_intersect)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_mk_finite_set_intersect const ay_link_Z3_mk_finite_set_intersect = &Z3_mk_finite_set_intersect;
Z3_ast ay_call_Z3_mk_finite_set_intersect(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_mk_finite_set_intersect(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_finite_set_map)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_mk_finite_set_map const ay_link_Z3_mk_finite_set_map = &Z3_mk_finite_set_map;
Z3_ast ay_call_Z3_mk_finite_set_map(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_mk_finite_set_map(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_finite_set_member)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_mk_finite_set_member const ay_link_Z3_mk_finite_set_member = &Z3_mk_finite_set_member;
Z3_ast ay_call_Z3_mk_finite_set_member(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_mk_finite_set_member(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_finite_set_range)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_mk_finite_set_range const ay_link_Z3_mk_finite_set_range = &Z3_mk_finite_set_range;
Z3_ast ay_call_Z3_mk_finite_set_range(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_mk_finite_set_range(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_finite_set_singleton)(Z3_context, Z3_ast);
ay_sig_Z3_mk_finite_set_singleton const ay_link_Z3_mk_finite_set_singleton = &Z3_mk_finite_set_singleton;
Z3_ast ay_call_Z3_mk_finite_set_singleton(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_mk_finite_set_singleton(ay_a0, ay_a1);
}

typedef Z3_ast (*ay_sig_Z3_mk_finite_set_size)(Z3_context, Z3_ast);
ay_sig_Z3_mk_finite_set_size const ay_link_Z3_mk_finite_set_size = &Z3_mk_finite_set_size;
Z3_ast ay_call_Z3_mk_finite_set_size(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_mk_finite_set_size(ay_a0, ay_a1);
}

typedef Z3_sort (*ay_sig_Z3_mk_finite_set_sort)(Z3_context, Z3_sort);
ay_sig_Z3_mk_finite_set_sort const ay_link_Z3_mk_finite_set_sort = &Z3_mk_finite_set_sort;
Z3_sort ay_call_Z3_mk_finite_set_sort(Z3_context ay_a0, Z3_sort ay_a1) {
    return Z3_mk_finite_set_sort(ay_a0, ay_a1);
}

typedef Z3_ast (*ay_sig_Z3_mk_finite_set_subset)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_mk_finite_set_subset const ay_link_Z3_mk_finite_set_subset = &Z3_mk_finite_set_subset;
Z3_ast ay_call_Z3_mk_finite_set_subset(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_mk_finite_set_subset(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_finite_set_union)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_mk_finite_set_union const ay_link_Z3_mk_finite_set_union = &Z3_mk_finite_set_union;
Z3_ast ay_call_Z3_mk_finite_set_union(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_mk_finite_set_union(ay_a0, ay_a1, ay_a2);
}

typedef Z3_fixedpoint (*ay_sig_Z3_mk_fixedpoint)(Z3_context);
ay_sig_Z3_mk_fixedpoint const ay_link_Z3_mk_fixedpoint = &Z3_mk_fixedpoint;
Z3_fixedpoint ay_call_Z3_mk_fixedpoint(Z3_context ay_a0) {
    return Z3_mk_fixedpoint(ay_a0);
}

typedef Z3_ast (*ay_sig_Z3_mk_forall_const)(Z3_context, unsigned int, unsigned int, const Z3_app *, unsigned int, const Z3_pattern *, Z3_ast);
ay_sig_Z3_mk_forall_const const ay_link_Z3_mk_forall_const = &Z3_mk_forall_const;
Z3_ast ay_call_Z3_mk_forall_const(Z3_context ay_a0, unsigned int ay_a1, unsigned int ay_a2, const Z3_app * ay_a3, unsigned int ay_a4, const Z3_pattern * ay_a5, Z3_ast ay_a6) {
    return Z3_mk_forall_const(ay_a0, ay_a1, ay_a2, ay_a3, ay_a4, ay_a5, ay_a6);
}

typedef Z3_ast (*ay_sig_Z3_mk_forall)(Z3_context, unsigned int, unsigned int, const Z3_pattern *, unsigned int, const Z3_sort *, const Z3_symbol *, Z3_ast);
ay_sig_Z3_mk_forall const ay_link_Z3_mk_forall = &Z3_mk_forall;
Z3_ast ay_call_Z3_mk_forall(Z3_context ay_a0, unsigned int ay_a1, unsigned int ay_a2, const Z3_pattern * ay_a3, unsigned int ay_a4, const Z3_sort * ay_a5, const Z3_symbol * ay_a6, Z3_ast ay_a7) {
    return Z3_mk_forall(ay_a0, ay_a1, ay_a2, ay_a3, ay_a4, ay_a5, ay_a6, ay_a7);
}

typedef Z3_ast (*ay_sig_Z3_mk_fpa_abs)(Z3_context, Z3_ast);
ay_sig_Z3_mk_fpa_abs const ay_link_Z3_mk_fpa_abs = &Z3_mk_fpa_abs;
Z3_ast ay_call_Z3_mk_fpa_abs(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_mk_fpa_abs(ay_a0, ay_a1);
}

typedef Z3_ast (*ay_sig_Z3_mk_fpa_add)(Z3_context, Z3_ast, Z3_ast, Z3_ast);
ay_sig_Z3_mk_fpa_add const ay_link_Z3_mk_fpa_add = &Z3_mk_fpa_add;
Z3_ast ay_call_Z3_mk_fpa_add(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2, Z3_ast ay_a3) {
    return Z3_mk_fpa_add(ay_a0, ay_a1, ay_a2, ay_a3);
}

typedef Z3_ast (*ay_sig_Z3_mk_fpa_div)(Z3_context, Z3_ast, Z3_ast, Z3_ast);
ay_sig_Z3_mk_fpa_div const ay_link_Z3_mk_fpa_div = &Z3_mk_fpa_div;
Z3_ast ay_call_Z3_mk_fpa_div(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2, Z3_ast ay_a3) {
    return Z3_mk_fpa_div(ay_a0, ay_a1, ay_a2, ay_a3);
}

typedef Z3_ast (*ay_sig_Z3_mk_fpa_eq)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_mk_fpa_eq const ay_link_Z3_mk_fpa_eq = &Z3_mk_fpa_eq;
Z3_ast ay_call_Z3_mk_fpa_eq(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_mk_fpa_eq(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_fpa_fma)(Z3_context, Z3_ast, Z3_ast, Z3_ast, Z3_ast);
ay_sig_Z3_mk_fpa_fma const ay_link_Z3_mk_fpa_fma = &Z3_mk_fpa_fma;
Z3_ast ay_call_Z3_mk_fpa_fma(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2, Z3_ast ay_a3, Z3_ast ay_a4) {
    return Z3_mk_fpa_fma(ay_a0, ay_a1, ay_a2, ay_a3, ay_a4);
}

typedef Z3_ast (*ay_sig_Z3_mk_fpa_fp)(Z3_context, Z3_ast, Z3_ast, Z3_ast);
ay_sig_Z3_mk_fpa_fp const ay_link_Z3_mk_fpa_fp = &Z3_mk_fpa_fp;
Z3_ast ay_call_Z3_mk_fpa_fp(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2, Z3_ast ay_a3) {
    return Z3_mk_fpa_fp(ay_a0, ay_a1, ay_a2, ay_a3);
}

typedef Z3_ast (*ay_sig_Z3_mk_fpa_geq)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_mk_fpa_geq const ay_link_Z3_mk_fpa_geq = &Z3_mk_fpa_geq;
Z3_ast ay_call_Z3_mk_fpa_geq(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_mk_fpa_geq(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_fpa_gt)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_mk_fpa_gt const ay_link_Z3_mk_fpa_gt = &Z3_mk_fpa_gt;
Z3_ast ay_call_Z3_mk_fpa_gt(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_mk_fpa_gt(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_fpa_inf)(Z3_context, Z3_sort, bool);
ay_sig_Z3_mk_fpa_inf const ay_link_Z3_mk_fpa_inf = &Z3_mk_fpa_inf;
Z3_ast ay_call_Z3_mk_fpa_inf(Z3_context ay_a0, Z3_sort ay_a1, bool ay_a2) {
    return Z3_mk_fpa_inf(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_fpa_is_infinite)(Z3_context, Z3_ast);
ay_sig_Z3_mk_fpa_is_infinite const ay_link_Z3_mk_fpa_is_infinite = &Z3_mk_fpa_is_infinite;
Z3_ast ay_call_Z3_mk_fpa_is_infinite(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_mk_fpa_is_infinite(ay_a0, ay_a1);
}

typedef Z3_ast (*ay_sig_Z3_mk_fpa_is_nan)(Z3_context, Z3_ast);
ay_sig_Z3_mk_fpa_is_nan const ay_link_Z3_mk_fpa_is_nan = &Z3_mk_fpa_is_nan;
Z3_ast ay_call_Z3_mk_fpa_is_nan(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_mk_fpa_is_nan(ay_a0, ay_a1);
}

typedef Z3_ast (*ay_sig_Z3_mk_fpa_is_negative)(Z3_context, Z3_ast);
ay_sig_Z3_mk_fpa_is_negative const ay_link_Z3_mk_fpa_is_negative = &Z3_mk_fpa_is_negative;
Z3_ast ay_call_Z3_mk_fpa_is_negative(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_mk_fpa_is_negative(ay_a0, ay_a1);
}

typedef Z3_ast (*ay_sig_Z3_mk_fpa_is_normal)(Z3_context, Z3_ast);
ay_sig_Z3_mk_fpa_is_normal const ay_link_Z3_mk_fpa_is_normal = &Z3_mk_fpa_is_normal;
Z3_ast ay_call_Z3_mk_fpa_is_normal(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_mk_fpa_is_normal(ay_a0, ay_a1);
}

typedef Z3_ast (*ay_sig_Z3_mk_fpa_is_positive)(Z3_context, Z3_ast);
ay_sig_Z3_mk_fpa_is_positive const ay_link_Z3_mk_fpa_is_positive = &Z3_mk_fpa_is_positive;
Z3_ast ay_call_Z3_mk_fpa_is_positive(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_mk_fpa_is_positive(ay_a0, ay_a1);
}

typedef Z3_ast (*ay_sig_Z3_mk_fpa_is_subnormal)(Z3_context, Z3_ast);
ay_sig_Z3_mk_fpa_is_subnormal const ay_link_Z3_mk_fpa_is_subnormal = &Z3_mk_fpa_is_subnormal;
Z3_ast ay_call_Z3_mk_fpa_is_subnormal(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_mk_fpa_is_subnormal(ay_a0, ay_a1);
}

typedef Z3_ast (*ay_sig_Z3_mk_fpa_is_zero)(Z3_context, Z3_ast);
ay_sig_Z3_mk_fpa_is_zero const ay_link_Z3_mk_fpa_is_zero = &Z3_mk_fpa_is_zero;
Z3_ast ay_call_Z3_mk_fpa_is_zero(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_mk_fpa_is_zero(ay_a0, ay_a1);
}

typedef Z3_ast (*ay_sig_Z3_mk_fpa_leq)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_mk_fpa_leq const ay_link_Z3_mk_fpa_leq = &Z3_mk_fpa_leq;
Z3_ast ay_call_Z3_mk_fpa_leq(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_mk_fpa_leq(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_fpa_lt)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_mk_fpa_lt const ay_link_Z3_mk_fpa_lt = &Z3_mk_fpa_lt;
Z3_ast ay_call_Z3_mk_fpa_lt(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_mk_fpa_lt(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_fpa_max)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_mk_fpa_max const ay_link_Z3_mk_fpa_max = &Z3_mk_fpa_max;
Z3_ast ay_call_Z3_mk_fpa_max(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_mk_fpa_max(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_fpa_min)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_mk_fpa_min const ay_link_Z3_mk_fpa_min = &Z3_mk_fpa_min;
Z3_ast ay_call_Z3_mk_fpa_min(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_mk_fpa_min(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_fpa_mul)(Z3_context, Z3_ast, Z3_ast, Z3_ast);
ay_sig_Z3_mk_fpa_mul const ay_link_Z3_mk_fpa_mul = &Z3_mk_fpa_mul;
Z3_ast ay_call_Z3_mk_fpa_mul(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2, Z3_ast ay_a3) {
    return Z3_mk_fpa_mul(ay_a0, ay_a1, ay_a2, ay_a3);
}

typedef Z3_ast (*ay_sig_Z3_mk_fpa_nan)(Z3_context, Z3_sort);
ay_sig_Z3_mk_fpa_nan const ay_link_Z3_mk_fpa_nan = &Z3_mk_fpa_nan;
Z3_ast ay_call_Z3_mk_fpa_nan(Z3_context ay_a0, Z3_sort ay_a1) {
    return Z3_mk_fpa_nan(ay_a0, ay_a1);
}

typedef Z3_ast (*ay_sig_Z3_mk_fpa_neg)(Z3_context, Z3_ast);
ay_sig_Z3_mk_fpa_neg const ay_link_Z3_mk_fpa_neg = &Z3_mk_fpa_neg;
Z3_ast ay_call_Z3_mk_fpa_neg(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_mk_fpa_neg(ay_a0, ay_a1);
}

typedef Z3_ast (*ay_sig_Z3_mk_fpa_numeral_double)(Z3_context, double, Z3_sort);
ay_sig_Z3_mk_fpa_numeral_double const ay_link_Z3_mk_fpa_numeral_double = &Z3_mk_fpa_numeral_double;
Z3_ast ay_call_Z3_mk_fpa_numeral_double(Z3_context ay_a0, double ay_a1, Z3_sort ay_a2) {
    return Z3_mk_fpa_numeral_double(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_fpa_numeral_float)(Z3_context, float, Z3_sort);
ay_sig_Z3_mk_fpa_numeral_float const ay_link_Z3_mk_fpa_numeral_float = &Z3_mk_fpa_numeral_float;
Z3_ast ay_call_Z3_mk_fpa_numeral_float(Z3_context ay_a0, float ay_a1, Z3_sort ay_a2) {
    return Z3_mk_fpa_numeral_float(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_fpa_numeral_int64_uint64)(Z3_context, bool, int64_t, uint64_t, Z3_sort);
ay_sig_Z3_mk_fpa_numeral_int64_uint64 const ay_link_Z3_mk_fpa_numeral_int64_uint64 = &Z3_mk_fpa_numeral_int64_uint64;
Z3_ast ay_call_Z3_mk_fpa_numeral_int64_uint64(Z3_context ay_a0, bool ay_a1, int64_t ay_a2, uint64_t ay_a3, Z3_sort ay_a4) {
    return Z3_mk_fpa_numeral_int64_uint64(ay_a0, ay_a1, ay_a2, ay_a3, ay_a4);
}

typedef Z3_ast (*ay_sig_Z3_mk_fpa_numeral_int_uint)(Z3_context, bool, int, unsigned int, Z3_sort);
ay_sig_Z3_mk_fpa_numeral_int_uint const ay_link_Z3_mk_fpa_numeral_int_uint = &Z3_mk_fpa_numeral_int_uint;
Z3_ast ay_call_Z3_mk_fpa_numeral_int_uint(Z3_context ay_a0, bool ay_a1, int ay_a2, unsigned int ay_a3, Z3_sort ay_a4) {
    return Z3_mk_fpa_numeral_int_uint(ay_a0, ay_a1, ay_a2, ay_a3, ay_a4);
}

typedef Z3_ast (*ay_sig_Z3_mk_fpa_numeral_int)(Z3_context, int, Z3_sort);
ay_sig_Z3_mk_fpa_numeral_int const ay_link_Z3_mk_fpa_numeral_int = &Z3_mk_fpa_numeral_int;
Z3_ast ay_call_Z3_mk_fpa_numeral_int(Z3_context ay_a0, int ay_a1, Z3_sort ay_a2) {
    return Z3_mk_fpa_numeral_int(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_fpa_rem)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_mk_fpa_rem const ay_link_Z3_mk_fpa_rem = &Z3_mk_fpa_rem;
Z3_ast ay_call_Z3_mk_fpa_rem(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_mk_fpa_rem(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_fpa_rna)(Z3_context);
ay_sig_Z3_mk_fpa_rna const ay_link_Z3_mk_fpa_rna = &Z3_mk_fpa_rna;
Z3_ast ay_call_Z3_mk_fpa_rna(Z3_context ay_a0) {
    return Z3_mk_fpa_rna(ay_a0);
}

typedef Z3_ast (*ay_sig_Z3_mk_fpa_rne)(Z3_context);
ay_sig_Z3_mk_fpa_rne const ay_link_Z3_mk_fpa_rne = &Z3_mk_fpa_rne;
Z3_ast ay_call_Z3_mk_fpa_rne(Z3_context ay_a0) {
    return Z3_mk_fpa_rne(ay_a0);
}

typedef Z3_ast (*ay_sig_Z3_mk_fpa_round_nearest_ties_to_away)(Z3_context);
ay_sig_Z3_mk_fpa_round_nearest_ties_to_away const ay_link_Z3_mk_fpa_round_nearest_ties_to_away = &Z3_mk_fpa_round_nearest_ties_to_away;
Z3_ast ay_call_Z3_mk_fpa_round_nearest_ties_to_away(Z3_context ay_a0) {
    return Z3_mk_fpa_round_nearest_ties_to_away(ay_a0);
}

typedef Z3_ast (*ay_sig_Z3_mk_fpa_round_nearest_ties_to_even)(Z3_context);
ay_sig_Z3_mk_fpa_round_nearest_ties_to_even const ay_link_Z3_mk_fpa_round_nearest_ties_to_even = &Z3_mk_fpa_round_nearest_ties_to_even;
Z3_ast ay_call_Z3_mk_fpa_round_nearest_ties_to_even(Z3_context ay_a0) {
    return Z3_mk_fpa_round_nearest_ties_to_even(ay_a0);
}

typedef Z3_ast (*ay_sig_Z3_mk_fpa_round_to_integral)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_mk_fpa_round_to_integral const ay_link_Z3_mk_fpa_round_to_integral = &Z3_mk_fpa_round_to_integral;
Z3_ast ay_call_Z3_mk_fpa_round_to_integral(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_mk_fpa_round_to_integral(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_fpa_round_toward_negative)(Z3_context);
ay_sig_Z3_mk_fpa_round_toward_negative const ay_link_Z3_mk_fpa_round_toward_negative = &Z3_mk_fpa_round_toward_negative;
Z3_ast ay_call_Z3_mk_fpa_round_toward_negative(Z3_context ay_a0) {
    return Z3_mk_fpa_round_toward_negative(ay_a0);
}

typedef Z3_ast (*ay_sig_Z3_mk_fpa_round_toward_positive)(Z3_context);
ay_sig_Z3_mk_fpa_round_toward_positive const ay_link_Z3_mk_fpa_round_toward_positive = &Z3_mk_fpa_round_toward_positive;
Z3_ast ay_call_Z3_mk_fpa_round_toward_positive(Z3_context ay_a0) {
    return Z3_mk_fpa_round_toward_positive(ay_a0);
}

typedef Z3_ast (*ay_sig_Z3_mk_fpa_round_toward_zero)(Z3_context);
ay_sig_Z3_mk_fpa_round_toward_zero const ay_link_Z3_mk_fpa_round_toward_zero = &Z3_mk_fpa_round_toward_zero;
Z3_ast ay_call_Z3_mk_fpa_round_toward_zero(Z3_context ay_a0) {
    return Z3_mk_fpa_round_toward_zero(ay_a0);
}

typedef Z3_sort (*ay_sig_Z3_mk_fpa_rounding_mode_sort)(Z3_context);
ay_sig_Z3_mk_fpa_rounding_mode_sort const ay_link_Z3_mk_fpa_rounding_mode_sort = &Z3_mk_fpa_rounding_mode_sort;
Z3_sort ay_call_Z3_mk_fpa_rounding_mode_sort(Z3_context ay_a0) {
    return Z3_mk_fpa_rounding_mode_sort(ay_a0);
}

typedef Z3_ast (*ay_sig_Z3_mk_fpa_rtn)(Z3_context);
ay_sig_Z3_mk_fpa_rtn const ay_link_Z3_mk_fpa_rtn = &Z3_mk_fpa_rtn;
Z3_ast ay_call_Z3_mk_fpa_rtn(Z3_context ay_a0) {
    return Z3_mk_fpa_rtn(ay_a0);
}

typedef Z3_ast (*ay_sig_Z3_mk_fpa_rtp)(Z3_context);
ay_sig_Z3_mk_fpa_rtp const ay_link_Z3_mk_fpa_rtp = &Z3_mk_fpa_rtp;
Z3_ast ay_call_Z3_mk_fpa_rtp(Z3_context ay_a0) {
    return Z3_mk_fpa_rtp(ay_a0);
}

typedef Z3_ast (*ay_sig_Z3_mk_fpa_rtz)(Z3_context);
ay_sig_Z3_mk_fpa_rtz const ay_link_Z3_mk_fpa_rtz = &Z3_mk_fpa_rtz;
Z3_ast ay_call_Z3_mk_fpa_rtz(Z3_context ay_a0) {
    return Z3_mk_fpa_rtz(ay_a0);
}

typedef Z3_sort (*ay_sig_Z3_mk_fpa_sort_128)(Z3_context);
ay_sig_Z3_mk_fpa_sort_128 const ay_link_Z3_mk_fpa_sort_128 = &Z3_mk_fpa_sort_128;
Z3_sort ay_call_Z3_mk_fpa_sort_128(Z3_context ay_a0) {
    return Z3_mk_fpa_sort_128(ay_a0);
}

typedef Z3_sort (*ay_sig_Z3_mk_fpa_sort_16)(Z3_context);
ay_sig_Z3_mk_fpa_sort_16 const ay_link_Z3_mk_fpa_sort_16 = &Z3_mk_fpa_sort_16;
Z3_sort ay_call_Z3_mk_fpa_sort_16(Z3_context ay_a0) {
    return Z3_mk_fpa_sort_16(ay_a0);
}

typedef Z3_sort (*ay_sig_Z3_mk_fpa_sort_32)(Z3_context);
ay_sig_Z3_mk_fpa_sort_32 const ay_link_Z3_mk_fpa_sort_32 = &Z3_mk_fpa_sort_32;
Z3_sort ay_call_Z3_mk_fpa_sort_32(Z3_context ay_a0) {
    return Z3_mk_fpa_sort_32(ay_a0);
}

typedef Z3_sort (*ay_sig_Z3_mk_fpa_sort_64)(Z3_context);
ay_sig_Z3_mk_fpa_sort_64 const ay_link_Z3_mk_fpa_sort_64 = &Z3_mk_fpa_sort_64;
Z3_sort ay_call_Z3_mk_fpa_sort_64(Z3_context ay_a0) {
    return Z3_mk_fpa_sort_64(ay_a0);
}

typedef Z3_sort (*ay_sig_Z3_mk_fpa_sort_double)(Z3_context);
ay_sig_Z3_mk_fpa_sort_double const ay_link_Z3_mk_fpa_sort_double = &Z3_mk_fpa_sort_double;
Z3_sort ay_call_Z3_mk_fpa_sort_double(Z3_context ay_a0) {
    return Z3_mk_fpa_sort_double(ay_a0);
}

typedef Z3_sort (*ay_sig_Z3_mk_fpa_sort_half)(Z3_context);
ay_sig_Z3_mk_fpa_sort_half const ay_link_Z3_mk_fpa_sort_half = &Z3_mk_fpa_sort_half;
Z3_sort ay_call_Z3_mk_fpa_sort_half(Z3_context ay_a0) {
    return Z3_mk_fpa_sort_half(ay_a0);
}

typedef Z3_sort (*ay_sig_Z3_mk_fpa_sort_quadruple)(Z3_context);
ay_sig_Z3_mk_fpa_sort_quadruple const ay_link_Z3_mk_fpa_sort_quadruple = &Z3_mk_fpa_sort_quadruple;
Z3_sort ay_call_Z3_mk_fpa_sort_quadruple(Z3_context ay_a0) {
    return Z3_mk_fpa_sort_quadruple(ay_a0);
}

typedef Z3_sort (*ay_sig_Z3_mk_fpa_sort_single)(Z3_context);
ay_sig_Z3_mk_fpa_sort_single const ay_link_Z3_mk_fpa_sort_single = &Z3_mk_fpa_sort_single;
Z3_sort ay_call_Z3_mk_fpa_sort_single(Z3_context ay_a0) {
    return Z3_mk_fpa_sort_single(ay_a0);
}

typedef Z3_sort (*ay_sig_Z3_mk_fpa_sort)(Z3_context, unsigned int, unsigned int);
ay_sig_Z3_mk_fpa_sort const ay_link_Z3_mk_fpa_sort = &Z3_mk_fpa_sort;
Z3_sort ay_call_Z3_mk_fpa_sort(Z3_context ay_a0, unsigned int ay_a1, unsigned int ay_a2) {
    return Z3_mk_fpa_sort(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_fpa_sqrt)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_mk_fpa_sqrt const ay_link_Z3_mk_fpa_sqrt = &Z3_mk_fpa_sqrt;
Z3_ast ay_call_Z3_mk_fpa_sqrt(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_mk_fpa_sqrt(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_fpa_sub)(Z3_context, Z3_ast, Z3_ast, Z3_ast);
ay_sig_Z3_mk_fpa_sub const ay_link_Z3_mk_fpa_sub = &Z3_mk_fpa_sub;
Z3_ast ay_call_Z3_mk_fpa_sub(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2, Z3_ast ay_a3) {
    return Z3_mk_fpa_sub(ay_a0, ay_a1, ay_a2, ay_a3);
}

typedef Z3_ast (*ay_sig_Z3_mk_fpa_to_fp_bv)(Z3_context, Z3_ast, Z3_sort);
ay_sig_Z3_mk_fpa_to_fp_bv const ay_link_Z3_mk_fpa_to_fp_bv = &Z3_mk_fpa_to_fp_bv;
Z3_ast ay_call_Z3_mk_fpa_to_fp_bv(Z3_context ay_a0, Z3_ast ay_a1, Z3_sort ay_a2) {
    return Z3_mk_fpa_to_fp_bv(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_fpa_to_fp_float)(Z3_context, Z3_ast, Z3_ast, Z3_sort);
ay_sig_Z3_mk_fpa_to_fp_float const ay_link_Z3_mk_fpa_to_fp_float = &Z3_mk_fpa_to_fp_float;
Z3_ast ay_call_Z3_mk_fpa_to_fp_float(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2, Z3_sort ay_a3) {
    return Z3_mk_fpa_to_fp_float(ay_a0, ay_a1, ay_a2, ay_a3);
}

typedef Z3_ast (*ay_sig_Z3_mk_fpa_to_fp_int_real)(Z3_context, Z3_ast, Z3_ast, Z3_ast, Z3_sort);
ay_sig_Z3_mk_fpa_to_fp_int_real const ay_link_Z3_mk_fpa_to_fp_int_real = &Z3_mk_fpa_to_fp_int_real;
Z3_ast ay_call_Z3_mk_fpa_to_fp_int_real(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2, Z3_ast ay_a3, Z3_sort ay_a4) {
    return Z3_mk_fpa_to_fp_int_real(ay_a0, ay_a1, ay_a2, ay_a3, ay_a4);
}

typedef Z3_ast (*ay_sig_Z3_mk_fpa_to_fp_real)(Z3_context, Z3_ast, Z3_ast, Z3_sort);
ay_sig_Z3_mk_fpa_to_fp_real const ay_link_Z3_mk_fpa_to_fp_real = &Z3_mk_fpa_to_fp_real;
Z3_ast ay_call_Z3_mk_fpa_to_fp_real(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2, Z3_sort ay_a3) {
    return Z3_mk_fpa_to_fp_real(ay_a0, ay_a1, ay_a2, ay_a3);
}

typedef Z3_ast (*ay_sig_Z3_mk_fpa_to_fp_signed)(Z3_context, Z3_ast, Z3_ast, Z3_sort);
ay_sig_Z3_mk_fpa_to_fp_signed const ay_link_Z3_mk_fpa_to_fp_signed = &Z3_mk_fpa_to_fp_signed;
Z3_ast ay_call_Z3_mk_fpa_to_fp_signed(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2, Z3_sort ay_a3) {
    return Z3_mk_fpa_to_fp_signed(ay_a0, ay_a1, ay_a2, ay_a3);
}

typedef Z3_ast (*ay_sig_Z3_mk_fpa_to_fp_unsigned)(Z3_context, Z3_ast, Z3_ast, Z3_sort);
ay_sig_Z3_mk_fpa_to_fp_unsigned const ay_link_Z3_mk_fpa_to_fp_unsigned = &Z3_mk_fpa_to_fp_unsigned;
Z3_ast ay_call_Z3_mk_fpa_to_fp_unsigned(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2, Z3_sort ay_a3) {
    return Z3_mk_fpa_to_fp_unsigned(ay_a0, ay_a1, ay_a2, ay_a3);
}

typedef Z3_ast (*ay_sig_Z3_mk_fpa_to_ieee_bv)(Z3_context, Z3_ast);
ay_sig_Z3_mk_fpa_to_ieee_bv const ay_link_Z3_mk_fpa_to_ieee_bv = &Z3_mk_fpa_to_ieee_bv;
Z3_ast ay_call_Z3_mk_fpa_to_ieee_bv(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_mk_fpa_to_ieee_bv(ay_a0, ay_a1);
}

typedef Z3_ast (*ay_sig_Z3_mk_fpa_to_real)(Z3_context, Z3_ast);
ay_sig_Z3_mk_fpa_to_real const ay_link_Z3_mk_fpa_to_real = &Z3_mk_fpa_to_real;
Z3_ast ay_call_Z3_mk_fpa_to_real(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_mk_fpa_to_real(ay_a0, ay_a1);
}

typedef Z3_ast (*ay_sig_Z3_mk_fpa_to_sbv)(Z3_context, Z3_ast, Z3_ast, unsigned int);
ay_sig_Z3_mk_fpa_to_sbv const ay_link_Z3_mk_fpa_to_sbv = &Z3_mk_fpa_to_sbv;
Z3_ast ay_call_Z3_mk_fpa_to_sbv(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2, unsigned int ay_a3) {
    return Z3_mk_fpa_to_sbv(ay_a0, ay_a1, ay_a2, ay_a3);
}

typedef Z3_ast (*ay_sig_Z3_mk_fpa_to_ubv)(Z3_context, Z3_ast, Z3_ast, unsigned int);
ay_sig_Z3_mk_fpa_to_ubv const ay_link_Z3_mk_fpa_to_ubv = &Z3_mk_fpa_to_ubv;
Z3_ast ay_call_Z3_mk_fpa_to_ubv(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2, unsigned int ay_a3) {
    return Z3_mk_fpa_to_ubv(ay_a0, ay_a1, ay_a2, ay_a3);
}

typedef Z3_ast (*ay_sig_Z3_mk_fpa_zero)(Z3_context, Z3_sort, bool);
ay_sig_Z3_mk_fpa_zero const ay_link_Z3_mk_fpa_zero = &Z3_mk_fpa_zero;
Z3_ast ay_call_Z3_mk_fpa_zero(Z3_context ay_a0, Z3_sort ay_a1, bool ay_a2) {
    return Z3_mk_fpa_zero(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_fresh_const)(Z3_context, Z3_string, Z3_sort);
ay_sig_Z3_mk_fresh_const const ay_link_Z3_mk_fresh_const = &Z3_mk_fresh_const;
Z3_ast ay_call_Z3_mk_fresh_const(Z3_context ay_a0, Z3_string ay_a1, Z3_sort ay_a2) {
    return Z3_mk_fresh_const(ay_a0, ay_a1, ay_a2);
}

typedef Z3_func_decl (*ay_sig_Z3_mk_fresh_func_decl)(Z3_context, Z3_string, unsigned int, const Z3_sort *, Z3_sort);
ay_sig_Z3_mk_fresh_func_decl const ay_link_Z3_mk_fresh_func_decl = &Z3_mk_fresh_func_decl;
Z3_func_decl ay_call_Z3_mk_fresh_func_decl(Z3_context ay_a0, Z3_string ay_a1, unsigned int ay_a2, const Z3_sort * ay_a3, Z3_sort ay_a4) {
    return Z3_mk_fresh_func_decl(ay_a0, ay_a1, ay_a2, ay_a3, ay_a4);
}

typedef Z3_ast (*ay_sig_Z3_mk_full_set)(Z3_context, Z3_sort);
ay_sig_Z3_mk_full_set const ay_link_Z3_mk_full_set = &Z3_mk_full_set;
Z3_ast ay_call_Z3_mk_full_set(Z3_context ay_a0, Z3_sort ay_a1) {
    return Z3_mk_full_set(ay_a0, ay_a1);
}

typedef Z3_func_decl (*ay_sig_Z3_mk_func_decl)(Z3_context, Z3_symbol, unsigned int, const Z3_sort *, Z3_sort);
ay_sig_Z3_mk_func_decl const ay_link_Z3_mk_func_decl = &Z3_mk_func_decl;
Z3_func_decl ay_call_Z3_mk_func_decl(Z3_context ay_a0, Z3_symbol ay_a1, unsigned int ay_a2, const Z3_sort * ay_a3, Z3_sort ay_a4) {
    return Z3_mk_func_decl(ay_a0, ay_a1, ay_a2, ay_a3, ay_a4);
}

typedef Z3_ast (*ay_sig_Z3_mk_ge)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_mk_ge const ay_link_Z3_mk_ge = &Z3_mk_ge;
Z3_ast ay_call_Z3_mk_ge(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_mk_ge(ay_a0, ay_a1, ay_a2);
}

typedef Z3_goal (*ay_sig_Z3_mk_goal)(Z3_context, bool, bool, bool);
ay_sig_Z3_mk_goal const ay_link_Z3_mk_goal = &Z3_mk_goal;
Z3_goal ay_call_Z3_mk_goal(Z3_context ay_a0, bool ay_a1, bool ay_a2, bool ay_a3) {
    return Z3_mk_goal(ay_a0, ay_a1, ay_a2, ay_a3);
}

typedef Z3_ast (*ay_sig_Z3_mk_gt)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_mk_gt const ay_link_Z3_mk_gt = &Z3_mk_gt;
Z3_ast ay_call_Z3_mk_gt(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_mk_gt(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_iff)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_mk_iff const ay_link_Z3_mk_iff = &Z3_mk_iff;
Z3_ast ay_call_Z3_mk_iff(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_mk_iff(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_implies)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_mk_implies const ay_link_Z3_mk_implies = &Z3_mk_implies;
Z3_ast ay_call_Z3_mk_implies(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_mk_implies(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_int2bv)(Z3_context, unsigned int, Z3_ast);
ay_sig_Z3_mk_int2bv const ay_link_Z3_mk_int2bv = &Z3_mk_int2bv;
Z3_ast ay_call_Z3_mk_int2bv(Z3_context ay_a0, unsigned int ay_a1, Z3_ast ay_a2) {
    return Z3_mk_int2bv(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_int2real)(Z3_context, Z3_ast);
ay_sig_Z3_mk_int2real const ay_link_Z3_mk_int2real = &Z3_mk_int2real;
Z3_ast ay_call_Z3_mk_int2real(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_mk_int2real(ay_a0, ay_a1);
}

typedef Z3_ast (*ay_sig_Z3_mk_int64)(Z3_context, int64_t, Z3_sort);
ay_sig_Z3_mk_int64 const ay_link_Z3_mk_int64 = &Z3_mk_int64;
Z3_ast ay_call_Z3_mk_int64(Z3_context ay_a0, int64_t ay_a1, Z3_sort ay_a2) {
    return Z3_mk_int64(ay_a0, ay_a1, ay_a2);
}

typedef Z3_sort (*ay_sig_Z3_mk_int_sort)(Z3_context);
ay_sig_Z3_mk_int_sort const ay_link_Z3_mk_int_sort = &Z3_mk_int_sort;
Z3_sort ay_call_Z3_mk_int_sort(Z3_context ay_a0) {
    return Z3_mk_int_sort(ay_a0);
}

typedef Z3_symbol (*ay_sig_Z3_mk_int_symbol)(Z3_context, int);
ay_sig_Z3_mk_int_symbol const ay_link_Z3_mk_int_symbol = &Z3_mk_int_symbol;
Z3_symbol ay_call_Z3_mk_int_symbol(Z3_context ay_a0, int ay_a1) {
    return Z3_mk_int_symbol(ay_a0, ay_a1);
}

typedef Z3_ast (*ay_sig_Z3_mk_int_to_str)(Z3_context, Z3_ast);
ay_sig_Z3_mk_int_to_str const ay_link_Z3_mk_int_to_str = &Z3_mk_int_to_str;
Z3_ast ay_call_Z3_mk_int_to_str(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_mk_int_to_str(ay_a0, ay_a1);
}

typedef Z3_ast (*ay_sig_Z3_mk_int)(Z3_context, int, Z3_sort);
ay_sig_Z3_mk_int const ay_link_Z3_mk_int = &Z3_mk_int;
Z3_ast ay_call_Z3_mk_int(Z3_context ay_a0, int ay_a1, Z3_sort ay_a2) {
    return Z3_mk_int(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_is_int)(Z3_context, Z3_ast);
ay_sig_Z3_mk_is_int const ay_link_Z3_mk_is_int = &Z3_mk_is_int;
Z3_ast ay_call_Z3_mk_is_int(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_mk_is_int(ay_a0, ay_a1);
}

typedef Z3_ast (*ay_sig_Z3_mk_ite)(Z3_context, Z3_ast, Z3_ast, Z3_ast);
ay_sig_Z3_mk_ite const ay_link_Z3_mk_ite = &Z3_mk_ite;
Z3_ast ay_call_Z3_mk_ite(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2, Z3_ast ay_a3) {
    return Z3_mk_ite(ay_a0, ay_a1, ay_a2, ay_a3);
}

typedef Z3_ast (*ay_sig_Z3_mk_lambda_const)(Z3_context, unsigned int, const Z3_app *, Z3_ast);
ay_sig_Z3_mk_lambda_const const ay_link_Z3_mk_lambda_const = &Z3_mk_lambda_const;
Z3_ast ay_call_Z3_mk_lambda_const(Z3_context ay_a0, unsigned int ay_a1, const Z3_app * ay_a2, Z3_ast ay_a3) {
    return Z3_mk_lambda_const(ay_a0, ay_a1, ay_a2, ay_a3);
}

typedef Z3_ast (*ay_sig_Z3_mk_lambda)(Z3_context, unsigned int, const Z3_sort *, const Z3_symbol *, Z3_ast);
ay_sig_Z3_mk_lambda const ay_link_Z3_mk_lambda = &Z3_mk_lambda;
Z3_ast ay_call_Z3_mk_lambda(Z3_context ay_a0, unsigned int ay_a1, const Z3_sort * ay_a2, const Z3_symbol * ay_a3, Z3_ast ay_a4) {
    return Z3_mk_lambda(ay_a0, ay_a1, ay_a2, ay_a3, ay_a4);
}

typedef Z3_ast (*ay_sig_Z3_mk_le)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_mk_le const ay_link_Z3_mk_le = &Z3_mk_le;
Z3_ast ay_call_Z3_mk_le(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_mk_le(ay_a0, ay_a1, ay_a2);
}

typedef Z3_func_decl (*ay_sig_Z3_mk_linear_order)(Z3_context, Z3_sort, unsigned int);
ay_sig_Z3_mk_linear_order const ay_link_Z3_mk_linear_order = &Z3_mk_linear_order;
Z3_func_decl ay_call_Z3_mk_linear_order(Z3_context ay_a0, Z3_sort ay_a1, unsigned int ay_a2) {
    return Z3_mk_linear_order(ay_a0, ay_a1, ay_a2);
}

typedef Z3_sort (*ay_sig_Z3_mk_list_sort)(Z3_context, Z3_symbol, Z3_sort, Z3_func_decl *, Z3_func_decl *, Z3_func_decl *, Z3_func_decl *, Z3_func_decl *, Z3_func_decl *);
ay_sig_Z3_mk_list_sort const ay_link_Z3_mk_list_sort = &Z3_mk_list_sort;
Z3_sort ay_call_Z3_mk_list_sort(Z3_context ay_a0, Z3_symbol ay_a1, Z3_sort ay_a2, Z3_func_decl * ay_a3, Z3_func_decl * ay_a4, Z3_func_decl * ay_a5, Z3_func_decl * ay_a6, Z3_func_decl * ay_a7, Z3_func_decl * ay_a8) {
    return Z3_mk_list_sort(ay_a0, ay_a1, ay_a2, ay_a3, ay_a4, ay_a5, ay_a6, ay_a7, ay_a8);
}

typedef Z3_ast (*ay_sig_Z3_mk_lstring)(Z3_context, unsigned int, Z3_string);
ay_sig_Z3_mk_lstring const ay_link_Z3_mk_lstring = &Z3_mk_lstring;
Z3_ast ay_call_Z3_mk_lstring(Z3_context ay_a0, unsigned int ay_a1, Z3_string ay_a2) {
    return Z3_mk_lstring(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_lt)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_mk_lt const ay_link_Z3_mk_lt = &Z3_mk_lt;
Z3_ast ay_call_Z3_mk_lt(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_mk_lt(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_map)(Z3_context, Z3_func_decl, unsigned int, const Z3_ast *);
ay_sig_Z3_mk_map const ay_link_Z3_mk_map = &Z3_mk_map;
Z3_ast ay_call_Z3_mk_map(Z3_context ay_a0, Z3_func_decl ay_a1, unsigned int ay_a2, const Z3_ast * ay_a3) {
    return Z3_mk_map(ay_a0, ay_a1, ay_a2, ay_a3);
}

typedef Z3_model (*ay_sig_Z3_mk_model)(Z3_context);
ay_sig_Z3_mk_model const ay_link_Z3_mk_model = &Z3_mk_model;
Z3_model ay_call_Z3_mk_model(Z3_context ay_a0) {
    return Z3_mk_model(ay_a0);
}

typedef Z3_ast (*ay_sig_Z3_mk_mod)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_mk_mod const ay_link_Z3_mk_mod = &Z3_mk_mod;
Z3_ast ay_call_Z3_mk_mod(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_mk_mod(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_mul)(Z3_context, unsigned int, const Z3_ast *);
ay_sig_Z3_mk_mul const ay_link_Z3_mk_mul = &Z3_mk_mul;
Z3_ast ay_call_Z3_mk_mul(Z3_context ay_a0, unsigned int ay_a1, const Z3_ast * ay_a2) {
    return Z3_mk_mul(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_not)(Z3_context, Z3_ast);
ay_sig_Z3_mk_not const ay_link_Z3_mk_not = &Z3_mk_not;
Z3_ast ay_call_Z3_mk_not(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_mk_not(ay_a0, ay_a1);
}

typedef Z3_ast (*ay_sig_Z3_mk_numeral)(Z3_context, Z3_string, Z3_sort);
ay_sig_Z3_mk_numeral const ay_link_Z3_mk_numeral = &Z3_mk_numeral;
Z3_ast ay_call_Z3_mk_numeral(Z3_context ay_a0, Z3_string ay_a1, Z3_sort ay_a2) {
    return Z3_mk_numeral(ay_a0, ay_a1, ay_a2);
}

typedef Z3_optimize (*ay_sig_Z3_mk_optimize)(Z3_context);
ay_sig_Z3_mk_optimize const ay_link_Z3_mk_optimize = &Z3_mk_optimize;
Z3_optimize ay_call_Z3_mk_optimize(Z3_context ay_a0) {
    return Z3_mk_optimize(ay_a0);
}

typedef Z3_ast (*ay_sig_Z3_mk_or)(Z3_context, unsigned int, const Z3_ast *);
ay_sig_Z3_mk_or const ay_link_Z3_mk_or = &Z3_mk_or;
Z3_ast ay_call_Z3_mk_or(Z3_context ay_a0, unsigned int ay_a1, const Z3_ast * ay_a2) {
    return Z3_mk_or(ay_a0, ay_a1, ay_a2);
}

typedef Z3_params (*ay_sig_Z3_mk_params)(Z3_context);
ay_sig_Z3_mk_params const ay_link_Z3_mk_params = &Z3_mk_params;
Z3_params ay_call_Z3_mk_params(Z3_context ay_a0) {
    return Z3_mk_params(ay_a0);
}

typedef Z3_parser_context (*ay_sig_Z3_mk_parser_context)(Z3_context);
ay_sig_Z3_mk_parser_context const ay_link_Z3_mk_parser_context = &Z3_mk_parser_context;
Z3_parser_context ay_call_Z3_mk_parser_context(Z3_context ay_a0) {
    return Z3_mk_parser_context(ay_a0);
}

typedef Z3_func_decl (*ay_sig_Z3_mk_partial_order)(Z3_context, Z3_sort, unsigned int);
ay_sig_Z3_mk_partial_order const ay_link_Z3_mk_partial_order = &Z3_mk_partial_order;
Z3_func_decl ay_call_Z3_mk_partial_order(Z3_context ay_a0, Z3_sort ay_a1, unsigned int ay_a2) {
    return Z3_mk_partial_order(ay_a0, ay_a1, ay_a2);
}

typedef Z3_pattern (*ay_sig_Z3_mk_pattern)(Z3_context, unsigned int, const Z3_ast *);
ay_sig_Z3_mk_pattern const ay_link_Z3_mk_pattern = &Z3_mk_pattern;
Z3_pattern ay_call_Z3_mk_pattern(Z3_context ay_a0, unsigned int ay_a1, const Z3_ast * ay_a2) {
    return Z3_mk_pattern(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_pbeq)(Z3_context, unsigned int, const Z3_ast *, const int *, int);
ay_sig_Z3_mk_pbeq const ay_link_Z3_mk_pbeq = &Z3_mk_pbeq;
Z3_ast ay_call_Z3_mk_pbeq(Z3_context ay_a0, unsigned int ay_a1, const Z3_ast * ay_a2, const int * ay_a3, int ay_a4) {
    return Z3_mk_pbeq(ay_a0, ay_a1, ay_a2, ay_a3, ay_a4);
}

typedef Z3_ast (*ay_sig_Z3_mk_pbge)(Z3_context, unsigned int, const Z3_ast *, const int *, int);
ay_sig_Z3_mk_pbge const ay_link_Z3_mk_pbge = &Z3_mk_pbge;
Z3_ast ay_call_Z3_mk_pbge(Z3_context ay_a0, unsigned int ay_a1, const Z3_ast * ay_a2, const int * ay_a3, int ay_a4) {
    return Z3_mk_pbge(ay_a0, ay_a1, ay_a2, ay_a3, ay_a4);
}

typedef Z3_ast (*ay_sig_Z3_mk_pble)(Z3_context, unsigned int, const Z3_ast *, const int *, int);
ay_sig_Z3_mk_pble const ay_link_Z3_mk_pble = &Z3_mk_pble;
Z3_ast ay_call_Z3_mk_pble(Z3_context ay_a0, unsigned int ay_a1, const Z3_ast * ay_a2, const int * ay_a3, int ay_a4) {
    return Z3_mk_pble(ay_a0, ay_a1, ay_a2, ay_a3, ay_a4);
}

typedef Z3_func_decl (*ay_sig_Z3_mk_piecewise_linear_order)(Z3_context, Z3_sort, unsigned int);
ay_sig_Z3_mk_piecewise_linear_order const ay_link_Z3_mk_piecewise_linear_order = &Z3_mk_piecewise_linear_order;
Z3_func_decl ay_call_Z3_mk_piecewise_linear_order(Z3_context ay_a0, Z3_sort ay_a1, unsigned int ay_a2) {
    return Z3_mk_piecewise_linear_order(ay_a0, ay_a1, ay_a2);
}

typedef Z3_sort (*ay_sig_Z3_mk_polymorphic_datatype)(Z3_context, Z3_symbol, unsigned int, Z3_sort *, unsigned int, Z3_constructor *);
ay_sig_Z3_mk_polymorphic_datatype const ay_link_Z3_mk_polymorphic_datatype = &Z3_mk_polymorphic_datatype;
Z3_sort ay_call_Z3_mk_polymorphic_datatype(Z3_context ay_a0, Z3_symbol ay_a1, unsigned int ay_a2, Z3_sort * ay_a3, unsigned int ay_a4, Z3_constructor * ay_a5) {
    return Z3_mk_polymorphic_datatype(ay_a0, ay_a1, ay_a2, ay_a3, ay_a4, ay_a5);
}

typedef Z3_ast (*ay_sig_Z3_mk_power)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_mk_power const ay_link_Z3_mk_power = &Z3_mk_power;
Z3_ast ay_call_Z3_mk_power(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_mk_power(ay_a0, ay_a1, ay_a2);
}

typedef Z3_probe (*ay_sig_Z3_mk_probe)(Z3_context, Z3_string);
ay_sig_Z3_mk_probe const ay_link_Z3_mk_probe = &Z3_mk_probe;
Z3_probe ay_call_Z3_mk_probe(Z3_context ay_a0, Z3_string ay_a1) {
    return Z3_mk_probe(ay_a0, ay_a1);
}

typedef Z3_ast (*ay_sig_Z3_mk_quantifier_const_ex)(Z3_context, bool, unsigned int, Z3_symbol, Z3_symbol, unsigned int, const Z3_app *, unsigned int, const Z3_pattern *, unsigned int, const Z3_ast *, Z3_ast);
ay_sig_Z3_mk_quantifier_const_ex const ay_link_Z3_mk_quantifier_const_ex = &Z3_mk_quantifier_const_ex;
Z3_ast ay_call_Z3_mk_quantifier_const_ex(Z3_context ay_a0, bool ay_a1, unsigned int ay_a2, Z3_symbol ay_a3, Z3_symbol ay_a4, unsigned int ay_a5, const Z3_app * ay_a6, unsigned int ay_a7, const Z3_pattern * ay_a8, unsigned int ay_a9, const Z3_ast * ay_a10, Z3_ast ay_a11) {
    return Z3_mk_quantifier_const_ex(ay_a0, ay_a1, ay_a2, ay_a3, ay_a4, ay_a5, ay_a6, ay_a7, ay_a8, ay_a9, ay_a10, ay_a11);
}

typedef Z3_ast (*ay_sig_Z3_mk_quantifier_const)(Z3_context, bool, unsigned int, unsigned int, const Z3_app *, unsigned int, const Z3_pattern *, Z3_ast);
ay_sig_Z3_mk_quantifier_const const ay_link_Z3_mk_quantifier_const = &Z3_mk_quantifier_const;
Z3_ast ay_call_Z3_mk_quantifier_const(Z3_context ay_a0, bool ay_a1, unsigned int ay_a2, unsigned int ay_a3, const Z3_app * ay_a4, unsigned int ay_a5, const Z3_pattern * ay_a6, Z3_ast ay_a7) {
    return Z3_mk_quantifier_const(ay_a0, ay_a1, ay_a2, ay_a3, ay_a4, ay_a5, ay_a6, ay_a7);
}

typedef Z3_ast (*ay_sig_Z3_mk_quantifier_ex)(Z3_context, bool, unsigned int, Z3_symbol, Z3_symbol, unsigned int, const Z3_pattern *, unsigned int, const Z3_ast *, unsigned int, const Z3_sort *, const Z3_symbol *, Z3_ast);
ay_sig_Z3_mk_quantifier_ex const ay_link_Z3_mk_quantifier_ex = &Z3_mk_quantifier_ex;
Z3_ast ay_call_Z3_mk_quantifier_ex(Z3_context ay_a0, bool ay_a1, unsigned int ay_a2, Z3_symbol ay_a3, Z3_symbol ay_a4, unsigned int ay_a5, const Z3_pattern * ay_a6, unsigned int ay_a7, const Z3_ast * ay_a8, unsigned int ay_a9, const Z3_sort * ay_a10, const Z3_symbol * ay_a11, Z3_ast ay_a12) {
    return Z3_mk_quantifier_ex(ay_a0, ay_a1, ay_a2, ay_a3, ay_a4, ay_a5, ay_a6, ay_a7, ay_a8, ay_a9, ay_a10, ay_a11, ay_a12);
}

typedef Z3_ast (*ay_sig_Z3_mk_quantifier)(Z3_context, bool, unsigned int, unsigned int, const Z3_pattern *, unsigned int, const Z3_sort *, const Z3_symbol *, Z3_ast);
ay_sig_Z3_mk_quantifier const ay_link_Z3_mk_quantifier = &Z3_mk_quantifier;
Z3_ast ay_call_Z3_mk_quantifier(Z3_context ay_a0, bool ay_a1, unsigned int ay_a2, unsigned int ay_a3, const Z3_pattern * ay_a4, unsigned int ay_a5, const Z3_sort * ay_a6, const Z3_symbol * ay_a7, Z3_ast ay_a8) {
    return Z3_mk_quantifier(ay_a0, ay_a1, ay_a2, ay_a3, ay_a4, ay_a5, ay_a6, ay_a7, ay_a8);
}

typedef Z3_ast (*ay_sig_Z3_mk_re_allchar)(Z3_context, Z3_sort);
ay_sig_Z3_mk_re_allchar const ay_link_Z3_mk_re_allchar = &Z3_mk_re_allchar;
Z3_ast ay_call_Z3_mk_re_allchar(Z3_context ay_a0, Z3_sort ay_a1) {
    return Z3_mk_re_allchar(ay_a0, ay_a1);
}

typedef Z3_ast (*ay_sig_Z3_mk_re_complement)(Z3_context, Z3_ast);
ay_sig_Z3_mk_re_complement const ay_link_Z3_mk_re_complement = &Z3_mk_re_complement;
Z3_ast ay_call_Z3_mk_re_complement(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_mk_re_complement(ay_a0, ay_a1);
}

typedef Z3_ast (*ay_sig_Z3_mk_re_concat)(Z3_context, unsigned int, const Z3_ast *);
ay_sig_Z3_mk_re_concat const ay_link_Z3_mk_re_concat = &Z3_mk_re_concat;
Z3_ast ay_call_Z3_mk_re_concat(Z3_context ay_a0, unsigned int ay_a1, const Z3_ast * ay_a2) {
    return Z3_mk_re_concat(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_re_diff)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_mk_re_diff const ay_link_Z3_mk_re_diff = &Z3_mk_re_diff;
Z3_ast ay_call_Z3_mk_re_diff(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_mk_re_diff(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_re_empty)(Z3_context, Z3_sort);
ay_sig_Z3_mk_re_empty const ay_link_Z3_mk_re_empty = &Z3_mk_re_empty;
Z3_ast ay_call_Z3_mk_re_empty(Z3_context ay_a0, Z3_sort ay_a1) {
    return Z3_mk_re_empty(ay_a0, ay_a1);
}

typedef Z3_ast (*ay_sig_Z3_mk_re_full)(Z3_context, Z3_sort);
ay_sig_Z3_mk_re_full const ay_link_Z3_mk_re_full = &Z3_mk_re_full;
Z3_ast ay_call_Z3_mk_re_full(Z3_context ay_a0, Z3_sort ay_a1) {
    return Z3_mk_re_full(ay_a0, ay_a1);
}

typedef Z3_ast (*ay_sig_Z3_mk_re_intersect)(Z3_context, unsigned int, const Z3_ast *);
ay_sig_Z3_mk_re_intersect const ay_link_Z3_mk_re_intersect = &Z3_mk_re_intersect;
Z3_ast ay_call_Z3_mk_re_intersect(Z3_context ay_a0, unsigned int ay_a1, const Z3_ast * ay_a2) {
    return Z3_mk_re_intersect(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_re_loop)(Z3_context, Z3_ast, unsigned int, unsigned int);
ay_sig_Z3_mk_re_loop const ay_link_Z3_mk_re_loop = &Z3_mk_re_loop;
Z3_ast ay_call_Z3_mk_re_loop(Z3_context ay_a0, Z3_ast ay_a1, unsigned int ay_a2, unsigned int ay_a3) {
    return Z3_mk_re_loop(ay_a0, ay_a1, ay_a2, ay_a3);
}

typedef Z3_ast (*ay_sig_Z3_mk_re_option)(Z3_context, Z3_ast);
ay_sig_Z3_mk_re_option const ay_link_Z3_mk_re_option = &Z3_mk_re_option;
Z3_ast ay_call_Z3_mk_re_option(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_mk_re_option(ay_a0, ay_a1);
}

typedef Z3_ast (*ay_sig_Z3_mk_re_plus)(Z3_context, Z3_ast);
ay_sig_Z3_mk_re_plus const ay_link_Z3_mk_re_plus = &Z3_mk_re_plus;
Z3_ast ay_call_Z3_mk_re_plus(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_mk_re_plus(ay_a0, ay_a1);
}

typedef Z3_ast (*ay_sig_Z3_mk_re_power)(Z3_context, Z3_ast, unsigned int);
ay_sig_Z3_mk_re_power const ay_link_Z3_mk_re_power = &Z3_mk_re_power;
Z3_ast ay_call_Z3_mk_re_power(Z3_context ay_a0, Z3_ast ay_a1, unsigned int ay_a2) {
    return Z3_mk_re_power(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_re_range)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_mk_re_range const ay_link_Z3_mk_re_range = &Z3_mk_re_range;
Z3_ast ay_call_Z3_mk_re_range(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_mk_re_range(ay_a0, ay_a1, ay_a2);
}

typedef Z3_sort (*ay_sig_Z3_mk_re_sort)(Z3_context, Z3_sort);
ay_sig_Z3_mk_re_sort const ay_link_Z3_mk_re_sort = &Z3_mk_re_sort;
Z3_sort ay_call_Z3_mk_re_sort(Z3_context ay_a0, Z3_sort ay_a1) {
    return Z3_mk_re_sort(ay_a0, ay_a1);
}

typedef Z3_ast (*ay_sig_Z3_mk_re_star)(Z3_context, Z3_ast);
ay_sig_Z3_mk_re_star const ay_link_Z3_mk_re_star = &Z3_mk_re_star;
Z3_ast ay_call_Z3_mk_re_star(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_mk_re_star(ay_a0, ay_a1);
}

typedef Z3_ast (*ay_sig_Z3_mk_re_union)(Z3_context, unsigned int, const Z3_ast *);
ay_sig_Z3_mk_re_union const ay_link_Z3_mk_re_union = &Z3_mk_re_union;
Z3_ast ay_call_Z3_mk_re_union(Z3_context ay_a0, unsigned int ay_a1, const Z3_ast * ay_a2) {
    return Z3_mk_re_union(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_real2int)(Z3_context, Z3_ast);
ay_sig_Z3_mk_real2int const ay_link_Z3_mk_real2int = &Z3_mk_real2int;
Z3_ast ay_call_Z3_mk_real2int(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_mk_real2int(ay_a0, ay_a1);
}

typedef Z3_ast (*ay_sig_Z3_mk_real_int64)(Z3_context, int64_t, int64_t);
ay_sig_Z3_mk_real_int64 const ay_link_Z3_mk_real_int64 = &Z3_mk_real_int64;
Z3_ast ay_call_Z3_mk_real_int64(Z3_context ay_a0, int64_t ay_a1, int64_t ay_a2) {
    return Z3_mk_real_int64(ay_a0, ay_a1, ay_a2);
}

typedef Z3_sort (*ay_sig_Z3_mk_real_sort)(Z3_context);
ay_sig_Z3_mk_real_sort const ay_link_Z3_mk_real_sort = &Z3_mk_real_sort;
Z3_sort ay_call_Z3_mk_real_sort(Z3_context ay_a0) {
    return Z3_mk_real_sort(ay_a0);
}

typedef Z3_ast (*ay_sig_Z3_mk_real)(Z3_context, int, int);
ay_sig_Z3_mk_real const ay_link_Z3_mk_real = &Z3_mk_real;
Z3_ast ay_call_Z3_mk_real(Z3_context ay_a0, int ay_a1, int ay_a2) {
    return Z3_mk_real(ay_a0, ay_a1, ay_a2);
}

typedef Z3_func_decl (*ay_sig_Z3_mk_rec_func_decl)(Z3_context, Z3_symbol, unsigned int, const Z3_sort *, Z3_sort);
ay_sig_Z3_mk_rec_func_decl const ay_link_Z3_mk_rec_func_decl = &Z3_mk_rec_func_decl;
Z3_func_decl ay_call_Z3_mk_rec_func_decl(Z3_context ay_a0, Z3_symbol ay_a1, unsigned int ay_a2, const Z3_sort * ay_a3, Z3_sort ay_a4) {
    return Z3_mk_rec_func_decl(ay_a0, ay_a1, ay_a2, ay_a3, ay_a4);
}

typedef Z3_ast (*ay_sig_Z3_mk_rem)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_mk_rem const ay_link_Z3_mk_rem = &Z3_mk_rem;
Z3_ast ay_call_Z3_mk_rem(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_mk_rem(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_repeat)(Z3_context, unsigned int, Z3_ast);
ay_sig_Z3_mk_repeat const ay_link_Z3_mk_repeat = &Z3_mk_repeat;
Z3_ast ay_call_Z3_mk_repeat(Z3_context ay_a0, unsigned int ay_a1, Z3_ast ay_a2) {
    return Z3_mk_repeat(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_rotate_left)(Z3_context, unsigned int, Z3_ast);
ay_sig_Z3_mk_rotate_left const ay_link_Z3_mk_rotate_left = &Z3_mk_rotate_left;
Z3_ast ay_call_Z3_mk_rotate_left(Z3_context ay_a0, unsigned int ay_a1, Z3_ast ay_a2) {
    return Z3_mk_rotate_left(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_rotate_right)(Z3_context, unsigned int, Z3_ast);
ay_sig_Z3_mk_rotate_right const ay_link_Z3_mk_rotate_right = &Z3_mk_rotate_right;
Z3_ast ay_call_Z3_mk_rotate_right(Z3_context ay_a0, unsigned int ay_a1, Z3_ast ay_a2) {
    return Z3_mk_rotate_right(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_sbv_to_str)(Z3_context, Z3_ast);
ay_sig_Z3_mk_sbv_to_str const ay_link_Z3_mk_sbv_to_str = &Z3_mk_sbv_to_str;
Z3_ast ay_call_Z3_mk_sbv_to_str(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_mk_sbv_to_str(ay_a0, ay_a1);
}

typedef Z3_ast (*ay_sig_Z3_mk_select_n)(Z3_context, Z3_ast, unsigned int, const Z3_ast *);
ay_sig_Z3_mk_select_n const ay_link_Z3_mk_select_n = &Z3_mk_select_n;
Z3_ast ay_call_Z3_mk_select_n(Z3_context ay_a0, Z3_ast ay_a1, unsigned int ay_a2, const Z3_ast * ay_a3) {
    return Z3_mk_select_n(ay_a0, ay_a1, ay_a2, ay_a3);
}

typedef Z3_ast (*ay_sig_Z3_mk_select)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_mk_select const ay_link_Z3_mk_select = &Z3_mk_select;
Z3_ast ay_call_Z3_mk_select(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_mk_select(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_seq_at)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_mk_seq_at const ay_link_Z3_mk_seq_at = &Z3_mk_seq_at;
Z3_ast ay_call_Z3_mk_seq_at(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_mk_seq_at(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_seq_concat)(Z3_context, unsigned int, const Z3_ast *);
ay_sig_Z3_mk_seq_concat const ay_link_Z3_mk_seq_concat = &Z3_mk_seq_concat;
Z3_ast ay_call_Z3_mk_seq_concat(Z3_context ay_a0, unsigned int ay_a1, const Z3_ast * ay_a2) {
    return Z3_mk_seq_concat(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_seq_contains)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_mk_seq_contains const ay_link_Z3_mk_seq_contains = &Z3_mk_seq_contains;
Z3_ast ay_call_Z3_mk_seq_contains(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_mk_seq_contains(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_seq_empty)(Z3_context, Z3_sort);
ay_sig_Z3_mk_seq_empty const ay_link_Z3_mk_seq_empty = &Z3_mk_seq_empty;
Z3_ast ay_call_Z3_mk_seq_empty(Z3_context ay_a0, Z3_sort ay_a1) {
    return Z3_mk_seq_empty(ay_a0, ay_a1);
}

typedef Z3_ast (*ay_sig_Z3_mk_seq_extract)(Z3_context, Z3_ast, Z3_ast, Z3_ast);
ay_sig_Z3_mk_seq_extract const ay_link_Z3_mk_seq_extract = &Z3_mk_seq_extract;
Z3_ast ay_call_Z3_mk_seq_extract(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2, Z3_ast ay_a3) {
    return Z3_mk_seq_extract(ay_a0, ay_a1, ay_a2, ay_a3);
}

typedef Z3_ast (*ay_sig_Z3_mk_seq_foldli)(Z3_context, Z3_ast, Z3_ast, Z3_ast, Z3_ast);
ay_sig_Z3_mk_seq_foldli const ay_link_Z3_mk_seq_foldli = &Z3_mk_seq_foldli;
Z3_ast ay_call_Z3_mk_seq_foldli(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2, Z3_ast ay_a3, Z3_ast ay_a4) {
    return Z3_mk_seq_foldli(ay_a0, ay_a1, ay_a2, ay_a3, ay_a4);
}

typedef Z3_ast (*ay_sig_Z3_mk_seq_foldl)(Z3_context, Z3_ast, Z3_ast, Z3_ast);
ay_sig_Z3_mk_seq_foldl const ay_link_Z3_mk_seq_foldl = &Z3_mk_seq_foldl;
Z3_ast ay_call_Z3_mk_seq_foldl(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2, Z3_ast ay_a3) {
    return Z3_mk_seq_foldl(ay_a0, ay_a1, ay_a2, ay_a3);
}

typedef Z3_ast (*ay_sig_Z3_mk_seq_in_re)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_mk_seq_in_re const ay_link_Z3_mk_seq_in_re = &Z3_mk_seq_in_re;
Z3_ast ay_call_Z3_mk_seq_in_re(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_mk_seq_in_re(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_seq_index)(Z3_context, Z3_ast, Z3_ast, Z3_ast);
ay_sig_Z3_mk_seq_index const ay_link_Z3_mk_seq_index = &Z3_mk_seq_index;
Z3_ast ay_call_Z3_mk_seq_index(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2, Z3_ast ay_a3) {
    return Z3_mk_seq_index(ay_a0, ay_a1, ay_a2, ay_a3);
}

typedef Z3_ast (*ay_sig_Z3_mk_seq_last_index)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_mk_seq_last_index const ay_link_Z3_mk_seq_last_index = &Z3_mk_seq_last_index;
Z3_ast ay_call_Z3_mk_seq_last_index(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_mk_seq_last_index(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_seq_length)(Z3_context, Z3_ast);
ay_sig_Z3_mk_seq_length const ay_link_Z3_mk_seq_length = &Z3_mk_seq_length;
Z3_ast ay_call_Z3_mk_seq_length(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_mk_seq_length(ay_a0, ay_a1);
}

typedef Z3_ast (*ay_sig_Z3_mk_seq_mapi)(Z3_context, Z3_ast, Z3_ast, Z3_ast);
ay_sig_Z3_mk_seq_mapi const ay_link_Z3_mk_seq_mapi = &Z3_mk_seq_mapi;
Z3_ast ay_call_Z3_mk_seq_mapi(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2, Z3_ast ay_a3) {
    return Z3_mk_seq_mapi(ay_a0, ay_a1, ay_a2, ay_a3);
}

typedef Z3_ast (*ay_sig_Z3_mk_seq_map)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_mk_seq_map const ay_link_Z3_mk_seq_map = &Z3_mk_seq_map;
Z3_ast ay_call_Z3_mk_seq_map(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_mk_seq_map(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_seq_nth)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_mk_seq_nth const ay_link_Z3_mk_seq_nth = &Z3_mk_seq_nth;
Z3_ast ay_call_Z3_mk_seq_nth(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_mk_seq_nth(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_seq_prefix)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_mk_seq_prefix const ay_link_Z3_mk_seq_prefix = &Z3_mk_seq_prefix;
Z3_ast ay_call_Z3_mk_seq_prefix(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_mk_seq_prefix(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_seq_replace_all)(Z3_context, Z3_ast, Z3_ast, Z3_ast);
ay_sig_Z3_mk_seq_replace_all const ay_link_Z3_mk_seq_replace_all = &Z3_mk_seq_replace_all;
Z3_ast ay_call_Z3_mk_seq_replace_all(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2, Z3_ast ay_a3) {
    return Z3_mk_seq_replace_all(ay_a0, ay_a1, ay_a2, ay_a3);
}

typedef Z3_ast (*ay_sig_Z3_mk_seq_replace_re_all)(Z3_context, Z3_ast, Z3_ast, Z3_ast);
ay_sig_Z3_mk_seq_replace_re_all const ay_link_Z3_mk_seq_replace_re_all = &Z3_mk_seq_replace_re_all;
Z3_ast ay_call_Z3_mk_seq_replace_re_all(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2, Z3_ast ay_a3) {
    return Z3_mk_seq_replace_re_all(ay_a0, ay_a1, ay_a2, ay_a3);
}

typedef Z3_ast (*ay_sig_Z3_mk_seq_replace_re)(Z3_context, Z3_ast, Z3_ast, Z3_ast);
ay_sig_Z3_mk_seq_replace_re const ay_link_Z3_mk_seq_replace_re = &Z3_mk_seq_replace_re;
Z3_ast ay_call_Z3_mk_seq_replace_re(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2, Z3_ast ay_a3) {
    return Z3_mk_seq_replace_re(ay_a0, ay_a1, ay_a2, ay_a3);
}

typedef Z3_ast (*ay_sig_Z3_mk_seq_replace)(Z3_context, Z3_ast, Z3_ast, Z3_ast);
ay_sig_Z3_mk_seq_replace const ay_link_Z3_mk_seq_replace = &Z3_mk_seq_replace;
Z3_ast ay_call_Z3_mk_seq_replace(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2, Z3_ast ay_a3) {
    return Z3_mk_seq_replace(ay_a0, ay_a1, ay_a2, ay_a3);
}

typedef Z3_sort (*ay_sig_Z3_mk_seq_sort)(Z3_context, Z3_sort);
ay_sig_Z3_mk_seq_sort const ay_link_Z3_mk_seq_sort = &Z3_mk_seq_sort;
Z3_sort ay_call_Z3_mk_seq_sort(Z3_context ay_a0, Z3_sort ay_a1) {
    return Z3_mk_seq_sort(ay_a0, ay_a1);
}

typedef Z3_ast (*ay_sig_Z3_mk_seq_suffix)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_mk_seq_suffix const ay_link_Z3_mk_seq_suffix = &Z3_mk_seq_suffix;
Z3_ast ay_call_Z3_mk_seq_suffix(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_mk_seq_suffix(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_seq_to_re)(Z3_context, Z3_ast);
ay_sig_Z3_mk_seq_to_re const ay_link_Z3_mk_seq_to_re = &Z3_mk_seq_to_re;
Z3_ast ay_call_Z3_mk_seq_to_re(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_mk_seq_to_re(ay_a0, ay_a1);
}

typedef Z3_ast (*ay_sig_Z3_mk_seq_unit)(Z3_context, Z3_ast);
ay_sig_Z3_mk_seq_unit const ay_link_Z3_mk_seq_unit = &Z3_mk_seq_unit;
Z3_ast ay_call_Z3_mk_seq_unit(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_mk_seq_unit(ay_a0, ay_a1);
}

typedef Z3_ast (*ay_sig_Z3_mk_set_add)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_mk_set_add const ay_link_Z3_mk_set_add = &Z3_mk_set_add;
Z3_ast ay_call_Z3_mk_set_add(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_mk_set_add(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_set_complement)(Z3_context, Z3_ast);
ay_sig_Z3_mk_set_complement const ay_link_Z3_mk_set_complement = &Z3_mk_set_complement;
Z3_ast ay_call_Z3_mk_set_complement(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_mk_set_complement(ay_a0, ay_a1);
}

typedef Z3_ast (*ay_sig_Z3_mk_set_del)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_mk_set_del const ay_link_Z3_mk_set_del = &Z3_mk_set_del;
Z3_ast ay_call_Z3_mk_set_del(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_mk_set_del(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_set_difference)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_mk_set_difference const ay_link_Z3_mk_set_difference = &Z3_mk_set_difference;
Z3_ast ay_call_Z3_mk_set_difference(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_mk_set_difference(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_set_intersect)(Z3_context, unsigned int, const Z3_ast *);
ay_sig_Z3_mk_set_intersect const ay_link_Z3_mk_set_intersect = &Z3_mk_set_intersect;
Z3_ast ay_call_Z3_mk_set_intersect(Z3_context ay_a0, unsigned int ay_a1, const Z3_ast * ay_a2) {
    return Z3_mk_set_intersect(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_set_member)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_mk_set_member const ay_link_Z3_mk_set_member = &Z3_mk_set_member;
Z3_ast ay_call_Z3_mk_set_member(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_mk_set_member(ay_a0, ay_a1, ay_a2);
}

typedef Z3_sort (*ay_sig_Z3_mk_set_sort)(Z3_context, Z3_sort);
ay_sig_Z3_mk_set_sort const ay_link_Z3_mk_set_sort = &Z3_mk_set_sort;
Z3_sort ay_call_Z3_mk_set_sort(Z3_context ay_a0, Z3_sort ay_a1) {
    return Z3_mk_set_sort(ay_a0, ay_a1);
}

typedef Z3_ast (*ay_sig_Z3_mk_set_subset)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_mk_set_subset const ay_link_Z3_mk_set_subset = &Z3_mk_set_subset;
Z3_ast ay_call_Z3_mk_set_subset(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_mk_set_subset(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_set_union)(Z3_context, unsigned int, const Z3_ast *);
ay_sig_Z3_mk_set_union const ay_link_Z3_mk_set_union = &Z3_mk_set_union;
Z3_ast ay_call_Z3_mk_set_union(Z3_context ay_a0, unsigned int ay_a1, const Z3_ast * ay_a2) {
    return Z3_mk_set_union(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_sign_ext)(Z3_context, unsigned int, Z3_ast);
ay_sig_Z3_mk_sign_ext const ay_link_Z3_mk_sign_ext = &Z3_mk_sign_ext;
Z3_ast ay_call_Z3_mk_sign_ext(Z3_context ay_a0, unsigned int ay_a1, Z3_ast ay_a2) {
    return Z3_mk_sign_ext(ay_a0, ay_a1, ay_a2);
}

typedef Z3_solver (*ay_sig_Z3_mk_simple_solver)(Z3_context);
ay_sig_Z3_mk_simple_solver const ay_link_Z3_mk_simple_solver = &Z3_mk_simple_solver;
Z3_solver ay_call_Z3_mk_simple_solver(Z3_context ay_a0) {
    return Z3_mk_simple_solver(ay_a0);
}

typedef Z3_simplifier (*ay_sig_Z3_mk_simplifier)(Z3_context, Z3_string);
ay_sig_Z3_mk_simplifier const ay_link_Z3_mk_simplifier = &Z3_mk_simplifier;
Z3_simplifier ay_call_Z3_mk_simplifier(Z3_context ay_a0, Z3_string ay_a1) {
    return Z3_mk_simplifier(ay_a0, ay_a1);
}

typedef Z3_solver (*ay_sig_Z3_mk_solver_for_logic)(Z3_context, Z3_symbol);
ay_sig_Z3_mk_solver_for_logic const ay_link_Z3_mk_solver_for_logic = &Z3_mk_solver_for_logic;
Z3_solver ay_call_Z3_mk_solver_for_logic(Z3_context ay_a0, Z3_symbol ay_a1) {
    return Z3_mk_solver_for_logic(ay_a0, ay_a1);
}

typedef Z3_solver (*ay_sig_Z3_mk_solver_from_tactic)(Z3_context, Z3_tactic);
ay_sig_Z3_mk_solver_from_tactic const ay_link_Z3_mk_solver_from_tactic = &Z3_mk_solver_from_tactic;
Z3_solver ay_call_Z3_mk_solver_from_tactic(Z3_context ay_a0, Z3_tactic ay_a1) {
    return Z3_mk_solver_from_tactic(ay_a0, ay_a1);
}

typedef Z3_solver (*ay_sig_Z3_mk_solver)(Z3_context);
ay_sig_Z3_mk_solver const ay_link_Z3_mk_solver = &Z3_mk_solver;
Z3_solver ay_call_Z3_mk_solver(Z3_context ay_a0) {
    return Z3_mk_solver(ay_a0);
}

typedef Z3_ast (*ay_sig_Z3_mk_store_n)(Z3_context, Z3_ast, unsigned int, const Z3_ast *, Z3_ast);
ay_sig_Z3_mk_store_n const ay_link_Z3_mk_store_n = &Z3_mk_store_n;
Z3_ast ay_call_Z3_mk_store_n(Z3_context ay_a0, Z3_ast ay_a1, unsigned int ay_a2, const Z3_ast * ay_a3, Z3_ast ay_a4) {
    return Z3_mk_store_n(ay_a0, ay_a1, ay_a2, ay_a3, ay_a4);
}

typedef Z3_ast (*ay_sig_Z3_mk_store)(Z3_context, Z3_ast, Z3_ast, Z3_ast);
ay_sig_Z3_mk_store const ay_link_Z3_mk_store = &Z3_mk_store;
Z3_ast ay_call_Z3_mk_store(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2, Z3_ast ay_a3) {
    return Z3_mk_store(ay_a0, ay_a1, ay_a2, ay_a3);
}

typedef Z3_ast (*ay_sig_Z3_mk_str_le)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_mk_str_le const ay_link_Z3_mk_str_le = &Z3_mk_str_le;
Z3_ast ay_call_Z3_mk_str_le(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_mk_str_le(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_str_lt)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_mk_str_lt const ay_link_Z3_mk_str_lt = &Z3_mk_str_lt;
Z3_ast ay_call_Z3_mk_str_lt(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_mk_str_lt(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_str_to_int)(Z3_context, Z3_ast);
ay_sig_Z3_mk_str_to_int const ay_link_Z3_mk_str_to_int = &Z3_mk_str_to_int;
Z3_ast ay_call_Z3_mk_str_to_int(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_mk_str_to_int(ay_a0, ay_a1);
}

typedef Z3_ast (*ay_sig_Z3_mk_string_from_code)(Z3_context, Z3_ast);
ay_sig_Z3_mk_string_from_code const ay_link_Z3_mk_string_from_code = &Z3_mk_string_from_code;
Z3_ast ay_call_Z3_mk_string_from_code(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_mk_string_from_code(ay_a0, ay_a1);
}

typedef Z3_sort (*ay_sig_Z3_mk_string_sort)(Z3_context);
ay_sig_Z3_mk_string_sort const ay_link_Z3_mk_string_sort = &Z3_mk_string_sort;
Z3_sort ay_call_Z3_mk_string_sort(Z3_context ay_a0) {
    return Z3_mk_string_sort(ay_a0);
}

typedef Z3_symbol (*ay_sig_Z3_mk_string_symbol)(Z3_context, Z3_string);
ay_sig_Z3_mk_string_symbol const ay_link_Z3_mk_string_symbol = &Z3_mk_string_symbol;
Z3_symbol ay_call_Z3_mk_string_symbol(Z3_context ay_a0, Z3_string ay_a1) {
    return Z3_mk_string_symbol(ay_a0, ay_a1);
}

typedef Z3_ast (*ay_sig_Z3_mk_string_to_code)(Z3_context, Z3_ast);
ay_sig_Z3_mk_string_to_code const ay_link_Z3_mk_string_to_code = &Z3_mk_string_to_code;
Z3_ast ay_call_Z3_mk_string_to_code(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_mk_string_to_code(ay_a0, ay_a1);
}

typedef Z3_ast (*ay_sig_Z3_mk_string)(Z3_context, Z3_string);
ay_sig_Z3_mk_string const ay_link_Z3_mk_string = &Z3_mk_string;
Z3_ast ay_call_Z3_mk_string(Z3_context ay_a0, Z3_string ay_a1) {
    return Z3_mk_string(ay_a0, ay_a1);
}

typedef Z3_ast (*ay_sig_Z3_mk_sub)(Z3_context, unsigned int, const Z3_ast *);
ay_sig_Z3_mk_sub const ay_link_Z3_mk_sub = &Z3_mk_sub;
Z3_ast ay_call_Z3_mk_sub(Z3_context ay_a0, unsigned int ay_a1, const Z3_ast * ay_a2) {
    return Z3_mk_sub(ay_a0, ay_a1, ay_a2);
}

typedef Z3_tactic (*ay_sig_Z3_mk_tactic)(Z3_context, Z3_string);
ay_sig_Z3_mk_tactic const ay_link_Z3_mk_tactic = &Z3_mk_tactic;
Z3_tactic ay_call_Z3_mk_tactic(Z3_context ay_a0, Z3_string ay_a1) {
    return Z3_mk_tactic(ay_a0, ay_a1);
}

typedef Z3_func_decl (*ay_sig_Z3_mk_transitive_closure)(Z3_context, Z3_func_decl);
ay_sig_Z3_mk_transitive_closure const ay_link_Z3_mk_transitive_closure = &Z3_mk_transitive_closure;
Z3_func_decl ay_call_Z3_mk_transitive_closure(Z3_context ay_a0, Z3_func_decl ay_a1) {
    return Z3_mk_transitive_closure(ay_a0, ay_a1);
}

typedef Z3_func_decl (*ay_sig_Z3_mk_tree_order)(Z3_context, Z3_sort, unsigned int);
ay_sig_Z3_mk_tree_order const ay_link_Z3_mk_tree_order = &Z3_mk_tree_order;
Z3_func_decl ay_call_Z3_mk_tree_order(Z3_context ay_a0, Z3_sort ay_a1, unsigned int ay_a2) {
    return Z3_mk_tree_order(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_true)(Z3_context);
ay_sig_Z3_mk_true const ay_link_Z3_mk_true = &Z3_mk_true;
Z3_ast ay_call_Z3_mk_true(Z3_context ay_a0) {
    return Z3_mk_true(ay_a0);
}

typedef Z3_sort (*ay_sig_Z3_mk_tuple_sort)(Z3_context, Z3_symbol, unsigned int, const Z3_symbol *, const Z3_sort *, Z3_func_decl *, Z3_func_decl *);
ay_sig_Z3_mk_tuple_sort const ay_link_Z3_mk_tuple_sort = &Z3_mk_tuple_sort;
Z3_sort ay_call_Z3_mk_tuple_sort(Z3_context ay_a0, Z3_symbol ay_a1, unsigned int ay_a2, const Z3_symbol * ay_a3, const Z3_sort * ay_a4, Z3_func_decl * ay_a5, Z3_func_decl * ay_a6) {
    return Z3_mk_tuple_sort(ay_a0, ay_a1, ay_a2, ay_a3, ay_a4, ay_a5, ay_a6);
}

typedef Z3_sort (*ay_sig_Z3_mk_type_variable)(Z3_context, Z3_symbol);
ay_sig_Z3_mk_type_variable const ay_link_Z3_mk_type_variable = &Z3_mk_type_variable;
Z3_sort ay_call_Z3_mk_type_variable(Z3_context ay_a0, Z3_symbol ay_a1) {
    return Z3_mk_type_variable(ay_a0, ay_a1);
}

typedef Z3_ast (*ay_sig_Z3_mk_u32string)(Z3_context, unsigned int, const unsigned int *);
ay_sig_Z3_mk_u32string const ay_link_Z3_mk_u32string = &Z3_mk_u32string;
Z3_ast ay_call_Z3_mk_u32string(Z3_context ay_a0, unsigned int ay_a1, const unsigned int * ay_a2) {
    return Z3_mk_u32string(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_ubv_to_str)(Z3_context, Z3_ast);
ay_sig_Z3_mk_ubv_to_str const ay_link_Z3_mk_ubv_to_str = &Z3_mk_ubv_to_str;
Z3_ast ay_call_Z3_mk_ubv_to_str(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_mk_ubv_to_str(ay_a0, ay_a1);
}

typedef Z3_ast (*ay_sig_Z3_mk_unary_minus)(Z3_context, Z3_ast);
ay_sig_Z3_mk_unary_minus const ay_link_Z3_mk_unary_minus = &Z3_mk_unary_minus;
Z3_ast ay_call_Z3_mk_unary_minus(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_mk_unary_minus(ay_a0, ay_a1);
}

typedef Z3_sort (*ay_sig_Z3_mk_uninterpreted_sort)(Z3_context, Z3_symbol);
ay_sig_Z3_mk_uninterpreted_sort const ay_link_Z3_mk_uninterpreted_sort = &Z3_mk_uninterpreted_sort;
Z3_sort ay_call_Z3_mk_uninterpreted_sort(Z3_context ay_a0, Z3_symbol ay_a1) {
    return Z3_mk_uninterpreted_sort(ay_a0, ay_a1);
}

typedef Z3_ast (*ay_sig_Z3_mk_unsigned_int64)(Z3_context, uint64_t, Z3_sort);
ay_sig_Z3_mk_unsigned_int64 const ay_link_Z3_mk_unsigned_int64 = &Z3_mk_unsigned_int64;
Z3_ast ay_call_Z3_mk_unsigned_int64(Z3_context ay_a0, uint64_t ay_a1, Z3_sort ay_a2) {
    return Z3_mk_unsigned_int64(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_unsigned_int)(Z3_context, unsigned int, Z3_sort);
ay_sig_Z3_mk_unsigned_int const ay_link_Z3_mk_unsigned_int = &Z3_mk_unsigned_int;
Z3_ast ay_call_Z3_mk_unsigned_int(Z3_context ay_a0, unsigned int ay_a1, Z3_sort ay_a2) {
    return Z3_mk_unsigned_int(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_xor)(Z3_context, Z3_ast, Z3_ast);
ay_sig_Z3_mk_xor const ay_link_Z3_mk_xor = &Z3_mk_xor;
Z3_ast ay_call_Z3_mk_xor(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2) {
    return Z3_mk_xor(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_mk_zero_ext)(Z3_context, unsigned int, Z3_ast);
ay_sig_Z3_mk_zero_ext const ay_link_Z3_mk_zero_ext = &Z3_mk_zero_ext;
Z3_ast ay_call_Z3_mk_zero_ext(Z3_context ay_a0, unsigned int ay_a1, Z3_ast ay_a2) {
    return Z3_mk_zero_ext(ay_a0, ay_a1, ay_a2);
}

typedef void (*ay_sig_Z3_model_dec_ref)(Z3_context, Z3_model);
ay_sig_Z3_model_dec_ref const ay_link_Z3_model_dec_ref = &Z3_model_dec_ref;
void ay_call_Z3_model_dec_ref(Z3_context ay_a0, Z3_model ay_a1) {
    Z3_model_dec_ref(ay_a0, ay_a1);
}

typedef bool (*ay_sig_Z3_model_eval)(Z3_context, Z3_model, Z3_ast, bool, Z3_ast *);
ay_sig_Z3_model_eval const ay_link_Z3_model_eval = &Z3_model_eval;
bool ay_call_Z3_model_eval(Z3_context ay_a0, Z3_model ay_a1, Z3_ast ay_a2, bool ay_a3, Z3_ast * ay_a4) {
    return Z3_model_eval(ay_a0, ay_a1, ay_a2, ay_a3, ay_a4);
}

typedef Z3_ast (*ay_sig_Z3_model_extrapolate)(Z3_context, Z3_model, Z3_ast);
ay_sig_Z3_model_extrapolate const ay_link_Z3_model_extrapolate = &Z3_model_extrapolate;
Z3_ast ay_call_Z3_model_extrapolate(Z3_context ay_a0, Z3_model ay_a1, Z3_ast ay_a2) {
    return Z3_model_extrapolate(ay_a0, ay_a1, ay_a2);
}

typedef Z3_func_decl (*ay_sig_Z3_model_get_const_decl)(Z3_context, Z3_model, unsigned int);
ay_sig_Z3_model_get_const_decl const ay_link_Z3_model_get_const_decl = &Z3_model_get_const_decl;
Z3_func_decl ay_call_Z3_model_get_const_decl(Z3_context ay_a0, Z3_model ay_a1, unsigned int ay_a2) {
    return Z3_model_get_const_decl(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_model_get_const_interp)(Z3_context, Z3_model, Z3_func_decl);
ay_sig_Z3_model_get_const_interp const ay_link_Z3_model_get_const_interp = &Z3_model_get_const_interp;
Z3_ast ay_call_Z3_model_get_const_interp(Z3_context ay_a0, Z3_model ay_a1, Z3_func_decl ay_a2) {
    return Z3_model_get_const_interp(ay_a0, ay_a1, ay_a2);
}

typedef Z3_func_decl (*ay_sig_Z3_model_get_func_decl)(Z3_context, Z3_model, unsigned int);
ay_sig_Z3_model_get_func_decl const ay_link_Z3_model_get_func_decl = &Z3_model_get_func_decl;
Z3_func_decl ay_call_Z3_model_get_func_decl(Z3_context ay_a0, Z3_model ay_a1, unsigned int ay_a2) {
    return Z3_model_get_func_decl(ay_a0, ay_a1, ay_a2);
}

typedef Z3_func_interp (*ay_sig_Z3_model_get_func_interp)(Z3_context, Z3_model, Z3_func_decl);
ay_sig_Z3_model_get_func_interp const ay_link_Z3_model_get_func_interp = &Z3_model_get_func_interp;
Z3_func_interp ay_call_Z3_model_get_func_interp(Z3_context ay_a0, Z3_model ay_a1, Z3_func_decl ay_a2) {
    return Z3_model_get_func_interp(ay_a0, ay_a1, ay_a2);
}

typedef unsigned int (*ay_sig_Z3_model_get_num_consts)(Z3_context, Z3_model);
ay_sig_Z3_model_get_num_consts const ay_link_Z3_model_get_num_consts = &Z3_model_get_num_consts;
unsigned int ay_call_Z3_model_get_num_consts(Z3_context ay_a0, Z3_model ay_a1) {
    return Z3_model_get_num_consts(ay_a0, ay_a1);
}

typedef unsigned int (*ay_sig_Z3_model_get_num_funcs)(Z3_context, Z3_model);
ay_sig_Z3_model_get_num_funcs const ay_link_Z3_model_get_num_funcs = &Z3_model_get_num_funcs;
unsigned int ay_call_Z3_model_get_num_funcs(Z3_context ay_a0, Z3_model ay_a1) {
    return Z3_model_get_num_funcs(ay_a0, ay_a1);
}

typedef unsigned int (*ay_sig_Z3_model_get_num_sorts)(Z3_context, Z3_model);
ay_sig_Z3_model_get_num_sorts const ay_link_Z3_model_get_num_sorts = &Z3_model_get_num_sorts;
unsigned int ay_call_Z3_model_get_num_sorts(Z3_context ay_a0, Z3_model ay_a1) {
    return Z3_model_get_num_sorts(ay_a0, ay_a1);
}

typedef Z3_ast_vector (*ay_sig_Z3_model_get_sort_universe)(Z3_context, Z3_model, Z3_sort);
ay_sig_Z3_model_get_sort_universe const ay_link_Z3_model_get_sort_universe = &Z3_model_get_sort_universe;
Z3_ast_vector ay_call_Z3_model_get_sort_universe(Z3_context ay_a0, Z3_model ay_a1, Z3_sort ay_a2) {
    return Z3_model_get_sort_universe(ay_a0, ay_a1, ay_a2);
}

typedef Z3_sort (*ay_sig_Z3_model_get_sort)(Z3_context, Z3_model, unsigned int);
ay_sig_Z3_model_get_sort const ay_link_Z3_model_get_sort = &Z3_model_get_sort;
Z3_sort ay_call_Z3_model_get_sort(Z3_context ay_a0, Z3_model ay_a1, unsigned int ay_a2) {
    return Z3_model_get_sort(ay_a0, ay_a1, ay_a2);
}

typedef bool (*ay_sig_Z3_model_has_interp)(Z3_context, Z3_model, Z3_func_decl);
ay_sig_Z3_model_has_interp const ay_link_Z3_model_has_interp = &Z3_model_has_interp;
bool ay_call_Z3_model_has_interp(Z3_context ay_a0, Z3_model ay_a1, Z3_func_decl ay_a2) {
    return Z3_model_has_interp(ay_a0, ay_a1, ay_a2);
}

typedef void (*ay_sig_Z3_model_inc_ref)(Z3_context, Z3_model);
ay_sig_Z3_model_inc_ref const ay_link_Z3_model_inc_ref = &Z3_model_inc_ref;
void ay_call_Z3_model_inc_ref(Z3_context ay_a0, Z3_model ay_a1) {
    Z3_model_inc_ref(ay_a0, ay_a1);
}

typedef Z3_string (*ay_sig_Z3_model_to_string)(Z3_context, Z3_model);
ay_sig_Z3_model_to_string const ay_link_Z3_model_to_string = &Z3_model_to_string;
Z3_string ay_call_Z3_model_to_string(Z3_context ay_a0, Z3_model ay_a1) {
    return Z3_model_to_string(ay_a0, ay_a1);
}

typedef Z3_model (*ay_sig_Z3_model_translate)(Z3_context, Z3_model, Z3_context);
ay_sig_Z3_model_translate const ay_link_Z3_model_translate = &Z3_model_translate;
Z3_model ay_call_Z3_model_translate(Z3_context ay_a0, Z3_model ay_a1, Z3_context ay_a2) {
    return Z3_model_translate(ay_a0, ay_a1, ay_a2);
}

typedef bool (*ay_sig_Z3_open_log)(Z3_string);
ay_sig_Z3_open_log const ay_link_Z3_open_log = &Z3_open_log;
bool ay_call_Z3_open_log(Z3_string ay_a0) {
    return Z3_open_log(ay_a0);
}

typedef void (*ay_sig_Z3_optimize_assert_and_track)(Z3_context, Z3_optimize, Z3_ast, Z3_ast);
ay_sig_Z3_optimize_assert_and_track const ay_link_Z3_optimize_assert_and_track = &Z3_optimize_assert_and_track;
void ay_call_Z3_optimize_assert_and_track(Z3_context ay_a0, Z3_optimize ay_a1, Z3_ast ay_a2, Z3_ast ay_a3) {
    Z3_optimize_assert_and_track(ay_a0, ay_a1, ay_a2, ay_a3);
}

typedef unsigned int (*ay_sig_Z3_optimize_assert_soft)(Z3_context, Z3_optimize, Z3_ast, Z3_string, Z3_symbol);
ay_sig_Z3_optimize_assert_soft const ay_link_Z3_optimize_assert_soft = &Z3_optimize_assert_soft;
unsigned int ay_call_Z3_optimize_assert_soft(Z3_context ay_a0, Z3_optimize ay_a1, Z3_ast ay_a2, Z3_string ay_a3, Z3_symbol ay_a4) {
    return Z3_optimize_assert_soft(ay_a0, ay_a1, ay_a2, ay_a3, ay_a4);
}

typedef void (*ay_sig_Z3_optimize_assert)(Z3_context, Z3_optimize, Z3_ast);
ay_sig_Z3_optimize_assert const ay_link_Z3_optimize_assert = &Z3_optimize_assert;
void ay_call_Z3_optimize_assert(Z3_context ay_a0, Z3_optimize ay_a1, Z3_ast ay_a2) {
    Z3_optimize_assert(ay_a0, ay_a1, ay_a2);
}

typedef Z3_lbool (*ay_sig_Z3_optimize_check)(Z3_context, Z3_optimize, unsigned int, const Z3_ast *);
ay_sig_Z3_optimize_check const ay_link_Z3_optimize_check = &Z3_optimize_check;
Z3_lbool ay_call_Z3_optimize_check(Z3_context ay_a0, Z3_optimize ay_a1, unsigned int ay_a2, const Z3_ast * ay_a3) {
    return Z3_optimize_check(ay_a0, ay_a1, ay_a2, ay_a3);
}

typedef void (*ay_sig_Z3_optimize_dec_ref)(Z3_context, Z3_optimize);
ay_sig_Z3_optimize_dec_ref const ay_link_Z3_optimize_dec_ref = &Z3_optimize_dec_ref;
void ay_call_Z3_optimize_dec_ref(Z3_context ay_a0, Z3_optimize ay_a1) {
    Z3_optimize_dec_ref(ay_a0, ay_a1);
}

typedef void (*ay_sig_Z3_optimize_from_file)(Z3_context, Z3_optimize, Z3_string);
ay_sig_Z3_optimize_from_file const ay_link_Z3_optimize_from_file = &Z3_optimize_from_file;
void ay_call_Z3_optimize_from_file(Z3_context ay_a0, Z3_optimize ay_a1, Z3_string ay_a2) {
    Z3_optimize_from_file(ay_a0, ay_a1, ay_a2);
}

typedef void (*ay_sig_Z3_optimize_from_string)(Z3_context, Z3_optimize, Z3_string);
ay_sig_Z3_optimize_from_string const ay_link_Z3_optimize_from_string = &Z3_optimize_from_string;
void ay_call_Z3_optimize_from_string(Z3_context ay_a0, Z3_optimize ay_a1, Z3_string ay_a2) {
    Z3_optimize_from_string(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast_vector (*ay_sig_Z3_optimize_get_assertions)(Z3_context, Z3_optimize);
ay_sig_Z3_optimize_get_assertions const ay_link_Z3_optimize_get_assertions = &Z3_optimize_get_assertions;
Z3_ast_vector ay_call_Z3_optimize_get_assertions(Z3_context ay_a0, Z3_optimize ay_a1) {
    return Z3_optimize_get_assertions(ay_a0, ay_a1);
}

typedef Z3_string (*ay_sig_Z3_optimize_get_help)(Z3_context, Z3_optimize);
ay_sig_Z3_optimize_get_help const ay_link_Z3_optimize_get_help = &Z3_optimize_get_help;
Z3_string ay_call_Z3_optimize_get_help(Z3_context ay_a0, Z3_optimize ay_a1) {
    return Z3_optimize_get_help(ay_a0, ay_a1);
}

typedef Z3_ast_vector (*ay_sig_Z3_optimize_get_lower_as_vector)(Z3_context, Z3_optimize, unsigned int);
ay_sig_Z3_optimize_get_lower_as_vector const ay_link_Z3_optimize_get_lower_as_vector = &Z3_optimize_get_lower_as_vector;
Z3_ast_vector ay_call_Z3_optimize_get_lower_as_vector(Z3_context ay_a0, Z3_optimize ay_a1, unsigned int ay_a2) {
    return Z3_optimize_get_lower_as_vector(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_optimize_get_lower)(Z3_context, Z3_optimize, unsigned int);
ay_sig_Z3_optimize_get_lower const ay_link_Z3_optimize_get_lower = &Z3_optimize_get_lower;
Z3_ast ay_call_Z3_optimize_get_lower(Z3_context ay_a0, Z3_optimize ay_a1, unsigned int ay_a2) {
    return Z3_optimize_get_lower(ay_a0, ay_a1, ay_a2);
}

typedef Z3_model (*ay_sig_Z3_optimize_get_model)(Z3_context, Z3_optimize);
ay_sig_Z3_optimize_get_model const ay_link_Z3_optimize_get_model = &Z3_optimize_get_model;
Z3_model ay_call_Z3_optimize_get_model(Z3_context ay_a0, Z3_optimize ay_a1) {
    return Z3_optimize_get_model(ay_a0, ay_a1);
}

typedef Z3_ast_vector (*ay_sig_Z3_optimize_get_objectives)(Z3_context, Z3_optimize);
ay_sig_Z3_optimize_get_objectives const ay_link_Z3_optimize_get_objectives = &Z3_optimize_get_objectives;
Z3_ast_vector ay_call_Z3_optimize_get_objectives(Z3_context ay_a0, Z3_optimize ay_a1) {
    return Z3_optimize_get_objectives(ay_a0, ay_a1);
}

typedef Z3_param_descrs (*ay_sig_Z3_optimize_get_param_descrs)(Z3_context, Z3_optimize);
ay_sig_Z3_optimize_get_param_descrs const ay_link_Z3_optimize_get_param_descrs = &Z3_optimize_get_param_descrs;
Z3_param_descrs ay_call_Z3_optimize_get_param_descrs(Z3_context ay_a0, Z3_optimize ay_a1) {
    return Z3_optimize_get_param_descrs(ay_a0, ay_a1);
}

typedef Z3_string (*ay_sig_Z3_optimize_get_reason_unknown)(Z3_context, Z3_optimize);
ay_sig_Z3_optimize_get_reason_unknown const ay_link_Z3_optimize_get_reason_unknown = &Z3_optimize_get_reason_unknown;
Z3_string ay_call_Z3_optimize_get_reason_unknown(Z3_context ay_a0, Z3_optimize ay_a1) {
    return Z3_optimize_get_reason_unknown(ay_a0, ay_a1);
}

typedef Z3_stats (*ay_sig_Z3_optimize_get_statistics)(Z3_context, Z3_optimize);
ay_sig_Z3_optimize_get_statistics const ay_link_Z3_optimize_get_statistics = &Z3_optimize_get_statistics;
Z3_stats ay_call_Z3_optimize_get_statistics(Z3_context ay_a0, Z3_optimize ay_a1) {
    return Z3_optimize_get_statistics(ay_a0, ay_a1);
}

typedef Z3_ast_vector (*ay_sig_Z3_optimize_get_unsat_core)(Z3_context, Z3_optimize);
ay_sig_Z3_optimize_get_unsat_core const ay_link_Z3_optimize_get_unsat_core = &Z3_optimize_get_unsat_core;
Z3_ast_vector ay_call_Z3_optimize_get_unsat_core(Z3_context ay_a0, Z3_optimize ay_a1) {
    return Z3_optimize_get_unsat_core(ay_a0, ay_a1);
}

typedef Z3_ast_vector (*ay_sig_Z3_optimize_get_upper_as_vector)(Z3_context, Z3_optimize, unsigned int);
ay_sig_Z3_optimize_get_upper_as_vector const ay_link_Z3_optimize_get_upper_as_vector = &Z3_optimize_get_upper_as_vector;
Z3_ast_vector ay_call_Z3_optimize_get_upper_as_vector(Z3_context ay_a0, Z3_optimize ay_a1, unsigned int ay_a2) {
    return Z3_optimize_get_upper_as_vector(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_optimize_get_upper)(Z3_context, Z3_optimize, unsigned int);
ay_sig_Z3_optimize_get_upper const ay_link_Z3_optimize_get_upper = &Z3_optimize_get_upper;
Z3_ast ay_call_Z3_optimize_get_upper(Z3_context ay_a0, Z3_optimize ay_a1, unsigned int ay_a2) {
    return Z3_optimize_get_upper(ay_a0, ay_a1, ay_a2);
}

typedef void (*ay_sig_Z3_optimize_inc_ref)(Z3_context, Z3_optimize);
ay_sig_Z3_optimize_inc_ref const ay_link_Z3_optimize_inc_ref = &Z3_optimize_inc_ref;
void ay_call_Z3_optimize_inc_ref(Z3_context ay_a0, Z3_optimize ay_a1) {
    Z3_optimize_inc_ref(ay_a0, ay_a1);
}

typedef unsigned int (*ay_sig_Z3_optimize_maximize)(Z3_context, Z3_optimize, Z3_ast);
ay_sig_Z3_optimize_maximize const ay_link_Z3_optimize_maximize = &Z3_optimize_maximize;
unsigned int ay_call_Z3_optimize_maximize(Z3_context ay_a0, Z3_optimize ay_a1, Z3_ast ay_a2) {
    return Z3_optimize_maximize(ay_a0, ay_a1, ay_a2);
}

typedef unsigned int (*ay_sig_Z3_optimize_minimize)(Z3_context, Z3_optimize, Z3_ast);
ay_sig_Z3_optimize_minimize const ay_link_Z3_optimize_minimize = &Z3_optimize_minimize;
unsigned int ay_call_Z3_optimize_minimize(Z3_context ay_a0, Z3_optimize ay_a1, Z3_ast ay_a2) {
    return Z3_optimize_minimize(ay_a0, ay_a1, ay_a2);
}

typedef void (*ay_sig_Z3_optimize_pop)(Z3_context, Z3_optimize);
ay_sig_Z3_optimize_pop const ay_link_Z3_optimize_pop = &Z3_optimize_pop;
void ay_call_Z3_optimize_pop(Z3_context ay_a0, Z3_optimize ay_a1) {
    Z3_optimize_pop(ay_a0, ay_a1);
}

typedef void (*ay_sig_Z3_optimize_push)(Z3_context, Z3_optimize);
ay_sig_Z3_optimize_push const ay_link_Z3_optimize_push = &Z3_optimize_push;
void ay_call_Z3_optimize_push(Z3_context ay_a0, Z3_optimize ay_a1) {
    Z3_optimize_push(ay_a0, ay_a1);
}

typedef void (*ay_sig_Z3_optimize_register_model_eh)(Z3_context, Z3_optimize, Z3_model, void *, Z3_model_eh *);
ay_sig_Z3_optimize_register_model_eh const ay_link_Z3_optimize_register_model_eh = &Z3_optimize_register_model_eh;
void ay_call_Z3_optimize_register_model_eh(Z3_context ay_a0, Z3_optimize ay_a1, Z3_model ay_a2, void * ay_a3, Z3_model_eh * ay_a4) {
    Z3_optimize_register_model_eh(ay_a0, ay_a1, ay_a2, ay_a3, ay_a4);
}

typedef void (*ay_sig_Z3_optimize_set_initial_value)(Z3_context, Z3_optimize, Z3_ast, Z3_ast);
ay_sig_Z3_optimize_set_initial_value const ay_link_Z3_optimize_set_initial_value = &Z3_optimize_set_initial_value;
void ay_call_Z3_optimize_set_initial_value(Z3_context ay_a0, Z3_optimize ay_a1, Z3_ast ay_a2, Z3_ast ay_a3) {
    Z3_optimize_set_initial_value(ay_a0, ay_a1, ay_a2, ay_a3);
}

typedef void (*ay_sig_Z3_optimize_set_params)(Z3_context, Z3_optimize, Z3_params);
ay_sig_Z3_optimize_set_params const ay_link_Z3_optimize_set_params = &Z3_optimize_set_params;
void ay_call_Z3_optimize_set_params(Z3_context ay_a0, Z3_optimize ay_a1, Z3_params ay_a2) {
    Z3_optimize_set_params(ay_a0, ay_a1, ay_a2);
}

typedef Z3_string (*ay_sig_Z3_optimize_to_string)(Z3_context, Z3_optimize);
ay_sig_Z3_optimize_to_string const ay_link_Z3_optimize_to_string = &Z3_optimize_to_string;
Z3_string ay_call_Z3_optimize_to_string(Z3_context ay_a0, Z3_optimize ay_a1) {
    return Z3_optimize_to_string(ay_a0, ay_a1);
}

typedef Z3_optimize (*ay_sig_Z3_optimize_translate)(Z3_context, Z3_optimize, Z3_context);
ay_sig_Z3_optimize_translate const ay_link_Z3_optimize_translate = &Z3_optimize_translate;
Z3_optimize ay_call_Z3_optimize_translate(Z3_context ay_a0, Z3_optimize ay_a1, Z3_context ay_a2) {
    return Z3_optimize_translate(ay_a0, ay_a1, ay_a2);
}

typedef void (*ay_sig_Z3_param_descrs_dec_ref)(Z3_context, Z3_param_descrs);
ay_sig_Z3_param_descrs_dec_ref const ay_link_Z3_param_descrs_dec_ref = &Z3_param_descrs_dec_ref;
void ay_call_Z3_param_descrs_dec_ref(Z3_context ay_a0, Z3_param_descrs ay_a1) {
    Z3_param_descrs_dec_ref(ay_a0, ay_a1);
}

typedef Z3_string (*ay_sig_Z3_param_descrs_get_documentation)(Z3_context, Z3_param_descrs, Z3_symbol);
ay_sig_Z3_param_descrs_get_documentation const ay_link_Z3_param_descrs_get_documentation = &Z3_param_descrs_get_documentation;
Z3_string ay_call_Z3_param_descrs_get_documentation(Z3_context ay_a0, Z3_param_descrs ay_a1, Z3_symbol ay_a2) {
    return Z3_param_descrs_get_documentation(ay_a0, ay_a1, ay_a2);
}

typedef Z3_param_kind (*ay_sig_Z3_param_descrs_get_kind)(Z3_context, Z3_param_descrs, Z3_symbol);
ay_sig_Z3_param_descrs_get_kind const ay_link_Z3_param_descrs_get_kind = &Z3_param_descrs_get_kind;
Z3_param_kind ay_call_Z3_param_descrs_get_kind(Z3_context ay_a0, Z3_param_descrs ay_a1, Z3_symbol ay_a2) {
    return Z3_param_descrs_get_kind(ay_a0, ay_a1, ay_a2);
}

typedef Z3_symbol (*ay_sig_Z3_param_descrs_get_name)(Z3_context, Z3_param_descrs, unsigned int);
ay_sig_Z3_param_descrs_get_name const ay_link_Z3_param_descrs_get_name = &Z3_param_descrs_get_name;
Z3_symbol ay_call_Z3_param_descrs_get_name(Z3_context ay_a0, Z3_param_descrs ay_a1, unsigned int ay_a2) {
    return Z3_param_descrs_get_name(ay_a0, ay_a1, ay_a2);
}

typedef void (*ay_sig_Z3_param_descrs_inc_ref)(Z3_context, Z3_param_descrs);
ay_sig_Z3_param_descrs_inc_ref const ay_link_Z3_param_descrs_inc_ref = &Z3_param_descrs_inc_ref;
void ay_call_Z3_param_descrs_inc_ref(Z3_context ay_a0, Z3_param_descrs ay_a1) {
    Z3_param_descrs_inc_ref(ay_a0, ay_a1);
}

typedef unsigned int (*ay_sig_Z3_param_descrs_size)(Z3_context, Z3_param_descrs);
ay_sig_Z3_param_descrs_size const ay_link_Z3_param_descrs_size = &Z3_param_descrs_size;
unsigned int ay_call_Z3_param_descrs_size(Z3_context ay_a0, Z3_param_descrs ay_a1) {
    return Z3_param_descrs_size(ay_a0, ay_a1);
}

typedef Z3_string (*ay_sig_Z3_param_descrs_to_string)(Z3_context, Z3_param_descrs);
ay_sig_Z3_param_descrs_to_string const ay_link_Z3_param_descrs_to_string = &Z3_param_descrs_to_string;
Z3_string ay_call_Z3_param_descrs_to_string(Z3_context ay_a0, Z3_param_descrs ay_a1) {
    return Z3_param_descrs_to_string(ay_a0, ay_a1);
}

typedef void (*ay_sig_Z3_params_dec_ref)(Z3_context, Z3_params);
ay_sig_Z3_params_dec_ref const ay_link_Z3_params_dec_ref = &Z3_params_dec_ref;
void ay_call_Z3_params_dec_ref(Z3_context ay_a0, Z3_params ay_a1) {
    Z3_params_dec_ref(ay_a0, ay_a1);
}

typedef void (*ay_sig_Z3_params_inc_ref)(Z3_context, Z3_params);
ay_sig_Z3_params_inc_ref const ay_link_Z3_params_inc_ref = &Z3_params_inc_ref;
void ay_call_Z3_params_inc_ref(Z3_context ay_a0, Z3_params ay_a1) {
    Z3_params_inc_ref(ay_a0, ay_a1);
}

typedef void (*ay_sig_Z3_params_set_bool)(Z3_context, Z3_params, Z3_symbol, bool);
ay_sig_Z3_params_set_bool const ay_link_Z3_params_set_bool = &Z3_params_set_bool;
void ay_call_Z3_params_set_bool(Z3_context ay_a0, Z3_params ay_a1, Z3_symbol ay_a2, bool ay_a3) {
    Z3_params_set_bool(ay_a0, ay_a1, ay_a2, ay_a3);
}

typedef void (*ay_sig_Z3_params_set_double)(Z3_context, Z3_params, Z3_symbol, double);
ay_sig_Z3_params_set_double const ay_link_Z3_params_set_double = &Z3_params_set_double;
void ay_call_Z3_params_set_double(Z3_context ay_a0, Z3_params ay_a1, Z3_symbol ay_a2, double ay_a3) {
    Z3_params_set_double(ay_a0, ay_a1, ay_a2, ay_a3);
}

typedef void (*ay_sig_Z3_params_set_symbol)(Z3_context, Z3_params, Z3_symbol, Z3_symbol);
ay_sig_Z3_params_set_symbol const ay_link_Z3_params_set_symbol = &Z3_params_set_symbol;
void ay_call_Z3_params_set_symbol(Z3_context ay_a0, Z3_params ay_a1, Z3_symbol ay_a2, Z3_symbol ay_a3) {
    Z3_params_set_symbol(ay_a0, ay_a1, ay_a2, ay_a3);
}

typedef void (*ay_sig_Z3_params_set_uint)(Z3_context, Z3_params, Z3_symbol, unsigned int);
ay_sig_Z3_params_set_uint const ay_link_Z3_params_set_uint = &Z3_params_set_uint;
void ay_call_Z3_params_set_uint(Z3_context ay_a0, Z3_params ay_a1, Z3_symbol ay_a2, unsigned int ay_a3) {
    Z3_params_set_uint(ay_a0, ay_a1, ay_a2, ay_a3);
}

typedef Z3_string (*ay_sig_Z3_params_to_string)(Z3_context, Z3_params);
ay_sig_Z3_params_to_string const ay_link_Z3_params_to_string = &Z3_params_to_string;
Z3_string ay_call_Z3_params_to_string(Z3_context ay_a0, Z3_params ay_a1) {
    return Z3_params_to_string(ay_a0, ay_a1);
}

typedef void (*ay_sig_Z3_params_validate)(Z3_context, Z3_params, Z3_param_descrs);
ay_sig_Z3_params_validate const ay_link_Z3_params_validate = &Z3_params_validate;
void ay_call_Z3_params_validate(Z3_context ay_a0, Z3_params ay_a1, Z3_param_descrs ay_a2) {
    Z3_params_validate(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast_vector (*ay_sig_Z3_parse_smtlib2_file)(Z3_context, Z3_string, unsigned int, const Z3_symbol *, const Z3_sort *, unsigned int, const Z3_symbol *, const Z3_func_decl *);
ay_sig_Z3_parse_smtlib2_file const ay_link_Z3_parse_smtlib2_file = &Z3_parse_smtlib2_file;
Z3_ast_vector ay_call_Z3_parse_smtlib2_file(Z3_context ay_a0, Z3_string ay_a1, unsigned int ay_a2, const Z3_symbol * ay_a3, const Z3_sort * ay_a4, unsigned int ay_a5, const Z3_symbol * ay_a6, const Z3_func_decl * ay_a7) {
    return Z3_parse_smtlib2_file(ay_a0, ay_a1, ay_a2, ay_a3, ay_a4, ay_a5, ay_a6, ay_a7);
}

typedef Z3_ast_vector (*ay_sig_Z3_parse_smtlib2_string)(Z3_context, Z3_string, unsigned int, const Z3_symbol *, const Z3_sort *, unsigned int, const Z3_symbol *, const Z3_func_decl *);
ay_sig_Z3_parse_smtlib2_string const ay_link_Z3_parse_smtlib2_string = &Z3_parse_smtlib2_string;
Z3_ast_vector ay_call_Z3_parse_smtlib2_string(Z3_context ay_a0, Z3_string ay_a1, unsigned int ay_a2, const Z3_symbol * ay_a3, const Z3_sort * ay_a4, unsigned int ay_a5, const Z3_symbol * ay_a6, const Z3_func_decl * ay_a7) {
    return Z3_parse_smtlib2_string(ay_a0, ay_a1, ay_a2, ay_a3, ay_a4, ay_a5, ay_a6, ay_a7);
}

typedef void (*ay_sig_Z3_parser_context_add_decl)(Z3_context, Z3_parser_context, Z3_func_decl);
ay_sig_Z3_parser_context_add_decl const ay_link_Z3_parser_context_add_decl = &Z3_parser_context_add_decl;
void ay_call_Z3_parser_context_add_decl(Z3_context ay_a0, Z3_parser_context ay_a1, Z3_func_decl ay_a2) {
    Z3_parser_context_add_decl(ay_a0, ay_a1, ay_a2);
}

typedef void (*ay_sig_Z3_parser_context_add_sort)(Z3_context, Z3_parser_context, Z3_sort);
ay_sig_Z3_parser_context_add_sort const ay_link_Z3_parser_context_add_sort = &Z3_parser_context_add_sort;
void ay_call_Z3_parser_context_add_sort(Z3_context ay_a0, Z3_parser_context ay_a1, Z3_sort ay_a2) {
    Z3_parser_context_add_sort(ay_a0, ay_a1, ay_a2);
}

typedef void (*ay_sig_Z3_parser_context_dec_ref)(Z3_context, Z3_parser_context);
ay_sig_Z3_parser_context_dec_ref const ay_link_Z3_parser_context_dec_ref = &Z3_parser_context_dec_ref;
void ay_call_Z3_parser_context_dec_ref(Z3_context ay_a0, Z3_parser_context ay_a1) {
    Z3_parser_context_dec_ref(ay_a0, ay_a1);
}

typedef Z3_ast_vector (*ay_sig_Z3_parser_context_from_string)(Z3_context, Z3_parser_context, Z3_string);
ay_sig_Z3_parser_context_from_string const ay_link_Z3_parser_context_from_string = &Z3_parser_context_from_string;
Z3_ast_vector ay_call_Z3_parser_context_from_string(Z3_context ay_a0, Z3_parser_context ay_a1, Z3_string ay_a2) {
    return Z3_parser_context_from_string(ay_a0, ay_a1, ay_a2);
}

typedef void (*ay_sig_Z3_parser_context_inc_ref)(Z3_context, Z3_parser_context);
ay_sig_Z3_parser_context_inc_ref const ay_link_Z3_parser_context_inc_ref = &Z3_parser_context_inc_ref;
void ay_call_Z3_parser_context_inc_ref(Z3_context ay_a0, Z3_parser_context ay_a1) {
    Z3_parser_context_inc_ref(ay_a0, ay_a1);
}

typedef Z3_ast (*ay_sig_Z3_pattern_to_ast)(Z3_context, Z3_pattern);
ay_sig_Z3_pattern_to_ast const ay_link_Z3_pattern_to_ast = &Z3_pattern_to_ast;
Z3_ast ay_call_Z3_pattern_to_ast(Z3_context ay_a0, Z3_pattern ay_a1) {
    return Z3_pattern_to_ast(ay_a0, ay_a1);
}

typedef Z3_string (*ay_sig_Z3_pattern_to_string)(Z3_context, Z3_pattern);
ay_sig_Z3_pattern_to_string const ay_link_Z3_pattern_to_string = &Z3_pattern_to_string;
Z3_string ay_call_Z3_pattern_to_string(Z3_context ay_a0, Z3_pattern ay_a1) {
    return Z3_pattern_to_string(ay_a0, ay_a1);
}

typedef Z3_ast_vector (*ay_sig_Z3_polynomial_subresultants)(Z3_context, Z3_ast, Z3_ast, Z3_ast);
ay_sig_Z3_polynomial_subresultants const ay_link_Z3_polynomial_subresultants = &Z3_polynomial_subresultants;
Z3_ast_vector ay_call_Z3_polynomial_subresultants(Z3_context ay_a0, Z3_ast ay_a1, Z3_ast ay_a2, Z3_ast ay_a3) {
    return Z3_polynomial_subresultants(ay_a0, ay_a1, ay_a2, ay_a3);
}

typedef Z3_probe (*ay_sig_Z3_probe_and)(Z3_context, Z3_probe, Z3_probe);
ay_sig_Z3_probe_and const ay_link_Z3_probe_and = &Z3_probe_and;
Z3_probe ay_call_Z3_probe_and(Z3_context ay_a0, Z3_probe ay_a1, Z3_probe ay_a2) {
    return Z3_probe_and(ay_a0, ay_a1, ay_a2);
}

typedef double (*ay_sig_Z3_probe_apply)(Z3_context, Z3_probe, Z3_goal);
ay_sig_Z3_probe_apply const ay_link_Z3_probe_apply = &Z3_probe_apply;
double ay_call_Z3_probe_apply(Z3_context ay_a0, Z3_probe ay_a1, Z3_goal ay_a2) {
    return Z3_probe_apply(ay_a0, ay_a1, ay_a2);
}

typedef Z3_probe (*ay_sig_Z3_probe_const)(Z3_context, double);
ay_sig_Z3_probe_const const ay_link_Z3_probe_const = &Z3_probe_const;
Z3_probe ay_call_Z3_probe_const(Z3_context ay_a0, double ay_a1) {
    return Z3_probe_const(ay_a0, ay_a1);
}

typedef void (*ay_sig_Z3_probe_dec_ref)(Z3_context, Z3_probe);
ay_sig_Z3_probe_dec_ref const ay_link_Z3_probe_dec_ref = &Z3_probe_dec_ref;
void ay_call_Z3_probe_dec_ref(Z3_context ay_a0, Z3_probe ay_a1) {
    Z3_probe_dec_ref(ay_a0, ay_a1);
}

typedef Z3_probe (*ay_sig_Z3_probe_eq)(Z3_context, Z3_probe, Z3_probe);
ay_sig_Z3_probe_eq const ay_link_Z3_probe_eq = &Z3_probe_eq;
Z3_probe ay_call_Z3_probe_eq(Z3_context ay_a0, Z3_probe ay_a1, Z3_probe ay_a2) {
    return Z3_probe_eq(ay_a0, ay_a1, ay_a2);
}

typedef Z3_string (*ay_sig_Z3_probe_get_descr)(Z3_context, Z3_string);
ay_sig_Z3_probe_get_descr const ay_link_Z3_probe_get_descr = &Z3_probe_get_descr;
Z3_string ay_call_Z3_probe_get_descr(Z3_context ay_a0, Z3_string ay_a1) {
    return Z3_probe_get_descr(ay_a0, ay_a1);
}

typedef Z3_probe (*ay_sig_Z3_probe_ge)(Z3_context, Z3_probe, Z3_probe);
ay_sig_Z3_probe_ge const ay_link_Z3_probe_ge = &Z3_probe_ge;
Z3_probe ay_call_Z3_probe_ge(Z3_context ay_a0, Z3_probe ay_a1, Z3_probe ay_a2) {
    return Z3_probe_ge(ay_a0, ay_a1, ay_a2);
}

typedef Z3_probe (*ay_sig_Z3_probe_gt)(Z3_context, Z3_probe, Z3_probe);
ay_sig_Z3_probe_gt const ay_link_Z3_probe_gt = &Z3_probe_gt;
Z3_probe ay_call_Z3_probe_gt(Z3_context ay_a0, Z3_probe ay_a1, Z3_probe ay_a2) {
    return Z3_probe_gt(ay_a0, ay_a1, ay_a2);
}

typedef void (*ay_sig_Z3_probe_inc_ref)(Z3_context, Z3_probe);
ay_sig_Z3_probe_inc_ref const ay_link_Z3_probe_inc_ref = &Z3_probe_inc_ref;
void ay_call_Z3_probe_inc_ref(Z3_context ay_a0, Z3_probe ay_a1) {
    Z3_probe_inc_ref(ay_a0, ay_a1);
}

typedef Z3_probe (*ay_sig_Z3_probe_le)(Z3_context, Z3_probe, Z3_probe);
ay_sig_Z3_probe_le const ay_link_Z3_probe_le = &Z3_probe_le;
Z3_probe ay_call_Z3_probe_le(Z3_context ay_a0, Z3_probe ay_a1, Z3_probe ay_a2) {
    return Z3_probe_le(ay_a0, ay_a1, ay_a2);
}

typedef Z3_probe (*ay_sig_Z3_probe_lt)(Z3_context, Z3_probe, Z3_probe);
ay_sig_Z3_probe_lt const ay_link_Z3_probe_lt = &Z3_probe_lt;
Z3_probe ay_call_Z3_probe_lt(Z3_context ay_a0, Z3_probe ay_a1, Z3_probe ay_a2) {
    return Z3_probe_lt(ay_a0, ay_a1, ay_a2);
}

typedef Z3_probe (*ay_sig_Z3_probe_not)(Z3_context, Z3_probe);
ay_sig_Z3_probe_not const ay_link_Z3_probe_not = &Z3_probe_not;
Z3_probe ay_call_Z3_probe_not(Z3_context ay_a0, Z3_probe ay_a1) {
    return Z3_probe_not(ay_a0, ay_a1);
}

typedef Z3_probe (*ay_sig_Z3_probe_or)(Z3_context, Z3_probe, Z3_probe);
ay_sig_Z3_probe_or const ay_link_Z3_probe_or = &Z3_probe_or;
Z3_probe ay_call_Z3_probe_or(Z3_context ay_a0, Z3_probe ay_a1, Z3_probe ay_a2) {
    return Z3_probe_or(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_qe_lite)(Z3_context, Z3_ast_vector, Z3_ast);
ay_sig_Z3_qe_lite const ay_link_Z3_qe_lite = &Z3_qe_lite;
Z3_ast ay_call_Z3_qe_lite(Z3_context ay_a0, Z3_ast_vector ay_a1, Z3_ast ay_a2) {
    return Z3_qe_lite(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_qe_model_project_skolem)(Z3_context, Z3_model, unsigned int, const Z3_app *, Z3_ast, Z3_ast_map);
ay_sig_Z3_qe_model_project_skolem const ay_link_Z3_qe_model_project_skolem = &Z3_qe_model_project_skolem;
Z3_ast ay_call_Z3_qe_model_project_skolem(Z3_context ay_a0, Z3_model ay_a1, unsigned int ay_a2, const Z3_app * ay_a3, Z3_ast ay_a4, Z3_ast_map ay_a5) {
    return Z3_qe_model_project_skolem(ay_a0, ay_a1, ay_a2, ay_a3, ay_a4, ay_a5);
}

typedef Z3_ast (*ay_sig_Z3_qe_model_project_with_witness)(Z3_context, Z3_model, unsigned int, const Z3_app *, Z3_ast, Z3_ast_map);
ay_sig_Z3_qe_model_project_with_witness const ay_link_Z3_qe_model_project_with_witness = &Z3_qe_model_project_with_witness;
Z3_ast ay_call_Z3_qe_model_project_with_witness(Z3_context ay_a0, Z3_model ay_a1, unsigned int ay_a2, const Z3_app * ay_a3, Z3_ast ay_a4, Z3_ast_map ay_a5) {
    return Z3_qe_model_project_with_witness(ay_a0, ay_a1, ay_a2, ay_a3, ay_a4, ay_a5);
}

typedef Z3_ast (*ay_sig_Z3_qe_model_project)(Z3_context, Z3_model, unsigned int, const Z3_app *, Z3_ast);
ay_sig_Z3_qe_model_project const ay_link_Z3_qe_model_project = &Z3_qe_model_project;
Z3_ast ay_call_Z3_qe_model_project(Z3_context ay_a0, Z3_model ay_a1, unsigned int ay_a2, const Z3_app * ay_a3, Z3_ast ay_a4) {
    return Z3_qe_model_project(ay_a0, ay_a1, ay_a2, ay_a3, ay_a4);
}

typedef void (*ay_sig_Z3_query_constructor)(Z3_context, Z3_constructor, unsigned int, Z3_func_decl *, Z3_func_decl *, Z3_func_decl *);
ay_sig_Z3_query_constructor const ay_link_Z3_query_constructor = &Z3_query_constructor;
void ay_call_Z3_query_constructor(Z3_context ay_a0, Z3_constructor ay_a1, unsigned int ay_a2, Z3_func_decl * ay_a3, Z3_func_decl * ay_a4, Z3_func_decl * ay_a5) {
    Z3_query_constructor(ay_a0, ay_a1, ay_a2, ay_a3, ay_a4, ay_a5);
}

typedef Z3_rcf_num (*ay_sig_Z3_rcf_add)(Z3_context, Z3_rcf_num, Z3_rcf_num);
ay_sig_Z3_rcf_add const ay_link_Z3_rcf_add = &Z3_rcf_add;
Z3_rcf_num ay_call_Z3_rcf_add(Z3_context ay_a0, Z3_rcf_num ay_a1, Z3_rcf_num ay_a2) {
    return Z3_rcf_add(ay_a0, ay_a1, ay_a2);
}

typedef Z3_rcf_num (*ay_sig_Z3_rcf_coefficient)(Z3_context, Z3_rcf_num, unsigned int);
ay_sig_Z3_rcf_coefficient const ay_link_Z3_rcf_coefficient = &Z3_rcf_coefficient;
Z3_rcf_num ay_call_Z3_rcf_coefficient(Z3_context ay_a0, Z3_rcf_num ay_a1, unsigned int ay_a2) {
    return Z3_rcf_coefficient(ay_a0, ay_a1, ay_a2);
}

typedef void (*ay_sig_Z3_rcf_del)(Z3_context, Z3_rcf_num);
ay_sig_Z3_rcf_del const ay_link_Z3_rcf_del = &Z3_rcf_del;
void ay_call_Z3_rcf_del(Z3_context ay_a0, Z3_rcf_num ay_a1) {
    Z3_rcf_del(ay_a0, ay_a1);
}

typedef Z3_rcf_num (*ay_sig_Z3_rcf_div)(Z3_context, Z3_rcf_num, Z3_rcf_num);
ay_sig_Z3_rcf_div const ay_link_Z3_rcf_div = &Z3_rcf_div;
Z3_rcf_num ay_call_Z3_rcf_div(Z3_context ay_a0, Z3_rcf_num ay_a1, Z3_rcf_num ay_a2) {
    return Z3_rcf_div(ay_a0, ay_a1, ay_a2);
}

typedef bool (*ay_sig_Z3_rcf_eq)(Z3_context, Z3_rcf_num, Z3_rcf_num);
ay_sig_Z3_rcf_eq const ay_link_Z3_rcf_eq = &Z3_rcf_eq;
bool ay_call_Z3_rcf_eq(Z3_context ay_a0, Z3_rcf_num ay_a1, Z3_rcf_num ay_a2) {
    return Z3_rcf_eq(ay_a0, ay_a1, ay_a2);
}

typedef unsigned int (*ay_sig_Z3_rcf_extension_index)(Z3_context, Z3_rcf_num);
ay_sig_Z3_rcf_extension_index const ay_link_Z3_rcf_extension_index = &Z3_rcf_extension_index;
unsigned int ay_call_Z3_rcf_extension_index(Z3_context ay_a0, Z3_rcf_num ay_a1) {
    return Z3_rcf_extension_index(ay_a0, ay_a1);
}

typedef void (*ay_sig_Z3_rcf_get_numerator_denominator)(Z3_context, Z3_rcf_num, Z3_rcf_num *, Z3_rcf_num *);
ay_sig_Z3_rcf_get_numerator_denominator const ay_link_Z3_rcf_get_numerator_denominator = &Z3_rcf_get_numerator_denominator;
void ay_call_Z3_rcf_get_numerator_denominator(Z3_context ay_a0, Z3_rcf_num ay_a1, Z3_rcf_num * ay_a2, Z3_rcf_num * ay_a3) {
    Z3_rcf_get_numerator_denominator(ay_a0, ay_a1, ay_a2, ay_a3);
}

typedef bool (*ay_sig_Z3_rcf_ge)(Z3_context, Z3_rcf_num, Z3_rcf_num);
ay_sig_Z3_rcf_ge const ay_link_Z3_rcf_ge = &Z3_rcf_ge;
bool ay_call_Z3_rcf_ge(Z3_context ay_a0, Z3_rcf_num ay_a1, Z3_rcf_num ay_a2) {
    return Z3_rcf_ge(ay_a0, ay_a1, ay_a2);
}

typedef bool (*ay_sig_Z3_rcf_gt)(Z3_context, Z3_rcf_num, Z3_rcf_num);
ay_sig_Z3_rcf_gt const ay_link_Z3_rcf_gt = &Z3_rcf_gt;
bool ay_call_Z3_rcf_gt(Z3_context ay_a0, Z3_rcf_num ay_a1, Z3_rcf_num ay_a2) {
    return Z3_rcf_gt(ay_a0, ay_a1, ay_a2);
}

typedef Z3_symbol (*ay_sig_Z3_rcf_infinitesimal_name)(Z3_context, Z3_rcf_num);
ay_sig_Z3_rcf_infinitesimal_name const ay_link_Z3_rcf_infinitesimal_name = &Z3_rcf_infinitesimal_name;
Z3_symbol ay_call_Z3_rcf_infinitesimal_name(Z3_context ay_a0, Z3_rcf_num ay_a1) {
    return Z3_rcf_infinitesimal_name(ay_a0, ay_a1);
}

typedef int (*ay_sig_Z3_rcf_interval)(Z3_context, Z3_rcf_num, bool *, bool *, Z3_rcf_num *, bool *, bool *, Z3_rcf_num *);
ay_sig_Z3_rcf_interval const ay_link_Z3_rcf_interval = &Z3_rcf_interval;
int ay_call_Z3_rcf_interval(Z3_context ay_a0, Z3_rcf_num ay_a1, bool * ay_a2, bool * ay_a3, Z3_rcf_num * ay_a4, bool * ay_a5, bool * ay_a6, Z3_rcf_num * ay_a7) {
    return Z3_rcf_interval(ay_a0, ay_a1, ay_a2, ay_a3, ay_a4, ay_a5, ay_a6, ay_a7);
}

typedef Z3_rcf_num (*ay_sig_Z3_rcf_inv)(Z3_context, Z3_rcf_num);
ay_sig_Z3_rcf_inv const ay_link_Z3_rcf_inv = &Z3_rcf_inv;
Z3_rcf_num ay_call_Z3_rcf_inv(Z3_context ay_a0, Z3_rcf_num ay_a1) {
    return Z3_rcf_inv(ay_a0, ay_a1);
}

typedef bool (*ay_sig_Z3_rcf_is_algebraic)(Z3_context, Z3_rcf_num);
ay_sig_Z3_rcf_is_algebraic const ay_link_Z3_rcf_is_algebraic = &Z3_rcf_is_algebraic;
bool ay_call_Z3_rcf_is_algebraic(Z3_context ay_a0, Z3_rcf_num ay_a1) {
    return Z3_rcf_is_algebraic(ay_a0, ay_a1);
}

typedef bool (*ay_sig_Z3_rcf_is_infinitesimal)(Z3_context, Z3_rcf_num);
ay_sig_Z3_rcf_is_infinitesimal const ay_link_Z3_rcf_is_infinitesimal = &Z3_rcf_is_infinitesimal;
bool ay_call_Z3_rcf_is_infinitesimal(Z3_context ay_a0, Z3_rcf_num ay_a1) {
    return Z3_rcf_is_infinitesimal(ay_a0, ay_a1);
}

typedef bool (*ay_sig_Z3_rcf_is_rational)(Z3_context, Z3_rcf_num);
ay_sig_Z3_rcf_is_rational const ay_link_Z3_rcf_is_rational = &Z3_rcf_is_rational;
bool ay_call_Z3_rcf_is_rational(Z3_context ay_a0, Z3_rcf_num ay_a1) {
    return Z3_rcf_is_rational(ay_a0, ay_a1);
}

typedef bool (*ay_sig_Z3_rcf_is_transcendental)(Z3_context, Z3_rcf_num);
ay_sig_Z3_rcf_is_transcendental const ay_link_Z3_rcf_is_transcendental = &Z3_rcf_is_transcendental;
bool ay_call_Z3_rcf_is_transcendental(Z3_context ay_a0, Z3_rcf_num ay_a1) {
    return Z3_rcf_is_transcendental(ay_a0, ay_a1);
}

typedef bool (*ay_sig_Z3_rcf_le)(Z3_context, Z3_rcf_num, Z3_rcf_num);
ay_sig_Z3_rcf_le const ay_link_Z3_rcf_le = &Z3_rcf_le;
bool ay_call_Z3_rcf_le(Z3_context ay_a0, Z3_rcf_num ay_a1, Z3_rcf_num ay_a2) {
    return Z3_rcf_le(ay_a0, ay_a1, ay_a2);
}

typedef bool (*ay_sig_Z3_rcf_lt)(Z3_context, Z3_rcf_num, Z3_rcf_num);
ay_sig_Z3_rcf_lt const ay_link_Z3_rcf_lt = &Z3_rcf_lt;
bool ay_call_Z3_rcf_lt(Z3_context ay_a0, Z3_rcf_num ay_a1, Z3_rcf_num ay_a2) {
    return Z3_rcf_lt(ay_a0, ay_a1, ay_a2);
}

typedef Z3_rcf_num (*ay_sig_Z3_rcf_mk_e)(Z3_context);
ay_sig_Z3_rcf_mk_e const ay_link_Z3_rcf_mk_e = &Z3_rcf_mk_e;
Z3_rcf_num ay_call_Z3_rcf_mk_e(Z3_context ay_a0) {
    return Z3_rcf_mk_e(ay_a0);
}

typedef Z3_rcf_num (*ay_sig_Z3_rcf_mk_infinitesimal)(Z3_context);
ay_sig_Z3_rcf_mk_infinitesimal const ay_link_Z3_rcf_mk_infinitesimal = &Z3_rcf_mk_infinitesimal;
Z3_rcf_num ay_call_Z3_rcf_mk_infinitesimal(Z3_context ay_a0) {
    return Z3_rcf_mk_infinitesimal(ay_a0);
}

typedef Z3_rcf_num (*ay_sig_Z3_rcf_mk_pi)(Z3_context);
ay_sig_Z3_rcf_mk_pi const ay_link_Z3_rcf_mk_pi = &Z3_rcf_mk_pi;
Z3_rcf_num ay_call_Z3_rcf_mk_pi(Z3_context ay_a0) {
    return Z3_rcf_mk_pi(ay_a0);
}

typedef Z3_rcf_num (*ay_sig_Z3_rcf_mk_rational)(Z3_context, Z3_string);
ay_sig_Z3_rcf_mk_rational const ay_link_Z3_rcf_mk_rational = &Z3_rcf_mk_rational;
Z3_rcf_num ay_call_Z3_rcf_mk_rational(Z3_context ay_a0, Z3_string ay_a1) {
    return Z3_rcf_mk_rational(ay_a0, ay_a1);
}

typedef unsigned int (*ay_sig_Z3_rcf_mk_roots)(Z3_context, unsigned int, const Z3_rcf_num *, Z3_rcf_num *);
ay_sig_Z3_rcf_mk_roots const ay_link_Z3_rcf_mk_roots = &Z3_rcf_mk_roots;
unsigned int ay_call_Z3_rcf_mk_roots(Z3_context ay_a0, unsigned int ay_a1, const Z3_rcf_num * ay_a2, Z3_rcf_num * ay_a3) {
    return Z3_rcf_mk_roots(ay_a0, ay_a1, ay_a2, ay_a3);
}

typedef Z3_rcf_num (*ay_sig_Z3_rcf_mk_small_int)(Z3_context, int);
ay_sig_Z3_rcf_mk_small_int const ay_link_Z3_rcf_mk_small_int = &Z3_rcf_mk_small_int;
Z3_rcf_num ay_call_Z3_rcf_mk_small_int(Z3_context ay_a0, int ay_a1) {
    return Z3_rcf_mk_small_int(ay_a0, ay_a1);
}

typedef Z3_rcf_num (*ay_sig_Z3_rcf_mul)(Z3_context, Z3_rcf_num, Z3_rcf_num);
ay_sig_Z3_rcf_mul const ay_link_Z3_rcf_mul = &Z3_rcf_mul;
Z3_rcf_num ay_call_Z3_rcf_mul(Z3_context ay_a0, Z3_rcf_num ay_a1, Z3_rcf_num ay_a2) {
    return Z3_rcf_mul(ay_a0, ay_a1, ay_a2);
}

typedef Z3_rcf_num (*ay_sig_Z3_rcf_neg)(Z3_context, Z3_rcf_num);
ay_sig_Z3_rcf_neg const ay_link_Z3_rcf_neg = &Z3_rcf_neg;
Z3_rcf_num ay_call_Z3_rcf_neg(Z3_context ay_a0, Z3_rcf_num ay_a1) {
    return Z3_rcf_neg(ay_a0, ay_a1);
}

typedef bool (*ay_sig_Z3_rcf_neq)(Z3_context, Z3_rcf_num, Z3_rcf_num);
ay_sig_Z3_rcf_neq const ay_link_Z3_rcf_neq = &Z3_rcf_neq;
bool ay_call_Z3_rcf_neq(Z3_context ay_a0, Z3_rcf_num ay_a1, Z3_rcf_num ay_a2) {
    return Z3_rcf_neq(ay_a0, ay_a1, ay_a2);
}

typedef unsigned int (*ay_sig_Z3_rcf_num_coefficients)(Z3_context, Z3_rcf_num);
ay_sig_Z3_rcf_num_coefficients const ay_link_Z3_rcf_num_coefficients = &Z3_rcf_num_coefficients;
unsigned int ay_call_Z3_rcf_num_coefficients(Z3_context ay_a0, Z3_rcf_num ay_a1) {
    return Z3_rcf_num_coefficients(ay_a0, ay_a1);
}

typedef unsigned int (*ay_sig_Z3_rcf_num_sign_condition_coefficients)(Z3_context, Z3_rcf_num, unsigned int);
ay_sig_Z3_rcf_num_sign_condition_coefficients const ay_link_Z3_rcf_num_sign_condition_coefficients = &Z3_rcf_num_sign_condition_coefficients;
unsigned int ay_call_Z3_rcf_num_sign_condition_coefficients(Z3_context ay_a0, Z3_rcf_num ay_a1, unsigned int ay_a2) {
    return Z3_rcf_num_sign_condition_coefficients(ay_a0, ay_a1, ay_a2);
}

typedef unsigned int (*ay_sig_Z3_rcf_num_sign_conditions)(Z3_context, Z3_rcf_num);
ay_sig_Z3_rcf_num_sign_conditions const ay_link_Z3_rcf_num_sign_conditions = &Z3_rcf_num_sign_conditions;
unsigned int ay_call_Z3_rcf_num_sign_conditions(Z3_context ay_a0, Z3_rcf_num ay_a1) {
    return Z3_rcf_num_sign_conditions(ay_a0, ay_a1);
}

typedef Z3_string (*ay_sig_Z3_rcf_num_to_decimal_string)(Z3_context, Z3_rcf_num, unsigned int);
ay_sig_Z3_rcf_num_to_decimal_string const ay_link_Z3_rcf_num_to_decimal_string = &Z3_rcf_num_to_decimal_string;
Z3_string ay_call_Z3_rcf_num_to_decimal_string(Z3_context ay_a0, Z3_rcf_num ay_a1, unsigned int ay_a2) {
    return Z3_rcf_num_to_decimal_string(ay_a0, ay_a1, ay_a2);
}

typedef Z3_string (*ay_sig_Z3_rcf_num_to_string)(Z3_context, Z3_rcf_num, bool, bool);
ay_sig_Z3_rcf_num_to_string const ay_link_Z3_rcf_num_to_string = &Z3_rcf_num_to_string;
Z3_string ay_call_Z3_rcf_num_to_string(Z3_context ay_a0, Z3_rcf_num ay_a1, bool ay_a2, bool ay_a3) {
    return Z3_rcf_num_to_string(ay_a0, ay_a1, ay_a2, ay_a3);
}

typedef Z3_rcf_num (*ay_sig_Z3_rcf_power)(Z3_context, Z3_rcf_num, unsigned int);
ay_sig_Z3_rcf_power const ay_link_Z3_rcf_power = &Z3_rcf_power;
Z3_rcf_num ay_call_Z3_rcf_power(Z3_context ay_a0, Z3_rcf_num ay_a1, unsigned int ay_a2) {
    return Z3_rcf_power(ay_a0, ay_a1, ay_a2);
}

typedef Z3_rcf_num (*ay_sig_Z3_rcf_sign_condition_coefficient)(Z3_context, Z3_rcf_num, unsigned int, unsigned int);
ay_sig_Z3_rcf_sign_condition_coefficient const ay_link_Z3_rcf_sign_condition_coefficient = &Z3_rcf_sign_condition_coefficient;
Z3_rcf_num ay_call_Z3_rcf_sign_condition_coefficient(Z3_context ay_a0, Z3_rcf_num ay_a1, unsigned int ay_a2, unsigned int ay_a3) {
    return Z3_rcf_sign_condition_coefficient(ay_a0, ay_a1, ay_a2, ay_a3);
}

typedef int (*ay_sig_Z3_rcf_sign_condition_sign)(Z3_context, Z3_rcf_num, unsigned int);
ay_sig_Z3_rcf_sign_condition_sign const ay_link_Z3_rcf_sign_condition_sign = &Z3_rcf_sign_condition_sign;
int ay_call_Z3_rcf_sign_condition_sign(Z3_context ay_a0, Z3_rcf_num ay_a1, unsigned int ay_a2) {
    return Z3_rcf_sign_condition_sign(ay_a0, ay_a1, ay_a2);
}

typedef Z3_rcf_num (*ay_sig_Z3_rcf_sub)(Z3_context, Z3_rcf_num, Z3_rcf_num);
ay_sig_Z3_rcf_sub const ay_link_Z3_rcf_sub = &Z3_rcf_sub;
Z3_rcf_num ay_call_Z3_rcf_sub(Z3_context ay_a0, Z3_rcf_num ay_a1, Z3_rcf_num ay_a2) {
    return Z3_rcf_sub(ay_a0, ay_a1, ay_a2);
}

typedef Z3_symbol (*ay_sig_Z3_rcf_transcendental_name)(Z3_context, Z3_rcf_num);
ay_sig_Z3_rcf_transcendental_name const ay_link_Z3_rcf_transcendental_name = &Z3_rcf_transcendental_name;
Z3_symbol ay_call_Z3_rcf_transcendental_name(Z3_context ay_a0, Z3_rcf_num ay_a1) {
    return Z3_rcf_transcendental_name(ay_a0, ay_a1);
}

typedef void (*ay_sig_Z3_reset_memory)(void);
ay_sig_Z3_reset_memory const ay_link_Z3_reset_memory = &Z3_reset_memory;
void ay_call_Z3_reset_memory(void) {
    Z3_reset_memory();
}

typedef void (*ay_sig_Z3_set_ast_print_mode)(Z3_context, Z3_ast_print_mode);
ay_sig_Z3_set_ast_print_mode const ay_link_Z3_set_ast_print_mode = &Z3_set_ast_print_mode;
void ay_call_Z3_set_ast_print_mode(Z3_context ay_a0, Z3_ast_print_mode ay_a1) {
    Z3_set_ast_print_mode(ay_a0, ay_a1);
}

typedef void (*ay_sig_Z3_set_error_handler)(Z3_context, Z3_error_handler *);
ay_sig_Z3_set_error_handler const ay_link_Z3_set_error_handler = &Z3_set_error_handler;
void ay_call_Z3_set_error_handler(Z3_context ay_a0, Z3_error_handler * ay_a1) {
    Z3_set_error_handler(ay_a0, ay_a1);
}

typedef void (*ay_sig_Z3_set_error)(Z3_context, Z3_error_code);
ay_sig_Z3_set_error const ay_link_Z3_set_error = &Z3_set_error;
void ay_call_Z3_set_error(Z3_context ay_a0, Z3_error_code ay_a1) {
    Z3_set_error(ay_a0, ay_a1);
}

typedef void (*ay_sig_Z3_set_param_value)(Z3_config, Z3_string, Z3_string);
ay_sig_Z3_set_param_value const ay_link_Z3_set_param_value = &Z3_set_param_value;
void ay_call_Z3_set_param_value(Z3_config ay_a0, Z3_string ay_a1, Z3_string ay_a2) {
    Z3_set_param_value(ay_a0, ay_a1, ay_a2);
}

typedef Z3_simplifier (*ay_sig_Z3_simplifier_and_then)(Z3_context, Z3_simplifier, Z3_simplifier);
ay_sig_Z3_simplifier_and_then const ay_link_Z3_simplifier_and_then = &Z3_simplifier_and_then;
Z3_simplifier ay_call_Z3_simplifier_and_then(Z3_context ay_a0, Z3_simplifier ay_a1, Z3_simplifier ay_a2) {
    return Z3_simplifier_and_then(ay_a0, ay_a1, ay_a2);
}

typedef void (*ay_sig_Z3_simplifier_dec_ref)(Z3_context, Z3_simplifier);
ay_sig_Z3_simplifier_dec_ref const ay_link_Z3_simplifier_dec_ref = &Z3_simplifier_dec_ref;
void ay_call_Z3_simplifier_dec_ref(Z3_context ay_a0, Z3_simplifier ay_a1) {
    Z3_simplifier_dec_ref(ay_a0, ay_a1);
}

typedef Z3_string (*ay_sig_Z3_simplifier_get_descr)(Z3_context, Z3_string);
ay_sig_Z3_simplifier_get_descr const ay_link_Z3_simplifier_get_descr = &Z3_simplifier_get_descr;
Z3_string ay_call_Z3_simplifier_get_descr(Z3_context ay_a0, Z3_string ay_a1) {
    return Z3_simplifier_get_descr(ay_a0, ay_a1);
}

typedef Z3_string (*ay_sig_Z3_simplifier_get_help)(Z3_context, Z3_simplifier);
ay_sig_Z3_simplifier_get_help const ay_link_Z3_simplifier_get_help = &Z3_simplifier_get_help;
Z3_string ay_call_Z3_simplifier_get_help(Z3_context ay_a0, Z3_simplifier ay_a1) {
    return Z3_simplifier_get_help(ay_a0, ay_a1);
}

typedef Z3_param_descrs (*ay_sig_Z3_simplifier_get_param_descrs)(Z3_context, Z3_simplifier);
ay_sig_Z3_simplifier_get_param_descrs const ay_link_Z3_simplifier_get_param_descrs = &Z3_simplifier_get_param_descrs;
Z3_param_descrs ay_call_Z3_simplifier_get_param_descrs(Z3_context ay_a0, Z3_simplifier ay_a1) {
    return Z3_simplifier_get_param_descrs(ay_a0, ay_a1);
}

typedef void (*ay_sig_Z3_simplifier_inc_ref)(Z3_context, Z3_simplifier);
ay_sig_Z3_simplifier_inc_ref const ay_link_Z3_simplifier_inc_ref = &Z3_simplifier_inc_ref;
void ay_call_Z3_simplifier_inc_ref(Z3_context ay_a0, Z3_simplifier ay_a1) {
    Z3_simplifier_inc_ref(ay_a0, ay_a1);
}

typedef Z3_simplifier (*ay_sig_Z3_simplifier_using_params)(Z3_context, Z3_simplifier, Z3_params);
ay_sig_Z3_simplifier_using_params const ay_link_Z3_simplifier_using_params = &Z3_simplifier_using_params;
Z3_simplifier ay_call_Z3_simplifier_using_params(Z3_context ay_a0, Z3_simplifier ay_a1, Z3_params ay_a2) {
    return Z3_simplifier_using_params(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_simplify_ex)(Z3_context, Z3_ast, Z3_params);
ay_sig_Z3_simplify_ex const ay_link_Z3_simplify_ex = &Z3_simplify_ex;
Z3_ast ay_call_Z3_simplify_ex(Z3_context ay_a0, Z3_ast ay_a1, Z3_params ay_a2) {
    return Z3_simplify_ex(ay_a0, ay_a1, ay_a2);
}

typedef Z3_string (*ay_sig_Z3_simplify_get_help)(Z3_context);
ay_sig_Z3_simplify_get_help const ay_link_Z3_simplify_get_help = &Z3_simplify_get_help;
Z3_string ay_call_Z3_simplify_get_help(Z3_context ay_a0) {
    return Z3_simplify_get_help(ay_a0);
}

typedef Z3_param_descrs (*ay_sig_Z3_simplify_get_param_descrs)(Z3_context);
ay_sig_Z3_simplify_get_param_descrs const ay_link_Z3_simplify_get_param_descrs = &Z3_simplify_get_param_descrs;
Z3_param_descrs ay_call_Z3_simplify_get_param_descrs(Z3_context ay_a0) {
    return Z3_simplify_get_param_descrs(ay_a0);
}

typedef Z3_ast (*ay_sig_Z3_simplify)(Z3_context, Z3_ast);
ay_sig_Z3_simplify const ay_link_Z3_simplify = &Z3_simplify;
Z3_ast ay_call_Z3_simplify(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_simplify(ay_a0, ay_a1);
}

typedef Z3_solver (*ay_sig_Z3_solver_add_simplifier)(Z3_context, Z3_solver, Z3_simplifier);
ay_sig_Z3_solver_add_simplifier const ay_link_Z3_solver_add_simplifier = &Z3_solver_add_simplifier;
Z3_solver ay_call_Z3_solver_add_simplifier(Z3_context ay_a0, Z3_solver ay_a1, Z3_simplifier ay_a2) {
    return Z3_solver_add_simplifier(ay_a0, ay_a1, ay_a2);
}

typedef void (*ay_sig_Z3_solver_assert_and_track)(Z3_context, Z3_solver, Z3_ast, Z3_ast);
ay_sig_Z3_solver_assert_and_track const ay_link_Z3_solver_assert_and_track = &Z3_solver_assert_and_track;
void ay_call_Z3_solver_assert_and_track(Z3_context ay_a0, Z3_solver ay_a1, Z3_ast ay_a2, Z3_ast ay_a3) {
    Z3_solver_assert_and_track(ay_a0, ay_a1, ay_a2, ay_a3);
}

typedef void (*ay_sig_Z3_solver_assert)(Z3_context, Z3_solver, Z3_ast);
ay_sig_Z3_solver_assert const ay_link_Z3_solver_assert = &Z3_solver_assert;
void ay_call_Z3_solver_assert(Z3_context ay_a0, Z3_solver ay_a1, Z3_ast ay_a2) {
    Z3_solver_assert(ay_a0, ay_a1, ay_a2);
}

typedef Z3_lbool (*ay_sig_Z3_solver_check_assumptions)(Z3_context, Z3_solver, unsigned int, const Z3_ast *);
ay_sig_Z3_solver_check_assumptions const ay_link_Z3_solver_check_assumptions = &Z3_solver_check_assumptions;
Z3_lbool ay_call_Z3_solver_check_assumptions(Z3_context ay_a0, Z3_solver ay_a1, unsigned int ay_a2, const Z3_ast * ay_a3) {
    return Z3_solver_check_assumptions(ay_a0, ay_a1, ay_a2, ay_a3);
}

typedef Z3_lbool (*ay_sig_Z3_solver_check)(Z3_context, Z3_solver);
ay_sig_Z3_solver_check const ay_link_Z3_solver_check = &Z3_solver_check;
Z3_lbool ay_call_Z3_solver_check(Z3_context ay_a0, Z3_solver ay_a1) {
    return Z3_solver_check(ay_a0, ay_a1);
}

typedef Z3_ast (*ay_sig_Z3_solver_congruence_explain)(Z3_context, Z3_solver, Z3_ast, Z3_ast);
ay_sig_Z3_solver_congruence_explain const ay_link_Z3_solver_congruence_explain = &Z3_solver_congruence_explain;
Z3_ast ay_call_Z3_solver_congruence_explain(Z3_context ay_a0, Z3_solver ay_a1, Z3_ast ay_a2, Z3_ast ay_a3) {
    return Z3_solver_congruence_explain(ay_a0, ay_a1, ay_a2, ay_a3);
}

typedef Z3_ast (*ay_sig_Z3_solver_congruence_next)(Z3_context, Z3_solver, Z3_ast);
ay_sig_Z3_solver_congruence_next const ay_link_Z3_solver_congruence_next = &Z3_solver_congruence_next;
Z3_ast ay_call_Z3_solver_congruence_next(Z3_context ay_a0, Z3_solver ay_a1, Z3_ast ay_a2) {
    return Z3_solver_congruence_next(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_solver_congruence_root)(Z3_context, Z3_solver, Z3_ast);
ay_sig_Z3_solver_congruence_root const ay_link_Z3_solver_congruence_root = &Z3_solver_congruence_root;
Z3_ast ay_call_Z3_solver_congruence_root(Z3_context ay_a0, Z3_solver ay_a1, Z3_ast ay_a2) {
    return Z3_solver_congruence_root(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast_vector (*ay_sig_Z3_solver_cube)(Z3_context, Z3_solver, Z3_ast_vector, unsigned int);
ay_sig_Z3_solver_cube const ay_link_Z3_solver_cube = &Z3_solver_cube;
Z3_ast_vector ay_call_Z3_solver_cube(Z3_context ay_a0, Z3_solver ay_a1, Z3_ast_vector ay_a2, unsigned int ay_a3) {
    return Z3_solver_cube(ay_a0, ay_a1, ay_a2, ay_a3);
}

typedef void (*ay_sig_Z3_solver_dec_ref)(Z3_context, Z3_solver);
ay_sig_Z3_solver_dec_ref const ay_link_Z3_solver_dec_ref = &Z3_solver_dec_ref;
void ay_call_Z3_solver_dec_ref(Z3_context ay_a0, Z3_solver ay_a1) {
    Z3_solver_dec_ref(ay_a0, ay_a1);
}

typedef void (*ay_sig_Z3_solver_from_file)(Z3_context, Z3_solver, Z3_string);
ay_sig_Z3_solver_from_file const ay_link_Z3_solver_from_file = &Z3_solver_from_file;
void ay_call_Z3_solver_from_file(Z3_context ay_a0, Z3_solver ay_a1, Z3_string ay_a2) {
    Z3_solver_from_file(ay_a0, ay_a1, ay_a2);
}

typedef void (*ay_sig_Z3_solver_from_string)(Z3_context, Z3_solver, Z3_string);
ay_sig_Z3_solver_from_string const ay_link_Z3_solver_from_string = &Z3_solver_from_string;
void ay_call_Z3_solver_from_string(Z3_context ay_a0, Z3_solver ay_a1, Z3_string ay_a2) {
    Z3_solver_from_string(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast_vector (*ay_sig_Z3_solver_get_assertions)(Z3_context, Z3_solver);
ay_sig_Z3_solver_get_assertions const ay_link_Z3_solver_get_assertions = &Z3_solver_get_assertions;
Z3_ast_vector ay_call_Z3_solver_get_assertions(Z3_context ay_a0, Z3_solver ay_a1) {
    return Z3_solver_get_assertions(ay_a0, ay_a1);
}

typedef Z3_lbool (*ay_sig_Z3_solver_get_consequences)(Z3_context, Z3_solver, Z3_ast_vector, Z3_ast_vector, Z3_ast_vector);
ay_sig_Z3_solver_get_consequences const ay_link_Z3_solver_get_consequences = &Z3_solver_get_consequences;
Z3_lbool ay_call_Z3_solver_get_consequences(Z3_context ay_a0, Z3_solver ay_a1, Z3_ast_vector ay_a2, Z3_ast_vector ay_a3, Z3_ast_vector ay_a4) {
    return Z3_solver_get_consequences(ay_a0, ay_a1, ay_a2, ay_a3, ay_a4);
}

typedef Z3_string (*ay_sig_Z3_solver_get_help)(Z3_context, Z3_solver);
ay_sig_Z3_solver_get_help const ay_link_Z3_solver_get_help = &Z3_solver_get_help;
Z3_string ay_call_Z3_solver_get_help(Z3_context ay_a0, Z3_solver ay_a1) {
    return Z3_solver_get_help(ay_a0, ay_a1);
}

typedef void (*ay_sig_Z3_solver_get_levels)(Z3_context, Z3_solver, Z3_ast_vector, unsigned int, unsigned int *);
ay_sig_Z3_solver_get_levels const ay_link_Z3_solver_get_levels = &Z3_solver_get_levels;
void ay_call_Z3_solver_get_levels(Z3_context ay_a0, Z3_solver ay_a1, Z3_ast_vector ay_a2, unsigned int ay_a3, unsigned int * ay_a4) {
    Z3_solver_get_levels(ay_a0, ay_a1, ay_a2, ay_a3, ay_a4);
}

typedef Z3_model (*ay_sig_Z3_solver_get_model)(Z3_context, Z3_solver);
ay_sig_Z3_solver_get_model const ay_link_Z3_solver_get_model = &Z3_solver_get_model;
Z3_model ay_call_Z3_solver_get_model(Z3_context ay_a0, Z3_solver ay_a1) {
    return Z3_solver_get_model(ay_a0, ay_a1);
}

typedef Z3_ast_vector (*ay_sig_Z3_solver_get_non_units)(Z3_context, Z3_solver);
ay_sig_Z3_solver_get_non_units const ay_link_Z3_solver_get_non_units = &Z3_solver_get_non_units;
Z3_ast_vector ay_call_Z3_solver_get_non_units(Z3_context ay_a0, Z3_solver ay_a1) {
    return Z3_solver_get_non_units(ay_a0, ay_a1);
}

typedef unsigned int (*ay_sig_Z3_solver_get_num_scopes)(Z3_context, Z3_solver);
ay_sig_Z3_solver_get_num_scopes const ay_link_Z3_solver_get_num_scopes = &Z3_solver_get_num_scopes;
unsigned int ay_call_Z3_solver_get_num_scopes(Z3_context ay_a0, Z3_solver ay_a1) {
    return Z3_solver_get_num_scopes(ay_a0, ay_a1);
}

typedef Z3_param_descrs (*ay_sig_Z3_solver_get_param_descrs)(Z3_context, Z3_solver);
ay_sig_Z3_solver_get_param_descrs const ay_link_Z3_solver_get_param_descrs = &Z3_solver_get_param_descrs;
Z3_param_descrs ay_call_Z3_solver_get_param_descrs(Z3_context ay_a0, Z3_solver ay_a1) {
    return Z3_solver_get_param_descrs(ay_a0, ay_a1);
}

typedef Z3_ast (*ay_sig_Z3_solver_get_proof)(Z3_context, Z3_solver);
ay_sig_Z3_solver_get_proof const ay_link_Z3_solver_get_proof = &Z3_solver_get_proof;
Z3_ast ay_call_Z3_solver_get_proof(Z3_context ay_a0, Z3_solver ay_a1) {
    return Z3_solver_get_proof(ay_a0, ay_a1);
}

typedef Z3_string (*ay_sig_Z3_solver_get_reason_unknown)(Z3_context, Z3_solver);
ay_sig_Z3_solver_get_reason_unknown const ay_link_Z3_solver_get_reason_unknown = &Z3_solver_get_reason_unknown;
Z3_string ay_call_Z3_solver_get_reason_unknown(Z3_context ay_a0, Z3_solver ay_a1) {
    return Z3_solver_get_reason_unknown(ay_a0, ay_a1);
}

typedef Z3_stats (*ay_sig_Z3_solver_get_statistics)(Z3_context, Z3_solver);
ay_sig_Z3_solver_get_statistics const ay_link_Z3_solver_get_statistics = &Z3_solver_get_statistics;
Z3_stats ay_call_Z3_solver_get_statistics(Z3_context ay_a0, Z3_solver ay_a1) {
    return Z3_solver_get_statistics(ay_a0, ay_a1);
}

typedef Z3_ast_vector (*ay_sig_Z3_solver_get_trail)(Z3_context, Z3_solver);
ay_sig_Z3_solver_get_trail const ay_link_Z3_solver_get_trail = &Z3_solver_get_trail;
Z3_ast_vector ay_call_Z3_solver_get_trail(Z3_context ay_a0, Z3_solver ay_a1) {
    return Z3_solver_get_trail(ay_a0, ay_a1);
}

typedef Z3_ast_vector (*ay_sig_Z3_solver_get_units)(Z3_context, Z3_solver);
ay_sig_Z3_solver_get_units const ay_link_Z3_solver_get_units = &Z3_solver_get_units;
Z3_ast_vector ay_call_Z3_solver_get_units(Z3_context ay_a0, Z3_solver ay_a1) {
    return Z3_solver_get_units(ay_a0, ay_a1);
}

typedef Z3_ast_vector (*ay_sig_Z3_solver_get_unsat_core)(Z3_context, Z3_solver);
ay_sig_Z3_solver_get_unsat_core const ay_link_Z3_solver_get_unsat_core = &Z3_solver_get_unsat_core;
Z3_ast_vector ay_call_Z3_solver_get_unsat_core(Z3_context ay_a0, Z3_solver ay_a1) {
    return Z3_solver_get_unsat_core(ay_a0, ay_a1);
}

typedef void (*ay_sig_Z3_solver_import_model_converter)(Z3_context, Z3_solver, Z3_solver);
ay_sig_Z3_solver_import_model_converter const ay_link_Z3_solver_import_model_converter = &Z3_solver_import_model_converter;
void ay_call_Z3_solver_import_model_converter(Z3_context ay_a0, Z3_solver ay_a1, Z3_solver ay_a2) {
    Z3_solver_import_model_converter(ay_a0, ay_a1, ay_a2);
}

typedef void (*ay_sig_Z3_solver_inc_ref)(Z3_context, Z3_solver);
ay_sig_Z3_solver_inc_ref const ay_link_Z3_solver_inc_ref = &Z3_solver_inc_ref;
void ay_call_Z3_solver_inc_ref(Z3_context ay_a0, Z3_solver ay_a1) {
    Z3_solver_inc_ref(ay_a0, ay_a1);
}

typedef void (*ay_sig_Z3_solver_interrupt)(Z3_context, Z3_solver);
ay_sig_Z3_solver_interrupt const ay_link_Z3_solver_interrupt = &Z3_solver_interrupt;
void ay_call_Z3_solver_interrupt(Z3_context ay_a0, Z3_solver ay_a1) {
    Z3_solver_interrupt(ay_a0, ay_a1);
}

typedef bool (*ay_sig_Z3_solver_next_split)(Z3_context, Z3_solver_callback, Z3_ast, unsigned int, Z3_lbool);
ay_sig_Z3_solver_next_split const ay_link_Z3_solver_next_split = &Z3_solver_next_split;
bool ay_call_Z3_solver_next_split(Z3_context ay_a0, Z3_solver_callback ay_a1, Z3_ast ay_a2, unsigned int ay_a3, Z3_lbool ay_a4) {
    return Z3_solver_next_split(ay_a0, ay_a1, ay_a2, ay_a3, ay_a4);
}

typedef void (*ay_sig_Z3_solver_pop)(Z3_context, Z3_solver, unsigned int);
ay_sig_Z3_solver_pop const ay_link_Z3_solver_pop = &Z3_solver_pop;
void ay_call_Z3_solver_pop(Z3_context ay_a0, Z3_solver ay_a1, unsigned int ay_a2) {
    Z3_solver_pop(ay_a0, ay_a1, ay_a2);
}

typedef bool (*ay_sig_Z3_solver_propagate_consequence)(Z3_context, Z3_solver_callback, unsigned int, const Z3_ast *, unsigned int, const Z3_ast *, const Z3_ast *, Z3_ast);
ay_sig_Z3_solver_propagate_consequence const ay_link_Z3_solver_propagate_consequence = &Z3_solver_propagate_consequence;
bool ay_call_Z3_solver_propagate_consequence(Z3_context ay_a0, Z3_solver_callback ay_a1, unsigned int ay_a2, const Z3_ast * ay_a3, unsigned int ay_a4, const Z3_ast * ay_a5, const Z3_ast * ay_a6, Z3_ast ay_a7) {
    return Z3_solver_propagate_consequence(ay_a0, ay_a1, ay_a2, ay_a3, ay_a4, ay_a5, ay_a6, ay_a7);
}

typedef void (*ay_sig_Z3_solver_propagate_created)(Z3_context, Z3_solver, Z3_created_eh *);
ay_sig_Z3_solver_propagate_created const ay_link_Z3_solver_propagate_created = &Z3_solver_propagate_created;
void ay_call_Z3_solver_propagate_created(Z3_context ay_a0, Z3_solver ay_a1, Z3_created_eh * ay_a2) {
    Z3_solver_propagate_created(ay_a0, ay_a1, ay_a2);
}

typedef void (*ay_sig_Z3_solver_propagate_decide)(Z3_context, Z3_solver, Z3_decide_eh *);
ay_sig_Z3_solver_propagate_decide const ay_link_Z3_solver_propagate_decide = &Z3_solver_propagate_decide;
void ay_call_Z3_solver_propagate_decide(Z3_context ay_a0, Z3_solver ay_a1, Z3_decide_eh * ay_a2) {
    Z3_solver_propagate_decide(ay_a0, ay_a1, ay_a2);
}

typedef Z3_func_decl (*ay_sig_Z3_solver_propagate_declare)(Z3_context, Z3_symbol, unsigned int, Z3_sort *, Z3_sort);
ay_sig_Z3_solver_propagate_declare const ay_link_Z3_solver_propagate_declare = &Z3_solver_propagate_declare;
Z3_func_decl ay_call_Z3_solver_propagate_declare(Z3_context ay_a0, Z3_symbol ay_a1, unsigned int ay_a2, Z3_sort * ay_a3, Z3_sort ay_a4) {
    return Z3_solver_propagate_declare(ay_a0, ay_a1, ay_a2, ay_a3, ay_a4);
}

typedef void (*ay_sig_Z3_solver_propagate_diseq)(Z3_context, Z3_solver, Z3_eq_eh *);
ay_sig_Z3_solver_propagate_diseq const ay_link_Z3_solver_propagate_diseq = &Z3_solver_propagate_diseq;
void ay_call_Z3_solver_propagate_diseq(Z3_context ay_a0, Z3_solver ay_a1, Z3_eq_eh * ay_a2) {
    Z3_solver_propagate_diseq(ay_a0, ay_a1, ay_a2);
}

typedef void (*ay_sig_Z3_solver_propagate_eq)(Z3_context, Z3_solver, Z3_eq_eh *);
ay_sig_Z3_solver_propagate_eq const ay_link_Z3_solver_propagate_eq = &Z3_solver_propagate_eq;
void ay_call_Z3_solver_propagate_eq(Z3_context ay_a0, Z3_solver ay_a1, Z3_eq_eh * ay_a2) {
    Z3_solver_propagate_eq(ay_a0, ay_a1, ay_a2);
}

typedef void (*ay_sig_Z3_solver_propagate_final)(Z3_context, Z3_solver, Z3_final_eh *);
ay_sig_Z3_solver_propagate_final const ay_link_Z3_solver_propagate_final = &Z3_solver_propagate_final;
void ay_call_Z3_solver_propagate_final(Z3_context ay_a0, Z3_solver ay_a1, Z3_final_eh * ay_a2) {
    Z3_solver_propagate_final(ay_a0, ay_a1, ay_a2);
}

typedef void (*ay_sig_Z3_solver_propagate_fixed)(Z3_context, Z3_solver, Z3_fixed_eh *);
ay_sig_Z3_solver_propagate_fixed const ay_link_Z3_solver_propagate_fixed = &Z3_solver_propagate_fixed;
void ay_call_Z3_solver_propagate_fixed(Z3_context ay_a0, Z3_solver ay_a1, Z3_fixed_eh * ay_a2) {
    Z3_solver_propagate_fixed(ay_a0, ay_a1, ay_a2);
}

typedef void (*ay_sig_Z3_solver_propagate_init)(Z3_context, Z3_solver, void *, Z3_push_eh *, Z3_pop_eh *, Z3_fresh_eh *);
ay_sig_Z3_solver_propagate_init const ay_link_Z3_solver_propagate_init = &Z3_solver_propagate_init;
void ay_call_Z3_solver_propagate_init(Z3_context ay_a0, Z3_solver ay_a1, void * ay_a2, Z3_push_eh * ay_a3, Z3_pop_eh * ay_a4, Z3_fresh_eh * ay_a5) {
    Z3_solver_propagate_init(ay_a0, ay_a1, ay_a2, ay_a3, ay_a4, ay_a5);
}

typedef void (*ay_sig_Z3_solver_propagate_on_binding)(Z3_context, Z3_solver, Z3_on_binding_eh *);
ay_sig_Z3_solver_propagate_on_binding const ay_link_Z3_solver_propagate_on_binding = &Z3_solver_propagate_on_binding;
void ay_call_Z3_solver_propagate_on_binding(Z3_context ay_a0, Z3_solver ay_a1, Z3_on_binding_eh * ay_a2) {
    Z3_solver_propagate_on_binding(ay_a0, ay_a1, ay_a2);
}

typedef void (*ay_sig_Z3_solver_propagate_register_cb)(Z3_context, Z3_solver_callback, Z3_ast);
ay_sig_Z3_solver_propagate_register_cb const ay_link_Z3_solver_propagate_register_cb = &Z3_solver_propagate_register_cb;
void ay_call_Z3_solver_propagate_register_cb(Z3_context ay_a0, Z3_solver_callback ay_a1, Z3_ast ay_a2) {
    Z3_solver_propagate_register_cb(ay_a0, ay_a1, ay_a2);
}

typedef void (*ay_sig_Z3_solver_propagate_register)(Z3_context, Z3_solver, Z3_ast);
ay_sig_Z3_solver_propagate_register const ay_link_Z3_solver_propagate_register = &Z3_solver_propagate_register;
void ay_call_Z3_solver_propagate_register(Z3_context ay_a0, Z3_solver ay_a1, Z3_ast ay_a2) {
    Z3_solver_propagate_register(ay_a0, ay_a1, ay_a2);
}

typedef void (*ay_sig_Z3_solver_push)(Z3_context, Z3_solver);
ay_sig_Z3_solver_push const ay_link_Z3_solver_push = &Z3_solver_push;
void ay_call_Z3_solver_push(Z3_context ay_a0, Z3_solver ay_a1) {
    Z3_solver_push(ay_a0, ay_a1);
}

typedef void (*ay_sig_Z3_solver_register_on_clause)(Z3_context, Z3_solver, void *, Z3_on_clause_eh *);
ay_sig_Z3_solver_register_on_clause const ay_link_Z3_solver_register_on_clause = &Z3_solver_register_on_clause;
void ay_call_Z3_solver_register_on_clause(Z3_context ay_a0, Z3_solver ay_a1, void * ay_a2, Z3_on_clause_eh * ay_a3) {
    Z3_solver_register_on_clause(ay_a0, ay_a1, ay_a2, ay_a3);
}

typedef void (*ay_sig_Z3_solver_reset)(Z3_context, Z3_solver);
ay_sig_Z3_solver_reset const ay_link_Z3_solver_reset = &Z3_solver_reset;
void ay_call_Z3_solver_reset(Z3_context ay_a0, Z3_solver ay_a1) {
    Z3_solver_reset(ay_a0, ay_a1);
}

typedef void (*ay_sig_Z3_solver_set_initial_value)(Z3_context, Z3_solver, Z3_ast, Z3_ast);
ay_sig_Z3_solver_set_initial_value const ay_link_Z3_solver_set_initial_value = &Z3_solver_set_initial_value;
void ay_call_Z3_solver_set_initial_value(Z3_context ay_a0, Z3_solver ay_a1, Z3_ast ay_a2, Z3_ast ay_a3) {
    Z3_solver_set_initial_value(ay_a0, ay_a1, ay_a2, ay_a3);
}

typedef void (*ay_sig_Z3_solver_set_params)(Z3_context, Z3_solver, Z3_params);
ay_sig_Z3_solver_set_params const ay_link_Z3_solver_set_params = &Z3_solver_set_params;
void ay_call_Z3_solver_set_params(Z3_context ay_a0, Z3_solver ay_a1, Z3_params ay_a2) {
    Z3_solver_set_params(ay_a0, ay_a1, ay_a2);
}

typedef void (*ay_sig_Z3_solver_solve_for)(Z3_context, Z3_solver, Z3_ast_vector, Z3_ast_vector, Z3_ast_vector);
ay_sig_Z3_solver_solve_for const ay_link_Z3_solver_solve_for = &Z3_solver_solve_for;
void ay_call_Z3_solver_solve_for(Z3_context ay_a0, Z3_solver ay_a1, Z3_ast_vector ay_a2, Z3_ast_vector ay_a3, Z3_ast_vector ay_a4) {
    Z3_solver_solve_for(ay_a0, ay_a1, ay_a2, ay_a3, ay_a4);
}

typedef Z3_string (*ay_sig_Z3_solver_to_dimacs_string)(Z3_context, Z3_solver, bool);
ay_sig_Z3_solver_to_dimacs_string const ay_link_Z3_solver_to_dimacs_string = &Z3_solver_to_dimacs_string;
Z3_string ay_call_Z3_solver_to_dimacs_string(Z3_context ay_a0, Z3_solver ay_a1, bool ay_a2) {
    return Z3_solver_to_dimacs_string(ay_a0, ay_a1, ay_a2);
}

typedef Z3_string (*ay_sig_Z3_solver_to_string)(Z3_context, Z3_solver);
ay_sig_Z3_solver_to_string const ay_link_Z3_solver_to_string = &Z3_solver_to_string;
Z3_string ay_call_Z3_solver_to_string(Z3_context ay_a0, Z3_solver ay_a1) {
    return Z3_solver_to_string(ay_a0, ay_a1);
}

typedef Z3_solver (*ay_sig_Z3_solver_translate)(Z3_context, Z3_solver, Z3_context);
ay_sig_Z3_solver_translate const ay_link_Z3_solver_translate = &Z3_solver_translate;
Z3_solver ay_call_Z3_solver_translate(Z3_context ay_a0, Z3_solver ay_a1, Z3_context ay_a2) {
    return Z3_solver_translate(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_sort_to_ast)(Z3_context, Z3_sort);
ay_sig_Z3_sort_to_ast const ay_link_Z3_sort_to_ast = &Z3_sort_to_ast;
Z3_ast ay_call_Z3_sort_to_ast(Z3_context ay_a0, Z3_sort ay_a1) {
    return Z3_sort_to_ast(ay_a0, ay_a1);
}

typedef Z3_string (*ay_sig_Z3_sort_to_string)(Z3_context, Z3_sort);
ay_sig_Z3_sort_to_string const ay_link_Z3_sort_to_string = &Z3_sort_to_string;
Z3_string ay_call_Z3_sort_to_string(Z3_context ay_a0, Z3_sort ay_a1) {
    return Z3_sort_to_string(ay_a0, ay_a1);
}

typedef void (*ay_sig_Z3_stats_dec_ref)(Z3_context, Z3_stats);
ay_sig_Z3_stats_dec_ref const ay_link_Z3_stats_dec_ref = &Z3_stats_dec_ref;
void ay_call_Z3_stats_dec_ref(Z3_context ay_a0, Z3_stats ay_a1) {
    Z3_stats_dec_ref(ay_a0, ay_a1);
}

typedef double (*ay_sig_Z3_stats_get_double_value)(Z3_context, Z3_stats, unsigned int);
ay_sig_Z3_stats_get_double_value const ay_link_Z3_stats_get_double_value = &Z3_stats_get_double_value;
double ay_call_Z3_stats_get_double_value(Z3_context ay_a0, Z3_stats ay_a1, unsigned int ay_a2) {
    return Z3_stats_get_double_value(ay_a0, ay_a1, ay_a2);
}

typedef Z3_string (*ay_sig_Z3_stats_get_key)(Z3_context, Z3_stats, unsigned int);
ay_sig_Z3_stats_get_key const ay_link_Z3_stats_get_key = &Z3_stats_get_key;
Z3_string ay_call_Z3_stats_get_key(Z3_context ay_a0, Z3_stats ay_a1, unsigned int ay_a2) {
    return Z3_stats_get_key(ay_a0, ay_a1, ay_a2);
}

typedef unsigned int (*ay_sig_Z3_stats_get_uint_value)(Z3_context, Z3_stats, unsigned int);
ay_sig_Z3_stats_get_uint_value const ay_link_Z3_stats_get_uint_value = &Z3_stats_get_uint_value;
unsigned int ay_call_Z3_stats_get_uint_value(Z3_context ay_a0, Z3_stats ay_a1, unsigned int ay_a2) {
    return Z3_stats_get_uint_value(ay_a0, ay_a1, ay_a2);
}

typedef void (*ay_sig_Z3_stats_inc_ref)(Z3_context, Z3_stats);
ay_sig_Z3_stats_inc_ref const ay_link_Z3_stats_inc_ref = &Z3_stats_inc_ref;
void ay_call_Z3_stats_inc_ref(Z3_context ay_a0, Z3_stats ay_a1) {
    Z3_stats_inc_ref(ay_a0, ay_a1);
}

typedef bool (*ay_sig_Z3_stats_is_double)(Z3_context, Z3_stats, unsigned int);
ay_sig_Z3_stats_is_double const ay_link_Z3_stats_is_double = &Z3_stats_is_double;
bool ay_call_Z3_stats_is_double(Z3_context ay_a0, Z3_stats ay_a1, unsigned int ay_a2) {
    return Z3_stats_is_double(ay_a0, ay_a1, ay_a2);
}

typedef bool (*ay_sig_Z3_stats_is_uint)(Z3_context, Z3_stats, unsigned int);
ay_sig_Z3_stats_is_uint const ay_link_Z3_stats_is_uint = &Z3_stats_is_uint;
bool ay_call_Z3_stats_is_uint(Z3_context ay_a0, Z3_stats ay_a1, unsigned int ay_a2) {
    return Z3_stats_is_uint(ay_a0, ay_a1, ay_a2);
}

typedef unsigned int (*ay_sig_Z3_stats_size)(Z3_context, Z3_stats);
ay_sig_Z3_stats_size const ay_link_Z3_stats_size = &Z3_stats_size;
unsigned int ay_call_Z3_stats_size(Z3_context ay_a0, Z3_stats ay_a1) {
    return Z3_stats_size(ay_a0, ay_a1);
}

typedef Z3_string (*ay_sig_Z3_stats_to_string)(Z3_context, Z3_stats);
ay_sig_Z3_stats_to_string const ay_link_Z3_stats_to_string = &Z3_stats_to_string;
Z3_string ay_call_Z3_stats_to_string(Z3_context ay_a0, Z3_stats ay_a1) {
    return Z3_stats_to_string(ay_a0, ay_a1);
}

typedef Z3_ast (*ay_sig_Z3_substitute_funs)(Z3_context, Z3_ast, unsigned int, const Z3_func_decl *, const Z3_ast *);
ay_sig_Z3_substitute_funs const ay_link_Z3_substitute_funs = &Z3_substitute_funs;
Z3_ast ay_call_Z3_substitute_funs(Z3_context ay_a0, Z3_ast ay_a1, unsigned int ay_a2, const Z3_func_decl * ay_a3, const Z3_ast * ay_a4) {
    return Z3_substitute_funs(ay_a0, ay_a1, ay_a2, ay_a3, ay_a4);
}

typedef Z3_ast (*ay_sig_Z3_substitute_vars)(Z3_context, Z3_ast, unsigned int, const Z3_ast *);
ay_sig_Z3_substitute_vars const ay_link_Z3_substitute_vars = &Z3_substitute_vars;
Z3_ast ay_call_Z3_substitute_vars(Z3_context ay_a0, Z3_ast ay_a1, unsigned int ay_a2, const Z3_ast * ay_a3) {
    return Z3_substitute_vars(ay_a0, ay_a1, ay_a2, ay_a3);
}

typedef Z3_ast (*ay_sig_Z3_substitute)(Z3_context, Z3_ast, unsigned int, const Z3_ast *, const Z3_ast *);
ay_sig_Z3_substitute const ay_link_Z3_substitute = &Z3_substitute;
Z3_ast ay_call_Z3_substitute(Z3_context ay_a0, Z3_ast ay_a1, unsigned int ay_a2, const Z3_ast * ay_a3, const Z3_ast * ay_a4) {
    return Z3_substitute(ay_a0, ay_a1, ay_a2, ay_a3, ay_a4);
}

typedef Z3_tactic (*ay_sig_Z3_tactic_and_then)(Z3_context, Z3_tactic, Z3_tactic);
ay_sig_Z3_tactic_and_then const ay_link_Z3_tactic_and_then = &Z3_tactic_and_then;
Z3_tactic ay_call_Z3_tactic_and_then(Z3_context ay_a0, Z3_tactic ay_a1, Z3_tactic ay_a2) {
    return Z3_tactic_and_then(ay_a0, ay_a1, ay_a2);
}

typedef Z3_apply_result (*ay_sig_Z3_tactic_apply_ex)(Z3_context, Z3_tactic, Z3_goal, Z3_params);
ay_sig_Z3_tactic_apply_ex const ay_link_Z3_tactic_apply_ex = &Z3_tactic_apply_ex;
Z3_apply_result ay_call_Z3_tactic_apply_ex(Z3_context ay_a0, Z3_tactic ay_a1, Z3_goal ay_a2, Z3_params ay_a3) {
    return Z3_tactic_apply_ex(ay_a0, ay_a1, ay_a2, ay_a3);
}

typedef Z3_apply_result (*ay_sig_Z3_tactic_apply)(Z3_context, Z3_tactic, Z3_goal);
ay_sig_Z3_tactic_apply const ay_link_Z3_tactic_apply = &Z3_tactic_apply;
Z3_apply_result ay_call_Z3_tactic_apply(Z3_context ay_a0, Z3_tactic ay_a1, Z3_goal ay_a2) {
    return Z3_tactic_apply(ay_a0, ay_a1, ay_a2);
}

typedef Z3_tactic (*ay_sig_Z3_tactic_cond)(Z3_context, Z3_probe, Z3_tactic, Z3_tactic);
ay_sig_Z3_tactic_cond const ay_link_Z3_tactic_cond = &Z3_tactic_cond;
Z3_tactic ay_call_Z3_tactic_cond(Z3_context ay_a0, Z3_probe ay_a1, Z3_tactic ay_a2, Z3_tactic ay_a3) {
    return Z3_tactic_cond(ay_a0, ay_a1, ay_a2, ay_a3);
}

typedef void (*ay_sig_Z3_tactic_dec_ref)(Z3_context, Z3_tactic);
ay_sig_Z3_tactic_dec_ref const ay_link_Z3_tactic_dec_ref = &Z3_tactic_dec_ref;
void ay_call_Z3_tactic_dec_ref(Z3_context ay_a0, Z3_tactic ay_a1) {
    Z3_tactic_dec_ref(ay_a0, ay_a1);
}

typedef Z3_tactic (*ay_sig_Z3_tactic_fail_if_not_decided)(Z3_context);
ay_sig_Z3_tactic_fail_if_not_decided const ay_link_Z3_tactic_fail_if_not_decided = &Z3_tactic_fail_if_not_decided;
Z3_tactic ay_call_Z3_tactic_fail_if_not_decided(Z3_context ay_a0) {
    return Z3_tactic_fail_if_not_decided(ay_a0);
}

typedef Z3_tactic (*ay_sig_Z3_tactic_fail_if)(Z3_context, Z3_probe);
ay_sig_Z3_tactic_fail_if const ay_link_Z3_tactic_fail_if = &Z3_tactic_fail_if;
Z3_tactic ay_call_Z3_tactic_fail_if(Z3_context ay_a0, Z3_probe ay_a1) {
    return Z3_tactic_fail_if(ay_a0, ay_a1);
}

typedef Z3_tactic (*ay_sig_Z3_tactic_fail)(Z3_context);
ay_sig_Z3_tactic_fail const ay_link_Z3_tactic_fail = &Z3_tactic_fail;
Z3_tactic ay_call_Z3_tactic_fail(Z3_context ay_a0) {
    return Z3_tactic_fail(ay_a0);
}

typedef Z3_string (*ay_sig_Z3_tactic_get_descr)(Z3_context, Z3_string);
ay_sig_Z3_tactic_get_descr const ay_link_Z3_tactic_get_descr = &Z3_tactic_get_descr;
Z3_string ay_call_Z3_tactic_get_descr(Z3_context ay_a0, Z3_string ay_a1) {
    return Z3_tactic_get_descr(ay_a0, ay_a1);
}

typedef Z3_string (*ay_sig_Z3_tactic_get_help)(Z3_context, Z3_tactic);
ay_sig_Z3_tactic_get_help const ay_link_Z3_tactic_get_help = &Z3_tactic_get_help;
Z3_string ay_call_Z3_tactic_get_help(Z3_context ay_a0, Z3_tactic ay_a1) {
    return Z3_tactic_get_help(ay_a0, ay_a1);
}

typedef Z3_param_descrs (*ay_sig_Z3_tactic_get_param_descrs)(Z3_context, Z3_tactic);
ay_sig_Z3_tactic_get_param_descrs const ay_link_Z3_tactic_get_param_descrs = &Z3_tactic_get_param_descrs;
Z3_param_descrs ay_call_Z3_tactic_get_param_descrs(Z3_context ay_a0, Z3_tactic ay_a1) {
    return Z3_tactic_get_param_descrs(ay_a0, ay_a1);
}

typedef void (*ay_sig_Z3_tactic_inc_ref)(Z3_context, Z3_tactic);
ay_sig_Z3_tactic_inc_ref const ay_link_Z3_tactic_inc_ref = &Z3_tactic_inc_ref;
void ay_call_Z3_tactic_inc_ref(Z3_context ay_a0, Z3_tactic ay_a1) {
    Z3_tactic_inc_ref(ay_a0, ay_a1);
}

typedef Z3_tactic (*ay_sig_Z3_tactic_or_else)(Z3_context, Z3_tactic, Z3_tactic);
ay_sig_Z3_tactic_or_else const ay_link_Z3_tactic_or_else = &Z3_tactic_or_else;
Z3_tactic ay_call_Z3_tactic_or_else(Z3_context ay_a0, Z3_tactic ay_a1, Z3_tactic ay_a2) {
    return Z3_tactic_or_else(ay_a0, ay_a1, ay_a2);
}

typedef Z3_tactic (*ay_sig_Z3_tactic_par_and_then)(Z3_context, Z3_tactic, Z3_tactic);
ay_sig_Z3_tactic_par_and_then const ay_link_Z3_tactic_par_and_then = &Z3_tactic_par_and_then;
Z3_tactic ay_call_Z3_tactic_par_and_then(Z3_context ay_a0, Z3_tactic ay_a1, Z3_tactic ay_a2) {
    return Z3_tactic_par_and_then(ay_a0, ay_a1, ay_a2);
}

typedef Z3_tactic (*ay_sig_Z3_tactic_par_or)(Z3_context, unsigned int, const Z3_tactic *);
ay_sig_Z3_tactic_par_or const ay_link_Z3_tactic_par_or = &Z3_tactic_par_or;
Z3_tactic ay_call_Z3_tactic_par_or(Z3_context ay_a0, unsigned int ay_a1, const Z3_tactic * ay_a2) {
    return Z3_tactic_par_or(ay_a0, ay_a1, ay_a2);
}

typedef Z3_tactic (*ay_sig_Z3_tactic_repeat)(Z3_context, Z3_tactic, unsigned int);
ay_sig_Z3_tactic_repeat const ay_link_Z3_tactic_repeat = &Z3_tactic_repeat;
Z3_tactic ay_call_Z3_tactic_repeat(Z3_context ay_a0, Z3_tactic ay_a1, unsigned int ay_a2) {
    return Z3_tactic_repeat(ay_a0, ay_a1, ay_a2);
}

typedef Z3_tactic (*ay_sig_Z3_tactic_skip)(Z3_context);
ay_sig_Z3_tactic_skip const ay_link_Z3_tactic_skip = &Z3_tactic_skip;
Z3_tactic ay_call_Z3_tactic_skip(Z3_context ay_a0) {
    return Z3_tactic_skip(ay_a0);
}

typedef Z3_tactic (*ay_sig_Z3_tactic_try_for)(Z3_context, Z3_tactic, unsigned int);
ay_sig_Z3_tactic_try_for const ay_link_Z3_tactic_try_for = &Z3_tactic_try_for;
Z3_tactic ay_call_Z3_tactic_try_for(Z3_context ay_a0, Z3_tactic ay_a1, unsigned int ay_a2) {
    return Z3_tactic_try_for(ay_a0, ay_a1, ay_a2);
}

typedef Z3_tactic (*ay_sig_Z3_tactic_using_params)(Z3_context, Z3_tactic, Z3_params);
ay_sig_Z3_tactic_using_params const ay_link_Z3_tactic_using_params = &Z3_tactic_using_params;
Z3_tactic ay_call_Z3_tactic_using_params(Z3_context ay_a0, Z3_tactic ay_a1, Z3_params ay_a2) {
    return Z3_tactic_using_params(ay_a0, ay_a1, ay_a2);
}

typedef Z3_tactic (*ay_sig_Z3_tactic_when)(Z3_context, Z3_probe, Z3_tactic);
ay_sig_Z3_tactic_when const ay_link_Z3_tactic_when = &Z3_tactic_when;
Z3_tactic ay_call_Z3_tactic_when(Z3_context ay_a0, Z3_probe ay_a1, Z3_tactic ay_a2) {
    return Z3_tactic_when(ay_a0, ay_a1, ay_a2);
}

typedef Z3_app (*ay_sig_Z3_to_app)(Z3_context, Z3_ast);
ay_sig_Z3_to_app const ay_link_Z3_to_app = &Z3_to_app;
Z3_app ay_call_Z3_to_app(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_to_app(ay_a0, ay_a1);
}

typedef Z3_func_decl (*ay_sig_Z3_to_func_decl)(Z3_context, Z3_ast);
ay_sig_Z3_to_func_decl const ay_link_Z3_to_func_decl = &Z3_to_func_decl;
Z3_func_decl ay_call_Z3_to_func_decl(Z3_context ay_a0, Z3_ast ay_a1) {
    return Z3_to_func_decl(ay_a0, ay_a1);
}

typedef void (*ay_sig_Z3_toggle_warning_messages)(bool);
ay_sig_Z3_toggle_warning_messages const ay_link_Z3_toggle_warning_messages = &Z3_toggle_warning_messages;
void ay_call_Z3_toggle_warning_messages(bool ay_a0) {
    Z3_toggle_warning_messages(ay_a0);
}

typedef Z3_ast (*ay_sig_Z3_translate)(Z3_context, Z3_ast, Z3_context);
ay_sig_Z3_translate const ay_link_Z3_translate = &Z3_translate;
Z3_ast ay_call_Z3_translate(Z3_context ay_a0, Z3_ast ay_a1, Z3_context ay_a2) {
    return Z3_translate(ay_a0, ay_a1, ay_a2);
}

typedef void (*ay_sig_Z3_update_param_value)(Z3_context, Z3_string, Z3_string);
ay_sig_Z3_update_param_value const ay_link_Z3_update_param_value = &Z3_update_param_value;
void ay_call_Z3_update_param_value(Z3_context ay_a0, Z3_string ay_a1, Z3_string ay_a2) {
    Z3_update_param_value(ay_a0, ay_a1, ay_a2);
}

typedef Z3_ast (*ay_sig_Z3_update_term)(Z3_context, Z3_ast, unsigned int, const Z3_ast *);
ay_sig_Z3_update_term const ay_link_Z3_update_term = &Z3_update_term;
Z3_ast ay_call_Z3_update_term(Z3_context ay_a0, Z3_ast ay_a1, unsigned int ay_a2, const Z3_ast * ay_a3) {
    return Z3_update_term(ay_a0, ay_a1, ay_a2, ay_a3);
}

int main(void) {
    unsigned present = 0;
    present += ay_link_Z3_add_const_interp != 0;
    present += ay_link_Z3_add_func_interp != 0;
    present += ay_link_Z3_add_rec_def != 0;
    present += ay_link_Z3_algebraic_add != 0;
    present += ay_link_Z3_algebraic_div != 0;
    present += ay_link_Z3_algebraic_eq != 0;
    present += ay_link_Z3_algebraic_eval != 0;
    present += ay_link_Z3_algebraic_get_i != 0;
    present += ay_link_Z3_algebraic_get_poly != 0;
    present += ay_link_Z3_algebraic_ge != 0;
    present += ay_link_Z3_algebraic_gt != 0;
    present += ay_link_Z3_algebraic_is_neg != 0;
    present += ay_link_Z3_algebraic_is_pos != 0;
    present += ay_link_Z3_algebraic_is_value != 0;
    present += ay_link_Z3_algebraic_is_zero != 0;
    present += ay_link_Z3_algebraic_le != 0;
    present += ay_link_Z3_algebraic_lt != 0;
    present += ay_link_Z3_algebraic_mul != 0;
    present += ay_link_Z3_algebraic_neq != 0;
    present += ay_link_Z3_algebraic_power != 0;
    present += ay_link_Z3_algebraic_roots != 0;
    present += ay_link_Z3_algebraic_root != 0;
    present += ay_link_Z3_algebraic_sign != 0;
    present += ay_link_Z3_algebraic_sub != 0;
    present += ay_link_Z3_app_to_ast != 0;
    present += ay_link_Z3_append_log != 0;
    present += ay_link_Z3_apply_result_dec_ref != 0;
    present += ay_link_Z3_apply_result_get_num_subgoals != 0;
    present += ay_link_Z3_apply_result_get_subgoal != 0;
    present += ay_link_Z3_apply_result_inc_ref != 0;
    present += ay_link_Z3_apply_result_to_string != 0;
    present += ay_link_Z3_ast_map_contains != 0;
    present += ay_link_Z3_ast_map_dec_ref != 0;
    present += ay_link_Z3_ast_map_erase != 0;
    present += ay_link_Z3_ast_map_find != 0;
    present += ay_link_Z3_ast_map_inc_ref != 0;
    present += ay_link_Z3_ast_map_insert != 0;
    present += ay_link_Z3_ast_map_keys != 0;
    present += ay_link_Z3_ast_map_reset != 0;
    present += ay_link_Z3_ast_map_size != 0;
    present += ay_link_Z3_ast_map_to_string != 0;
    present += ay_link_Z3_ast_to_string != 0;
    present += ay_link_Z3_ast_vector_dec_ref != 0;
    present += ay_link_Z3_ast_vector_get != 0;
    present += ay_link_Z3_ast_vector_inc_ref != 0;
    present += ay_link_Z3_ast_vector_push != 0;
    present += ay_link_Z3_ast_vector_resize != 0;
    present += ay_link_Z3_ast_vector_set != 0;
    present += ay_link_Z3_ast_vector_size != 0;
    present += ay_link_Z3_ast_vector_to_string != 0;
    present += ay_link_Z3_ast_vector_translate != 0;
    present += ay_link_Z3_benchmark_to_smtlib_string != 0;
    present += ay_link_Z3_close_log != 0;
    present += ay_link_Z3_constructor_num_fields != 0;
    present += ay_link_Z3_datatype_update_field != 0;
    present += ay_link_Z3_dec_ref != 0;
    present += ay_link_Z3_del_config != 0;
    present += ay_link_Z3_del_constructor_list != 0;
    present += ay_link_Z3_del_constructor != 0;
    present += ay_link_Z3_del_context != 0;
    present += ay_link_Z3_disable_trace != 0;
    present += ay_link_Z3_enable_concurrent_dec_ref != 0;
    present += ay_link_Z3_enable_trace != 0;
    present += ay_link_Z3_eval_smtlib2_string != 0;
    present += ay_link_Z3_finalize_memory != 0;
    present += ay_link_Z3_fixedpoint_add_callback != 0;
    present += ay_link_Z3_fixedpoint_add_constraint != 0;
    present += ay_link_Z3_fixedpoint_add_cover != 0;
    present += ay_link_Z3_fixedpoint_add_fact != 0;
    present += ay_link_Z3_fixedpoint_add_invariant != 0;
    present += ay_link_Z3_fixedpoint_add_rule != 0;
    present += ay_link_Z3_fixedpoint_assert != 0;
    present += ay_link_Z3_fixedpoint_dec_ref != 0;
    present += ay_link_Z3_fixedpoint_from_file != 0;
    present += ay_link_Z3_fixedpoint_from_string != 0;
    present += ay_link_Z3_fixedpoint_get_answer != 0;
    present += ay_link_Z3_fixedpoint_get_assertions != 0;
    present += ay_link_Z3_fixedpoint_get_cover_delta != 0;
    present += ay_link_Z3_fixedpoint_get_ground_sat_answer != 0;
    present += ay_link_Z3_fixedpoint_get_help != 0;
    present += ay_link_Z3_fixedpoint_get_num_levels != 0;
    present += ay_link_Z3_fixedpoint_get_param_descrs != 0;
    present += ay_link_Z3_fixedpoint_get_reachable != 0;
    present += ay_link_Z3_fixedpoint_get_reason_unknown != 0;
    present += ay_link_Z3_fixedpoint_get_rule_names_along_trace != 0;
    present += ay_link_Z3_fixedpoint_get_rules_along_trace != 0;
    present += ay_link_Z3_fixedpoint_get_rules != 0;
    present += ay_link_Z3_fixedpoint_get_statistics != 0;
    present += ay_link_Z3_fixedpoint_inc_ref != 0;
    present += ay_link_Z3_fixedpoint_init != 0;
    present += ay_link_Z3_fixedpoint_query_from_lvl != 0;
    present += ay_link_Z3_fixedpoint_query_relations != 0;
    present += ay_link_Z3_fixedpoint_query != 0;
    present += ay_link_Z3_fixedpoint_register_relation != 0;
    present += ay_link_Z3_fixedpoint_set_params != 0;
    present += ay_link_Z3_fixedpoint_set_predicate_representation != 0;
    present += ay_link_Z3_fixedpoint_set_reduce_app_callback != 0;
    present += ay_link_Z3_fixedpoint_set_reduce_assign_callback != 0;
    present += ay_link_Z3_fixedpoint_to_string != 0;
    present += ay_link_Z3_fixedpoint_update_rule != 0;
    present += ay_link_Z3_fpa_get_ebits != 0;
    present += ay_link_Z3_fpa_get_numeral_exponent_bv != 0;
    present += ay_link_Z3_fpa_get_numeral_exponent_int64 != 0;
    present += ay_link_Z3_fpa_get_numeral_exponent_string != 0;
    present += ay_link_Z3_fpa_get_numeral_sign_bv != 0;
    present += ay_link_Z3_fpa_get_numeral_significand_bv != 0;
    present += ay_link_Z3_fpa_get_numeral_significand_string != 0;
    present += ay_link_Z3_fpa_get_numeral_significand_uint64 != 0;
    present += ay_link_Z3_fpa_get_numeral_sign != 0;
    present += ay_link_Z3_fpa_get_sbits != 0;
    present += ay_link_Z3_fpa_is_numeral_inf != 0;
    present += ay_link_Z3_fpa_is_numeral_nan != 0;
    present += ay_link_Z3_fpa_is_numeral_negative != 0;
    present += ay_link_Z3_fpa_is_numeral_normal != 0;
    present += ay_link_Z3_fpa_is_numeral_positive != 0;
    present += ay_link_Z3_fpa_is_numeral_subnormal != 0;
    present += ay_link_Z3_fpa_is_numeral_zero != 0;
    present += ay_link_Z3_fpa_is_numeral != 0;
    present += ay_link_Z3_func_decl_to_ast != 0;
    present += ay_link_Z3_func_decl_to_string != 0;
    present += ay_link_Z3_func_entry_dec_ref != 0;
    present += ay_link_Z3_func_entry_get_arg != 0;
    present += ay_link_Z3_func_entry_get_num_args != 0;
    present += ay_link_Z3_func_entry_get_value != 0;
    present += ay_link_Z3_func_entry_inc_ref != 0;
    present += ay_link_Z3_func_interp_add_entry != 0;
    present += ay_link_Z3_func_interp_dec_ref != 0;
    present += ay_link_Z3_func_interp_get_arity != 0;
    present += ay_link_Z3_func_interp_get_else != 0;
    present += ay_link_Z3_func_interp_get_entry != 0;
    present += ay_link_Z3_func_interp_get_num_entries != 0;
    present += ay_link_Z3_func_interp_inc_ref != 0;
    present += ay_link_Z3_func_interp_set_else != 0;
    present += ay_link_Z3_get_algebraic_number_lower != 0;
    present += ay_link_Z3_get_algebraic_number_upper != 0;
    present += ay_link_Z3_get_app_arg != 0;
    present += ay_link_Z3_get_app_decl != 0;
    present += ay_link_Z3_get_app_num_args != 0;
    present += ay_link_Z3_get_arity != 0;
    present += ay_link_Z3_get_array_arity != 0;
    present += ay_link_Z3_get_array_sort_domain_n != 0;
    present += ay_link_Z3_get_array_sort_domain != 0;
    present += ay_link_Z3_get_array_sort_range != 0;
    present += ay_link_Z3_get_as_array_func_decl != 0;
    present += ay_link_Z3_get_ast_hash != 0;
    present += ay_link_Z3_get_ast_id != 0;
    present += ay_link_Z3_get_ast_kind != 0;
    present += ay_link_Z3_get_bool_value != 0;
    present += ay_link_Z3_get_bv_sort_size != 0;
    present += ay_link_Z3_get_datatype_sort_constructor_accessor != 0;
    present += ay_link_Z3_get_datatype_sort_constructor != 0;
    present += ay_link_Z3_get_datatype_sort_num_constructors != 0;
    present += ay_link_Z3_get_datatype_sort_recognizer != 0;
    present += ay_link_Z3_get_decl_ast_parameter != 0;
    present += ay_link_Z3_get_decl_double_parameter != 0;
    present += ay_link_Z3_get_decl_func_decl_parameter != 0;
    present += ay_link_Z3_get_decl_int_parameter != 0;
    present += ay_link_Z3_get_decl_kind != 0;
    present += ay_link_Z3_get_decl_name != 0;
    present += ay_link_Z3_get_decl_num_parameters != 0;
    present += ay_link_Z3_get_decl_parameter_kind != 0;
    present += ay_link_Z3_get_decl_rational_parameter != 0;
    present += ay_link_Z3_get_decl_sort_parameter != 0;
    present += ay_link_Z3_get_decl_symbol_parameter != 0;
    present += ay_link_Z3_get_denominator != 0;
    present += ay_link_Z3_get_depth != 0;
    present += ay_link_Z3_get_domain_size != 0;
    present += ay_link_Z3_get_domain != 0;
    present += ay_link_Z3_get_error_code != 0;
    present += ay_link_Z3_get_error_msg != 0;
    present += ay_link_Z3_get_estimated_alloc_size != 0;
    present += ay_link_Z3_get_finite_domain_sort_size != 0;
    present += ay_link_Z3_get_finite_set_sort_basis != 0;
    present += ay_link_Z3_get_full_version != 0;
    present += ay_link_Z3_get_func_decl_id != 0;
    present += ay_link_Z3_get_global_param_descrs != 0;
    present += ay_link_Z3_get_implied_equalities != 0;
    present += ay_link_Z3_get_index_value != 0;
    present += ay_link_Z3_get_lstring != 0;
    present += ay_link_Z3_get_num_probes != 0;
    present += ay_link_Z3_get_num_simplifiers != 0;
    present += ay_link_Z3_get_num_tactics != 0;
    present += ay_link_Z3_get_numeral_binary_string != 0;
    present += ay_link_Z3_get_numeral_decimal_string != 0;
    present += ay_link_Z3_get_numeral_double != 0;
    present += ay_link_Z3_get_numeral_int64 != 0;
    present += ay_link_Z3_get_numeral_int != 0;
    present += ay_link_Z3_get_numeral_rational_int64 != 0;
    present += ay_link_Z3_get_numeral_small != 0;
    present += ay_link_Z3_get_numeral_string != 0;
    present += ay_link_Z3_get_numeral_uint64 != 0;
    present += ay_link_Z3_get_numeral_uint != 0;
    present += ay_link_Z3_get_numerator != 0;
    present += ay_link_Z3_get_pattern_num_terms != 0;
    present += ay_link_Z3_get_pattern != 0;
    present += ay_link_Z3_get_probe_name != 0;
    present += ay_link_Z3_get_quantifier_body != 0;
    present += ay_link_Z3_get_quantifier_bound_name != 0;
    present += ay_link_Z3_get_quantifier_bound_sort != 0;
    present += ay_link_Z3_get_quantifier_id != 0;
    present += ay_link_Z3_get_quantifier_no_pattern_ast != 0;
    present += ay_link_Z3_get_quantifier_num_bound != 0;
    present += ay_link_Z3_get_quantifier_num_no_patterns != 0;
    present += ay_link_Z3_get_quantifier_num_patterns != 0;
    present += ay_link_Z3_get_quantifier_pattern_ast != 0;
    present += ay_link_Z3_get_quantifier_skolem_id != 0;
    present += ay_link_Z3_get_quantifier_weight != 0;
    present += ay_link_Z3_get_range != 0;
    present += ay_link_Z3_get_re_sort_basis != 0;
    present += ay_link_Z3_get_relation_arity != 0;
    present += ay_link_Z3_get_relation_column != 0;
    present += ay_link_Z3_get_seq_sort_basis != 0;
    present += ay_link_Z3_get_simplifier_name != 0;
    present += ay_link_Z3_get_sort_id != 0;
    present += ay_link_Z3_get_sort_kind != 0;
    present += ay_link_Z3_get_sort_name != 0;
    present += ay_link_Z3_get_sort != 0;
    present += ay_link_Z3_get_string_contents != 0;
    present += ay_link_Z3_get_string_length != 0;
    present += ay_link_Z3_get_string != 0;
    present += ay_link_Z3_get_symbol_int != 0;
    present += ay_link_Z3_get_symbol_kind != 0;
    present += ay_link_Z3_get_symbol_string != 0;
    present += ay_link_Z3_get_tactic_name != 0;
    present += ay_link_Z3_get_tuple_sort_field_decl != 0;
    present += ay_link_Z3_get_tuple_sort_mk_decl != 0;
    present += ay_link_Z3_get_tuple_sort_num_fields != 0;
    present += ay_link_Z3_get_version != 0;
    present += ay_link_Z3_global_param_get != 0;
    present += ay_link_Z3_global_param_reset_all != 0;
    present += ay_link_Z3_global_param_set != 0;
    present += ay_link_Z3_goal_assert != 0;
    present += ay_link_Z3_goal_convert_model != 0;
    present += ay_link_Z3_goal_dec_ref != 0;
    present += ay_link_Z3_goal_depth != 0;
    present += ay_link_Z3_goal_formula != 0;
    present += ay_link_Z3_goal_inc_ref != 0;
    present += ay_link_Z3_goal_inconsistent != 0;
    present += ay_link_Z3_goal_is_decided_sat != 0;
    present += ay_link_Z3_goal_is_decided_unsat != 0;
    present += ay_link_Z3_goal_num_exprs != 0;
    present += ay_link_Z3_goal_precision != 0;
    present += ay_link_Z3_goal_reset != 0;
    present += ay_link_Z3_goal_size != 0;
    present += ay_link_Z3_goal_to_dimacs_string != 0;
    present += ay_link_Z3_goal_to_string != 0;
    present += ay_link_Z3_goal_translate != 0;
    present += ay_link_Z3_inc_ref != 0;
    present += ay_link_Z3_interrupt != 0;
    present += ay_link_Z3_is_algebraic_number != 0;
    present += ay_link_Z3_is_app != 0;
    present += ay_link_Z3_is_as_array != 0;
    present += ay_link_Z3_is_char_sort != 0;
    present += ay_link_Z3_is_eq_ast != 0;
    present += ay_link_Z3_is_eq_func_decl != 0;
    present += ay_link_Z3_is_eq_sort != 0;
    present += ay_link_Z3_is_finite_set_sort != 0;
    present += ay_link_Z3_is_ground != 0;
    present += ay_link_Z3_is_lambda != 0;
    present += ay_link_Z3_is_numeral_ast != 0;
    present += ay_link_Z3_is_quantifier_exists != 0;
    present += ay_link_Z3_is_quantifier_forall != 0;
    present += ay_link_Z3_is_re_sort != 0;
    present += ay_link_Z3_is_recursive_datatype_sort != 0;
    present += ay_link_Z3_is_seq_sort != 0;
    present += ay_link_Z3_is_string_sort != 0;
    present += ay_link_Z3_is_string != 0;
    present += ay_link_Z3_is_well_sorted != 0;
    present += ay_link_Z3_mk_abs != 0;
    present += ay_link_Z3_mk_add != 0;
    present += ay_link_Z3_mk_and != 0;
    present += ay_link_Z3_mk_app != 0;
    present += ay_link_Z3_mk_array_default != 0;
    present += ay_link_Z3_mk_array_ext != 0;
    present += ay_link_Z3_mk_array_sort_n != 0;
    present += ay_link_Z3_mk_array_sort != 0;
    present += ay_link_Z3_mk_as_array != 0;
    present += ay_link_Z3_mk_ast_map != 0;
    present += ay_link_Z3_mk_ast_vector != 0;
    present += ay_link_Z3_mk_atleast != 0;
    present += ay_link_Z3_mk_atmost != 0;
    present += ay_link_Z3_mk_bit2bool != 0;
    present += ay_link_Z3_mk_bool_sort != 0;
    present += ay_link_Z3_mk_bound != 0;
    present += ay_link_Z3_mk_bv2int != 0;
    present += ay_link_Z3_mk_bv_numeral != 0;
    present += ay_link_Z3_mk_bv_sort != 0;
    present += ay_link_Z3_mk_bvadd_no_overflow != 0;
    present += ay_link_Z3_mk_bvadd_no_underflow != 0;
    present += ay_link_Z3_mk_bvadd != 0;
    present += ay_link_Z3_mk_bvand != 0;
    present += ay_link_Z3_mk_bvashr != 0;
    present += ay_link_Z3_mk_bvlshr != 0;
    present += ay_link_Z3_mk_bvmul_no_overflow != 0;
    present += ay_link_Z3_mk_bvmul_no_underflow != 0;
    present += ay_link_Z3_mk_bvmul != 0;
    present += ay_link_Z3_mk_bvnand != 0;
    present += ay_link_Z3_mk_bvneg_no_overflow != 0;
    present += ay_link_Z3_mk_bvneg != 0;
    present += ay_link_Z3_mk_bvnor != 0;
    present += ay_link_Z3_mk_bvnot != 0;
    present += ay_link_Z3_mk_bvor != 0;
    present += ay_link_Z3_mk_bvredand != 0;
    present += ay_link_Z3_mk_bvredor != 0;
    present += ay_link_Z3_mk_bvsdiv_no_overflow != 0;
    present += ay_link_Z3_mk_bvsdiv != 0;
    present += ay_link_Z3_mk_bvsge != 0;
    present += ay_link_Z3_mk_bvsgt != 0;
    present += ay_link_Z3_mk_bvshl != 0;
    present += ay_link_Z3_mk_bvsle != 0;
    present += ay_link_Z3_mk_bvslt != 0;
    present += ay_link_Z3_mk_bvsmod != 0;
    present += ay_link_Z3_mk_bvsrem != 0;
    present += ay_link_Z3_mk_bvsub_no_overflow != 0;
    present += ay_link_Z3_mk_bvsub_no_underflow != 0;
    present += ay_link_Z3_mk_bvsub != 0;
    present += ay_link_Z3_mk_bvudiv != 0;
    present += ay_link_Z3_mk_bvuge != 0;
    present += ay_link_Z3_mk_bvugt != 0;
    present += ay_link_Z3_mk_bvule != 0;
    present += ay_link_Z3_mk_bvult != 0;
    present += ay_link_Z3_mk_bvurem != 0;
    present += ay_link_Z3_mk_bvxnor != 0;
    present += ay_link_Z3_mk_bvxor != 0;
    present += ay_link_Z3_mk_char_from_bv != 0;
    present += ay_link_Z3_mk_char_is_digit != 0;
    present += ay_link_Z3_mk_char_le != 0;
    present += ay_link_Z3_mk_char_sort != 0;
    present += ay_link_Z3_mk_char_to_bv != 0;
    present += ay_link_Z3_mk_char_to_int != 0;
    present += ay_link_Z3_mk_char != 0;
    present += ay_link_Z3_mk_concat != 0;
    present += ay_link_Z3_mk_config != 0;
    present += ay_link_Z3_mk_const_array != 0;
    present += ay_link_Z3_mk_constructor_list != 0;
    present += ay_link_Z3_mk_constructor != 0;
    present += ay_link_Z3_mk_const != 0;
    present += ay_link_Z3_mk_context_rc != 0;
    present += ay_link_Z3_mk_context != 0;
    present += ay_link_Z3_mk_datatype_sort != 0;
    present += ay_link_Z3_mk_datatypes != 0;
    present += ay_link_Z3_mk_datatype != 0;
    present += ay_link_Z3_mk_distinct != 0;
    present += ay_link_Z3_mk_divides != 0;
    present += ay_link_Z3_mk_div != 0;
    present += ay_link_Z3_mk_empty_set != 0;
    present += ay_link_Z3_mk_enumeration_sort != 0;
    present += ay_link_Z3_mk_eq != 0;
    present += ay_link_Z3_mk_exists_const != 0;
    present += ay_link_Z3_mk_exists != 0;
    present += ay_link_Z3_mk_ext_rotate_left != 0;
    present += ay_link_Z3_mk_ext_rotate_right != 0;
    present += ay_link_Z3_mk_extract != 0;
    present += ay_link_Z3_mk_false != 0;
    present += ay_link_Z3_mk_finite_domain_sort != 0;
    present += ay_link_Z3_mk_finite_set_difference != 0;
    present += ay_link_Z3_mk_finite_set_empty != 0;
    present += ay_link_Z3_mk_finite_set_filter != 0;
    present += ay_link_Z3_mk_finite_set_intersect != 0;
    present += ay_link_Z3_mk_finite_set_map != 0;
    present += ay_link_Z3_mk_finite_set_member != 0;
    present += ay_link_Z3_mk_finite_set_range != 0;
    present += ay_link_Z3_mk_finite_set_singleton != 0;
    present += ay_link_Z3_mk_finite_set_size != 0;
    present += ay_link_Z3_mk_finite_set_sort != 0;
    present += ay_link_Z3_mk_finite_set_subset != 0;
    present += ay_link_Z3_mk_finite_set_union != 0;
    present += ay_link_Z3_mk_fixedpoint != 0;
    present += ay_link_Z3_mk_forall_const != 0;
    present += ay_link_Z3_mk_forall != 0;
    present += ay_link_Z3_mk_fpa_abs != 0;
    present += ay_link_Z3_mk_fpa_add != 0;
    present += ay_link_Z3_mk_fpa_div != 0;
    present += ay_link_Z3_mk_fpa_eq != 0;
    present += ay_link_Z3_mk_fpa_fma != 0;
    present += ay_link_Z3_mk_fpa_fp != 0;
    present += ay_link_Z3_mk_fpa_geq != 0;
    present += ay_link_Z3_mk_fpa_gt != 0;
    present += ay_link_Z3_mk_fpa_inf != 0;
    present += ay_link_Z3_mk_fpa_is_infinite != 0;
    present += ay_link_Z3_mk_fpa_is_nan != 0;
    present += ay_link_Z3_mk_fpa_is_negative != 0;
    present += ay_link_Z3_mk_fpa_is_normal != 0;
    present += ay_link_Z3_mk_fpa_is_positive != 0;
    present += ay_link_Z3_mk_fpa_is_subnormal != 0;
    present += ay_link_Z3_mk_fpa_is_zero != 0;
    present += ay_link_Z3_mk_fpa_leq != 0;
    present += ay_link_Z3_mk_fpa_lt != 0;
    present += ay_link_Z3_mk_fpa_max != 0;
    present += ay_link_Z3_mk_fpa_min != 0;
    present += ay_link_Z3_mk_fpa_mul != 0;
    present += ay_link_Z3_mk_fpa_nan != 0;
    present += ay_link_Z3_mk_fpa_neg != 0;
    present += ay_link_Z3_mk_fpa_numeral_double != 0;
    present += ay_link_Z3_mk_fpa_numeral_float != 0;
    present += ay_link_Z3_mk_fpa_numeral_int64_uint64 != 0;
    present += ay_link_Z3_mk_fpa_numeral_int_uint != 0;
    present += ay_link_Z3_mk_fpa_numeral_int != 0;
    present += ay_link_Z3_mk_fpa_rem != 0;
    present += ay_link_Z3_mk_fpa_rna != 0;
    present += ay_link_Z3_mk_fpa_rne != 0;
    present += ay_link_Z3_mk_fpa_round_nearest_ties_to_away != 0;
    present += ay_link_Z3_mk_fpa_round_nearest_ties_to_even != 0;
    present += ay_link_Z3_mk_fpa_round_to_integral != 0;
    present += ay_link_Z3_mk_fpa_round_toward_negative != 0;
    present += ay_link_Z3_mk_fpa_round_toward_positive != 0;
    present += ay_link_Z3_mk_fpa_round_toward_zero != 0;
    present += ay_link_Z3_mk_fpa_rounding_mode_sort != 0;
    present += ay_link_Z3_mk_fpa_rtn != 0;
    present += ay_link_Z3_mk_fpa_rtp != 0;
    present += ay_link_Z3_mk_fpa_rtz != 0;
    present += ay_link_Z3_mk_fpa_sort_128 != 0;
    present += ay_link_Z3_mk_fpa_sort_16 != 0;
    present += ay_link_Z3_mk_fpa_sort_32 != 0;
    present += ay_link_Z3_mk_fpa_sort_64 != 0;
    present += ay_link_Z3_mk_fpa_sort_double != 0;
    present += ay_link_Z3_mk_fpa_sort_half != 0;
    present += ay_link_Z3_mk_fpa_sort_quadruple != 0;
    present += ay_link_Z3_mk_fpa_sort_single != 0;
    present += ay_link_Z3_mk_fpa_sort != 0;
    present += ay_link_Z3_mk_fpa_sqrt != 0;
    present += ay_link_Z3_mk_fpa_sub != 0;
    present += ay_link_Z3_mk_fpa_to_fp_bv != 0;
    present += ay_link_Z3_mk_fpa_to_fp_float != 0;
    present += ay_link_Z3_mk_fpa_to_fp_int_real != 0;
    present += ay_link_Z3_mk_fpa_to_fp_real != 0;
    present += ay_link_Z3_mk_fpa_to_fp_signed != 0;
    present += ay_link_Z3_mk_fpa_to_fp_unsigned != 0;
    present += ay_link_Z3_mk_fpa_to_ieee_bv != 0;
    present += ay_link_Z3_mk_fpa_to_real != 0;
    present += ay_link_Z3_mk_fpa_to_sbv != 0;
    present += ay_link_Z3_mk_fpa_to_ubv != 0;
    present += ay_link_Z3_mk_fpa_zero != 0;
    present += ay_link_Z3_mk_fresh_const != 0;
    present += ay_link_Z3_mk_fresh_func_decl != 0;
    present += ay_link_Z3_mk_full_set != 0;
    present += ay_link_Z3_mk_func_decl != 0;
    present += ay_link_Z3_mk_ge != 0;
    present += ay_link_Z3_mk_goal != 0;
    present += ay_link_Z3_mk_gt != 0;
    present += ay_link_Z3_mk_iff != 0;
    present += ay_link_Z3_mk_implies != 0;
    present += ay_link_Z3_mk_int2bv != 0;
    present += ay_link_Z3_mk_int2real != 0;
    present += ay_link_Z3_mk_int64 != 0;
    present += ay_link_Z3_mk_int_sort != 0;
    present += ay_link_Z3_mk_int_symbol != 0;
    present += ay_link_Z3_mk_int_to_str != 0;
    present += ay_link_Z3_mk_int != 0;
    present += ay_link_Z3_mk_is_int != 0;
    present += ay_link_Z3_mk_ite != 0;
    present += ay_link_Z3_mk_lambda_const != 0;
    present += ay_link_Z3_mk_lambda != 0;
    present += ay_link_Z3_mk_le != 0;
    present += ay_link_Z3_mk_linear_order != 0;
    present += ay_link_Z3_mk_list_sort != 0;
    present += ay_link_Z3_mk_lstring != 0;
    present += ay_link_Z3_mk_lt != 0;
    present += ay_link_Z3_mk_map != 0;
    present += ay_link_Z3_mk_model != 0;
    present += ay_link_Z3_mk_mod != 0;
    present += ay_link_Z3_mk_mul != 0;
    present += ay_link_Z3_mk_not != 0;
    present += ay_link_Z3_mk_numeral != 0;
    present += ay_link_Z3_mk_optimize != 0;
    present += ay_link_Z3_mk_or != 0;
    present += ay_link_Z3_mk_params != 0;
    present += ay_link_Z3_mk_parser_context != 0;
    present += ay_link_Z3_mk_partial_order != 0;
    present += ay_link_Z3_mk_pattern != 0;
    present += ay_link_Z3_mk_pbeq != 0;
    present += ay_link_Z3_mk_pbge != 0;
    present += ay_link_Z3_mk_pble != 0;
    present += ay_link_Z3_mk_piecewise_linear_order != 0;
    present += ay_link_Z3_mk_polymorphic_datatype != 0;
    present += ay_link_Z3_mk_power != 0;
    present += ay_link_Z3_mk_probe != 0;
    present += ay_link_Z3_mk_quantifier_const_ex != 0;
    present += ay_link_Z3_mk_quantifier_const != 0;
    present += ay_link_Z3_mk_quantifier_ex != 0;
    present += ay_link_Z3_mk_quantifier != 0;
    present += ay_link_Z3_mk_re_allchar != 0;
    present += ay_link_Z3_mk_re_complement != 0;
    present += ay_link_Z3_mk_re_concat != 0;
    present += ay_link_Z3_mk_re_diff != 0;
    present += ay_link_Z3_mk_re_empty != 0;
    present += ay_link_Z3_mk_re_full != 0;
    present += ay_link_Z3_mk_re_intersect != 0;
    present += ay_link_Z3_mk_re_loop != 0;
    present += ay_link_Z3_mk_re_option != 0;
    present += ay_link_Z3_mk_re_plus != 0;
    present += ay_link_Z3_mk_re_power != 0;
    present += ay_link_Z3_mk_re_range != 0;
    present += ay_link_Z3_mk_re_sort != 0;
    present += ay_link_Z3_mk_re_star != 0;
    present += ay_link_Z3_mk_re_union != 0;
    present += ay_link_Z3_mk_real2int != 0;
    present += ay_link_Z3_mk_real_int64 != 0;
    present += ay_link_Z3_mk_real_sort != 0;
    present += ay_link_Z3_mk_real != 0;
    present += ay_link_Z3_mk_rec_func_decl != 0;
    present += ay_link_Z3_mk_rem != 0;
    present += ay_link_Z3_mk_repeat != 0;
    present += ay_link_Z3_mk_rotate_left != 0;
    present += ay_link_Z3_mk_rotate_right != 0;
    present += ay_link_Z3_mk_sbv_to_str != 0;
    present += ay_link_Z3_mk_select_n != 0;
    present += ay_link_Z3_mk_select != 0;
    present += ay_link_Z3_mk_seq_at != 0;
    present += ay_link_Z3_mk_seq_concat != 0;
    present += ay_link_Z3_mk_seq_contains != 0;
    present += ay_link_Z3_mk_seq_empty != 0;
    present += ay_link_Z3_mk_seq_extract != 0;
    present += ay_link_Z3_mk_seq_foldli != 0;
    present += ay_link_Z3_mk_seq_foldl != 0;
    present += ay_link_Z3_mk_seq_in_re != 0;
    present += ay_link_Z3_mk_seq_index != 0;
    present += ay_link_Z3_mk_seq_last_index != 0;
    present += ay_link_Z3_mk_seq_length != 0;
    present += ay_link_Z3_mk_seq_mapi != 0;
    present += ay_link_Z3_mk_seq_map != 0;
    present += ay_link_Z3_mk_seq_nth != 0;
    present += ay_link_Z3_mk_seq_prefix != 0;
    present += ay_link_Z3_mk_seq_replace_all != 0;
    present += ay_link_Z3_mk_seq_replace_re_all != 0;
    present += ay_link_Z3_mk_seq_replace_re != 0;
    present += ay_link_Z3_mk_seq_replace != 0;
    present += ay_link_Z3_mk_seq_sort != 0;
    present += ay_link_Z3_mk_seq_suffix != 0;
    present += ay_link_Z3_mk_seq_to_re != 0;
    present += ay_link_Z3_mk_seq_unit != 0;
    present += ay_link_Z3_mk_set_add != 0;
    present += ay_link_Z3_mk_set_complement != 0;
    present += ay_link_Z3_mk_set_del != 0;
    present += ay_link_Z3_mk_set_difference != 0;
    present += ay_link_Z3_mk_set_intersect != 0;
    present += ay_link_Z3_mk_set_member != 0;
    present += ay_link_Z3_mk_set_sort != 0;
    present += ay_link_Z3_mk_set_subset != 0;
    present += ay_link_Z3_mk_set_union != 0;
    present += ay_link_Z3_mk_sign_ext != 0;
    present += ay_link_Z3_mk_simple_solver != 0;
    present += ay_link_Z3_mk_simplifier != 0;
    present += ay_link_Z3_mk_solver_for_logic != 0;
    present += ay_link_Z3_mk_solver_from_tactic != 0;
    present += ay_link_Z3_mk_solver != 0;
    present += ay_link_Z3_mk_store_n != 0;
    present += ay_link_Z3_mk_store != 0;
    present += ay_link_Z3_mk_str_le != 0;
    present += ay_link_Z3_mk_str_lt != 0;
    present += ay_link_Z3_mk_str_to_int != 0;
    present += ay_link_Z3_mk_string_from_code != 0;
    present += ay_link_Z3_mk_string_sort != 0;
    present += ay_link_Z3_mk_string_symbol != 0;
    present += ay_link_Z3_mk_string_to_code != 0;
    present += ay_link_Z3_mk_string != 0;
    present += ay_link_Z3_mk_sub != 0;
    present += ay_link_Z3_mk_tactic != 0;
    present += ay_link_Z3_mk_transitive_closure != 0;
    present += ay_link_Z3_mk_tree_order != 0;
    present += ay_link_Z3_mk_true != 0;
    present += ay_link_Z3_mk_tuple_sort != 0;
    present += ay_link_Z3_mk_type_variable != 0;
    present += ay_link_Z3_mk_u32string != 0;
    present += ay_link_Z3_mk_ubv_to_str != 0;
    present += ay_link_Z3_mk_unary_minus != 0;
    present += ay_link_Z3_mk_uninterpreted_sort != 0;
    present += ay_link_Z3_mk_unsigned_int64 != 0;
    present += ay_link_Z3_mk_unsigned_int != 0;
    present += ay_link_Z3_mk_xor != 0;
    present += ay_link_Z3_mk_zero_ext != 0;
    present += ay_link_Z3_model_dec_ref != 0;
    present += ay_link_Z3_model_eval != 0;
    present += ay_link_Z3_model_extrapolate != 0;
    present += ay_link_Z3_model_get_const_decl != 0;
    present += ay_link_Z3_model_get_const_interp != 0;
    present += ay_link_Z3_model_get_func_decl != 0;
    present += ay_link_Z3_model_get_func_interp != 0;
    present += ay_link_Z3_model_get_num_consts != 0;
    present += ay_link_Z3_model_get_num_funcs != 0;
    present += ay_link_Z3_model_get_num_sorts != 0;
    present += ay_link_Z3_model_get_sort_universe != 0;
    present += ay_link_Z3_model_get_sort != 0;
    present += ay_link_Z3_model_has_interp != 0;
    present += ay_link_Z3_model_inc_ref != 0;
    present += ay_link_Z3_model_to_string != 0;
    present += ay_link_Z3_model_translate != 0;
    present += ay_link_Z3_open_log != 0;
    present += ay_link_Z3_optimize_assert_and_track != 0;
    present += ay_link_Z3_optimize_assert_soft != 0;
    present += ay_link_Z3_optimize_assert != 0;
    present += ay_link_Z3_optimize_check != 0;
    present += ay_link_Z3_optimize_dec_ref != 0;
    present += ay_link_Z3_optimize_from_file != 0;
    present += ay_link_Z3_optimize_from_string != 0;
    present += ay_link_Z3_optimize_get_assertions != 0;
    present += ay_link_Z3_optimize_get_help != 0;
    present += ay_link_Z3_optimize_get_lower_as_vector != 0;
    present += ay_link_Z3_optimize_get_lower != 0;
    present += ay_link_Z3_optimize_get_model != 0;
    present += ay_link_Z3_optimize_get_objectives != 0;
    present += ay_link_Z3_optimize_get_param_descrs != 0;
    present += ay_link_Z3_optimize_get_reason_unknown != 0;
    present += ay_link_Z3_optimize_get_statistics != 0;
    present += ay_link_Z3_optimize_get_unsat_core != 0;
    present += ay_link_Z3_optimize_get_upper_as_vector != 0;
    present += ay_link_Z3_optimize_get_upper != 0;
    present += ay_link_Z3_optimize_inc_ref != 0;
    present += ay_link_Z3_optimize_maximize != 0;
    present += ay_link_Z3_optimize_minimize != 0;
    present += ay_link_Z3_optimize_pop != 0;
    present += ay_link_Z3_optimize_push != 0;
    present += ay_link_Z3_optimize_register_model_eh != 0;
    present += ay_link_Z3_optimize_set_initial_value != 0;
    present += ay_link_Z3_optimize_set_params != 0;
    present += ay_link_Z3_optimize_to_string != 0;
    present += ay_link_Z3_optimize_translate != 0;
    present += ay_link_Z3_param_descrs_dec_ref != 0;
    present += ay_link_Z3_param_descrs_get_documentation != 0;
    present += ay_link_Z3_param_descrs_get_kind != 0;
    present += ay_link_Z3_param_descrs_get_name != 0;
    present += ay_link_Z3_param_descrs_inc_ref != 0;
    present += ay_link_Z3_param_descrs_size != 0;
    present += ay_link_Z3_param_descrs_to_string != 0;
    present += ay_link_Z3_params_dec_ref != 0;
    present += ay_link_Z3_params_inc_ref != 0;
    present += ay_link_Z3_params_set_bool != 0;
    present += ay_link_Z3_params_set_double != 0;
    present += ay_link_Z3_params_set_symbol != 0;
    present += ay_link_Z3_params_set_uint != 0;
    present += ay_link_Z3_params_to_string != 0;
    present += ay_link_Z3_params_validate != 0;
    present += ay_link_Z3_parse_smtlib2_file != 0;
    present += ay_link_Z3_parse_smtlib2_string != 0;
    present += ay_link_Z3_parser_context_add_decl != 0;
    present += ay_link_Z3_parser_context_add_sort != 0;
    present += ay_link_Z3_parser_context_dec_ref != 0;
    present += ay_link_Z3_parser_context_from_string != 0;
    present += ay_link_Z3_parser_context_inc_ref != 0;
    present += ay_link_Z3_pattern_to_ast != 0;
    present += ay_link_Z3_pattern_to_string != 0;
    present += ay_link_Z3_polynomial_subresultants != 0;
    present += ay_link_Z3_probe_and != 0;
    present += ay_link_Z3_probe_apply != 0;
    present += ay_link_Z3_probe_const != 0;
    present += ay_link_Z3_probe_dec_ref != 0;
    present += ay_link_Z3_probe_eq != 0;
    present += ay_link_Z3_probe_get_descr != 0;
    present += ay_link_Z3_probe_ge != 0;
    present += ay_link_Z3_probe_gt != 0;
    present += ay_link_Z3_probe_inc_ref != 0;
    present += ay_link_Z3_probe_le != 0;
    present += ay_link_Z3_probe_lt != 0;
    present += ay_link_Z3_probe_not != 0;
    present += ay_link_Z3_probe_or != 0;
    present += ay_link_Z3_qe_lite != 0;
    present += ay_link_Z3_qe_model_project_skolem != 0;
    present += ay_link_Z3_qe_model_project_with_witness != 0;
    present += ay_link_Z3_qe_model_project != 0;
    present += ay_link_Z3_query_constructor != 0;
    present += ay_link_Z3_rcf_add != 0;
    present += ay_link_Z3_rcf_coefficient != 0;
    present += ay_link_Z3_rcf_del != 0;
    present += ay_link_Z3_rcf_div != 0;
    present += ay_link_Z3_rcf_eq != 0;
    present += ay_link_Z3_rcf_extension_index != 0;
    present += ay_link_Z3_rcf_get_numerator_denominator != 0;
    present += ay_link_Z3_rcf_ge != 0;
    present += ay_link_Z3_rcf_gt != 0;
    present += ay_link_Z3_rcf_infinitesimal_name != 0;
    present += ay_link_Z3_rcf_interval != 0;
    present += ay_link_Z3_rcf_inv != 0;
    present += ay_link_Z3_rcf_is_algebraic != 0;
    present += ay_link_Z3_rcf_is_infinitesimal != 0;
    present += ay_link_Z3_rcf_is_rational != 0;
    present += ay_link_Z3_rcf_is_transcendental != 0;
    present += ay_link_Z3_rcf_le != 0;
    present += ay_link_Z3_rcf_lt != 0;
    present += ay_link_Z3_rcf_mk_e != 0;
    present += ay_link_Z3_rcf_mk_infinitesimal != 0;
    present += ay_link_Z3_rcf_mk_pi != 0;
    present += ay_link_Z3_rcf_mk_rational != 0;
    present += ay_link_Z3_rcf_mk_roots != 0;
    present += ay_link_Z3_rcf_mk_small_int != 0;
    present += ay_link_Z3_rcf_mul != 0;
    present += ay_link_Z3_rcf_neg != 0;
    present += ay_link_Z3_rcf_neq != 0;
    present += ay_link_Z3_rcf_num_coefficients != 0;
    present += ay_link_Z3_rcf_num_sign_condition_coefficients != 0;
    present += ay_link_Z3_rcf_num_sign_conditions != 0;
    present += ay_link_Z3_rcf_num_to_decimal_string != 0;
    present += ay_link_Z3_rcf_num_to_string != 0;
    present += ay_link_Z3_rcf_power != 0;
    present += ay_link_Z3_rcf_sign_condition_coefficient != 0;
    present += ay_link_Z3_rcf_sign_condition_sign != 0;
    present += ay_link_Z3_rcf_sub != 0;
    present += ay_link_Z3_rcf_transcendental_name != 0;
    present += ay_link_Z3_reset_memory != 0;
    present += ay_link_Z3_set_ast_print_mode != 0;
    present += ay_link_Z3_set_error_handler != 0;
    present += ay_link_Z3_set_error != 0;
    present += ay_link_Z3_set_param_value != 0;
    present += ay_link_Z3_simplifier_and_then != 0;
    present += ay_link_Z3_simplifier_dec_ref != 0;
    present += ay_link_Z3_simplifier_get_descr != 0;
    present += ay_link_Z3_simplifier_get_help != 0;
    present += ay_link_Z3_simplifier_get_param_descrs != 0;
    present += ay_link_Z3_simplifier_inc_ref != 0;
    present += ay_link_Z3_simplifier_using_params != 0;
    present += ay_link_Z3_simplify_ex != 0;
    present += ay_link_Z3_simplify_get_help != 0;
    present += ay_link_Z3_simplify_get_param_descrs != 0;
    present += ay_link_Z3_simplify != 0;
    present += ay_link_Z3_solver_add_simplifier != 0;
    present += ay_link_Z3_solver_assert_and_track != 0;
    present += ay_link_Z3_solver_assert != 0;
    present += ay_link_Z3_solver_check_assumptions != 0;
    present += ay_link_Z3_solver_check != 0;
    present += ay_link_Z3_solver_congruence_explain != 0;
    present += ay_link_Z3_solver_congruence_next != 0;
    present += ay_link_Z3_solver_congruence_root != 0;
    present += ay_link_Z3_solver_cube != 0;
    present += ay_link_Z3_solver_dec_ref != 0;
    present += ay_link_Z3_solver_from_file != 0;
    present += ay_link_Z3_solver_from_string != 0;
    present += ay_link_Z3_solver_get_assertions != 0;
    present += ay_link_Z3_solver_get_consequences != 0;
    present += ay_link_Z3_solver_get_help != 0;
    present += ay_link_Z3_solver_get_levels != 0;
    present += ay_link_Z3_solver_get_model != 0;
    present += ay_link_Z3_solver_get_non_units != 0;
    present += ay_link_Z3_solver_get_num_scopes != 0;
    present += ay_link_Z3_solver_get_param_descrs != 0;
    present += ay_link_Z3_solver_get_proof != 0;
    present += ay_link_Z3_solver_get_reason_unknown != 0;
    present += ay_link_Z3_solver_get_statistics != 0;
    present += ay_link_Z3_solver_get_trail != 0;
    present += ay_link_Z3_solver_get_units != 0;
    present += ay_link_Z3_solver_get_unsat_core != 0;
    present += ay_link_Z3_solver_import_model_converter != 0;
    present += ay_link_Z3_solver_inc_ref != 0;
    present += ay_link_Z3_solver_interrupt != 0;
    present += ay_link_Z3_solver_next_split != 0;
    present += ay_link_Z3_solver_pop != 0;
    present += ay_link_Z3_solver_propagate_consequence != 0;
    present += ay_link_Z3_solver_propagate_created != 0;
    present += ay_link_Z3_solver_propagate_decide != 0;
    present += ay_link_Z3_solver_propagate_declare != 0;
    present += ay_link_Z3_solver_propagate_diseq != 0;
    present += ay_link_Z3_solver_propagate_eq != 0;
    present += ay_link_Z3_solver_propagate_final != 0;
    present += ay_link_Z3_solver_propagate_fixed != 0;
    present += ay_link_Z3_solver_propagate_init != 0;
    present += ay_link_Z3_solver_propagate_on_binding != 0;
    present += ay_link_Z3_solver_propagate_register_cb != 0;
    present += ay_link_Z3_solver_propagate_register != 0;
    present += ay_link_Z3_solver_push != 0;
    present += ay_link_Z3_solver_register_on_clause != 0;
    present += ay_link_Z3_solver_reset != 0;
    present += ay_link_Z3_solver_set_initial_value != 0;
    present += ay_link_Z3_solver_set_params != 0;
    present += ay_link_Z3_solver_solve_for != 0;
    present += ay_link_Z3_solver_to_dimacs_string != 0;
    present += ay_link_Z3_solver_to_string != 0;
    present += ay_link_Z3_solver_translate != 0;
    present += ay_link_Z3_sort_to_ast != 0;
    present += ay_link_Z3_sort_to_string != 0;
    present += ay_link_Z3_stats_dec_ref != 0;
    present += ay_link_Z3_stats_get_double_value != 0;
    present += ay_link_Z3_stats_get_key != 0;
    present += ay_link_Z3_stats_get_uint_value != 0;
    present += ay_link_Z3_stats_inc_ref != 0;
    present += ay_link_Z3_stats_is_double != 0;
    present += ay_link_Z3_stats_is_uint != 0;
    present += ay_link_Z3_stats_size != 0;
    present += ay_link_Z3_stats_to_string != 0;
    present += ay_link_Z3_substitute_funs != 0;
    present += ay_link_Z3_substitute_vars != 0;
    present += ay_link_Z3_substitute != 0;
    present += ay_link_Z3_tactic_and_then != 0;
    present += ay_link_Z3_tactic_apply_ex != 0;
    present += ay_link_Z3_tactic_apply != 0;
    present += ay_link_Z3_tactic_cond != 0;
    present += ay_link_Z3_tactic_dec_ref != 0;
    present += ay_link_Z3_tactic_fail_if_not_decided != 0;
    present += ay_link_Z3_tactic_fail_if != 0;
    present += ay_link_Z3_tactic_fail != 0;
    present += ay_link_Z3_tactic_get_descr != 0;
    present += ay_link_Z3_tactic_get_help != 0;
    present += ay_link_Z3_tactic_get_param_descrs != 0;
    present += ay_link_Z3_tactic_inc_ref != 0;
    present += ay_link_Z3_tactic_or_else != 0;
    present += ay_link_Z3_tactic_par_and_then != 0;
    present += ay_link_Z3_tactic_par_or != 0;
    present += ay_link_Z3_tactic_repeat != 0;
    present += ay_link_Z3_tactic_skip != 0;
    present += ay_link_Z3_tactic_try_for != 0;
    present += ay_link_Z3_tactic_using_params != 0;
    present += ay_link_Z3_tactic_when != 0;
    present += ay_link_Z3_to_app != 0;
    present += ay_link_Z3_to_func_decl != 0;
    present += ay_link_Z3_toggle_warning_messages != 0;
    present += ay_link_Z3_translate != 0;
    present += ay_link_Z3_update_param_value != 0;
    present += ay_link_Z3_update_term != 0;
    return present == 805 ? 0 : 1;
}
