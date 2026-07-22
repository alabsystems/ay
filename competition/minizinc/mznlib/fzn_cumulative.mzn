% AY cumulative: native time-tabling for FIXED (par) capacity, std decomposition
% for VARIABLE capacity. ay-cp's Cumulative propagator requires a constant
% capacity; routing variable-capacity cumulative through the std decomposition
% keeps it on the CP path (avoids a whole-model SMT fallback) while the common
% fixed-capacity case (e.g. ihtc-2024-kletzander) uses the native propagator.

% Native builtin — fixed (par) capacity; AY's solve_cp reads args[3] as a const.
predicate fzn_cumulative(
  array [int] of var int: s,
  array [int] of var int: d,
  array [int] of var int: r,
  int: b,
);

% Variable capacity: route fixed values to the native builtin above, otherwise
% fall back to the standard time/task decomposition (inlined — this file shadows
% std/fzn_cumulative.mzn so its helpers are not otherwise visible).
predicate fzn_cumulative(
  array [int] of var int: s,
  array [int] of var int: d,
  array [int] of var int: r,
  var int: b,
) =
  if is_fixed(b) then
    fzn_cumulative(s, d, r, fix(b))
  else
    let {
      set of int: Tasks =
        {i | i in index_set(s) where ub(r[i]) > 0 /\ ub(d[i]) > 0};
    } in if 0 == card(Tasks) then
      0 == card(index_set(s)) \/ b >= 0
    else
      let {
        int: early = min([lb(s[i]) | i in Tasks]);
        int: late = max([ub(s[i]) + ub(d[i]) | i in Tasks]);
      } in (
        if late - early > 5000 then
          fzn_cumulative_task(s, d, r, b)
        else
          fzn_cumulative_time(s, d, r, b)
        endif
      )
    endif
  endif;

predicate fzn_cumulative_time(
  array [int] of var int: s,
  array [int] of var int: d,
  array [int] of var int: r,
  var int: b,
) =
  let {
    set of int: Tasks =
      {i | i in index_set(s) where ub(r[i]) > 0 /\ ub(d[i]) > 0};
    int: early = min([lb(s[i]) | i in Tasks]);
    int: late = max([ub(s[i]) + ub(d[i]) | i in Tasks]);
  } in (
    forall (t in early..late) (
      b >= sum (i in Tasks) ((s[i] <= t /\ t < s[i] + d[i]) * r[i])
    )
  );

predicate fzn_cumulative_task(
  array [int] of var int: s,
  array [int] of var int: d,
  array [int] of var int: r,
  var int: b,
) =
  let {
    set of int: Tasks =
      {i | i in index_set(s) where ub(r[i]) > 0 /\ ub(d[i]) > 0};
  } in (
    forall (j in Tasks) (
      b >= sum (i in Tasks) ((s[i] <= s[j] /\ s[j] < s[i] + d[i]) * r[i])
    )
  );
