% AY circuit. FlatZinc arrays are always indexed from 1, so a circuit over an
% array indexed from another base (for example `array[0..n] of var 0..n`) would
% reach FlatZinc with its node numbering lost: successor value v would be read
% as the 1-based node v, which turns valid circuits into self-loops. Pass the
% first node explicitly, as Gecode's and OR-Tools' libraries do.

% Native builtin: x[i] (i = 1..n) is the successor of node base+i-1, and the
% successors range over base..base+n-1.
predicate ay_circuit(array [int] of var int: x, int: base);

predicate fzn_circuit(array [int] of var int: x) =
  if length(x) = 0 then true else ay_circuit(array1d(x), min(index_set(x))) endif;
