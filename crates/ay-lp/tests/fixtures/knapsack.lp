\ 0/1 knapsack in LP format.
\ max  3 x + 4 y + 2 z s.t. 2 x + 3 y + z <= 6, x,y,z binary.
\ Optimum: x=y=z=1, obj=9.
Maximize
 value: 3 x + 4 y + 2 z
Subject To
 weight: 2 x + 3 y + z <= 6
Binary
 x y z
End
