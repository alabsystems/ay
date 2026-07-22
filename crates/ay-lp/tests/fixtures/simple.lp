\ Simple LP test fixture.
\ min  x + y   s.t.  x + y >= 4,  x + 3y >= 6,  x,y >= 0.
\ Optimum: x = 3, y = 1, obj = 4.
Minimize
 obj: x + y
Subject To
 c1: x + y >= 4
 c2: x + 3 y >= 6
Bounds
 x >= 0
 y >= 0
End
