\ Production LP example: maximize profit.
\ max  5 x + 4 y s.t. 6 x + 4 y <= 24, x + 2 y <= 6, x,y >= 0.
\ Optimum: x = 3, y = 1.5, obj = 21.
Maximize
 profit: 5 x + 4 y
Subject To
 wood:  6 x + 4 y <= 24
 labor: x + 2 y <= 6
Bounds
 x >= 0
 y >= 0
End
