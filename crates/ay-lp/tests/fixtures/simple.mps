* Simple MPS test fixture.
* min  x + y
* s.t. x + y >= 4
*      x + 3y >= 6
*      x, y >= 0
* Optimum: x = 3, y = 1, obj = 4.
NAME          SIMPLE
ROWS
 N  COST
 G  C1
 G  C2
COLUMNS
    X         COST          1.0   C1            1.0
    X         C2            1.0
    Y         COST          1.0   C1            1.0
    Y         C2            3.0
RHS
    RHS       C1            4.0   C2            6.0
BOUNDS
ENDATA
