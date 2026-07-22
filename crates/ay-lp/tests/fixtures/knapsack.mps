* 0/1 knapsack: choose items to maximize value with weight <= 6.
* max  3 X + 4 Y + 2 Z
* s.t. 2 X + 3 Y + 1 Z <= 6
*      X, Y, Z binary
* Optimum: X=1, Y=1, Z=1, 2+3+1=6, obj=9.
NAME          KNAPSACK
OBJSENSE
    MAX
ROWS
 N  VALUE
 L  WEIGHT
COLUMNS
    MARKER1   'MARKER'  'INTORG'
    X         VALUE         3.0   WEIGHT        2.0
    Y         VALUE         4.0   WEIGHT        3.0
    Z         VALUE         2.0   WEIGHT        1.0
    MARKER2   'MARKER'  'INTEND'
RHS
    RHS       WEIGHT        6.0
BOUNDS
 BV BND       X
 BV BND       Y
 BV BND       Z
ENDATA
