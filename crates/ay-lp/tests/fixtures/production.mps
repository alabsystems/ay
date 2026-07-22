* Production LP (textbook): maximize profit from chairs (X) and tables (Y).
* max  5 X + 4 Y
* s.t. 6 X + 4 Y <= 24   (wood)
*      X + 2 Y <= 6      (labor)
*      X, Y >= 0
* Optimum: X = 3, Y = 1.5, obj = 21.
NAME          PRODUCTION
OBJSENSE
    MAX
ROWS
 N  PROFIT
 L  WOOD
 L  LABOR
COLUMNS
    X         PROFIT        5.0   WOOD          6.0
    X         LABOR         1.0
    Y         PROFIT        4.0   WOOD          4.0
    Y         LABOR         2.0
RHS
    RHS       WOOD         24.0   LABOR         6.0
BOUNDS
ENDATA
