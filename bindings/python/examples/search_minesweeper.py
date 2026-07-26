"""Turn Minesweeper's local clues into Boolean search constraints."""

from aysearch import Model


model = Model("5x5 Minesweeper")
mine = [[model.bool(f"mine_{row}_{column}") for column in range(5)] for row in range(5)]

# A revealed board: every tuple is (row, column, adjacent-mine count). Revealed
# squares are safe; AY searches for the hidden mines satisfying every clue.
clues = (
    (0, 0, 1),
    (0, 2, 2),
    (0, 3, 1),
    (0, 4, 1),
    (1, 0, 1),
    (1, 1, 1),
    (1, 2, 2),
    (1, 4, 1),
    (2, 0, 1),
    (2, 1, 1),
    (2, 2, 1),
    (2, 3, 2),
    (2, 4, 2),
    (3, 1, 2),
    (3, 2, 1),
    (3, 3, 2),
    (4, 0, 1),
    (4, 1, 2),
    (4, 3, 2),
    (4, 4, 1),
)
for row, column, count in clues:
    model.add(f"{mine[row][column]} == 0")
    neighbors = [
        mine[r][c].name
        for r in range(max(0, row - 1), min(5, row + 2))
        for c in range(max(0, column - 1), min(5, column + 2))
        if (r, c) != (row, column)
    ]
    model.add(" + ".join(neighbors) + f" == {count}")

solution = model.solve().require_solution()
for row in mine:
    print(" ".join("*" if solution[cell] else "." for cell in row))
