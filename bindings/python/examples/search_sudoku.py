"""Solve a 4x4 Sudoku with AY Search."""

from aysearch import Model


model = Model("4x4 Sudoku")
cell = model.int_grid("cell", 4, 4, 1, 4)

for row in cell:
    model.all_different(row)
for column in range(4):
    model.all_different(cell[row][column] for row in range(4))
for box_row in (0, 2):
    for box_column in (0, 2):
        model.all_different(
            cell[row][column]
            for row in range(box_row, box_row + 2)
            for column in range(box_column, box_column + 2)
        )

for row, column, value in (
    (0, 0, 1),
    (0, 3, 4),
    (1, 1, 4),
    (2, 2, 4),
    (3, 0, 4),
    (3, 3, 1),
):
    model.add(f"{cell[row][column]} == {value}")

solution = model.solve().require_solution()
for row in cell:
    print(" ".join(str(solution[value]) for value in row))
