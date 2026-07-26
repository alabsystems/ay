import { Model } from "../search.mjs";

const model = new Model("4x4 Sudoku");
const cell = model.intGrid("cell", 4, 4, 1, 4);
for (const row of cell) model.allDifferent(row);
for (let column = 0; column < 4; column++) {
  model.allDifferent(cell.map((row) => row[column]));
}
for (const boxRow of [0, 2]) {
  for (const boxColumn of [0, 2]) {
    model.allDifferent(
      [0, 1].flatMap((dr) =>
        [0, 1].map((dc) => cell[boxRow + dr][boxColumn + dc]),
      ),
    );
  }
}
for (const [row, column, value] of [
  [0, 0, 1],
  [0, 3, 4],
  [1, 1, 4],
  [2, 2, 4],
  [3, 0, 4],
  [3, 3, 1],
]) {
  model.add(`${cell[row][column]} == ${value}`);
}
const solution = model.solve().requireSolution();
for (const row of cell)
  console.log(row.map((value) => solution.get(value)).join(" "));
