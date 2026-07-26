import { Model } from "../search.mjs";

const model = new Model("5x5 Minesweeper");
const mine = Array.from({ length: 5 }, (_, row) =>
  Array.from({ length: 5 }, (_, column) => model.bool(`mine_${row}_${column}`)),
);
const clues = [
  [0, 0, 1],
  [0, 2, 2],
  [0, 3, 1],
  [0, 4, 1],
  [1, 0, 1],
  [1, 1, 1],
  [1, 2, 2],
  [1, 4, 1],
  [2, 0, 1],
  [2, 1, 1],
  [2, 2, 1],
  [2, 3, 2],
  [2, 4, 2],
  [3, 1, 2],
  [3, 2, 1],
  [3, 3, 2],
  [4, 0, 1],
  [4, 1, 2],
  [4, 3, 2],
  [4, 4, 1],
];
for (const [row, column, count] of clues) {
  model.add(`${mine[row][column]} == 0`);
  const neighbors = [];
  for (let r = Math.max(0, row - 1); r < Math.min(5, row + 2); r++) {
    for (let c = Math.max(0, column - 1); c < Math.min(5, column + 2); c++) {
      if (r !== row || c !== column) neighbors.push(mine[r][c].name);
    }
  }
  model.add(`${neighbors.join(" + ")} == ${count}`);
}
const solution = model.solve().requireSolution();
for (const row of mine)
  console.log(row.map((cell) => (solution.get(cell) ? "*" : ".")).join(" "));
