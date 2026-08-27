import assert from "node:assert/strict";
import { Model, NativeSearchError, SearchError } from "./search.mjs";

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
])
  model.add(`${cell[row][column]} == ${value}`);

const result = model.solve();
const solution = result.requireSolution();
for (const row of cell) {
  assert.deepEqual(
    new Set(row.map((value) => solution.get(value))),
    new Set([1, 2, 3, 4]),
  );
}
assert.match(model.toSMT2(), /declare-const \|cell_0_0\|/);

const choices = new Model("choices");
const route = choices.choice("route", ["cpu", "gpu"]);
choices.add("route >= 0");
const routes = choices.enumerate(10);
assert.equal(routes.status, "complete");
assert.deepEqual(
  new Set(routes.solutions.map((item) => item.get(route))),
  new Set(["cpu", "gpu"]),
);

const elementModel = new Model("element");
const index = elementModel.int("index", 0, 1);
const first = elementModel.int("first", 4, 4);
const second = elementModel.int("second", 9, 9);
const selected = elementModel.int("selected", 4, 9);
elementModel.element(index, [first, second], selected).add("index == 1");
assert.equal(elementModel.solve().requireSolution().get(selected), 9);
elementModel.minimize(selected);
assert.throws(() => elementModel.enumerate(), /objective/);

const emptyTable = new Model("empty table");
const emptyTableVariable = emptyTable.int("x", 0, 1);
assert.throws(() => emptyTable.table([emptyTableVariable], []), SearchError);

const prototypeNames = new Model("prototype-safe names");
const proto = prototypeNames.int("__proto__", 7, 7);
const constructor = prototypeNames.int("constructor", 11, 11);
assert.equal(Object.isFrozen(proto), true);
assert.throws(() => {
  proto.name = "renamed";
}, TypeError);
const prototypeSolution = prototypeNames.solve().requireSolution();
assert.equal(prototypeSolution.get(proto), 7);
assert.equal(prototypeSolution.get("__proto__"), 7);
assert.equal(prototypeSolution.rawValues.__proto__, 7);
assert.equal(prototypeSolution.get(constructor), 11);
assert.equal(Object.getPrototypeOf(prototypeSolution.values), null);
assert.equal(Object.getPrototypeOf(prototypeSolution.rawValues), null);
assert.equal(Object.hasOwn(prototypeSolution.values, "__proto__"), true);

const otherPrototypeNames = new Model("other model with the same names");
const foreignProto = otherPrototypeNames.int("__proto__", 7, 7);
assert.throws(() => prototypeSolution.get(foreignProto), /another model/);
assert.equal(prototypeSolution.get("__proto__"), 7); // String lookup stays valid.

const laterVariable = prototypeNames.int("declared_later", 13, 13);
assert.throws(() => prototypeSolution.get(laterVariable), /solve epoch/);
assert.equal(prototypeSolution.get(proto), 7);

const unsafeObjective = new Model("unsafe JavaScript objective");
const maxSafe = unsafeObjective.int(
  "max_safe",
  Number.MAX_SAFE_INTEGER,
  Number.MAX_SAFE_INTEGER,
);
unsafeObjective.maximize(`${maxSafe} + 1`);
assert.throws(() => unsafeObjective.solve(), NativeSearchError);

console.log("AY Search Node binding: PASS");
