"""Focused end-to-end tests for the aysearch JSON binding."""

from aysearch import Model, SearchError


def test_search_spec_is_the_stable_safe_schema():
    model = Model("router")
    route = model.choice("route", ["cpu", "gpu"])
    cost = model.int("cost", 0, 20)
    model.table([route, cost], [["cpu", 3], ["gpu", 7]])
    model.add("cost <= 10")
    model.minimize(cost)

    assert model.to_spec() == {
        "version": 1,
        "name": "router",
        "variables": [
            {
                "name": "route",
                "domain": {"min": 0, "max": 1},
                "labels": {"0": "cpu", "1": "gpu"},
            },
            {"name": "cost", "domain": {"min": 0, "max": 20}},
        ],
        "constraints": [
            {"table": {"variables": ["route", "cost"], "tuples": [[0, 3], [1, 7]]}},
            {"expression": "cost <= 10"},
        ],
        "objective": {"sense": "minimize", "expression": "cost"},
    }


def test_search_solves_4x4_sudoku():
    model = Model("sudoku")
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

    result = model.solve()
    solution = result.require_solution()
    expected = {1, 2, 3, 4}
    assert all({solution[value] for value in row} == expected for row in cell)
    assert "declare-const |cell_0_0|" in model.to_smt2()


def test_search_choice_labels_and_complete_enumeration():
    model = Model("tiny router")
    route = model.choice("route", ["cpu", "gpu"])
    model.add("route >= 0")

    result = model.enumerate(10)
    assert result.status == "complete"
    assert result.complete is True
    assert {solution[route] for solution in result.solutions} == {"cpu", "gpu"}


def test_search_element_and_objective_enumeration_guard():
    model = Model("element")
    index = model.int("index", 0, 1)
    first = model.int("first", 4, 4)
    second = model.int("second", 9, 9)
    selected = model.int("selected", 4, 9)
    model.element(index, [first, second], selected)
    model.add("index == 1")
    assert model.solve().require_solution()[selected] == 9

    model.minimize(selected)
    try:
        model.enumerate()
    except SearchError as error:
        assert "objective" in str(error)
    else:
        raise AssertionError("enumerate() silently optimized an objective model")


def test_solution_rejects_a_variable_from_another_model():
    first = Model("first")
    own = first.int("same_name", 3, 3)
    solution = first.solve().require_solution()

    second = Model("second")
    foreign = second.int("same_name", 3, 3)
    try:
        solution[foreign]
    except SearchError as error:
        assert "another model" in str(error)
    else:
        raise AssertionError("solution accepted a variable from another model")

    assert solution[own] == 3
    assert solution["same_name"] == 3
