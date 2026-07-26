"""Optimize an LLM request router with table constraints and a token budget."""

from aysearch import Model, equation_prompt


model = Model("LLM token router")
requests = ["chat", "code", "batch"]
# Rounded 1k-token billing units keep the objective directly interpretable.
token_units = [1, 2, 5]

routes = []
costs = []
latencies = []
local_loads = []
for index, request in enumerate(requests):
    route = model.choice(f"{request}_route", ["local", "fast_cloud", "cheap_cloud"])
    cost = model.int(f"{request}_cost", 0, 20)
    latency = model.int(f"{request}_latency", 45, 180)
    local_load = model.int(f"{request}_local_load", 0, token_units[index])
    # Rows are route, micro-dollars per 1k tokens, milliseconds, and local load.
    model.table(
        [route, cost, latency, local_load],
        [
            ["local", 0, 180, token_units[index]],
            ["fast_cloud", 20, 45, 0],
            ["cheap_cloud", 7, 120, 0],
        ],
    )
    routes.append(route)
    costs.append(cost)
    latencies.append(latency)
    local_loads.append(local_load)

# The strings below are exactly the sort of output an LLM can safely propose:
# they remain data and AY parses a deliberately restricted linear grammar.
model.add("chat_latency <= 100")
model.add("code_latency <= 200")
model.add("batch_latency <= 200")
model.add("chat_local_load + code_local_load + batch_local_load <= 5")
weighted_cost = " + ".join(
    f"{units} * {cost.name}" for units, cost in zip(token_units, costs)
)
model.minimize(weighted_cost)

print(
    equation_prompt(
        [*latencies, *local_loads],
        "chat latency must be at most 100 ms; code and batch latency must be at "
        "most 200 ms; total local load must be at most 5",
    )
)
result = model.solve(timeout_ms=2_000)
if result.status != "optimal":
    raise RuntimeError(f"router has no proved optimum: {result.status}")
solution = result.require_solution()
for request, route in zip(requests, routes):
    print(f"{request:5}: {solution[route]}")
print(f"proved minimum weighted cost: {result.objective}")
