import { Model, equationPrompt } from "../search.mjs";

const model = new Model("LLM token router");
const requests = ["chat", "code", "batch"];
const tokenUnits = [1, 2, 5]; // rounded 1k-token billing units
const routes = [];
const costs = [];
const latencies = [];
const localLoads = [];

for (const [index, request] of requests.entries()) {
  const route = model.choice(`${request}_route`, [
    "local",
    "fast_cloud",
    "cheap_cloud",
  ]);
  const cost = model.int(`${request}_cost`, 0, 20);
  const latency = model.int(`${request}_latency`, 45, 180);
  const localLoad = model.int(`${request}_local_load`, 0, tokenUnits[index]);
  model.table(
    [route, cost, latency, localLoad],
    [
      ["local", 0, 180, tokenUnits[index]],
      ["fast_cloud", 20, 45, 0],
      ["cheap_cloud", 7, 120, 0],
    ],
  );
  routes.push(route);
  costs.push(cost);
  latencies.push(latency);
  localLoads.push(localLoad);
}
model.add("chat_latency <= 100");
model.add("code_latency <= 200");
model.add("batch_latency <= 200");
model.add("chat_local_load + code_local_load + batch_local_load <= 5");
model.minimize(
  costs.map((cost, index) => `${tokenUnits[index]} * ${cost}`).join(" + "),
);

console.log(
  equationPrompt(
    [...latencies, ...localLoads],
    "chat latency must be at most 100 ms; code and batch latency must be at most 200 ms; total local load must be at most 5",
  ),
);
const result = model.solve({ timeoutMs: 2_000 });
if (result.status !== "optimal") {
  throw new Error(`router has no proved optimum: ${result.status}`);
}
const solution = result.requireSolution();
requests.forEach((request, index) =>
  console.log(`${request}: ${solution.get(routes[index])}`),
);
console.log(`proved minimum weighted cost: ${result.objective}`);
