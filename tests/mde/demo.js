const mde = require('../../lib/mde');

// Helper to convert binary to decimal
function binToDec(s) {
  if (s === "e") return 0;
  // Handle nested parens: "o (i e)" or "i (o (i e))"
  s = s.trim();
  if (s.startsWith("o ")) {
    const inner = s.slice(2).replace(/^\(/, '').replace(/\)$/, '');
    return 2 * binToDec(inner);
  }
  if (s.startsWith("i ")) {
    const inner = s.slice(2).replace(/^\(/, '').replace(/\)$/, '');
    return 2 * binToDec(inner) + 1;
  }
  return NaN;
}

// Helper to convert decimal to binary representation
function decToBin(n) {
  if (n === 0) return "e";
  if (n % 2 === 1) return `i (${decToBin((n - 1) / 2)})`;
  return `o (${decToBin(n / 2)})`;
}

(async () => {
  const calc = await mde.load("/home/mhhf/src/optimism-mde/lib/bin.mde");

  console.log("=== MDE Binary Arithmetic Demo ===\n");
  console.log("Binary representation:");
  console.log("  e     = 0");
  console.log("  i X   = 2*X + 1  (odd)");
  console.log("  o X   = 2*X      (even, non-zero)");
  console.log();

  // Test additions
  const additions = [
    [0, 0], [1, 0], [1, 1], [2, 2], [3, 1], [5, 3], [7, 8]
  ];

  console.log("Addition tests:");
  for (const [a, b] of additions) {
    const aBin = decToBin(a);
    const bBin = decToBin(b);
    const query = `plus (${aBin}) (${bBin}) X`;
    const goal = await mde.parseExpr(query);
    const result = calc.prove(goal, { maxDepth: 100 });

    if (result.success) {
      const solution = mde.extractSolution(result.theta, goal);
      const resultDec = binToDec(solution.X);
      console.log(`  ${a} + ${b} = ${resultDec} (${solution.X})`);
    } else {
      console.log(`  ${a} + ${b} = FAILED`);
    }
  }

  // Test multiplications
  console.log("\nMultiplication tests:");
  const mults = [[1, 1], [2, 2], [3, 2], [2, 3]];
  for (const [a, b] of mults) {
    const aBin = decToBin(a);
    const bBin = decToBin(b);
    const query = `mul (${aBin}) (${bBin}) X`;
    const goal = await mde.parseExpr(query);
    const result = calc.prove(goal, { maxDepth: 100 });

    if (result.success) {
      const solution = mde.extractSolution(result.theta, goal);
      const resultDec = binToDec(solution.X);
      console.log(`  ${a} * ${b} = ${resultDec} (${solution.X})`);
    } else {
      console.log(`  ${a} * ${b} = FAILED`);
    }
  }
})().catch(e => console.error(e));
