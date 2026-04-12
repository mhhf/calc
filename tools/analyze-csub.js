#!/usr/bin/env node
const path = require("path");
const Store = require("../lib/kernel/store");
const mde = require("../lib/engine");
const { loadBytecode, bytecodeArrGetGuard } = require("../lib/engine/ill/bytecode-loader");
const { intToBin, binToInt } = require("../lib/engine/ill/ffi/convert");

const EVM_PATH = path.join(__dirname, "../calculus/ill/programs/evm.ill");
const fixturePath = path.join(__dirname, "../tests/fixtures/VMTests/vmPerformance/loop-add-10M.json");
const data = JSON.parse(require("fs").readFileSync(fixturePath, "utf8"));
const fixture = Object.values(data)[0];
const hex = fixture.exec.code.startsWith("0x") ? fixture.exec.code.slice(2) : fixture.exec.code;

Store.clear();
const bc = loadBytecode(hex);
const barriers = new Set();
for (const pc of bc.entryPoints) barriers.add(intToBin(BigInt(pc)));

const calc = mde.load(EVM_PATH, {
  cache: false,
  extraGrade0Facts: bc.facts,
  scopeGuard: bytecodeArrGetGuard,
  fusionBarriers: barriers,
});

function showHash(h) {
  if (h < 0) return "mv(" + h + ")";
  const tag = Store.tag(h);
  if (tag) {
    const arity = Store.arity(h);
    if (arity === 0) return tag;
    const args = [];
    for (let i = 0; i < arity; i++) args.push(showHash(Store.child(h, i)));
    return tag + "(" + args.join(",") + ")";
  }
  return "#" + h;
}

// Find fused rules with checked_sub goals — show the loop body rule
const fusedRules = calc.forwardRules.filter(r => r.name && r.name.includes("+"));
for (const r of fusedRules) {
  const persGoals = r.antecedent.persistent || [];
  const csGoals = persGoals.filter(p => Store.tag(p) === "checked_sub");
  if (csGoals.length < 3) continue; // skip small chains

  console.log("Rule:", r.name.slice(0, 120));
  console.log("  checked_sub goals:", csGoals.length);

  for (const g of csGoals) {
    const a0 = Store.child(g, 0);
    const a1 = Store.child(g, 1);
    const a2 = Store.child(g, 2);
    const costStr = binToInt(a1) !== null ? String(binToInt(a1)) : showHash(a1);
    console.log("    checked_sub(", showHash(a0).slice(0, 30), ",", costStr, ",", showHash(a2).slice(0, 30), ")");
  }
  console.log();
}
