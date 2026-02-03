/**
 * Polarity Inference Test
 *
 * Tests that the polarity inference module correctly infers polarities from rule structure.
 * Polarity is now inferred (not specified in ll.json), so we validate against expected values.
 */

const fs = require('fs');
const path = require('path');
const {
  analyzeContextFlow,
  inferPolarity,
  inferAllPolarities,
  inferAllContextModes,
  CONNECTIVE_TO_RIGHT_RULE,
} = require('../lib/v1/polarity');

// Load ll.json
const llPath = path.join(__dirname, '..', 'll.json');
const ll = JSON.parse(fs.readFileSync(llPath, 'utf8'));

// Get rules
const rules = ll.rules;

// Expected polarities (derived from linear logic theory)
// Positive connectives: Tensor (*), Plus (+), One (1), Zero (0), Bang (!), Atom
// Negative connectives: Par (|), With (&), Loli (-o), Top, WhyNot (?), Forall
const expectedPolarity = {
  Formula_Tensor: 'positive',
  Formula_Bang: 'positive',
  Formula_With: 'negative',
  Formula_Loli: 'negative',
  Formula_Forall: 'negative',
  Formula_Lax: 'positive',
};

// Expected context modes for binary rules
const expectedContextModes = {
  Tensor_R: 'split',
  Loli_L: 'split',
  With_R: 'copy',
};

/**
 * Get a rule by name from any category
 */
function getRule(ruleName) {
  for (const category of Object.keys(rules)) {
    if (rules[category][ruleName]) {
      return {
        name: ruleName,
        category,
        rule: rules[category][ruleName]
      };
    }
  }
  return null;
}

// Main test
console.log('='.repeat(60));
console.log('POLARITY INFERENCE TEST');
console.log('='.repeat(60));
console.log();

let allMatch = true;

// Test inferAllPolarities function
console.log('Testing inferAllPolarities():');
console.log();

const inferredPolarities = inferAllPolarities(rules);
console.log('Inferred polarities:', JSON.stringify(inferredPolarities, null, 2));
console.log();

for (const [formulaName, expectedPol] of Object.entries(expectedPolarity)) {
  const infPol = inferredPolarities[formulaName];
  const match = infPol === expectedPol;
  const icon = match ? '✓' : '✗';
  console.log(`${icon} ${formulaName}: inferred ${infPol}, expected ${expectedPol}`);
  if (!match) allMatch = false;
}

console.log();

// Test inferAllContextModes function
console.log('='.repeat(60));
console.log('CONTEXT MODE INFERENCE TEST');
console.log('='.repeat(60));
console.log();

const contextModes = inferAllContextModes(rules);
console.log('Inferred context modes:', JSON.stringify(contextModes, null, 2));
console.log();

for (const [ruleName, expectedMode] of Object.entries(expectedContextModes)) {
  const infMode = contextModes[ruleName];
  const match = infMode === expectedMode;
  const icon = match ? '✓' : '✗';
  console.log(`${icon} ${ruleName}: inferred ${infMode}, expected ${expectedMode}`);
  if (!match) allMatch = false;
}

console.log();

// Test analyzeContextFlow for specific rules
console.log('='.repeat(60));
console.log('CONTEXT FLOW ANALYSIS');
console.log('='.repeat(60));
console.log();

const rulesToAnalyze = ['Tensor_R', 'Loli_L', 'Loli_R', 'With_R', 'Bang_R', 'Forall_R'];
for (const ruleName of rulesToAnalyze) {
  const ruleInfo = getRule(ruleName);
  if (!ruleInfo) {
    console.log(`⚠ ${ruleName}: Not found`);
    continue;
  }

  const ruleArray = ruleInfo.rule;
  const conclusion = ruleArray[0];
  const premises = ruleArray.slice(1).filter(s => s.trim() !== '');

  console.log(`${ruleName}:`);
  console.log(`  Conclusion: ${conclusion}`);
  premises.forEach((p, i) => console.log(`  Premise ${i + 1}: ${p}`));

  const flowAnalysis = analyzeContextFlow(conclusion, premises);
  console.log(`  Flow type: ${flowAnalysis.type}`);
  console.log(`  Conclusion vars: ${flowAnalysis.conclusionVars.join(', ') || '(none)'}`);
  if (flowAnalysis.varBehaviors) {
    for (const [v, behavior] of Object.entries(flowAnalysis.varBehaviors)) {
      console.log(`    ${v}: ${behavior}`);
    }
  }
  console.log();
}

// Summary
console.log('='.repeat(60));
console.log('SUMMARY');
console.log('='.repeat(60));
console.log();

if (allMatch) {
  console.log('✓ ALL TESTS PASSED');
  console.log('  Polarity can be inferred correctly from rule structure');
} else {
  console.log('✗ SOME TESTS FAILED');
}
console.log();

process.exit(allMatch ? 0 : 1);
