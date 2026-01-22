import {run} from '@cycle/run'
import xs from 'xstream';
import sampleCombine from 'xstream/extra/sampleCombine'
import katex from 'katex';
import {h, div, span, label, input, hr, button, h1, makeDOMDriver} from '@cycle/dom'

const parser = require("../../out/parser.js");
const Node = require("../../lib/node.js");
const PT = require("../../lib/pt.js");
const calc = require("../../out/calc.json");
const helper = require("../../lib/helper.js");
const Calc = require("../../lib/calc.js");
const Viz = require("viz.js");

// Initialize the calculus database (required for Node.toString to work)
Calc.init(calc);
parser.parser.yy.Node = Node;


function main(sources) {
  const input$ = sources.DOM.select('.field').events('input')
  const click$ = sources.DOM.select('#render').events('click').startWith("")

  const name$ = input$
    .map(ev => ev.target.value)
    .startWith('')
  const vdom$ = click$.compose(sampleCombine(name$))
    .map(e => e[1])
    .map((formula, _) => {

    var katexFormula = "";
    var graphSVG = "";
    if (formula && formula.trim()) {
      try {
        let node = parser.parse(formula)
        let latexFormula = node.toString({style: "latex_se"});
        let tableargs = ["constr", "ascii", "formula"];
        let graphObject = Node.toTree({node, rules: Calc.db.rules, attrs: tableargs})
        let graph = helper.tree2dot(graphObject, tableargs)
        try {
          katexFormula = katex.renderToString(latexFormula, {
            displayMode: true
          });
          graphSVG = Viz(graph, {format: "svg"});
        } catch (e) {
          katexFormula = e.toString();
        }
      } catch (e) {
        console.log(e);
        katexFormula = `<code>${e.message.replace(/\n/g, "<br />")}</code>`;
      }
    }

    let name = katex.renderToString("\\multimap_R");
    let A = katex.renderToString("A\\vdash B");
    let B = katex.renderToString("B\\vdash C");
    let C = katex.renderToString("C\\vdash D");

    // Example proof tree using current syntax (-- for any-term, * for tensor)
    let ll = [
      "?X, ?Y, -- : F?A -o F?B |- -- : F?C",
      "?X |- -- : F?A", "?Y, -- : F?B |- -- : F?C"
    ];
    let ll_pt;
    try {
      ll_pt = PT.fromNodeArray(ll.map(f => parser.parse(f)));
    } catch (e) {
      console.log("Error parsing example proof tree:", e);
      ll_pt = null;
    }


    return div([
      label('Name:'),
      input('.field', {attrs: {type: 'text'}}),
      button('#render', 'render'),
      hr(),
      h("div", {props:{innerHTML: katexFormula}}),
      h("center", {props:{innerHTML: graphSVG}}),
      ll_pt ? div({props: {innerHTML: ll_pt.toString({style: "html"})}}) : div("(proof tree parse error)")
      // span(".inferenceRule", [
      //   span(".rules", [
      //     span(".premisses", [
      //       span(".formula", {props: {innerHTML: A}}),
      //       span(".formula", {props: {innerHTML: B}})
      //     ]),
      //     span(".conclusion", [
      //       span(".formula", {props: {innerHTML: C}})
      //     ])
      //   ]),
      //   span(".name", [
      //     span({props: {innerHTML: name}})
      //   ])
      // ])
    ])
  })

  return { DOM: vdom$ }
}

run(main, { DOM: makeDOMDriver('#app-container') })
