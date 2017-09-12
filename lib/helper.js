const keccak = require('keccakjs')
const clc = require('cli-color');

const sha3 = str => {
  var hash = new keccak() // uses 512 bits by default
  hash.update(str)
  return hash.digest('hex') // hex output
}


const rightPad = (str, max) => {
  let bufferLength = max - (str || "").toString().length;
  if(bufferLength < 0) bufferLength = 0;
  return " ".repeat(bufferLength);
}

// TODO - default attrs is everything
const formatDb = function (db, attrs) {
  // get the desired attributes from the db objects
  let table = db.map(row => attrs.map(attr => row[attr] || ""));
  // Add attrs as titles
  table = ([attrs.map(t => t.toUpperCase())]).concat(table);

  let tableSizes = table
    .reduceRight((a, row) => row.map( (s,i) => Math.max(s && s.toString().length || 0, a[i] || 0) ), []);

  let SPACE = 3;
  let formattedTable = table
  .map(e => e.map((str, i) => str + rightPad(str, tableSizes[i])).join(" ".repeat(SPACE)))
  .join("\n");

  return formattedTable;

}

const formatCleanTree = function (tree, loc) {
  const fArray = (e, s) =>
    Array.isArray(e) && e.length > 1 ? e[0] + "\n" + e.slice(1).map(ee => s+ee).join("\n") : e

  const prefix = (row, dot = true) => "  " + (dot ? ".": " ").repeat(Math.max(0, max - row[0].length - 6)) + "  "
  let table = foldCleanPreorder(tree, loc)
  let max = table
    .reduceRight((a, row) => (row[0].length > a) ? row[0].length : a, 0);
  let str = table.map(row => row[0] + ((1 in row) && (prefix(row) + fArray(row[1], row[0].replace(/\w/g, " ") + prefix(row, false)) ) || "")).join("\n")
  return str;
}


const foldCleanPreorder = function (tree, loc, prefix = "", last = true) {
  let table = [];
  let __prefix = prefix + (last ? "╘ ": "╞ ")
  table.push([__prefix + clc.yellow(tree.head[loc])]);

  Object.keys(tree.head).forEach(name => {
    if(name !== loc) {
      let str = prefix +  ((last || tree.children.length === 0) ? (tree.children.length === 0 && !last ? "│   " : "  │ ") : "│ ") + "" + name ;
      table.push([str, tree.head[name]]);
    }
  })

  // TODO - do i need children which are not arrays?
  let childs = Array.isArray(tree.children)
    ? tree.children
    : ("children" in tree
        ? [tree.children]
        : [])
  let l = childs.length - 1;

  let rest = childs
  .map((child, i) => {
    let prefix_ = prefix + (last ? "  " : "│ ")
    let last_ = i === l;
    return foldCleanPreorder(child, loc, prefix_, last_)
  })
  .reverse()
  .reduceRight((a, c) => a.concat(c), [])

  return table.concat(rest)
}

const foldPreorder = function (tree, loc, prefix = "", last = true) {
  let table = [];
  let __prefix = prefix + (last ? "└ ": "├ ")
  // let head = Object.assign(tree.head, {__prefix})
  loc && (tree.head[loc] = __prefix + tree.head[loc]);
  table.push(tree.head);

  // TODO - do i need children which are not arrays?
  let childs = Array.isArray(tree.children)
    ? tree.children
    : ("children" in tree
        ? [tree.children]
        : [])
  let l = childs.length - 1;

  let rest = childs
  .map((child, i) => {
    let prefix_ = prefix + (last ? "  " : "│ ")
    let last_ = i === l;
    return foldPreorder(child, loc, prefix_, last_)
  })
  .reverse()
  .reduceRight((a, c) => a.concat(c), [])

  return table.concat(rest)
}


const _tree2dot = (id, tree, heads) => {
  // let name = tree.head[head] || tree.head.constr;
  let children = ("children" in tree && tree.children || []);

  let child_pointers = children
    .map((child, i) => sha3(id + i))

  let pointers = child_pointers
  .map(p => `"${id}" -> "${p}";`)
  .join("\n")

  let childTrees = children
  .map((c, i) => _tree2dot(sha3(id + i), c, heads))
  .join("\n")

  let information = heads
    .map(h => `<TR><TD>${h}</TD><TD>${(tree.head[h] || "").replace(/\<|\>/g,"")}</TD></TR>`)
    .join("\n")


  let label = `<<TABLE BORDER="1" CELLSPACING ="0">\n${information}\n</TABLE>>`;

  return `"${ id }" [shape=none, label=${ label }];\n${ pointers }\n${ childTrees }`;
}

const tree2dot = (tree, heads) => {
  return `digraph A {\n${_tree2dot(sha3("0"), tree, heads)}\n}`;
}

module.exports = {
  formatCleanTree,
  formatDb,
  tree2dot,
  foldCleanPreorder,
  foldPreorder
}
