const keccak = require('keccakjs')

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
  let table = db.map(el => attrs.map(attr => el[attr] || ""));
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
  formatDb,
  tree2dot
}
