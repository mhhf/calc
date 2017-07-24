const rightPad = (str, max) => {
  let bufferLength = max - str.toString().length;
  if(bufferLength < 0) bufferLength = 0;
  return " ".repeat(bufferLength);
}

// TODO - default attrs is everything
const formatDb = function (db, attrs) {
  // get the desired attributes from the db objects
  let table = db.map(el => attrs.map(attr => el[attr]));
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

module.exports = {
  formatDb
}
