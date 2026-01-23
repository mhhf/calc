// Browser-compatible cli-color stub
// Returns strings unchanged (no terminal colors in browser)

const identity = (s: any) => String(s);

// Create color functions that just return input unchanged
const colors = [
  'black', 'red', 'green', 'yellow', 'blue', 'magenta', 'cyan', 'white',
  'blackBright', 'redBright', 'greenBright', 'yellowBright', 'blueBright',
  'magentaBright', 'cyanBright', 'whiteBright', 'bgBlack', 'bgRed', 'bgGreen',
  'bgYellow', 'bgBlue', 'bgMagenta', 'bgCyan', 'bgWhite',
  'bold', 'dim', 'italic', 'underline', 'inverse', 'strike'
];

const clc: Record<string, (s: any) => string> = {};
for (const color of colors) {
  clc[color] = identity;
}

// Special methods
clc.xterm = () => identity;
clc.bgXterm = () => identity;

export default clc;
export { clc };
