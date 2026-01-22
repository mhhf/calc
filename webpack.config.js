const path = require('path');

module.exports = {
  entry: './src/html/main.js',
  output: {
    filename: 'bundle.js',
    path: path.resolve(__dirname, 'src/html'),
  },
  mode: 'development',
  resolve: {
    fallback: {
      fs: false,
      path: false,
      crypto: false,
      stream: false
    }
  }
};
