import { render } from 'solid-js/web';
import { Router } from '@solidjs/router';
import { RootLayout, routes } from './App';
import './styles/app.css';

// Import and initialize the calculus library
// @ts-ignore - CommonJS module
import * as CalcModule from '../../lib/calc.js';
// @ts-ignore - JSON import
import calcData from '../../out/calc.json';

// Handle CommonJS default export
const Calc = (CalcModule as any).default || CalcModule;

// Initialize the calculus database (must happen before any parsing)
Calc.init(calcData);

// Mount the app
const root = document.getElementById('root');

if (!root) {
  throw new Error('Root element not found');
}

render(
  () => (
    <Router root={RootLayout}>
      {routes}
    </Router>
  ),
  root
);
