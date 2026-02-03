import { render } from 'solid-js/web';
import { Router } from '@solidjs/router';
import { RootLayout, routes } from './App';
import './styles/app.css';

// v2 API is lazily initialized via calcV2.ts when needed
// No global initialization required

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
