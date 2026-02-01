/**
 * Profiler - Performance measurement for proof search
 *
 * Usage:
 *   CALC_PROFILE=1 node script.js
 *
 * Or programmatically:
 *   const { profiler } = require('./profiler');
 *   profiler.enable();
 *   // ... do work ...
 *   console.log(profiler.report());
 */

const { performance } = typeof window !== 'undefined'
  ? { performance: window.performance }
  : require('perf_hooks');

class Profiler {
  constructor(opts = {}) {
    this.enabled = opts.enabled ?? (typeof process !== 'undefined' && process.env.CALC_PROFILE === '1');
    this.counters = {};
    this.timers = {};
    this.scopeStack = [];
    this.startTime = null;
  }

  enable() {
    this.enabled = true;
    this.startTime = performance.now();
  }

  disable() {
    this.enabled = false;
  }

  reset() {
    this.counters = {};
    this.timers = {};
    this.scopeStack = [];
    this.startTime = performance.now();
  }

  // Count an operation
  count(name, amount = 1) {
    if (!this.enabled) return;
    const key = this._key(name);
    this.counters[key] = (this.counters[key] || 0) + amount;
  }

  // Time an operation - returns function to call when done
  time(name) {
    if (!this.enabled) return () => {};
    const key = this._key(name);
    const start = performance.now();
    return () => {
      const elapsed = performance.now() - start;
      if (!this.timers[key]) {
        this.timers[key] = { total: 0, count: 0, max: 0, min: Infinity };
      }
      this.timers[key].total += elapsed;
      this.timers[key].count++;
      this.timers[key].max = Math.max(this.timers[key].max, elapsed);
      this.timers[key].min = Math.min(this.timers[key].min, elapsed);
    };
  }

  // Time a synchronous function
  timeSync(name, fn) {
    if (!this.enabled) return fn();
    const end = this.time(name);
    try {
      return fn();
    } finally {
      end();
    }
  }

  // Enter a scope (for hierarchical profiling)
  push(scope) {
    if (this.enabled) this.scopeStack.push(scope);
  }

  // Exit a scope
  pop() {
    if (this.enabled) this.scopeStack.pop();
  }

  // Run function within a scope
  scope(name, fn) {
    this.push(name);
    try {
      return fn();
    } finally {
      this.pop();
    }
  }

  _key(name) {
    return this.scopeStack.length > 0
      ? `${this.scopeStack.join('/')}.${name}`
      : name;
  }

  stats() {
    const timerStats = {};
    for (const [key, timer] of Object.entries(this.timers)) {
      timerStats[key] = {
        total: timer.total,
        count: timer.count,
        avg: timer.count > 0 ? timer.total / timer.count : 0,
        max: timer.max,
        min: timer.min === Infinity ? 0 : timer.min,
      };
    }
    return {
      counters: { ...this.counters },
      timers: timerStats,
      elapsed: this.startTime ? performance.now() - this.startTime : 0,
    };
  }

  report() {
    if (!this.enabled) {
      return 'Profiling disabled. Set CALC_PROFILE=1 or call profiler.enable()';
    }

    const s = this.stats();
    const lines = ['=== CALC Profiler Report ===', ''];

    // Counters
    const counterKeys = Object.keys(s.counters).sort();
    if (counterKeys.length > 0) {
      lines.push('Counters:');
      for (const key of counterKeys) {
        lines.push(`  ${key}: ${s.counters[key]}`);
      }
      lines.push('');
    }

    // Timers
    const timerKeys = Object.keys(s.timers).sort();
    if (timerKeys.length > 0) {
      lines.push('Timers:');
      for (const key of timerKeys) {
        const t = s.timers[key];
        lines.push(`  ${key}: ${t.count} calls, ${t.total.toFixed(2)}ms total, ${t.avg.toFixed(3)}ms avg`);
      }
      lines.push('');
    }

    lines.push(`Total elapsed: ${s.elapsed.toFixed(2)}ms`);
    return lines.join('\n');
  }

  // Get a specific counter value
  getCount(name) {
    return this.counters[name] || 0;
  }

  // Get timer stats for a specific operation
  getTimer(name) {
    return this.timers[name] || null;
  }
}

// Global singleton instance
const profiler = new Profiler();

module.exports = { Profiler, profiler };
