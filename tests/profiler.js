const { describe, it, beforeEach } = require('node:test');
const assert = require('node:assert');
const { Profiler, profiler } = require('../lib/v1/profiler');

describe('Profiler', () => {
  let p;

  beforeEach(() => {
    p = new Profiler({ enabled: true });
  });

  describe('counters', () => {
    it('should track operation counts', () => {
      p.count('mgu');
      p.count('mgu');
      p.count('substitute');
      assert.strictEqual(p.stats().counters.mgu, 2);
      assert.strictEqual(p.stats().counters.substitute, 1);
    });

    it('should support custom amounts', () => {
      p.count('nodes', 5);
      p.count('nodes', 3);
      assert.strictEqual(p.stats().counters.nodes, 8);
    });

    it('should return 0 for uncounted operations', () => {
      assert.strictEqual(p.getCount('nonexistent'), 0);
    });
  });

  describe('timers', () => {
    it('should time operations', async () => {
      const end = p.time('mgu');
      await new Promise(resolve => setTimeout(resolve, 10));
      end();
      const timer = p.stats().timers.mgu;
      assert.strictEqual(timer.count, 1);
      assert.ok(timer.total > 0);
    });

    it('should track multiple calls', () => {
      for (let i = 0; i < 5; i++) {
        const end = p.time('fast_op');
        end();
      }
      const timer = p.stats().timers.fast_op;
      assert.strictEqual(timer.count, 5);
    });

    it('should track min/max/avg', () => {
      const end1 = p.time('op');
      end1();
      const end2 = p.time('op');
      end2();

      const timer = p.stats().timers.op;
      assert.strictEqual(timer.count, 2);
      assert.ok(timer.min <= timer.max);
      assert.strictEqual(timer.avg, timer.total / timer.count);
    });

    it('should support timeSync for synchronous functions', () => {
      const result = p.timeSync('compute', () => {
        let sum = 0;
        for (let i = 0; i < 1000; i++) sum += i;
        return sum;
      });
      assert.strictEqual(result, 499500);
      assert.strictEqual(p.stats().timers.compute.count, 1);
    });
  });

  describe('scopes', () => {
    it('should track nested scopes', () => {
      p.push('branch1');
      p.count('mgu');
      p.pop();

      p.push('branch2');
      p.count('mgu');
      p.pop();

      assert.strictEqual(p.stats().counters['branch1.mgu'], 1);
      assert.strictEqual(p.stats().counters['branch2.mgu'], 1);
    });

    it('should support deep nesting', () => {
      p.push('a');
      p.push('b');
      p.count('op');
      p.pop();
      p.pop();

      assert.strictEqual(p.stats().counters['a/b.op'], 1);
    });

    it('should support scope() helper', () => {
      const result = p.scope('myScope', () => {
        p.count('inner');
        return 42;
      });
      assert.strictEqual(result, 42);
      assert.strictEqual(p.stats().counters['myScope.inner'], 1);
    });
  });

  describe('enable/disable', () => {
    it('should be disabled by default (without env var)', () => {
      const disabled = new Profiler({ enabled: false });
      disabled.count('mgu');
      assert.deepStrictEqual(disabled.stats().counters, {});
    });

    it('should do nothing when disabled', () => {
      const disabled = new Profiler({ enabled: false });
      disabled.count('mgu');
      const end = disabled.time('op');
      end();
      assert.deepStrictEqual(disabled.stats().counters, {});
      assert.deepStrictEqual(disabled.stats().timers, {});
    });

    it('should enable on demand', () => {
      const p2 = new Profiler({ enabled: false });
      p2.count('before');
      p2.enable();
      p2.count('after');
      assert.strictEqual(p2.stats().counters.before, undefined);
      assert.strictEqual(p2.stats().counters.after, 1);
    });
  });

  describe('reset', () => {
    it('should clear all data', () => {
      p.count('mgu');
      const end = p.time('op');
      end();
      p.reset();
      assert.deepStrictEqual(p.stats().counters, {});
      assert.deepStrictEqual(p.stats().timers, {});
    });
  });

  describe('report', () => {
    it('should generate readable report', () => {
      p.count('mgu', 10);
      p.count('substitute', 5);
      const end = p.time('proof');
      end();

      const report = p.report();
      assert.ok(report.includes('CALC Profiler Report'));
      assert.ok(report.includes('mgu: 10'));
      assert.ok(report.includes('substitute: 5'));
      assert.ok(report.includes('proof:'));
    });

    it('should indicate when disabled', () => {
      const disabled = new Profiler({ enabled: false });
      assert.ok(disabled.report().includes('disabled'));
    });
  });

  describe('global profiler', () => {
    it('should export a singleton instance', () => {
      assert.ok(profiler instanceof Profiler);
    });
  });
});
