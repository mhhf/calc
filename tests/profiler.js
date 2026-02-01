const { Profiler, profiler } = require('../lib/profiler');
const should = require('chai').should();

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
      p.stats().counters.mgu.should.equal(2);
      p.stats().counters.substitute.should.equal(1);
    });

    it('should support custom amounts', () => {
      p.count('nodes', 5);
      p.count('nodes', 3);
      p.stats().counters.nodes.should.equal(8);
    });

    it('should return 0 for uncounted operations', () => {
      p.getCount('nonexistent').should.equal(0);
    });
  });

  describe('timers', () => {
    it('should time operations', (done) => {
      const end = p.time('mgu');
      setTimeout(() => {
        end();
        const timer = p.stats().timers.mgu;
        timer.count.should.equal(1);
        timer.total.should.be.greaterThan(0);
        done();
      }, 10);
    });

    it('should track multiple calls', () => {
      for (let i = 0; i < 5; i++) {
        const end = p.time('fast_op');
        end();
      }
      const timer = p.stats().timers.fast_op;
      timer.count.should.equal(5);
    });

    it('should track min/max/avg', () => {
      const end1 = p.time('op');
      end1();
      const end2 = p.time('op');
      end2();

      const timer = p.stats().timers.op;
      timer.count.should.equal(2);
      timer.min.should.be.at.most(timer.max);
      timer.avg.should.equal(timer.total / timer.count);
    });

    it('should support timeSync for synchronous functions', () => {
      const result = p.timeSync('compute', () => {
        let sum = 0;
        for (let i = 0; i < 1000; i++) sum += i;
        return sum;
      });
      result.should.equal(499500);
      p.stats().timers.compute.count.should.equal(1);
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

      p.stats().counters['branch1.mgu'].should.equal(1);
      p.stats().counters['branch2.mgu'].should.equal(1);
    });

    it('should support deep nesting', () => {
      p.push('a');
      p.push('b');
      p.count('op');
      p.pop();
      p.pop();

      p.stats().counters['a/b.op'].should.equal(1);
    });

    it('should support scope() helper', () => {
      const result = p.scope('myScope', () => {
        p.count('inner');
        return 42;
      });
      result.should.equal(42);
      p.stats().counters['myScope.inner'].should.equal(1);
    });
  });

  describe('enable/disable', () => {
    it('should be disabled by default (without env var)', () => {
      const disabled = new Profiler({ enabled: false });
      disabled.count('mgu');
      disabled.stats().counters.should.deep.equal({});
    });

    it('should do nothing when disabled', () => {
      const disabled = new Profiler({ enabled: false });
      disabled.count('mgu');
      const end = disabled.time('op');
      end();
      disabled.stats().counters.should.deep.equal({});
      disabled.stats().timers.should.deep.equal({});
    });

    it('should enable on demand', () => {
      const p2 = new Profiler({ enabled: false });
      p2.count('before');
      p2.enable();
      p2.count('after');
      p2.stats().counters.should.not.have.property('before');
      p2.stats().counters.after.should.equal(1);
    });
  });

  describe('reset', () => {
    it('should clear all data', () => {
      p.count('mgu');
      const end = p.time('op');
      end();
      p.reset();
      p.stats().counters.should.deep.equal({});
      p.stats().timers.should.deep.equal({});
    });
  });

  describe('report', () => {
    it('should generate readable report', () => {
      p.count('mgu', 10);
      p.count('substitute', 5);
      const end = p.time('proof');
      end();

      const report = p.report();
      report.should.include('CALC Profiler Report');
      report.should.include('mgu: 10');
      report.should.include('substitute: 5');
      report.should.include('proof:');
    });

    it('should indicate when disabled', () => {
      const disabled = new Profiler({ enabled: false });
      disabled.report().should.include('disabled');
    });
  });

  describe('global profiler', () => {
    it('should export a singleton instance', () => {
      profiler.should.be.instanceOf(Profiler);
    });
  });
});
