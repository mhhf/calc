/**
 * Profiler - Performance measurement and statistics
 */

export interface CounterStats {
  [name: string]: number;
}

export interface TimerEntry {
  count: number;
  total: number;
  min: number;
  max: number;
  avg: number;
}

export interface TimerStats {
  [name: string]: TimerEntry;
}

export interface ProfilerStats {
  counters: CounterStats;
  timers: TimerStats;
  elapsed: number;
}

export interface ProfilerOptions {
  enabled?: boolean;
}

/**
 * Performance profiler for tracking operation counts and timing
 */
export class Profiler {
  enabled: boolean;
  counters: CounterStats;
  timers: { [name: string]: { times: number[]; total: number } };
  scopeStack: string[];

  constructor(opts?: ProfilerOptions);

  /**
   * Increment a counter
   */
  count(name: string, amount?: number): void;

  /**
   * Get current counter value
   */
  getCount(name: string): number;

  /**
   * Start timing an operation (returns end function)
   */
  time(name: string): () => number;

  /**
   * Time a synchronous function
   */
  timeSync<T>(name: string, fn: () => T): T;

  /**
   * Enter a named scope
   */
  push(scope: string): void;

  /**
   * Exit current scope
   */
  pop(): string | undefined;

  /**
   * Execute function within a scope
   */
  scope<T>(name: string, fn: () => T): T;

  /**
   * Reset all counters and timers
   */
  reset(): void;

  /**
   * Enable profiling
   */
  enable(): void;

  /**
   * Disable profiling
   */
  disable(): void;

  /**
   * Get current statistics
   */
  stats(): ProfilerStats;

  /**
   * Generate human-readable report
   */
  report(): string;
}

/**
 * Global profiler singleton
 */
export const profiler: Profiler;
