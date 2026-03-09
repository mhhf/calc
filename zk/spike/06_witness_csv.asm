// Spike 06: External witness CSV
// Tests Q4: Can we provide witness values via CSV file?
// And does stage-0 witness CSV get processed before stage-1 hint computation?
//
// Pattern: provide x values externally, compute stage-1 acc from challenge + x.

machine Main with degree: 8 {
    let r: expr = std::prelude::challenge(0, 42);

    col fixed STEP(i) { i };
    col fixed FIRST = [1] + [0]*;
    col fixed LAST(i) { if i == 7 { 1 } else { 0 } };
    col witness x;                    // stage-0: provided via CSV
    col witness stage(1) acc;         // stage-1: depends on challenge + x

    // acc = product of (r - x) over rows
    // Intermediate to keep degree ≤ 3
    col witness stage(1) acc_step;
    acc_step = acc * (r - x');

    FIRST * (acc - (r - x)) = 0;
    (1 - FIRST) * (1 - LAST) * (acc' - acc_step) = 0;
}
