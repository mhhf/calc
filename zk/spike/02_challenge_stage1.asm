// Spike 02: Challenge mechanism + stage-1 witnesses
// Tests Q3 partially: can we use challenge() and stage(1) columns?
// Tests Q4: does witness CSV work with stage-1 hint computation?

machine Main with degree: 8 {
    let r: expr = std::prelude::challenge(0, 42);

    col fixed STEP(i) { i };
    col witness x;                    // stage-0: known values
    col witness stage(1) acc;         // stage-1: depends on challenge

    // x is just the step number
    x = STEP;

    // acc = product of (r - x) over all rows so far
    // Row 0: acc = (r - x[0])
    // Row i: acc = acc_prev * (r - x[i])
    col fixed FIRST = [1] + [0]*;
    col fixed LAST(i) { if i == 7 { 1 } else { 0 } };

    // Degree analysis:
    // acc * (r - x') = stage1 * (challenge - stage0) = degree 3 if unconstrained
    // BUT with selector: (1-FIRST)*(1-LAST)*acc*(r-x') = degree 4 → TOO HIGH
    //
    // Solution: materialize the product as intermediate column
    // Then constraint is: (1-FIRST)*(1-LAST)*(acc' - acc_step) = degree 3 (fixed*fixed*stage1)
    col witness stage(1) acc_step;
    acc_step = acc * (r - x');        // degree 3: stage1 * (challenge - stage0)

    FIRST * (acc - (r - x)) = 0;
    (1 - FIRST) * (1 - LAST) * (acc' - acc_step) = 0;  // degree 3: fixed * fixed * stage1
}
