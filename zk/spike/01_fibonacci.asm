// Spike 01: Basic toolchain validation
// Tests: powdr-cli compile + witness + prove + verify with Goldilocks + plonky3

machine Main with degree: 8 {
    col fixed FIRST = [1] + [0]*;
    col fixed LAST(i) { if i == 7 { 1 } else { 0 } };
    col witness x, y;

    FIRST * (x - 1) = 0;
    FIRST * (y - 1) = 0;
    (1 - FIRST) * (1 - LAST) * (y' - x - y) = 0;
    (1 - FIRST) * (1 - LAST) * (x' - y) = 0;
}
