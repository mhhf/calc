// Spike 04b: Bus with recursive stage-1 grand product
// Tests: can we compute a recursive grand product (delta_acc) and use it in bus?

use std::protocols::bus::bus;
use std::protocols::bus::bus_multi;
use std::protocols::bus::BusInteraction;
use std::prover::eval;

machine Main with degree: 8 {
    let r: expr = std::prelude::challenge(0, 42);

    let BUS_ID = 1;

    col fixed STEP(i) { i };
    col fixed IS_SEND = [1, 0, 1, 0, 1, 0, 1, 0];
    col fixed IS_RECV = [0, 1, 0, 1, 0, 1, 0, 1];
    col fixed FIRST = [1] + [0]*;
    col fixed LAST(i) { if i == 7 { 1 } else { 0 } };

    // Grand product: delta_acc = product of (r - STEP) from row 0 to current
    // Query function reads previous row's delta_acc
    let delta_acc_query: -> fe = query || {
        let is_first = eval(FIRST);
        let step = eval(STEP);
        let r_val = eval(r);
        if is_first == 1 {
            r_val - step
        } else {
            // Can't read delta_acc here since it's the current row being computed.
            // We need to read from *this* row's value, which isn't set yet.
            // Alternative: use eval on the constraint to compute.
            // Actually, the recursive pattern needs row-by-row computation.
            // The prover processes rows sequentially for stage-1, so prev row should be available.
            // But eval(delta_acc) reads current row. We need the prev row.
            // powdr doesn't seem to support eval(col_prev) directly.
            // Workaround: store the previous value in another column computed via constraint.
            0
        }
    };

    col witness stage(1) delta_acc(i) query Query::Hint(delta_acc_query());

    // Intermediate for degree
    col witness stage(1) delta_step;
    delta_step = delta_acc * (r - STEP');

    FIRST * (delta_acc - (r - STEP)) = 0;
    (1 - FIRST) * (1 - LAST) * (delta_acc' - delta_step) = 0;

    // Bus with stage-1 value
    bus_multi([
        BusInteraction::Send(BUS_ID, [STEP, delta_acc], IS_SEND),
        BusInteraction::Receive(BUS_ID, [STEP, delta_acc], IS_RECV, IS_RECV)
    ]);
}
