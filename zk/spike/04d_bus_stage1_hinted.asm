// Spike 04d: Bus with stage-1 value + explicit hint
// Tests: does Query::Hint for stage-1 get computed before bus eval?

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

    // Hinted stage-1 with constraint (not direct equality)
    let acc_hint: -> fe = query || {
        let step = eval(STEP);
        let r_val = eval(r);
        r_val * step + r_val * r_val
    };

    col witness stage(1) acc(i) query Query::Hint(acc_hint());
    // Constrain acc to expected value (not direct equality to avoid optimizer conflict)
    (acc - r * STEP - r * r) = 0;

    // Bus with hinted stage-1 value
    bus_multi([
        BusInteraction::Send(BUS_ID, [STEP, acc], IS_SEND),
        BusInteraction::Receive(BUS_ID, [STEP, acc], IS_RECV, IS_RECV)
    ]);
}
