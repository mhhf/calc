// Spike 04c: Bus with recursive stage-1 running sum
// Tests: auto-witgen for recursive stage-1 columns with bus

use std::protocols::bus::bus;
use std::protocols::bus::bus_multi;
use std::protocols::bus::BusInteraction;

machine Main with degree: 8 {
    let r: expr = std::prelude::challenge(0, 42);

    let BUS_ID = 1;

    col fixed STEP(i) { i };
    col fixed IS_SEND = [1, 0, 1, 0, 1, 0, 1, 0];
    col fixed IS_RECV = [0, 1, 0, 1, 0, 1, 0, 1];
    col fixed FIRST = [1] + [0]*;
    col fixed LAST(i) { if i == 7 { 1 } else { 0 } };

    // Running sum: acc = sum of (r + STEP) from row 0 to current row
    // Row 0: acc = r + 0
    // Row i: acc = acc_prev + (r + STEP_i)
    col witness stage(1) acc;

    FIRST * (acc - (r + STEP)) = 0;                              // degree 2
    (1 - FIRST) * (1 - LAST) * (acc' - acc - (r + STEP')) = 0;   // degree 3 (fixed*fixed*stage1)

    // Bus with the running sum
    bus_multi([
        BusInteraction::Send(BUS_ID, [STEP, acc], IS_SEND),
        BusInteraction::Receive(BUS_ID, [STEP, acc], IS_RECV, IS_RECV)
    ]);
}
