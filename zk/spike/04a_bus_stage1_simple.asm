// Spike 04a: Simplified bus with stage-1 value
// Isolate Q1: stage-1 column in bus tuple, no recursive computation

use std::protocols::bus::bus;
use std::protocols::bus::bus_multi;
use std::protocols::bus::BusInteraction;

machine Main with degree: 8 {
    let r: expr = std::prelude::challenge(0, 42);

    let BUS_ID = 1;

    col fixed STEP(i) { i };
    col fixed IS_SEND = [1, 0, 1, 0, 1, 0, 1, 0];
    col fixed IS_RECV = [0, 1, 0, 1, 0, 1, 0, 1];

    // Simple stage-1 column: just r * STEP (no recursion)
    col witness stage(1) val;
    val = r * STEP;    // degree 2: challenge * fixed, can be solved algebraically

    // Send and receive the same (STEP, val) pairs
    bus_multi([
        BusInteraction::Send(BUS_ID, [STEP, val], IS_SEND),
        BusInteraction::Receive(BUS_ID, [STEP, val], IS_RECV, IS_RECV)
    ]);
}
