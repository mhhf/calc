// Spike 03: Basic bus send/receive
// Tests Q1 (partial): does bus_send/bus_receive work with plonky3?
// Tests: bus balance across same namespace

use std::protocols::bus::bus;
use std::protocols::bus::bus_multi;
use std::protocols::bus::BusInteraction;

machine Main with degree: 8 {
    let BUS_ID = 1;

    // Fixed values: send (key, value) pairs on even rows, receive on odd rows
    col fixed KEY   = [10, 10, 20, 20, 30, 30, 40, 40];
    col fixed VALUE = [11, 11, 22, 22, 33, 33, 44, 44];
    col fixed IS_SEND = [1, 0, 1, 0, 1, 0, 1, 0];
    col fixed IS_RECV = [0, 1, 0, 1, 0, 1, 0, 1];

    // Send on even rows, receive on odd rows
    // Bus should balance: 4 sends = 4 receives with matching (key, value)
    bus_multi([
        BusInteraction::Send(BUS_ID, [KEY, VALUE], IS_SEND),
        BusInteraction::Receive(BUS_ID, [KEY, VALUE], IS_RECV, IS_RECV)
    ]);
}
