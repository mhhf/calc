// Spike 04: Bus with stage-1 value in tuple
// Tests Q1: Can bus_send accept stage-1 column expressions as tuple elements?
// This is the critical test for BRANCH_BUS (delta save/restore).
//
// Pattern: save a grand product value (stage-1) via bus, then receive it back
// and verify it matches.

use std::protocols::bus::bus;
use std::protocols::bus::bus_multi;
use std::protocols::bus::BusInteraction;
use std::prover::eval;

machine Main with degree: 8 {
    let r: expr = std::prelude::challenge(0, 42);

    let BUS_ID = 1;

    col fixed STEP(i) { i };
    col fixed IS_SAVE = [1, 0, 0, 0, 1, 0, 0, 0];    // save at rows 0, 4
    col fixed IS_RESTORE = [0, 0, 0, 1, 0, 0, 0, 1];  // restore at rows 3, 7

    // Stage-1 value: grand product of (r - i)
    // Needs explicit query function so bus can eval() it
    col fixed FIRST = [1] + [0]*;
    col fixed LAST(i) { if i == 7 { 1 } else { 0 } };

    // Query function computes delta_acc for witness generation
    let delta_acc_hint: -> fe = query || {
        let step = eval(STEP);
        let r_val = eval(r);
        if step == 0 {
            r_val - step
        } else {
            eval(delta_acc) * (r_val - step)
        }
    };

    col witness stage(1) delta_acc(i) query Query::Hint(delta_acc_hint());

    // Intermediate to keep degree ≤ 3
    col witness stage(1) delta_step;
    delta_step = delta_acc * (r - STEP');     // degree 3: stage1 * (challenge - fixed)

    FIRST * (delta_acc - (r - STEP)) = 0;
    (1 - FIRST) * (1 - LAST) * (delta_acc' - delta_step) = 0;  // degree 3

    // The KEY question: can we put delta_acc (stage-1) in a bus tuple?
    col fixed SEND_NONCE = [0, 0, 0, 0, 1, 0, 0, 0];
    col fixed RESTORE_NONCE = [0, 0, 0, 0, 0, 0, 0, 1];

    bus_multi([
        BusInteraction::Send(BUS_ID, [SEND_NONCE, delta_acc], IS_SAVE),
        BusInteraction::Receive(BUS_ID, [RESTORE_NONCE, delta_acc], IS_RESTORE, IS_RESTORE)
    ]);
}
