module AsynchronousInterface {
    type DATA_TYPE = int
    pure val DATA_VALUES = 1.to(10)

    // Channel record with value, ready bit, and acknowledge bit
    type Chan = {
        value: DATA_TYPE,
        rdy: bool,
        ack: bool
    }

    var chan: Chan

    // Initial state: ready and ack bits are equal
    action init = {
        nondet value = oneOf(DATA_VALUES)
        nondet flag = oneOf(Bool)
        all {
            chan' = { value: value, rdy: flag, ack: flag }
        }
    }

    // Send action: when ack equals rdy, send data and flip rdy
    action Send(value: DATA_TYPE): bool = all {
        chan.ack == chan.rdy,
        chan' = { value: value, rdy: not(chan.rdy), ...chan }
    }

    // Receive action: when ack doesn't equal rdy, flip ack
    action Recv = all {
        chan.ack != chan.rdy,
        chan' = { ack: not(chan.ack), ...chan }
    }

    // Next state relation
    action step = {
        nondet d = oneOf(DATA_VALUES)
        any {
            Send(d),
            Recv
        }
    }
}