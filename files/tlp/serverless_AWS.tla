--------------------- MODULE rpc ---------------------
EXTENDS Sequences, Integers, TLC
CONSTANTS Messages, Consumers, Producers, MaxGeneration

(*--algorithm rpc
variables
    generation = 1,
    queue = {},
    store = [ m \in Messages |-> 0 ];

define
    QueueInvariant == queue = {} \/ \A m \in queue: (m.message \in Messages /\ m.generation \in Nat)
    Liveness == <>[](\A f \in DOMAIN store: store[f] = generation)
end define

fair process consumer \in Consumers
begin
    Consume:
        await queue /= {};
        with m \in queue do
            either \* read
                queue := queue \ {m};
            or \* read but not delete
                skip;
            end either;
            store[m.message] := m.generation;
        end with; 
        goto Consume
end process;

fair process producer \in Producers
begin
    Publish:
        with m \in Messages do
            queue := queue \union {[message |-> m, generation |-> generation]};
        end with;
        goto Publish
end process;

fair process clock = "clock"
begin
    Tick:
        if generation < MaxGeneration then
            generation := generation + 1;
            goto Tick;
        end if;
end process;
end algorithm; *)
