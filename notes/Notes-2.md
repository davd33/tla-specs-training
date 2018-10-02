Time, Clocks and the ordering of Events in a distributed system - Notes
===

Find the full article from Leslie Lamport [here](https://lamport.azurewebsites.net/pubs/time-clocks.pdf).



> The concept of the temporal ordering of events pervades our thinking about systems.

A distributed system consists of a collection of distinct processes which are spatially separated, and which communicate with one another by exchanging messages.

A system is distributed if the message transmission delay isn’t negligible compared to the time between events in a single process.

> **In a distributed system, it is sometimes impossible to say that one of two events occurred first: the relation “happened before” is therefore only a partial ordering of the events in the system.**



## The Partial Ordering

### It happened before

_The relation “happened before” (“→”) is defined here without using physical clocks._

**Definition:** The relation “→” on the set of events of a system is the smallest relation satisfying the following three conditions:

 1. If _a_ and _b_ are events in the same process, and _a_ comes before _b_, then _a → b_.
 2. If _a_ is the sending of a message by one process and _b_ is the receipt of the <u>same</u> message by another process, then _a → b_.
 3. If _a → b_ and _b → c_, then _a → c_.

When _a → b_: it is possible that _a_ *causally affect* _b_.

Two distinct events _a_ and _b_ are said to be concurrent if _a /→ b_ (_/→_ meaning “does not happen before”) and _b /→ a_* Two events are concurrent if neither can causally affect the other.

We assume that _a /→ a_ for any event _a_, so that “→” is an irreflexive partial ordering on the set of all events in the system.

> We should be able to determine if a system performed correctly by knowing only those events which did occur, without knowing which events could have occurred.



### The clock

We define a clock _C<sub>i</sub>_ for each process _P<sub>i</sub>_ to be a function _C_ which assigns a number _C<sub>i</sub>(a)_ to any event _a_ in that process.

The entire system of clocks is represented by the function _C_ which assigns to any event _b_ the number _C(b)_, where _C(b) = C<sub>j</sub>(b)_ if _b_ is an event in process _P<sub>j</sub>_.

**Clock condition:** For any events _a, b_: if _a → b_ then _C(a) < C(b)_.

The converse condition do not hold!

The clock condition is satisfied if the following two conditions hold:

1. If _a_ and _b_ are events in process _P<sub>i</sub>_, and _a → b_, then _C<sub>i</sub>(a) < C<sub>i</sub>(b)_.
2. If _a_ is the sending of a message by process _P<sub>i</sub>_ and _b_ is the receipt of that message by process _P<sub>j</sub>_, then _C<sub>i</sub>(a) < C<sub>j</sub>(b)_.

