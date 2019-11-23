# Examples

Synthetic examples created to test and explain
certain features of our verification formalism
and algorithms.


## multi-0

Multi-cycle unit that accepts a value when `start = 1` and
after 1...N cycles sets `done = 1` at which point the output
can be read.
There is no way to delay reading the _result_.
