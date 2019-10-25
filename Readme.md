# serv-formal

Transactional verification prototype repo.

**TODO**: rename to something more generic since we might be
          verifying more than just the serv processor

## Dependencies

The python scripts assume a number of programs top be installed.

### Yosys

Used to read Verilog designs and convert them to SMT2, BTOR2, ILANG and
single-file Verilog.
Use a recent version from: https://github.com/YosysHQ/yosys

### Verilator

Used to sanitiy check witnesses returned by the model checker.
I.e. we create a simulation and apply initial state + inputs to
generate a more reliable VCD file.

On Fedora Linux, just install the verilator package.

https://www.veripool.org/wiki/verilator


### Yices2

We currently use yices as an SMT solver (`smt2.py`).

On Fedora Linux, just install the yices package.


https://github.com/SRI-CSL/yices2


### Boolector Model Checker

As an alternative to using an SMT2 solver we also make use
of a word level model checker (`mc.py`).
Currently this checker is the `btormc` binary supplied with boolector.

https://github.com/Boolector/boolector


### GTKWave

Not strictly needed by the tool. However this open-source program
is useful for looking at VCD traces generated as witnesses to failing
checks.
