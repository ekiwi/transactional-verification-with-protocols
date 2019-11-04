# Transaction Spec

A Transaction Spec specifies the behavior of a RTL module.
It can be used to verify that the module behaves as expected
as well as that a module instance is used correctly.
Thus the spec enables assume guarantee reasoning for RTL.

Some properties are:
- transaction specs can be incomplete,
  the user only needs to specify the behavior other modules depend on
- our modle checking algorithm results in a counter example or an inductive "proof"
- transactions can be combined or split up, there is some user freedom in chosing how
  exactly to model the module




## Transaction

A transaction is essentially a multi-input, multi-output method.
It can read and modify architectural state.



## Architectural State


## Protocol




## Model Abstraction for Compositional Model Checking
- _idea_: combine all transactions into automaton
- most transactions should have a very small common prefix
  --> more efficient checking if this is the case
- if common prefix not only has the same inputs but also the same outputs
  --> we can merge the states in our automaton (only one state to track now!)
- once the inputs are driven such that there is no matching state
  --> violated transaction interface!


### Spurious Counter Examples
- normally abstractions have problems with spurious counter examples
  if not carefully chosen
- what is the nature of counter examples in our system?
- it seems like the spurious counter example would consist of
  triggering a transaction that is not specified or relying on
  an output that is left unspecified
- is this fundamentally diferent from other approached?
- is it easier to understand?


## Combinatorial Loops

There are multiple sound approaches to tackling the problem of combinatorial
loops. Some are more precise, thus allowing us to verify more circuits, but are
harder to check.

In general it seems that if we can prove for the whole (combined) design that
there are no combinatorial loops (which most RTL synthesis tools do anyways),
we can just ignore any worries about circular reasoning. TODO: show a little
more convincingly that this is actually true.

Some points in the design space:

### Static Combinatorial Loop Checking

Run a conservative static check to see which outputs of the
implementation depend directly on the inputs.
This information can than be used when doing compositional
checking in that the static dependencies tell us which outputs
can be assumed in order to prove correct input values.


### Transaction Specific Combinatorial Dependencies

When checking the transaction, we check at every transition
which output depends on which input.
Thus instead of generic static dependencies we get transaction
specific dependencies. This allows more assumptions on the
module outputs in order to prove other inputs.

### Transaction Specific Combinatorial Dependencies with Case Splitting

Finds the exact formula under which an output depends on an input.
This could cover even more cases but is hopelessly over complicated.


## Todo:
- check for causality:
  - this is important for compositional model checking
  - essentially we need to make sure that module outputs
    only depend on inputs from the present or past
  - when we verify a spec non-causality should automatically fail
  - it might still be interesting to have a separate check to
    alert the user that their spec is impossible to fulfill
- reset should be modeled as transaction that starts the model,
  i.e., the language is (`RT*`)


## Open Questions
- how do we deal with concurrent / overlapping transactions
- do we need to include combinational paths in our spec?
  how do we ensure ansence of combinatorial loops?
  an example would be nice
- do we need "rules" in addition to "methods"?
  I.e. currently our components only act when promted to do so
  from the outside, however, at some point they might have to act
  on their own.
- do we need to add precondition support for transactions?
- should the input/output mapping support functions that are not direct bit-to-bit mappings?
- should the input/output mapping functions be required to be bijective?
- how do we test for bijectivity?
- what about the architectural state mapping function? also bijective?
