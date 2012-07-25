This is a pure Haskell implementation of Datalog, as a library

Datalog is a logic language that allows for recursive database
queries.  This implementation is distinguished from many others in
that it is embeddable as a library in other (Haskell) programs.  A
driver program that operates on textual input is also planned.

It is currently just a semi-naive evaluator, but it is reasonably
efficient.  The implementation is currently in its early stages
but it seems to produce reasonably correct results.  See the
test suite for some details.

## Planned Enhancements

 * Magic sets transformation
 * Optional BDD backend for a subset of queries
