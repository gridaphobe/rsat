`rsat`
======

A toy SAT solver in Rust, for reasons.

## `cnf` function

The `cnf` function is a new addition to the `Term` struct. It converts a `Term` into a CNF formula (`cnf::Formula`). This function allows for the conversion of logical expressions into Conjunctive Normal Form (CNF), which is a standard form used in SAT solvers. The `cnf` function supports various logical operations such as `Lit`, `Var`, `Not`, `And`, and `Or`.
