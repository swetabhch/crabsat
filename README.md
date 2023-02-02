# CrabSAT

This project started out as an implementation of the [DPLL (Davis–Putnam–Logemann–Loveland)](https://www.wikiwand.com/en/DPLL_algorithm) algorithm for deciding the satisfiability of a boolean formula in conjunctive normal form (CNF). Hopefully, it will evolve into a more general suite of [SAT solvers](https://www.wikiwand.com/en/SAT_solver) that give users more informative output than they could get from just DPLL! I'm using this project as a way to learn Rust, and it's been really fun so far.

At present, the main function this serves is as a DPLL SAT-solver. It takes in a formula in DIMACS CNF format and outputs whether or not the formula encoded in the input file is satisfiable. If it is, it also returns an assignment of variables that satisfies it!

## Usage

Run the solver by entering the command `./run.sh <file>` in your command line! This runs it with the release profile, which would be faster than the alternative, which is `cargo run <file>`. The latter runs with more helpful debugging hints on!

Use `cargo test` to test this code! Unit tests live across most files in `src/` and some deeper tests and integration tests live in `tests/`. There is also a `examples/` directory for you to try `./run.sh` out with, and to see examples of formulae in the CNF DIMACS format.

## Features

- A DPLL implementation that uses pure literal elimination and unit clause propagation.
- A variable-picking heuristic within DPLL that prevents [heavy-tailed behavior](https://www.semanticscholar.org/paper/Heavy-Tailed-Phenomena-in-Satisfiability-and-Gomes-Selman/6eb44d3238bcab0b0b7ad634288a49787b84abde). This *dramatically* improves performance and reduces stack-overflows! 
- A testing oracle to check satisfiable formulae. (This admittedly needs to have stronger checks.)
- A (relatively-barebones) CNF module with useful structs!

## The shape of things to come

I hope to build this out with time, both to include more solving/explainability features and to improve its user interface. Here are some things I have in mind:

- [ ] Packaging optimizations in their own, single struct, and taking in command line flags to enable/disable them.
- [ ] Implementing a [conflict-driven clause learning (CDCL)](https://www.wikiwand.com/en/Conflict-driven_clause_learning#Algorithm) based solver.
- [ ] Using the CDCL to add more explainability features like [UNSAT cores](https://www.wikiwand.com/en/Unsatisfiable_core)!
- [ ] Investigating what an 'optimal' UNSAT core is, in terms of explainability, and implementing an algorithm to generate such cores based on user input. 
