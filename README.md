# CrabSAT

This is an implementation of the DPLL (Davis–Putnam–Logemann–Loveland) algorithm for deciding the satisfiability of a boolean formula in conjunctive normal form (CNF). I'm using this project as a way to learn Rust! 

## Features

I hope to build this out with time, both to include more solving/explainability features and to improve its user interface. Here are some things I have in mind:

- [x] Creating representations for literals, clauses, and CNF formulae.
- [x] Implementing a solving algorithm based on pure literal elimination and unit clause propagation.
- [x] Writing a parser that takes in boolean formulae in string form via the DIMACS CNF format and converts them to the internal representation of CNF formulae.
- [ ] Writing a CLI to feed in such formulae manually and via files and produce solutions as output.
- [ ] Adding more explainability features like UNSAT cores!
- [ ] Packaging this in a more reproducible way.
- [ ] Investigating what an 'optimal' UNSAT core is, in terms of explainability, and implementing an algorithm to generate such cores based on user input. 
