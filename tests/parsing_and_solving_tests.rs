use crabsat::cnf::cnf::*;
use crabsat::parser::parser::*;
use crabsat::solver::solver::*;
use std::collections::HashMap;

#[test]
fn parse_and_solve_empty_formula() {
    let formula = parse_dimacs_cnf(
        "c
    c empty formula
    c
    p cnf 0 0",
    );
    match formula {
        Err(_) => assert!(false),
        Ok(formula) => assert_eq!(solve(formula), SATResult::SAT(HashMap::new())),
    };
}

#[test]
fn parse_and_solve_formula_with_only_empty_clause() {
    let formula = parse_dimacs_cnf(
        "c
    c empty clause
    c
    p cnf 0 1
    0",
    );
    match formula {
        Err(_) => assert!(false),
        Ok(formula) => assert_eq!(solve(formula), SATResult::UNSAT),
    };
}

#[test]
fn parse_and_solve_formula_with_empty_and_other_clauses() {
    let formula = parse_dimacs_cnf(
        "p cnf 3 4
    1 0
    -2 3 0
    0
    -1 2 0",
    );
    match formula {
        Err(_) => assert!(false, "formula should have parsed correctly"),
        Ok(formula) => assert_eq!(solve(formula), SATResult::UNSAT),
    };
}

#[test]
fn parse_and_solve_formula_with_only_a_unit_clause() {
    let formula = parse_dimacs_cnf(
        "c
    c only has a unit clause
    c
    p cnf 1 1
    -1 0",
    );
    let mut soln = HashMap::new();
    soln.insert(1, false);
    match formula {
        Err(_) => assert!(false),
        Ok(formula) => assert_eq!(solve(formula), SATResult::SAT(soln)),
    };
}

#[test]
fn parse_and_solve_formula_with_multiple_unit_clauses() {
    let formula = parse_dimacs_cnf(
        "c
    c only has a unit clause
    c
    p cnf 3 3
    1 0
    -2 0
    3 0",
    );
    let mut soln = HashMap::new();
    soln.insert(1, true);
    soln.insert(2, false);
    soln.insert(3, true);
    match formula {
        Err(_) => assert!(false),
        Ok(formula) => assert_eq!(solve(formula), SATResult::SAT(soln)),
    };
}

#[test]
fn parse_and_solve_formula_with_one_non_unit_clause() {
    let formula = parse_dimacs_cnf(
        "c
    c only has a non-unit clause
    c
    p cnf 3 1
    1 -2 3 0",
    );
    match formula {
        Err(_) => assert!(false),
        Ok(formula) => match solve(formula) {
            SATResult::UNSAT => assert!(false),
            SATResult::SAT(soln) => {
                assert!(*soln.get(&1).unwrap() || !*soln.get(&2).unwrap() || *soln.get(&3).unwrap())
            }
        },
    }
}

#[test]
fn parse_and_solve_formula_with_contradictory_unit_clauses() {
    let formula = parse_dimacs_cnf(
        "c
  c formula has opposing unit clauses 
  c
  p cnf 1 2
  1 0
  -1 0",
    );
    match formula {
        Err(_) => assert!(false),
        Ok(formula) => assert_eq!(solve(formula), SATResult::UNSAT),
    };
}

#[test]
fn parse_and_solve_non_trivial_unsat_formula() {
    let formula = parse_dimacs_cnf(
        "c
  p cnf 2 4
  1 2 0
  -1 2 0
  1 -2 0
  -1 -2 0",
    );
    match formula {
        Err(_) => assert!(false),
        Ok(formula) => assert_eq!(solve(formula), SATResult::UNSAT),
    };
}

#[test]
fn parse_and_solve_simple_sat_examples() {
    let formula = parse_dimacs_cnf(
        "c
  c simple non-trivial sat example
  c
  p cnf 3 2
  1 -3 0
  2 3 -1 0",
    );
    match formula {
        Err(_) => assert!(false),
        Ok(formula) => match solve(formula) {
            SATResult::UNSAT => assert!(false),
            SATResult::SAT(soln) => {
                assert!(*soln.get(&2).unwrap());
                assert!(*soln.get(&1).unwrap() || !*soln.get(&3).unwrap());
            }
        },
    };
}
