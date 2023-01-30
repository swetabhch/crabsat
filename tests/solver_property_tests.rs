use crabsat::cnf::cnf::*;
use crabsat::parser::parser::*;
use crabsat::solver::solver::*;
use rand::prelude::*;
use rand::seq::SliceRandom;
use std::cmp;
use std::collections::HashMap;
use thiserror::Error;

// This file involves functions that randomly generate SAT boolean
// formulae and test the solver and parser with them.

const MAX_VARS: u32 = 100;
const MAX_NUM_CLAUSES: u32 = 100;
const NUM_ITERATIONS: u32 = 100;

#[derive(Debug, Error)]
enum TestError {
    #[error("cannot generate a true clause error given no variables")]
    NoVariables,
}

/// Randomly generates a CNFFormula.
fn generate_formula() -> CNFFormula {
    let mut rng = rand::thread_rng();
    let num_vars = rng.gen_range(0..MAX_VARS);
    let vars: Vec<u32> = (1..num_vars).collect();
    let num_clauses = rng.gen_range(0..MAX_NUM_CLAUSES);

    let mut clauses = vec![];
    (0..num_clauses)
        .for_each(|_| clauses.push(generate_clause(&vars, &HashMap::new(), None).unwrap()));
    CNFFormula { clauses }
}

/// Randomly generates a CNFFormula representing a satisfiable boolean formula.
fn generate_sat_formula() -> CNFFormula {
    let mut rng = rand::thread_rng();
    let num_clauses = rng.gen_range(0..MAX_NUM_CLAUSES);
    if num_clauses == 0 {
        return CNFFormula { clauses: vec![] };
    }
    let num_vars = rng.gen_range(1..MAX_VARS);
    let vars: Vec<u32> = (1..(num_vars + 1)).collect();
    let assignment = generate_assignment(&vars, &mut rng);

    // SAT => all clauses must evaluate to true
    let mut clauses = vec![];
    (0..num_clauses)
        .for_each(|_| clauses.push(generate_clause(&vars, &assignment, Some(true)).unwrap()));
    CNFFormula { clauses }
}

/// Converts a clause into DIMACS CNF format, eg. "1 -3 4 0\n"
fn clause_to_dimacs(clause: &Clause) -> String {
    let mut clause_str = String::new();
    clause.literals.iter().for_each(|l| {
        clause_str.push_str(&l.to_string());
        clause_str.push_str(" ");
    });
    clause_str.push_str("0\n");
    clause_str
}

/// Randomly generates a string literal of a CNF formula, in DIMACS format,
/// representing a satisfiable boolean formula.
fn generate_sat_formula_dimacs() -> String {
    let mut rng = rand::thread_rng();
    let num_clauses = rng.gen_range(0..MAX_NUM_CLAUSES);
    if num_clauses == 0 {
        return String::from("p cnf 0 0");
    }
    let num_vars = rng.gen_range(1..MAX_VARS);
    let vars: Vec<u32> = (1..(num_vars + 1)).collect();
    let assignment = generate_assignment(&vars, &mut rng);

    // SAT => all clauses must evaluate to true
    let mut clauses = vec![];
    (0..num_clauses)
        .for_each(|_| clauses.push(generate_clause(&vars, &assignment, Some(true)).unwrap()));
    let mut formula_str = String::from(format!("p cnf {} {}\n", num_vars, num_clauses));
    clauses
        .iter()
        .for_each(|c| formula_str.push_str(&clause_to_dimacs(c)));
    formula_str
}

/// Short helper to convert from a boolean value to a corresponding sign.
fn bool_to_sign(bool_value: bool) -> Sign {
    if bool_value {
        Sign::Positive
    } else {
        Sign::Negative
    }
}

/// Randomly generates a Clause, given a list of variables to choose from.
/// If truth_val is not None, this function assumes that every var in vars
/// has a corresponding assignment.
fn generate_clause(
    vars: &Vec<u32>,
    assignment: &HashMap<u32, bool>,
    truth_val: Option<bool>,
) -> Result<Clause, TestError> {
    // Error if a true clause is expected but `vars` is empty
    if vars.is_empty() && truth_val == Some(true) {
        return Err(TestError::NoVariables);
    }

    let mut rng = rand::thread_rng();

    // Choose the subset of variables that will go into the clause
    let mut vars_copy = vars.clone();
    let min_true_vars = if truth_val == Some(true) { 1 } else { 0 };

    let clause_size = if vars.len() > 0 {
        rng.gen_range(min_true_vars..(cmp::max(vars.len(), min_true_vars) + 1))
    } else {
        0
    };
    if clause_size == 0 {
        return Ok(Clause { literals: vec![] });
    }

    // Choose a random subset of variables to include in the clause
    vars_copy.shuffle(&mut rng);
    let chosen_vars: Vec<u32> = vars_copy.drain(0..clause_size).collect();

    // Depending on truth_val, create literals from the chosen vars
    let mut literals = vec![];
    let num_true_vars = rng.gen_range(min_true_vars..(clause_size + 1));
    let true_vars: Vec<u32> = chosen_vars
        .choose_multiple(&mut rng, num_true_vars)
        .cloned()
        .collect();
    for var in chosen_vars {
        let sign = match truth_val {
            None => bool_to_sign(rng.gen_bool(0.5)),
            Some(truth) => {
                // Assuming that assignment contains var
                let assigned_val = *assignment.get(&var).unwrap();
                if truth && true_vars.contains(&var) {
                    bool_to_sign(assigned_val)
                } else if truth {
                    bool_to_sign(rng.gen_bool(0.5))
                } else {
                    bool_to_sign(!assigned_val)
                }
            }
        };
        literals.push(Literal::new(var, sign));
    }

    Ok(Clause { literals })
}

/// Given a list of variables, this generates an assignment mapping each of them to a
/// true or false value.
fn generate_assignment(vars: &Vec<u32>, rng: &mut ThreadRng) -> HashMap<u32, bool> {
    let mut assignment = HashMap::new();
    for var in vars {
        assignment.insert(*var, rng.gen_bool(0.5));
    }
    assignment
}

#[test]
fn solve_satisfiable_formulae() {
    (0..NUM_ITERATIONS).for_each(|_| {
        let sat_formula = generate_sat_formula();
        //println!("{}", sat_formula);
        let soln = solve(sat_formula);
        match soln {
            SATResult::SAT(_) => assert!(true),
            SATResult::UNSAT => assert!(false),
        }
    })
}

#[test]
fn parse_and_solve_satisfiable_formulae() {
    (0..NUM_ITERATIONS).for_each(|_| {
        let sat_formula_dimacs = generate_sat_formula_dimacs();
        let sat_formula = parse_dimacs_cnf(&sat_formula_dimacs).unwrap();
        let soln = solve(sat_formula);
        match soln {
            SATResult::SAT(_) => assert!(true),
            SATResult::UNSAT => assert!(false),
        }
    })
}
