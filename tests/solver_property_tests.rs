use crabsat::cnf::cnf::*;
use crabsat::solver::*;
use rand::prelude::*;
use rand::seq::SliceRandom;
use std::collections::HashMap;

// This file involves functions that randomly generate SAT and UNSAT boolean
// formulae and test the solver and parser with them.

const MAX_VARS: u32 = 10;
const MAX_NUM_CLAUSES: u32 = 10;
//const MAX_CLAUSE_SIZE: u32 = MAX_VARS + 1;
const NUM_ITERATIONS: u32 = 50;

/// Randomly generates a CNFFormula.
fn generate_formula() -> CNFFormula {
    let mut rng = rand::thread_rng();
    let num_vars = rng.gen_range(0..MAX_VARS);
    let vars: Vec<u32> = (1..num_vars).collect();
    let num_clauses = rng.gen_range(0..MAX_NUM_CLAUSES);

    let mut clauses = vec![];
    (0..num_clauses).for_each(|_| clauses.push(generate_clause(&vars, &HashMap::new(), None)));
    CNFFormula { clauses }
}

/// Randomly generates a CNFFormula representing a satisfiable boolean formula.
fn generate_sat_formula() -> CNFFormula {
    let mut rng = rand::thread_rng();
    let num_vars = rng.gen_range(0..MAX_VARS);
    let vars: Vec<u32> = (1..num_vars).collect();
    let assignment = generate_assignment(&vars, &mut rng);
    let num_clauses = rng.gen_range(0..MAX_NUM_CLAUSES);

    // SAT => all clauses must evaluate to true
    let mut clauses = vec![];
    (0..num_clauses).for_each(|_| clauses.push(generate_clause(&vars, &assignment, Some(true))));
    CNFFormula { clauses }
}

/// Randomly generates a CNFFormula representing a unsatisfiable boolean formula.
// fn generate_unsat_formula() -> CNFFormula {
//     let mut rng = rand::thread_rng();
//     let num_vars = rng.gen_range(0..MAX_VARS);
//     let vars: Vec<u32> = (1..num_vars).collect();
//     let assignment = generate_assignment(&vars, &mut rng);

//     // UNSAT => at least one clause must evaluate to false
//     // starting from 1 here because an UNSAT CNF formula must have at least one clause
//     let num_clauses = rng.gen_range(1..MAX_NUM_CLAUSES);
//     let num_false_clauses = if num_clauses == 1 {
//         1
//     } else {
//         rng.gen_range(1..num_clauses)
//     };
//     let mut clauses = vec![];

//     (0..num_false_clauses)
//         .for_each(|_| clauses.push(generate_clause(&vars, &assignment, Some(false))));
//     let num_true_clauses = num_clauses - num_false_clauses;
//     if num_true_clauses > 0 {
//         (0..num_true_clauses)
//             .for_each(|_| clauses.push(generate_clause(&vars, &assignment, Some(false))));
//     }
//     CNFFormula { clauses }
// }

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
) -> Clause {
    let mut rng = rand::thread_rng();

    // Choose the subset of variables that will go into the clause
    let mut vars_copy = vars.clone();
    let min_true_vars = if let Some(b) = truth_val {
        if b {
            1
        } else {
            0
        }
    } else {
        0
    };
    let clause_size = if vars.len() > 0 {
        rng.gen_range(min_true_vars..(vars.len() + 1))
    } else {
        0
    };
    if clause_size == 0 {
        return Clause { literals: vec![] };
    }
    vars_copy.shuffle(&mut rng);

    let chosen_vars: Vec<u32> = vars_copy.drain(0..clause_size).collect();

    // Depending on truth_val, create literals from the chosen vars
    let mut literals = vec![];
    let num_true_vars = rng.gen_range(min_true_vars..(clause_size + min_true_vars));
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

    Clause { literals }
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

// #[test]
// fn check_solver_on_unsat_formulae() {
//     (0..NUM_ITERATIONS).for_each(|_| {
//         let unsat_formula = generate_unsat_formula();
//         println!("{}", unsat_formula);
//         let soln = solve(unsat_formula);
//         if soln != SATResult::UNSAT {
//             println!("FAILURE:\n{}", soln);
//         } else {
//             println!("SUCCESS");
//         }
//         println!("");
//         // assert_eq!(solve(unsat_formula), SATResult::UNSAT);
//     });
// }

#[test]
fn sat_formulae_are_satisfiable() {
    (0..NUM_ITERATIONS).for_each(|_| {
        let sat_formula = generate_sat_formula();
        println!("{}", sat_formula);
        let soln = solve(sat_formula);
        match soln {
            SATResult::SAT(_) => assert!(true),
            SATResult::UNSAT => assert!(false),
        }
    })
}
