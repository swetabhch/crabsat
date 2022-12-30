mod cnf;

// For learning purposes, I'm going to try to implement this without giving Clause the Copy trait.
// TODO: this file is becoming somewhat unwieldy with all the tests being grouped here.
//   -> Think about rearrangement?

pub mod solver {
    use super::cnf::cnf::*;
    use std::collections::{HashMap, HashSet};

    /// The core of the solver's functionality. This function
    /// returns SAT with a satisfying assignment for the input formula
    /// if such an assignment exists, else returns UNSAT.
    /// Returns full assignments, not partial ones, where variables are
    /// by default set to false.
    pub fn solve(formula: CNFFormula) -> SATResult {
        let assignment: HashMap<u32, bool> = HashMap::new();
        let vars = get_vars_from_formula(&formula);
        match solve_with_assignment(formula, assignment, &vars) {
            None => SATResult::UNSAT,
            Some(mut assignment) => {
                for var in vars {
                    if !assignment.contains_key(&var) {
                        assignment.insert(var, false);
                    }
                }
                SATResult::SAT(assignment)
            }
        }
    }

    /// Returns the variables present in a formula.
    /// TODO: test this.
    fn get_vars_from_formula(formula: &CNFFormula) -> Vec<u32> {
        let mut vars = HashSet::new();
        for clause in &formula.clauses {
            for literal in &clause.literals {
                vars.insert(literal.name);
            }
        }
        let var_vec = vars.into_iter().collect();
        var_vec
    }

    /// Recursively tries to find a satisfying truth assignment for a given formula
    /// given the current assignment. Returns an option containing a satisfying (partial)
    /// assignment if such an assignment exists, else returns None.
    fn solve_with_assignment<'a>(
        formula: CNFFormula,
        mut assignment: HashMap<u32, bool>,
        vars: &Vec<u32>,
    ) -> Option<HashMap<u32, bool>> {
        // Unit clause and pure literal elimination
        let formula = eliminate_unit_clauses(&formula, &mut assignment);
        let formula = eliminate_pure_literals(&formula, &mut assignment, vars);
        // Check for empty formulae and clauses
        if formula.clauses.iter().any(|c| c.literals == vec![]) {
            return None;
        }
        if formula.clauses == vec![] {
            return Some(assignment);
        }

        // Choose any variable to assign / backtrack on
        // Assumption: the earlier checks ensure that there is a first element in `vars`.
        let var = vars.first().unwrap();

        let mut pos_clauses = formula.clauses.clone();
        let mut pos_assignment = assignment.clone();
        propagate_unit_literal(
            Literal {
                name: *var,
                sign: Sign::Positive,
            },
            &mut pos_clauses,
            &mut pos_assignment,
        );
        let pos_result = solve_with_assignment(
            CNFFormula {
                clauses: pos_clauses,
            },
            pos_assignment,
            vars,
        );
        match pos_result {
            Some(assignment_ref) => Some(assignment_ref),
            None => {
                let mut neg_clauses = formula.clauses.clone();
                let mut neg_assignment = assignment.clone();
                propagate_unit_literal(
                    Literal {
                        name: *var,
                        sign: Sign::Negative,
                    },
                    &mut neg_clauses,
                    &mut neg_assignment,
                );
                solve_with_assignment(
                    CNFFormula {
                        clauses: neg_clauses,
                    },
                    neg_assignment,
                    vars,
                )
            }
        }
    }

    /// Performs unit clause propagation on a formula for each unit clause and
    /// returns the formula remaining after propagation.
    /// Side effect: mutates the assignment mapping according to the unit prop process.
    fn eliminate_unit_clauses(
        formula: &CNFFormula,
        assignment: &mut HashMap<u32, bool>,
    ) -> CNFFormula {
        let mut edited_clauses = formula.clauses.clone();
        // Find a unit clause (if none, do not loop; return inp formula).
        while let Some(clause_ref) = get_first_unit_clause(&edited_clauses) {
            // We know this clause will have length 1, so we unwrap here.
            let unit_literal = clause_ref.literals.first().unwrap().clone();
            propagate_unit_literal(unit_literal, &mut edited_clauses, assignment);
        }

        CNFFormula {
            clauses: edited_clauses,
        }
    }

    /// Perform unit propagation given a literal to propagate. Updates clauses, assignment
    /// as a side effect.
    fn propagate_unit_literal(
        literal: Literal,
        clauses: &mut Vec<Clause>,
        assignment: &mut HashMap<u32, bool>,
    ) -> () {
        // Change assignment according to literal.
        assign_literal_to_true(&literal, assignment);
        let mut clauses_to_remove = Vec::new();
        // TODO: see if there's a better way to do this than just cloning clauses.
        for clause in clauses.clone() {
            if clause.literals.contains(&literal) {
                clauses_to_remove.push(clause);
            }
        }
        // Drop all clauses that contain the literal.
        clauses.retain(|c| !clauses_to_remove.contains(c));
        // Remove the negated version of this literal from the remaining clauses.
        for clause in clauses {
            let opposite_sign = match literal.sign {
                Sign::Positive => Sign::Negative,
                Sign::Negative => Sign::Positive,
            };
            let negated_literal = Literal {
                name: literal.name,
                sign: opposite_sign,
            };
            if clause.literals.contains(&negated_literal) {
                clause.literals.retain(|l| *l != negated_literal);
            }
        }
    }

    /// If a literal has positive parity, sets the variable to true in the assignment.
    /// Else, sets the variable to false.
    fn assign_literal_to_true(literal: &Literal, assignment: &mut HashMap<u32, bool>) -> () {
        match literal.sign {
            Sign::Positive => assignment.insert(literal.name, true),
            Sign::Negative => assignment.insert(literal.name, false),
        };
    }

    /// Performs pure literal elimination on a formula and returns the formula that remains.
    /// Side effect: mutates the assignment mapping according to the pure literal elim process.
    /// TODO: Decide where we get variable names from. For now: take it in as input.
    fn eliminate_pure_literals(
        formula: &CNFFormula,
        assignment: &mut HashMap<u32, bool>,
        variables: &Vec<u32>,
    ) -> CNFFormula {
        let mut edited_clauses = formula.clauses.clone();
        let mut pure_literal_found = true;
        while pure_literal_found {
            pure_literal_found = false;
            for name in variables {
                let pure_lit_opt = var_has_pure_literal(&edited_clauses, *name);
                match pure_lit_opt {
                    None => continue,
                    Some(pure_lit) => {
                        assign_literal_to_true(&pure_lit, assignment);
                        edited_clauses.retain(|c| !c.literals.contains(&pure_lit));
                        pure_literal_found = true;
                    }
                }
            }
        }

        CNFFormula {
            clauses: edited_clauses,
        }
    }

    /// Determines whether a variable corresponds to a pure literal in the given vector of clauses,
    /// i.e. has the same parity throughout the formula. If so, returns an Option containing
    /// the literal. If not, returns None.
    fn var_has_pure_literal(clauses: &Vec<Clause>, name: u32) -> Option<Literal> {
        let mut pos_is_pure = true;
        let mut neg_is_pure = true;
        let mut pos_encountered = false;
        let mut neg_encountered = false;
        for clause in clauses {
            for literal in &clause.literals {
                if literal.name == name {
                    match literal.sign {
                        Sign::Positive => {
                            neg_is_pure = false;
                            pos_encountered = true
                        }
                        Sign::Negative => {
                            pos_is_pure = false;
                            neg_encountered = true
                        }
                    };
                }
            }
        }
        if pos_is_pure && pos_encountered {
            Some(Literal {
                name,
                sign: Sign::Positive,
            })
        } else if neg_is_pure && neg_encountered {
            Some(Literal {
                name,
                sign: Sign::Negative,
            })
        } else {
            None
        }
    }

    /// Returns an option containing the a reference to the first unit clause
    /// in a vector of clauses. If there is no unit clause, returns a None.
    fn get_first_unit_clause(clauses: &Vec<Clause>) -> Option<&Clause> {
        for clause in clauses {
            if is_unit_clause(clause) {
                return Some(clause);
            }
        }
        return None;
    }

    /// Determines whether a given clause has only one literal.
    fn is_unit_clause(clause: &Clause) -> bool {
        clause.literals.len() == 1
    }

    // _            _           _          _          _
    //     /\ \         /\ \        / /\       /\ \       / /\
    //     \_\ \       /  \ \      / /  \      \_\ \     / /  \
    //     /\__ \     / /\ \ \    / / /\ \__   /\__ \   / / /\ \__
    //    / /_ \ \   / / /\ \_\  / / /\ \___\ / /_ \ \ / / /\ \___\
    //   / / /\ \ \ / /_/_ \/_/  \ \ \ \/___// / /\ \ \\ \ \ \/___/
    //  / / /  \/_// /____/\      \ \ \     / / /  \/_/ \ \ \
    // / / /      / /\____\/  _    \ \ \   / / /    _    \ \ \
    // / / /      / / /______ /_/\__/ / /  / / /    /_/\__/ / /
    // /_/ /      / / /_______\\ \/___/ /  /_/ /     \ \/___/ /
    // \_\/       \/__________/ \_____\/   \_\/       \_____\/

    #[cfg(test)]
    mod tests {
        use super::*;

        // --- is_unit_clause ---

        #[test]
        fn empty_clause_is_not_unit() {
            let v = Vec::new();
            let c = Clause { literals: v };
            assert!(!is_unit_clause(&c));
        }

        #[test]
        fn unit_clause_is_unit() {
            let mut v = Vec::new();
            v.push(Literal {
                name: 1,
                sign: Sign::Negative,
            });
            let c = Clause { literals: v };
            assert!(is_unit_clause(&c));
        }

        #[test]
        fn multi_literal_clause_is_not_unit() {
            let mut v = Vec::new();
            let l1 = Literal {
                name: 1,
                sign: Sign::Negative,
            };
            let l2 = Literal {
                name: 1,
                sign: Sign::Positive,
            };
            let l3 = Literal {
                name: 5,
                sign: Sign::Positive,
            };
            v.push(l1);
            v.push(l2);
            v.push(l3);
            let c = Clause { literals: v };
            assert!(!is_unit_clause(&c))
        }

        // --- get_first_unit_clause ---

        #[test]
        fn first_unit_clause_from_empty_vec() {
            let v = Vec::new();
            let c = Clause { literals: v };
            let clauses = vec![c];
            assert_eq!(get_first_unit_clause(&clauses), None);
        }

        #[test]
        fn no_unit_clause_in_single_elem_vec() {
            let c1 = Clause { literals: vec![] };
            let clauses = vec![c1];
            assert_eq!(get_first_unit_clause(&clauses), None);
        }

        #[test]
        fn first_unit_clause_in_single_elem_vec() {
            let c1 = Clause {
                literals: vec![Literal {
                    name: 1,
                    sign: Sign::Negative,
                }],
            };
            let clauses = vec![c1];
            let obtained_literals = &get_first_unit_clause(&clauses).unwrap().literals;
            assert_eq!(obtained_literals.len(), 1);
            let literal = obtained_literals.first().unwrap();
            assert_eq!(literal.name, 1);
            assert_eq!(literal.sign, Sign::Negative);
        }

        #[test]
        fn first_unit_clause_of_multiple_in_vec() {
            let c1 = Clause {
                literals: vec![Literal {
                    name: 2,
                    sign: Sign::Positive,
                }],
            };
            let c2 = Clause {
                literals: vec![Literal {
                    name: 1,
                    sign: Sign::Negative,
                }],
            };
            let clauses = vec![c1, c2];
            let obtained_literals = &get_first_unit_clause(&clauses).unwrap().literals;
            assert_eq!(obtained_literals.len(), 1);
            let literal = obtained_literals.first().unwrap();
            assert_eq!(literal.name, 2);
            assert_eq!(literal.sign, Sign::Positive);
        }

        #[test]
        fn first_unit_clause_is_not_first_elem() {
            let c1 = Clause {
                literals: vec![
                    Literal {
                        name: 2,
                        sign: Sign::Positive,
                    },
                    Literal {
                        name: 1,
                        sign: Sign::Positive,
                    },
                ],
            };
            let c2 = Clause {
                literals: vec![
                    Literal {
                        name: 1,
                        sign: Sign::Negative,
                    },
                    Literal {
                        name: 2,
                        sign: Sign::Negative,
                    },
                    Literal {
                        name: 3,
                        sign: Sign::Positive,
                    },
                ],
            };
            let c3 = Clause {
                literals: vec![Literal {
                    name: 1,
                    sign: Sign::Positive,
                }],
            };
            let clauses = vec![c1, c2, c3];
            let obtained_literals = &get_first_unit_clause(&clauses).unwrap().literals;
            assert_eq!(obtained_literals.len(), 1);
            let literal = obtained_literals.first().unwrap();
            assert_eq!(literal.name, 1);
            assert_eq!(literal.sign, Sign::Positive);
        }

        // --- eliminate_unit_clauses ---
        #[test]
        fn eliminate_unit_clauses_from_empty_formula() {
            let clauses = vec![];
            let formula = CNFFormula { clauses };
            let mut assignment: HashMap<u32, bool> = HashMap::new();
            let new_formula = eliminate_unit_clauses(&formula, &mut assignment);
            assert_eq!(new_formula.clauses.len(), 0);
            assert_eq!(assignment.len(), 0);
        }

        #[test]
        fn eliminate_unit_clauses_where_only_unit_clause() {
            let c1 = Clause {
                literals: vec![Literal {
                    name: 1,
                    sign: Sign::Positive,
                }],
            };
            let clauses = vec![c1];
            let formula = CNFFormula { clauses };
            let mut assignment: HashMap<u32, bool> = HashMap::new();
            let new_formula = eliminate_unit_clauses(&formula, &mut assignment);
            assert_eq!(new_formula.clauses.len(), 0);
            assert_eq!(assignment.len(), 1);
            assert!(*assignment.get(&1).unwrap());
        }

        #[test]
        fn eliminate_unit_clauses_where_only_non_unit_clause() {
            let c1 = Clause {
                literals: vec![
                    Literal {
                        name: 1,
                        sign: Sign::Positive,
                    },
                    Literal {
                        name: 2,
                        sign: Sign::Negative,
                    },
                ],
            };
            let clauses = vec![c1];
            let formula = CNFFormula { clauses };
            let mut assignment: HashMap<u32, bool> = HashMap::new();
            let new_formula = eliminate_unit_clauses(&formula, &mut assignment);
            assert_eq!(new_formula.clauses.len(), 1);
            assert_eq!(assignment.len(), 0);
        }

        #[test]
        fn eliminate_unit_clauses_where_multiple_non_unit_clauses() {
            let c1 = Clause {
                literals: vec![
                    Literal {
                        name: 2,
                        sign: Sign::Positive,
                    },
                    Literal {
                        name: 1,
                        sign: Sign::Positive,
                    },
                ],
            };
            let c2 = Clause {
                literals: vec![
                    Literal {
                        name: 1,
                        sign: Sign::Negative,
                    },
                    Literal {
                        name: 2,
                        sign: Sign::Negative,
                    },
                    Literal {
                        name: 3,
                        sign: Sign::Positive,
                    },
                ],
            };
            let c3 = Clause {
                literals: vec![
                    Literal {
                        name: 1,
                        sign: Sign::Negative,
                    },
                    Literal {
                        name: 2,
                        sign: Sign::Negative,
                    },
                ],
            };
            let clauses = vec![c1, c2, c3];
            let formula = CNFFormula { clauses };
            let mut assignment: HashMap<u32, bool> = HashMap::new();
            let new_formula = eliminate_unit_clauses(&formula, &mut assignment);
            assert_eq!(new_formula.clauses.len(), 3);
            assert_eq!(assignment.len(), 0);
        }

        #[test]
        fn eliminate_unit_clauses_where_multiple_clauses_one_unrelated_unit() {
            let c1 = Clause {
                literals: vec![
                    Literal {
                        name: 2,
                        sign: Sign::Positive,
                    },
                    Literal {
                        name: 1,
                        sign: Sign::Positive,
                    },
                ],
            };
            let c2 = Clause {
                literals: vec![
                    Literal {
                        name: 1,
                        sign: Sign::Negative,
                    },
                    Literal {
                        name: 2,
                        sign: Sign::Negative,
                    },
                    Literal {
                        name: 3,
                        sign: Sign::Positive,
                    },
                ],
            };
            let c3 = Clause {
                literals: vec![Literal {
                    name: 4,
                    sign: Sign::Negative,
                }],
            };
            let c1_copy = c1.clone();
            let c2_copy = c2.clone();
            let clauses = vec![c1, c2, c3];
            let formula = CNFFormula { clauses };
            let mut assignment: HashMap<u32, bool> = HashMap::new();
            let new_formula = eliminate_unit_clauses(&formula, &mut assignment);
            assert_eq!(new_formula.clauses, vec![c1_copy, c2_copy]);
            assert_eq!(assignment.len(), 1);
            assert!(!*assignment.get(&4).unwrap());
        }

        #[test]
        fn eliminate_unit_clauses_where_one_unit_leads_to_full_solution() {
            let c1 = Clause {
                literals: vec![
                    Literal {
                        name: 2,
                        sign: Sign::Positive,
                    },
                    Literal {
                        name: 1,
                        sign: Sign::Positive,
                    },
                ],
            };
            let c2 = Clause {
                literals: vec![
                    Literal {
                        name: 1,
                        sign: Sign::Negative,
                    },
                    Literal {
                        name: 2,
                        sign: Sign::Negative,
                    },
                    Literal {
                        name: 3,
                        sign: Sign::Positive,
                    },
                ],
            };
            let c3 = Clause {
                literals: vec![Literal {
                    name: 1,
                    sign: Sign::Negative,
                }],
            };
            let clauses = vec![c1, c2, c3];
            let formula = CNFFormula { clauses };
            let mut assignment: HashMap<u32, bool> = HashMap::new();
            let new_formula = eliminate_unit_clauses(&formula, &mut assignment);
            assert_eq!(new_formula.clauses, vec![]);
            assert!(!*assignment.get(&1).unwrap());
            assert!(*assignment.get(&2).unwrap());
            // leaving whether or not 3 is assigned to be unspecified behavior right now
        }

        #[test]
        fn eliminate_unit_clauses_where_one_unit_affects_clauses_but_doesnt_trigger_more_elims() {
            let c1 = Clause {
                literals: vec![
                    Literal {
                        name: 2,
                        sign: Sign::Positive,
                    },
                    Literal {
                        name: 4,
                        sign: Sign::Positive,
                    },
                ],
            };
            let c2 = Clause {
                literals: vec![
                    Literal {
                        name: 1,
                        sign: Sign::Negative,
                    },
                    Literal {
                        name: 2,
                        sign: Sign::Negative,
                    },
                    Literal {
                        name: 3,
                        sign: Sign::Positive,
                    },
                ],
            };
            let c3 = Clause {
                literals: vec![Literal {
                    name: 1,
                    sign: Sign::Positive,
                }],
            };
            let c1_copy = c1.clone();
            let modified_c2 = Clause {
                literals: vec![
                    Literal {
                        name: 2,
                        sign: Sign::Negative,
                    },
                    Literal {
                        name: 3,
                        sign: Sign::Positive,
                    },
                ],
            };
            let clauses = vec![c1, c2, c3];
            let formula = CNFFormula { clauses };
            let mut assignment: HashMap<u32, bool> = HashMap::new();
            let new_formula = eliminate_unit_clauses(&formula, &mut assignment);
            assert_eq!(new_formula.clauses, vec![c1_copy, modified_c2]);
            assert_eq!(assignment.len(), 1);
            assert!(*assignment.get(&1).unwrap());
        }

        #[test]
        fn eliminate_unit_clauses_where_multiple_distinct_units() {
            let c1 = Clause {
                literals: vec![Literal {
                    name: 1,
                    sign: Sign::Positive,
                }],
            };
            let c2 = Clause {
                literals: vec![Literal {
                    name: 3,
                    sign: Sign::Negative,
                }],
            };
            let c3 = Clause {
                literals: vec![Literal {
                    name: 100,
                    sign: Sign::Positive,
                }],
            };
            let c4 = Clause {
                literals: vec![Literal {
                    name: 5,
                    sign: Sign::Negative,
                }],
            };
            let clauses = vec![c1, c2, c3, c4];
            let formula = CNFFormula { clauses };
            let mut assignment: HashMap<u32, bool> = HashMap::new();
            let new_formula = eliminate_unit_clauses(&formula, &mut assignment);
            assert_eq!(new_formula.clauses.len(), 0);
            assert_eq!(assignment.len(), 4);
            assert!(*assignment.get(&1).unwrap());
            assert!(!*assignment.get(&3).unwrap());
            assert!(*assignment.get(&100).unwrap());
            assert!(!*assignment.get(&5).unwrap());
        }

        // --- var_has_pure_literal ---

        #[test]
        fn var_has_pure_literal_no_clauses() {
            assert_eq!(var_has_pure_literal(&vec![], 1), None);
        }

        #[test]
        fn var_has_pure_literal_one_clause_one_literal() {
            let clause = Clause {
                literals: vec![Literal {
                    name: 1,
                    sign: Sign::Positive,
                }],
            };
            let clauses = vec![clause];
            assert_eq!(
                var_has_pure_literal(&clauses, 1),
                Some(Literal {
                    name: 1,
                    sign: Sign::Positive
                })
            );
        }

        #[test]
        fn var_has_pure_literal_one_clause_one_lit_diff_name() {
            let clause = Clause {
                literals: vec![Literal {
                    name: 1,
                    sign: Sign::Positive,
                }],
            };
            let clauses = vec![clause];
            assert_eq!(var_has_pure_literal(&clauses, 2), None);
        }

        #[test]
        fn var_has_pure_literal_one_clause_multi_non_conflicting_lits() {
            let clause = Clause {
                literals: vec![
                    Literal {
                        name: 1,
                        sign: Sign::Positive,
                    },
                    Literal {
                        name: 2,
                        sign: Sign::Negative,
                    },
                ],
            };
            let clauses = vec![clause];
            assert_eq!(
                var_has_pure_literal(&clauses, 2),
                Some(Literal {
                    name: 2,
                    sign: Sign::Negative
                })
            );
        }

        #[test]
        fn var_has_pure_literal_one_clause_conflicting_lits() {
            let clause = Clause {
                literals: vec![
                    Literal {
                        name: 2,
                        sign: Sign::Positive,
                    },
                    Literal {
                        name: 2,
                        sign: Sign::Negative,
                    },
                ],
            };
            let clauses = vec![clause];
            assert_eq!(var_has_pure_literal(&clauses, 2), None)
        }

        #[test]
        fn var_has_pure_literal_multi_clauses_no_pure() {
            let c1 = Clause {
                literals: vec![
                    Literal {
                        name: 1,
                        sign: Sign::Positive,
                    },
                    Literal {
                        name: 2,
                        sign: Sign::Negative,
                    },
                ],
            };
            let c2 = Clause {
                literals: vec![
                    Literal {
                        name: 1,
                        sign: Sign::Negative,
                    },
                    Literal {
                        name: 3,
                        sign: Sign::Positive,
                    },
                ],
            };
            let c3 = Clause {
                literals: vec![
                    Literal {
                        name: 2,
                        sign: Sign::Positive,
                    },
                    Literal {
                        name: 3,
                        sign: Sign::Negative,
                    },
                ],
            };
            let clauses = vec![c1, c2, c3];
            assert_eq!(var_has_pure_literal(&clauses, 2), None);
            assert_eq!(var_has_pure_literal(&clauses, 1), None);
            assert_eq!(var_has_pure_literal(&clauses, 3), None);
        }

        #[test]
        fn var_has_pure_literal_multi_clauses_one_pure() {
            let c1 = Clause {
                literals: vec![
                    Literal {
                        name: 1,
                        sign: Sign::Positive,
                    },
                    Literal {
                        name: 2,
                        sign: Sign::Negative,
                    },
                ],
            };
            let c2 = Clause {
                literals: vec![
                    Literal {
                        name: 1,
                        sign: Sign::Negative,
                    },
                    Literal {
                        name: 3,
                        sign: Sign::Positive,
                    },
                ],
            };
            let c3 = Clause {
                literals: vec![
                    Literal {
                        name: 2,
                        sign: Sign::Negative,
                    },
                    Literal {
                        name: 3,
                        sign: Sign::Negative,
                    },
                ],
            };
            let clauses = vec![c1, c2, c3];
            assert_eq!(
                var_has_pure_literal(&clauses, 2),
                Some(Literal {
                    name: 2,
                    sign: Sign::Negative
                })
            );
            assert_eq!(var_has_pure_literal(&clauses, 1), None);
            assert_eq!(var_has_pure_literal(&clauses, 3), None);
        }

        // --- eliminate_pure_literals ---

        #[test]
        fn eliminate_pure_literals_no_clauses() {
            let formula = CNFFormula { clauses: vec![] };
            let mut assignment = HashMap::new();
            let vars = vec![];
            let new_formula = eliminate_pure_literals(&formula, &mut assignment, &vars);
            assert_eq!(assignment.len(), 0);
            assert_eq!(new_formula.clauses, vec![]);
        }

        #[test]
        fn eliminate_pure_literals_empty_clause() {
            let formula = CNFFormula {
                clauses: vec![Clause { literals: vec![] }],
            };
            let mut assignment = HashMap::new();
            let vars = vec![];
            let new_formula = eliminate_pure_literals(&formula, &mut assignment, &vars);
            assert_eq!(assignment.len(), 0);
            assert_eq!(new_formula.clauses, vec![Clause { literals: vec![] }]);
        }

        #[test]
        fn eliminate_pure_literals_just_unit_clause() {
            let formula = CNFFormula {
                clauses: vec![Clause {
                    literals: vec![Literal {
                        name: 1,
                        sign: Sign::Positive,
                    }],
                }],
            };
            let mut assignment = HashMap::new();
            let vars = vec![1];
            let new_formula = eliminate_pure_literals(&formula, &mut assignment, &vars);
            assert_eq!(assignment.len(), 1);
            assert!(*assignment.get(&1).unwrap());
            assert_eq!(new_formula.clauses, vec![]);
        }

        #[test]
        fn eliminate_pure_literals_one_clause_multi_pure_lits() {
            let formula = CNFFormula {
                clauses: vec![Clause {
                    literals: vec![
                        Literal {
                            name: 1,
                            sign: Sign::Positive,
                        },
                        Literal {
                            name: 2,
                            sign: Sign::Negative,
                        },
                        Literal {
                            name: 3,
                            sign: Sign::Positive,
                        },
                    ],
                }],
            };
            let mut assignment = HashMap::new();
            let vars = vec![1, 2, 3];
            let new_formula = eliminate_pure_literals(&formula, &mut assignment, &vars);
            assert!(*assignment.get(&1).unwrap());
            assert_eq!(new_formula.clauses, vec![]);
        }

        #[test]
        fn eliminate_pure_literals_one_clause_conflicting_lits() {
            let l1 = Literal {
                name: 2,
                sign: Sign::Negative,
            };
            let l2 = Literal {
                name: 2,
                sign: Sign::Positive,
            };
            let formula = CNFFormula {
                clauses: vec![Clause {
                    literals: vec![l1, l2],
                }],
            };
            let mut assignment = HashMap::new();
            let vars = vec![2];
            let new_formula = eliminate_pure_literals(&formula, &mut assignment, &vars);
            assert_eq!(
                new_formula.clauses,
                vec![Clause {
                    literals: vec![l1, l2]
                }]
            );
            assert_eq!(assignment.len(), 0);
        }

        #[test]
        fn eliminate_pure_literals_multi_clauses_no_pure_lits() {
            let c1 = Clause {
                literals: vec![
                    Literal {
                        name: 1,
                        sign: Sign::Positive,
                    },
                    Literal {
                        name: 2,
                        sign: Sign::Negative,
                    },
                ],
            };
            let c2 = Clause {
                literals: vec![
                    Literal {
                        name: 1,
                        sign: Sign::Negative,
                    },
                    Literal {
                        name: 3,
                        sign: Sign::Positive,
                    },
                ],
            };
            let c3 = Clause {
                literals: vec![
                    Literal {
                        name: 2,
                        sign: Sign::Positive,
                    },
                    Literal {
                        name: 3,
                        sign: Sign::Negative,
                    },
                ],
            };
            let c1_copy = c1.clone();
            let c2_copy = c2.clone();
            let c3_copy = c3.clone();
            let formula = CNFFormula {
                clauses: vec![c1, c2, c3],
            };
            let vars = vec![1, 2, 3];
            let mut assignment = HashMap::new();
            let new_formula = eliminate_pure_literals(&formula, &mut assignment, &vars);
            assert_eq!(new_formula.clauses, vec![c1_copy, c2_copy, c3_copy]);
            assert_eq!(assignment.len(), 0);
        }

        #[test]
        fn eliminate_pure_literals_multi_clauses_exhaustive_search_on_vars() {
            // Each elimination of a pure literal opens up a new pure literal in
            // the formula. This test checks that we aren't just doing a linear scan
            // over the variables and instead are checking every possible pure literal
            // each time.
            let c1 = Clause {
                literals: vec![
                    Literal {
                        name: 1,
                        sign: Sign::Positive,
                    },
                    Literal {
                        name: 2,
                        sign: Sign::Negative,
                    },
                ],
            };
            let c2 = Clause {
                literals: vec![
                    Literal {
                        name: 1,
                        sign: Sign::Negative,
                    },
                    Literal {
                        name: 3,
                        sign: Sign::Positive,
                    },
                ],
            };
            let c3 = Clause {
                literals: vec![
                    Literal {
                        name: 2,
                        sign: Sign::Negative,
                    },
                    Literal {
                        name: 3,
                        sign: Sign::Negative,
                    },
                ],
            };
            let c4 = Clause {
                literals: vec![Literal {
                    name: 3,
                    sign: Sign::Negative,
                }],
            };
            let formula = CNFFormula {
                clauses: vec![c1, c2, c3, c4],
            };
            let vars = vec![1, 2, 3];
            let mut assignment = HashMap::new();
            let new_formula = eliminate_pure_literals(&formula, &mut assignment, &vars);
            assert_eq!(new_formula.clauses.len(), 0);
            assert!(!*assignment.get(&2).unwrap());
            assert!(!*assignment.get(&1).unwrap());
            assert!(!*assignment.get(&3).unwrap());
        }

        // --- solve ---

        #[test]
        fn solve_empty_formula() {
            let formula = CNFFormula { clauses: vec![] };
            assert_eq!(solve(formula), SATResult::SAT(HashMap::new()));
        }

        #[test]
        fn solve_formula_with_only_empty_clause() {
            let formula = CNFFormula {
                clauses: vec![Clause { literals: vec![] }],
            };
            assert_eq!(solve(formula), SATResult::UNSAT);
        }

        #[test]
        fn solve_formula_with_misc_clauses_and_empty_clause() {
            let c1 = Clause {
                literals: vec![Literal {
                    name: 1,
                    sign: Sign::Positive,
                }],
            };
            let c2 = Clause {
                literals: vec![
                    Literal {
                        name: 1,
                        sign: Sign::Negative,
                    },
                    Literal {
                        name: 2,
                        sign: Sign::Positive,
                    },
                ],
            };
            let c3 = Clause { literals: vec![] };
            let formula = CNFFormula {
                clauses: vec![c1, c2, c3],
            };
            assert_eq!(solve(formula), SATResult::UNSAT);
        }

        #[test]
        fn solve_formula_with_only_a_unit_clause() {
            let clauses = vec![Clause {
                literals: vec![Literal {
                    name: 1,
                    sign: Sign::Positive,
                }],
            }];
            let formula = CNFFormula { clauses };
            let mut soln = HashMap::new();
            soln.insert(1, true);
            assert_eq!(solve(formula), SATResult::SAT(soln));
        }

        #[test]
        fn solve_formula_with_multiple_unit_clauses() {
            let clauses = vec![
                Clause {
                    literals: vec![Literal {
                        name: 1,
                        sign: Sign::Positive,
                    }],
                },
                Clause {
                    literals: vec![Literal {
                        name: 2,
                        sign: Sign::Negative,
                    }],
                },
                Clause {
                    literals: vec![Literal {
                        name: 5,
                        sign: Sign::Positive,
                    }],
                },
            ];
            let formula = CNFFormula { clauses };
            let mut soln = HashMap::new();
            soln.insert(1, true);
            soln.insert(2, false);
            soln.insert(5, true);
            assert_eq!(solve(formula), SATResult::SAT(soln));
        }

        #[test]
        fn solve_formula_with_one_clause() {
            // Only one clause, so any of the literals could be true
            let l1 = Literal {
                name: 1,
                sign: Sign::Positive,
            };
            let l2 = Literal {
                name: 2,
                sign: Sign::Positive,
            };
            let l3 = Literal {
                name: 5,
                sign: Sign::Negative,
            };
            let clauses = vec![Clause {
                literals: vec![l1, l2, l3],
            }];
            let soln = solve(CNFFormula { clauses });
            match soln {
                SATResult::UNSAT => assert!(false),
                SATResult::SAT(soln) => assert!(
                    *soln.get(&1).unwrap() || *soln.get(&2).unwrap() || !*soln.get(&5).unwrap()
                ),
            };
        }

        #[test]
        fn solve_formula_with_contradictory_unit_clauses() {
            let clauses = vec![
                Clause {
                    literals: vec![Literal {
                        name: 1,
                        sign: Sign::Positive,
                    }],
                },
                Clause {
                    literals: vec![Literal {
                        name: 2,
                        sign: Sign::Negative,
                    }],
                },
                Clause {
                    literals: vec![Literal {
                        name: 1,
                        sign: Sign::Negative,
                    }],
                },
            ];
            let formula = CNFFormula { clauses };
            assert_eq!(solve(formula), SATResult::UNSAT);
        }

        #[test]
        fn solve_non_trivial_unsat_formula() {
            let one_pos = Literal {
                name: 1,
                sign: Sign::Positive,
            };
            let one_neg = Literal {
                name: 1,
                sign: Sign::Negative,
            };
            let two_pos = Literal {
                name: 2,
                sign: Sign::Positive,
            };
            let two_neg = Literal {
                name: 2,
                sign: Sign::Negative,
            };
            let c1 = Clause {
                literals: vec![one_pos, two_pos],
            };
            let c2 = Clause {
                literals: vec![one_pos, two_neg],
            };
            let c3 = Clause {
                literals: vec![one_neg, two_pos],
            };
            let c4 = Clause {
                literals: vec![one_neg, two_neg],
            };
            let formula = CNFFormula {
                clauses: vec![c1, c2, c3, c4],
            };
            assert_eq!(solve(formula), SATResult::UNSAT);
        }

        #[test]
        fn solve_simple_sat_example() {
            let c1 = Clause {
                literals: vec![
                    Literal {
                        name: 1,
                        sign: Sign::Positive,
                    },
                    Literal {
                        name: 3,
                        sign: Sign::Negative,
                    },
                ],
            };
            let c2 = Clause {
                literals: vec![
                    Literal {
                        name: 2,
                        sign: Sign::Positive,
                    },
                    Literal {
                        name: 3,
                        sign: Sign::Positive,
                    },
                    Literal {
                        name: 1,
                        sign: Sign::Negative,
                    },
                ],
            };
            let formula = CNFFormula {
                clauses: vec![c1, c2],
            };
            if let SATResult::SAT(soln) = solve(formula) {
                assert!(*soln.get(&2).unwrap());
                assert!(*soln.get(&1).unwrap() || !*soln.get(&3).unwrap());
            } else {
                assert!(false);
            }
        }
    }
}
