mod cnf;

// For some reason, I'm going to try to implement this without giving Clause, Literal
// the Copy trait.
// TODO: this file is becoming somewhat unwieldy with all the tests being grouped here.
//   -> Think about rearrangement?

pub mod solver {
    use super::cnf::cnf::*;
    use std::collections::HashMap;

    // The core of the solver's functionality. This function
    // returns SAT with a satisfying assignment for the input formula
    // if such an assignment exists, else returns UNSAT.
    pub fn solve(formula: CNFFormula) -> SATResult {
        SATResult::UNSAT
    }

    // Performs unit clause propagation on a formula for each unit clause and
    // returns the formula remaining after propagation.
    // Side effect: mutates the assignment mapping according to the unit prop process.
    fn eliminate_unit_clauses(
        formula: &CNFFormula,
        assignment: &mut HashMap<u32, bool>,
    ) -> CNFFormula {
        let mut edited_clauses = formula.clauses.clone();
        // Find a unit clause (if none, do not loop; return inp formula).
        while let Some(clause_ref) = get_first_unit_clause(&edited_clauses) {
            // We know this clause will have length 1, so we unwrap here.
            let unit_literal = clause_ref.literals.first().unwrap().clone();
            // Change assignment according to literal.
            assign_literal_to_true(&unit_literal, assignment);
            let mut clauses_to_remove = Vec::new();
            for clause in &edited_clauses {
                if clause.literals.contains(&unit_literal) {
                    // NOTE: Pushing clones of clauses here so as to avoid the problem of
                    // edited_clauses's borrow lasting until after the for loop due
                    // to lexical lifetimes.
                    clauses_to_remove.push(clause.clone());
                }
            }
            // Drop all clauses that contain the literal.
            edited_clauses.retain(|c| !clauses_to_remove.contains(c));
            // Remove the negated version of this literal from the remaining clauses.
            for clause in &mut edited_clauses {
                let opposite_sign = match unit_literal.sign {
                    Sign::Positive => Sign::Negative,
                    Sign::Negative => Sign::Positive,
                };
                let negated_literal = Literal {
                    name: unit_literal.name,
                    sign: opposite_sign,
                };
                if clause.literals.contains(&negated_literal) {
                    clause.literals.retain(|l| *l != negated_literal);
                }
            }
        }

        CNFFormula {
            clauses: edited_clauses,
        }
    }

    // If a literal has positive parity, sets the variable to true in the assignment.
    // Else, sets the variable to false.
    fn assign_literal_to_true(literal: &Literal, assignment: &mut HashMap<u32, bool>) -> () {
        match literal.sign {
            Sign::Positive => assignment.insert(literal.name, true),
            Sign::Negative => assignment.insert(literal.name, false),
        };
    }

    // Performs pure literal elimination on a formula and returns the formula that remains.
    // Side effect: mutates the assignment mapping according to the pure literal elim process.
    // TODO: Decide where we get variable names from. For now: take it in as input.
    fn eliminate_pure_literals(
        formula: &CNFFormula,
        assignment: &mut HashMap<u32, bool>,
        variables: &Vec<u32>,
    ) -> CNFFormula {
        let mut edited_clauses = formula.clauses.clone();
        for name in variables {
            let pure_lit_opt = var_has_pure_literal(&edited_clauses, *name);
            match pure_lit_opt {
                None => continue,
                Some(pure_lit) => {
                    assign_literal_to_true(&pure_lit, assignment);
                    edited_clauses.retain(|c| !c.literals.contains(&pure_lit));
                }
            }
        }

        CNFFormula {
            clauses: edited_clauses,
        }
    }

    // Determines whether a variable corresponds to a pure literal in the given vector of clauses,
    // i.e. has the same parity throughout the formula. If so, returns an Option containing
    // the literal. If not, returns None.
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

    // Returns an option containing the a reference to the first unit clause
    // in a vector of clauses. If there is no unit clause, returns a None.
    fn get_first_unit_clause(clauses: &Vec<Clause>) -> Option<&Clause> {
        for clause in clauses {
            if is_unit_clause(clause) {
                return Some(clause);
            }
        }
        return None;
    }

    // Determines whether a given clause has only one literal.
    fn is_unit_clause(clause: &Clause) -> bool {
        clause.literals.len() == 1
    }

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
            // TODO: this should currently fail. Fix implementation.
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
    }
}
