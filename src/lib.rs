mod cnf;

pub mod solver {
    use super::cnf::cnf::*;
    use std::collections::HashMap;

    // The core of the solver's functionality. This function
    // returns SAT with a satisfying assignment for the input formula
    // if such an assignment exists, else returns UNSAT.
    pub fn solve(formula: CNFFormula) -> SATResult {
        SATResult::UNSAT
    }

    // Performs unit clause propagation on a formula and returns the formula
    // remaining after propagation.
    // Side effect: mutates the assignment mapping according to the unit prop process.
    fn propagate_unit_clauses(
        formula: &CNFFormula,
        assignment: &mut HashMap<u32, bool>,
    ) -> CNFFormula {
        // 1. Find a unit clause (if none, return inp formula)
        // 2. Change assignment according to literal
        // 3. From formula, drop all clauses that contain the literal
        // 4. From formula, drop negated literal from all clauses that contain it
        // 5. Return to step 1
        CNFFormula {
            clauses: Vec::new(),
        }
    }

    // Performs pure literal elimination on a formula and returns the formula that remains.
    // Side effect: mutates the assignment mapping according to the pure literal elim process.
    fn eliminate_pure_literals(
        formula: &CNFFormula,
        assignment: &mut HashMap<u32, bool>,
    ) -> CNFFormula {
        // 1. Find a pure literal (if none, return inp formula)
        // 2. Change assignment so that the literal evaluates to true
        // 3. From formula, drop all clauses that contain the literal
        // 4. Return to step 1
        CNFFormula {
            clauses: Vec::new(),
        }
    }

    // Determines whether a given clause has only one literal.
    fn is_unit_clause(clause: &Clause) -> bool {
        clause.literals.len() == 1
    }

    #[cfg(test)]
    mod tests {
        use super::*;

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
    }
}
