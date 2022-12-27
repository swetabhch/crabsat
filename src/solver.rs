pub mod solver {
    // The core of the solver's functionality. This function
    // returns SAT with a satisfying assignment for the input formula
    // if such an assignment exists, else returns UNSAT.
    pub fn solve(formula: CNFFormula) -> SATResult {}

    // Performs unit clause propagation on a formula and returns the formula
    // remaining after propagation.
    // Side effect: mutates the assignment mapping according to the unit prop process.
    fn propagate_unit_clauses(
        formula: &CNFFormula,
        assignment: &mut HashMap<int, bool>,
    ) -> CNFFormula {
    }

    // Performs pure literal elimination on a formula and returns the formula that remains.
    // Side effect: mutates the assignment mapping according to the pure literal elim process.
    fn eliminate_pure_literals(
        formula: &CNFFormula,
        assignment: &mut HashMap<int, bool>,
    ) -> CNFFormula {
    }
}
