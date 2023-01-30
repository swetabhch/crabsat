use crate::cnf::cnf::*;

pub mod solver {
    use super::*;
    pub trait Solver {
        fn solve(&self, formula: CNFFormula) -> SATResult;
    }
}
