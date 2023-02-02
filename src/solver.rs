use crate::cnf::cnf::*;

pub mod solver {
    use super::*;
    use std::collections::HashMap;
    use std::fmt;

    /// A trait to describe a general CNF-SAT solver.
    /// *May* generalize to non-CNF formulae in the future!
    pub trait Solver {
        fn solve(&self, formula: CNFFormula) -> SATResult;
    }

    /// A result returned by a SAT solver. If the result is SAT, the result contains
    /// a mapping from boolean variables to their assignments. Else, the result is just UNSAT.
    #[derive(Debug, PartialEq, Eq)]
    pub enum SATResult {
        SAT(HashMap<u32, bool>),
        UNSAT,
    }

    impl fmt::Display for SATResult {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            match self {
                Self::UNSAT => write!(f, "UNSAT"),
                Self::SAT(soln) => {
                    let mut soln_string = String::from("SAT. Satisfying assignment: {\n");
                    for (var, truth_val) in soln.iter() {
                        soln_string.push_str(&format!("  {}: {}\n", var, truth_val));
                    }
                    soln_string.push('}');
                    write!(f, "{}", &soln_string)
                }
            }
        }
    }
}
