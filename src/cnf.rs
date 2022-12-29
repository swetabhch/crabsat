pub mod cnf {
    use std::collections::HashMap;

    #[derive(Debug, PartialEq, Eq, Clone, Copy)]
    pub enum Sign {
        Positive,
        Negative,
    }

    // TODO: Added Copy here, change code in lib.rs to reflect this.
    #[derive(Debug, PartialEq, Eq, Clone, Copy)]
    pub struct Literal {
        pub name: u32,
        pub sign: Sign,
    }

    #[derive(Debug, PartialEq, Eq, Clone)]
    pub struct Clause {
        pub literals: Vec<Literal>,
    }

    #[derive(Debug)]
    pub struct CNFFormula {
        pub clauses: Vec<Clause>,
    }

    #[derive(Debug, PartialEq, Eq)]
    pub enum SATResult {
        SAT(HashMap<u32, bool>),
        UNSAT,
    }
}
