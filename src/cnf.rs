pub mod cnf {
    use std::collections::HashMap;

    #[derive(Debug, PartialEq, Eq, Clone, Copy)]
    pub enum Sign {
        Positive,
        Negative,
    }

    #[derive(Debug, PartialEq, Eq, Clone)]
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

    pub enum SATResult {
        SAT(HashMap<u32, bool>),
        UNSAT,
    }
}
