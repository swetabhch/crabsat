pub mod cnf_structs {
    use std::collections::HashMap;

    #[derive(Debug)]
    pub enum Sign {
        Positive,
        Negative,
    }

    #[derive(Debug)]
    pub struct Literal {
        pub name: u32,
        pub sign: Sign,
    }

    #[derive(Debug)]
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
