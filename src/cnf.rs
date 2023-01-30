pub mod cnf {
    use std::collections::HashMap;
    use std::fmt;

    #[derive(Debug, PartialEq, Eq, Clone, Copy)]
    pub enum Sign {
        Positive,
        Negative,
    }

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

    impl Literal {
        pub fn new(name: u32, sign: Sign) -> Literal {
            Literal { name, sign }
        }
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

    impl fmt::Display for Literal {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            let sign_str = match self.sign {
                Sign::Positive => "",
                Sign::Negative => "-",
            };
            write!(f, "{}{}", sign_str, self.name)
        }
    }

    impl fmt::Display for Clause {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            let mut literals_str = String::from("");
            for literal in &self.literals {
                literals_str.push_str(&format!("{}, ", literal));
            }
            write!(f, "clause[{}]", &literals_str)
        }
    }

    impl fmt::Display for CNFFormula {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            let mut fmla_string = String::from("Clauses: {\n");
            let mut clause_num = 1;
            for clause in &self.clauses {
                fmla_string.push_str(&format!("  {}. {}\n", clause_num, clause));
                clause_num += 1;
            }
            fmla_string.push('}');
            write!(f, "{}", &fmla_string)
        }
    }
}
