pub mod cnf {
    use std::collections::HashMap;
    use std::fmt;

    /// An enum representing the sign of a literal.
    #[derive(Debug, PartialEq, Eq, Clone, Copy)]
    pub enum Sign {
        Positive,
        Negative,
    }

    /// A struct for a literal in a boolean formula! Names are bounded by the limits of u32.
    /// Note that Literals are Copy-able.
    #[derive(Debug, PartialEq, Eq, Clone, Copy)]
    pub struct Literal {
        pub name: u32,
        pub sign: Sign,
    }

    /// A struct for a clause in a boolean formula. Semanically, this should be
    /// interpreted as an AND expression of all of its literals.
    /// Note that this can be Cloned but not Copied.
    #[derive(Debug, PartialEq, Eq, Clone)]
    pub struct Clause {
        pub literals: Vec<Literal>,
    }

    /// A struct for a boolean formula in conjunctive normal form (CNF). This should
    /// be interpreted as an OR of all of its clauses.
    #[derive(Debug)]
    pub struct CNFFormula {
        pub clauses: Vec<Clause>,
    }

    impl Literal {
        /// Simplifying literal construction!
        pub fn new(name: u32, sign: Sign) -> Literal {
            Literal { name, sign }
        }
    }

    // Display code!

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
