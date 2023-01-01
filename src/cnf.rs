pub mod cnf {
    use std::collections::HashMap;

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
}

pub mod parser {
    use super::cnf::*;
    use thiserror::Error;

    #[derive(Debug, Error, PartialEq)]
    pub enum ParseError {
        #[error("absolute value of literal too large, will cause overflow")]
        VarNameTooLarge,
        #[error("cannot use 0 as a literal")]
        UsingZeroAsLiteral,
        #[error("clause in incorrect format, no zero end")]
        MalformedClauseEnd,
        #[error("literal is not in the form of a signed int")]
        MalformedLiteral,
        #[error("cannot parse empty formula")]
        EmptyFormula,
    }

    /// Converts a string describing a CNF formula in the DIMACS format
    /// into a CNFFormula representation.
    /// Assumption: a clause can only take up one line.
    /// (See 'CNF Input Format' on page 4 of http://www.satcompetition.org/2011/rules.pdf)
    pub fn parse_dimacs_cnf(dimacs_str: &str) -> Result<CNFFormula, &str> {
        Ok(CNFFormula { clauses: vec![] })
    }

    /// Takes in a line as input. If it is in DIMACS format and correctly represents a
    /// clause, return a Result containing the equivalent Clause. Else, return a ParseError
    /// describing the issue.
    fn parse_line_to_clause(dimacs_line: &str) -> Result<Clause, ParseError> {
        let mut literal_ints: Vec<&str> = dimacs_line.trim().split(" ").collect();
        if (literal_ints.len() == 0) || (literal_ints.last().unwrap() != &"0") {
            return Err(ParseError::MalformedClauseEnd);
        }
        let mut vec_of_lits: Vec<Literal> = Vec::new();
        literal_ints.truncate(literal_ints.len() - 1);
        for lit_int in literal_ints {
            match lit_int.parse::<i32>() {
                Ok(n) => vec_of_lits.push(parse_num_to_literal(n)?),
                Err(_) => {
                    return Err(ParseError::MalformedLiteral);
                }
            }
        }
        Ok(Clause {
            literals: vec_of_lits,
        })
    }

    /// Takes a number representing a literal in the DIMACS format and returns
    /// a Result containing the equivalent Literal. This will return an Err if
    /// the variable overflows when we try to take its absolute value for the
    /// variable name. Assumes that the input is not 0.
    fn parse_num_to_literal(n: i32) -> Result<Literal, ParseError> {
        if n == 0 {
            Err(ParseError::UsingZeroAsLiteral)
        } else if n == i32::MIN {
            Err(ParseError::VarNameTooLarge)
        } else {
            Ok(Literal::new(
                n.abs().try_into().unwrap(),
                if n > 0 {
                    Sign::Positive
                } else {
                    Sign::Negative
                },
            ))
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        // --- parse_line_to_clause ---
        #[test]
        fn parse_valid_empty_clause() {
            assert_eq!(
                parse_line_to_clause(&"0").unwrap(),
                Clause { literals: vec![] }
            );
        }

        #[test]
        fn empty_string_parsed_as_invalid_clause() {
            assert_eq!(
                parse_line_to_clause(&""),
                Err(ParseError::MalformedClauseEnd)
            );
        }

        // --- parse_num_to_literal ---
        #[test]
        fn parsing_positive_literal() {
            match parse_num_to_literal(3) {
                Err(_) => assert!(false),
                Ok(v) => assert_eq!(v, Literal::new(3, Sign::Positive)),
            }
        }

        #[test]
        fn parsing_negative_literal() {
            match parse_num_to_literal(-100) {
                Err(_) => assert!(false),
                Ok(v) => assert_eq!(v, Literal::new(100, Sign::Negative)),
            }
        }

        #[test]
        fn parsing_max_positive_literal() {
            match parse_num_to_literal(i32::MAX) {
                Err(_) => assert!(false),
                Ok(v) => assert_eq!(
                    v,
                    Literal::new(i32::MAX.try_into().unwrap(), Sign::Positive)
                ),
            }
        }

        #[test]
        fn parsing_min_negative_literal_errors() {
            assert_eq!(
                parse_num_to_literal(i32::MIN),
                Err(ParseError::VarNameTooLarge)
            );
        }
    }
}
