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

pub mod parser {
    use std::collections::HashSet;

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
        #[error("comment in unrecognized format or no specification line")]
        BadComment,
        #[error("comments, specification, clauses sequencing incorrect")]
        BadSequencing,
        #[error("specfication line incorrectly formatted")]
        BadSpecification,
        #[error("specification does not match formula")]
        SpecificationMismatch,
    }

    /// Converts a string describing a CNF formula in the DIMACS format
    /// into a CNFFormula representation.
    /// Assumption: a clause can only take up one line.
    /// (See 'CNF Input Format' on page 4 of http://www.satcompetition.org/2011/rules.pdf)
    pub fn parse_dimacs_cnf(dimacs_str: &str) -> Result<CNFFormula, ParseError> {
        let dimacs_str = dimacs_str.trim();
        let mut trimmed_strs: Vec<&str> = dimacs_str.lines().map(&str::trim).collect();

        // Check that c, p, content lines are correctly sequenced and specification info
        let mut p_idx = None;
        let mut spec_line = "";
        for (idx, line) in trimmed_strs.iter().enumerate() {
            if (line.starts_with("c") || line.starts_with("p cnf")) && p_idx.is_some() {
                return Err(ParseError::BadSequencing);
            }
            if line.starts_with("p cnf") {
                p_idx = Some(idx);
                spec_line = line;
            } else if p_idx.is_none() && !line.starts_with("c") {
                return Err(ParseError::BadComment);
            }
        }

        // Parse content lines
        let split_idx = p_idx.unwrap();
        let (num_vars, num_clauses) = parse_spec_line(spec_line)?;
        let mut clauses = Vec::new();
        for clause_str in trimmed_strs.drain((split_idx + 1)..) {
            clauses.push(parse_line_to_clause(clause_str)?);
        }

        // Validate obtained formula against specification in 'p cnf' line
        let formula = CNFFormula { clauses };
        if validate_formula(&formula, num_vars, num_clauses) {
            Ok(formula)
        } else {
            Err(ParseError::SpecificationMismatch)
        }
    }

    /// Determines whether a CNFFormula has the specified number of vars and clauses.
    fn validate_formula(formula: &CNFFormula, num_vars: u32, num_clauses: u32) -> bool {
        if formula.clauses.len() != num_clauses.try_into().unwrap() {
            return false;
        }
        let mut distinct_vars = HashSet::new();
        let insert_vars = |clause: &Clause| {
            clause.literals.iter().for_each(|l| {
                distinct_vars.insert(l.name);
            })
        };
        formula.clauses.iter().for_each(insert_vars);
        distinct_vars.len() <= num_vars.try_into().unwrap()
    }

    /// Parses a specification line in DIMACS format and returns a Result containing
    /// a tuple with the number of vars and the number of clauses.
    /// Assumes that the input starts with "p cnf"
    fn parse_spec_line(spec_line: &str) -> Result<(u32, u32), ParseError> {
        let mut spec_iter = spec_line.split_ascii_whitespace();
        spec_iter.next();
        spec_iter.next();
        let num_vars = match spec_iter.next() {
            None => return Err(ParseError::BadSpecification),
            Some(v_str) => match v_str.parse::<u32>() {
                Ok(n) => n,
                Err(_) => return Err(ParseError::BadSpecification),
            },
        };
        let num_clauses = match spec_iter.next() {
            None => return Err(ParseError::BadSpecification),
            Some(v_str) => match v_str.parse::<u32>() {
                Ok(n) => n,
                Err(_) => return Err(ParseError::BadSpecification),
            },
        };
        Ok((num_vars, num_clauses))
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

        // --- validate_formula ---

        #[test]
        fn validate_empty_formula() {
            assert!(validate_formula(&CNFFormula { clauses: vec![] }, 0, 0));
        }

        #[test]
        fn validate_empty_formula_fails() {
            assert!(!validate_formula(&CNFFormula { clauses: vec![] }, 0, 1));
        }

        #[test]
        fn validate_formula_with_empty_clause() {
            let fmla = CNFFormula {
                clauses: vec![Clause { literals: vec![] }],
            };
            assert!(!validate_formula(&fmla, 0, 0));
            assert!(validate_formula(&fmla, 0, 1));
        }

        #[test]
        fn validate_formula_one_var_one_clause() {
            assert!(validate_formula(
                &CNFFormula {
                    clauses: vec![Clause {
                        literals: vec![Literal::new(1, Sign::Positive)]
                    }]
                },
                1,
                1
            ));
        }

        #[test]
        fn validate_formula_one_var_repeated_one_clause() {
            assert!(validate_formula(
                &CNFFormula {
                    clauses: vec![Clause {
                        literals: vec![
                            Literal::new(1, Sign::Positive),
                            Literal::new(1, Sign::Negative)
                        ]
                    }]
                },
                1,
                1
            ));
        }

        #[test]
        fn validate_formula_one_var_multiple_clauses() {
            assert!(validate_formula(
                &CNFFormula {
                    clauses: vec![
                        Clause {
                            literals: vec![Literal::new(1, Sign::Positive)]
                        },
                        Clause {
                            literals: vec![Literal::new(1, Sign::Negative)]
                        }
                    ]
                },
                1,
                2
            ));
        }

        #[test]
        fn validate_formula_one_clause_multiple_vars() {
            assert!(validate_formula(
                &CNFFormula {
                    clauses: vec![Clause {
                        literals: vec![
                            Literal::new(1, Sign::Positive),
                            Literal::new(2, Sign::Negative)
                        ]
                    }]
                },
                2,
                1
            ));
        }

        #[test]
        fn validate_formula_multi_clauses_multi_vars() {
            let fmla = CNFFormula {
                clauses: vec![
                    Clause {
                        literals: vec![
                            Literal::new(1, Sign::Positive),
                            Literal::new(2, Sign::Negative),
                        ],
                    },
                    Clause {
                        literals: vec![
                            Literal::new(2, Sign::Positive),
                            Literal::new(3, Sign::Negative),
                        ],
                    },
                    Clause { literals: vec![] },
                    Clause {
                        literals: vec![Literal::new(1, Sign::Negative)],
                    },
                ],
            };
            assert!(validate_formula(&fmla, 3, 4));
            assert!(!validate_formula(&fmla, 3, 3));
            assert!(validate_formula(&fmla, 4, 4));
            assert!(!validate_formula(&fmla, 4, 3));
        }

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

        #[test]
        fn parse_needs_clause_to_end_with_zero() {
            assert_eq!(
                parse_line_to_clause(&"1"),
                Err(ParseError::MalformedClauseEnd)
            );
        }

        #[test]
        fn parse_line_to_clause_zero_present_at_non_terminal_posn() {
            assert_eq!(
                parse_line_to_clause(&"5 -6 -1 0 2"),
                Err(ParseError::MalformedClauseEnd)
            )
        }

        #[test]
        fn parse_line_to_clause_errors_on_malformed_literal() {
            assert_eq!(
                parse_line_to_clause(&"5 -6 - 2 0"),
                Err(ParseError::MalformedLiteral)
            );
            assert_eq!(
                parse_line_to_clause(&"5 -6 c 2 0"),
                Err(ParseError::MalformedLiteral)
            );
            assert_eq!(
                parse_line_to_clause(&"! -6 -1 2 0"),
                Err(ParseError::MalformedLiteral)
            );
        }

        #[test]
        fn parse_line_to_clause_errors_when_overflowing_var_name() {
            assert_eq!(
                parse_line_to_clause(&format!("1 {} 0", i32::to_string(&i32::MIN))),
                Err(ParseError::VarNameTooLarge)
            )
        }

        #[test]
        fn parse_line_to_clause_trims_input() {
            assert_eq!(
                parse_line_to_clause(&"   0  ").unwrap(),
                Clause { literals: vec![] }
            );
        }

        #[test]
        fn parse_line_to_clause_single_literal() {
            assert_eq!(
                parse_line_to_clause(&" -1 0"),
                Ok(Clause {
                    literals: vec![Literal::new(1, Sign::Negative)]
                })
            )
        }

        #[test]
        fn parse_line_to_clause_multiple_literals() {
            assert_eq!(
                parse_line_to_clause(&"5 -6 -1 2 0"),
                Ok(Clause {
                    literals: vec![
                        Literal::new(5, Sign::Positive),
                        Literal::new(6, Sign::Negative),
                        Literal::new(1, Sign::Negative),
                        Literal::new(2, Sign::Positive)
                    ]
                })
            )
        }

        // --- parse_spec_line ---
        #[test]
        fn parse_spec_line_with_no_nums() {
            assert_eq!(parse_spec_line("p cnf"), Err(ParseError::BadSpecification));
        }

        #[test]
        fn parse_spec_line_with_one_num() {
            assert_eq!(
                parse_spec_line("p cnf 5"),
                Err(ParseError::BadSpecification)
            );
        }

        #[test]
        fn parse_spec_line_with_non_num() {
            assert_eq!(
                parse_spec_line("p cnf f"),
                Err(ParseError::BadSpecification)
            );
        }

        #[test]
        fn parse_spec_line_with_one_num_one_char() {
            assert_eq!(
                parse_spec_line("p cnf 5 f"),
                Err(ParseError::BadSpecification)
            );
        }

        #[test]
        fn parse_spec_line_with_neg_num() {
            assert_eq!(
                parse_spec_line("p cnf 3 -4"),
                Err(ParseError::BadSpecification)
            );
        }

        #[test]
        fn parse_spec_line_with_two_non_neg_nums() {
            assert_eq!(parse_spec_line("p cnf 3 4"), Ok((3, 4)));
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
