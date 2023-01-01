// pub mod parser {
//     use cnf::cnf::*;
//     use std::fs;

//     const EMPTY_FORMULA_EXN: &str = "cannot parse empty formula";

//     /// Converts a string describing a CNF formula in the DIMACS format
//     /// into a CNFFormula representation.
//     /// Assumption: a clause can only take up one line.
//     /// (See 'CNF Input Format' on page 4 of http://www.satcompetition.org/2011/rules.pdf)
//     pub fn parse_dimacs_cnf(dimacs_str: &str) -> Result<CNFFormula, &str> {
//         CNFFormula { clauses: vec![] }
//     }

//     /// Takes in a line as input. If it is in DIMACS format and correctly represents a
//     /// clause, return a Result containing the equivalent Clause. Else, return an Err
//     /// describing the issue.
//     fn parse_line_to_clause(dimacs_line: &str) -> Result<Clause, &str> {
//         Err("not in DIMACS format");
//     }

//     fn parse_num_to_literal(num_literal: i32) -> Literal {
//         Literal::new(1, Sign::Positive)
//     }

//     // #[cfg(test)]
//     // mod tests {
//     //     use super::*;

//     //     // --- parse_line_to_clause ---
//     //     #[test]
//     //     fn empty_string_doesnt_parse() {
//     //         match parse_line_to_clause("") {
//     //             Ok(_) => assert!(false),
//     //             Err(e) => assert_eq!(e, EMPTY_FORMULA_EXN),
//     //         }
//     //     }
//     // }
// }
