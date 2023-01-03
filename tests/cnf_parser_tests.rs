use crabsat::cnf::cnf::*;
use crabsat::cnf::parser::*;

#[test]
fn parse_simple_multi_var_multi_clause_formula() {
    let s = "c
          c start with comments
          c
          c
          p cnf 5 3
          1 -5 4 0
          -1 5 3 4 0
          -3 -4 0";
    let c1 = Clause {
        literals: vec![
            Literal::new(1, Sign::Positive),
            Literal::new(5, Sign::Negative),
            Literal::new(4, Sign::Positive),
        ],
    };
    let c2 = Clause {
        literals: vec![
            Literal::new(1, Sign::Negative),
            Literal::new(5, Sign::Positive),
            Literal::new(3, Sign::Positive),
            Literal::new(4, Sign::Positive),
        ],
    };
    let c3 = Clause {
        literals: vec![
            Literal::new(3, Sign::Negative),
            Literal::new(4, Sign::Negative),
        ],
    };
    match parse_dimacs_cnf(s) {
        Err(_) => assert!(false),
        Ok(fmla) => assert_eq!(fmla.clauses, vec![c1, c2, c3]),
    }
}

#[test]
fn parse_formula_with_no_clauses() {
    let s = "c
  c a formula with no vars and no clauses
  c 
  p cnf 0 0";
    match parse_dimacs_cnf(s) {
        Err(_) => assert!(false),
        Ok(fmla) => assert_eq!(fmla.clauses, vec![]),
    }
}

#[test]
fn parse_formula_with_one_empty_clause() {
    let s = "c
  c a formula with no vars and one empty clauses
  c 
  p cnf 0 1
  0";
    match parse_dimacs_cnf(s) {
        Err(_) => assert!(false),
        Ok(fmla) => assert_eq!(fmla.clauses, vec![Clause { literals: vec![] }]),
    }
}

#[test]
fn parse_formula_with_one_unit_clause() {
    let s = "c
  c a formula with one var and one unit clause
  c 
  p cnf 1 1
  1 0";
    match parse_dimacs_cnf(s) {
        Err(_) => assert!(false),
        Ok(fmla) => assert_eq!(
            fmla.clauses,
            vec![Clause {
                literals: vec![Literal::new(1, Sign::Positive)]
            }]
        ),
    }
}

#[test]
fn parse_formula_with_one_non_unit_clause() {
    let s = "c
c a formula with 2 vars and 1 clause
c 
p cnf 2 1
1 -3 0";
    match parse_dimacs_cnf(s) {
        Err(_) => assert!(false),
        Ok(fmla) => assert_eq!(
            fmla.clauses,
            vec![Clause {
                literals: vec![
                    Literal::new(1, Sign::Positive),
                    Literal::new(3, Sign::Negative)
                ]
            }]
        ),
    }
}

#[test]
fn parse_formula_with_multiple_unit_clauses() {
    let s = "c
c a formula with 3 vars and 3 unit clause
c 
p cnf 3 3
1 0
-2 0
3 0";
    match parse_dimacs_cnf(s) {
        Err(_) => assert!(false),
        Ok(fmla) => assert_eq!(
            fmla.clauses,
            vec![
                Clause {
                    literals: vec![Literal::new(1, Sign::Positive),]
                },
                Clause {
                    literals: vec![Literal::new(2, Sign::Negative)]
                },
                Clause {
                    literals: vec![Literal::new(3, Sign::Positive)]
                }
            ]
        ),
    }
}

#[test]
fn parse_formula_without_comments() {
    let s = "p cnf 1 1
  1 0";
    match parse_dimacs_cnf(s) {
        Err(_) => assert!(false),
        Ok(fmla) => assert_eq!(
            fmla.clauses,
            vec![Clause {
                literals: vec![Literal::new(1, Sign::Positive)]
            }]
        ),
    }
}

#[test]
fn parsing_fails_without_spec_line() {
    let s = "c
  c a formula with one var and one unit clause
  c 
  1 0";
    match parse_dimacs_cnf(s) {
        Err(e) => assert_eq!(e, ParseError::BadComment),
        Ok(_) => assert!(false),
    }
}

#[test]
fn parsing_fails_when_comment_after_spec_line() {
    let s1 = "c
  c a formula with one var and one unit clause
  c 
  p cnf 1 1
  c another comment
  1 0";
    match parse_dimacs_cnf(s1) {
        Err(e) => assert_eq!(e, ParseError::BadSequencing),
        Ok(_) => assert!(false),
    };

    let s2 = "c
  c a formula with one var and two unit clauses
  c 
  p cnf 1 2
  1 0
  c
  -1 0";
    match parse_dimacs_cnf(s2) {
        Err(e) => assert_eq!(e, ParseError::BadSequencing),
        Ok(_) => assert!(false),
    };
}

#[test]
fn parsing_fails_when_spec_doesnt_match_fmla() {
    let s1 = "c
    c spec has fewer clauses than listed
    c
    c
    p cnf 5 4
    1 -5 4 0
    -1 5 3 4 0
    -3 -4 0";
    match parse_dimacs_cnf(s1) {
        Ok(_) => assert!(false),
        Err(e) => assert_eq!(e, ParseError::SpecificationMismatch),
    };

    let s2 = "c
    c spec has fewer vars than listed
    c
    c
    p cnf 2 3
    1 -5 4 0
    -1 5 3 4 0
    -3 -4 0";
    match parse_dimacs_cnf(s2) {
        Ok(_) => assert!(false),
        Err(e) => assert_eq!(e, ParseError::SpecificationMismatch),
    };

    let s3 = "c
    c spec has more clauses than listed
    c
    c
    p cnf 5 2
    1 -5 4 0
    -1 5 3 4 0
    -3 -4 0";
    match parse_dimacs_cnf(s3) {
        Ok(_) => assert!(false),
        Err(e) => assert_eq!(e, ParseError::SpecificationMismatch),
    };
}

#[test]
fn parsing_fails_when_spec_is_malformed() {
    let s1 = "c
  c a formula with one var and one unit clause
  c 
  p cnf 1
  1 0";
    match parse_dimacs_cnf(s1) {
        Err(e) => assert_eq!(e, ParseError::BadSpecification),
        Ok(_) => assert!(false),
    };

    let s2 = "c
  c a formula with one var and one unit clause
  c 
  p cnf
  1 0";
    match parse_dimacs_cnf(s2) {
        Err(e) => assert_eq!(e, ParseError::BadSpecification),
        Ok(_) => assert!(false),
    }

    let s3 = "c
  c a formula with one var and one unit clause
  c 
  p cnf 1 a
  1 0";
    match parse_dimacs_cnf(s3) {
        Err(e) => assert_eq!(e, ParseError::BadSpecification),
        Ok(_) => assert!(false),
    }
}

#[test]
fn parsing_fails_if_multiple_spec_lines() {
    let s = "c
c a formula with 2 vars and 1 clause
c 
p cnf 2 1
p cnf 2 1
1 -3 0";
    match parse_dimacs_cnf(s) {
        Err(e) => assert_eq!(e, ParseError::BadSequencing),
        Ok(_) => assert!(false),
    }
}

#[test]
fn parsing_fails_when_clause_is_malformed() {
    let s1 = "c
  c a formula with one var and one unit clause
  c 
  p cnf 1 1
  1 c 0";
    match parse_dimacs_cnf(s1) {
        Err(e) => assert_eq!(e, ParseError::MalformedLiteral),
        Ok(_) => assert!(false),
    }

    let s2 = "p cnf 2 2
  1 -2 0
  2 -1";
    match parse_dimacs_cnf(s2) {
        Err(e) => assert_eq!(e, ParseError::MalformedClauseEnd),
        Ok(_) => assert!(false),
    }
}

#[test]
fn parsing_fails_when_unrecognized_chars_before_p_line() {
    let s1 = "c
  c a formula with one var and one unit clause
  d
  c 
  p cnf 1 1
  1 0";
    match parse_dimacs_cnf(s1) {
        Err(e) => assert_eq!(e, ParseError::BadComment),
        Ok(_) => assert!(false),
    }
}
