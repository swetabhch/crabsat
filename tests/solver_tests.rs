use crabsat::cnf::cnf::*;
use crabsat::solver::solver::*;
use std::collections::HashMap;

#[test]
fn solve_empty_formula() {
    let formula = CNFFormula { clauses: vec![] };
    assert_eq!(solve(formula), SATResult::SAT(HashMap::new()));
}

#[test]
fn solve_formula_with_only_empty_clause() {
    let formula = CNFFormula {
        clauses: vec![Clause { literals: vec![] }],
    };
    assert_eq!(solve(formula), SATResult::UNSAT);
}

#[test]
fn solve_formula_with_misc_clauses_and_empty_clause() {
    let c1 = Clause {
        literals: vec![Literal::new(1, Sign::Positive)],
    };
    let c2 = Clause {
        literals: vec![
            Literal::new(1, Sign::Negative),
            Literal::new(2, Sign::Positive),
        ],
    };
    let c3 = Clause { literals: vec![] };
    let formula = CNFFormula {
        clauses: vec![c1, c2, c3],
    };
    assert_eq!(solve(formula), SATResult::UNSAT);
}

#[test]
fn solve_formula_with_only_a_unit_clause() {
    let clauses = vec![Clause {
        literals: vec![Literal::new(1, Sign::Positive)],
    }];
    let formula = CNFFormula { clauses };
    let mut soln = HashMap::new();
    soln.insert(1, true);
    assert_eq!(solve(formula), SATResult::SAT(soln));
}

#[test]
fn solve_formula_with_multiple_unit_clauses() {
    let clauses = vec![
        Clause {
            literals: vec![Literal::new(1, Sign::Positive)],
        },
        Clause {
            literals: vec![Literal::new(2, Sign::Negative)],
        },
        Clause {
            literals: vec![Literal::new(5, Sign::Positive)],
        },
    ];
    let formula = CNFFormula { clauses };
    let mut soln = HashMap::new();
    soln.insert(1, true);
    soln.insert(2, false);
    soln.insert(5, true);
    assert_eq!(solve(formula), SATResult::SAT(soln));
}

#[test]
fn solve_formula_with_one_clause() {
    // Only one clause, so any of the literals could be true
    let l1 = Literal::new(1, Sign::Positive);
    let l2 = Literal::new(2, Sign::Positive);
    let l3 = Literal::new(5, Sign::Negative);
    let clauses = vec![Clause {
        literals: vec![l1, l2, l3],
    }];
    let soln = solve(CNFFormula { clauses });
    match soln {
        SATResult::UNSAT => assert!(false),
        SATResult::SAT(soln) => {
            assert!(*soln.get(&1).unwrap() || *soln.get(&2).unwrap() || !*soln.get(&5).unwrap())
        }
    };
}

#[test]
fn solve_formula_with_contradictory_unit_clauses() {
    let clauses = vec![
        Clause {
            literals: vec![Literal::new(1, Sign::Positive)],
        },
        Clause {
            literals: vec![Literal::new(2, Sign::Negative)],
        },
        Clause {
            literals: vec![Literal::new(1, Sign::Negative)],
        },
    ];
    let formula = CNFFormula { clauses };
    assert_eq!(solve(formula), SATResult::UNSAT);
}

#[test]
fn solve_non_trivial_unsat_formula() {
    let one_pos = Literal::new(1, Sign::Positive);
    let one_neg = Literal::new(1, Sign::Negative);
    let two_pos = Literal::new(2, Sign::Positive);
    let two_neg = Literal::new(2, Sign::Negative);
    let c1 = Clause {
        literals: vec![one_pos, two_pos],
    };
    let c2 = Clause {
        literals: vec![one_pos, two_neg],
    };
    let c3 = Clause {
        literals: vec![one_neg, two_pos],
    };
    let c4 = Clause {
        literals: vec![one_neg, two_neg],
    };
    let formula = CNFFormula {
        clauses: vec![c1, c2, c3, c4],
    };
    assert_eq!(solve(formula), SATResult::UNSAT);
}

#[test]
fn solve_simple_sat_example() {
    let c1 = Clause {
        literals: vec![
            Literal::new(1, Sign::Positive),
            Literal::new(3, Sign::Negative),
        ],
    };
    let c2 = Clause {
        literals: vec![
            Literal::new(2, Sign::Positive),
            Literal::new(3, Sign::Positive),
            Literal::new(1, Sign::Negative),
        ],
    };
    let formula = CNFFormula {
        clauses: vec![c1, c2],
    };
    if let SATResult::SAT(soln) = solve(formula) {
        assert!(*soln.get(&2).unwrap());
        assert!(*soln.get(&1).unwrap() || !*soln.get(&3).unwrap());
    } else {
        assert!(false);
    }
}
