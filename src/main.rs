use clap::Parser;
use crabsat::dpll_solver::dpll::*;
use crabsat::parser::parser::*;
use crabsat::solver::solver::*;
use std::{fs, process};

/// Take a file whose contents represent a CNF boolean formula written
/// in the DIMACS format. Solves the formula and produces the solution as
/// output.
#[derive(Parser)]
struct Cli {
    /// The path to the file to read
    path: std::path::PathBuf,
}

fn main() {
    let args = Cli::parse();
    let dimacs_bytes = &match fs::read(args.path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("Error reading file: {}", e);
            process::exit(1);
        }
    };
    let dimacs_str = match std::str::from_utf8(dimacs_bytes) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("Error in string literal conversion: {}", e);
            process::exit(1);
        }
    };
    let formula = match parse_dimacs_cnf(dimacs_str) {
        Ok(f) => f,
        Err(e) => {
            eprintln!("Error reading file: {}", e);
            process::exit(1);
        }
    };
    let solver = DPLLSolver {};
    println!("{}", solver.solve(formula));
}
