use cnf::cnf_structs;

pub mod cnf;

fn main() {
    let lit_1 = cnf_structs::Literal {
        name: 1,
        sign: cnf_structs::Sign::Positive,
    };
    println!("Hello, {:?}!", lit_1);
}
