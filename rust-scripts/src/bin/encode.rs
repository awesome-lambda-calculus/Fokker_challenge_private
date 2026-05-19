use lambda_calculus::term::*;
use lambda_calculus::*;
use lambda_calculus::{abs, app, beta, combinators::K, data::num::convert::IntoChurchNum};
use std::env::args;

fn main() {
    let t = args()
        .nth(1)
        .as_ref()
        .map(|x| parse(x, DeBruijn).unwrap())
        .unwrap();

    println!(
        "def Term_{0}: Term String := {1}

theorem {0}_is_not_basis : not_basis Term_{0} := by sorry",
        t.encode(),
        t.print_lean(),
    );
}
