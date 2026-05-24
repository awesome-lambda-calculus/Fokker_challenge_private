use lambda_calculus::term::*;
use lambda_calculus::*;
use wasm_bindgen::prelude::wasm_bindgen;

#[wasm_bindgen]
pub fn parse_term_in_any_format(x: &str) -> Option<String> {
    let x = x.replace("Term.app", " ");
    let x = x.replace("Term.bvar", " ");
    let x = x.replace("Term.abs", "λ");

    let x = x.replace(".app", " ");
    let x = x.replace(".bvar", " ");
    let x = x.replace(".abs", "λ");

    let x = x.replace("app", " ");
    let x = x.replace("bvar", " ");
    let x = x.replace("abs", "λ");

    let x = x.replace("var", " ");
    let x = x.replace("lam", "λ");

    let t;

    if let Ok(a) = parse(&x, DeBruijn) {
        t = a;
    } else if let Ok(a) = parse(&x, Classic) {
        t = a;
    } else {
        return None;
    }

    let s = format!(
        "def Term_{0}: Term String := {1}

theorem {0}_is_not_basis : not_basis Term_{0} := by sorry",
        t.encode(),
        t.print_lean(),
    );
    Some(s)
}
