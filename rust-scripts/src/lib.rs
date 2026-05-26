use lambda_calculus::term::*;
use lambda_calculus::*;
use wasm_bindgen::prelude::wasm_bindgen;

#[wasm_bindgen(getter_with_clone)]
#[derive(Debug, Clone)]
pub struct Res {
    pub encoded: String,
    pub debruijn: String,
    pub fokker_size: usize,
    pub lc: bool,
    pub all0: bool,
    pub no_duplicate: bool,
    pub every_bvar_is_used: bool,
    pub has_beta_redex: bool,
    pub eta_normal_form: Option<String>,
    pub two_vars_are_enough: bool,
    pub priority: String,
    pub difficulty: String,
    pub code_template: String,
}

#[wasm_bindgen]
pub fn parse_term_in_any_format(x: &str) -> Option<Res> {
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

    let xs: Vec<_> = x.trim().chars().collect();
    let t;

    if let Ok(a) = parse(&x, DeBruijn) {
        t = a;
    } else if let Ok(a) = parse(&x, Classic) {
        t = a;
    } else if let Some((a, _)) = Term::decode_fuel(&xs) {
        t = a;
    } else {
        return None;
    }

    let eta_normal_form = match t.lc() {
        true => match t.has_eta_redex() {
            true => {
                let x = t.clone().eta_reduce();
                assert!(x.lc());
                assert_ne!(t, x);
                Some(format!("{:?}", x))
            }
            false => None,
        },
        false => None,
    };

    let priority = if t.all0() {
        "high"
    } else if t.no_duplicate() && t.two_vars_are_enough() && t.every_bvar_used() {
        "medium"
    } else {
        "low"
    };

    let difficulty = if t.all0() {
        "easy"
    } else if t.no_duplicate() && t.two_vars_are_enough() && t.every_bvar_used() {
        "medium"
    } else {
        "hard"
    };

    let res = Res {
        encoded: t.encode(),
        debruijn: format!("{:?}", t),
        fokker_size: t.fokker_size(),
        lc: t.lc(),
        all0: t.all0(),
        no_duplicate: t.no_duplicate(),
        every_bvar_is_used: t.every_bvar_used(),
        has_beta_redex: t.has_beta_redex(),
        eta_normal_form,
        two_vars_are_enough: t.two_vars_are_enough(),
        priority: priority.to_string(),
        difficulty: difficulty.to_string(),
        code_template: format!(
            "def Term_{0}: Term String := {1}

theorem {0}_is_not_basis : not_basis Term_{0} := by sorry",
            t.encode(),
            t.print_lean(),
        ),
    };

    Some(res)
}
