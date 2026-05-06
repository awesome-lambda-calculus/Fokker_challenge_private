import FokkerChallenge

def main : IO Unit := do
  let mut terms := []
  terms := terms ++ Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.gen_terms 2 0 0

  terms := terms ++ Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.gen_terms 3 0 0
  terms := terms ++ Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.gen_terms 2 1 0

  terms := terms ++ Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.gen_terms 4 0 0
  terms := terms ++ Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.gen_terms 3 1 0
  terms := terms ++ Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.gen_terms 2 2 0

  terms := terms ++ Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.gen_terms 5 0 0
  terms := terms ++ Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.gen_terms 4 1 0
  terms := terms ++ Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.gen_terms 3 2 0
  terms := terms ++ Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.gen_terms 2 3 0

  terms := terms ++ Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.gen_terms 6 0 0
  terms := terms ++ Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.gen_terms 5 1 0
  terms := terms ++ Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.gen_terms 4 2 0
  terms := terms ++ Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.gen_terms 3 3 0
  terms := terms ++ Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.gen_terms 2 4 0

  -- let len := terms.length
  -- IO.println s!"Solution: {len}"

  terms := terms.filter Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.no_redex
  -- let len := terms.length
  -- IO.println s!"Solution: {len}"

  terms := terms.filter (fun t => !Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.every_bvar_used t)
  -- let len := terms.length
  -- IO.println s!"Solution: {len}"

  terms := terms.filter (fun t => !Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.no_duplicate t)
  terms := terms.filter (fun t => !Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.all0_no_fvar_inside_abs t)
  let len := terms.length
  IO.println s!"{len} undecided"
  IO.println s!"{terms}"
