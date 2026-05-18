import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullEta
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBetaEtaConfluence
import Mathlib.Data.Set.Card
import FokkerChallenge.Basic
import FokkerChallenge.EnhancedCslib.CountBvar
import FokkerChallenge.EnhancedCslib.Fmt
import FokkerChallenge.EncoderDecoder.Basic

def stringToBits (s : String) : List Bool := do
  s.toList.foldr
    (fun c acc => match c with
                  | '0' => (false :: acc)
                  | '1' => (true :: acc)
                  | _   => (acc)
    )
    []

def main (args : List String) : IO Unit := do
  for arg in args do
    let arg := stringToBits arg
    match Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.decode arg with
    | some t => IO.println s!"decoded: {t}"
    | none => IO.println "invalid BLC bitstring"
