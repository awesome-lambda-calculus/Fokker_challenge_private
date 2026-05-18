import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Congruence
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.LcAt
import Cslib.Foundations.Data.HasFresh
import FokkerChallenge.EnhancedCslib.Basic
import Mathlib.Data.Finset.Lattice.Basic

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

@[simp, scoped grind =]
def fokker_size : (Term String) -> Nat
| bvar _ => 0
| fvar _ => 0
| abs t => 1 + fokker_size t
| app t1 t2 => 1 + fokker_size t1 + fokker_size t2

theorem fokker_size_openrec {x M}: (i: Nat) -> (openRec i (fvar x) M).fokker_size = M.fokker_size := by
induction M with (unfold openRec fokker_size; grind)

def r_preserves (f: Term String -> Bool) (R : Term String → Term String → Prop) : Prop :=
  ∀ M N, R M N → f M → f N


/-
  K = λx y. x
-/
def K : Term String := abs (abs (bvar 1))

def S : Term String :=
abs (abs (abs (
    app (app (bvar 2) (bvar 0))   -- x z
        (app (bvar 1) (bvar 0))   -- y z
  )))

/-
  omega = λx y. x
-/
def omega : Term String := abs (app (bvar 0) (bvar 0))

/-
  Generated terms (application closure)
-/
inductive Gen (Y: Term String) : Term String → Prop where
  | base : Gen Y Y
  | app {M N}  : Gen Y M → Gen Y N → Gen Y (app M N)

end Term

end LambdaCalculus.LocallyNameless.Untyped

end Cslib
