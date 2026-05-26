import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBetaEtaConfluence
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Congruence
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.LcAt
import Cslib.Foundations.Data.HasFresh
import FokkerChallenge.EnhancedCslib.NormalForm
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

theorem normal_K : Relation.Normal FullBetaEta K := by
  rw [<- normal_fullBetaEta_iff_no_beta_eta_redex]
  decide

def S : Term String :=
abs (abs (abs (
    app (app (bvar 2) (bvar 0))   -- x z
        (app (bvar 1) (bvar 0))   -- y z
  )))

/-
  M combinator in BAMT combinator systems
  M = λx.x x
-/
def M : Term String := abs (app (bvar 0) (bvar 0))

/-
  Generated terms (application closure)
-/
inductive Gen (Y: Term String) : Term String → Prop where
  | base : Gen Y Y
  | app {M N}  : Gen Y M → Gen Y N → Gen Y (app M N)

theorem gen_lc {Y M} (h: Gen Y M) : Y.LC -> M.LC := by
induction h with grind

def not_basis (t: Term String) := ∃ X, X.LC /\ X.fv = ∅ /\ ∀ Y, Gen t Y -> Relation.ReflTransGen FullBetaEta Y X -> False

-- 给定具体的 finset, 很容易证明
-- 但是证明一个通用的, 会方便一点
theorem not_basis_of_finite_beta_eta_reducts (t: Term String) (fs : Finset (Term String))
(h: ∀ X, Gen t X -> ∃ Y, Relation.ReflTransGen FullBetaEta X Y /\ Y ∈ fs) : not_basis t := by
unfold not_basis
sorry

end Term

end LambdaCalculus.LocallyNameless.Untyped

end Cslib
