import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Congruence
import FokkerChallenge.EnhancedCslib.Basic
import Mathlib.Data.Finset.Lattice.Basic

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

def fokker_size : (Term String) -> Nat
| bvar _ => 0
| fvar _ => 0
| abs t => 1 + fokker_size t
| app t1 t2 => 1 + fokker_size t1 + fokker_size t2

theorem fokker_size_openrec {x M}: (i: Nat) -> (openRec i (fvar x) M).fokker_size = M.fokker_size := by
induction M with (unfold openRec fokker_size; grind)

def r_preserves (f: Term String -> Bool) (R : Term String → Term String → Prop) : Prop :=
  ∀ M N, R M N → f M → f N

def no_redex: Term String → Bool
  | Term.bvar _ => true
  | Term.fvar _ => true
  | Term.abs t => no_redex t
  | Term.app (Term.abs _) _ => false
  | Term.app t1 t2 => no_redex t1 && no_redex t2

/-
theorem no_redex_false_equiv_full_beta {M}: no_redex M = false <-> ∃ N, FullBeta M N := by
induction M with
| bvar _ => unfold no_redex
            simp
            intros _ h
            cases h
            rename_i h
            cases h
| fvar _ => unfold no_redex
            simp
            intros _ h
            cases h
            rename_i h
            cases h
| abs M ih => unfold no_redex
              rw [ih]
              constructor <;> intros h <;> obtain ⟨N, h⟩ := h
              . exists N.abs
                apply Xi.abs M.fv
                intros x _
                unfold open'
                rw [<- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.open_lc]
                rw [<- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.open_lc]
                assumption
                . apply Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullBeta.step_lc_r h
                . apply Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullBeta.step_lc_l h
              . cases h with
                | base h => cases h
                | abs xs h => rename_i N
                              exists N
                              -- impossible to prove
                              sorry
| app _ _ _ _ => sorry
-/

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
