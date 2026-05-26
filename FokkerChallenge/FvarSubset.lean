import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullEta
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBetaEtaConfluence
import Mathlib.Data.Set.Card
import FokkerChallenge.Basic

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

def r_preserves_fvar_subset (R : Term String → Term String → Prop) : Prop :=
  ∀ M N, R M N → N.fv ⊆ M.fv

theorem beta_preserves_fvar_subset: r_preserves_fvar_subset Beta := by
intros M N hmn
cases hmn
rename_i M N lcm lcn
unfold open'
conv =>
  rhs
  unfold fv
have h:= open_preserve_not_fvar 0 M N
cases h <;> rename_i h <;> rw [h] <;> grind

theorem eta_preserves_fvar_subset: r_preserves_fvar_subset Eta := by
intros M N hmn
cases hmn
conv =>
  rhs
  unfold fv
  unfold fv
grind

theorem xi_preserves_fvar_subset {R: Term String → Term String → Prop} :
  r_preserves_fvar_subset R → r_preserves_fvar_subset (Xi R) := by
intros hR M N hmn
induction hmn with
| base _ => tauto
| appL _ _ _ => grind
| appR _ _ _ => grind
| abs xs _ ih =>  rename_i M N _
                  unfold fv
                  have h4 : ∃ x : String, x ∉ xs ∪ M.fv ∪ N.fv := by apply Finset.exists_not_mem_of_card_lt_enatCard; simp
                  obtain ⟨x, hx⟩ := h4
                  specialize ih x (by grind)
                  unfold open' at ih
                  have h := open_preserve_not_fvar 0 M (fvar x)
                  have g := open_preserve_not_fvar 0 N (fvar x)
                  cases h <;> rename_i h <;> rw [h] at ih <;> cases g <;> rename_i h <;> rw [h] at ih
                  any_goals grind
                  simp at ih
                  rw [Finset.insert_subset_insert_iff] at ih
                  assumption
                  grind
