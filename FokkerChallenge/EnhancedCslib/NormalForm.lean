import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBetaConfluence
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Congruence
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBetaEtaConfluence
import FokkerChallenge.EnhancedCslib.Basic
import Mathlib.Data.Finset.Lattice.Basic

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

def has_redex: Term String → Bool
  | Term.bvar _ => false
  | Term.fvar _ => false
  | Term.abs t => has_redex t
  | Term.app (Term.abs _) _ => true
  | Term.app t1 t2 => has_redex t1 || has_redex t2

private lemma has_redex_openRec (i : ℕ) (x : String) (M : Term String) :
    has_redex (Term.openRec i (Term.fvar x) M) = has_redex M := by
  induction M generalizing i with
  | bvar j =>
    show has_redex (if i = j then Term.fvar x else Term.bvar j) = false
    split <;> rfl
  | fvar _ => rfl
  | abs t ih =>
    show has_redex (Term.openRec (i + 1) (Term.fvar x) t) = has_redex t
    exact ih (i + 1)
  | app l r ih_l ih_r =>
    cases l with
    | bvar j =>
      show has_redex (Term.app (if i = j then Term.fvar x else Term.bvar j)
            (Term.openRec i (Term.fvar x) r)) = has_redex r
      split
      · show (false || has_redex (Term.openRec i (Term.fvar x) r)) = has_redex r
        rw [ih_r]; rfl
      · show (false || has_redex (Term.openRec i (Term.fvar x) r)) = has_redex r
        rw [ih_r]; rfl
    | fvar _ =>
      show (false || has_redex (Term.openRec i (Term.fvar x) r)) = has_redex r
      rw [ih_r]; rfl
    | abs _ => rfl
    | app l1 l2 =>
      show (has_redex (Term.app (Term.openRec i (Term.fvar x) l1)
              (Term.openRec i (Term.fvar x) l2))
            || has_redex (Term.openRec i (Term.fvar x) r))
            = (has_redex (Term.app l1 l2) || has_redex r)
      rw [show
            has_redex (Term.app (Term.openRec i (Term.fvar x) l1)
              (Term.openRec i (Term.fvar x) l2))
            = has_redex (Term.app l1 l2)
          from ih_l i, ih_r i]

private lemma has_redex_of_full_beta {M N : Term String} (h : FullBeta M N) :
    has_redex M = true := by
  induction h with
  | base h_b =>
    cases h_b with | beta _ _ => rfl
  | @appL Z M' _ _ _ ih =>
    cases Z with
    | abs _ => rfl
    | bvar _ =>
      show (false || has_redex M') = true
      simp [ih]
    | fvar _ =>
      show (false || has_redex M') = true
      simp [ih]
    | app a b =>
      show (has_redex (Term.app a b) || has_redex M') = true
      simp [ih]
  | @appR Z M' _ _ _ ih =>
    cases M' with
    | abs _ => rfl
    | bvar _ => simp [has_redex] at ih
    | fvar _ => simp [has_redex] at ih
    | app a b =>
      show (has_redex (Term.app a b) || has_redex Z) = true
      simp [ih]
  | @abs M' _ xs _ ih =>
    show has_redex M' = true
    have ⟨x, hx⟩ := fresh_exists xs
    rw [← has_redex_openRec 0 x M']
    exact ih x hx

theorem has_redex_equiv_full_beta {M : Term String} :
    has_redex M ∧ M.LC ↔ ∃ N, FullBeta M N := by
  constructor
  · rintro ⟨h_redex, h_lc⟩
    induction h_lc with
    | fvar _ => simp [has_redex] at h_redex
    | @abs L e h_body ih =>
      have h_redex_e : has_redex e = true := h_redex
      have ⟨x, hx⟩ := fresh_exists (L ∪ e.fv : Finset String)
      simp only [Finset.mem_union, not_or] at hx
      obtain ⟨hxL, hxe⟩ := hx
      have h_redex_open : has_redex (e ^ Term.fvar x) = true := by
        show has_redex (Term.openRec 0 (Term.fvar x) e) = true
        rw [has_redex_openRec]; exact h_redex_e
      have ⟨N, hN⟩ := ih x hxL h_redex_open
      have hclose : ((e ^ Term.fvar x) ^* x).abs ⭢βᶠ (N ^* x).abs :=
        FullBeta.step_abs_close hN
      rw [show (e ^ Term.fvar x) ^* x = e from (open_close_var x e hxe).symm] at hclose
      exact ⟨_, hclose⟩
    | @app l r lc_l lc_r ih_l ih_r =>
      cases l with
      | bvar i => cases lc_l
      | fvar y =>
        have hr : has_redex r = true := h_redex
        have ⟨N, hN⟩ := ih_r hr
        exact ⟨_, Xi.appL lc_l hN⟩
      | abs t =>
        exact ⟨t ^ r, .base (.beta lc_l lc_r)⟩
      | app l1 l2 =>
        have h_or : (has_redex (Term.app l1 l2) || has_redex r) = true := h_redex
        by_cases hl : has_redex (Term.app l1 l2) = true
        · have ⟨N, hN⟩ := ih_l hl
          exact ⟨_, Xi.appR lc_r hN⟩
        · have hl_false : has_redex (Term.app l1 l2) = false := by
            cases hh : has_redex (Term.app l1 l2)
            · rfl
            · exact absurd hh hl
          rw [hl_false] at h_or
          have hr : has_redex r = true := h_or
          have ⟨N, hN⟩ := ih_r hr
          exact ⟨_, Xi.appL lc_l hN⟩
  · rintro ⟨N, hN⟩
    exact ⟨has_redex_of_full_beta hN, FullBeta.step_lc_l hN⟩

theorem no_redex_refl {M N : Term String} (hn : has_redex M = false)
    (h : Relation.ReflTransGen FullBeta M N) : M = N := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => rfl
  | head step _ _ =>
    have h1 := has_redex_of_full_beta step
    rw [hn] at h1
    exact absurd h1 (by decide)

/--
Note: the original statement used `FullBetaEta`, but that is unprovable.
Counterexample: take `N := app (fvar f) (bvar 0)` so `has_redex N = false`,
yet `N.abs = abs (app (fvar f) (bvar 0))` is an η-redex reducing to `fvar f`.
With `M := fvar f`, `EqvGen FullBetaEta M N.abs` holds (via η) but
`ReflTransGen FullBetaEta M N.abs` does not.

The `FullBeta`-only version is genuinely true: if `N.abs` has no β-redex,
then by confluence every member of its `EqvGen`-class reaches it via
`ReflTransGen`.
-/
theorem reflTransGen_iff_eqvGen_of_normal {M N : Term String}
    (hn : N.has_redex = false) :
    Relation.ReflTransGen FullBeta M N.abs ↔ Relation.EqvGen FullBeta M N.abs := by
  refine ⟨Relation.ReflTransGen.to_eqvGen, ?_⟩
  intro h
  have norm : Relation.Normal FullBeta N.abs := by
    rintro ⟨_, hY⟩
    have h1 : has_redex N.abs = true := has_redex_of_full_beta hY
    have h2 : has_redex N.abs = false := hn
    rw [h2] at h1
    exact absurd h1 (by decide)
  exact Relation.ChurchRosser.normal_eqvGen_reflTransGen
    (Relation.Confluent.toChurchRosser confluence_beta) norm h

end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
