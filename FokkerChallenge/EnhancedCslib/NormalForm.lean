import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBetaConfluence
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Congruence
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBetaEtaConfluence
import FokkerChallenge.EnhancedCslib.Basic
import Mathlib.Data.Finset.Lattice.Basic

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

def has_beta_redex: Term String → Bool
  | Term.bvar _ => false
  | Term.fvar _ => false
  | Term.abs t => has_beta_redex t
  | Term.app (Term.abs _) _ => true
  | Term.app t1 t2 => has_beta_redex t1 || has_beta_redex t2

private lemma has_beta_redex_openRec (i : ℕ) (x : String) (M : Term String) :
    has_beta_redex (Term.openRec i (Term.fvar x) M) = has_beta_redex M := by
  induction M generalizing i with
  | bvar j =>
    show has_beta_redex (if i = j then Term.fvar x else Term.bvar j) = false
    split <;> rfl
  | fvar _ => rfl
  | abs t ih =>
    show has_beta_redex (Term.openRec (i + 1) (Term.fvar x) t) = has_beta_redex t
    exact ih (i + 1)
  | app l r ih_l ih_r =>
    cases l with
    | bvar j =>
      show has_beta_redex (Term.app (if i = j then Term.fvar x else Term.bvar j)
            (Term.openRec i (Term.fvar x) r)) = has_beta_redex r
      split
      · show (false || has_beta_redex (Term.openRec i (Term.fvar x) r)) = has_beta_redex r
        rw [ih_r]; rfl
      · show (false || has_beta_redex (Term.openRec i (Term.fvar x) r)) = has_beta_redex r
        rw [ih_r]; rfl
    | fvar _ =>
      show (false || has_beta_redex (Term.openRec i (Term.fvar x) r)) = has_beta_redex r
      rw [ih_r]; rfl
    | abs _ => rfl
    | app l1 l2 =>
      show (has_beta_redex (Term.app (Term.openRec i (Term.fvar x) l1)
              (Term.openRec i (Term.fvar x) l2))
            || has_beta_redex (Term.openRec i (Term.fvar x) r))
            = (has_beta_redex (Term.app l1 l2) || has_beta_redex r)
      rw [show
            has_beta_redex (Term.app (Term.openRec i (Term.fvar x) l1)
              (Term.openRec i (Term.fvar x) l2))
            = has_beta_redex (Term.app l1 l2)
          from ih_l i, ih_r i]

private lemma has_beta_redex_of_full_beta {M N : Term String} (h : FullBeta M N) :
    has_beta_redex M = true := by
  induction h with
  | base h_b =>
    cases h_b with | beta _ _ => rfl
  | @appL Z M' _ _ _ ih =>
    cases Z with
    | abs _ => rfl
    | bvar _ =>
      show (false || has_beta_redex M') = true
      simp [ih]
    | fvar _ =>
      show (false || has_beta_redex M') = true
      simp [ih]
    | app a b =>
      show (has_beta_redex (Term.app a b) || has_beta_redex M') = true
      simp [ih]
  | @appR Z M' _ _ _ ih =>
    cases M' with
    | abs _ => rfl
    | bvar _ => simp [has_beta_redex] at ih
    | fvar _ => simp [has_beta_redex] at ih
    | app a b =>
      show (has_beta_redex (Term.app a b) || has_beta_redex Z) = true
      simp [ih]
  | @abs M' _ xs _ ih =>
    show has_beta_redex M' = true
    have ⟨x, hx⟩ := fresh_exists xs
    rw [← has_beta_redex_openRec 0 x M']
    exact ih x hx

theorem has_beta_redex_equiv_full_beta {M : Term String} :
    has_beta_redex M ∧ M.LC ↔ ∃ N, FullBeta M N := by
  constructor
  · rintro ⟨h_redex, h_lc⟩
    induction h_lc with
    | fvar _ => simp [has_beta_redex] at h_redex
    | @abs L e h_body ih =>
      have h_redex_e : has_beta_redex e = true := h_redex
      have ⟨x, hx⟩ := fresh_exists (L ∪ e.fv : Finset String)
      simp only [Finset.mem_union, not_or] at hx
      obtain ⟨hxL, hxe⟩ := hx
      have h_redex_open : has_beta_redex (e ^ Term.fvar x) = true := by
        show has_beta_redex (Term.openRec 0 (Term.fvar x) e) = true
        rw [has_beta_redex_openRec]; exact h_redex_e
      have ⟨N, hN⟩ := ih x hxL h_redex_open
      have hclose : ((e ^ Term.fvar x) ^* x).abs ⭢βᶠ (N ^* x).abs :=
        FullBeta.step_abs_close hN
      rw [show (e ^ Term.fvar x) ^* x = e from (open_close_var x e hxe).symm] at hclose
      exact ⟨_, hclose⟩
    | @app l r lc_l lc_r ih_l ih_r =>
      cases l with
      | bvar i => cases lc_l
      | fvar y =>
        have hr : has_beta_redex r = true := h_redex
        have ⟨N, hN⟩ := ih_r hr
        exact ⟨_, Xi.appL lc_l hN⟩
      | abs t =>
        exact ⟨t ^ r, .base (.beta lc_l lc_r)⟩
      | app l1 l2 =>
        have h_or : (has_beta_redex (Term.app l1 l2) || has_beta_redex r) = true := h_redex
        by_cases hl : has_beta_redex (Term.app l1 l2) = true
        · have ⟨N, hN⟩ := ih_l hl
          exact ⟨_, Xi.appR lc_r hN⟩
        · have hl_false : has_beta_redex (Term.app l1 l2) = false := by
            cases hh : has_beta_redex (Term.app l1 l2)
            · rfl
            · exact absurd hh hl
          rw [hl_false] at h_or
          have hr : has_beta_redex r = true := h_or
          have ⟨N, hN⟩ := ih_r hr
          exact ⟨_, Xi.appL lc_l hN⟩
  · rintro ⟨N, hN⟩
    exact ⟨has_beta_redex_of_full_beta hN, FullBeta.step_lc_l hN⟩

theorem no_beta_redex_refl {M N : Term String} (hn : has_beta_redex M = false)
    (h : Relation.ReflTransGen FullBeta M N) : M = N := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => rfl
  | head step _ _ =>
    have h1 := has_beta_redex_of_full_beta step
    rw [hn] at h1
    exact absurd h1 (by decide)

/-- `has_bvar k M` returns `true` iff bound variable index `k`
(measured from outside `M`) appears free anywhere in `M`. -/
def has_bvar (k : ℕ) : Term String → Bool
  | Term.bvar i => decide (i = k)
  | Term.fvar _ => false
  | Term.abs t => has_bvar (k + 1) t
  | Term.app l r => has_bvar k l || has_bvar k r

/-- `is_eta_pattern t` recognises the body of an η-redex: `t = app A (bvar 0)`
where `A` does not reference `bvar 0`. -/
def is_eta_pattern : Term String → Bool
  | Term.app A (Term.bvar 0) => !has_bvar 0 A
  | _ => false

/-- `has_eta_redex M` returns `true` iff `M` contains a sub-term of the form
`abs (app A (bvar 0))` where `A` does not reference the immediately binding
abstraction. After fully opening the surrounding binders such a sub-term
becomes a real η-redex. -/
def has_eta_redex : Term String → Bool
  | Term.bvar _ => false
  | Term.fvar _ => false
  | Term.abs t => is_eta_pattern t || has_eta_redex t
  | Term.app l r => has_eta_redex l || has_eta_redex r

private lemma has_bvar_openRec_fvar {k i : ℕ} {x : String} (M : Term String)
    (h : k ≠ i) :
    has_bvar k (Term.openRec i (Term.fvar x) M) = has_bvar k M := by
  induction M generalizing k i with
  | bvar j =>
    show has_bvar k (if i = j then Term.fvar x else Term.bvar j)
        = has_bvar k (Term.bvar j)
    split
    case isTrue h_eq =>
      show false = decide (j = k)
      have : ¬ (j = k) := fun hjk => h (h_eq ▸ hjk.symm)
      simp [this]
    case isFalse _ => rfl
  | fvar _ => rfl
  | abs t ih =>
    show has_bvar (k + 1) (Term.openRec (i + 1) (Term.fvar x) t)
        = has_bvar (k + 1) t
    exact ih (by omega)
  | app l r ihl ihr =>
    show (has_bvar k (Term.openRec i (Term.fvar x) l)
          || has_bvar k (Term.openRec i (Term.fvar x) r))
        = (has_bvar k l || has_bvar k r)
    rw [ihl h, ihr h]

private lemma has_bvar_eq_false_of_LC {M : Term String} (h : LC M) :
    ∀ k, has_bvar k M = false := by
  induction h with
  | fvar _ => intro k; rfl
  | @abs L e _ ih =>
    intro k
    show has_bvar (k + 1) e = false
    have ⟨x, hx⟩ := fresh_exists L
    have h1 : has_bvar (k + 1) (e ^ Term.fvar x) = false := ih x hx (k + 1)
    rw [show (e ^ Term.fvar x) = Term.openRec 0 (Term.fvar x) e from rfl] at h1
    rwa [has_bvar_openRec_fvar e (by omega)] at h1
  | app _ _ ih_l ih_r =>
    intro k
    show (has_bvar k _ || has_bvar k _) = false
    rw [ih_l k, ih_r k]; rfl

private lemma is_eta_pattern_openRec {i : ℕ} {x : String} (t : Term String)
    (h : i ≠ 0) :
    is_eta_pattern (Term.openRec i (Term.fvar x) t) = is_eta_pattern t := by
  cases t with
  | bvar j =>
    show is_eta_pattern (if i = j then Term.fvar x else Term.bvar j) = false
    split <;> rfl
  | fvar _ => rfl
  | abs _ => rfl
  | app l r =>
    show is_eta_pattern (Term.app (Term.openRec i (Term.fvar x) l)
                                  (Term.openRec i (Term.fvar x) r))
        = is_eta_pattern (Term.app l r)
    cases r with
    | bvar j =>
      show is_eta_pattern (Term.app (Term.openRec i (Term.fvar x) l)
                                    (if i = j then Term.fvar x else Term.bvar j))
          = is_eta_pattern (Term.app l (Term.bvar j))
      split
      case isTrue h_eq =>
        -- i = j and i ≠ 0, so j ≠ 0, both sides `false`.
        have hj : j ≠ 0 := h_eq ▸ h
        simp [is_eta_pattern, hj]
      case isFalse _ =>
        cases j with
        | zero =>
          show (!has_bvar 0 (Term.openRec i (Term.fvar x) l)) = (!has_bvar 0 l)
          rw [has_bvar_openRec_fvar l (Ne.symm h)]
        | succ _ => rfl
    | fvar _ => rfl
    | abs _ => rfl
    | app _ _ => rfl

private lemma has_eta_redex_openRec (i : ℕ) (x : String) (M : Term String) :
    has_eta_redex (Term.openRec i (Term.fvar x) M) = has_eta_redex M := by
  induction M generalizing i with
  | bvar j =>
    show has_eta_redex (if i = j then Term.fvar x else Term.bvar j) = false
    split <;> rfl
  | fvar _ => rfl
  | abs t ih =>
    show (is_eta_pattern (Term.openRec (i + 1) (Term.fvar x) t)
          || has_eta_redex (Term.openRec (i + 1) (Term.fvar x) t))
        = (is_eta_pattern t || has_eta_redex t)
    rw [ih (i + 1), is_eta_pattern_openRec t (by omega)]
  | app l r ihl ihr =>
    show (has_eta_redex (Term.openRec i (Term.fvar x) l)
          || has_eta_redex (Term.openRec i (Term.fvar x) r))
        = (has_eta_redex l || has_eta_redex r)
    rw [ihl, ihr]

private lemma has_eta_redex_of_full_eta {M N : Term String} (h : FullEta M N) :
    has_eta_redex M = true := by
  induction h with
  | base h_e =>
    cases h_e with
    | eta lc_A =>
      rename_i A
      show (is_eta_pattern (Term.app A (Term.bvar 0)) || has_eta_redex _) = true
      have : has_bvar 0 A = false := has_bvar_eq_false_of_LC lc_A 0
      simp [is_eta_pattern, this]
  | @appL Z M' _ _ _ ih =>
    show (has_eta_redex Z || has_eta_redex M') = true
    simp [ih]
  | @appR Z M' _ _ _ ih =>
    show (has_eta_redex M' || has_eta_redex Z) = true
    simp [ih]
  | @abs M' _ xs _ ih =>
    show (is_eta_pattern M' || has_eta_redex M') = true
    have ⟨x, hx⟩ := fresh_exists xs
    have h1 : has_eta_redex (M' ^ Term.fvar x) = true := ih x hx
    rw [show (M' ^ Term.fvar x) = Term.openRec 0 (Term.fvar x) M' from rfl,
        has_eta_redex_openRec] at h1
    simp [h1]

/--
If `N.abs` has no β-redex and no η-redex anywhere, then `M` reaches `N.abs` by
forward `FullBetaEta` reductions iff they are merely `EqvGen`-related.

The previous `FullBeta`-only version is the special case where `has_eta_redex` is
ignored. Both `has_beta_redex` and `has_eta_redex` are required because either
kind of redex makes `N.abs` non-normal under `FullBetaEta`. In particular, just
asking for `N.fv = ∅` is not enough — e.g. `N := abs (app (bvar 1) (bvar 0))`
satisfies `N.fv = ∅` and `has_beta_redex N = false`, yet
`N.abs = abs (abs (app (bvar 1) (bvar 0)))` reduces by η to `abs (bvar 0)` after
opening the outer binder. The `has_eta_redex` check rules this out.
-/
theorem reflTransGen_iff_eqvGen_of_normal {M N : Term String}
    (hb : N.abs.has_beta_redex = false) (he : N.abs.has_eta_redex = false) :
    Relation.ReflTransGen FullBetaEta M N.abs ↔ Relation.EqvGen FullBetaEta M N.abs := by
  refine ⟨Relation.ReflTransGen.to_eqvGen, ?_⟩
  intro h
  have norm : Relation.Normal FullBetaEta N.abs := by
    rintro ⟨Y, hY⟩
    rcases hY with hbeta | heta
    · have h1 : has_beta_redex N.abs = true := has_beta_redex_of_full_beta hbeta
      rw [hb] at h1
      exact absurd h1 (by decide)
    · have h1 : has_eta_redex N.abs = true := has_eta_redex_of_full_eta heta
      rw [he] at h1
      exact absurd h1 (by decide)
  exact Relation.ChurchRosser.normal_eqvGen_reflTransGen
    (Relation.Confluent.toChurchRosser confluent_beta_eta) norm h

end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
