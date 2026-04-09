import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic
import Mathlib.Data.Set.Card

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

def count_bvar (k : Nat) : Term String → Nat
  | bvar n   => if n = k then 1 else 0
  | app M N => count_bvar k M + count_bvar k N
  | abs M   => count_bvar (k + 1) M
  | fvar _ => 0

theorem openRec_noop_of_count_bvar_zero {M N} :
  (i: Nat) -> count_bvar i M = 0 -> openRec i N M = M := by
induction M with
| bvar M => intros i h
            unfold openRec
            split
            . subst M
              unfold count_bvar at h
              simp at h
            . simp
| fvar M => intros i h
            unfold openRec
            rfl
| app a b ha hb =>  intros i h
                    unfold count_bvar at h
                    have g: count_bvar i a = 0 := by omega
                    specialize ha _ g
                    have g: count_bvar i b = 0 := by omega
                    specialize hb _ g
                    unfold openRec
                    rw [ha, hb]
| abs _ ih =>   intros i h
                unfold count_bvar at h
                unfold openRec
                simp
                apply ih
                assumption


theorem count_bvar_preserved_under_open_2 {x M} :
  (i j : Nat) → ¬ j = i → count_bvar j (M⟦i ↝ (fvar x)⟧) = count_bvar j M := by
induction M with
| fvar _ => simp [count_bvar, openRec]
| abs M hM => intros i j h
              simp [count_bvar, openRec]
              apply hM
              omega
| bvar M => intros i j _
            simp [count_bvar, openRec]
            split <;> split
            any_goals subst M
            any_goals subst j
            any_goals omega
            all_goals unfold count_bvar
            any_goals omega
            all_goals split
            all_goals tauto
| app a b ha hb =>  intros i j h
                    simp [count_bvar, openRec]
                    specialize ha i j h
                    specialize hb i j h
                    rw [ha, hb]

theorem openRec_fv_union {M N} : (i: Nat) -> count_bvar i M > 0 -> (openRec i N M).fv = M.fv ∪ N.fv := by
induction M with intros i h
| bvar _ => unfold openRec
            split
            . subst i
              conv =>
                right
                left
                unfold fv
              simp
            . unfold count_bvar at h
              split at h
              all_goals omega
| fvar _ => unfold count_bvar at h
            omega
| abs _ ih => unfold count_bvar at h
              unfold openRec
              conv =>
                right
                left
                unfold fv
              conv =>
                left
                unfold fv
              apply ih
              assumption
| app a b ha hb =>  unfold count_bvar at h
                    unfold openRec
                    conv =>
                      left
                      unfold fv
                    conv =>
                      right
                      left
                      unfold fv
                    have ga: count_bvar i a > 0 \/ count_bvar i a = 0 := by omega
                    have gb: count_bvar i b > 0 \/ count_bvar i b = 0 := by omega
                    cases ga <;> cases gb
                    any_goals omega
                    all_goals rename_i ga gb
                    any_goals try specialize ha _ ga
                    any_goals try specialize hb _ gb
                    . rw [ha]
                      rw [hb]
                      simp
                      apply congr
                      all_goals simp
                    . rw [ha]
                      apply (@openRec_noop_of_count_bvar_zero _ N) at gb
                      rw [gb]
                      simp
                      apply congr
                      simp
                      apply Finset.union_comm
                    . rw [hb]
                      apply (@openRec_noop_of_count_bvar_zero _ N) at ga
                      rw [ga]
                      simp_all

theorem count_bvar_even_of_locally_closed {N} : LC N -> (j: Nat) -> count_bvar j N = 0 := by
intros h
induction h with
| fvar x => unfold count_bvar
            simp
| app _ _ hi hj =>  unfold count_bvar
                    intros j
                    specialize hi j
                    specialize hj j
                    omega
| abs L e h ih => unfold count_bvar
                  intros j
                  have h4 : ∃ x : String, x ∉ L := by apply Finset.exists_not_mem_of_card_lt_enatCard; simp
                  obtain ⟨x, hx⟩ := h4
                  specialize ih x hx (j+1)
                  unfold open' at ih
                  rw [count_bvar_preserved_under_open_2] at ih
                  assumption
                  omega

theorem count_bvar_preserved_under_open {M N} :
  (i j : Nat) → ¬ j = i -> N.LC → count_bvar j M = count_bvar j (M⟦i ↝ N⟧) := by
induction M with
| bvar M => intros i j
            simp [count_bvar, openRec]
            split
            any_goals subst M
            any_goals split
            all_goals intros
            any_goals subst i
            any_goals omega
            . unfold count_bvar
              simp
            . symm
              apply count_bvar_even_of_locally_closed (by assumption)
            . unfold count_bvar
              split <;> omega
| fvar _ => simp [count_bvar, openRec]
| abs M hM => intros i j h
              simp [count_bvar, openRec]
              apply hM
              omega
| app a b ha hb =>
              intros i j _ h
              simp [count_bvar, openRec]
              rw [ha, hb]
              all_goals assumption
