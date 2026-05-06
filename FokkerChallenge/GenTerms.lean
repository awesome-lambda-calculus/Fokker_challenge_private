import FokkerChallenge.Basic
import FokkerChallenge.CountBvar

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

def gen_terms : Nat → Nat → Nat → List (Term String)
  | 0, 0, depth => (List.range depth).map Term.bvar
  | lams, apps, depth =>
      let lambda_terms := if lams > 0 then
        (gen_terms (lams - 1) apps (depth + 1)).map Term.abs
      else
        []

      let app_terms := if apps > 0 then
        (List.range (lams + 1)).attach.flatMap fun ⟨left_l_nat, hl⟩ =>
        (List.range apps).attach.flatMap fun ⟨left_a_nat, ha⟩ =>
        let left_l  := left_l_nat
        let left_a  := left_a_nat
        let right_l := lams - left_l
        let right_a := apps - 1 - left_a
        -- The two `have`s below feed bounds to `decreasing_by`.
        have _hl : left_l_nat < lams + 1 := List.mem_range.mp hl
        have _ha : left_a_nat < apps := List.mem_range.mp ha
        (gen_terms left_l left_a depth).flatMap fun left =>
        (gen_terms right_l right_a depth).map fun right =>
        Term.app left right
      else
        []
      lambda_terms ++ app_terms
termination_by lams apps _ => lams + apps
decreasing_by
  all_goals simp_wf
  all_goals omega

/-- Number of `abs` constructors in a term. -/
def abs_count : Term String → Nat
  | bvar _ => 0
  | fvar _ => 0
  | abs t => 1 + abs_count t
  | app t1 t2 => abs_count t1 + abs_count t2

/-- Number of `app` constructors in a term. -/
def app_count : Term String → Nat
  | bvar _ => 0
  | fvar _ => 0
  | abs t => app_count t
  | app t1 t2 => 1 + app_count t1 + app_count t2

/-- The Fokker size decomposes as the count of abstractions plus the count of applications. -/
theorem fokker_size_eq_abs_count_add_app_count (M : Term String) :
    M.fokker_size = M.abs_count + M.app_count := by
  induction M with
  | bvar _ => rfl
  | fvar _ => rfl
  | abs M ih =>
    simp only [fokker_size, abs_count, app_count, ih]
    omega
  | app L R ihL ihR =>
    simp only [fokker_size, abs_count, app_count, ihL, ihR]
    omega

/-- `gen_terms` enumerates every term modulo three preconditions:
- `M` has no free variables (`gen_terms` only produces closed-modulo-bvars terms);
- every bound variable index in `M` is below the current binder depth `d`;
- the abs/app counts match `M`'s.
-/
theorem gen_terms_complete : ∀ (M : Term String) (d : Nat),
    M.fv = ∅ →
    (∀ k, k ≥ d → count_bvar k M = 0) →
    M ∈ gen_terms M.abs_count M.app_count d := by
  intro M
  induction M with
  | bvar n =>
    intro d _ hbv
    -- abs_count = app_count = 0; gen_terms 0 0 d = (List.range d).map bvar.
    have hn : n < d := by
      by_contra h
      have := hbv n (Nat.not_lt.mp h)
      simp [count_bvar] at this
    show bvar n ∈ gen_terms 0 0 d
    unfold gen_terms
    exact List.mem_map.mpr ⟨n, List.mem_range.mpr hn, rfl⟩
  | fvar x =>
    intro _ hfv _
    -- fv (fvar x) = {x}, contradicting fv = ∅.
    simp [fv] at hfv
  | abs M ih =>
    intro d hfv hbv
    -- Specialize ih at depth (d + 1) using the abs body.
    have hfv' : M.fv = ∅ := by simpa [fv] using hfv
    have hbv' : ∀ k, k ≥ d + 1 → count_bvar k M = 0 := by
      intro j hj
      have hk : j - 1 ≥ d := by omega
      have h := hbv (j - 1) hk
      -- count_bvar (j-1) (abs M) = count_bvar (j-1+1) M ≡ count_bvar j M
      have hjp : j - 1 + 1 = j := by omega
      rw [show count_bvar (j-1) (abs M) = count_bvar (j-1+1) M from rfl, hjp] at h
      exact h
    have ihM : M ∈ gen_terms M.abs_count M.app_count (d + 1) := ih (d + 1) hfv' hbv'
    -- Goal: abs M ∈ gen_terms (1 + M.abs_count) M.app_count d.
    -- The second equation lemma gives a clean unfolding (the side condition is vacuous).
    show abs M ∈ gen_terms (1 + M.abs_count) M.app_count d
    rw [gen_terms.eq_2 _ _ _ (by intro h; omega)]
    simp only [show (1 + M.abs_count) > 0 from by omega, if_true,
      show (1 + M.abs_count) - 1 = M.abs_count from by omega]
    apply List.mem_append_left
    exact List.mem_map_of_mem ihM
  | app L R ihL ihR =>
    intro d hfv hbv
    -- Decompose preconditions onto L and R.
    have hfv_union : L.fv ∪ R.fv = ∅ := by simpa [fv] using hfv
    have hfvL : L.fv = ∅ := (Finset.union_eq_empty.mp hfv_union).1
    have hfvR : R.fv = ∅ := (Finset.union_eq_empty.mp hfv_union).2
    have hbvL : ∀ k, k ≥ d → count_bvar k L = 0 := by
      intro k hk
      have h := hbv k hk
      simp only [count_bvar] at h
      omega
    have hbvR : ∀ k, k ≥ d → count_bvar k R = 0 := by
      intro k hk
      have h := hbv k hk
      simp only [count_bvar] at h
      omega
    have ihL' : L ∈ gen_terms L.abs_count L.app_count d := ihL d hfvL hbvL
    have ihR' : R ∈ gen_terms R.abs_count R.app_count d := ihR d hfvR hbvR
    -- Goal: app L R ∈ gen_terms (a_L + a_R) (1 + b_L + b_R) d.
    -- Use the second equation lemma; pick the right (app_terms) branch.
    show app L R ∈ gen_terms (L.abs_count + R.abs_count) (1 + L.app_count + R.app_count) d
    rw [gen_terms.eq_2 _ _ _ (by intro _ h; omega)]
    apply List.mem_append_right
    simp only [show (1 + L.app_count + R.app_count) > 0 from by omega, if_true]
    -- Pick left_l_nat = a_L and left_a_nat = b_L; the inner right_l reduces to a_R, right_a to b_R.
    refine List.mem_flatMap.mpr ⟨⟨L.abs_count, ?_⟩, ?_, ?_⟩
    · -- L.abs_count ∈ List.range (L.abs_count + R.abs_count + 1)
      rw [List.mem_range]; omega
    · -- the subtype element is in `.attach`
      exact List.mem_attach _ _
    · -- inner flatMap over (List.range apps).attach
      refine List.mem_flatMap.mpr ⟨⟨L.app_count, ?_⟩, ?_, ?_⟩
      · rw [List.mem_range]; omega
      · exact List.mem_attach _ _
      · refine List.mem_flatMap.mpr ⟨L, ihL', ?_⟩
        -- right_l = (a_L + a_R) - a_L = a_R, right_a = (1 + b_L + b_R) - 1 - b_L = b_R.
        have hRl : (L.abs_count + R.abs_count) - L.abs_count = R.abs_count := by omega
        have hRa : (1 + L.app_count + R.app_count) - 1 - L.app_count = R.app_count := by omega
        simp only [hRl, hRa]
        exact List.mem_map_of_mem ihR'

def terms_fokker_lt_7: List (Term String) :=
      Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.gen_terms 0 0 0
   ++ Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.gen_terms 1 0 0
   ++ Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.gen_terms 0 1 0
   ++ Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.gen_terms 2 0 0
   ++ Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.gen_terms 1 1 0
   ++ Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.gen_terms 0 2 0
   ++ Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.gen_terms 3 0 0
   ++ Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.gen_terms 2 1 0
   ++ Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.gen_terms 1 2 0
   ++ Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.gen_terms 0 3 0
   ++ Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.gen_terms 4 0 0
   ++ Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.gen_terms 3 1 0
   ++ Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.gen_terms 2 2 0
   ++ Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.gen_terms 1 3 0
   ++ Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.gen_terms 0 4 0
   ++ Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.gen_terms 5 0 0
   ++ Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.gen_terms 4 1 0
   ++ Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.gen_terms 3 2 0
   ++ Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.gen_terms 2 3 0
   ++ Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.gen_terms 1 4 0
   ++ Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.gen_terms 0 5 0
   ++ Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.gen_terms 6 0 0
   ++ Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.gen_terms 5 1 0
   ++ Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.gen_terms 4 2 0
   ++ Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.gen_terms 3 3 0
   ++ Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.gen_terms 2 4 0
   ++ Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.gen_terms 1 5 0
   ++ Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.gen_terms 0 6 0

-- 表述可以改变
theorem gen_terms_spec: ∀ (M : Term String) (abs_count app_count: Nat),
  M.abs_count = abs_count ->
  M.app_count = app_count ->
  (M.fv = ∅ /\ M.LC) ↔ M ∈ gen_terms abs_count app_count 0 := by
sorry

theorem closed_lc_iff_mem_gen_terms (M: Term String): (M.LC /\ M.fv = ∅ /\ M.fokker_size < 7) ↔ M ∈ terms_fokker_lt_7 := by
sorry

end Term

end LambdaCalculus.LocallyNameless.Untyped

end Cslib
