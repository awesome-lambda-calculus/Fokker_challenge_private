import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullEta
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBetaEtaConfluence
import Mathlib.Data.Set.Card
import FokkerChallenge.Basic
import FokkerChallenge.EnhancedCslib.CountBvar

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

/-
Most things here need rewrite
-/

def H: Nat -> Term String
| 0 => Term.abs (Term.abs (Term.app (Term.bvar 1) (Term.app (Term.bvar 0) (Term.bvar 0))))
| Nat.succ n => Term.abs (Term.abs (Term.app (Term.bvar 0) (H n)))

def two_vars_are_not_enough: Term String → Bool
  | Term.bvar n => n < 2
  | Term.fvar _ => true
  | Term.abs (Term.abs t) => two_vars_are_not_enough t
  | Term.app t1 t2 => two_vars_are_not_enough t1 && two_vars_are_not_enough t2
  | _ => false

def rank: Term String -> Nat
  | Term.abs (Term.abs t) => 1 + rank t
  | Term.app t1 t2 => max (rank t1) (rank t2)
  | _ => 0

example: rank K = 1 := by repeat constructor
example: rank (Term.abs (Term.abs K)) = 2 := by repeat constructor
example: rank (Term.abs (Term.abs (Term.app K K))) = 2 := by repeat constructor
example: rank (Term.abs (Term.abs (Term.app (Term.bvar 1) K))) = 2 := by repeat constructor

def WrappedFvar (n: Nat): Term String -> Bool
  | Term.fvar _ => true
  | Term.bvar _ => false
  | Term.app (Term.abs t1) t2 => two_vars_are_not_enough (Term.abs t1) && rank (Term.abs t1) <= n && WrappedFvar n t2
  | Term.app (Term.fvar _) _ => false
  | Term.app (Term.bvar _) _ => false
  | Term.app (Term.app _ _) _ => false
  | Term.abs _ => false

inductive produce (P: Term String -> Bool): Term String -> Prop
  | base {t}: P t -> produce P t
  | app {t1 t2}:  P t1 -> P t2 -> produce P (Term.app t1 t2)

-- A(A(A x))
def atom_rec: Term String -> String -> Nat -> Bool
  | Term.fvar x, y, _ => x = y
  | Term.bvar _, _, _ => false
  | Term.abs _, _, _ => false
  | Term.app _ (Term.bvar _), _, _ => false
  | Term.app _ (Term.abs _), _, _ => false
  | Term.app t (Term.fvar x), y, n => two_vars_are_not_enough t && rank t < n && x = y && x ∉ t.fv
  | Term.app t1 (Term.app t2 t3), y, n => two_vars_are_not_enough t1 && rank t1 < n && atom_rec (Term.app t2 t3) y n

example: atom_rec (Term.fvar "x") "x" 1 = true := by repeat constructor
example: atom_rec (Term.app (Term.fvar "x") (Term.fvar "x")) "x" 1 = false := by repeat constructor
example: atom_rec (Term.app (Term.fvar "y") (Term.fvar "x")) "x" 1 = true := by repeat constructor

def only_01: Term String -> Bool
  | Term.bvar n => n < 2
  | Term.fvar _ => true
  | Term.abs t => only_01 t
  | Term.app t1 t2 => only_01 t1 && only_01 t2

theorem two_vars_are_not_enough_implies_only_01_inner {k} : (M: Term String) -> M.fokker_size < k -> two_vars_are_not_enough M → only_01 M := by
induction k with intros M
| succ n h => cases M with unfold two_vars_are_not_enough
  | fvar _ => unfold only_01
              grind
  | bvar _ => unfold only_01
              grind
  | abs M =>  split
              any_goals tauto
              rename_i heq
              rw [heq]
              unfold fokker_size
              unfold fokker_size
              intros _ _
              unfold only_01
              unfold only_01
              apply h <;> omega
  | app _ _ =>  unfold fokker_size
                unfold only_01
                simp
                grind
| zero => cases M with grind


theorem two_vars_are_not_enough_implies_only_01 {M} : two_vars_are_not_enough M → only_01 M :=
@two_vars_are_not_enough_implies_only_01_inner (M.fokker_size +1) M (by omega)

def strong_no_head_redex: Term String -> Bool
| bvar _ => true
| fvar _ => true
| app t _ => strong_no_head_redex t
| abs _ => false

inductive TripleBeta : Term String → Term String → Prop
| beta {M N0 N1} : LC M.abs.abs → LC N0 -> LC N1 → TripleBeta (app (app M.abs.abs N1) N0) (openRec 0 N0 (openRec 1 N1 M))


private theorem openRec_LC_congruence_inner {k:Nat}{N1 N2: Term String}: (M: Term String) -> M.fokker_size < k -> (i: Nat) -> N1.LC -> N2.LC -> (openRec i N1 M).LC -> (openRec i N2 M).LC := by
induction k with
| zero => intros M hm i _ _ h
          cases M with
          | bvar _ => unfold openRec
                      unfold openRec at h
                      split <;> split at h <;> tauto
          | fvar _ => tauto
          | abs _ =>  unfold fokker_size at hm
                      omega
          | app _ _ =>  unfold fokker_size at hm
                        omega
| succ n ih => intros M hm i _ _ h
               cases M with
  | bvar _ => unfold openRec
              unfold openRec at h
              split <;> split at h <;> tauto
  | fvar _ => tauto
  | app _ _  => unfold openRec
                unfold openRec at h
                cases h
                unfold fokker_size at hm
                constructor
                . apply ih _ (by omega) _ (by assumption) (by assumption) (by assumption)
                . apply ih _ (by omega) _ (by assumption) (by assumption) (by assumption)
  | abs M  => unfold openRec at h
              cases h
              unfold openRec
              constructor
              rename_i cs h
              intros x hx
              specialize h x hx
              unfold fokker_size at hm
              unfold open'
              rw [swap_open]
              apply ih
              rw [fokker_size_openrec]
              any_goals omega
              rw [swap_open]
              assumption
              any_goals omega
              all_goals constructor


theorem openRec_LC_congruence {M N1 N2: Term String}: (i: Nat) -> N1.LC -> N2.LC -> (openRec i N1 M).LC -> (openRec i N2 M).LC := @openRec_LC_congruence_inner (M.fokker_size + 1) N1 N2 M (by omega)

theorem tripleBeta_is_special_beta {M N}: TripleBeta M N -> Relation.ReflTransGen FullBeta M N := by
intro h
cases h
rename_i M N0 N1 h h1 h2
cases h
rename_i xs h
apply Relation.ReflTransGen.tail
. apply Relation.ReflTransGen.tail
  . apply Relation.ReflTransGen.refl
  . apply Xi.appR
    . assumption
    . apply Xi.base
      constructor
      any_goals assumption
      constructor
      assumption
. apply Xi.base
  unfold open'
  conv =>
    left
    unfold openRec
  simp
  constructor
  . constructor
    . intros x g
      specialize h x g
      unfold open' at h
      unfold openRec at h
      simp at h
      cases h
      rename_i ys h
      have h4 : ∃ x: String, x ∉ ys := by apply Finset.exists_not_mem_of_card_lt_enatCard; simp
      obtain ⟨y, hy⟩ := h4
      specialize h y hy
      unfold open' at *
      have g:= @openRec_LC_congruence (M⟦1 ↝ fvar x⟧) (fvar y) (fvar x) 0 (by constructor) (by constructor) h
      rw [swap_open] at g
      rw [swap_open]
      apply openRec_LC_congruence
      pick_goal 3
      exact g
      any_goals omega
      all_goals constructor
  . assumption

theorem xi_tripleBeta_is_special_beta {M N}: Xi TripleBeta M N -> Relation.ReflTransGen FullBeta M N := by
intros h
induction h with
| base _ => apply tripleBeta_is_special_beta
            tauto
| appL _ _ _ => apply Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullBeta.redex_app_r_cong <;> assumption
| appR _ _ _ => apply Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullBeta.redex_app_l_cong <;> assumption
| abs xs h1 h2 => rename_i M N
                  apply Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullBeta.redex_abs_cong
                  assumption

private theorem openrec_preserve_two_vars_are_not_enough_inner {k N} (h: N.two_vars_are_not_enough) :
(M: Term String) ->
M.fokker_size < k ->
(i: Nat) ->
M.two_vars_are_not_enough ->
(openRec i N M).two_vars_are_not_enough := by
induction k with
| zero => intros M hm i _
          cases M with
  | bvar _ => grind
  | fvar _ => grind
  | abs _ =>  unfold fokker_size at hm
              omega
  | app _ _ =>  unfold fokker_size at hm
                omega
| succ n ih =>  intros M hm i _
                cases M with
  | bvar _ => grind
  | fvar _ => grind
  | app _ _ =>  rename_i h1
                unfold openRec two_vars_are_not_enough
                unfold fokker_size at hm
                unfold two_vars_are_not_enough at h1
                simp at h1
                simp
                constructor
                . apply ih
                  omega
                  tauto
                . apply ih
                  omega
                  tauto
  | abs M =>  rename_i h1
              unfold two_vars_are_not_enough at h1
              split at h1
              any_goals tauto
              rename_i Z heq
              rw [heq]
              rw [heq] at hm
              unfold fokker_size at hm
              unfold fokker_size at hm
              unfold openRec openRec two_vars_are_not_enough
              apply ih
              omega
              assumption

theorem openrec_preserve_two_vars_are_not_enough {M N}
(h: N.two_vars_are_not_enough) :
(i: Nat) ->
M.two_vars_are_not_enough ->
(openRec i N M).two_vars_are_not_enough :=
@openrec_preserve_two_vars_are_not_enough_inner (M.fokker_size +1) N h M (by omega)

theorem triplebeta_preserve_two_vars_are_not_enough {M N} : TripleBeta M N -> two_vars_are_not_enough M ->
two_vars_are_not_enough N := by
intros h _
cases h
rename_i M N0 N1 _ _ _ h
unfold two_vars_are_not_enough at h
simp at h
obtain ⟨h, _⟩ := h
unfold two_vars_are_not_enough at h
simp at h
obtain ⟨h, _⟩ := h
unfold two_vars_are_not_enough at h
apply openrec_preserve_two_vars_are_not_enough
assumption
apply openrec_preserve_two_vars_are_not_enough <;> assumption


/-
theorem bar {x y M Y n}: atom_rec M x (Nat.succ n) -> Relation.ReflTransGen (Xi TripleBeta) ((M.app (fvar x)).app (fvar y)) ((fvar x).app Y) -> two_vars_are_not_enough Y := by
sorry
-/

theorem count_bvar_zero_of_high_index_inner {k}: (M: Term String) -> M.fokker_size < k -> (i: Nat) -> i > 1 -> two_vars_are_not_enough M -> count_bvar i M = 0 := by
induction k with
| zero => grind
| succ n ih =>  intros M h i _ hm
                unfold two_vars_are_not_enough at hm
                split at hm
                any_goals tauto
                all_goals unfold count_bvar
                . split <;> grind
                . unfold count_bvar
                  apply ih
                  unfold fokker_size at h
                  unfold fokker_size at h
                  omega
                  omega
                  assumption
                . simp at hm
                  unfold fokker_size at h
                  grind


theorem count_bvar_zero_of_high_index {i M}: i> 1 -> two_vars_are_not_enough M -> count_bvar i M = 0 := @count_bvar_zero_of_high_index_inner (M.fokker_size +1) M (by omega) i

private theorem openrec_preserve_only_01_inner {k N} (hn: only_01 N) : (M: Term String) -> M.fokker_size < k -> two_vars_are_not_enough M -> only_01 (openRec 1 N M) := by
induction k with
| zero => grind
| succ n _ => intros M h1 h
              unfold two_vars_are_not_enough at h
              split at h
              any_goals grind
              any_goals tauto
              . unfold openRec
                split <;> tauto
              . unfold openRec
                unfold openRec
                unfold only_01
                unfold only_01
                rw [openRec_noop_of_count_bvar_zero]
                apply two_vars_are_not_enough_implies_only_01; assumption
                apply count_bvar_zero_of_high_index <;> omega
              . unfold openRec
                unfold only_01
                unfold fokker_size at h1
                simp
                grind

theorem openrec_preserve_only_01 {M N} (hn: only_01 N) : two_vars_are_not_enough M -> only_01 (openRec 1 N M) := @openrec_preserve_only_01_inner (M.fokker_size + 1) N hn M (by omega)

def diverge (t : Term String) : Prop :=
  ∀ (t': Term String), Relation.ReflTransGen FullBeta t t' -> has_beta_redex t'

def has_normal_form (t : Term String) : Prop :=
  ∃ (t': Term String), Relation.ReflTransGen FullBeta t t' /\ has_beta_redex t' = false

theorem foo1 {t} : diverge t \/ has_normal_form t := by
-- Use the law of excluded middle on the existence of a normal form
  cases Classical.em (has_normal_form t) with
  | inr h_not_nf =>
    -- If it does NOT have a normal form, we must show it diverges
    apply Or.inl
    intro t' h_red
    -- We know there is no t'' such that t reduces to it and it's a normal form
    -- Since t' is one such reduction, it must not be a normal form
    by_contra h_is_nf
    have : has_normal_form t := ⟨t', h_red, by simp_all⟩
    contradiction
  | inl h_nf =>
    -- If it has a normal form, the proof is trivial
    exact Or.inr h_nf

def no_triple_redex: Term String -> Bool
  | Term.bvar _ => true
  | Term.fvar _ => true
  | Term.app (Term.app (.abs (.abs _)) _) _=> false
  | Term.app t1 t2 => no_triple_redex t1 && no_triple_redex t2
  | Term.abs t => no_triple_redex t

mutual
  -- x () () ()
  def start_with_bvar: Term String -> Bool
  | Term.bvar n => n < 2
  | Term.fvar _ => true
  | Term.abs _ => false
  | Term.app t1 t2 => start_with_bvar t1 && (start_with_bvar t2 || euphoric t2)

  def euphoric: Term String -> Bool
  | bvar n => n < 2
  | fvar _ => true
  | abs (abs t) => start_with_bvar t || euphoric t
  | abs (app _ _) => false
  | abs (fvar _) => false
  | abs (bvar _) => false
  | app (abs (abs t1)) t2 => two_vars_are_not_enough t1 && only_01 t2
  | app (app _ _) _ => false
  | app (fvar _) _ => false
  | app (bvar _) _ => false
  | app (abs (app _ _)) _ => false
  | app (abs (fvar _)) _ => false
  | app (abs (bvar _)) _ => false
end

theorem app_no_triple_redex_two_vars_are_not_enough_left_case {n} {t1 : Term String}
(ih: ∀ (M : Term String),
  M.fokker_size < n →
    M.no_triple_redex = true → M.two_vars_are_not_enough = true → M.start_with_bvar = true ∨ M.euphoric = true)
(h1 : t1.no_triple_redex = true)
(h2 : t1.two_vars_are_not_enough = true)
(h3: ∀ (a b : Term String), t1 = a.abs.abs.app b → False):
∀ (t2 : Term String),
  1 + t1.fokker_size + t2.fokker_size < n + 1 →
    t2.no_triple_redex = true →
      t2.two_vars_are_not_enough = true → (t1.app t2).start_with_bvar = true ∨ ∃ a: Term String, t1 = a.abs.abs := by
induction t1 with intros t2 h5 h6 h7
| bvar _ => left
            unfold start_with_bvar
            simp
            constructor
            . unfold start_with_bvar
              unfold two_vars_are_not_enough at h2
              omega
            . apply ih <;> omega
| fvar _ => left
            unfold start_with_bvar
            simp
            constructor
            . tauto
            . apply ih <;> omega
| abs _ _ =>  unfold two_vars_are_not_enough at h2
              split at h2 <;> tauto
| app M1 M2 hm1 hm2 =>  left
                        unfold start_with_bvar
                        simp
                        constructor
                        . unfold no_triple_redex at h1
                          split at h1
                          any_goals tauto
                          simp at h1
                          rename_i t1 t2 _ heq
                          simp at heq
                          obtain ⟨_, _⟩ := heq
                          subst M1 M2
                          unfold two_vars_are_not_enough at h2
                          simp at h2
                          conv at h5 =>
                            left
                            left
                            unfold fokker_size
                          specialize hm1 (by tauto) (by tauto) (by assumption) t2 (by omega) (by tauto) (by tauto)
                          cases hm1 <;> tauto
                        . apply ih <;> omega

private theorem no_triple_redex_two_vars_are_not_enough_implies_happy_inner {k} :
  (M : Term String) ->
  M.fokker_size < k ->
  no_triple_redex M ->
  two_vars_are_not_enough M ->
  start_with_bvar M \/ euphoric M := by
induction k with
| zero => grind
| succ n ih =>  intros M _ h1 h2
                unfold no_triple_redex at h1
                split at h1
                any_goals tauto
                all_goals rename_i h3
                . rename_i t1 t2 _
                  unfold fokker_size at h3
                  unfold two_vars_are_not_enough at h2
                  simp at h2
                  simp at h1
                  obtain ⟨h1, _⟩ := h1
                  obtain ⟨h2, _⟩ := h2
                  have h := @app_no_triple_redex_two_vars_are_not_enough_left_case n t1 (by assumption) (by assumption) (by assumption) (by assumption) t2 (by omega) (by assumption) (by assumption)
                  cases h
                  any_goals tauto
                  right
                  rename_i h
                  obtain ⟨t, _⟩ := h
                  subst t1
                  unfold euphoric
                  simp
                  constructor
                  any_goals tauto
                  apply two_vars_are_not_enough_implies_only_01
                  any_goals tauto
                . unfold two_vars_are_not_enough at h2
                  split at h2
                  any_goals tauto
                  right
                  rename_i heq
                  rw [heq]
                  rw [heq] at h3
                  simp at heq
                  rw [heq] at h1
                  unfold no_triple_redex at h1
                  unfold euphoric
                  simp
                  unfold fokker_size at h3
                  unfold fokker_size at h3
                  apply ih <;> omega

/-
-- TODO: is thie definition right ?
theorem foo_inner {k}: (M: Term String) -> M.fokker_size < k -> no_triple_redex M -> start_with_bvar M \/ euphoric M -> ∃ N, Relation.ReflTransGen (Xi Beta) M N /\ no_redex N /\ (start_with_bvar N \/ euphoric N) := by
induction k with
| zero => grind
| succ n ih =>  intros M h1 h2 h
                cases h <;> rename_i h
                unfold start_with_bvar at h
                split at h
                any_goals tauto
                all_goals sorry


theorem foo {M}: no_triple_redex M -> start_with_bvar M \/ euphoric M -> ∃ N, Relation.ReflTransGen (Xi Beta) M N /\ no_redex N /\ (start_with_bvar N \/ euphoric N) := by
sorry
-/

theorem beta_preserve_happy_1 {M N}: Beta M N -> start_with_bvar M -> start_with_bvar N \/ euphoric N := by
intros h _
cases h
rename_i h
unfold start_with_bvar at h
simp at h
obtain ⟨h, _⟩ := h
unfold start_with_bvar at h
tauto

/-
theorem beta_preserve_happy_2 {M N}: Beta M N -> euphoric M -> start_with_bvar N \/ euphoric N := by
intros h _
cases h
rename_i h
unfold euphoric at h
split at h
any_goals tauto
rename_i heq
simp at heq
obtain ⟨_, _⟩ := heq
rename_i M N _ _ t1 t2 t3 g _
subst M t3
simp at h
unfold open' openRec
simp
right
-- impossible
sorry
-/


/-
def happy: Term String -> Bool
  | (abs (app _ _)) => false
  | (abs (bvar _)) => false
  | (abs (fvar _)) => false
  | app (Term.abs (Term.abs t1)) t2 => two_vars_are_not_enough t1 && only_01 t2
  | app (Term.bvar n) t2 => n < 2 && happy t2
  | app (Term.fvar _) t2 => happy t2
  | app (Term.app t1 t2) t3 => happy (Term.app t1 t2) && happy t3
  | app (abs (app _ _)) _ => false
  | app (abs (bvar _)) _ => false
  | app (abs (fvar _)) _ => false


theorem unexpected: happy (app (app (abs (abs (bvar 0))) (abs (abs (bvar 0)))) (abs (abs (bvar 0)))) := by
repeat constructor


theorem happy_only_01_inner {k}: (M: Term String) -> M.fokker_size < k -> happy M -> only_01 M := by
induction k with
| zero => grind
| succ n ih =>  intros M _ h
                unfold happy at h
                split at h
                all_goals unfold only_01
                any_goals grind
                . unfold only_01
                  apply ih
                  any_goals assumption
                  rename_i g
                  unfold fokker_size at g
                  unfold fokker_size at g
                  omega
                . simp_all
                  rename_i g
                  unfold fokker_size at g
                  conv at g=>
                    left
                    left
                    unfold fokker_size
                    unfold fokker_size
                  constructor
                  any_goals grind
                  unfold only_01
                  unfold only_01
                  apply two_vars_are_not_enough_implies_only_01
                  tauto
                . simp
                  simp at h
                  constructor
                  . unfold only_01
                    grind
                  . apply ih
                    any_goals tauto
                    rename_i g
                    unfold fokker_size at g
                    omega
                . simp
                  constructor
                  . unfold only_01
                    grind
                  . apply ih
                    any_goals tauto
                    rename_i g
                    unfold fokker_size at g
                    omega
                . simp
                  rename_i g
                  unfold fokker_size at g
                  simp at h
                  constructor
                  . apply ih
                    omega
                    grind
                  . apply ih
                    any_goals tauto
                    omega


theorem happy_only_01 {M}: happy M -> only_01 M := @happy_only_01_inner (M.fokker_size+1) M (by omega)

private theorem no_triple_redex_two_vars_are_not_enough_implies_happy_inner {k} :
  (M : Term String) ->
  M.fokker_size < k ->
  no_triple_redex M ->
  two_vars_are_not_enough M ->
  happy M := by
induction k with
| zero => grind
| succ n ih =>  intros M _ h1 h2
                unfold no_triple_redex at h1
                split at h1
                any_goals tauto
                . unfold happy
                  split
                  any_goals tauto
                  . rename_i t1 M _ h _ a N heq
                    simp at heq
                    obtain ⟨_, _⟩ := heq
                    subst t1 N
                    unfold fokker_size at h
                    unfold two_vars_are_not_enough at h2
                    simp
                    simp at h2
                    obtain ⟨h2, _⟩ := h2
                    unfold two_vars_are_not_enough at h2
                    constructor
                    . grind
                    . apply ih <;> grind
                  . rename_i t1 M _ h _ a N heq
                    simp at heq
                    obtain ⟨_, _⟩ := heq
                    subst t1 N
                    unfold fokker_size at h
                    unfold two_vars_are_not_enough at h2
                    simp at h2
                    obtain ⟨h2, _⟩ := h2
                    unfold two_vars_are_not_enough at h2
                    simp
                    constructor
                    simp at h2
                    omega
                    apply ih <;> grind
                  . rename_i t1 M _ h _ a N heq
                    simp at heq
                    obtain ⟨_, _⟩ := heq
                    subst t1 N
                    unfold fokker_size at h
                    unfold two_vars_are_not_enough at h2
                    apply ih <;> grind
                  . rename_i t5 t4 _ _ h _ t1 t2 t3 heq
                    simp at heq
                    obtain ⟨_, _⟩ := heq
                    subst t4 t3
                    simp
                    unfold fokker_size at h
                    simp at h1
                    unfold two_vars_are_not_enough at h2
                    grind
                  . unfold two_vars_are_not_enough at h2
                    simp at h1
                    rename_i heq
                    simp at heq
                    obtain ⟨heq, _⟩ := heq
                    rw [heq] at h2
                    simp at h2
                    unfold two_vars_are_not_enough at h2
                    tauto
                  . unfold two_vars_are_not_enough at h2
                    simp at h1
                    rename_i heq
                    simp at heq
                    obtain ⟨heq, _⟩ := heq
                    rw [heq] at h2
                    simp at h2
                    unfold two_vars_are_not_enough at h2
                    tauto
                  . unfold two_vars_are_not_enough at h2
                    simp at h1
                    rename_i heq
                    simp at heq
                    obtain ⟨heq, _⟩ := heq
                    rw [heq] at h2
                    simp at h2
                    unfold two_vars_are_not_enough at h2
                    tauto
                . unfold two_vars_are_not_enough at h2
                  split at h2
                  any_goals tauto
                  rename_i M h _ N heq
                  rw [heq]
                  rw [heq] at h
                  simp at heq
                  rw [heq] at h1
                  unfold no_triple_redex at h1
                  unfold fokker_size at h
                  unfold fokker_size at h
                  unfold happy
                  apply ih <;> omega


theorem no_triple_redex_two_vars_are_not_enough_implies_happy {M} :
  no_triple_redex M ->
  two_vars_are_not_enough M ->
  happy M := @no_triple_redex_two_vars_are_not_enough_implies_happy_inner (M.fokker_size + 1) M (by omega)


theorem beta_preserve_happy {M N}: Beta M N -> happy M -> only_01 N := by
intros h hm
cases h
unfold happy at hm
split at hm
any_goals tauto
all_goals rename_i heq
all_goals simp at heq
obtain ⟨_, _⟩ := heq
rename_i M N _ _ _ t1 t2 _ _
subst M N
simp at hm
obtain ⟨_, _⟩ := hm
unfold open' openRec
simp
unfold only_01
apply openrec_preserve_only_01
any_goals assumption
apply happy_only_01
assumption

theorem xi_beta_preserve_happy {M N}: Xi Beta M N -> happy M -> only_01 N := by
intros h hm
induction h with
| base _ => apply beta_preserve_happy <;> assumption
| appL h1 h2 ih =>  unfold happy at hm
                    split at hm
                    any_goals tauto
                    all_goals rename_i heq
                    all_goals simp at heq
                    all_goals obtain ⟨_, _⟩ := heq
                    any_goals simp at hm
                    any_goals subst Z
                    sorry
| appR _ _ ih => sorry
| abs xs _ _ => sorry
-/


/-
inductive XiXi (R : Term String → Term String → Prop) : Term String → Term String → Prop
| base : R M N → XiXi R M N
| appL: LC Z → XiXi R M N → XiXi R (app Z M) (app Z N)
| appR : LC Z → XiXi R M N → XiXi R (app M Z) (app N Z)
| abs (xs : Finset String) : (∀ y ∉ xs, ∀ x ∉ xs, x ≠ y -> XiXi R (openRec 1 (fvar y) (M ^ fvar x)) (openRec 1 (fvar y) (N ^ fvar x))) → XiXi R M.abs.abs N.abs.abs

theorem xixi_tripleBeta_is_special_beta {M N}: XiXi TripleBeta M N -> Relation.ReflTransGen FullBeta M N := by
intros h
induction h with
| base _ => apply tripleBeta_is_special_beta
            assumption
| appL _ _ h => apply xi_app_l <;> assumption
| appR _ _ h => apply xi_app_r <;> assumption
| abs xs h ih =>  rename_i M N
                  apply Relation.ReflTransGen.tail
                  apply Relation.ReflTransGen.refl
                  apply Xi.abs
                  -- have h4 : ∃ x: String, x ∉ xs := by apply Finset.exists_not_mem_of_card_lt_enatCard; simp
                  -- obtain ⟨y, hy⟩ := h4
                  -- specialize ih y hy
                  intros z hz
                  unfold open' openRec
                  simp
                  apply Xi.abs
                  intros a ha
                  unfold open'
                  unfold open' at ih
                  rw [swap_open 0 1]
                  rw [swap_open 0 1]
                  -- apply ih
                  all_goals sorry
-/
