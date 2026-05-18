import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullEta
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBetaEtaConfluence
import Mathlib.Data.Set.Card
import FokkerChallenge.Basic
import FokkerChallenge.EnhancedCslib.CountBvar
import FokkerChallenge.EnhancedCslib.Fmt

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term


-- 2. Encoder (Modified to return Option (List Bool))
def encodeVar : Nat → List Bool
  | 0 => [true, false]
  | n + 1 => true :: encodeVar n

def encode: Term String → Option (List Bool)
  | Term.bvar i => some (encodeVar i)
  | Term.fvar _ => none -- Return None immediately when an fvar is met
  | Term.abs t =>
    match encode t with
    | some bs => some (false :: false :: bs)
    | none => none
  | Term.app t₁ t₂ =>
    match encode t₁, encode t₂ with
    | some bs₁, some bs₂ => some (false :: true :: bs₁ ++ bs₂)
    | _, _ => none

-- 3. Decoder
def decodeVar : List Bool → Option (Nat × List Bool)
  | true :: false :: rest => some (0, rest)
  | true :: true :: rest =>
    match decodeVar (true :: rest) with
    | some (n, rest') => some (n + 1, rest')
    | none => none
  | _ => none

def decodeFuel : Nat → List Bool → Option (Term String × List Bool)
  | 0,  _ => none
  | f + 1, false :: false :: bs =>
    match decodeFuel f bs with
    | some (t, rest) => some (Term.abs t, rest)
    | none => none
  | f + 1, false :: true :: bs =>
    match decodeFuel f bs with
    | some (t₁, rest₁) =>
      match decodeFuel f rest₁ with
      | some (t₂, rest₂) => some (Term.app t₁ t₂, rest₂)
      | none => none
    | none => none
  | _ + 1, true :: bs =>
    match decodeVar (true :: bs) with
    | some (n, rest) => some (Term.bvar n, rest)
    | none => none
  | _, __=> none

def decode (bs : List Bool) : Option (Term String × List Bool) :=
  decodeFuel bs.length bs

-- 4. Auxiliary Core Properties

theorem decodeVar_correct (n : Nat) (rest : List Bool) :
    decodeVar (encodeVar n ++ rest) = some (n, rest) := by
  induction n with
  | zero => rfl
  | succ m ih =>
    cases m with
    | zero => rfl
    | succ k =>
      dsimp [encodeVar, decodeVar]
      have h : decodeVar (true :: encodeVar k ++ rest) = some (k + 1, rest) := ih
      simp at h
      rw [h]

theorem decodeFuel_encodeVar (f n : Nat) (rest : List Bool) :
    decodeFuel (f + 1) (encodeVar n ++ rest) = some (Term.bvar n, rest) := by
  cases n with
  | zero => dsimp [encodeVar, decodeFuel, decodeVar]
  | succ m =>
    cases m with
    | zero => dsimp [encodeVar, decodeFuel, decodeVar]
    | succ k =>
      unfold decodeFuel
      have h : decodeVar (encodeVar (k + 2) ++ rest) = some (k + 2, rest) :=
        decodeVar_correct (k + 2) rest
      simp [Nat.add_assoc]
      set x := encodeVar (k + 2) ++ rest
      split
      any_goals tauto
      all_goals split
      any_goals split
      any_goals grind
      . rename_i heq _ _ _ _
        rw [heq] at h
        dsimp [decodeVar] at h
        cases h
      . rename_i heq _ _
        rw [heq] at h
        dsimp [decodeVar] at h
        cases h
      . rename_i heq _ _ _ _ _ _ _ _
        rw [heq] at h
        dsimp [decodeVar] at h
        cases h
      . rename_i heq _ _ _ _ _ _
        rw [heq] at h
        dsimp [decodeVar] at h
        cases h
      . rename_i heq _ _
        rw [heq] at h
        dsimp [decodeVar] at h
        cases h

theorem termNodes_lt_encode_length  (t : Term String) (bs : List Bool)
    (henc : encode t = some bs) : fokker_size t < bs.length := by
  induction t generalizing bs with
  | bvar n =>
    simp [encode] at henc; subst bs
    have h : (encodeVar n).length = n + 2 := by
      induction n with | zero => rfl | succ m ih => dsimp [encodeVar]; omega
    dsimp [fokker_size]; omega
  | fvar x => simp [encode] at henc
  | abs body ih =>
    dsimp [encode] at henc
    cases h_enc : encode body with
    | none => simp [h_enc] at henc
    | some bs' =>
      simp [h_enc] at henc; subst bs
      dsimp [fokker_size]
      have ih' := ih  bs' h_enc
      omega
  | app t₁ t₂ ih₁ ih₂ =>
    dsimp [encode] at henc
    cases h1 : encode t₁ with
    | none => simp [h1] at henc
    | some bs₁ =>
      cases h2 : encode t₂ with
      | none => simp [h2] at henc
      | some bs₂ =>
        simp [h1, h2] at henc; subst bs
        dsimp [fokker_size]
        have ih1' := ih₁ bs₁ h1
        have ih2' := ih₂ bs₂ h2
        simp
        omega

-- 5. Correctness Proof: `decode (encode t) = t`

theorem decodeFuel_encode (t : Term String) (fuel : Nat) (bs rest : List Bool)
    (henc : encode t = some bs) (hnodes : fokker_size t < fuel) :
    decodeFuel fuel (bs ++ rest) = some (t, rest) := by
  induction t generalizing fuel bs rest with
  | bvar n =>
    cases fuel with | zero => contradiction | succ f =>
    simp [encode] at henc; subst bs
    rw [decodeFuel_encodeVar]
  | fvar x => simp [encode] at henc
  | abs body ih =>
    cases fuel with | zero => contradiction | succ f =>
    dsimp [encode] at henc
    cases h_enc : encode  body with
    | none => simp [h_enc] at henc
    | some bs' =>
      simp [h_enc] at henc; subst bs
      dsimp [decodeFuel]
      have hf : fokker_size body < f := by simp [fokker_size] at hnodes; omega
      have h1 := ih f bs' rest h_enc hf
      rw [h1]
  | app t₁ t₂ ih₁ ih₂ =>
    cases fuel with | zero => contradiction | succ f =>
    dsimp [encode] at henc
    cases h1 : encode t₁ with
    | none => simp [h1] at henc
    | some bs₁ =>
      cases h2 : encode t₂ with
      | none => simp [h2] at henc
      | some bs₂ =>
        simp [h1, h2] at henc; subst bs
        dsimp [decodeFuel]
        rw [List.append_assoc]
        have hf₁ : fokker_size t₁ < f := by simp [fokker_size] at hnodes; omega
        have h1' := ih₁ f bs₁ (bs₂ ++ rest) h1 hf₁
        rw [h1']
        have hf₂ : fokker_size t₂ < f := by simp [fokker_size] at hnodes; omega
        have h2' := ih₂ f bs₂ rest h2 hf₂
        simp
        rw [h2']

theorem decode_correct (t : Term String) (bs):
    encode t = some bs -> decode bs = some (t, []) := by
  intro hbs
  unfold decode
  have hlen := termNodes_lt_encode_length t bs hbs
  have h := decodeFuel_encode t bs.length bs [] hbs hlen
  simp at h
  exact h

theorem encode_wf_succeeds (t : Term String) (ht : t.fv = ∅): ∃ bs, encode t = some bs := by
induction t with
| bvar _ => tauto
| fvar _ => simp [fv] at ht
| abs _ _ => grind [fv, encode]
| app _ _ ih1 ih2 =>  unfold fv at ht
                      simp at ht
                      obtain ⟨h1, h2⟩ := ht
                      obtain ⟨_, h1⟩ := ih1 h1
                      obtain ⟨_, h2⟩ := ih2 h2
                      unfold encode
                      simp [h1, h2]

-- 6. Inverse Correctness Proof: `encode (decode bs) = bs`

theorem decodeVar_sound : ∀ (bs : List Bool) (n : Nat) (rest : List Bool),
    decodeVar bs = some (n, rest) → encodeVar n ++ rest = bs
  | true :: false :: bs', 0, rest, h => by  simp [decodeVar] at h
                                            subst_vars
                                            rfl
  | true :: true :: bs', m + 1, rest, h => by
    simp [decodeVar] at h
    cases h_dec : decodeVar (true :: bs') with
    | none => simp [h_dec] at h
    | some pair =>
      cases pair with | mk m' r' =>
      simp [h_dec] at h; have ⟨h1, h2⟩ := h; subst_vars
      have ih := decodeVar_sound (true :: bs') _ _ h_dec
      dsimp [encodeVar]; rw [ih]
  | [], _, _, h => by contradiction
  | [true], _, _, h => by contradiction
  | false :: _, _, _, h => by contradiction
  | true :: false :: _, m + 1, _, h => by simp [decodeVar] at h
  | true :: true :: _, 0, _, h => by
    simp [decodeVar] at h
    rename_i tail _
    split at h <;> cases h
termination_by bs n rest _ => bs.length

theorem decodeFuel_sound : ∀ fuel bs t rest,
    decodeFuel fuel bs = some (t, rest) →
    ∃ t_bs, encode t = some t_bs ∧ t_bs ++ rest = bs
  | 0, _, _,  _, h => by contradiction
  | f + 1, false :: false :: bs, t, rest, h => by
    simp [decodeFuel] at h
    cases h_dec : decodeFuel f bs with
    | none => simp [h_dec] at h
    | some pair =>
      cases pair with | mk t' rest' =>
      simp [h_dec] at h; have ⟨h1, h2⟩ := h; subst_vars
      have ⟨t_bs, henc, h_append⟩ := decodeFuel_sound f bs t' _ h_dec
      use (false :: false :: t_bs)
      refine ⟨by dsimp [encode]; rw [henc], by dsimp; rw [h_append]⟩
  | f + 1, false :: true :: bs, t, rest, h => by
    simp [decodeFuel] at h
    cases h1 : decodeFuel f bs with
    | none => simp [h1] at h
    | some pair1 =>
      cases pair1 with | mk t1 rest1 =>
      simp [h1] at h
      cases h2 : decodeFuel f rest1 with
      | none => simp [h2] at h
      | some pair2 =>
        cases pair2 with | mk t2 rest2 =>
        simp [h2] at h; have ⟨hx, hy⟩ := h; subst_vars
        have ⟨t_bs1, henc1, h_app1⟩ := decodeFuel_sound f bs t1 rest1 h1
        have ⟨t_bs2, henc2, h_app2⟩ := decodeFuel_sound f rest1 t2 _ h2
        use (false :: true :: t_bs1 ++ t_bs2)
        have henc_app : encode (Term.app t1 t2) = some (false :: true :: t_bs1 ++ t_bs2) := by
          dsimp [encode]; rw [henc1, henc2]
        refine ⟨henc_app, ?_⟩
        subst bs
        subst rest1
        simp
  | f + 1, true :: bs, t, rest, h => by
    simp [decodeFuel] at h
    cases h_dec : decodeVar (true :: bs) with
    | none => simp [h_dec] at h
    | some pair =>
      cases pair with | mk n r =>
      simp [h_dec] at h
      obtain ⟨_, _⟩ := h
      subst_vars
      unfold encode
      use (encodeVar n)
      have h_sound := decodeVar_sound _ _ _ h_dec
      tauto
  | f + 1, [], _, _, h => by contradiction
  | f + 1, [false], _, _, h => by contradiction

theorem encode_decode (bs : List Bool) (t : Term String) (rest : List Bool) :
    decode bs = some (t, rest) →
    ∃ t_bs, encode t = some t_bs ∧ t_bs ++ rest = bs := by
  intro h
  unfold decode at h
  exact decodeFuel_sound bs.length bs t rest h
