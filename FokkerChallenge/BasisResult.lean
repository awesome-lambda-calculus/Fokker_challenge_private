import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Congruence
import FokkerChallenge.Basic
import FokkerChallenge.EnhancedCslib.Basic
import FokkerChallenge.EnhancedCslib.NormalForm

/-!
# A Basis Result in Combinatory Logic

This file is a (partial) formalization of:

> Remi Legrand, *A basis result in combinatory logic*,
> The Journal of Symbolic Logic, vol. 53 (1988), no. 4, pp. 1224–1226.

The paper proves that any basis for combinatory logic must contain at least one
combinator with rank strictly greater than two. Translated to the single-term
lambda-calculus setting used by this project: a closed lambda term whose body
uses at most two bound variables in a "rank-≤-2 fashion" cannot be a basis,
because there is no way to build a term that reduces to `C A B` (the `C`
combinator behaviour) from such a `Y` alone.

The proof outline of the paper:

* Suppose `Y` is a basis with rank ≤ 2.
  Then there exists a pure combination `X` of `Y` with `X A B C ↠ C A B`.
* **Lemma 1.** Head-reduction of `X A B` must stop at a term `T (E₁[A,B])`
  where `T` is a rank-2 combinator (so `X A B C ↠ T(E₁[A,B]) C`).
* Define a *π-expression* as a term in which every occurrence of `A` and `B`
  appears inside a subterm `E₁[A,B]` that contains no `C`, and which contains
  at least one `C`.
* **Lemma 2.** A π-expression that reduces to `C A B` admits a leftmost-step
  reduction to another π-expression that still reduces to `C A B`.
* By the (quasi-)normalization theorem this strategy must reach a normal form,
  but `C A B` is not a π-expression — contradiction.

Because the (quasi-)normalization theorem and standardization theorem are not
yet available in cslib (see issue #25), several of the central proofs are
left as `sorry` for now. The structure of the argument and the statements
of all the auxiliary lemmas are recorded so that they can be filled in
incrementally.
-/

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

/-! ## Rank of a closed lambda term

Following the paper, a combinator `Q x₁ … xₙ → C` has *rank* `n` whenever its
reduction rule binds `n` arguments and the body `C` is a *pure combination*
of those arguments (no further abstractions, no other free variables).

In the locally-nameless presentation a closed lambda term of rank `n` is
exactly an `n`-fold abstraction whose body has no further `abs`s and whose
bound variables are all in the range `0..n-1`.
-/

/-- Number of leading abstractions of a term. For a combinator `λx₁…xₙ. body`
this equals `n`. -/
def head_abs_count : Term String → Nat
  | abs t => 1 + head_abs_count t
  | _ => 0

/-- Whether a term contains no `abs`. The body of a combinator must satisfy
this (it is a pure combination of variables). -/
def has_no_abs : Term String → Bool
  | bvar _ => true
  | fvar _ => true
  | abs _ => false
  | app t1 t2 => has_no_abs t1 && has_no_abs t2

/-- A term is in the *combinator form of rank `n`* when it consists of `n`
leading abstractions followed by a body without any abstractions. -/
def is_combinator_form (n : Nat) : Term String → Prop
  | abs t => n > 0 ∧ is_combinator_form (n - 1) t
  | t => n = 0 ∧ has_no_abs t = true

/-- The paper's *rank* of a combinator. We define it as `head_abs_count`,
which is the correct value when `M` is in `is_combinator_form n` for
some `n`; for arbitrary terms it is simply the number of leading
abstractions and does **not** validate the combinator-form requirement
on the body. Pair this with `is_combinator_form` when the body
condition matters. -/
def comb_rank (M : Term String) : Nat := head_abs_count M

example : comb_rank K = 2 := by
  unfold comb_rank K head_abs_count head_abs_count head_abs_count
  rfl

example : comb_rank S = 3 := by
  unfold comb_rank S head_abs_count head_abs_count head_abs_count head_abs_count
  rfl

/-! ## Pure combinations

A *pure combination* of a term `Y` is built from `Y` and free variables by
applications. We reuse `Gen` from `Basic.lean` and extend it to allow
free variables as well — this matches the paper's notion of "a pure
combination of the basis combinators applied to variables `A`, `B`, `C`". -/

/-- Pure combinations: built from `Y`, free variables, and applications. -/
inductive PureComb (Y : Term String) : Term String → Prop
  | base : PureComb Y Y
  | fvar (x : String) : PureComb Y (fvar x)
  | app {M N} : PureComb Y M → PureComb Y N → PureComb Y (app M N)

/-- Every `Gen Y M` is a `PureComb Y M`. -/
theorem PureComb.of_Gen {Y M : Term String} : Gen Y M → PureComb Y M := by
  intro h
  induction h with
  | base => exact PureComb.base
  | app _ _ ih1 ih2 => exact PureComb.app ih1 ih2

/-! ## What it means for `Y` to be a (single-term) basis

We say that a closed term `Y` is a *basis* if for every closed term `M`
there is a pure combination `N` of `Y` and free variables such that `N`
β-reduces to `M`. This matches the paper's definition specialised to a
single basis element. -/

/-- `Y` is a single-term basis: every closed term is reachable, up to
β-reduction, from a pure combination of `Y` with free variables. -/
def IsBasis (Y : Term String) : Prop :=
  Y.LC ∧ Y.fv = ∅ ∧
    ∀ M : Term String, M.LC → M.fv = ∅ →
      ∃ N : Term String, PureComb Y N ∧ Relation.ReflTransGen FullBeta N M

/-! ## Specific reachability target: the `C` combinator behaviour

The paper's argument fixes three distinct fresh variables `A`, `B`, `C` and
constructs a pure combination `X` of basis combinators with
`X A B C ↠ C A B`. Below we package this with `IsBasis`. -/

/-- The shape `C A B` (the body of the `C` combinator applied to fresh
variables): `app (app (fvar c) (fvar a)) (fvar b)`. -/
def cab_witness (a b c : String) : Term String :=
  app (app (fvar c) (fvar a)) (fvar b)

/-- The shape `X A B C` for some `X`. -/
def applied_abc (X : Term String) (a b c : String) : Term String :=
  app (app (app X (fvar a)) (fvar b)) (fvar c)

/-- If `Y` is a basis then there is a pure combination `X` of `Y` whose
application to three distinct fresh variables `A B C` reduces to `C A B`. -/
theorem basis_reaches_cab {Y : Term String} (hY : IsBasis Y)
    (a b c : String) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    ∃ X : Term String, PureComb Y X ∧
      Relation.ReflTransGen FullBeta (applied_abc X a b c) (cab_witness a b c) := by
  -- The target `λ a b c. C A B`-applied-to-fresh-vars is closed up to the
  -- three free variables; one constructs `X` by taking the basis-witness for
  -- the (closed) lambda term `λABC. CAB` and discharging the abstractions.
  -- The full proof is left to a future iteration.
  sorry

/-! ## π-expressions

Given three fresh variables `A`, `B`, `C`, a *π-expression* is a term that

1. contains at least one occurrence of `C`;
2. has every occurrence of `A` or `B` inside a subterm that contains no `C`.

This is equivalent to saying the term has the shape `E₂[E₁[A,B], C]` where
`E₁[A,B]` mentions `A` or `B` but never `C`. We capture (1) and (2) via two
predicates over the set of free variables of subterms. -/

/-- The set `{a, b, c}` of three "marker" variables. -/
def abc_set (a b c : String) : Finset String := {a, b, c}

/-- A subterm is `C`-free relative to the marker set: it does not contain `c`. -/
def c_free (c : String) (M : Term String) : Prop := c ∉ M.fv

/-- A subterm has the *E₁* shape with respect to `a, b, c`: it is `c`-free
and contains at least one of `a`, `b`. -/
def is_E1 (a b c : String) (M : Term String) : Prop :=
  c_free c M ∧ (a ∈ M.fv ∨ b ∈ M.fv)

/-- The "skeleton" of a π-expression. Built from the marker `fvar c` and
copies of a single fixed subterm `E₁`, by applications. The paper's
informal `E₂[E₁[A,B], C]` is precisely this: a context whose holes are filled
by `E₁` and whose remaining leaves are `C`. -/
inductive PiBuild (c : String) (E1 : Term String) : Term String → Prop
  | leaf_c : PiBuild c E1 (fvar c)
  | leaf_E1 : PiBuild c E1 E1
  | app {M N} : PiBuild c E1 M → PiBuild c E1 N → PiBuild c E1 (app M N)

/-- A *π-expression* with respect to `a b c`: there is a single subterm `E₁`
that is `c`-free, contains `a` or `b`, and `M` is built from `fvar c` and
copies of `E₁` by applications, with `M` containing at least one `c`. -/
def PiExpr (a b c : String) (M : Term String) : Prop :=
  c ∈ M.fv ∧ ∃ E1 : Term String, c ∉ E1.fv ∧ (a ∈ E1.fv ∨ b ∈ E1.fv)
    ∧ PiBuild c E1 M

/-- Free variables of a `PiBuild`-shaped term are bounded by `{c} ∪ fv E₁`. -/
theorem PiBuild.fv_subset {c : String} {E1 M : Term String}
    (h : PiBuild c E1 M) : M.fv ⊆ insert c E1.fv := by
  induction h with
  | leaf_c => intro x hx; simp [fv] at hx; subst hx; simp
  | leaf_E1 => intro x hx; exact Finset.mem_insert_of_mem hx
  | app _ _ ihM ihN =>
      intro x hx
      simp [fv] at hx
      rcases hx with hx | hx
      · exact ihM hx
      · exact ihN hx

/-- The normal form `C A B` is **not** a π-expression: there is no choice of
`E₁` (`c`-free, containing `a` or `b`) for which `cab_witness` can be built
from `fvar c` and copies of `E₁` by applications. -/
theorem cab_not_PiExpr (a b c : String)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    ¬ PiExpr a b c (cab_witness a b c) := by
  rintro ⟨_, E1, hE1c, _, hbuild⟩
  -- `cab_witness = app (app (fvar c) (fvar a)) (fvar b)`.
  -- The outer `app` rules out the `leaf_c` case; the `leaf_E1` case forces
  -- `E1 = cab_witness`, which has `c` in its free variables, contradicting
  -- `hE1c`. The `app` case decomposes into the two factors and we recurse.
  unfold cab_witness at hbuild
  cases hbuild with
  | leaf_E1 =>
      -- `E1 = app (app (fvar c) (fvar a)) (fvar b)` contains `c`.
      apply hE1c; simp [fv]
  | app hM hN =>
      -- `hN : PiBuild c E1 (fvar b)`.
      cases hN with
      | leaf_c => exact hbc rfl   -- forces `b = c`
      | leaf_E1 =>
          -- `E1 = fvar b`. Now `hM : PiBuild c (fvar b) (app (fvar c) (fvar a))`.
          cases hM with
          | app hCf hAf =>
              -- `hAf : PiBuild c (fvar b) (fvar a)`.
              cases hAf with
              | leaf_c => exact hac rfl
              | leaf_E1 => exact hab rfl

/-! ## Lemma 1 of the paper

Head reduction of `X A B`, where `X` is a pure combination of rank-≤-2
basis combinators, must stop at a term of the form `T (E₁[A, B])` with
`T` a rank-2 combinator. Therefore `X A B C` reduces to a π-expression
`E₂[E₁[A,B], C] ≡ T(E₁[A,B]) C`. -/

/-- Iterated abstraction: `iter_abs n M` is `λ…λ M` with `n` abstractions. -/
def iter_abs : Nat → Term String → Term String
  | 0, M => M
  | n+1, M => abs (iter_abs n M)

/-- A rank-≤-2 combinator: closed, locally closed, of `head_abs_count`
at most 2, and whose body under those leading abstractions contains no
further `abs`. -/
def IsRankLeq2 (Q : Term String) : Prop :=
  Q.LC ∧ Q.fv = ∅ ∧ head_abs_count Q ≤ 2 ∧
    ∃ body, has_no_abs body = true ∧ Q = iter_abs (head_abs_count Q) body

/-- The standing assumption of the paper, specialised to a single-term
basis: `Y` itself is a rank-≤-2 combinator. Renamed from a misleading
"all" formulation: in the single-term-basis setting the only basis
combinator is `Y`, so the paper's "every combinator in B has rank ≤ 2"
collapses to `IsRankLeq2 Y`. -/
abbrev AllRankLeq2 (Y : Term String) : Prop := IsRankLeq2 Y

/-- **Lemma 1.** Under the rank-≤-2 hypothesis, head-reduction of `X A B`
terminates at `T (E₁[A,B])` where `T` is a rank-2 combinator. We state the
consequence used in the proof of the main theorem: `X A B C` reduces to a
π-expression. -/
theorem lemma1 {Y X : Term String} (hY : AllRankLeq2 Y) (hYbasis : IsBasis Y)
    (hX : PureComb Y X) (a b c : String)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    Relation.ReflTransGen FullBeta (applied_abc X a b c) (cab_witness a b c) →
    ∃ M, Relation.ReflTransGen FullBeta (applied_abc X a b c) M ∧ PiExpr a b c M := by
  -- Uses (quasi-)normalization to discard the case where head-reduction of
  -- `X A B` is infinite, and the rank-≤-2 hypothesis to rule out the case
  -- that head-reduction terminates at a variable (rules out by point (∗)
  -- of the paper).
  sorry

/-! ## Lemma 2 of the paper

A π-expression that reduces to `C A B` admits a leftmost-step reduction to
another π-expression that still reduces to `C A B`. The proof in the paper
splits into three cases depending on the position of the leftmost redex
(outside `E₁[A,B]`, strictly inside `E₁[A,B]`, or whose head is in
`E₁[A,B]` but the redex itself is not). -/

theorem lemma2 {a b c : String} {M : Term String}
    (hPi : PiExpr a b c M)
    (hRed : Relation.ReflTransGen FullBeta M (cab_witness a b c)) :
    ∃ N, PiExpr a b c N
      ∧ Relation.ReflTransGen FullBeta M N
      ∧ Relation.ReflTransGen FullBeta N (cab_witness a b c)
      -- The "with at least one leftmost contraction" content of the paper
      -- can be added once a leftmost-reduction predicate is available.
      := by
  sorry

/-! ## Main theorem

Putting Lemma 1, Lemma 2 and the (quasi-)normalization theorem together:
the rank-≤-2 hypothesis on `Y` contradicts `Y` being a basis. -/

/-- **Main theorem (paper):** No closed lambda term of rank ≤ 2 (in the
combinatory-logic sense) can be a single-term basis. -/
theorem rank_leq_two_not_basis (Y : Term String)
    (hY : AllRankLeq2 Y) : ¬ IsBasis Y := by
  intro hbasis
  -- Pick three distinct fresh variables.
  set a : String := "a"
  set b : String := "b"
  set c : String := "c"
  have hab : a ≠ b := by decide
  have hbc : b ≠ c := by decide
  have hac : a ≠ c := by decide
  -- 1. Get a pure combination `X` of `Y` with `X A B C ↠ C A B`.
  obtain ⟨X, hX, hXred⟩ := basis_reaches_cab hbasis a b c hab hbc hac
  -- 2. Apply Lemma 1: there is a π-expression `M0` reachable from `X A B C`.
  obtain ⟨M0, hRed0, hPi0⟩ := lemma1 hY hbasis hX a b c hab hbc hac hXred
  -- 3. By Church-Rosser, `M0 ↠ C A B`.
  have hRedM0 : Relation.ReflTransGen FullBeta M0 (cab_witness a b c) := by
    -- Both `applied_abc X a b c → cab_witness` and `applied_abc X a b c → M0`
    -- can be combined using confluence; we record the obligation here.
    sorry
  -- 4. Apply Lemma 2 iteratively, building an infinite quasi-leftmost
  --    reduction sequence of π-expressions. By the (quasi-)normalization
  --    theorem this must reach a normal form, which would be `C A B` —
  --    but `C A B` is not a π-expression (`cab_not_PiExpr`).
  exact (cab_not_PiExpr a b c hab hbc hac) (by
    -- The normalization-theorem step, which is currently unavailable, would
    -- close the contradiction here.
    sorry)

/-- A convenient reformulation: if `Y` has rank ≤ 2 and `Y` is a basis, this
is contradictory. -/
theorem not_basis_of_rank_leq_two (Y : Term String)
    (hY : IsRankLeq2 Y) (hbasis : IsBasis Y) : False :=
  rank_leq_two_not_basis Y hY hbasis

end Term

end LambdaCalculus.LocallyNameless.Untyped

end Cslib
