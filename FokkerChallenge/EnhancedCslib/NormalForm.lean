import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta
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

theorem has_redex_equiv_full_beta {M}: has_redex M /\ M.LC <-> ∃ N, FullBeta M N := by
sorry

theorem no_redex_refl {M N}: has_redex M = false -> Relation.ReflTransGen FullBeta M N -> M = N := by
sorry

theorem reflTransGen_iff_eqvGen_of_normal {M N: Term String} (hn: N.has_redex = false) : Relation.ReflTransGen FullBetaEta M N.abs ↔ Relation.EqvGen FullBetaEta M N.abs := by
sorry
