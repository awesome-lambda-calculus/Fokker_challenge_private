import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.LcAt
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullEta
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBetaEtaConfluence
import Mathlib.Data.Set.Card

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

/-
-- Not sure we really need this
-- Not sure this theorem is correct: we might need eta-equal rather than eta-reduction
-- eta-equal is not defined in cslib
theorem double_eta {M N: Term String} : M.LC ->
LcAt 2 N ->
(∀ x y,
x ∉ M.fv ∪ N.fv ->
y ∉ M.fv ∪ N.fv ->
x ≠ y ->
Relation.ReflTransGen FullBetaEta (Term.app (Term.app M (Term.fvar x)) (Term.fvar y)) (openRec 1 (Term.fvar y) (openRec 0 (Term.fvar x) N))) ->
Relation.ReflTransGen FullBetaEta M N.abs.abs := by
-- 应该不需要证明
-- 在 apply Xi.abs 的时候, 会自然出现这个目标
sorry
-/

end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
