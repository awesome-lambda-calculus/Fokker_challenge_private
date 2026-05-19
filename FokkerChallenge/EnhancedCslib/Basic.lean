import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Congruence
import Mathlib.Data.Finset.Lattice.Basic

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

theorem openRec_fv_cases {M N: Term String} :
(i: Nat) ->
(openRec i N M).fv = M.fv \/
(openRec i N M).fv = M.fv ∪ N.fv := by
induction M with grind

end Term

end LambdaCalculus.LocallyNameless.Untyped

end Cslib
