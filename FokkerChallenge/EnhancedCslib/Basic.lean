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
induction M with unfold openRec
| bvar _ => intros i
            split
            simp
            tauto
| fvar _ => tauto
| abs _ ih => intros i
              conv =>
                lhs
                unfold fv
              conv =>
                rhs
                lhs
                unfold fv
              conv =>
                rhs
                rhs
                lhs
                unfold fv
              apply ih
| app a b iha ihb =>  intros i
                      conv =>
                        lhs
                        unfold fv
                      conv =>
                        rhs
                        lhs
                        unfold fv
                      conv =>
                        rhs
                        rhs
                        lhs
                        unfold fv
                      specialize iha i
                      specialize ihb i
                      cases iha <;> cases ihb <;> grind

end Term

end LambdaCalculus.LocallyNameless.Untyped

end Cslib
