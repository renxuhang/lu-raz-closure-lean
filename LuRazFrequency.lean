import ColumnTotalCases
import FrequencyBridge

namespace LuRazParametric
open LuRazCounting RazReimerPredicates
noncomputable section

theorem exact_frequencies (q e : Nat) (hq : 3 ≤ q)
    (he1 : 1 ≤ e) (he2 : e ≤ 4*q) :
    sumTo (weight q e) (4*q+3) = 2*(q : Int)+1 := by
  rw [frequency_as_columnTotal q e hq he1 he2, columnTotal_value q e hq he1 he2]

theorem predicate_frequencies (q : Nat) (hq : 3 ≤ q) (e : Fin (4*q)) :
    frequency (S q) e = 2*q+1 := by
  classical
  have hf := exact_frequencies q (e.val+1) hq (by omega) (by have := e.isLt; omega)
  unfold weight at hf
  rw [sumTo_filter] at hf
  have hb := finRange_filter_length (fun i => Row q i (e.val+1)) (4*q+3)
  change ((List.finRange (4*q+3)).filter (fun i => decide (Row q i.val (e.val+1)))).length = _
  rw [hb]
  omega

theorem no_abundant_element (q : Nat) (hq : 3 ≤ q) :
    ¬ HasAbundantElement (S q) := by
  rintro ⟨e,he⟩
  rw [predicate_frequencies q hq e] at he
  omega

end
end LuRazParametric
