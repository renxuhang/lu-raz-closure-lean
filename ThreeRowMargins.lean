import ThreeRowStructure
import LuRazResults

namespace LuRazThreeRow
open LuRazParametric RazReimerPredicates LuRazCounting
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

theorem mark_balance (q i e : Nat) (hq : 4 ≤ q) :
    mark (VRow q i e) + mark (Removed q i e) =
      mark (Row q i e) + mark (Added q i e) := by
  classical
  have hr := removed_present q i e hq
  have ha := added_absent q i e hq
  by_cases hp : Row q i e <;> by_cases hrem : Removed q i e <;>
    by_cases hadd : Added q i e <;> simp_all [mark,VRow]

theorem removed_col (q i e : Nat) (hq : 4 ≤ q) :
    mark (Removed q i e) = mark (i=2 ∧ e=4) +
      mark (i=4 ∧ e=4*q-1) + mark (i=4*q-1 ∧ e=2) := by
  unfold Removed mark
  repeat first | omega | split

theorem added_col (q i e : Nat) (hq : 4 ≤ q) :
    mark (Added q i e) = mark (i=2 ∧ e=4*q-1) +
      mark (i=4 ∧ e=2) + mark (i=4*q-1 ∧ e=4) := by
  unfold Added mark
  repeat first | omega | split

theorem column_margin (q e : Nat) (hq : 4 ≤ q) :
    sumTo (fun i => mark (VRow q i e)) (4*q+3) =
      sumTo (fun i => mark (Row q i e)) (4*q+3) := by
  have h := sumTo_congr (4*q+3) (fun i _ => mark_balance q i e hq)
  rw [sumTo_add,sumTo_add] at h
  have hr : sumTo (fun i => mark (Removed q i e)) (4*q+3) =
      mark (e=4) + mark (e=4*q-1) + mark (e=2) := by
    calc
      _ = sumTo (fun i => mark (i=2 ∧ e=4) +
          mark (i=4 ∧ e=4*q-1) + mark (i=4*q-1 ∧ e=2)) (4*q+3) :=
        sumTo_congr _ (fun i _ => removed_col q i e hq)
      _ = _ := by rw [sumTo_add,sumTo_add,
        sumTo_point_and _ 2 _ (by omega),sumTo_point_and _ 4 _ (by omega),
        sumTo_point_and _ (4*q-1) _ (by omega)]
  have ha : sumTo (fun i => mark (Added q i e)) (4*q+3) =
      mark (e=4*q-1) + mark (e=2) + mark (e=4) := by
    calc
      _ = sumTo (fun i => mark (i=2 ∧ e=4*q-1) +
          mark (i=4 ∧ e=2) + mark (i=4*q-1 ∧ e=4)) (4*q+3) :=
        sumTo_congr _ (fun i _ => added_col q i e hq)
      _ = _ := by rw [sumTo_add,sumTo_add,
        sumTo_point_and _ 2 _ (by omega),sumTo_point_and _ 4 _ (by omega),
        sumTo_point_and _ (4*q-1) _ (by omega)]
  omega

theorem removed_row (q i e : Nat) (hq : 4 ≤ q) :
    mark (Removed q i (e+1)) = mark (e=3 ∧ i=2) +
      mark (e=4*q-2 ∧ i=4) + mark (e=1 ∧ i=4*q-1) := by
  unfold Removed mark
  repeat first | omega | split

theorem added_row (q i e : Nat) (hq : 4 ≤ q) :
    mark (Added q i (e+1)) = mark (e=4*q-2 ∧ i=2) +
      mark (e=1 ∧ i=4) + mark (e=3 ∧ i=4*q-1) := by
  unfold Added mark
  repeat first | omega | split

theorem row_margin (q i : Nat) (hq : 4 ≤ q) :
    sumTo (fun e => mark (VRow q i (e+1))) (4*q) = rowTally q i := by
  have h := sumTo_congr (4*q) (fun e _ => mark_balance q i (e+1) hq)
  rw [sumTo_add,sumTo_add] at h
  have hr : sumTo (fun e => mark (Removed q i (e+1))) (4*q) =
      mark (i=2) + mark (i=4) + mark (i=4*q-1) := by
    calc
      _ = sumTo (fun e => mark (e=3 ∧ i=2) +
          mark (e=4*q-2 ∧ i=4) + mark (e=1 ∧ i=4*q-1)) (4*q) :=
        sumTo_congr _ (fun e _ => removed_row q i e hq)
      _ = _ := by rw [sumTo_add,sumTo_add,
        sumTo_point_and _ 3 _ (by omega),sumTo_point_and _ (4*q-2) _ (by omega),
        sumTo_point_and _ 1 _ (by omega)]
  have ha : sumTo (fun e => mark (Added q i (e+1))) (4*q) =
      mark (i=2) + mark (i=4) + mark (i=4*q-1) := by
    calc
      _ = sumTo (fun e => mark (e=4*q-2 ∧ i=2) +
          mark (e=1 ∧ i=4) + mark (e=3 ∧ i=4*q-1)) (4*q) :=
        sumTo_congr _ (fun e _ => added_row q i e hq)
      _ = _ := by rw [sumTo_add,sumTo_add,
        sumTo_point_and _ (4*q-2) _ (by omega),sumTo_point_and _ 1 _ (by omega),
        sumTo_point_and _ 3 _ (by omega)]
  unfold rowTally
  omega

theorem frequency_unchanged (q : Nat) (hq : 4 ≤ q) (e : Fin (4*q)) :
    frequency (V q) e = frequency (S q) e := by
  classical
  have h := column_margin q (e.val+1) hq
  rw [sumTo_filter,sumTo_filter] at h
  have hv := finRange_filter_length (fun i => VRow q i (e.val+1)) (4*q+3)
  have hs := finRange_filter_length (fun i => Row q i (e.val+1)) (4*q+3)
  change ((List.finRange _).filter (fun i => decide (VRow q i.val (e.val+1)))).length =
    ((List.finRange _).filter (fun i => decide (Row q i.val (e.val+1)))).length
  rw [hv,hs]
  omega

def vSize (q : Nat) (i : Fin (4*q+3)) : Nat := by
  classical
  exact ((List.finRange (4*q)).filter (fun e => decide (V q i e))).length

theorem size_unchanged (q : Nat) (hq : 4 ≤ q) (i : Fin (4*q+3)) :
    vSize q i = setSize q i := by
  classical
  have h := row_margin q i.val hq
  rw [rowTally_size q i] at h
  rw [sumTo_filter] at h
  have hv := finRange_filter_length (fun e => VRow q i.val (e+1)) (4*q)
  change ((List.finRange _).filter (fun e => decide (VRow q i.val (e.val+1)))).length = _
  rw [hv]
  omega

theorem uniform_frequency (q : Nat) (hq : 4 ≤ q) (e : Fin (4*q)) :
    frequency (V q) e = 2*q+1 := by
  rw [frequency_unchanged q hq e]
  exact predicate_frequencies q (by omega) e

theorem no_abundant (q : Nat) (hq : 4 ≤ q) : ¬HasAbundantElement (V q) := by
  rintro ⟨e,h⟩
  rw [uniform_frequency q hq e] at h
  omega

theorem min_lower (q : Nat) (hq : 4 ≤ q) (i : Fin (4*q+3)) : q-1 ≤ vSize q i := by
  rw [size_unchanged q hq i]
  exact minimum_size_lower q (by omega) i

theorem min_attained (q : Nat) (hq : 4 ≤ q) :
    vSize q ⟨4*q+1,by omega⟩ = q-1 := by
  rw [size_unchanged q hq]
  exact minimum_size_attained q (by omega)

end
end LuRazThreeRow
