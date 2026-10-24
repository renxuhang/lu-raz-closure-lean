import SixRowFrequencyBridge
import SixRowRemovedRangeCounts
import SixRowAddedRangeCounts
import SixRowRegularGroupCounts
import SixRowSpecialGroupCounts
import SixRowFiniteGroupCounts

namespace LuRazSixRowSpectrum
open LuRazClosure LuRazEnumeration LuRazThreeRow LuRazSixRowClosure Difference
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

theorem removed_group_count_closed (q e : Nat) (hq : 4≤q) (he : 1≤e) (hen : e≤4*q)
    (k : Nat) (hk : k<27) :
    CountAt ((removedGroup q k).map (RemovedForm.eval q)) e=
      (removedGroupCounts (q:Int) (e:Int)).getD k 0 := by
  have hc : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨ k=7 ∨ k=8 ∨ k=9 ∨ k=10 ∨ k=11 ∨ k=12 ∨ k=13 ∨ k=14 ∨ k=15 ∨ k=16 ∨ k=17 ∨ k=18 ∨ k=19 ∨ k=20 ∨ k=21 ∨ k=22 ∨ k=23 ∨ k=24 ∨ k=25 ∨ k=26 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact removed_finite_count_0 q e hq he hen
  · exact removed_finite_count_1 q e hq he hen
  · exact removed_finite_count_2 q e hq he hen
  · exact removed_finite_count_3 q e hq he hen
  · exact removed_count_R6C_regular q e hq he hen
  · exact removed_finite_count_5 q e hq he hen
  · exact removed_count_R6D q e hq he hen
  · exact removed_finite_count_7 q e hq he hen
  · exact removed_count_R7E q e hq he hen
  · exact removed_count_R7D q e hq he hen
  · exact removed_count_R10 q e hq he hen
  · exact removed_count_R11J q e hq he hen
  · exact removed_count_R11AJ q e hq he hen
  · exact removed_count_R11AK q e hq he hen
  · exact removed_finite_count_14 q e hq he hen
  · exact removed_count_R13CJ q e hq he hen
  · exact removed_count_R13ZJ q e hq he hen
  · exact removed_count_R13CZJ q e hq he hen
  · exact removed_finite_count_18 q e hq he hen
  · exact removed_finite_count_19 q e hq he hen
  · exact removed_count_R14line q e hq he hen
  · exact removed_count_R14C q e hq he hen
  · exact removed_finite_count_22 q e hq he hen
  · exact removed_count_R15right q e hq he hen
  · exact removed_count_R15gap q e hq he hen
  · exact removed_count_R15line q e hq he hen
  · exact removed_count_R15short q e hq he hen

theorem added_group_count_closed (q e : Nat) (hq : 4≤q) (he : 1≤e) (hen : e≤4*q)
    (k : Nat) (hk : k<16) :
    CountAt ((addedGroup q k).map (AddedForm.eval q)) e=
      (addedGroupCounts (q:Int) (e:Int)).getD k 0 := by
  have hc : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨ k=7 ∨ k=8 ∨ k=9 ∨ k=10 ∨ k=11 ∨ k=12 ∨ k=13 ∨ k=14 ∨ k=15 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact added_finite_count_0 q e hq he hen
  · exact added_finite_count_1 q e hq he hen
  · exact added_count_N6C_regular q e hq he hen
  · exact added_finite_count_3 q e hq he hen
  · exact added_count_N6E q e hq he hen
  · exact added_count_N7C_regular q e hq he hen
  · exact added_finite_count_6 q e hq he hen
  · exact added_count_N7right q e hq he hen
  · exact added_finite_count_8 q e hq he hen
  · exact added_count_N10 q e hq he hen
  · exact added_count_N11J q e hq he hen
  · exact added_count_N11AJ q e hq he hen
  · exact added_count_N11AK q e hq he hen
  · exact added_count_N13plain q e hq he hen
  · exact added_count_N13isolated q e hq he hen
  · exact added_count_N13right q e hq he hen

theorem count_map_flatMap {α β : Type} (l : List α) (f : α → List β)
    (g : β → Nat → Prop) (e : Nat) :
    CountAt ((l.flatMap f).map g) e=
      (l.map (fun a => CountAt ((f a).map g) e)).sum := by
  induction l with
  | nil => simp [CountAt]
  | cons a l ih =>
    simp only [List.flatMap_cons,List.map_append,count_at_append,ih,List.map_cons,List.sum_cons]

theorem removed_frequency_closed (q e : Nat) (hq : 4≤q) (he : 1≤e) (hen : e≤4*q) :
    removedFrequency q e=(removedGroupCounts (q:Int) (e:Int)).sum := by
  unfold removedFrequency RemovedMembers removedList
  rw [count_map_flatMap]
  apply congrArg List.sum
  calc
    ((List.range 27).map (fun k => CountAt ((removedGroup q k).map (RemovedForm.eval q)) e))=
        (List.range 27).map (fun k => (removedGroupCounts (q:Int) (e:Int)).getD k 0) := by
      apply List.map_congr_left
      intro k hk
      exact removed_group_count_closed q e hq he hen k (List.mem_range.mp hk)
    _=removedGroupCounts (q:Int) (e:Int) := by rfl

theorem added_frequency_closed (q e : Nat) (hq : 4≤q) (he : 1≤e) (hen : e≤4*q) :
    addedFrequency q e=(addedGroupCounts (q:Int) (e:Int)).sum := by
  unfold addedFrequency AddedMembers addedList
  rw [count_map_flatMap]
  apply congrArg List.sum
  calc
    ((List.range 16).map (fun k => CountAt ((addedGroup q k).map (AddedForm.eval q)) e))=
        (List.range 16).map (fun k => (addedGroupCounts (q:Int) (e:Int)).getD k 0) := by
      apply List.map_congr_left
      intro k hk
      exact added_group_count_closed q e hq he hen k (List.mem_range.mp hk)
    _=addedGroupCounts (q:Int) (e:Int) := by rfl

theorem six_row_frequency_delta_closed (q e : Nat) (hq : 4≤q) (he : 1≤e) (hen : e≤4*q) :
    sixRowFrequency q e=variantFrequency q e-
      (removedGroupCounts (q:Int) (e:Int)).sum+(addedGroupCounts (q:Int) (e:Int)).sum := by
  rw [six_row_frequency_delta q e hq,removed_frequency_closed q e hq he hen,
    added_frequency_closed q e hq he hen]

end LuRazSixRowSpectrum
