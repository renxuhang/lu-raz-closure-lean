import SixRowFullOld
import SixRowFullNormal

namespace LuRazSixRowClosure
open LuRazClosure LuRazParametric
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

theorem full_source_one_extra (q i : Nat) (hq : 4≤q)
    (ha : LuRazSixRow.BRow q i 1) :
    LuRazSixRow.BRow q i (q+2) ∨ LuRazSixRow.BRow q i (2*q+1) := by
  by_cases hs : FullChanged q i
  · rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [full_row_one q 1 hq] at ha; omega
    · exact Or.inl ((full_row_two q _ hq).mpr (by omega))
    · rw [full_row_four q 1 hq] at ha; omega
    · rw [LuRazSixRow.row_middle q 1 hq] at ha; omega
    · exact Or.inl ((LuRazSixRow.row_last q _ hq).mpr (by omega))
    · rw [LuRazSixRow.row_n q 1 hq] at ha; omega
  · rw [full_unchanged q i 1 hs] at ha
    rw [full_unchanged q i (q+2) hs,full_unchanged q i (2*q+1) hs]
    unfold FullChanged at hs
    unfold Row at ha
    rcases ha with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl ((row_case_0 q i _ (by omega) h.1).mpr (by omega))
    · omega
    · omega
    · exact Or.inr ((row_case_3 q i _ (by omega) h.1).mpr (by omega))
    · omega
    · exact Or.inr ((row_case_5 q i _ (by omega) ⟨h.1,h.2.1⟩).mpr (by omega))
    · exact Or.inr ((row_case_6 q i _ (by omega) ⟨h.1,h.2.1⟩).mpr (by omega))
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · exact Or.inl ((row_case_15 q i _ (by omega) h.1).mpr (by omega))

theorem full_source_two_end (q i : Nat) (hq : 4≤q)
    (ha : LuRazSixRow.BRow q i 2) :
    LuRazSixRow.BRow q i (4*q-2) ∨ LuRazSixRow.BRow q i (4*q-1) := by
  by_cases hs : FullChanged q i
  · rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ((full_row_one q _ hq).mpr (by omega))
    · rw [full_row_two q 2 hq] at ha; omega
    · exact Or.inl ((full_row_four q _ hq).mpr (by omega))
    · exact Or.inl ((LuRazSixRow.row_middle q _ hq).mpr (by omega))
    · rw [LuRazSixRow.row_last q 2 hq] at ha; omega
    · rw [LuRazSixRow.row_n q 2 hq] at ha; omega
  · rw [full_unchanged q i 2 hs] at ha
    rw [full_unchanged q i (4*q-2) hs,full_unchanged q i (4*q-1) hs]
    unfold FullChanged at hs
    unfold Row at ha
    rcases ha with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inr ((row_case_0 q i _ (by omega) h.1).mpr (by omega))
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · exact Or.inl ((row_case_7 q i _ (by omega) h.1).mpr (by omega))
    · omega
    · exact Or.inr ((row_case_9 q i _ (by omega) h.1).mpr (by omega))
    · exact Or.inr ((row_case_10 q i _ (by omega) ⟨h.1,h.2.1⟩).mpr (by omega))
    · exact Or.inr ((row_case_11 q i _ (by omega) h.1).mpr (by omega))
    · exact Or.inr ((row_case_12 q i _ (by omega) ⟨h.1,h.2.1⟩).mpr (by omega))
    · omega
    · omega
    · omega

theorem full_source_left_horn (q i : Nat) (hq : 4≤q)
    (ha : LuRazSixRow.BRow q i (q+3)) :
    LuRazSixRow.BRow q i (2*q+1) ∨ LuRazSixRow.BRow q i (4*q-1) := by
  by_cases hs : FullChanged q i
  · rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [full_row_one q (q+3) hq] at ha; omega
    · exact Or.inr ((full_row_two q _ hq).mpr (by omega))
    · rw [full_row_four q (q+3) hq] at ha; omega
    · rw [LuRazSixRow.row_middle q (q+3) hq] at ha; omega
    · exact Or.inl ((LuRazSixRow.row_last q _ hq).mpr (by omega))
    · exact Or.inr ((LuRazSixRow.row_n q _ hq).mpr (by omega))
  · rw [full_unchanged q i (q+3) hs] at ha
    rw [full_unchanged q i (2*q+1) hs,full_unchanged q i (4*q-1) hs]
    unfold FullChanged at hs
    unfold Row at ha
    rcases ha with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inr ((row_case_0 q i _ (by omega) h.1).mpr (by omega))
    · omega
    · omega
    · exact Or.inl ((row_case_3 q i _ (by omega) h.1).mpr (by omega))
    · omega
    · exact Or.inl ((row_case_5 q i _ (by omega) ⟨h.1,h.2.1⟩).mpr (by omega))
    · exact Or.inl ((row_case_6 q i _ (by omega) ⟨h.1,h.2.1⟩).mpr (by omega))
    · omega
    · omega
    · omega
    · omega
    · exact Or.inr ((row_case_11 q i _ (by omega) h.1).mpr (by omega))
    · exact Or.inr ((row_case_12 q i _ (by omega) ⟨h.1,h.2.1⟩).mpr (by omega))
    · omega
    · omega
    · omega

theorem full_test_necessary (q : Nat) (hq : 4≤q) {R : Nat → Prop}
    (hg : Generated q R) (hc : CoreFull R) : FullTest q R := by
  have h2 : R (4*q-2) ∨ R (4*q-1) := by
    obtain ⟨i,_,hi,hs⟩ := point_covered q hg hc.2.1
    exact (full_source_two_end q i hq hi).elim (fun h => Or.inl (hs _ h)) (fun h => Or.inr (hs _ h))
  have h1 : R (q+2) ∨ R (2*q+1) := by
    obtain ⟨i,_,hi,hs⟩ := point_covered q hg hc.1
    exact (full_source_one_extra q i hq hi).elim (fun h => Or.inl (hs _ h)) (fun h => Or.inr (hs _ h))
  have hh : R (2*q+2) ∨ R (2*q+3) := by
    classical
    by_cases hm : R (2*q+2)
    · exact Or.inl hm
    · exact Or.inr (full_no_middle_source q hq hg hc.2.2.2 hm _
        ((LuRazSixRow.row_middle q _ hq).mpr (by omega)))
  have hn : R (2*q+2) ∨ R (4*q) := by
    classical
    by_cases hm : R (2*q+2)
    · exact Or.inl hm
    · exact Or.inr (full_no_middle_source q hq hg hc.2.2.2 hm _
        ((LuRazSixRow.row_middle q _ hq).mpr (by omega)))
  refine ⟨⟨h2,hh.elim (fun h => Or.inr (Or.inl h)) (fun h => Or.inr (Or.inr h)),?_⟩,
    h1,hh,hn⟩
  intro hp
  obtain ⟨i,_,hi,hs⟩ := point_covered q hg hp
  exact (full_source_left_horn q i hq hi).elim (fun h => Or.inl (hs _ h)) (fun h => Or.inr (hs _ h))

theorem full_generated_normal (q : Nat) (hq : 4≤q) {R : Nat → Prop}
    (hg : Generated q R) (hc : CoreFull R) :
    ∃ z : NFFull, FullKeep q z ∧ ∀ e, R e ↔ z.eval q e := by
  obtain ⟨z,hz,he⟩ := (full_closure_exact q hq R).mp ⟨full_generated_old q hq hg hc,hc⟩
  have hp := full_test_necessary q hq hg hc
  have hzp : FullTest q (z.eval q) := by
    unfold FullTest LuRazThreeRow.FullPass FullExtras at *
    simpa only [he] using hp
  exact ⟨z,⟨hz,(full_test_classification q hq z hz).mp hzp⟩,he⟩

end LuRazSixRowClosure
