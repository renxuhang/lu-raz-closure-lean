import SixRowFullSources

namespace LuRazSixRowClosure
open LuRazClosure LuRazParametric
set_option maxRecDepth 32768
set_option maxHeartbeats 500000

theorem source_three_no_last (q i : Nat) (hq : 4≤q) (hi : i≤4*q+2)
    (h3 : LuRazSixRow.BRow q i 3) (hn : ¬LuRazSixRow.BRow q i (4*q-1)) : i=4*q-1 := by
  by_cases hs : FullChanged q i
  · rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [full_row_one q 3 hq] at h3; omega
    · exact False.elim (hn ((full_row_two q (4*q-1) hq).mpr (by omega)))
    · exact False.elim (hn ((full_row_four q (4*q-1) hq).mpr (by omega)))
    · rw [LuRazSixRow.row_middle q 3 hq] at h3; omega
    · rfl
    · exact False.elim (hn ((LuRazSixRow.row_n q (4*q-1) hq).mpr (by omega)))
  · rw [full_unchanged q i 3 hs] at h3
    rw [full_unchanged q i (4*q-1) hs] at hn
    unfold FullChanged at hs
    unfold Row at h3
    rcases h3 with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact False.elim (hn ((row_case_0 q i _ (by omega) h.1).mpr (by omega)))
    · omega
    · omega
    · omega
    · exact False.elim (hn ((row_case_4 q i _ (by omega) h.1).mpr (by omega)))
    · omega
    · omega
    · omega
    · omega
    · exact False.elim (hn ((row_case_9 q i _ (by omega) h.1).mpr (by omega)))
    · exact False.elim (hn ((row_case_10 q i _ (by omega) ⟨h.1,h.2.1⟩).mpr (by omega)))
    · exact False.elim (hn ((row_case_11 q i _ (by omega) h.1).mpr (by omega)))
    · exact False.elim (hn ((row_case_12 q i _ (by omega) ⟨h.1,h.2.1⟩).mpr (by omega)))
    · omega
    · omega
    · omega

theorem source_four_no_middle (q i : Nat) (hq : 4≤q) (hi : i≤4*q+2)
    (h4 : LuRazSixRow.BRow q i 4) (hn : ¬LuRazSixRow.BRow q i (2*q+2)) : i=2*q+2 := by
  by_cases hs : FullChanged q i
  · rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
    · exact False.elim (hn ((full_row_one q (2*q+2) hq).mpr (by omega)))
    · rw [full_row_two q 4 hq] at h4; omega
    · rw [full_row_four q 4 hq] at h4; omega
    · rfl
    · rw [LuRazSixRow.row_last q 4 hq] at h4; omega
    · rw [LuRazSixRow.row_n q 4 hq] at h4; omega
  · rw [full_unchanged q i 4 hs] at h4
    rw [full_unchanged q i (2*q+2) hs] at hn
    unfold FullChanged at hs
    unfold Row at h4
    rcases h4 with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact False.elim (hn ((row_case_0 q i _ (by omega) h.1).mpr (by omega)))
    · omega
    · omega
    · exact False.elim (hn ((row_case_3 q i _ (by omega) h.1).mpr (by omega)))
    · omega
    · exact False.elim (hn ((row_case_5 q i _ (by omega) ⟨h.1,h.2.1⟩).mpr (by omega)))
    · exact False.elim (hn ((row_case_6 q i _ (by omega) ⟨h.1,h.2.1⟩).mpr (by omega)))
    · exact False.elim (hn ((row_case_7 q i _ (by omega) h.1).mpr (by omega)))
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega

theorem full_no_last_prefix (q : Nat) (hq : 4≤q) {R : Nat → Prop}
    (hg : Generated q R) (h3 : R 3) (hn : ¬R (4*q-1)) :
    ∀ f, (5≤f ∧ f≤2*q+2) → R f := by
  obtain ⟨i,hi,hi3,hsub⟩ := point_covered q hg h3
  have hie := source_three_no_last q i hq hi hi3 (fun he => hn (hsub _ he))
  subst i
  intro f hf
  exact hsub f ((LuRazSixRow.row_last q f hq).mpr (by omega))

theorem full_no_middle_source (q : Nat) (hq : 4≤q) {R : Nat → Prop}
    (hg : Generated q R) (h4 : R 4) (hn : ¬R (2*q+2)) :
    ∀ f, LuRazSixRow.BRow q (2*q+2) f → R f := by
  obtain ⟨i,hi,hi4,hsub⟩ := point_covered q hg h4
  have hie := source_four_no_middle q i hq hi hi4 (fun he => hn (hsub _ he))
  subst i
  exact hsub

def OldCover (q : Nat) (R : Nat → Prop) (e : Nat) : Prop :=
  ∃ j, j≤4*q+2 ∧ Row q j e ∧ ∀ f, Row q j f → R f

theorem old_cover_last (q : Nat) (hq : 4≤q) {R : Nat → Prop}
    (hg : Generated q R) (hc : CoreFull R) (hn : R (4*q-1)) : OldCover q R (4*q-1) := by
  obtain ⟨i,hi,hi2,hsub⟩ := point_covered q hg hc.2.1
  by_cases hs : FullChanged q i
  · rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨1,by omega,(row_case_1 q 1 _ (by omega) rfl).mpr (by omega),?_⟩
      intro f hf
      rw [row_case_1 q 1 f (by omega) rfl] at hf
      by_cases he : f=4*q-1
      · simpa [he] using hn
      · exact hsub f ((full_row_one q f hq).mpr (by omega))
    · rw [full_row_two q 2 hq] at hi2; omega
    · refine ⟨4,by omega,(row_case_4 q 4 _ (by omega) rfl).mpr (by omega),?_⟩
      intro f hf
      rw [row_case_4 q 4 f (by omega) rfl] at hf
      rcases hf with hf | hf | hf
      · simpa [hf] using hc.1
      · simpa [hf] using hc.2.2.1
      · exact hsub f ((full_row_four q f hq).mpr (by omega))
    · refine ⟨2*q+2,by omega,(row_case_8 q _ _ (by omega) rfl).mpr (by omega),?_⟩
      intro f hf
      rw [row_case_8 q _ f (by omega) rfl] at hf
      by_cases he : f=4*q-1
      · simpa [he] using hn
      · exact hsub f ((LuRazSixRow.row_middle q f hq).mpr (by omega))
    · rw [LuRazSixRow.row_last q 2 hq] at hi2; omega
    · rw [LuRazSixRow.row_n q 2 hq] at hi2; omega
  · have ho2 := (full_unchanged q i 2 hs).mp hi2
    by_cases he : i=2*q+1
    · subst i
      refine ⟨2*q+2,by omega,(row_case_8 q _ _ (by omega) rfl).mpr (by omega),?_⟩
      intro f hf
      rw [row_case_8 q _ f (by omega) rfl] at hf
      by_cases hfn : f=4*q-1
      · simpa [hfn] using hn
      · apply hsub f
        rw [full_unchanged q _ f hs,row_case_7 q _ f (by omega) rfl]
        omega
    · refine ⟨i,hi,?_,fun f hf => hsub f ((full_unchanged q i f hs).mpr hf)⟩
      unfold FullChanged at hs
      unfold Row at ho2
      rcases ho2 with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact (row_case_0 q i _ (by omega) h.1).mpr (by omega)
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
      · exact (row_case_9 q i _ (by omega) h.1).mpr (by omega)
      · exact (row_case_10 q i _ (by omega) ⟨h.1,h.2.1⟩).mpr (by omega)
      · exact (row_case_11 q i _ (by omega) h.1).mpr (by omega)
      · exact (row_case_12 q i _ (by omega) ⟨h.1,h.2.1⟩).mpr (by omega)
      · omega
      · omega
      · omega

theorem old_cover_last_source_three (q : Nat) (hq : 4≤q) {R : Nat → Prop}
    (hg : Generated q R) (hc : CoreFull R)
    (hp : ∀ f, (5≤f ∧ f≤2*q+2) → R f) : OldCover q R 3 := by
  obtain ⟨i,hi,hi2,hsub⟩ := point_covered q hg hc.2.1
  by_cases hr : R (3*q+1)
  · refine ⟨4*q,by omega,(row_case_13 q _ _ (by omega) rfl).mpr (by omega),?_⟩
    intro f hf
    rw [row_case_13 q _ f (by omega) rfl] at hf
    rcases hf with hf | hf | hf
    · simpa [hf] using hc.2.2.1
    · exact hp f hf
    · simpa [hf] using hr
  · by_cases hs : FullChanged q i
    · rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
      · exact False.elim (hr (hsub _ ((full_row_one q _ hq).mpr (by omega))))
      · rw [full_row_two q 2 hq] at hi2; omega
      · exact False.elim (hr (hsub _ ((full_row_four q _ hq).mpr (by omega))))
      · exact False.elim (hr (hsub _ ((LuRazSixRow.row_middle q _ hq).mpr (by omega))))
      · rw [LuRazSixRow.row_last q 2 hq] at hi2; omega
      · rw [LuRazSixRow.row_n q 2 hq] at hi2; omega
    · refine ⟨i,hi,?_,fun f hf => hsub f ((full_unchanged q i f hs).mpr hf)⟩
      have ho2 := (full_unchanged q i 2 hs).mp hi2
      have hnr : ¬Row q i (3*q+1) := fun he => hr (hsub _ ((full_unchanged q i _ hs).mpr he))
      unfold FullChanged at hs
      unfold Row at ho2
      rcases ho2 with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact (row_case_0 q i _ (by omega) h.1).mpr (by omega)
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
      · exact False.elim (hnr ((row_case_7 q i (3*q+1) (by omega) h.1).mpr (Or.inr (Or.inr ⟨by omega,by omega⟩))))
      · omega
      · exact (row_case_9 q i _ (by omega) h.1).mpr (by omega)
      · exact (row_case_10 q i _ (by omega) ⟨h.1,h.2.1⟩).mpr (by omega)
      · exact (row_case_11 q i _ (by omega) h.1).mpr (by omega)
      · exact (row_case_12 q i _ (by omega) ⟨h.1,h.2.1⟩).mpr (by omega)
      · omega
      · omega
      · omega

end LuRazSixRowClosure


