import SixRowFullCovers

namespace LuRazSixRowClosure
open LuRazClosure LuRazParametric
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

theorem full_old_point (q : Nat) (hq : 4≤q) {R : Nat → Prop}
    (hg : Generated q R) (hc : CoreFull R) {e : Nat} (he : R e) : OldCover q R e := by
  obtain ⟨i,hi,hie,hsub⟩ := point_covered q hg he
  by_cases hs : FullChanged q i
  · rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
    · have hiE := (full_row_one q e hq).mp hie
      by_cases hn : R (4*q-1)
      · by_cases he4 : e=4
        · refine ⟨2*q+2,by omega,(row_case_8 q _ _ (by omega) rfl).mpr (by omega),?_⟩
          intro f hf
          rw [row_case_8 q _ f (by omega) rfl] at hf
          by_cases hfn : f=4*q-1
          · simpa [hfn] using hn
          · exact hsub f ((full_row_one q f hq).mpr (by omega))
        · refine ⟨1,by omega,(row_case_1 q _ _ (by omega) rfl).mpr (by omega),?_⟩
          intro f hf
          rw [row_case_1 q _ f (by omega) rfl] at hf
          by_cases hfn : f=4*q-1
          · simpa [hfn] using hn
          · exact hsub f ((full_row_one q f hq).mpr (by omega))
      · have hp := full_no_last_prefix q hq hg hc.2.2.1 hn
        by_cases hk : e=4 ∨ (2*q+2≤e ∧ e≤4*q-2)
        · refine ⟨2*q+1,by omega,(row_case_7 q _ _ (by omega) rfl).mpr (by omega),?_⟩
          intro f hf
          rw [row_case_7 q _ f (by omega) rfl] at hf
          exact hsub f ((full_row_one q f hq).mpr (by omega))
        · refine ⟨4*q-1,by omega,(row_case_12 q _ _ (by omega) (by omega)).mpr ?_,?_⟩
          · omega
          · intro f hf
            rw [row_case_12 q _ f (by omega) (by omega)] at hf
            rcases hf with hf | hf | hf | hf
            · simpa [hf] using hc.2.1
            · simpa [hf] using hc.2.2.1
            · exact hp f (by omega)
            · exact hsub f ((full_row_one q f hq).mpr (by omega))
    · have hiE := (full_row_two q e hq).mp hie
      by_cases heN : e=4*q-1
      · subst e; exact old_cover_last q hq hg hc he
      · refine ⟨2,by omega,(row_case_2 q _ _ (by omega) rfl).mpr (by omega),?_⟩
        intro f hf
        rw [row_case_2 q _ f (by omega) rfl] at hf
        by_cases hf4 : f=4
        · simpa [hf4] using hc.2.2.2
        · exact hsub f ((full_row_two q f hq).mpr (by omega))
    · have hiE := (full_row_four q e hq).mp hie
      by_cases he2 : e=2
      · refine ⟨2*q+2,by omega,(row_case_8 q _ _ (by omega) rfl).mpr (by omega),?_⟩
        intro f hf
        rw [row_case_8 q _ f (by omega) rfl] at hf
        by_cases hf4 : f=4
        · simpa [hf4] using hc.2.2.2
        · exact hsub f ((full_row_four q f hq).mpr (by omega))
      · refine ⟨4,by omega,(row_case_4 q _ _ (by omega) rfl).mpr (by omega),?_⟩
        intro f hf
        rw [row_case_4 q _ f (by omega) rfl] at hf
        by_cases hf1 : f=1
        · simpa [hf1] using hc.1
        · exact hsub f ((full_row_four q f hq).mpr (by omega))
    · have hiE := (LuRazSixRow.row_middle q e hq).mp hie
      by_cases hn : R (4*q-1)
      · by_cases heN : e=4*q
        · refine ⟨4*q+1,by omega,(row_case_14 q _ _ (by omega) rfl).mpr (by omega),?_⟩
          intro f hf
          rw [row_case_14 q _ f (by omega) rfl] at hf
          by_cases hfn : f=4*q-1
          · simpa [hfn] using hn
          · exact hsub f ((LuRazSixRow.row_middle q f hq).mpr (by omega))
        · refine ⟨2*q+2,by omega,(row_case_8 q _ _ (by omega) rfl).mpr (by omega),?_⟩
          intro f hf
          rw [row_case_8 q _ f (by omega) rfl] at hf
          by_cases hfn : f=4*q-1
          · simpa [hfn] using hn
          · exact hsub f ((LuRazSixRow.row_middle q f hq).mpr (by omega))
      · have hp := full_no_last_prefix q hq hg hc.2.2.1 hn
        by_cases heN : e=4*q
        · refine ⟨4*q-1,by omega,(row_case_12 q _ _ (by omega) (by omega)).mpr ?_,?_⟩
          · omega
          · intro f hf
            rw [row_case_12 q _ f (by omega) (by omega)] at hf
            rcases hf with hf | hf | hf | hf
            · simpa [hf] using hc.2.1
            · simpa [hf] using hc.2.2.1
            · exact hp f (by omega)
            · exact hsub f ((LuRazSixRow.row_middle q f hq).mpr (by omega))
        · refine ⟨2*q+1,by omega,(row_case_7 q _ _ (by omega) rfl).mpr (by omega),?_⟩
          intro f hf
          rw [row_case_7 q _ f (by omega) rfl] at hf
          by_cases hfm : f=2*q+2
          · exact hp f (by omega)
          · exact hsub f ((LuRazSixRow.row_middle q f hq).mpr (by omega))
    · have hiE := (LuRazSixRow.row_last q e hq).mp hie
      have hp : ∀ f, (5≤f ∧ f≤2*q+2) → R f := fun f hf =>
        hsub f ((LuRazSixRow.row_last q f hq).mpr (by omega))
      by_cases he3 : e=3
      · subst e; exact old_cover_last_source_three q hq hg hc hp
      · refine ⟨3,by omega,(row_case_3 q _ _ (by omega) rfl).mpr (by omega),?_⟩
        intro f hf
        rw [row_case_3 q _ f (by omega) rfl] at hf
        by_cases hf1 : f=1
        · simpa [hf1] using hc.1
        · by_cases hf4 : f=4
          · simpa [hf4] using hc.2.2.2
          · exact hp f (by omega)
    · have hiE := (LuRazSixRow.row_n q e hq).mp hie
      by_cases heN : e=4*q-1
      · subst e; exact old_cover_last q hq hg hc he
      · by_cases hm : R (2*q+2)
        · refine ⟨4*q,by omega,(row_case_13 q _ _ (by omega) rfl).mpr (by omega),?_⟩
          intro f hf
          rw [row_case_13 q _ f (by omega) rfl] at hf
          by_cases hfm : f=2*q+2
          · simpa [hfm] using hm
          · exact hsub f ((LuRazSixRow.row_n q f hq).mpr (by omega))
        · have hmid := full_no_middle_source q hq hg hc.2.2.2 hm
          by_cases her : e=3*q+1
          · refine ⟨4,by omega,(row_case_4 q _ _ (by omega) rfl).mpr (by omega),?_⟩
            intro f hf
            rw [row_case_4 q _ f (by omega) rfl] at hf
            by_cases hf1 : f=1
            · simpa [hf1] using hc.1
            · by_cases hf3 : f=3
              · simpa [hf3] using hc.2.2.1
              · by_cases hfn : f=4*q-1
                · exact hsub f ((LuRazSixRow.row_n q f hq).mpr (by omega))
                · exact hmid f ((LuRazSixRow.row_middle q f hq).mpr (by omega))
          · refine ⟨4*q-1,by omega,(row_case_12 q _ _ (by omega) (by omega)).mpr ?_,?_⟩
            · omega
            · intro f hf
              rw [row_case_12 q _ f (by omega) (by omega)] at hf
              rcases hf with hf | hf | hf | hf
              · simpa [hf] using hc.2.1
              · simpa [hf] using hc.2.2.1
              · exact hsub f ((LuRazSixRow.row_n q f hq).mpr (by omega))
              · exact hmid f ((LuRazSixRow.row_middle q f hq).mpr (by omega))
  · exact ⟨i,hi,(full_unchanged q i e hs).mp hie,
      fun f hf => hsub f ((full_unchanged q i f hs).mpr hf)⟩

theorem full_generated_old (q : Nat) (hq : 4≤q) {R : Nat → Prop}
    (hg : Generated q R) (hc : CoreFull R) : LuRazClosure.Generated q R := by
  apply LuRazThreeRow.old_of_local_covers q R 1 hc.1
  intro e he
  obtain ⟨i,hi,hie,hsub⟩ := full_old_point q hq hg hc he
  exact ⟨Row q i,LuRazClosure.generated_row q i hi,hie,hsub⟩

end LuRazSixRowClosure
