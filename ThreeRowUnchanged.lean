import ThreeRowGenerated
import ThreeRowCore12
import LuRazSmallResults

namespace LuRazThreeRow
open LuRazClosure LuRazParametric
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

theorem special_old_three (q i : Nat) (hq : 4≤q) (hi : Special q i) : Row q i 3 := by
  rcases hi with rfl | rfl | rfl
  · rw [row_case_2 q 2 3 (by omega) rfl]; omega
  · rw [row_case_4 q 4 3 (by omega) rfl]; omega
  · rw [row_case_12 q (4*q-1) 3 (by omega) (by omega)]; omega

theorem special_new_three (q i : Nat) (hq : 4≤q) (hi : Special q i) : VRow q i 3 :=
  (unchanged_column q i 3 (by unfold Special; omega)).mpr (special_old_three q i hq hi)

theorem no_three_unchanged (q : Nat) (hq : 4≤q) (R : Nat → Prop) (h3 : ¬R 3) :
    Generated q R ↔ LuRazClosure.Generated q R := by
  constructor
  · rintro ⟨l,hn,hv,hR⟩
    have hs : ∀ i∈l, ¬Special q i := by
      intro i hi h
      exact h3 ((hR 3).mp ⟨i,hi,special_new_three q i hq h⟩)
    refine ⟨l,hn,hv,?_⟩
    intro e
    rw [←hR e]
    constructor
    · rintro ⟨i,hi,hie⟩; exact ⟨i,hi,(unchanged_row q i e (hs i hi)).mpr hie⟩
    · rintro ⟨i,hi,hie⟩; exact ⟨i,hi,(unchanged_row q i e (hs i hi)).mp hie⟩
  · rintro ⟨l,hn,hv,hR⟩
    have hs : ∀ i∈l, ¬Special q i := by
      intro i hi h
      exact h3 ((hR 3).mp ⟨i,hi,special_old_three q i hq h⟩)
    refine ⟨l,hn,hv,?_⟩
    intro e
    rw [←hR e]
    constructor
    · rintro ⟨i,hi,hie⟩; exact ⟨i,hi,(unchanged_row q i e (hs i hi)).mp hie⟩
    · rintro ⟨i,hi,hie⟩; exact ⟨i,hi,(unchanged_row q i e (hs i hi)).mpr hie⟩

theorem no_one_two_four_unchanged (q : Nat) (hq : 4≤q) (R : Nat → Prop)
    (h1 : ¬R 1) (h2 : ¬R 2) (h4 : ¬R 4) :
    Generated q R ↔ LuRazClosure.Generated q R := by
  constructor
  · rintro ⟨l,hn,hv,hR⟩
    have hs : ∀ i∈l, ¬Special q i := by
      intro i hi h
      rcases h with rfl | rfl | rfl
      · exact h1 ((hR 1).mp ⟨2,hi,(row_two q 1 hq).mpr (by omega)⟩)
      · exact h1 ((hR 1).mp ⟨4,hi,(row_four q 1 hq).mpr (by omega)⟩)
      · exact h4 ((hR 4).mp ⟨4*q-1,hi,(row_last q 4 hq).mpr (by omega)⟩)
    refine ⟨l,hn,hv,?_⟩
    intro e
    rw [←hR e]
    constructor
    · rintro ⟨i,hi,hie⟩; exact ⟨i,hi,(unchanged_row q i e (hs i hi)).mpr hie⟩
    · rintro ⟨i,hi,hie⟩; exact ⟨i,hi,(unchanged_row q i e (hs i hi)).mp hie⟩
  · rintro ⟨l,hn,hv,hR⟩
    have hs : ∀ i∈l, ¬Special q i := by
      intro i hi h
      rcases h with rfl | rfl | rfl
      · apply h1; apply (hR 1).mp
        exact ⟨2,hi,(row_case_2 q 2 1 (by omega) rfl).mpr (by omega)⟩
      · apply h1; apply (hR 1).mp
        exact ⟨4,hi,(row_case_4 q 4 1 (by omega) rfl).mpr (by omega)⟩
      · apply h2; apply (hR 2).mp
        exact ⟨4*q-1,hi,(row_case_12 q (4*q-1) 2 (by omega) (by omega)).mpr (by omega)⟩
    refine ⟨l,hn,hv,?_⟩
    intro e
    rw [←hR e]
    constructor
    · rintro ⟨i,hi,hie⟩; exact ⟨i,hi,(unchanged_row q i e (hs i hi)).mp hie⟩
    · rintro ⟨i,hi,hie⟩; exact ⟨i,hi,(unchanged_row q i e (hs i hi)).mpr hie⟩

end LuRazThreeRow
