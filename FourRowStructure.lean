import FourRowDefs

namespace LuRazFourRow
open LuRazParametric RazReimerPredicates
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

theorem coatom_separated (q i j : Nat) (hq : 4 ≤ q)
    (hi : 1 ≤ i ∧ i ≤ 4*q) (hj : 1 ≤ j ∧ j ≤ 4*q) (hne : i ≠ j) :
    WRow q i j ∨ WRow q j i := by
  by_cases hsi : Special q i
  · by_cases hsj : Special q j
    · rcases hsi with rfl | rfl | rfl <;>
        rcases hsj with rfl | rfl | rfl
      all_goals try omega
      all_goals first
        | exact Or.inl ((row_one q _ hq).mpr (by omega))
        | exact Or.inr ((row_one q _ hq).mpr (by omega))
        | exact Or.inl ((row_four q _ hq).mpr (by omega))
        | exact Or.inr ((row_four q _ hq).mpr (by omega))
        | exact Or.inl ((row_last q _ hq).mpr (by omega))
        | exact Or.inr ((row_last q _ hq).mpr (by omega))
    · rw [unchanged_column q i j hsj, unchanged_row q j i hsj]
      exact LuRazThreeRow.coatom_separated q i j hq hi hj hne
  · by_cases hsj : Special q j
    · rw [unchanged_row q i j hsi, unchanged_column q j i hsi]
      exact LuRazThreeRow.coatom_separated q i j hq hi hj hne
    · rw [unchanged_row q i j hsi, unchanged_row q j i hsj]
      exact LuRazThreeRow.coatom_separated q i j hq hi hj hne

theorem first_hole (q i : Nat) (hq : 4 ≤ q) (hi : 1 ≤ i ∧ i ≤ 4*q) :
    WRow q i 1 ∨ WRow q i 2 ∨ WRow q (4*q+1) i := by
  by_cases hs : Special q i
  · rcases hs with rfl | rfl | rfl
    · exact Or.inr (Or.inl ((row_one q _ hq).mpr (by omega)))
    · exact Or.inr (Or.inl ((row_four q _ hq).mpr (by omega)))
    · exact Or.inl ((row_last q _ hq).mpr (by omega))
  · rw [unchanged_row q i 1 hs, unchanged_row q i 2 hs,
      unchanged_row q (4*q+1) i (by unfold Special; omega)]
    exact LuRazThreeRow.first_hole q i hq hi

theorem second_hole (q i : Nat) (hq : 4 ≤ q) (hi : 1 ≤ i ∧ i ≤ 4*q) :
    WRow q i 3 ∨ WRow q i 4 ∨ WRow q (4*q+2) i := by
  by_cases hs : Special q i
  · rcases hs with rfl | rfl | rfl
    · exact Or.inr (Or.inl ((row_one q _ hq).mpr (by omega)))
    · exact Or.inl ((row_four q _ hq).mpr (by omega))
    · exact Or.inl ((row_last q _ hq).mpr (by omega))
  · rw [unchanged_row q i 3 hs, unchanged_row q i 4 hs,
      unchanged_row q (4*q+2) i (by unfold Special; omega)]
    exact LuRazThreeRow.second_hole q i hq hi

def Separated (q i j : Nat) : Prop :=
  ∃ e, 1 ≤ e ∧ e ≤ 4*q ∧
    ((WRow q i e ∧ ¬FilterRow q j e) ∨ (WRow q j e ∧ ¬FilterRow q i e))

theorem Separated.symm {q i j : Nat} (h : Separated q i j) : Separated q j i := by
  obtain ⟨e,he1,he2,h⟩ := h
  exact ⟨e,he1,he2,h.symm⟩

theorem unchanged_separation (q i j : Nat) (hi : ¬Special q i) (hj : ¬Special q j)
    (h : LuRazThreeRow.Separated q i j) : Separated q i j := by
  obtain ⟨e,he1,he2,h⟩ := h
  exact ⟨e,he1,he2,by rwa [unchanged_row q i e hi, unchanged_row q j e hj]⟩

theorem zero_sep (q j : Nat) (hq : 4 ≤ q) (hj : 1 ≤ j ∧ j ≤ 4*q) :
    Separated q 0 j := by
  refine ⟨j,hj.1,hj.2,Or.inl ⟨?_,?_⟩⟩
  · rw [unchanged_row q 0 j (by unfold Special; omega),
      LuRazThreeRow.unchanged_row q 0 j (by unfold LuRazThreeRow.Special; omega)]
    exact (row_case_0 q 0 j (by omega) rfl).mpr hj
  · unfold FilterRow; omega

theorem coatom_sep (q i j : Nat) (hq : 4 ≤ q)
    (hi : 1 ≤ i ∧ i ≤ 4*q) (hj : 1 ≤ j ∧ j ≤ 4*q) (hne : i ≠ j) :
    Separated q i j := by
  rcases coatom_separated q i j hq hi hj hne with h | h
  · exact ⟨j,hj.1,hj.2,Or.inl ⟨h,by unfold FilterRow; omega⟩⟩
  · exact ⟨i,hi.1,hi.2,Or.inr ⟨h,by unfold FilterRow; omega⟩⟩

theorem first_sep (q i : Nat) (hq : 4 ≤ q) (hi : 1 ≤ i ∧ i ≤ 4*q) :
    Separated q i (4*q+1) := by
  rcases first_hole q i hq hi with h | h | h
  · exact ⟨1,by omega,by omega,Or.inl ⟨h,by unfold FilterRow; omega⟩⟩
  · exact ⟨2,by omega,by omega,Or.inl ⟨h,by unfold FilterRow; omega⟩⟩
  · exact ⟨i,hi.1,hi.2,Or.inr ⟨h,by unfold FilterRow; omega⟩⟩

theorem second_sep (q i : Nat) (hq : 4 ≤ q) (hi : 1 ≤ i ∧ i ≤ 4*q) :
    Separated q i (4*q+2) := by
  rcases second_hole q i hq hi with h | h | h
  · exact ⟨3,by omega,by omega,Or.inl ⟨h,by unfold FilterRow; omega⟩⟩
  · exact ⟨4,by omega,by omega,Or.inl ⟨h,by unfold FilterRow; omega⟩⟩
  · exact ⟨i,hi.1,hi.2,Or.inr ⟨h,by unfold FilterRow; omega⟩⟩

theorem separated (q i j : Nat) (hq : 4 ≤ q)
    (hi : i < 4*q+3) (hj : j < 4*q+3) (hne : i ≠ j) : Separated q i j := by
  rcases main_partition q i hi with rfl | hiC | rfl | rfl
  · rcases main_partition q j hj with rfl | hjC | rfl | rfl
    · omega
    · exact zero_sep q j hq hjC
    · exact unchanged_separation q _ _ (by unfold Special; omega)
        (by unfold Special; omega) (LuRazThreeRow.separated q 0 (4*q+1) hq (by omega) (by omega) (by omega))
    · exact unchanged_separation q _ _ (by unfold Special; omega)
        (by unfold Special; omega) (LuRazThreeRow.separated q 0 (4*q+2) hq (by omega) (by omega) (by omega))
  · rcases main_partition q j hj with rfl | hjC | rfl | rfl
    · exact (zero_sep q i hq hiC).symm
    · exact coatom_sep q i j hq hiC hjC hne
    · exact first_sep q i hq hiC
    · exact second_sep q i hq hiC
  · rcases main_partition q j hj with rfl | hjC | rfl | rfl
    · exact (unchanged_separation q _ _ (by unfold Special; omega)
        (by unfold Special; omega) (LuRazThreeRow.separated q 0 (4*q+1) hq (by omega) (by omega) (by omega))).symm
    · exact (first_sep q j hq hjC).symm
    · omega
    · exact unchanged_separation q _ _ (by unfold Special; omega)
        (by unfold Special; omega) (LuRazThreeRow.separated q (4*q+1) (4*q+2) hq (by omega) (by omega) (by omega))
  · rcases main_partition q j hj with rfl | hjC | rfl | rfl
    · exact (unchanged_separation q _ _ (by unfold Special; omega)
        (by unfold Special; omega) (LuRazThreeRow.separated q 0 (4*q+2) hq (by omega) (by omega) (by omega))).symm
    · exact (second_sep q j hq hjC).symm
    · exact (unchanged_separation q _ _ (by unfold Special; omega)
        (by unfold Special; omega) (LuRazThreeRow.separated q (4*q+1) (4*q+2) hq (by omega) (by omega) (by omega))).symm
    · omega

theorem disjoint_intervals (q : Nat) (hq : 4 ≤ q) : IntervalsDisjoint (W q) (F q) := by
  intro i j hne T hiS hiF hjS hjF
  obtain ⟨e,hlo,hhi,hsep⟩ := separated q i.val j.val hq i.isLt j.isLt
    (fun heq => hne (Fin.ext heq))
  let E : Fin (4*q) := ⟨e-1,by omega⟩
  have hr : e-1+1 = e := by omega
  rcases hsep with h | h
  · have hs : W q i E := by change WRow q i.val (e-1+1); simpa only [hr] using h.1
    have hn : ¬ F q j E := by change ¬FilterRow q j.val (e-1+1); simpa only [hr] using h.2
    exact hn (hjF E (hiS E hs))
  · have hs : W q j E := by change WRow q j.val (e-1+1); simpa only [hr] using h.1
    have hn : ¬ F q i E := by change ¬FilterRow q i.val (e-1+1); simpa only [hr] using h.2
    exact hn (hiF E (hjS E hs))

theorem injective (q : Nat) (hq : 4 ≤ q) : Function.Injective (W q) := by
  classical
  intro i j heq
  apply Classical.byContradiction
  intro hne
  apply disjoint_intervals q hq i j hne (W q i)
  · exact fun _ h => h
  · exact included_filter q hq i
  · rw [heq]; exact fun _ h => h
  · rw [heq]; exact included_filter q hq j

theorem reimer (q : Nat) (hq : 4 ≤ q) : ReimerCondition (W q) :=
  ⟨F q,injective q hq,F_injective q (by omega),F_upward q (by omega),
    included_filter q hq,disjoint_intervals q hq⟩

end LuRazFourRow
