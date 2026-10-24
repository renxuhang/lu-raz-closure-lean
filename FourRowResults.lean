import FourRowMargins

namespace LuRazFourRow
open LuRazParametric RazReimerPredicates
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

theorem nontrivial (q : Nat) (hq : 4 ≤ q) : Nontrivial (W q) := by
  refine ⟨0,(⟨0,by omega⟩ : Fin (4*q)),?_⟩
  change WRow q 0 1
  rw [unchanged_row q 0 1 (by unfold Special; omega),
    LuRazThreeRow.unchanged_row q 0 1 (by unfold LuRazThreeRow.Special; omega)]
  exact (row_case_0 q 0 1 (by omega) rfl).mpr (by omega)

theorem one_last_implies_three (q i : Nat) (hq : 4≤q)
    (h1 : WRow q i 1) (hn : WRow q i (4*q)) : WRow q i 3 := by
  by_cases hs : Special q i
  · rcases hs with rfl | rfl | rfl
    · rw [row_one q 1 hq] at h1
      omega
    · rw [row_four q 1 hq] at h1
      omega
    · exact (row_last q 3 hq).mpr (by omega)
  · rw [unchanged_row q i 1 hs] at h1
    rw [unchanged_row q i (4*q) hs] at hn
    rw [unchanged_row q i 3 hs]
    exact LuRazThreeRow.one_last_implies_three q i hq h1 hn

theorem not_union_closed (q : Nat) (hq : 4 ≤ q) : ¬UnionClosed (W q) := by
  intro hu
  let a : Fin (4*q+3) := ⟨4*q+1,by omega⟩
  let b : Fin (4*q+3) := ⟨4*q+2,by omega⟩
  let E1 : Fin (4*q) := ⟨0,by omega⟩
  let E3 : Fin (4*q) := ⟨2,by omega⟩
  let EN : Fin (4*q) := ⟨4*q-1,by omega⟩
  have hn : 4*q-1+1 = 4*q := by omega
  obtain ⟨k,hk⟩ := hu a b
  have hb1 : W q b E1 := by
    change WRow q (4*q+2) 1
    rw [unchanged_row q (4*q+2) 1 (by unfold Special; omega),
      LuRazThreeRow.unchanged_row q (4*q+2) 1 (by unfold LuRazThreeRow.Special; omega)]
    exact (row_case_15 q (4*q+2) 1 (by omega) rfl).mpr (by omega)
  have haN : W q a EN := by
    change WRow q (4*q+1) (4*q-1+1)
    rw [hn,unchanged_row q (4*q+1) (4*q) (by unfold Special; omega),
      LuRazThreeRow.unchanged_row q (4*q+1) (4*q) (by unfold LuRazThreeRow.Special; omega)]
    exact (row_case_14 q (4*q+1) (4*q) (by omega) rfl).mpr (by omega)
  have hk1 : WRow q k.val 1 := (hk E1).mpr (Or.inr hb1)
  have hkN := (hk EN).mpr (Or.inl haN)
  change WRow q k.val (4*q-1+1) at hkN
  rw [hn] at hkN
  have hk3 : W q k E3 := one_last_implies_three q k.val hq hk1 hkN
  have ha3 : ¬W q a E3 := by
    change ¬WRow q (4*q+1) 3
    rw [unchanged_row q (4*q+1) 3 (by unfold Special; omega),
      LuRazThreeRow.unchanged_row q (4*q+1) 3 (by unfold LuRazThreeRow.Special; omega),
      row_case_14 q (4*q+1) 3 (by omega) rfl]
    omega
  have hb3 : ¬W q b E3 := by
    change ¬WRow q (4*q+2) 3
    rw [unchanged_row q (4*q+2) 3 (by unfold Special; omega),
      LuRazThreeRow.unchanged_row q (4*q+2) 3 (by unfold LuRazThreeRow.Special; omega),
      row_case_15 q (4*q+2) 3 (by omega) rfl]
    omega
  exact ((hk E3).mp hk3).elim ha3 hb3

/-- The four-row variant satisfies the construction requirements for every q >= 4. -/
theorem completed_construction (q : Nat) (hq : 4 ≤ q) :
    ReimerCondition (W q) ∧ Nontrivial (W q) ∧
    (∀ e, frequency (W q) e = 2*q+1) ∧
    ¬HasAbundantElement (W q) ∧ ¬UnionClosed (W q) ∧
    (∀ i, q-1 ≤ wSize q i) ∧ (∃ i, wSize q i = q-1) ∧
    (∀ i, wSize q i = setSize q i) ∧ Function.Injective (W q) :=
  ⟨reimer q hq,nontrivial q hq,uniform_frequency q hq,no_abundant q hq,
    not_union_closed q hq,min_lower q hq,⟨⟨4*q+1,by omega⟩,min_attained q hq⟩,
    size_unchanged q hq,injective q hq⟩

end LuRazFourRow
