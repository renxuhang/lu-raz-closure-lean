import ThreeRowMargins

namespace LuRazThreeRow
open LuRazParametric RazReimerPredicates
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

theorem nontrivial (q : Nat) (hq : 4 ≤ q) : Nontrivial (V q) := by
  refine ⟨0,(⟨0,by omega⟩ : Fin (4*q)),?_⟩
  change VRow q 0 1
  rw [unchanged_row q 0 1 (by unfold Special; omega)]
  exact (row_case_0 q 0 1 (by omega) rfl).mpr (by omega)

theorem one_last_implies_three (q i : Nat) (hq : 4 ≤ q)
    (h1 : VRow q i 1) (hn : VRow q i (4*q)) : VRow q i 3 := by
  rw [unchanged_column q i 1 (by unfold Special; omega)] at h1
  rw [unchanged_column q i (4*q) (by unfold Special; omega)] at hn
  rw [unchanged_column q i 3 (by unfold Special; omega)]
  exact row_one_last_implies_three q i (by omega) h1 hn

theorem not_union_closed (q : Nat) (hq : 4 ≤ q) : ¬UnionClosed (V q) := by
  intro hu
  let a : Fin (4*q+3) := ⟨4*q+1,by omega⟩
  let b : Fin (4*q+3) := ⟨4*q+2,by omega⟩
  let E1 : Fin (4*q) := ⟨0,by omega⟩
  let E3 : Fin (4*q) := ⟨2,by omega⟩
  let EN : Fin (4*q) := ⟨4*q-1,by omega⟩
  have hn : 4*q-1+1 = 4*q := by omega
  obtain ⟨k,hk⟩ := hu a b
  have hb1 : V q b E1 := by
    change VRow q (4*q+2) 1
    rw [unchanged_row q (4*q+2) 1 (by unfold Special; omega)]
    exact (row_case_15 q (4*q+2) 1 (by omega) rfl).mpr (by omega)
  have haN : V q a EN := by
    change VRow q (4*q+1) (4*q-1+1)
    rw [hn,unchanged_row q (4*q+1) (4*q) (by unfold Special; omega)]
    exact (row_case_14 q (4*q+1) (4*q) (by omega) rfl).mpr (by omega)
  have hk1 : VRow q k.val 1 := (hk E1).mpr (Or.inr hb1)
  have hkN := (hk EN).mpr (Or.inl haN)
  change VRow q k.val (4*q-1+1) at hkN
  rw [hn] at hkN
  have hk3 : V q k E3 := one_last_implies_three q k.val hq hk1 hkN
  have ha3 : ¬V q a E3 := by
    change ¬VRow q (4*q+1) 3
    rw [unchanged_row q (4*q+1) 3 (by unfold Special; omega),
      row_case_14 q (4*q+1) 3 (by omega) rfl]
    omega
  have hb3 : ¬V q b E3 := by
    change ¬VRow q (4*q+2) 3
    rw [unchanged_row q (4*q+2) 3 (by unfold Special; omega),
      row_case_15 q (4*q+2) 3 (by omega) rfl]
    omega
  exact ((hk E3).mp hk3).elim ha3 hb3

/-- The three-row variant satisfies the construction requirements for every q >= 4. -/
theorem completed_construction (q : Nat) (hq : 4 ≤ q) :
    ReimerCondition (V q) ∧ Nontrivial (V q) ∧
    (∀ e, frequency (V q) e = 2*q+1) ∧
    ¬HasAbundantElement (V q) ∧ ¬UnionClosed (V q) ∧
    (∀ i, q-1 ≤ vSize q i) ∧ (∃ i, vSize q i = q-1) ∧
    (∀ i, vSize q i = setSize q i) :=
  ⟨reimer q hq,nontrivial q hq,uniform_frequency q hq,no_abundant q hq,
    not_union_closed q hq,min_lower q hq,⟨⟨4*q+1,by omega⟩,min_attained q hq⟩,
    size_unchanged q hq⟩

end LuRazThreeRow
