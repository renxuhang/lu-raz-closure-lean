import SixRowGlobalCore
import SixRowMixedDifference
import SixRowLargeDifferenceAt
import SixRow10DifferenceEnumeration
import SixRowEmptyDifferenceAt

namespace LuRazSixRowClosure
open LuRazClosure Difference
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

theorem all_core_removed_at (q : Nat) (hq : 4≤q) (k : Nat) (hk : k≤15)
    (R : Nat → Prop) (hc : CoreMask k R) :
    (LuRazThreeRow.Generated q R ∧ ¬Generated q R) ↔ RemovedAt q k R := by
  have hh : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨ k=7 ∨
      k=8 ∨ k=9 ∨ k=10 ∨ k=11 ∨ k=12 ∨ k=13 ∨ k=14 ∨ k=15 := by omega
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact neutral_core_removed_at q hq 0 R (Or.inl rfl) hc
  · exact neutral_core_removed_at q hq 1 R (Or.inr (Or.inl rfl)) hc
  · exact core2_removed_at q hq R hc
  · exact core3_removed_at q hq R hc
  · exact core4_removed_at q hq R hc
  · exact core5_removed_at q hq R hc
  · exact core6_removed_at q hq R hc
  · exact core7_removed_at q hq R hc
  · exact core8_removed_at q hq R hc
  · exact neutral_core_removed_at q hq 9 R (Or.inr (Or.inr rfl)) hc
  · exact core10_removed_at q hq R hc
  · exact core11_removed_at q hq R hc
  · exact core12_removed_at q hq R hc
  · exact core13_removed_at q hq R hc
  · exact core14_removed_at q hq R hc
  · exact core15_removed_at q hq R hc

theorem all_core_added_at (q : Nat) (hq : 4≤q) (k : Nat) (hk : k≤15)
    (R : Nat → Prop) (hc : CoreMask k R) :
    (Generated q R ∧ ¬LuRazThreeRow.Generated q R) ↔ AddedAt q k R := by
  have hh : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨ k=7 ∨
      k=8 ∨ k=9 ∨ k=10 ∨ k=11 ∨ k=12 ∨ k=13 ∨ k=14 ∨ k=15 := by omega
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact neutral_core_added_at q hq 0 R (Or.inl rfl) hc
  · exact neutral_core_added_at q hq 1 R (Or.inr (Or.inl rfl)) hc
  · exact core2_added_at q hq R hc
  · exact core3_added_at q hq R hc
  · exact core4_added_at q hq R hc
  · exact core5_added_at q hq R hc
  · exact core6_added_at q hq R hc
  · exact core7_added_at q hq R hc
  · exact core8_added_at q hq R hc
  · exact neutral_core_added_at q hq 9 R (Or.inr (Or.inr rfl)) hc
  · exact core10_added_at q hq R hc
  · exact core11_added_at q hq R hc
  · exact core12_added_at q hq R hc
  · exact core13_added_at q hq R hc
  · exact core14_added_at q hq R hc
  · exact core15_added_at q hq R hc

/-- The 27 explicit removed groups are exhaustive for the actual set difference. -/
theorem removed_exact (q : Nat) (hq : 4≤q) (R : Nat → Prop) :
    (LuRazThreeRow.Generated q R ∧ ¬Generated q R) ↔ Removed q R := by
  have hc := difference_core_mask R
  have hk := difference_core_le R
  exact (all_core_removed_at q hq (differenceCore R) hk R hc).trans
    (removed_iff_at_core q hq (differenceCore R) hk R hc).symm

/-- The 16 explicit added groups are exhaustive for the actual set difference. -/
theorem added_exact (q : Nat) (hq : 4≤q) (R : Nat → Prop) :
    (Generated q R ∧ ¬LuRazThreeRow.Generated q R) ↔ Added q R := by
  have hc := difference_core_mask R
  have hk := difference_core_le R
  exact (all_core_added_at q hq (differenceCore R) hk R hc).trans
    (added_iff_at_core q hq (differenceCore R) hk R hc).symm

/-- Exact closure replacement, with ordinary predicate sets and no numerical oracle. -/
theorem closure_delta_exact (q : Nat) (hq : 4≤q) (R : Nat → Prop) :
    Generated q R ↔ (LuRazThreeRow.Generated q R ∧ ¬Removed q R) ∨ Added q R := by
  classical
  constructor
  · intro hg
    by_cases ho : LuRazThreeRow.Generated q R
    · refine Or.inl ⟨ho,?_⟩
      exact fun hr => ((removed_exact q hq R).mpr hr).2 hg
    · exact Or.inr ((added_exact q hq R).mp ⟨hg,ho⟩)
  · rintro (h | h)
    · apply Classical.byContradiction
      intro hn
      exact h.2 ((removed_exact q hq R).mp ⟨h.1,hn⟩)
    · exact ((added_exact q hq R).mpr h).1

theorem removed_added_disjoint (q : Nat) (hq : 4≤q) (R : Nat → Prop)
    (hr : Removed q R) : ¬Added q R := by
  intro ha
  exact ((removed_exact q hq R).mpr hr).2 ((added_exact q hq R).mpr ha).1

end LuRazSixRowClosure
