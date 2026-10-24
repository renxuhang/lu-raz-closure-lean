import SixRowSmallDifferenceAt
import SixRowNeutral

namespace LuRazSixRowClosure
open LuRazClosure Difference
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

noncomputable def differenceCore (R : Nat → Prop) : Nat := by
  classical
  exact (if R 1 then 1 else 0) + (if R 2 then 2 else 0) +
    (if R 3 then 4 else 0) + (if R 4 then 8 else 0)

theorem difference_core_le (R : Nat → Prop) : differenceCore R≤15 := by
  classical
  by_cases h1 : R 1 <;> by_cases h2 : R 2 <;> by_cases h3 : R 3 <;> by_cases h4 : R 4 <;>
    simp [differenceCore,h1,h2,h3,h4]

theorem difference_core_mask (R : Nat → Prop) : CoreMask (differenceCore R) R := by
  classical
  by_cases h1 : R 1 <;> by_cases h2 : R 2 <;> by_cases h3 : R 3 <;> by_cases h4 : R 4 <;>
    simp [differenceCore,CoreMask,h1,h2,h3,h4]

theorem global_removed_core_le (z : RemovedForm) : z.core≤15 := by
  cases z <;> simp [RemovedForm.core]

theorem global_added_core_le (z : AddedForm) : z.core≤15 := by
  cases z <;> simp [AddedForm.core]

theorem removed_iff_at_core (q : Nat) (hq : 4≤q) (k : Nat) (hk : k≤15)
    (R : Nat → Prop) (hc : CoreMask k R) : Removed q R ↔ RemovedAt q k R := by
  constructor
  · rintro ⟨z,hz,he⟩
    have hm := (core_mask_congr z.core (z.eval q) R he).mp (z.core_mask q hq hz)
    have heq := core_mask_unique z.core k (global_removed_core_le z) hk R hm hc
    exact ⟨z,hz,heq,he⟩
  · rintro ⟨z,hz,_,he⟩
    exact ⟨z,hz,he⟩

theorem added_iff_at_core (q : Nat) (hq : 4≤q) (k : Nat) (hk : k≤15)
    (R : Nat → Prop) (hc : CoreMask k R) : Added q R ↔ AddedAt q k R := by
  constructor
  · rintro ⟨z,hz,he⟩
    have hm := (core_mask_congr z.core (z.eval q) R he).mp (z.core_mask q hq hz)
    have heq := core_mask_unique z.core k (global_added_core_le z) hk R hm hc
    exact ⟨z,hz,heq,he⟩
  · rintro ⟨z,hz,_,he⟩
    exact ⟨z,hz,he⟩

theorem neutral_removed_empty (q k : Nat) (R : Nat → Prop)
    (hk : k=0 ∨ k=1 ∨ k=9) : ¬RemovedAt q k R := by
  rintro ⟨z,hz,hzc,he⟩
  rcases hk with rfl | rfl | rfl
  all_goals cases z <;> simp [RemovedForm.core] at hzc

theorem neutral_added_empty (q k : Nat) (R : Nat → Prop)
    (hk : k=0 ∨ k=1 ∨ k=9) : ¬AddedAt q k R := by
  rintro ⟨z,hz,hzc,he⟩
  rcases hk with rfl | rfl | rfl
  all_goals cases z <;> simp [AddedForm.core] at hzc

theorem neutral_core_unchanged (q : Nat) (hq : 4≤q) (k : Nat) (R : Nat → Prop)
    (hk : k=0 ∨ k=1 ∨ k=9) (hc : CoreMask k R) :
    Generated q R ↔ LuRazThreeRow.Generated q R := by
  have h2 : ¬R 2 := by
    rcases hk with rfl | rfl | rfl <;> simpa [CoreMask] using hc.2.1
  have h3 : ¬R 3 := by
    rcases hk with rfl | rfl | rfl <;> simpa [CoreMask] using hc.2.2.1
  exact neutral_generated_iff q hq R h2 h3

theorem neutral_core_removed_at (q : Nat) (hq : 4≤q) (k : Nat) (R : Nat → Prop)
    (hk : k=0 ∨ k=1 ∨ k=9) (hc : CoreMask k R) :
    (LuRazThreeRow.Generated q R ∧ ¬Generated q R) ↔ RemovedAt q k R := by
  constructor
  · exact fun h => False.elim (h.2 ((neutral_core_unchanged q hq k R hk hc).mpr h.1))
  · exact fun h => False.elim (neutral_removed_empty q k R hk h)

theorem neutral_core_added_at (q : Nat) (hq : 4≤q) (k : Nat) (R : Nat → Prop)
    (hk : k=0 ∨ k=1 ∨ k=9) (hc : CoreMask k R) :
    (Generated q R ∧ ¬LuRazThreeRow.Generated q R) ↔ AddedAt q k R := by
  constructor
  · exact fun h => False.elim (h.2 ((neutral_core_unchanged q hq k R hk hc).mp h.1))
  · exact fun h => False.elim (neutral_added_empty q k R hk h)

end LuRazSixRowClosure
