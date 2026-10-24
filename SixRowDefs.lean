import FourRowResults

namespace LuRazSixRow
open LuRazParametric RazReimerPredicates
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- The third balanced cycle, on labels 2q+2, 4q-1, and 4q. -/
def Removed (q i e : Nat) : Prop :=
  (i=2*q+2 ∧ e=4*q-1) ∨ (i=4*q-1 ∧ e=4*q) ∨ (i=4*q ∧ e=2*q+2)

def Added (q i e : Nat) : Prop :=
  (i=2*q+2 ∧ e=4*q) ∨ (i=4*q-1 ∧ e=2*q+2) ∨ (i=4*q ∧ e=4*q-1)

def BRow (q i e : Nat) : Prop := (LuRazFourRow.WRow q i e ∧ ¬Removed q i e) ∨ Added q i e

def B (q : Nat) (i : Fin (4*q+3)) (e : Fin (4*q)) : Prop := BRow q i.val (e.val+1)

def Special (q i : Nat) : Prop := i=2*q+2 ∨ i=4*q-1 ∨ i=4*q

theorem unchanged_row (q i e : Nat) (hi : ¬Special q i) :
    BRow q i e ↔ LuRazFourRow.WRow q i e := by
  have hr : ¬Removed q i e := by unfold Removed Special at *; omega
  have ha : ¬Added q i e := by unfold Added Special at *; omega
  simp [BRow,hr,ha]

theorem unchanged_column (q i e : Nat) (he : ¬Special q e) :
    BRow q i e ↔ LuRazFourRow.WRow q i e := by
  have hr : ¬Removed q i e := by unfold Removed Special at *; omega
  have ha : ¬Added q i e := by unfold Added Special at *; omega
  simp [BRow,hr,ha]

theorem base_middle (q e : Nat) (hq : 4≤q) :
    LuRazFourRow.WRow q (2*q+2) e ↔ e=2 ∨ e=4 ∨ (2*q+3≤e ∧ e≤4*q-1) := by
  rw [LuRazFourRow.unchanged_row q (2*q+2) e (by unfold LuRazFourRow.Special; omega),
    LuRazThreeRow.unchanged_row q (2*q+2) e (by unfold LuRazThreeRow.Special; omega),
    row_case_8 q (2*q+2) e (by omega) rfl]
  omega

theorem base_n (q e : Nat) (hq : 4≤q) :
    LuRazFourRow.WRow q (4*q) e ↔ e=3 ∨ (5≤e ∧ e≤2*q+2) ∨ e=3*q+1 := by
  rw [LuRazFourRow.unchanged_row q (4*q) e (by unfold LuRazFourRow.Special; omega),
    LuRazThreeRow.unchanged_row q (4*q) e (by unfold LuRazThreeRow.Special; omega)]
  exact row_case_13 q (4*q) e (by omega) rfl

theorem row_middle (q e : Nat) (hq : 4≤q) :
    BRow q (2*q+2) e ↔ e=2 ∨ e=4 ∨ (2*q+3≤e ∧ e≤4*q-2) ∨ e=4*q := by
  unfold BRow Removed Added
  rw [base_middle q e hq]
  omega

theorem row_last (q e : Nat) (hq : 4≤q) :
    BRow q (4*q-1) e ↔ e=1 ∨ e=3 ∨ (5≤e ∧ e≤2*q+2) := by
  unfold BRow Removed Added
  rw [LuRazFourRow.row_last q e hq]
  omega

theorem row_n (q e : Nat) (hq : 4≤q) :
    BRow q (4*q) e ↔ e=3 ∨ (5≤e ∧ e≤2*q+1) ∨ e=3*q+1 ∨ e=4*q-1 := by
  unfold BRow Removed Added
  rw [base_n q e hq]
  omega

theorem removed_present (q i e : Nat) (hq : 4≤q) (h : Removed q i e) :
    LuRazFourRow.WRow q i e := by
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · rw [base_middle q (4*q-1) hq]; omega
  · rw [LuRazFourRow.row_last q (4*q) hq]; omega
  · rw [base_n q (2*q+2) hq]; omega

theorem added_absent (q i e : Nat) (hq : 4≤q) (h : Added q i e) :
    ¬LuRazFourRow.WRow q i e := by
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · rw [base_middle q (4*q) hq]; omega
  · rw [LuRazFourRow.row_last q (2*q+2) hq]; omega
  · rw [base_n q (4*q-1) hq]; omega

theorem included_filter (q : Nat) (hq : 4≤q) : ∀ i, Included (B q i) (F q i) := by
  intro i e he
  rcases he with h | h
  · exact LuRazFourRow.included_filter q hq i e h.1
  · change FilterRow q i.val (e.val+1)
    unfold Added at h
    unfold FilterRow
    have := i.isLt
    rcases h with h | h | h <;> omega

end LuRazSixRow
