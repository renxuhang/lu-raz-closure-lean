import ThreeRowResults

namespace LuRazFourRow
open LuRazParametric RazReimerPredicates
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- A second balanced three-cycle, performed on the previously verified variant. -/
def Removed (q i e : Nat) : Prop :=
  (i=1 ∧ e=4*q-1) ∨ (i=4 ∧ e=1) ∨ (i=4*q-1 ∧ e=4)

def Added (q i e : Nat) : Prop :=
  (i=1 ∧ e=4) ∨ (i=4 ∧ e=4*q-1) ∨ (i=4*q-1 ∧ e=1)

def WRow (q i e : Nat) : Prop := (LuRazThreeRow.VRow q i e ∧ ¬Removed q i e) ∨ Added q i e

def W (q : Nat) (i : Fin (4*q+3)) (e : Fin (4*q)) : Prop := WRow q i.val (e.val+1)

def Special (q i : Nat) : Prop := i=1 ∨ i=4 ∨ i=4*q-1

theorem unchanged_row (q i e : Nat) (hi : ¬Special q i) :
    WRow q i e ↔ LuRazThreeRow.VRow q i e := by
  have hr : ¬Removed q i e := by unfold Removed Special at *; omega
  have ha : ¬Added q i e := by unfold Added Special at *; omega
  simp [WRow,hr,ha]

theorem unchanged_column (q i e : Nat) (he : ¬Special q e) :
    WRow q i e ↔ LuRazThreeRow.VRow q i e := by
  have hr : ¬Removed q i e := by unfold Removed Special at *; omega
  have ha : ¬Added q i e := by unfold Added Special at *; omega
  simp [WRow,hr,ha]

theorem row_one (q e : Nat) (hq : 4≤q) :
    WRow q 1 e ↔ e=2 ∨ e=4 ∨ (2*q+1≤e ∧ e≤4*q-2) ∨ e=4*q := by
  unfold WRow Removed Added
  rw [LuRazThreeRow.unchanged_row q 1 e (by unfold LuRazThreeRow.Special; omega),
    row_case_1 q 1 e (by omega) rfl]
  omega

theorem row_two (q e : Nat) (hq : 4≤q) :
    WRow q 2 e ↔ e=1 ∨ e=3 ∨ (5≤e ∧ e≤2*q) ∨ e=4*q-1 ∨ e=4*q := by
  rw [unchanged_row q 2 e (by unfold Special; omega)]
  exact LuRazThreeRow.row_two q e hq

theorem row_four (q e : Nat) (hq : 4≤q) :
    WRow q 4 e ↔ e=2 ∨ e=3 ∨ (2*q+3≤e ∧ e≤4*q) := by
  unfold WRow Removed Added
  rw [LuRazThreeRow.row_four q e hq]
  omega

theorem row_last (q e : Nat) (hq : 4≤q) :
    WRow q (4*q-1) e ↔ e=1 ∨ e=3 ∨ (5≤e ∧ e≤2*q+1) ∨ e=4*q := by
  unfold WRow Removed Added
  rw [LuRazThreeRow.row_last q e hq]
  omega

theorem removed_present (q i e : Nat) (hq : 4≤q) (h : Removed q i e) :
    LuRazThreeRow.VRow q i e := by
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · rw [LuRazThreeRow.unchanged_row q 1 (4*q-1) (by unfold LuRazThreeRow.Special; omega),
      row_case_1 q 1 (4*q-1) (by omega) rfl]
    omega
  · rw [LuRazThreeRow.row_four q 1 hq]; omega
  · rw [LuRazThreeRow.row_last q 4 hq]; omega

theorem added_absent (q i e : Nat) (hq : 4≤q) (h : Added q i e) :
    ¬LuRazThreeRow.VRow q i e := by
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · rw [LuRazThreeRow.unchanged_row q 1 4 (by unfold LuRazThreeRow.Special; omega),
      row_case_1 q 1 4 (by omega) rfl]
    omega
  · rw [LuRazThreeRow.row_four q (4*q-1) hq]; omega
  · rw [LuRazThreeRow.row_last q 1 hq]; omega

theorem included_filter (q : Nat) (hq : 4≤q) : ∀ i, Included (W q i) (F q i) := by
  intro i e he
  rcases he with h | h
  · exact LuRazThreeRow.included_filter q hq i e h.1
  · change FilterRow q i.val (e.val+1)
    unfold Added at h
    unfold FilterRow
    have := i.isLt
    rcases h with h | h | h <;> omega

end LuRazFourRow
