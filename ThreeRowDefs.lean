import LuRazStructure

namespace LuRazThreeRow
open LuRazParametric RazReimerPredicates

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

def Removed (q i e : Nat) : Prop :=
  (i = 2 ∧ e = 4) ∨ (i = 4 ∧ e = 4*q-1) ∨ (i = 4*q-1 ∧ e = 2)

def Added (q i e : Nat) : Prop :=
  (i = 2 ∧ e = 4*q-1) ∨ (i = 4 ∧ e = 2) ∨ (i = 4*q-1 ∧ e = 4)

def VRow (q i e : Nat) : Prop := (Row q i e ∧ ¬Removed q i e) ∨ Added q i e

def V (q : Nat) (i : Fin (4*q+3)) (e : Fin (4*q)) : Prop :=
  VRow q i.val (e.val+1)

def Special (q i : Nat) : Prop := i = 2 ∨ i = 4 ∨ i = 4*q-1

theorem unchanged_row (q i e : Nat) (hi : ¬Special q i) :
    VRow q i e ↔ Row q i e := by
  have hr : ¬Removed q i e := by unfold Removed Special at *; omega
  have ha : ¬Added q i e := by unfold Added Special at *; omega
  simp [VRow,hr,ha]

theorem unchanged_column (q i e : Nat) (he : ¬Special q e) :
    VRow q i e ↔ Row q i e := by
  have hr : ¬Removed q i e := by unfold Removed Special at *; omega
  have ha : ¬Added q i e := by unfold Added Special at *; omega
  simp [VRow,hr,ha]

theorem row_two (q e : Nat) (hq : 4 ≤ q) :
    VRow q 2 e ↔ e = 1 ∨ e = 3 ∨ (5 ≤ e ∧ e ≤ 2*q) ∨ e = 4*q-1 ∨ e = 4*q := by
  unfold VRow Removed Added
  rw [row_case_2 q 2 e (by omega) rfl]
  omega

theorem row_four (q e : Nat) (hq : 4 ≤ q) :
    VRow q 4 e ↔ e = 1 ∨ e = 2 ∨ e = 3 ∨
      (2*q+3 ≤ e ∧ e ≤ 4*q-2) ∨ e = 4*q := by
  unfold VRow Removed Added
  rw [row_case_4 q 4 e (by omega) rfl]
  omega

theorem row_last (q e : Nat) (hq : 4 ≤ q) :
    VRow q (4*q-1) e ↔ e = 3 ∨ (4 ≤ e ∧ e ≤ 2*q+1) ∨ e = 4*q := by
  unfold VRow Removed Added
  rw [row_case_12 q (4*q-1) e (by omega) (by omega)]
  omega

theorem removed_present (q i e : Nat) (hq : 4 ≤ q) (h : Removed q i e) : Row q i e := by
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · rw [row_case_2 q 2 4 (by omega) rfl]; omega
  · rw [row_case_4 q 4 (4*q-1) (by omega) rfl]; omega
  · rw [row_case_12 q (4*q-1) 2 (by omega) (by omega)]; omega

theorem added_absent (q i e : Nat) (hq : 4 ≤ q) (h : Added q i e) : ¬Row q i e := by
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · rw [row_case_2 q 2 (4*q-1) (by omega) rfl]; omega
  · rw [row_case_4 q 4 2 (by omega) rfl]; omega
  · rw [row_case_12 q (4*q-1) 4 (by omega) (by omega)]; omega

theorem included_filter (q : Nat) (hq : 4 ≤ q) : ∀ i, Included (V q i) (F q i) := by
  intro i e he
  rcases he with h | h
  · exact S_included_F q (by omega) i e h.1
  · change FilterRow q i.val (e.val+1)
    unfold Added at h
    unfold FilterRow
    have := i.isLt
    rcases h with h | h | h <;> omega

end LuRazThreeRow
