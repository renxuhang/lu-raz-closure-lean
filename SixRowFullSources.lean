import SixRowClosureDefs

namespace LuRazSixRowClosure
open LuRazClosure LuRazParametric
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

def FullChanged (q i : Nat) : Prop :=
  i=1 ∨ i=2 ∨ i=4 ∨ i=2*q+2 ∨ i=4*q-1 ∨ i=4*q

theorem full_unchanged (q i e : Nat) (hi : ¬FullChanged q i) :
    LuRazSixRow.BRow q i e ↔ Row q i e := by
  rw [LuRazSixRow.unchanged_row q i e (by unfold FullChanged LuRazSixRow.Special at *; omega),
    LuRazFourRow.unchanged_row q i e (by unfold FullChanged LuRazFourRow.Special at *; omega),
    LuRazThreeRow.unchanged_row q i e (by unfold FullChanged LuRazThreeRow.Special at *; omega)]

theorem full_row_one (q e : Nat) (hq : 4≤q) :
    LuRazSixRow.BRow q 1 e ↔ e=2 ∨ e=4 ∨ (2*q+1≤e ∧ e≤4*q-2) ∨ e=4*q := by
  rw [LuRazSixRow.unchanged_row q 1 e (by unfold LuRazSixRow.Special; omega),
    LuRazFourRow.row_one q e hq]

theorem full_row_two (q e : Nat) (hq : 4≤q) :
    LuRazSixRow.BRow q 2 e ↔ e=1 ∨ e=3 ∨ (5≤e ∧ e≤2*q) ∨ e=4*q-1 ∨ e=4*q := by
  rw [LuRazSixRow.unchanged_row q 2 e (by unfold LuRazSixRow.Special; omega),
    LuRazFourRow.unchanged_row q 2 e (by unfold LuRazFourRow.Special; omega),
    LuRazThreeRow.row_two q e hq]

theorem full_row_four (q e : Nat) (hq : 4≤q) :
    LuRazSixRow.BRow q 4 e ↔ e=2 ∨ e=3 ∨ (2*q+3≤e ∧ e≤4*q) := by
  rw [LuRazSixRow.unchanged_row q 4 e (by unfold LuRazSixRow.Special; omega),
    LuRazFourRow.row_four q e hq]


end LuRazSixRowClosure
