import ThreeRowNecessary
import LuRazTotalClosure

namespace LuRazThreeRow
open LuRazClosure
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

def LostFull (q : Nat) : NFFull → Prop
  | .noH1ZL _ | .noH1Exception => True
  | .noH2 a => a=4*q
  | .rightGap b c => c=4*q ∧ b≤4*q-3
  | .isolatedR _ c => c=4*q
  | _ => False

def FullPass (q : Nat) (R : Nat → Prop) : Prop :=
  (R (4*q-2) ∨ R (4*q-1)) ∧
  (R (2*q+1) ∨ R (2*q+2) ∨ R (2*q+3)) ∧
  (R (q+3) → R (2*q+1) ∨ R (4*q-1))

theorem full_pass_necessary (q : Nat) (hq : 4≤q) (R : Nat → Prop)
    (hg : Generated q R) (h2 : R 2) (h4 : R 4) : FullPass q R :=
  ⟨generated_two_end q hq R hg h2,generated_four_middle q hq R hg h4,
    generated_prefix_middle q hq R hg⟩

/-- Among the old full-core normal forms, the three necessary clauses reject exactly these five lines. -/
theorem full_pass_classification (q : Nat) (hq : 4≤q) (z : NFFull) (hz : z.Valid q) :
    FullPass q (z.eval q) ↔ ¬LostFull q z := by
  cases z <;> simp only [NFFull.Valid] at hz <;>
    simp only [FullPass,LostFull,NFFull.eval,FullHead,I] <;> simp_all <;> omega

theorem lost_full_not_generated (q : Nat) (hq : 4≤q) (z : NFFull)
    (hz : z.Valid q) (hl : LostFull q z) : ¬Generated q (z.eval q) := by
  intro hg
  have h2 : z.eval q 2 := by cases z <;> simp [NFFull.eval,FullHead]
  have h4 : z.eval q 4 := by cases z <;> simp [NFFull.eval,FullHead]
  exact ((full_pass_classification q hq z hz).mp (full_pass_necessary q hq _ hg h2 h4)) hl

end LuRazThreeRow
