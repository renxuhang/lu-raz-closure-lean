import SixRowFullSources

namespace LuRazSixRowClosure
open LuRazClosure LuRazParametric
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

def FullExtraKeep (q : Nat) : NFFull → Prop
  | .noNMK k => k=0
  | .noH1Short p _ => q+2≤p
  | .noH2 a => a=2*q+3
  | _ => True

def FullKeep (q : Nat) (z : NFFull) : Prop :=
  z.Valid q ∧ ¬LuRazThreeRow.LostFull q z ∧ FullExtraKeep q z

def FullExtras (q : Nat) (R : Nat → Prop) : Prop :=
  (R (q+2) ∨ R (2*q+1)) ∧
  (R (2*q+2) ∨ R (2*q+3)) ∧
  (R (2*q+2) ∨ R (4*q))

def FullTest (q : Nat) (R : Nat → Prop) : Prop :=
  LuRazThreeRow.FullPass q R ∧ FullExtras q R

theorem full_extra_classification (q : Nat) (hq : 4≤q) (z : NFFull)
    (hz : z.Valid q) (hl : ¬LuRazThreeRow.LostFull q z) :
    FullExtras q (z.eval q) ↔ FullExtraKeep q z := by
  cases z <;>
    simp only [NFFull.Valid,LuRazThreeRow.LostFull] at hz hl <;>
    simp only [FullExtras,FullExtraKeep,NFFull.eval,FullHead,I] <;> (simp_all <;> omega)

theorem full_test_classification (q : Nat) (hq : 4≤q) (z : NFFull) (hz : z.Valid q) :
    FullTest q (z.eval q) ↔ ¬LuRazThreeRow.LostFull q z ∧ FullExtraKeep q z := by
  unfold FullTest
  constructor
  · intro h
    have hl := (LuRazThreeRow.full_pass_classification q hq z hz).mp h.1
    exact ⟨hl,(full_extra_classification q hq z hz hl).mp h.2⟩
  · intro h
    exact ⟨(LuRazThreeRow.full_pass_classification q hq z hz).mpr h.1,
      (full_extra_classification q hq z hz h.1).mpr h.2⟩

end LuRazSixRowClosure
