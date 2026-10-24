import SixRowDifferenceForms
namespace LuRazSixRowClosure.Difference
open LuRazClosure
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

def CoreMask (k : Nat) (R : Nat → Prop) : Prop :=
  (R 1 ↔ k=1 ∨ k=3 ∨ k=5 ∨ k=7 ∨ k=9 ∨ k=11 ∨ k=13 ∨ k=15) ∧
  (R 2 ↔ k=2 ∨ k=3 ∨ k=6 ∨ k=7 ∨ k=10 ∨ k=11 ∨ k=14 ∨ k=15) ∧
  (R 3 ↔ k=4 ∨ k=5 ∨ k=6 ∨ k=7 ∨ k=12 ∨ k=13 ∨ k=14 ∨ k=15) ∧
  (R 4 ↔ 8≤k ∧ k≤15)

def RemovedForm.tag : RemovedForm → Nat
  | .r2 => 0
  | .r3 => 1
  | .r4 _ => 2
  | .r5 => 3
  | .r6regular _ => 4
  | .r6exception => 5
  | .r6d _ => 6
  | .r7fresh _ => 7
  | .r7e _ => 8
  | .r7d _ => 9
  | .r10 _ => 10
  | .r11j _ => 11
  | .r11aj _ => 12
  | .r11ak _ => 13
  | .r12 _ => 14
  | .r13cj _ => 15
  | .r13zj _ => 16
  | .r13czj _ => 17
  | .r13points _ => 18
  | .r14points _ => 19
  | .r14line _ => 20
  | .r14c _ => 21
  | .r15points _ => 22
  | .r15right _ => 23
  | .r15gap _ => 24
  | .r15line _ => 25
  | .r15short _ _ => 26

def RemovedForm.core : RemovedForm → Nat
  | .r2 => 2
  | .r3 => 3
  | .r4 _ => 4
  | .r5 => 5
  | .r6regular _ => 6
  | .r6exception => 6
  | .r6d _ => 6
  | .r7fresh _ => 7
  | .r7e _ => 7
  | .r7d _ => 7
  | .r10 _ => 10
  | .r11j _ => 11
  | .r11aj _ => 11
  | .r11ak _ => 11
  | .r12 _ => 12
  | .r13cj _ => 13
  | .r13zj _ => 13
  | .r13czj _ => 13
  | .r13points _ => 13
  | .r14points _ => 14
  | .r14line _ => 14
  | .r14c _ => 14
  | .r15points _ => 15
  | .r15right _ => 15
  | .r15gap _ => 15
  | .r15line _ => 15
  | .r15short _ _ => 15

theorem RemovedForm.core_mask (q : Nat) (hq : 4≤q) (z : RemovedForm) (hz : z.Valid q) : CoreMask z.core (z.eval q) := by
  cases z <;> simp_all [RemovedForm.Valid,RemovedForm.eval,RemovedForm.core,CoreMask,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] <;> omega

def AddedForm.tag : AddedForm → Nat
  | .n4 _ => 0
  | .n5 _ => 1
  | .n6regular _ => 2
  | .n6exception => 3
  | .n6e _ => 4
  | .n7regular _ => 5
  | .n7exception => 6
  | .n7right _ => 7
  | .n7point => 8
  | .n10 _ => 9
  | .n11j _ => 10
  | .n11aj _ => 11
  | .n11ak _ => 12
  | .n13plain _ => 13
  | .n13isolated _ => 14
  | .n13right _ => 15

def AddedForm.core : AddedForm → Nat
  | .n4 _ => 4
  | .n5 _ => 5
  | .n6regular _ => 6
  | .n6exception => 6
  | .n6e _ => 6
  | .n7regular _ => 7
  | .n7exception => 7
  | .n7right _ => 7
  | .n7point => 7
  | .n10 _ => 10
  | .n11j _ => 11
  | .n11aj _ => 11
  | .n11ak _ => 11
  | .n13plain _ => 13
  | .n13isolated _ => 13
  | .n13right _ => 13

theorem AddedForm.core_mask (q : Nat) (hq : 4≤q) (z : AddedForm) (hz : z.Valid q) : CoreMask z.core (z.eval q) := by
  cases z <;> simp_all [AddedForm.Valid,AddedForm.eval,AddedForm.core,CoreMask,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] <;> omega

def Removed (q : Nat) (R : Nat → Prop) : Prop :=
  ∃z : RemovedForm,z.Valid q ∧ ∀e,z.eval q e ↔ R e

def Added (q : Nat) (R : Nat → Prop) : Prop :=
  ∃z : AddedForm,z.Valid q ∧ ∀e,z.eval q e ↔ R e

def RemovedAt (q k : Nat) (R : Nat → Prop) : Prop :=
  ∃z : RemovedForm,z.Valid q ∧ z.core=k ∧ ∀e,z.eval q e ↔ R e

def AddedAt (q k : Nat) (R : Nat → Prop) : Prop :=
  ∃z : AddedForm,z.Valid q ∧ z.core=k ∧ ∀e,z.eval q e ↔ R e

theorem core_mask_congr (k : Nat) (R T : Nat→Prop) (he : ∀e,R e↔T e) : CoreMask k R ↔ CoreMask k T := by
  unfold CoreMask
  rw [he 1,he 2,he 3,he 4]

theorem core_mask_unique (k j : Nat) (hk : k≤15) (hj : j≤15) (R : Nat→Prop)
    (hc : CoreMask k R) (hd : CoreMask j R) : k=j := by
  have h1 := hc.1.symm.trans hd.1
  have h2 := hc.2.1.symm.trans hd.2.1
  have h3 := hc.2.2.1.symm.trans hd.2.2.1
  have h4 := hc.2.2.2.symm.trans hd.2.2.2
  omega

theorem core_mask_5 (R : Nat→Prop) : CoreMask 5 R ↔ LuRazThreeRow.Core5 R := by
  simp [CoreMask,LuRazThreeRow.Core5]

theorem core_mask_6 (R : Nat→Prop) : CoreMask 6 R ↔ Core23 R := by
  simp [CoreMask,Core23]

theorem core_mask_7 (R : Nat→Prop) : CoreMask 7 R ↔ Core123 R := by
  simp [CoreMask,Core123]

theorem core_mask_9 (R : Nat→Prop) : CoreMask 9 R ↔ Core14 R := by
  simp [CoreMask,Core14]

theorem core_mask_10 (R : Nat→Prop) : CoreMask 10 R ↔ Core24 R := by
  simp [CoreMask,Core24]

theorem core_mask_11 (R : Nat→Prop) : CoreMask 11 R ↔ Core124 R := by
  simp [CoreMask,Core124]

theorem core_mask_12 (R : Nat→Prop) : CoreMask 12 R ↔ LuRazThreeRow.Core12 R := by
  simp [CoreMask,LuRazThreeRow.Core12]

theorem core_mask_13 (R : Nat→Prop) : CoreMask 13 R ↔ Core134 R := by
  simp [CoreMask,Core134]

theorem core_mask_14 (R : Nat→Prop) : CoreMask 14 R ↔ Core234 R := by
  simp [CoreMask,Core234]

theorem core_mask_15 (R : Nat→Prop) : CoreMask 15 R ↔ CoreFull R := by
  simp [CoreMask,CoreFull]

end LuRazSixRowClosure.Difference
