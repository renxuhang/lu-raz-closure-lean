import SixRowSmallDifferenceBase

namespace LuRazSixRowClosure
open LuRazClosure LuRazParametric Difference
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

theorem new4_added_exact (q : Nat) (hq : 4≤q) (R : Nat → Prop) (hc : CoreMask 4 R) :
    Generated q R ↔ AddedAt q 4 R := by
  constructor
  · intro hg
    have hh : ¬R 1 ∧ ¬R 2 ∧ R 3 ∧ ¬R 4 := by simpa [CoreMask] using hc
    obtain ⟨x,he⟩ := (Small.exhaustive q hq R).mp ⟨hg,hh.2.1,hh.2.2.2⟩
    have hcx := (core_mask_congr 4 R (x.eval q) he).mp hc
    cases x with
    | a =>
      simp [CoreMask,Small.Normal.eval,Small.SA,Small.SB,Small.SC,Small.SZ,Small.SL,I] at hcx <;> omega
    | b =>
      simp [CoreMask,Small.Normal.eval,Small.SA,Small.SB,Small.SC,Small.SZ,Small.SL,I] at hcx <;> omega
    | ab =>
      simp [CoreMask,Small.Normal.eval,Small.SA,Small.SB,Small.SC,Small.SZ,Small.SL,I] at hcx <;> omega
    | c =>
      refine ⟨.n4 0,by simp [AddedForm.Valid],rfl,?_⟩
      intro e
      rw [he e]
      simp [RemovedForm.eval,AddedForm.eval,Small.Normal.eval,Small.SA,Small.SB,Small.SC,Small.SZ,Small.SL,LuRazThreeRow.NF5.eval,LuRazThreeRow.ZPrime,ARow,LuRazClosure.BRow,CRow,A,B,C,Cp,Ct,Zp,Lnew,I] <;> omega
    | ac =>
      simp [CoreMask,Small.Normal.eval,Small.SA,Small.SB,Small.SC,Small.SZ,Small.SL,I] at hcx <;> omega
    | cb =>
      refine ⟨.n4 1,by simp [AddedForm.Valid],rfl,?_⟩
      intro e
      rw [he e]
      simp [RemovedForm.eval,AddedForm.eval,Small.Normal.eval,Small.SA,Small.SB,Small.SC,Small.SZ,Small.SL,LuRazThreeRow.NF5.eval,LuRazThreeRow.ZPrime,ARow,LuRazClosure.BRow,CRow,A,B,C,Cp,Ct,Zp,Lnew,I] <;> omega
    | acb =>
      simp [CoreMask,Small.Normal.eval,Small.SA,Small.SB,Small.SC,Small.SZ,Small.SL,I] at hcx <;> omega
    | z =>
      simp [CoreMask,Small.Normal.eval,Small.SA,Small.SB,Small.SC,Small.SZ,Small.SL,I] at hcx <;> omega
    | zb =>
      simp [CoreMask,Small.Normal.eval,Small.SA,Small.SB,Small.SC,Small.SZ,Small.SL,I] at hcx <;> omega
    | cz =>
      simp [CoreMask,Small.Normal.eval,Small.SA,Small.SB,Small.SC,Small.SZ,Small.SL,I] at hcx <;> omega
    | l =>
      simp [CoreMask,Small.Normal.eval,Small.SA,Small.SB,Small.SC,Small.SZ,Small.SL,I] at hcx <;> omega
    | lb =>
      simp [CoreMask,Small.Normal.eval,Small.SA,Small.SB,Small.SC,Small.SZ,Small.SL,I] at hcx <;> omega
    | cl =>
      simp [CoreMask,Small.Normal.eval,Small.SA,Small.SB,Small.SC,Small.SZ,Small.SL,I] at hcx <;> omega
    | clb =>
      simp [CoreMask,Small.Normal.eval,Small.SA,Small.SB,Small.SC,Small.SZ,Small.SL,I] at hcx <;> omega
    | zl =>
      simp [CoreMask,Small.Normal.eval,Small.SA,Small.SB,Small.SC,Small.SZ,Small.SL,I] at hcx <;> omega
    | czl =>
      simp [CoreMask,Small.Normal.eval,Small.SA,Small.SB,Small.SC,Small.SZ,Small.SL,I] at hcx <;> omega
  · exact added4_generated q hq

theorem core4_delta_exact (q : Nat) (hq : 4≤q) (R : Nat → Prop) (hc : CoreMask 4 R) :
    Generated q R ↔ (LuRazThreeRow.Generated q R ∧ ¬RemovedAt q 4 R) ∨ AddedAt q 4 R := by
  rw [new4_added_exact q hq R hc]
  constructor
  · exact Or.inr
  · rintro (h | h)
    · exact False.elim (h.2 ((old4_removed_exact q hq R hc).mp h.1))
    · exact h

theorem core5_delta_exact (q : Nat) (hq : 4≤q) (R : Nat → Prop) (hc : CoreMask 5 R) :
    Generated q R ↔ (LuRazThreeRow.Generated q R ∧ ¬RemovedAt q 5 R) ∨ AddedAt q 5 R := by
  constructor
  · intro hg
    have hnot := generated5_not_removed q hq hg
    have hh : R 1 ∧ ¬R 2 ∧ R 3 ∧ ¬R 4 := by simpa [CoreMask] using hc
    obtain ⟨x,he⟩ := (Small.exhaustive q hq R).mp ⟨hg,hh.2.1,hh.2.2.2⟩
    have hcx := (core_mask_congr 5 R (x.eval q) he).mp hc
    cases x with
    | a =>
      simp [CoreMask,Small.Normal.eval,Small.SA,Small.SB,Small.SC,Small.SZ,Small.SL,I] at hcx <;> omega
    | b =>
      simp [CoreMask,Small.Normal.eval,Small.SA,Small.SB,Small.SC,Small.SZ,Small.SL,I] at hcx <;> omega
    | ab =>
      simp [CoreMask,Small.Normal.eval,Small.SA,Small.SB,Small.SC,Small.SZ,Small.SL,I] at hcx <;> omega
    | c =>
      simp [CoreMask,Small.Normal.eval,Small.SA,Small.SB,Small.SC,Small.SZ,Small.SL,I] at hcx <;> omega
    | ac =>
      right
      refine ⟨.n5 1,by simp [AddedForm.Valid],rfl,?_⟩
      intro e
      rw [he e]
      simp [RemovedForm.eval,AddedForm.eval,Small.Normal.eval,Small.SA,Small.SB,Small.SC,Small.SZ,Small.SL,LuRazThreeRow.NF5.eval,LuRazThreeRow.ZPrime,ARow,LuRazClosure.BRow,CRow,A,B,C,Cp,Ct,Zp,Lnew,I] <;> omega
    | cb =>
      simp [CoreMask,Small.Normal.eval,Small.SA,Small.SB,Small.SC,Small.SZ,Small.SL,I] at hcx <;> omega
    | acb =>
      right
      refine ⟨.n5 6,by simp [AddedForm.Valid],rfl,?_⟩
      intro e
      rw [he e]
      simp [RemovedForm.eval,AddedForm.eval,Small.Normal.eval,Small.SA,Small.SB,Small.SC,Small.SZ,Small.SL,LuRazThreeRow.NF5.eval,LuRazThreeRow.ZPrime,ARow,LuRazClosure.BRow,CRow,A,B,C,Cp,Ct,Zp,Lnew,I] <;> omega
    | z =>
      left
      refine ⟨?_,hnot⟩
      apply LuRazThreeRow.generated_congr q (LuRazThreeRow.nf5_generated q hq .z)
      intro e
      rw [he e]
      simp [RemovedForm.eval,AddedForm.eval,Small.Normal.eval,Small.SA,Small.SB,Small.SC,Small.SZ,Small.SL,LuRazThreeRow.NF5.eval,LuRazThreeRow.ZPrime,ARow,LuRazClosure.BRow,CRow,A,B,C,Cp,Ct,Zp,Lnew,I] <;> omega
    | zb =>
      left
      refine ⟨?_,hnot⟩
      apply LuRazThreeRow.generated_congr q (LuRazThreeRow.nf5_generated q hq .zb)
      intro e
      rw [he e]
      simp [RemovedForm.eval,AddedForm.eval,Small.Normal.eval,Small.SA,Small.SB,Small.SC,Small.SZ,Small.SL,LuRazThreeRow.NF5.eval,LuRazThreeRow.ZPrime,ARow,LuRazClosure.BRow,CRow,A,B,C,Cp,Ct,Zp,Lnew,I] <;> omega
    | cz =>
      right
      refine ⟨.n5 4,by simp [AddedForm.Valid],rfl,?_⟩
      intro e
      rw [he e]
      simp [RemovedForm.eval,AddedForm.eval,Small.Normal.eval,Small.SA,Small.SB,Small.SC,Small.SZ,Small.SL,LuRazThreeRow.NF5.eval,LuRazThreeRow.ZPrime,ARow,LuRazClosure.BRow,CRow,A,B,C,Cp,Ct,Zp,Lnew,I] <;> omega
    | l =>
      right
      refine ⟨.n5 0,by simp [AddedForm.Valid],rfl,?_⟩
      intro e
      rw [he e]
      simp [RemovedForm.eval,AddedForm.eval,Small.Normal.eval,Small.SA,Small.SB,Small.SC,Small.SZ,Small.SL,LuRazThreeRow.NF5.eval,LuRazThreeRow.ZPrime,ARow,LuRazClosure.BRow,CRow,A,B,C,Cp,Ct,Zp,Lnew,I] <;> omega
    | lb =>
      right
      refine ⟨.n5 5,by simp [AddedForm.Valid],rfl,?_⟩
      intro e
      rw [he e]
      simp [RemovedForm.eval,AddedForm.eval,Small.Normal.eval,Small.SA,Small.SB,Small.SC,Small.SZ,Small.SL,LuRazThreeRow.NF5.eval,LuRazThreeRow.ZPrime,ARow,LuRazClosure.BRow,CRow,A,B,C,Cp,Ct,Zp,Lnew,I] <;> omega
    | cl =>
      right
      refine ⟨.n5 2,by simp [AddedForm.Valid],rfl,?_⟩
      intro e
      rw [he e]
      simp [RemovedForm.eval,AddedForm.eval,Small.Normal.eval,Small.SA,Small.SB,Small.SC,Small.SZ,Small.SL,LuRazThreeRow.NF5.eval,LuRazThreeRow.ZPrime,ARow,LuRazClosure.BRow,CRow,A,B,C,Cp,Ct,Zp,Lnew,I] <;> omega
    | clb =>
      left
      refine ⟨?_,hnot⟩
      apply LuRazThreeRow.generated_congr q (LuRazThreeRow.nf5_generated q hq .acb)
      intro e
      rw [he e]
      simp [RemovedForm.eval,AddedForm.eval,Small.Normal.eval,Small.SA,Small.SB,Small.SC,Small.SZ,Small.SL,LuRazThreeRow.NF5.eval,LuRazThreeRow.ZPrime,ARow,LuRazClosure.BRow,CRow,A,B,C,Cp,Ct,Zp,Lnew,I] <;> omega
    | zl =>
      right
      refine ⟨.n5 3,by simp [AddedForm.Valid],rfl,?_⟩
      intro e
      rw [he e]
      simp [RemovedForm.eval,AddedForm.eval,Small.Normal.eval,Small.SA,Small.SB,Small.SC,Small.SZ,Small.SL,LuRazThreeRow.NF5.eval,LuRazThreeRow.ZPrime,ARow,LuRazClosure.BRow,CRow,A,B,C,Cp,Ct,Zp,Lnew,I] <;> omega
    | czl =>
      left
      refine ⟨?_,hnot⟩
      apply LuRazThreeRow.generated_congr q (LuRazThreeRow.nf5_generated q hq .zc)
      intro e
      rw [he e]
      simp [RemovedForm.eval,AddedForm.eval,Small.Normal.eval,Small.SA,Small.SB,Small.SC,Small.SZ,Small.SL,LuRazThreeRow.NF5.eval,LuRazThreeRow.ZPrime,ARow,LuRazClosure.BRow,CRow,A,B,C,Cp,Ct,Zp,Lnew,I] <;> omega
  · rintro (h | h)
    · have hco : LuRazThreeRow.Core5 R := by simpa [CoreMask,LuRazThreeRow.Core5] using hc
      obtain ⟨z,he⟩ := (LuRazThreeRow.core5_exact q hq R).mp ⟨h.1,hco⟩
      cases z with
      | z =>
        apply generated_congr q ((Small.Normal.z).generated q hq)
        intro e
        rw [he e]
        simp [RemovedForm.eval,AddedForm.eval,Small.Normal.eval,Small.SA,Small.SB,Small.SC,Small.SZ,Small.SL,LuRazThreeRow.NF5.eval,LuRazThreeRow.ZPrime,ARow,LuRazClosure.BRow,CRow,A,B,C,Cp,Ct,Zp,Lnew,I] <;> omega
      | zb =>
        apply generated_congr q ((Small.Normal.zb).generated q hq)
        intro e
        rw [he e]
        simp [RemovedForm.eval,AddedForm.eval,Small.Normal.eval,Small.SA,Small.SB,Small.SC,Small.SZ,Small.SL,LuRazThreeRow.NF5.eval,LuRazThreeRow.ZPrime,ARow,LuRazClosure.BRow,CRow,A,B,C,Cp,Ct,Zp,Lnew,I] <;> omega
      | zc =>
        apply generated_congr q ((Small.Normal.czl).generated q hq)
        intro e
        rw [he e]
        simp [RemovedForm.eval,AddedForm.eval,Small.Normal.eval,Small.SA,Small.SB,Small.SC,Small.SZ,Small.SL,LuRazThreeRow.NF5.eval,LuRazThreeRow.ZPrime,ARow,LuRazClosure.BRow,CRow,A,B,C,Cp,Ct,Zp,Lnew,I] <;> omega
      | ac =>
        apply False.elim
        apply h.2
        refine ⟨.r5,by simp [RemovedForm.Valid],rfl,?_⟩
        intro e
        rw [he e]
        simp [RemovedForm.eval,AddedForm.eval,Small.Normal.eval,Small.SA,Small.SB,Small.SC,Small.SZ,Small.SL,LuRazThreeRow.NF5.eval,LuRazThreeRow.ZPrime,ARow,LuRazClosure.BRow,CRow,A,B,C,Cp,Ct,Zp,Lnew,I] <;> omega
      | acb =>
        apply generated_congr q ((Small.Normal.clb).generated q hq)
        intro e
        rw [he e]
        simp [RemovedForm.eval,AddedForm.eval,Small.Normal.eval,Small.SA,Small.SB,Small.SC,Small.SZ,Small.SL,LuRazThreeRow.NF5.eval,LuRazThreeRow.ZPrime,ARow,LuRazClosure.BRow,CRow,A,B,C,Cp,Ct,Zp,Lnew,I] <;> omega
    · exact added5_generated q hq h

end LuRazSixRowClosure
