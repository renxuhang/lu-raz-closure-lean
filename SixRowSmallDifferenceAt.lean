import SixRowSmallDifference
import SixRowFullDifference

namespace LuRazSixRowClosure
open LuRazClosure LuRazParametric Difference
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

theorem core4_added_not_old (q : Nat) (hq : 4≤q) (R : Nat → Prop) (hc : CoreMask 4 R)
    (ha : AddedAt q 4 R) : ¬LuRazThreeRow.Generated q R := by
  intro ho
  obtain ⟨z,hz,hzc,hze⟩ := (old4_removed_exact q hq R hc).mp ho
  obtain ⟨w,hw,hwc,hwe⟩ := ha
  have he := (hze (2*q+2)).trans (hwe (2*q+2)).symm
  cases z <;> simp only [RemovedForm.core] at hzc
  all_goals try omega
  cases w <;> simp only [AddedForm.core] at hwc
  all_goals try omega
  simp only [RemovedForm.Valid,AddedForm.Valid] at hz hw
  simp only [RemovedForm.eval,AddedForm.eval,Cp,Ct,C,B,I] at he
  simp_all <;> omega

theorem core4_removed_at (q : Nat) (hq : 4≤q) (R : Nat → Prop) (hc : CoreMask 4 R) :
    (LuRazThreeRow.Generated q R ∧ ¬Generated q R) ↔ RemovedAt q 4 R := by
  constructor
  · exact fun h => (old4_removed_exact q hq R hc).mp h.1
  · intro h
    have ho := (old4_removed_exact q hq R hc).mpr h
    refine ⟨ho,?_⟩
    intro hg
    exact core4_added_not_old q hq R hc ((new4_added_exact q hq R hc).mp hg) ho

theorem core4_added_at (q : Nat) (hq : 4≤q) (R : Nat → Prop) (hc : CoreMask 4 R) :
    (Generated q R ∧ ¬LuRazThreeRow.Generated q R) ↔ AddedAt q 4 R := by
  constructor
  · exact fun h => (new4_added_exact q hq R hc).mp h.1
  · exact fun h => ⟨added4_generated q hq h,core4_added_not_old q hq R hc h⟩

theorem core5_added_not_old (q : Nat) (hq : 4≤q) (R : Nat → Prop) (hc : CoreMask 5 R)
    (ha : AddedAt q 5 R) : ¬LuRazThreeRow.Generated q R := by
  intro ho
  have hco : LuRazThreeRow.Core5 R := by simpa [CoreMask,LuRazThreeRow.Core5] using hc
  obtain ⟨z,hze⟩ := (LuRazThreeRow.core5_exact q hq R).mp ⟨ho,hco⟩
  obtain ⟨w,hw,hwc,hwe⟩ := ha
  have hn := (hwe (4*q)).trans (hze (4*q))
  have hm := (hwe (2*q+2)).trans (hze (2*q+2))
  have hr := (hwe (3*q+1)).trans (hze (3*q+1))
  have hnm := (hwe (4*q-1)).trans (hze (4*q-1))
  cases w <;> simp only [AddedForm.core] at hwc
  all_goals try omega
  rename_i k
  have hk : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 := by
    change k≤6 at hw
    omega
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals cases z <;>
    simp only [AddedForm.eval,LuRazThreeRow.NF5.eval,LuRazThreeRow.ZPrime,ARow,
      LuRazClosure.BRow,CRow,A,B,Cp,Ct,Lnew,Zp,I] at hn hm hr hnm <;> (simp_all <;> omega)

theorem core5_removed_old (q : Nat) (hq : 4≤q) (R : Nat → Prop)
    (h : RemovedAt q 5 R) : LuRazThreeRow.Generated q R := by
  obtain ⟨z,hz,hzc,he⟩ := h
  cases z <;> simp only [RemovedForm.core] at hzc
  all_goals try omega
  apply LuRazThreeRow.generated_congr q (LuRazThreeRow.nf5_generated q hq .ac)
  intro e
  rw [←he e]
  simp only [LuRazThreeRow.NF5.eval,RemovedForm.eval,ARow,CRow,C,I]
  omega

theorem core5_removed_at (q : Nat) (hq : 4≤q) (R : Nat → Prop) (hc : CoreMask 5 R) :
    (LuRazThreeRow.Generated q R ∧ ¬Generated q R) ↔ RemovedAt q 5 R := by
  classical
  constructor
  · rintro ⟨ho,hn⟩
    apply Classical.byContradiction
    intro hr
    exact hn ((core5_delta_exact q hq R hc).mpr (Or.inl ⟨ho,hr⟩))
  · intro h
    exact ⟨core5_removed_old q hq R h,fun hg => generated5_not_removed q hq hg h⟩

theorem core5_added_at (q : Nat) (hq : 4≤q) (R : Nat → Prop) (hc : CoreMask 5 R) :
    (Generated q R ∧ ¬LuRazThreeRow.Generated q R) ↔ AddedAt q 5 R := by
  constructor
  · rintro ⟨hg,hn⟩
    exact ((core5_delta_exact q hq R hc).mp hg).elim (fun h => False.elim (hn h.1)) id
  · exact fun h => ⟨added5_generated q hq h,core5_added_not_old q hq R hc h⟩

theorem core15_removed_old (q : Nat) (hq : 4≤q) (R : Nat → Prop)
    (h : RemovedAt q 15 R) : LuRazThreeRow.Generated q R := by
  obtain ⟨z,hz,hzc,he⟩ := h
  cases z <;> simp only [RemovedForm.core] at hzc
  all_goals try omega
  case r15points k =>
    have hk : k=0 ∨ k=1 := by change k≤1 at hz; omega
    rcases hk with rfl | rfl
    · apply LuRazThreeRow.generated_congr q
        (LuRazThreeRow.retained_full_generated q hq (.noNMK 1) (by simp [NFFull.Valid,LuRazThreeRow.LostFull]))
      intro e
      rw [←he e]
      simp [NFFull.eval,RemovedForm.eval,FullHead,I] <;> omega
    · apply LuRazThreeRow.generated_congr q (LuRazThreeRow.add_full_generated q hq .point True.intro)
      intro e
      rw [←he e]
      simp [LuRazThreeRow.AddFull.eval,RemovedForm.eval,FullHead,I] <;> omega
  case r15right a =>
    apply LuRazThreeRow.generated_congr q (LuRazThreeRow.add_full_generated q hq (.right a) hz)
    intro e
    rw [←he e]
    simp [LuRazThreeRow.AddFull.eval,RemovedForm.eval,FullHead,I] <;> omega
  case r15gap a =>
    apply LuRazThreeRow.generated_congr q (LuRazThreeRow.add_full_generated q hq (.gap a) hz)
    intro e
    rw [←he e]
    simp [LuRazThreeRow.AddFull.eval,RemovedForm.eval,FullHead,A,I] <;> omega
  case r15line a =>
    apply LuRazThreeRow.generated_congr q (LuRazThreeRow.retained_full_generated q hq (.noH2 a) ?_)
    · intro e
      rw [←he e]
      simp [NFFull.eval,RemovedForm.eval,FullHead,I]
    · simp only [NFFull.Valid,LuRazThreeRow.LostFull]
      change 2*q+4≤a ∧ a≤4*q-1 at hz
      omega
  case r15short p t =>
    have hh : 4≤p ∧ p≤q+1 ∧ (t=2*q+2 ∨ t=2*q+3) := hz
    rcases hh.2.2 with rfl | rfl
    · apply LuRazThreeRow.generated_congr q
        (LuRazThreeRow.retained_full_generated q hq (.noH1Short p 0) (by simp [NFFull.Valid,LuRazThreeRow.LostFull]; omega))
      intro e
      rw [←he e]
      simp [NFFull.eval,RemovedForm.eval,FullHead,I]
    · apply LuRazThreeRow.generated_congr q
        (LuRazThreeRow.retained_full_generated q hq (.noH1Short p 1) (by simp [NFFull.Valid,LuRazThreeRow.LostFull]; omega))
      intro e
      rw [←he e]
      simp [NFFull.eval,RemovedForm.eval,FullHead,I]

theorem core15_removed_at (q : Nat) (hq : 4≤q) (R : Nat → Prop) (hc : CoreMask 15 R) :
    (LuRazThreeRow.Generated q R ∧ ¬Generated q R) ↔ RemovedAt q 15 R := by
  classical
  constructor
  · rintro ⟨ho,hn⟩
    apply Classical.byContradiction
    intro hr
    exact hn ((full_core_mask_delta q hq R hc).mpr ⟨ho,hr⟩)
  · intro h
    refine ⟨core15_removed_old q hq R h,?_⟩
    intro hg
    exact ((full_core_mask_delta q hq R hc).mp hg).2 h

theorem core15_added_at (q : Nat) (hq : 4≤q) (R : Nat → Prop) (hc : CoreMask 15 R) :
    (Generated q R ∧ ¬LuRazThreeRow.Generated q R) ↔ AddedAt q 15 R := by
  constructor
  · rintro ⟨hg,hn⟩
    exact False.elim (hn ((full_core_mask_delta q hq R hc).mp hg).1)
  · rintro ⟨z,hz,hzc,he⟩
    cases z <;> simp [AddedForm.core] at hzc

end LuRazSixRowClosure
