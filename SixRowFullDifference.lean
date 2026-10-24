import SixRowFullExact
import SixRowDifferencePredicates

namespace LuRazSixRowClosure
open LuRazClosure LuRazParametric Difference
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

theorem removed15_not_generated (q : Nat) (hq : 4≤q) (z : RemovedForm)
    (hz : z.Valid q) (hc : z.core=15) : ¬Generated q (z.eval q) := by
  intro hg
  have hmask := z.core_mask q hq hz
  rw [hc] at hmask
  have hfull : CoreFull (z.eval q) := by simpa [CoreMask,CoreFull] using hmask
  have htest := full_test_necessary q hq hg hfull
  have hprefix : ¬z.eval q (4*q-1) → z.eval q 5 ∧ z.eval q (q+3) ∧ z.eval q (2*q+2) := by
    intro hn
    have hp := full_no_last_prefix q hq hg hfull.2.2.1 hn
    exact ⟨hp 5 (by omega),hp (q+3) (by omega),hp (2*q+2) (by omega)⟩
  cases z <;> simp only [RemovedForm.core] at hc
  all_goals try omega
  all_goals
    simp only [FullTest,LuRazThreeRow.FullPass,FullExtras,RemovedForm.eval,A,I] at htest hprefix
    simp_all [RemovedForm.Valid] <;> omega

theorem removed15_congr (q : Nat) {R T : Nat → Prop}
    (h : RemovedAt q 15 R) (he : ∀ e, R e ↔ T e) : RemovedAt q 15 T := by
  obtain ⟨z,hz,hc,hR⟩ := h
  exact ⟨z,hz,hc,fun e => (hR e).trans (he e)⟩

theorem old_full_extra_removed (q : Nat) (hq : 4≤q) (z : NFFull)
    (hz : z.Valid q) (hl : ¬LuRazThreeRow.LostFull q z)
    (he : ¬FullExtraKeep q z) : RemovedAt q 15 (z.eval q) := by
  cases z <;> simp only [FullExtraKeep] at he
  all_goals try exact False.elim (he True.intro)
  case noNMK k =>
    have hk : k<2 := hz
    have hke : k=1 := by omega
    subst k
    refine ⟨.r15points 0,by simp [RemovedForm.Valid],rfl,?_⟩
    intro e
    simp only [RemovedForm.eval,NFFull.eval,FullHead,I] <;> (simp_all <;> omega)
  case noH1Short p k =>
    have hv : (4≤p ∧ p≤2*q) ∧ k<2 := hz
    refine ⟨.r15short p (2*q+2+k),?_,rfl,?_⟩
    · change 4≤p ∧ p≤q+1 ∧ (2*q+2+k=2*q+2 ∨ 2*q+2+k=2*q+3)
      omega
    · intro e
      simp only [RemovedForm.eval,NFFull.eval,FullHead,I] <;> (simp_all <;> omega)
  case noH2 a =>
    have hv : 2*q+3≤a ∧ a≤4*q := hz
    have hn : a≠4*q := hl
    refine ⟨.r15line a,?_,rfl,?_⟩
    · change 2*q+4≤a ∧ a≤4*q-1
      omega
    · intro e
      simp only [RemovedForm.eval,NFFull.eval,FullHead,I]

theorem fresh_full_removed (q : Nat) (hq : 4≤q) (z : LuRazThreeRow.AddFull)
    (hz : z.Valid q) : RemovedAt q 15 (z.eval q) := by
  cases z with
  | right a =>
    refine ⟨.r15right a,hz,rfl,?_⟩
    intro e
    simp only [RemovedForm.eval,LuRazThreeRow.AddFull.eval,FullHead] <;> (simp_all <;> omega)
  | gap a =>
    refine ⟨.r15gap a,hz,rfl,?_⟩
    intro e
    simp only [RemovedForm.eval,LuRazThreeRow.AddFull.eval,FullHead,A] <;> (simp_all <;> omega)
  | point =>
    refine ⟨.r15points 1,by simp [RemovedForm.Valid],rfl,?_⟩
    intro e
    simp only [RemovedForm.eval,LuRazThreeRow.AddFull.eval,FullHead] <;> (simp_all <;> omega)

theorem full_delta_exact (q : Nat) (hq : 4≤q) (R : Nat → Prop) (hc : CoreFull R) :
    Generated q R ↔ LuRazThreeRow.Generated q R ∧ ¬RemovedAt q 15 R := by
  classical
  constructor
  · intro hg
    obtain ⟨z,hz,he⟩ := full_generated_normal q hq hg hc
    refine ⟨LuRazThreeRow.generated_congr q
      (LuRazThreeRow.retained_full_generated q hq z ⟨hz.1,hz.2.1⟩)
      (fun e => (he e).symm),?_⟩
    rintro ⟨w,hw,hwc,hwe⟩
    exact removed15_not_generated q hq w hw hwc
      (generated_congr q hg (fun e => (hwe e).symm))
  · rintro ⟨hg,hr⟩
    obtain ⟨z,hz,he⟩ := (LuRazThreeRow.full_new_exhaustive q hq R).mp ⟨hg,hc⟩
    cases z with
    | old z =>
      have hk : FullExtraKeep q z := by
        apply Classical.byContradiction
        intro h
        exact hr (removed15_congr q (old_full_extra_removed q hq z hz.1 hz.2 h)
          (fun e => (he e).symm))
      exact generated_congr q (full_retained_generated q hq z ⟨hz.1,hz.2,hk⟩)
        (fun e => (he e).symm)
    | fresh z =>
      exact False.elim (hr (removed15_congr q (fresh_full_removed q hq z hz)
        (fun e => (he e).symm)))

theorem full_core_mask_delta (q : Nat) (hq : 4≤q) (R : Nat → Prop)
    (hc : CoreMask 15 R) :
    Generated q R ↔ LuRazThreeRow.Generated q R ∧ ¬RemovedAt q 15 R :=
  full_delta_exact q hq R (by simpa [CoreMask,CoreFull] using hc)

end LuRazSixRowClosure
