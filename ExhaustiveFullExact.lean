import ExhaustiveThinNormal

namespace LuRazThreeRow
open LuRazClosure
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000

theorem full_old_retained (q : Nat) (hq : 4≤q) (R : Nat → Prop)
    (hg : Generated q R) (ho : LuRazClosure.Generated q R) (hc : CoreFull R) :
    ∃ z : NormalFull, z.Valid q ∧ ∀ e, R e ↔ z.eval q e := by
  obtain ⟨z,hz,he⟩ := (full_closure_exact q hq R).mp ⟨ho,hc⟩
  have hp := full_pass_necessary q hq R hg hc.2.1 hc.2.2.2
  have hzp : FullPass q (z.eval q) := by
    unfold FullPass at *
    simpa only [he] using hp
  exact ⟨.old z,⟨hz,(full_pass_classification q hq z hz).mp hzp⟩,he⟩

theorem full_new_normal (q : Nat) (hq : 4≤q) (R : Nat → Prop)
    (hg : Generated q R) (hc : CoreFull R) :
    ∃ z : NormalFull, z.Valid q ∧ ∀ e, R e ↔ z.eval q e := by
  classical
  by_cases hn1 : R (4*q-1)
  · exact full_old_retained q hq R hg (full_old_if_last q hq R hg hc hn1) hc
  · by_cases hn : R (4*q)
    · exact full_thin_normal q hq R hg hc hn1 hn
    · exact full_old_retained q hq R hg (full_old_if_neither q hq R hg hn1 hn) hc

theorem normal_full_generated (q : Nat) (hq : 4≤q) (z : NormalFull) (hz : z.Valid q) : Generated q (z.eval q) := by
  cases z with
  | old z => exact retained_full_generated q hq z hz
  | fresh z => exact add_full_generated q hq z hz

theorem normal_full_core (q : Nat) (hq : 4≤q) (z : NormalFull) (hz : z.Valid q) : CoreFull (z.eval q) := by
  cases z with
  | old z => exact NFFull.core q hq z hz.1
  | fresh z => exact add_full_core q hq z hz

theorem full_new_exhaustive (q : Nat) (hq : 4≤q) (R : Nat → Prop) :
    Generated q R ∧ CoreFull R ↔ ∃ z : NormalFull, z.Valid q ∧ ∀ e, R e ↔ z.eval q e := by
  constructor
  · exact fun h => full_new_normal q hq R h.1 h.2
  · rintro ⟨z,hz,he⟩
    refine ⟨generated_congr q (normal_full_generated q hq z hz) (fun e => (he e).symm),?_⟩
    have hc := normal_full_core q hq z hz
    unfold CoreFull at *
    rw [he 1,he 2,he 3,he 4]
    exact hc

theorem normal_full_unique (q : Nat) (hq : 4≤q) (z w : NormalFull) (hz : z.Valid q) (hw : w.Valid q)
    (he : ∀ e, z.eval q e ↔ w.eval q e) : z=w := by
  cases z with
  | old z =>
    cases w with
    | old w => exact congrArg NormalFull.old (NFFull.unique q hq z w hz.1 hw.1 he)
    | fresh w => exact False.elim (add_full_not_old q hq w hw
        (LuRazClosure.generated_congr q (NFFull.generated q hq z hz.1) he))
  | fresh z =>
    cases w with
    | old w => exact False.elim (add_full_not_old q hq z hz
        (LuRazClosure.generated_congr q (NFFull.generated q hq w hw.1) (fun e => (he e).symm)))
    | fresh w => exact congrArg NormalFull.fresh (add_full_unique q hq z w hz hw he)

end LuRazThreeRow
