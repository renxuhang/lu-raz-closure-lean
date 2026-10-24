import SixRowSmallClosure
import SixRowDifferencePredicates

namespace LuRazSixRowClosure
open LuRazClosure LuRazParametric Difference
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

def smallN4 (k : Nat) : Small.Normal := if k=0 then .c else .cb
def smallN5 : Nat → Small.Normal
  | 0 => .l | 1 => .ac | 2 => .cl | 3 => .zl | 4 => .cz | 5 => .lb | 6 => .acb | _ => .a

theorem small_n4_eval (q k : Nat) (hq : 4≤q) (hk : k≤1) (e : Nat) :
    (AddedForm.n4 k).eval q e ↔ (smallN4 k).eval q e := by
  have hc : k=0 ∨ k=1 := by omega
  rcases hc with rfl | rfl <;>
    simp [AddedForm.eval,smallN4,Small.Normal.eval,Small.SC,Small.SB,Cp,Ct,B,I] <;> omega

theorem small_n5_eval (q k : Nat) (hq : 4≤q) (hk : k≤6) (e : Nat) :
    (AddedForm.n5 k).eval q e ↔ (smallN5 k).eval q e := by
  have hc : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [AddedForm.eval,smallN5,Small.Normal.eval,Small.SA,Small.SB,Small.SC,Small.SZ,Small.SL,
      A,B,Cp,Ct,Lnew,Zp,I] <;> omega

theorem small_n4_generated (q k : Nat) (hq : 4≤q) (hk : k≤1) :
    Generated q ((AddedForm.n4 k).eval q) :=
  generated_congr q ((smallN4 k).generated q hq) (fun e => (small_n4_eval q k hq hk e).symm)

theorem small_n5_generated (q k : Nat) (hq : 4≤q) (hk : k≤6) :
    Generated q ((AddedForm.n5 k).eval q) :=
  generated_congr q ((smallN5 k).generated q hq) (fun e => (small_n5_eval q k hq hk e).symm)

theorem added4_generated (q : Nat) (hq : 4≤q) {R : Nat → Prop}
    (h : AddedAt q 4 R) : Generated q R := by
  obtain ⟨z,hz,hc,he⟩ := h
  cases z <;> simp only [AddedForm.core] at hc
  all_goals try omega
  exact generated_congr q (small_n4_generated q _ hq hz) he

theorem added5_generated (q : Nat) (hq : 4≤q) {R : Nat → Prop}
    (h : AddedAt q 5 R) : Generated q R := by
  obtain ⟨z,hz,hc,he⟩ := h
  cases z <;> simp only [AddedForm.core] at hc
  all_goals try omega
  exact generated_congr q (small_n5_generated q _ hq hz) he

theorem removed5_not_generated (q : Nat) (hq : 4≤q) :
    ¬Generated q ((RemovedForm.r5).eval q) := by
  intro hg
  have hsmall : ¬(RemovedForm.r5).eval q 2 ∧ ¬(RemovedForm.r5).eval q 4 := by
    simp [RemovedForm.eval,C,I] <;> omega
  obtain ⟨x,he⟩ := (Small.exhaustive q hq ((RemovedForm.r5).eval q)).mp ⟨hg,hsmall⟩
  have h1 := he 1
  have h3 := he 3
  have hm := he (2*q+2)
  have hn := he (4*q)
  have hnm := he (4*q-1)
  have hr := he (3*q+1)
  cases x <;>
    simp only [RemovedForm.eval,C,Small.Normal.eval,Small.SA,Small.SB,Small.SC,Small.SZ,Small.SL,I]
      at h1 h3 hm hn hnm hr <;> (simp_all <;> omega)

theorem generated5_not_removed (q : Nat) (hq : 4≤q) {R : Nat → Prop}
    (hg : Generated q R) : ¬RemovedAt q 5 R := by
  rintro ⟨z,hz,hc,he⟩
  cases z <;> simp only [RemovedForm.core] at hc
  all_goals try omega
  exact removed5_not_generated q hq (generated_congr q hg (fun e => (he e).symm))

theorem old4_removed_exact (q : Nat) (hq : 4≤q) (R : Nat → Prop) (hc : CoreMask 4 R) :
    LuRazThreeRow.Generated q R ↔ RemovedAt q 4 R := by
  have hh : ¬R 1 ∧ ¬R 2 ∧ R 3 ∧ ¬R 4 := by simpa [CoreMask] using hc
  constructor
  · intro hg
    have ho := (LuRazThreeRow.no_one_two_four_unchanged q hq R hh.1 hh.2.1 hh.2.2.2).mp hg
    have hcs : CoreSmallAt 4 R := by simpa [CoreSmallAt] using hh
    have hm := (small_members_exact q 4 hq R).mpr ⟨ho,hcs⟩
    simp [smallMembers,enumSmall,allSmall,NFSmall.tag,NFSmall.eval] at hm
    rcases hm with hm | hm
    · refine ⟨.r4 0,by simp [RemovedForm.Valid],rfl,?_⟩
      intro e
      rw [hm]
      simp [RemovedForm.eval,CRow,C,I]
    · refine ⟨.r4 1,by simp [RemovedForm.Valid],rfl,?_⟩
      intro e
      rw [hm]
      simp [RemovedForm.eval,CRow,LuRazClosure.BRow,C,B,I] <;> omega
  · rintro ⟨z,hz,hzc,he⟩
    cases z <;> simp only [RemovedForm.core] at hzc
    all_goals try omega
    rename_i k
    have hk : k=0 ∨ k=1 := by change k≤1 at hz; omega
    rcases hk with rfl | rfl
    · apply LuRazThreeRow.generated_congr q (LuRazThreeRow.generated_c q hq)
      intro e
      rw [←he e]
      simp [RemovedForm.eval,CRow,C,I]
    · apply LuRazThreeRow.generated_congr q
        (LuRazThreeRow.generated_join q (LuRazThreeRow.generated_c q hq) (LuRazThreeRow.generated_b q hq))
      intro e
      rw [←he e]
      simp [RemovedForm.eval,CRow,LuRazClosure.BRow,C,B,I] <;> omega

end LuRazSixRowClosure
