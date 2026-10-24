import SixRowCore13Normal

namespace LuRazSixRowClosure
open LuRazClosure LuRazParametric LuRazEnumeration
open Difference
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false

def IsRemoved13 : RemovedForm → Prop
  | .r13cj _ | .r13zj _ | .r13czj _ | .r13points _ => True
  | _ => False

def IsAdded13 : AddedForm → Prop
  | .n13plain _ | .n13isolated _ | .n13right _ => True
  | _ => False

theorem old13_horns (q : Nat) (hq : 4≤q) (R : Nat → Prop)
    (hg : LuRazThreeRow.Generated q R) (hc : Core134 R) :
    (R (3*q+1) ∨ R (4*q)) ∧ (R (4*q-1) → R (4*q)) := by
  obtain ⟨w,hw,he⟩ := (LuRazThreeRow.core134_exhaustive q hq R).mp ⟨hg,hc⟩
  have hp : (w.eval q (3*q+1) ∨ w.eval q (4*q)) ∧
      (w.eval q (4*q-1) → w.eval q (4*q)) := by
    cases w <;> rename_i z <;> cases z <;>
      simp_all [LuRazThreeRow.Normal134.Valid,LuRazThreeRow.Valid134,LuRazThreeRow.Cut134,
        NF134.Valid,LuRazThreeRow.Fresh134.Valid,LuRazThreeRow.Normal134.eval,
        NF134.eval,LuRazThreeRow.Fresh134.eval,T134,ZRow,ERow,LuRazClosure.BRow,I] <;> omega
  exact ⟨hp.1.elim (fun h => Or.inl ((he _).mpr h)) (fun h => Or.inr ((he _).mpr h)),
    fun h => (he _).mpr (hp.2 ((he _).mp h))⟩

theorem new13_horns (q : Nat) (hq : 4≤q) (R : Nat → Prop)
    (hg : Generated q R) (hc : Core134 R) :
    R (2*q+2) ∧ (R (4*q) → R (4*q-1)) ∧
    (R (3*q+1) → R (4*q-1) ∨ R (3*q)) := by
  obtain ⟨w,hw,he⟩ := core13_normal q hq R hg hc
  have hp : w.eval q (2*q+2) ∧ (w.eval q (4*q) → w.eval q (4*q-1)) ∧
      (w.eval q (3*q+1) → w.eval q (4*q-1) ∨ w.eval q (3*q)) := by
    cases w <;> simp_all [NF13.Valid,NF13.eval,T134,I] <;> omega
  exact ⟨(he _).mpr hp.1,fun h => (he _).mpr (hp.2.1 ((he _).mp h)),fun h =>
    (hp.2.2 ((he _).mp h)).elim (fun h => Or.inl ((he _).mpr h)) (fun h => Or.inr ((he _).mpr h))⟩

theorem b13_of_eq (q : Nat) (hq : 4≤q) (R : Nat → Prop) (w : NF13)
    (hw : w.Valid q) (he : ∀ e,R e ↔ w.eval q e) : Generated q R :=
  generated_congr q (NF13.generated q hq w hw) (fun e => (he e).symm)

theorem v13_of_eq (q : Nat) (hq : 4≤q) (R : Nat → Prop) (w : LuRazThreeRow.Normal134)
    (hw : w.Valid q) (he : ∀ e,R e ↔ w.eval q e) : LuRazThreeRow.Generated q R :=
  LuRazThreeRow.generated_congr q (LuRazThreeRow.normal134_generated q hq w hw)
    (fun e => (he e).symm)

theorem core13_old_partition (q : Nat) (hq : 4≤q) (R : Nat → Prop)
    (hg : LuRazThreeRow.Generated q R) (hc : Core134 R) :
    Generated q R ∨ ∃ f : RemovedForm,f.Valid q ∧ IsRemoved13 f ∧ ∀ e,R e ↔ f.eval q e := by
  obtain ⟨w,hw,he⟩ := (LuRazThreeRow.core134_exhaustive q hq R).mp ⟨hg,hc⟩
  cases w with
  | old z =>
    cases z with
    | ej a =>
      simp [LuRazThreeRow.Normal134.Valid,LuRazThreeRow.Valid134,LuRazThreeRow.Cut134,NF134.Valid] at hw
      left
      apply b13_of_eq q hq R (.full) (by simp [NF13.Valid] <;> omega)
      intro e
      rw [he e]
      simp [LuRazThreeRow.Normal134.eval,LuRazThreeRow.Normal134.Valid,LuRazThreeRow.Valid134,LuRazThreeRow.Cut134,NF134.Valid,NF134.eval,LuRazThreeRow.Fresh134.eval,NF13.Valid,NF13.eval,RemovedForm.Valid,RemovedForm.eval,IsRemoved13,T134,Lp,Difference.B,LuRazClosure.BRow,I]
      all_goals omega
    | aej a => simp [LuRazThreeRow.Normal134.Valid,LuRazThreeRow.Valid134,LuRazThreeRow.Cut134] at hw
    | extra k => simp [LuRazThreeRow.Normal134.Valid,LuRazThreeRow.Valid134,LuRazThreeRow.Cut134] at hw
    | cj b =>
      simp [LuRazThreeRow.Normal134.Valid,LuRazThreeRow.Valid134,LuRazThreeRow.Cut134,NF134.Valid] at hw
      by_cases hb : b≤3*q-1
      · right
        refine ⟨.r13cj b,by simp [RemovedForm.Valid] <;> omega,True.intro,?_⟩
        intro e
        rw [he e]
        simp [LuRazThreeRow.Normal134.eval,NF134.eval,RemovedForm.eval,T134]
        all_goals omega
      · left
        apply b13_of_eq q hq R (.plain b) (by simp [NF13.Valid] <;> omega)
        intro e
        rw [he e]
        simp [LuRazThreeRow.Normal134.eval,NF134.eval,NF13.eval,T134,I]
        all_goals omega
    | zj b =>
      simp [LuRazThreeRow.Normal134.Valid,LuRazThreeRow.Valid134,LuRazThreeRow.Cut134,NF134.Valid] at hw
      right
      refine ⟨.r13zj b,by simp [RemovedForm.Valid] <;> omega,True.intro,?_⟩
      intro e
      rw [he e]
      simp [LuRazThreeRow.Normal134.eval,LuRazThreeRow.Normal134.Valid,LuRazThreeRow.Valid134,LuRazThreeRow.Cut134,NF134.Valid,NF134.eval,LuRazThreeRow.Fresh134.eval,NF13.Valid,NF13.eval,RemovedForm.Valid,RemovedForm.eval,IsRemoved13,T134,Lp,Difference.B,LuRazClosure.BRow,I]
      all_goals omega
    | czj b =>
      simp [LuRazThreeRow.Normal134.Valid,LuRazThreeRow.Valid134,LuRazThreeRow.Cut134,NF134.Valid] at hw
      right
      refine ⟨.r13czj b,by simp [RemovedForm.Valid] <;> omega,True.intro,?_⟩
      intro e
      rw [he e]
      simp [LuRazThreeRow.Normal134.eval,LuRazThreeRow.Normal134.Valid,LuRazThreeRow.Valid134,LuRazThreeRow.Cut134,NF134.Valid,NF134.eval,LuRazThreeRow.Fresh134.eval,NF13.Valid,NF13.eval,RemovedForm.Valid,RemovedForm.eval,IsRemoved13,T134,Lp,Difference.B,LuRazClosure.BRow,I]
      all_goals omega
    | zjb b =>
      simp [LuRazThreeRow.Normal134.Valid,LuRazThreeRow.Valid134,LuRazThreeRow.Cut134,NF134.Valid] at hw
      left
      apply b13_of_eq q hq R (.withB b) (by simp [NF13.Valid] <;> omega)
      intro e
      rw [he e]
      simp [LuRazThreeRow.Normal134.eval,LuRazThreeRow.Normal134.Valid,LuRazThreeRow.Valid134,LuRazThreeRow.Cut134,NF134.Valid,NF134.eval,LuRazThreeRow.Fresh134.eval,NF13.Valid,NF13.eval,RemovedForm.Valid,RemovedForm.eval,IsRemoved13,T134,Lp,Difference.B,LuRazClosure.BRow,I]
      all_goals omega
    | cjb b =>
      simp [LuRazThreeRow.Normal134.Valid,LuRazThreeRow.Valid134,LuRazThreeRow.Cut134,NF134.Valid] at hw
      left
      apply b13_of_eq q hq R (.withC b) (by simp [NF13.Valid] <;> omega)
      intro e
      rw [he e]
      simp [LuRazThreeRow.Normal134.eval,LuRazThreeRow.Normal134.Valid,LuRazThreeRow.Valid134,LuRazThreeRow.Cut134,NF134.Valid,NF134.eval,LuRazThreeRow.Fresh134.eval,NF13.Valid,NF13.eval,RemovedForm.Valid,RemovedForm.eval,IsRemoved13,T134,Lp,Difference.B,LuRazClosure.BRow,I]
      all_goals omega
  | fresh z =>
    cases z with
    | lp =>
      right
      refine ⟨.r13points 0,by simp [RemovedForm.Valid],True.intro,?_⟩
      intro e
      rw [he e]
      simp [LuRazThreeRow.Normal134.eval,LuRazThreeRow.Fresh134.eval,RemovedForm.eval,Lp,Difference.B,LuRazClosure.BRow,T134,I]
      all_goals omega
    | lb =>
      right
      refine ⟨.r13points 1,by simp [RemovedForm.Valid],True.intro,?_⟩
      intro e
      rw [he e]
      simp [LuRazThreeRow.Normal134.eval,LuRazThreeRow.Fresh134.eval,RemovedForm.eval,Lp,Difference.B,LuRazClosure.BRow,T134,I]
      all_goals omega
    | zz b =>
      simp [LuRazThreeRow.Normal134.Valid,LuRazThreeRow.Fresh134.Valid] at hw
      by_cases hb : b=2*q+1
      · right
        refine ⟨.r13points 2,by simp [RemovedForm.Valid],True.intro,?_⟩
        intro e
        rw [he e]
        simp [LuRazThreeRow.Normal134.eval,LuRazThreeRow.Fresh134.eval,RemovedForm.eval,T134,I,hb]
      · left
        apply b13_of_eq q hq R (.double b) (by simp [NF13.Valid] <;> omega)
        intro e
        rw [he e]
        rfl
    | cz b =>
      simp [LuRazThreeRow.Normal134.Valid,LuRazThreeRow.Fresh134.Valid] at hw
      left
      apply b13_of_eq q hq R (.doubleIsolated b) hw
      intro e
      rw [he e]
      rfl

theorem core13_new_partition (q : Nat) (hq : 4≤q) (R : Nat → Prop)
    (hg : Generated q R) (hc : Core134 R) :
    LuRazThreeRow.Generated q R ∨ ∃ f : AddedForm,f.Valid q ∧ IsAdded13 f ∧ ∀ e,R e ↔ f.eval q e := by
  obtain ⟨w,hw,he⟩ := core13_normal q hq R hg hc
  cases w with
  | full =>
    simp [NF13.Valid] at hw
    left
    apply v13_of_eq q hq R (.old (.ej 5)) (by
      simp [LuRazThreeRow.Normal134.Valid,LuRazThreeRow.Valid134,LuRazThreeRow.Cut134,NF134.Valid,LuRazThreeRow.Fresh134.Valid]
      all_goals omega)
    intro e
    rw [he e]
    simp [NF13.eval,LuRazThreeRow.Normal134.eval,NF134.eval,LuRazThreeRow.Fresh134.eval,T134,I]
    all_goals omega
  | plain b =>
    simp [NF13.Valid] at hw
    by_cases hb : b≤3*q
    · right
      refine ⟨.n13plain b,by simp [AddedForm.Valid] <;> omega,True.intro,?_⟩
      intro e
      rw [he e]
      rfl
    · left
      apply v13_of_eq q hq R (.old (.cj b)) (by
        simp [LuRazThreeRow.Normal134.Valid,LuRazThreeRow.Valid134,LuRazThreeRow.Cut134,NF134.Valid]
        all_goals omega)
      intro e
      rw [he e]
      simp [NF13.eval,LuRazThreeRow.Normal134.eval,NF134.eval,T134,I]
      all_goals omega
  | last b =>
    right
    refine ⟨.n13right b,hw,True.intro,?_⟩
    intro e
    rw [he e]
    rfl
  | isolated b =>
    right
    refine ⟨.n13isolated b,hw,True.intro,?_⟩
    intro e
    rw [he e]
    rfl
  | double b =>
    simp [NF13.Valid] at hw
    left
    apply v13_of_eq q hq R (.fresh (.zz b)) (by
      simp [LuRazThreeRow.Normal134.Valid,LuRazThreeRow.Valid134,LuRazThreeRow.Cut134,NF134.Valid,LuRazThreeRow.Fresh134.Valid]
      all_goals omega)
    intro e
    rw [he e]
    simp [NF13.eval,LuRazThreeRow.Normal134.eval,NF134.eval,LuRazThreeRow.Fresh134.eval,T134,I]
    all_goals omega
  | doubleIsolated b =>
    simp [NF13.Valid] at hw
    left
    apply v13_of_eq q hq R (.fresh (.cz b)) (by
      simp [LuRazThreeRow.Normal134.Valid,LuRazThreeRow.Valid134,LuRazThreeRow.Cut134,NF134.Valid,LuRazThreeRow.Fresh134.Valid]
      all_goals omega)
    intro e
    rw [he e]
    simp [NF13.eval,LuRazThreeRow.Normal134.eval,NF134.eval,LuRazThreeRow.Fresh134.eval,T134,I]
    all_goals omega
  | withB b =>
    simp [NF13.Valid] at hw
    left
    apply v13_of_eq q hq R (.old (.zjb b)) (by
      simp [LuRazThreeRow.Normal134.Valid,LuRazThreeRow.Valid134,LuRazThreeRow.Cut134,NF134.Valid,LuRazThreeRow.Fresh134.Valid]
      all_goals omega)
    intro e
    rw [he e]
    simp [NF13.eval,LuRazThreeRow.Normal134.eval,NF134.eval,LuRazThreeRow.Fresh134.eval,T134,I]
    all_goals omega
  | withC b =>
    simp [NF13.Valid] at hw
    left
    apply v13_of_eq q hq R (.old (.cjb b)) (by
      simp [LuRazThreeRow.Normal134.Valid,LuRazThreeRow.Valid134,LuRazThreeRow.Cut134,NF134.Valid,LuRazThreeRow.Fresh134.Valid]
      all_goals omega)
    intro e
    rw [he e]
    simp [NF13.eval,LuRazThreeRow.Normal134.eval,NF134.eval,LuRazThreeRow.Fresh134.eval,T134,I]
    all_goals omega
theorem removed13_not_new (q : Nat) (hq : 4≤q) (f : RemovedForm)
    (hf : f.Valid q) (h13 : IsRemoved13 f) : ¬Generated q (f.eval q) := by
  intro hg
  have hc : Core134 (f.eval q) := by
    cases f <;> simp_all [IsRemoved13,RemovedForm.Valid,RemovedForm.eval,Core134,Lp,Difference.B,I] <;> omega
  have hh := new13_horns q hq (f.eval q) hg hc
  cases f <;> simp_all [IsRemoved13,RemovedForm.Valid,RemovedForm.eval,Lp,Difference.B,I] <;> omega

theorem added13_not_old (q : Nat) (hq : 4≤q) (f : AddedForm)
    (hf : f.Valid q) (h13 : IsAdded13 f) : ¬LuRazThreeRow.Generated q (f.eval q) := by
  intro hg
  have hc : Core134 (f.eval q) := by
    cases f <;> simp_all [IsAdded13,AddedForm.Valid,AddedForm.eval,Core134,I] <;> omega
  have hh := old13_horns q hq (f.eval q) hg hc
  cases f <;> simp_all [IsAdded13,AddedForm.Valid,AddedForm.eval,I] <;> omega


theorem added13_generated (q : Nat) (hq : 4≤q) (f : AddedForm)
    (hf : f.Valid q) (h13 : IsAdded13 f) : Generated q (f.eval q) := by
  cases f <;> simp [IsAdded13] at h13
  case n13plain b => exact b13_of_eq q hq _ (.plain b) (by unfold NF13.Valid; unfold AddedForm.Valid at hf; omega) (fun _ => Iff.rfl)
  case n13isolated b => exact b13_of_eq q hq _ (.isolated b) hf (fun _ => Iff.rfl)
  case n13right b => exact b13_of_eq q hq _ (.last b) hf (fun _ => Iff.rfl)

theorem removed13_old_generated (q : Nat) (hq : 4≤q) (f : RemovedForm)
    (hf : f.Valid q) (h13 : IsRemoved13 f) : LuRazThreeRow.Generated q (f.eval q) := by
  cases f <;> simp [IsRemoved13] at h13
  case r13cj b =>
    apply v13_of_eq q hq _ (.old (.cj b)) (by
      simp [LuRazThreeRow.Normal134.Valid,LuRazThreeRow.Valid134,LuRazThreeRow.Cut134,NF134.Valid,RemovedForm.Valid] at hf ⊢
      omega)
    intro e
    simp [RemovedForm.eval,LuRazThreeRow.Normal134.eval,NF134.eval,T134]
    all_goals omega
  case r13zj b =>
    apply v13_of_eq q hq _ (.old (.zj b)) (by
      simpa [LuRazThreeRow.Normal134.Valid,LuRazThreeRow.Valid134,LuRazThreeRow.Cut134,NF134.Valid,RemovedForm.Valid] using hf)
    intro e
    simp [RemovedForm.eval,LuRazThreeRow.Normal134.eval,NF134.eval,T134]
    all_goals omega
  case r13czj b =>
    apply v13_of_eq q hq _ (.old (.czj b)) (by
      simpa [LuRazThreeRow.Normal134.Valid,LuRazThreeRow.Valid134,LuRazThreeRow.Cut134,NF134.Valid,RemovedForm.Valid] using hf)
    intro e
    simp [RemovedForm.eval,LuRazThreeRow.Normal134.eval,NF134.eval,T134]
    all_goals omega
  case r13points k =>
    have hk : k=0 ∨ k=1 ∨ k=2 := by simp only [RemovedForm.Valid] at hf; omega
    rcases hk with rfl | rfl | rfl
    · apply v13_of_eq q hq _ (.fresh .lp) (by simp [LuRazThreeRow.Normal134.Valid,LuRazThreeRow.Fresh134.Valid])
      intro e
      simp [RemovedForm.eval,Lp,LuRazThreeRow.Normal134.eval,LuRazThreeRow.Fresh134.eval,T134,I]
      all_goals omega
    · apply v13_of_eq q hq _ (.fresh .lb) (by simp [LuRazThreeRow.Normal134.Valid,LuRazThreeRow.Fresh134.Valid])
      intro e
      simp [RemovedForm.eval,Lp,Difference.B,LuRazClosure.BRow,LuRazThreeRow.Normal134.eval,LuRazThreeRow.Fresh134.eval,T134,I]
      all_goals omega
    · apply v13_of_eq q hq _ (.fresh (.zz (2*q+1))) (by
        simp [LuRazThreeRow.Normal134.Valid,LuRazThreeRow.Fresh134.Valid]; omega)
      intro e
      simp [RemovedForm.eval,LuRazThreeRow.Normal134.eval,LuRazThreeRow.Fresh134.eval,T134,I]
      all_goals omega

theorem core13_removed_exact (q : Nat) (hq : 4≤q) (R : Nat → Prop) (hc : Core134 R) :
    (LuRazThreeRow.Generated q R ∧ ¬Generated q R) ↔
      ∃ f : RemovedForm,f.Valid q ∧ IsRemoved13 f ∧ ∀ e,R e ↔ f.eval q e := by
  constructor
  · rintro ⟨hg,hn⟩
    rcases core13_old_partition q hq R hg hc with h | h
    · exact False.elim (hn h)
    · exact h
  · rintro ⟨f,hf,h13,he⟩
    refine ⟨LuRazThreeRow.generated_congr q (removed13_old_generated q hq f hf h13)
      (fun e => (he e).symm),?_⟩
    intro hg
    exact removed13_not_new q hq f hf h13 (generated_congr q hg he)

theorem core13_added_exact (q : Nat) (hq : 4≤q) (R : Nat → Prop) (hc : Core134 R) :
    (Generated q R ∧ ¬LuRazThreeRow.Generated q R) ↔
      ∃ f : AddedForm,f.Valid q ∧ IsAdded13 f ∧ ∀ e,R e ↔ f.eval q e := by
  constructor
  · rintro ⟨hg,hn⟩
    rcases core13_new_partition q hq R hg hc with h | h
    · exact False.elim (hn h)
    · exact h
  · rintro ⟨f,hf,h13,he⟩
    refine ⟨generated_congr q (added13_generated q hq f hf h13) (fun e => (he e).symm),?_⟩
    intro hg
    exact added13_not_old q hq f hf h13 (LuRazThreeRow.generated_congr q hg he)

end LuRazSixRowClosure
