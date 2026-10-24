import SixRowCore14Exact
import SixRowDifferenceForms

namespace LuRazSixRowClosure
open LuRazClosure LuRazParametric LuRazEnumeration Difference
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false

def IsRemoved14 : RemovedForm → Prop
  | .r14points _ | .r14line _ | .r14c _ => True | _ => False

theorem b14_of_eq (q : Nat) (hq : 4≤q) (R : Nat → Prop) (w : NF234)
    (hw : w.Valid q) (hcut : Cut14 w) (he : ∀ e,R e ↔ w.eval q e) : Generated q R :=
  generated_congr q (normal14_retained_generated q hq w hw hcut) (fun e => (he e).symm)

theorem v14_of_eq (q : Nat) (hq : 4≤q) (R : Nat → Prop) (w : NF234)
    (hw : w.Valid q) (he : ∀ e,R e ↔ w.eval q e) : LuRazThreeRow.Generated q R :=
  LuRazThreeRow.generated_congr q
    (LuRazThreeRow.old234_in_new q hq (w.eval q) (NF234.generated q hq w hw) (NF234.core q hq w hw))
    (fun e => (he e).symm)

theorem core14_old_partition (q : Nat) (hq : 4≤q) (R : Nat → Prop)
    (hg : LuRazThreeRow.Generated q R) (hc : Core234 R) :
    Generated q R ∨ ∃ f : RemovedForm,f.Valid q ∧ IsRemoved14 f ∧ ∀ e,R e ↔ f.eval q e := by
  rcases (LuRazThreeRow.core234_exact q hq R).mp ⟨hg,hc⟩ with ⟨ho,_⟩ | ⟨z,hz,he⟩
  · obtain ⟨w,hw,he⟩ := (core234_closure_exact q hq R).mp ⟨ho,hc⟩
    classical
    by_cases hcut : Cut14 w
    · exact Or.inl (b14_of_eq q hq R w hw hcut he)
    · right
      cases w <;> simp [Cut14] at hcut
      case km k =>
        have hk : k=1 := by simp only [NF234.Valid] at hw; omega
        subst k
        refine ⟨.r14points 1,by simp [RemovedForm.Valid],True.intro,?_⟩
        intro e
        rw [he e]
        simp [NF234.eval,RemovedForm.eval,T234]
        all_goals omega
      case ck k =>
        have hk : k=0 := by simp only [NF234.Valid] at hw; omega
        subst k
        refine ⟨.r14points 0,by simp [RemovedForm.Valid],True.intro,?_⟩
        intro e
        rw [he e]
        simp [NF234.eval,RemovedForm.eval,T234]
        all_goals omega
      case last =>
        refine ⟨.r14points 2,by simp [RemovedForm.Valid],True.intro,?_⟩
        intro e
        rw [he e]
        simp [NF234.eval,RemovedForm.eval,T234]
        all_goals omega
  · right
    cases z <;> simp [LuRazThreeRow.Extra234] at hz
    case lp t p =>
      obtain ⟨ht,hts,rfl⟩ := hz
      have hbt : 2*q+4≤beta q t ∧ beta q t≤4*q-1 := by
        unfold beta
        unfold P at ht
        split <;> omega
      refine ⟨.r14line (beta q t),hbt,True.intro,?_⟩
      intro e
      rw [he e]
      simp only [LuRazThreeRow.Four,NF23.eval,LRow,LNormal,RemovedForm.eval,I]
      split <;> omega
    case creg t =>
      obtain ⟨ht,hts,hte⟩ := hz
      have hbt : 2*q+4≤beta q t ∧ beta q t≤4*q-1 ∧ beta q t≠3*q+2 := by
        unfold beta
        unfold P at ht
        split <;> omega
      refine ⟨.r14c (beta q t),hbt,True.intro,?_⟩
      intro e
      rw [he e]
      simp [LuRazThreeRow.Four,NF23.eval,RemovedForm.eval,Difference.C,I]
      all_goals omega

theorem removed14_not_new (q : Nat) (hq : 4≤q) (f : RemovedForm)
    (hf : f.Valid q) (h14 : IsRemoved14 f) : ¬Generated q (f.eval q) := by
  intro hg
  have hc : Core234 (f.eval q) := by
    cases f <;> simp_all [IsRemoved14,RemovedForm.Valid,RemovedForm.eval,Core234,Difference.C,I] <;> omega
  have hh := core14_horns q hq (f.eval q) hg hc
  cases f <;> simp_all [IsRemoved14,RemovedForm.Valid,RemovedForm.eval,Difference.C,I] <;> omega

theorem removed14_old_generated (q : Nat) (hq : 4≤q) (f : RemovedForm)
    (hf : f.Valid q) (h14 : IsRemoved14 f) : LuRazThreeRow.Generated q (f.eval q) := by
  cases f <;> simp [IsRemoved14] at h14
  case r14points k =>
    have hk : k=0 ∨ k=1 ∨ k=2 := by simp only [RemovedForm.Valid] at hf; omega
    rcases hk with rfl | rfl | rfl
    · apply v14_of_eq q hq _ (.ck 0) (by simp [NF234.Valid])
      intro e
      simp [RemovedForm.eval,NF234.eval,T234]
      all_goals omega
    · apply v14_of_eq q hq _ (.km 1) (by simp [NF234.Valid])
      intro e
      simp [RemovedForm.eval,NF234.eval,T234]
      all_goals omega
    · apply v14_of_eq q hq _ .last True.intro
      intro e
      simp [RemovedForm.eval,NF234.eval,T234]
      all_goals omega
  case r14line b =>
    have hb := hf
    simp only [RemovedForm.Valid] at hb
    obtain ⟨p,hp,hbp⟩ := beta_surjective q b hq ⟨hb.1,by omega⟩
    have hps : p≤2*q := by
      unfold beta at hbp
      unfold P at hp
      split at hbp <;> omega
    apply LuRazThreeRow.generated_congr q
      (LuRazThreeRow.extra234_generated q hq (.lp p (2*q+1)) ⟨hp,hps,rfl⟩)
    intro e
    simp only [LuRazThreeRow.Four,NF23.eval,LRow,LNormal,RemovedForm.eval,I,hbp]
    split <;> omega
  case r14c b =>
    have hb := hf
    simp only [RemovedForm.Valid] at hb
    obtain ⟨p,hp,hbp⟩ := beta_surjective q b hq ⟨hb.1,by omega⟩
    have hps : p≤2*q ∧ p≠q+3 := by
      unfold beta at hbp
      unfold P at hp
      split at hbp <;> omega
    apply LuRazThreeRow.generated_congr q
      (LuRazThreeRow.extra234_generated q hq (.creg p) ⟨hp,hps.1,hps.2⟩)
    intro e
    simp [LuRazThreeRow.Four,NF23.eval,RemovedForm.eval,Difference.C,I,hbp]
    all_goals omega

theorem core14_removed_exact (q : Nat) (hq : 4≤q) (R : Nat → Prop) (hc : Core234 R) :
    (LuRazThreeRow.Generated q R ∧ ¬Generated q R) ↔
      ∃ f : RemovedForm,f.Valid q ∧ IsRemoved14 f ∧ ∀ e,R e ↔ f.eval q e := by
  constructor
  · rintro ⟨hg,hn⟩
    rcases core14_old_partition q hq R hg hc with h | h
    · exact False.elim (hn h)
    · exact h
  · rintro ⟨f,hf,h14,he⟩
    refine ⟨LuRazThreeRow.generated_congr q (removed14_old_generated q hq f hf h14)
      (fun e => (he e).symm),?_⟩
    intro hg
    exact removed14_not_new q hq f hf h14 (generated_congr q hg he)

theorem core14_no_added (q : Nat) (hq : 4≤q) (R : Nat → Prop) (hc : Core234 R) :
    ¬(Generated q R ∧ ¬LuRazThreeRow.Generated q R) := by
  rintro ⟨hg,hn⟩
  exact hn (core14_old q hq R hg hc)

end LuRazSixRowClosure
