import SixRowCore11Unique
import SixRowDifferencePredicates

namespace LuRazSixRowClosure
open LuRazClosure LuRazParametric LuRazEnumeration Difference
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false

def IsRemoved11 : RemovedForm → Prop
  | .r11j _ | .r11aj _ | .r11ak _ => True
  | _ => False

def IsAdded11 : AddedForm → Prop
  | .n11j _ | .n11aj _ | .n11ak _ => True
  | _ => False

theorem b11_of_eq (q : Nat) (hq : 4≤q) (R : Nat→Prop) (w : NF11)
    (hw : w.Valid q) (he : ∀e,R e↔w.eval q e) : Generated q R :=
  generated_congr q (NF11.generated q hq w hw) (fun e => (he e).symm)

theorem v11_of_eq (q : Nat) (hq : 4≤q) (R : Nat→Prop) (w : NF124)
    (hw : w.Valid q) (he : ∀e,R e↔w.eval q e) : LuRazThreeRow.Generated q R := by
  have hc := NF124.core q hq w hw
  have h3 : ¬R 3 := fun h => hc.2.2.1 ((he 3).mp h)
  exact (LuRazThreeRow.no_three_unchanged q hq R h3).mpr
    (LuRazClosure.generated_congr q (NF124.generated q hq w hw) (fun e => (he e).symm))

theorem old11_horn (q : Nat) (hq : 4≤q) (R : Nat→Prop)
    (hg : LuRazThreeRow.Generated q R) (hc : Core124 R) : R (4*q)→R (4*q-1) := by
  have hg := (LuRazThreeRow.no_three_unchanged q hq R hc.2.2.1).mp hg
  obtain ⟨w,hw,he⟩ := (core124_closure_exact q hq R).mp ⟨hg,hc⟩
  have hp : w.eval q (4*q)→w.eval q (4*q-1) := by
    cases w with
    | interval a k => simp [NF124.Valid] at hw; simp [NF124.eval,T124,I]; omega
    | agap a k => simp [NF124.Valid] at hw; simp [NF124.eval,T124,ARow,I]; omega
    | ak z => cases z <;> simp [NF124.eval,NF24.eval,ARow,K1Row,K2Row,LuRazClosure.BRow,DRow,I] <;> omega
  exact fun h => (he _).mpr (hp ((he _).mp h))

theorem new11_horn (q : Nat) (hq : 4≤q) (R : Nat→Prop)
    (hg : Generated q R) (hc : Core124 R) : R (4*q-1)→R (4*q) := by
  obtain ⟨w,hw,he⟩ := core11_normal q hq R hg hc
  have hp : w.eval q (4*q-1)→w.eval q (4*q) := by
    cases w with
    | interval a k => simp [NF11.Valid] at hw; simp [NF11.eval,Head11,Tail11,I]; omega
    | agap a k => simp [NF11.Valid] at hw; simp [NF11.eval,Head11,Tail11,ARow,I]; omega
    | ak k =>
      have hk : k=0∨k=1∨k=2∨k=3∨k=4 := by have : k<5 := hw; omega
      rcases hk with rfl|rfl|rfl|rfl|rfl <;>
        simp [NF11.eval,FixedPick11,ARow,K1Row,KPrime14,LuRazClosure.BRow,I] <;> omega
  exact fun h => (he _).mpr (hp ((he _).mp h))

theorem core11_old_partition (q : Nat) (hq : 4≤q) (R : Nat→Prop)
    (hg : LuRazThreeRow.Generated q R) (hc : Core124 R) :
    Generated q R ∨ ∃f : RemovedForm,f.Valid q ∧ IsRemoved11 f ∧ ∀e,R e↔f.eval q e := by
  have hg := (LuRazThreeRow.no_three_unchanged q hq R hc.2.2.1).mp hg
  obtain ⟨w,hw,he⟩ := (core124_closure_exact q hq R).mp ⟨hg,hc⟩
  cases w with
  | interval a k =>
    simp [NF124.Valid,NF11.Valid] at hw
    have hk : k=0∨k=1∨k=2 := by omega
    rcases hk with rfl|rfl|rfl
    · left
      apply b11_of_eq q hq R (.interval a 0) (by simp [NF11.Valid]; omega)
      intro e
      rw [he e]
      simp [NF11.eval,Head11,Tail11,FixedPick11,NF124.eval,NF24.eval,RemovedForm.eval,AddedForm.eval,Difference.A,ARow,K1Row,K2Row,KPrime14,LuRazClosure.BRow,T124,I]
      all_goals omega
    · right
      refine ⟨.r11j a,by simpa [RemovedForm.Valid] using hw.1,True.intro,?_⟩
      intro e
      rw [he e]
      simp [NF11.eval,Head11,Tail11,FixedPick11,NF124.eval,NF24.eval,RemovedForm.eval,AddedForm.eval,Difference.A,ARow,K1Row,K2Row,KPrime14,LuRazClosure.BRow,T124,I]
      all_goals omega
    · left
      apply b11_of_eq q hq R (.interval a 2) (by simp [NF11.Valid]; omega)
      intro e
      rw [he e]
      simp [NF11.eval,Head11,Tail11,FixedPick11,NF124.eval,NF24.eval,RemovedForm.eval,AddedForm.eval,Difference.A,ARow,K1Row,K2Row,KPrime14,LuRazClosure.BRow,T124,I]
      all_goals omega
  | agap a k =>
    simp [NF124.Valid,NF11.Valid] at hw
    have hk : k=0∨k=1∨k=2 := by omega
    rcases hk with rfl|rfl|rfl
    · left
      apply b11_of_eq q hq R (.agap a 0) (by simp [NF11.Valid]; omega)
      intro e
      rw [he e]
      simp [NF11.eval,Head11,Tail11,FixedPick11,NF124.eval,NF24.eval,RemovedForm.eval,AddedForm.eval,Difference.A,ARow,K1Row,K2Row,KPrime14,LuRazClosure.BRow,T124,I]
      all_goals omega
    · right
      refine ⟨.r11aj a,by simpa [RemovedForm.Valid] using hw.1,True.intro,?_⟩
      intro e
      rw [he e]
      simp [NF11.eval,Head11,Tail11,FixedPick11,NF124.eval,NF24.eval,RemovedForm.eval,AddedForm.eval,Difference.A,ARow,K1Row,K2Row,KPrime14,LuRazClosure.BRow,T124,I]
      all_goals omega
    · left
      apply b11_of_eq q hq R (.agap a 2) (by simp [NF11.Valid]; omega)
      intro e
      rw [he e]
      simp [NF11.eval,Head11,Tail11,FixedPick11,NF124.eval,NF24.eval,RemovedForm.eval,AddedForm.eval,Difference.A,ARow,K1Row,K2Row,KPrime14,LuRazClosure.BRow,T124,I]
      all_goals omega
  | ak z =>
    cases z with
    | k1 =>
      left
      apply b11_of_eq q hq R (.ak 0) (by simp [NF11.Valid])
      intro e
      rw [he e]
      simp [NF11.eval,Head11,Tail11,FixedPick11,NF124.eval,NF24.eval,RemovedForm.eval,AddedForm.eval,Difference.A,ARow,K1Row,K2Row,KPrime14,LuRazClosure.BRow,T124,I]
      all_goals omega
    | k2 =>
      right
      refine ⟨.r11ak (2*q+3),by simp [RemovedForm.Valid],True.intro,?_⟩
      intro e
      rw [he e]
      simp [NF11.eval,Head11,Tail11,FixedPick11,NF124.eval,NF24.eval,RemovedForm.eval,AddedForm.eval,Difference.A,ARow,K1Row,K2Row,KPrime14,LuRazClosure.BRow,T124,I]
      all_goals omega
    | joinK =>
      right
      refine ⟨.r11ak (2*q+2),by simp [RemovedForm.Valid],True.intro,?_⟩
      intro e
      rw [he e]
      simp [NF11.eval,Head11,Tail11,FixedPick11,NF124.eval,NF24.eval,RemovedForm.eval,AddedForm.eval,Difference.A,ARow,K1Row,K2Row,KPrime14,LuRazClosure.BRow,T124,I]
      all_goals omega
    | fill1 =>
      left
      apply b11_of_eq q hq R (.ak 3) (by simp [NF11.Valid])
      intro e
      rw [he e]
      simp [NF11.eval,Head11,Tail11,FixedPick11,NF124.eval,NF24.eval,RemovedForm.eval,AddedForm.eval,Difference.A,ARow,K1Row,K2Row,KPrime14,LuRazClosure.BRow,T124,I]
      all_goals omega
    | fill2 =>
      left
      apply b11_of_eq q hq R (.ak 4) (by simp [NF11.Valid])
      intro e
      rw [he e]
      simp [NF11.eval,Head11,Tail11,FixedPick11,NF124.eval,NF24.eval,RemovedForm.eval,AddedForm.eval,Difference.A,ARow,K1Row,K2Row,KPrime14,LuRazClosure.BRow,T124,I]
      all_goals omega
    | dBig => simp [NF124.Valid] at hw

theorem core11_new_partition (q : Nat) (hq : 4≤q) (R : Nat→Prop)
    (hg : Generated q R) (hc : Core124 R) :
    LuRazThreeRow.Generated q R ∨ ∃f : AddedForm,f.Valid q ∧ IsAdded11 f ∧ ∀e,R e↔f.eval q e := by
  obtain ⟨w,hw,he⟩ := core11_normal q hq R hg hc
  cases w with
  | interval a k =>
    simp [NF124.Valid,NF11.Valid] at hw
    have hk : k=0∨k=1∨k=2 := by omega
    rcases hk with rfl|rfl|rfl
    · left
      apply v11_of_eq q hq R (.interval a 0) (by simp [NF124.Valid]; omega)
      intro e
      rw [he e]
      simp [NF11.eval,Head11,Tail11,FixedPick11,NF124.eval,NF24.eval,RemovedForm.eval,AddedForm.eval,Difference.A,ARow,K1Row,K2Row,KPrime14,LuRazClosure.BRow,T124,I]
      all_goals omega
    · right
      refine ⟨.n11j a,by simpa [AddedForm.Valid] using hw.1,True.intro,?_⟩
      intro e
      rw [he e]
      simp [NF11.eval,Head11,Tail11,FixedPick11,NF124.eval,NF24.eval,RemovedForm.eval,AddedForm.eval,Difference.A,ARow,K1Row,K2Row,KPrime14,LuRazClosure.BRow,T124,I]
      all_goals omega
    · left
      apply v11_of_eq q hq R (.interval a 2) (by simp [NF124.Valid]; omega)
      intro e
      rw [he e]
      simp [NF11.eval,Head11,Tail11,FixedPick11,NF124.eval,NF24.eval,RemovedForm.eval,AddedForm.eval,Difference.A,ARow,K1Row,K2Row,KPrime14,LuRazClosure.BRow,T124,I]
      all_goals omega
  | agap a k =>
    simp [NF124.Valid,NF11.Valid] at hw
    have hk : k=0∨k=1∨k=2 := by omega
    rcases hk with rfl|rfl|rfl
    · left
      apply v11_of_eq q hq R (.agap a 0) (by simp [NF124.Valid]; omega)
      intro e
      rw [he e]
      simp [NF11.eval,Head11,Tail11,FixedPick11,NF124.eval,NF24.eval,RemovedForm.eval,AddedForm.eval,Difference.A,ARow,K1Row,K2Row,KPrime14,LuRazClosure.BRow,T124,I]
      all_goals omega
    · right
      refine ⟨.n11aj a,by simpa [AddedForm.Valid] using hw.1,True.intro,?_⟩
      intro e
      rw [he e]
      simp [NF11.eval,Head11,Tail11,FixedPick11,NF124.eval,NF24.eval,RemovedForm.eval,AddedForm.eval,Difference.A,ARow,K1Row,K2Row,KPrime14,LuRazClosure.BRow,T124,I]
      all_goals omega
    · left
      apply v11_of_eq q hq R (.agap a 2) (by simp [NF124.Valid]; omega)
      intro e
      rw [he e]
      simp [NF11.eval,Head11,Tail11,FixedPick11,NF124.eval,NF24.eval,RemovedForm.eval,AddedForm.eval,Difference.A,ARow,K1Row,K2Row,KPrime14,LuRazClosure.BRow,T124,I]
      all_goals omega
  | ak k =>
    have hk : k=0∨k=1∨k=2∨k=3∨k=4 := by have : k<5 := hw; omega
    rcases hk with rfl|rfl|rfl|rfl|rfl
    · left
      apply v11_of_eq q hq R (.ak .k1) (by simp [NF124.Valid])
      intro e
      rw [he e]
      simp [NF11.eval,Head11,Tail11,FixedPick11,NF124.eval,NF24.eval,RemovedForm.eval,AddedForm.eval,Difference.A,ARow,K1Row,K2Row,KPrime14,LuRazClosure.BRow,T124,I]
      all_goals omega
    · right
      refine ⟨.n11ak (2*q+3),by simp [AddedForm.Valid],True.intro,?_⟩
      intro e
      rw [he e]
      simp [NF11.eval,Head11,Tail11,FixedPick11,NF124.eval,NF24.eval,RemovedForm.eval,AddedForm.eval,Difference.A,ARow,K1Row,K2Row,KPrime14,LuRazClosure.BRow,T124,I]
      all_goals omega
    · right
      refine ⟨.n11ak (2*q+2),by simp [AddedForm.Valid],True.intro,?_⟩
      intro e
      rw [he e]
      simp [NF11.eval,Head11,Tail11,FixedPick11,NF124.eval,NF24.eval,RemovedForm.eval,AddedForm.eval,Difference.A,ARow,K1Row,K2Row,KPrime14,LuRazClosure.BRow,T124,I]
      all_goals omega
    · left
      apply v11_of_eq q hq R (.ak .fill1) (by simp [NF124.Valid])
      intro e
      rw [he e]
      simp [NF11.eval,Head11,Tail11,FixedPick11,NF124.eval,NF24.eval,RemovedForm.eval,AddedForm.eval,Difference.A,ARow,K1Row,K2Row,KPrime14,LuRazClosure.BRow,T124,I]
      all_goals omega
    · left
      apply v11_of_eq q hq R (.ak .fill2) (by simp [NF124.Valid])
      intro e
      rw [he e]
      simp [NF11.eval,Head11,Tail11,FixedPick11,NF124.eval,NF24.eval,RemovedForm.eval,AddedForm.eval,Difference.A,ARow,K1Row,K2Row,KPrime14,LuRazClosure.BRow,T124,I]
      all_goals omega

theorem removed11_generated (q : Nat) (hq : 4≤q) (f : RemovedForm)
    (hf : f.Valid q) (h11 : IsRemoved11 f) : LuRazThreeRow.Generated q (f.eval q) := by
  cases f <;> simp [IsRemoved11] at h11
  case r11j a =>
    apply v11_of_eq q hq _ (.interval a 1) (by simpa [NF124.Valid,RemovedForm.Valid] using And.intro hf (show 1<3 by decide))
    intro e
    simp [NF11.eval,Head11,Tail11,FixedPick11,NF124.eval,NF24.eval,RemovedForm.eval,AddedForm.eval,Difference.A,ARow,K1Row,K2Row,KPrime14,LuRazClosure.BRow,T124,I]
    all_goals omega
  case r11aj a =>
    apply v11_of_eq q hq _ (.agap a 1) (by simpa [NF124.Valid,RemovedForm.Valid] using And.intro hf (show 1<3 by decide))
    intro e
    simp [NF11.eval,Head11,Tail11,FixedPick11,NF124.eval,NF24.eval,RemovedForm.eval,AddedForm.eval,Difference.A,ARow,K1Row,K2Row,KPrime14,LuRazClosure.BRow,T124,I]
    all_goals omega
  case r11ak a =>
    have ha : a=2*q+2∨a=2*q+3 := hf
    rcases ha with rfl|rfl
    · apply v11_of_eq q hq _ (.ak .joinK) (by simp [NF124.Valid])
      intro e
      simp [NF11.eval,Head11,Tail11,FixedPick11,NF124.eval,NF24.eval,RemovedForm.eval,AddedForm.eval,Difference.A,ARow,K1Row,K2Row,KPrime14,LuRazClosure.BRow,T124,I]
      all_goals omega
    · apply v11_of_eq q hq _ (.ak .k2) (by simp [NF124.Valid])
      intro e
      simp [NF11.eval,Head11,Tail11,FixedPick11,NF124.eval,NF24.eval,RemovedForm.eval,AddedForm.eval,Difference.A,ARow,K1Row,K2Row,KPrime14,LuRazClosure.BRow,T124,I]
      all_goals omega

theorem removed11_not_new (q : Nat) (hq : 4≤q) (f : RemovedForm)
    (hf : f.Valid q) (h11 : IsRemoved11 f) : ¬Generated q (f.eval q) := by
  intro hg
  have hc : Core124 (f.eval q) := by
    cases f <;> simp [IsRemoved11] at h11 <;>
      simp_all [RemovedForm.Valid,RemovedForm.eval,Core124,Difference.A,I] <;> omega
  have hp := new11_horn q hq (f.eval q) hg hc
  cases f <;> simp [IsRemoved11] at h11 <;>
    simp_all [RemovedForm.Valid,RemovedForm.eval,Difference.A,I] <;> omega

theorem added11_generated (q : Nat) (hq : 4≤q) (f : AddedForm)
    (hf : f.Valid q) (h11 : IsAdded11 f) : Generated q (f.eval q) := by
  cases f <;> simp [IsAdded11] at h11
  case n11j a =>
    apply b11_of_eq q hq _ (.interval a 1) (by simpa [NF11.Valid,AddedForm.Valid] using And.intro hf (show 1<3 by decide))
    intro e
    simp [NF11.eval,Head11,Tail11,FixedPick11,NF124.eval,NF24.eval,RemovedForm.eval,AddedForm.eval,Difference.A,ARow,K1Row,K2Row,KPrime14,LuRazClosure.BRow,T124,I]
    all_goals omega
  case n11aj a =>
    apply b11_of_eq q hq _ (.agap a 1) (by simpa [NF11.Valid,AddedForm.Valid] using And.intro hf (show 1<3 by decide))
    intro e
    simp [NF11.eval,Head11,Tail11,FixedPick11,NF124.eval,NF24.eval,RemovedForm.eval,AddedForm.eval,Difference.A,ARow,K1Row,K2Row,KPrime14,LuRazClosure.BRow,T124,I]
    all_goals omega
  case n11ak a =>
    have ha : a=2*q+2∨a=2*q+3 := hf
    rcases ha with rfl|rfl
    · apply b11_of_eq q hq _ (.ak 2) (by simp [NF11.Valid])
      intro e
      simp [NF11.eval,Head11,Tail11,FixedPick11,NF124.eval,NF24.eval,RemovedForm.eval,AddedForm.eval,Difference.A,ARow,K1Row,K2Row,KPrime14,LuRazClosure.BRow,T124,I]
      all_goals omega
    · apply b11_of_eq q hq _ (.ak 1) (by simp [NF11.Valid])
      intro e
      simp [NF11.eval,Head11,Tail11,FixedPick11,NF124.eval,NF24.eval,RemovedForm.eval,AddedForm.eval,Difference.A,ARow,K1Row,K2Row,KPrime14,LuRazClosure.BRow,T124,I]
      all_goals omega

theorem added11_not_old (q : Nat) (hq : 4≤q) (f : AddedForm)
    (hf : f.Valid q) (h11 : IsAdded11 f) : ¬LuRazThreeRow.Generated q (f.eval q) := by
  intro hg
  have hc : Core124 (f.eval q) := by
    cases f <;> simp [IsAdded11] at h11 <;>
      simp_all [AddedForm.Valid,AddedForm.eval,Core124,Difference.A,I] <;> omega
  have hp := old11_horn q hq (f.eval q) hg hc
  cases f <;> simp [IsAdded11] at h11 <;>
    simp_all [AddedForm.Valid,AddedForm.eval,Difference.A,I] <;> omega

theorem core11_removed_exact (q : Nat) (hq : 4≤q) (R : Nat→Prop) (hc : Core124 R) :
    (LuRazThreeRow.Generated q R ∧ ¬Generated q R) ↔
    ∃f : RemovedForm,f.Valid q ∧ IsRemoved11 f ∧ ∀e,R e↔f.eval q e := by
  constructor
  · rintro ⟨hg,hn⟩
    rcases core11_old_partition q hq R hg hc with h|h
    · exact False.elim (hn h)
    · exact h
  · rintro ⟨f,hf,h11,he⟩
    refine ⟨LuRazThreeRow.generated_congr q (removed11_generated q hq f hf h11) (fun e => (he e).symm),?_⟩
    intro hg
    exact removed11_not_new q hq f hf h11 (generated_congr q hg he)

theorem core11_added_exact (q : Nat) (hq : 4≤q) (R : Nat→Prop) (hc : Core124 R) :
    (Generated q R ∧ ¬LuRazThreeRow.Generated q R) ↔
    ∃f : AddedForm,f.Valid q ∧ IsAdded11 f ∧ ∀e,R e↔f.eval q e := by
  constructor
  · rintro ⟨hg,hn⟩
    rcases core11_new_partition q hq R hg hc with h|h
    · exact False.elim (hn h)
    · exact h
  · rintro ⟨f,hf,h11,he⟩
    refine ⟨generated_congr q (added11_generated q hq f hf h11) (fun e => (he e).symm),?_⟩
    intro hg
    exact added11_not_old q hq f hf h11 (LuRazThreeRow.generated_congr q hg he)

end LuRazSixRowClosure
