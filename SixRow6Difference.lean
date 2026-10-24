import SixRowLargeEnumeration
import SixRowDifferenceForms
namespace LuRazSixRowClosure
open LuRazClosure LuRazParametric Difference
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false
def IsRemoved6 : RemovedForm→Prop
  | .r6regular _ | .r6exception | .r6d _ => True | _ => False
def IsAdded6 : AddedForm→Prop
  | .n6regular _ | .n6exception | .n6e _ => True | _ => False
def NF6.Fresh : NF6→Prop | .lp _ _ | .filled => False | _ => True

theorem NF6.no_cut (q : Nat) (hq : 4≤q) (z : NF6) (hz : z.Valid q) : ¬z.eval q (2*q+2) := by
  cases z <;> simp only [NF6.Valid,P] at hz <;>
    simp only [NF6.eval,NF23.eval,LRow,LNormal,I,beta] <;>
    repeat first | omega | (simp_all <;> omega) | split
theorem core6_no_cut (q : Nat) (hq : 4≤q) (R : Nat→Prop)
    (hg : Generated q R) (hc : Core23 R) : ¬R (2*q+2) := by
  obtain ⟨z,hz,he⟩ := core6_normal q hq R hg hc
  exact fun h=>NF6.no_cut q hq z hz ((he _).mp h)

theorem fresh6_not_v (q : Nat) (hq : 4≤q) (z : NF6) (hz : z.Valid q) (hf : z.Fresh) :
    ¬LuRazThreeRow.Generated q (z.eval q) := by
  intro hg
  obtain ⟨w,hw,he⟩ := (LuRazThreeRow.core23_exact q hq _).mp ⟨hg,z.core q hq hz⟩
  have h1 := he (2*q+1)
  have h2 := he (2*q+2)
  have h3 := he (2*q+3)
  cases z <;> cases w <;>
    simp only [NF6.Fresh,NF6.Valid,LuRazThreeRow.Valid23,LuRazThreeRow.Avoid23,NF23.Valid,P] at hz hf hw <;>
    simp only [NF6.eval,NF23.eval,LRow,LNormal,I,beta] at h1 h2 h3 <;>
    repeat first | omega | (simp_all <;> omega) | split at h1 <;> split at h2 <;> split at h3

theorem removed6_old_generated (q : Nat) (hq : 4≤q) (f : RemovedForm)
    (hf : f.Valid q) (h6 : IsRemoved6 f) : LuRazThreeRow.Generated q (f.eval q) := by
  cases f <;> simp only [IsRemoved6] at h6
  case r6regular t =>
    have hh : P q t ∧ t≤2*q ∧ t≠q+3 := hf
    apply LuRazThreeRow.generated_congr q (LuRazThreeRow.normal23_generated q hq (.creg t) ⟨⟨hh.1,hh.2.2⟩,hh.2.1⟩)
    intro e; simp only [NF23.eval,RemovedForm.eval,C,Suffix,I,beta]
    repeat first | omega | (simp_all <;> omega) | split
  case r6exception =>
    apply LuRazThreeRow.generated_congr q (LuRazThreeRow.normal23_generated q hq .cexception ⟨True.intro,True.intro⟩)
    intro e; simp only [NF23.eval,RemovedForm.eval,C,I]; omega
  case r6d p =>
    have hp : p=0 ∨ (P q p ∧ p≤2*q-1) := hf
    rcases hp with hp|hp
    · subst p
      apply LuRazThreeRow.generated_congr q (LuRazThreeRow.normal23_generated q hq .full ⟨True.intro,True.intro⟩)
      intro e; simp [NF23.eval,RemovedForm.eval,or_assoc]
    · have hp0 := hp.1
      unfold P at hp0
      apply LuRazThreeRow.generated_congr q (LuRazThreeRow.normal23_generated q hq (.dgap p) ⟨hp,True.intro⟩)
      intro e; simp only [NF23.eval,RemovedForm.eval,I]
      omega
  all_goals contradiction

theorem removed6_cut (q : Nat) (hq : 4≤q) (f : RemovedForm) (hf : f.Valid q) (h6 : IsRemoved6 f) :
    f.eval q (2*q+2) := by
  cases f <;> simp only [IsRemoved6] at h6 <;>
    simp only [RemovedForm.Valid,P] at hf <;>
    simp only [RemovedForm.eval,C,Suffix,I] <;> simp_all <;> omega

theorem core6_old_partition (q : Nat) (hq : 4≤q) (R : Nat→Prop)
    (hg : LuRazThreeRow.Generated q R) (hc : Core23 R) :
    Generated q R ∨ ∃f : RemovedForm,f.Valid q ∧ IsRemoved6 f ∧ ∀e,R e ↔ f.eval q e := by
  obtain ⟨z,hz,he⟩ := (LuRazThreeRow.core23_exact q hq R).mp ⟨hg,hc⟩
  cases z with
  | lp t p =>
    left
    exact generated_congr q (NF6.generated q hq (.lp t p) ⟨hz.1.1,hz.1.2.1,hz.1.2.2,hz.2⟩) (fun e=>(he e).symm)
  | filledM =>
    exact Or.inl (generated_congr q (NF6.generated q hq .filled True.intro) (fun e=>(he e).symm))
  | dgap p =>
    right
    refine ⟨.r6d p,Or.inr hz.1,True.intro,?_⟩
    have hp := hz.1.1
    unfold P at hp
    intro e
    refine (he e).trans ?_
    simp only [NF23.eval,RemovedForm.eval,I]; omega
  | full => exact Or.inr ⟨.r6d 0,Or.inl rfl,True.intro,by intro e; simpa [NF23.eval,RemovedForm.eval,or_assoc] using he e⟩
  | creg t =>
    right
    refine ⟨.r6regular t,⟨hz.1.1,hz.2,hz.1.2⟩,True.intro,?_⟩
    intro e; refine (he e).trans ?_
    simp only [NF23.eval,RemovedForm.eval,C,Suffix,I,beta]
    repeat first | omega | (simp_all <;> omega) | split
  | cexception => exact Or.inr ⟨.r6exception,True.intro,True.intro,by
      intro e; refine (he e).trans ?_; simp only [NF23.eval,RemovedForm.eval,C,I]; omega⟩

theorem core6_removed_exact (q : Nat) (hq : 4≤q) (R : Nat→Prop) (hc : Core23 R) :
    (LuRazThreeRow.Generated q R ∧ ¬Generated q R) ↔
      ∃f : RemovedForm,f.Valid q ∧ IsRemoved6 f ∧ ∀e,R e ↔ f.eval q e := by
  constructor
  · rintro ⟨hg,hn⟩
    exact (core6_old_partition q hq R hg hc).elim (fun h=>False.elim (hn h)) id
  · rintro ⟨f,hf,ht,he⟩
    refine ⟨LuRazThreeRow.generated_congr q (removed6_old_generated q hq f hf ht) (fun e=>(he e).symm),?_⟩
    intro hg
    exact core6_no_cut q hq R hg hc ((he _).mpr (removed6_cut q hq f hf ht))

theorem added6_corresponds (q : Nat) (hq : 4≤q) (f : AddedForm)
    (hf : f.Valid q) (h6 : IsAdded6 f) :
    ∃z : NF6,z.Valid q ∧ z.Fresh ∧ ∀e,z.eval q e ↔ f.eval q e := by
  cases f <;> simp only [IsAdded6] at h6
  case n6regular t =>
    refine ⟨.creg t,hf,True.intro,?_⟩
    intro e; simp only [NF6.eval,AddedForm.eval,Ct,Suffix,I,beta]
    repeat first | omega | (simp_all <;> omega) | split
  case n6exception => exact ⟨.cex,True.intro,True.intro,by intro e; simp only [NF6.eval,AddedForm.eval,Ct,I]; omega⟩
  case n6e p => exact ⟨.er p,hf,True.intro,by intro e; simp only [NF6.eval,AddedForm.eval,or_assoc]⟩
  all_goals contradiction

theorem core6_new_partition (q : Nat) (hq : 4≤q) (R : Nat→Prop)
    (hg : Generated q R) (hc : Core23 R) :
    LuRazThreeRow.Generated q R ∨ ∃f : AddedForm,f.Valid q ∧ IsAdded6 f ∧ ∀e,R e ↔ f.eval q e := by
  obtain ⟨z,hz,he⟩ := core6_normal q hq R hg hc
  cases z with
  | lp t p => exact Or.inl (LuRazThreeRow.generated_congr q
      (LuRazThreeRow.normal23_generated q hq (.lp t p) ⟨⟨hz.1,hz.2.1,hz.2.2.1⟩,hz.2.2.2⟩) (fun e=>(he e).symm))
  | filled => exact Or.inl (LuRazThreeRow.generated_congr q
      (LuRazThreeRow.normal23_generated q hq .filledM ⟨True.intro,True.intro⟩) (fun e=>(he e).symm))
  | creg t =>
    right; refine ⟨.n6regular t,hz,True.intro,?_⟩
    intro e; refine (he e).trans ?_
    simp only [NF6.eval,AddedForm.eval,Ct,Suffix,I,beta]
    repeat first | omega | (simp_all <;> omega) | split
  | cex => exact Or.inr ⟨.n6exception,True.intro,True.intro,by
      intro e; refine (he e).trans ?_; simp only [NF6.eval,AddedForm.eval,Ct,I]; omega⟩
  | er p => exact Or.inr ⟨.n6e p,hz,True.intro,by
      intro e; refine (he e).trans ?_; simp only [NF6.eval,AddedForm.eval,or_assoc]⟩

theorem core6_added_exact (q : Nat) (hq : 4≤q) (R : Nat→Prop) (hc : Core23 R) :
    (Generated q R ∧ ¬LuRazThreeRow.Generated q R) ↔
      ∃f : AddedForm,f.Valid q ∧ IsAdded6 f ∧ ∀e,R e ↔ f.eval q e := by
  constructor
  · rintro ⟨hg,hn⟩
    exact (core6_new_partition q hq R hg hc).elim (fun h=>False.elim (hn h)) id
  · rintro ⟨f,hf,ht,he⟩
    obtain ⟨z,hz,hfresh,hze⟩ := added6_corresponds q hq f hf ht
    have hez : ∀e,z.eval q e ↔ R e := fun e=>(hze e).trans (he e).symm
    refine ⟨generated_congr q (z.generated q hq hz) hez,?_⟩
    intro hv
    exact fresh6_not_v q hq z hz hfresh
      (LuRazThreeRow.generated_congr q hv (fun e=>(hez e).symm))
end LuRazSixRowClosure
