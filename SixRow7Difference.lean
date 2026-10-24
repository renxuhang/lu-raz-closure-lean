import SixRow7Invariants
import SixRowDifferenceForms
namespace LuRazSixRowClosure
open LuRazClosure LuRazParametric Difference
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false
def IsRemoved7 : RemovedForm→Prop
  | .r7fresh _ | .r7e _ | .r7d _ => True | _ => False
def IsAdded7 : AddedForm→Prop
  | .n7regular _ | .n7exception | .n7right _ | .n7point => True | _ => False

theorem removed7_old_generated (q : Nat) (hq : 4≤q) (f : RemovedForm)
    (hf : f.Valid q) (h7 : IsRemoved7 f) : LuRazThreeRow.Generated q (f.eval q) := by
  cases f <;> simp only [IsRemoved7] at h7
  case r7fresh k =>
    have hk : k=0 ∨ k=1 ∨ k=2 := by have hh : k≤2 := hf; omega
    rcases hk with hk|hk|hk <;> subst k
    · apply LuRazThreeRow.generated_congr q (LuRazThreeRow.fresh123_generated q hq .e)
      intro e; simp only [LuRazThreeRow.Fresh123.eval,LuRazThreeRow.EPrime,RemovedForm.eval,Ep,I] <;> simp_all <;> omega
    · apply LuRazThreeRow.generated_congr q (LuRazThreeRow.fresh123_generated q hq .ae)
      intro e; simp only [LuRazThreeRow.Fresh123.eval,LuRazThreeRow.EPrime,ARow,RemovedForm.eval,A,Ep,I] <;> simp_all <;> omega
    · apply LuRazThreeRow.generated_congr q (LuRazThreeRow.fresh123_generated q hq .ce)
      intro e; simp only [LuRazThreeRow.Fresh123.eval,LuRazThreeRow.EPrime,CRow,RemovedForm.eval,Ep,I] <;> simp_all <;> omega
  case r7e p =>
    have hp : 4≤p ∧ p≤q+1 := hf
    apply LuRazThreeRow.generated_congr q (LuRazThreeRow.retained123_generated q hq (.er p) ⟨by change 4≤p ∧ p≤2*q+1; omega,by change p≤2*q; omega⟩)
    intro e; simp only [NF123.eval,NF123.body,TwoPiece,RemovedForm.eval,or_assoc]
  case r7d p =>
    have hp : 4≤p ∧ p≤2*q-1 := hf
    by_cases hl : p≤q+1
    · apply LuRazThreeRow.generated_congr q (LuRazThreeRow.retained123_generated q hq (.ed p) ⟨⟨hp.1,hl⟩,True.intro⟩)
      intro e; simp only [NF123.eval,NF123.body,TwoPiece,RemovedForm.eval,or_assoc]
    · apply LuRazThreeRow.generated_congr q (LuRazThreeRow.retained123_generated q hq (.dg p) ⟨⟨by omega,hp.2⟩,True.intro⟩)
      intro e; simp only [NF123.eval,NF123.body,TwoPiece,RemovedForm.eval,or_assoc]
  all_goals contradiction

theorem removed7_obstructs (q : Nat) (hq : 4≤q) (f : RemovedForm) (hf : f.Valid q) (h7 : IsRemoved7 f) :
    ¬(f.eval q (4*q-1) ∧ f.eval q (q+2) ∧
      (f.eval q (2*q+1) → f.eval q (2*q))) := by
  cases f <;> simp only [IsRemoved7] at h7 <;>
    simp only [RemovedForm.Valid] at hf <;>
    simp only [RemovedForm.eval,A,Ep,I] <;> simp_all <;> omega

theorem core7_old_partition (q : Nat) (hq : 4≤q) (R : Nat→Prop)
    (hg : LuRazThreeRow.Generated q R) (hc : Core123 R) :
    Generated q R ∨ ∃f : RemovedForm,f.Valid q ∧ IsRemoved7 f ∧ ∀e,R e ↔ f.eval q e := by
  rcases (LuRazThreeRow.core123_exhaustive q hq R).mp ⟨hg,hc⟩ with ⟨z,hz,he⟩|⟨z,he⟩
  · have hzv := hz.1
    have hzc := hz.2
    cases z with
    | low t => exact Or.inl (generated_congr q (NF7.generated q hq (.old (.low t)) ⟨hzv,True.intro⟩) (fun e=>(he e).symm))
    | high t p => exact Or.inl (generated_congr q (NF7.generated q hq (.old (.high t p)) ⟨hzv,hzc⟩) (fun e=>(he e).symm))
    | filled => exact Or.inl (generated_congr q (NF7.generated q hq (.old .filled) ⟨hzv,True.intro⟩) (fun e=>(he e).symm))
    | full => exact Or.inl (generated_congr q (NF7.generated q hq (.old .full) ⟨hzv,True.intro⟩) (fun e=>(he e).symm))
    | creg t => exact Or.inl (generated_congr q (NF7.generated q hq (.old (.creg t)) ⟨hzv,hzc⟩) (fun e=>(he e).symm))
    | cex => exact Or.inl (generated_congr q (NF7.generated q hq (.old .cex) ⟨hzv,True.intro⟩) (fun e=>(he e).symm))
    | dg p =>
      right
      have hp : q+2≤p ∧ p≤2*q-1 := hzv
      refine ⟨.r7d p,⟨by omega,hp.2⟩,True.intro,?_⟩
      intro e; simpa only [NF123.eval,NF123.body,TwoPiece,RemovedForm.eval,or_assoc] using he e
    | ed p =>
      right
      have hp : 4≤p ∧ p≤q+1 := hzv
      refine ⟨.r7d p,⟨hp.1,by omega⟩,True.intro,?_⟩
      intro e; simpa only [NF123.eval,NF123.body,TwoPiece,RemovedForm.eval,or_assoc] using he e
    | er p =>
      have hp : 4≤p ∧ p≤2*q+1 := hzv
      have hph : p≤2*q := hzc
      by_cases hl : p≤q+1
      · right; refine ⟨.r7e p,⟨hp.1,hl⟩,True.intro,?_⟩
        intro e; simpa only [NF123.eval,NF123.body,TwoPiece,RemovedForm.eval,or_assoc] using he e
      · exact Or.inl (generated_congr q (NF7.generated q hq (.old (.er p)) ⟨hzv,by change q+2≤p ∧ p≤2*q; omega⟩) (fun e=>(he e).symm))
  · right
    cases z with
    | e =>
      refine ⟨.r7fresh 0,by change 0≤2; omega,True.intro,?_⟩
      intro e; refine (he e).trans ?_
      simp only [LuRazThreeRow.Fresh123.eval,LuRazThreeRow.EPrime,RemovedForm.eval,Ep,I] <;> simp_all <;> omega
    | ae =>
      refine ⟨.r7fresh 1,by change 1≤2; omega,True.intro,?_⟩
      intro e; refine (he e).trans ?_
      simp only [LuRazThreeRow.Fresh123.eval,LuRazThreeRow.EPrime,ARow,RemovedForm.eval,A,Ep,I] <;> simp_all <;> omega
    | ce =>
      refine ⟨.r7fresh 2,by change 2≤2; omega,True.intro,?_⟩
      intro e; refine (he e).trans ?_
      simp only [LuRazThreeRow.Fresh123.eval,LuRazThreeRow.EPrime,CRow,RemovedForm.eval,Ep,I] <;> simp_all <;> omega

theorem core7_removed_exact (q : Nat) (hq : 4≤q) (R : Nat→Prop) (hc : Core123 R) :
    (LuRazThreeRow.Generated q R ∧ ¬Generated q R) ↔
      ∃f : RemovedForm,f.Valid q ∧ IsRemoved7 f ∧ ∀e,R e ↔ f.eval q e := by
  constructor
  · rintro ⟨hg,hn⟩
    exact (core7_old_partition q hq R hg hc).elim (fun h=>False.elim (hn h)) id
  · rintro ⟨f,hf,ht,he⟩
    refine ⟨LuRazThreeRow.generated_congr q (removed7_old_generated q hq f hf ht) (fun e=>(he e).symm),?_⟩
    intro hg
    have hh := core7_cut_conditions q hq R hg hc
    exact removed7_obstructs q hq f hf ht
      ⟨(he _).mp hh.1,(he _).mp hh.2.1,fun h=>(he _).mp (hh.2.2 ((he _).mpr h))⟩

theorem added7_corresponds (q : Nat) (hq : 4≤q) (f : AddedForm)
    (hf : f.Valid q) (h7 : IsAdded7 f) :
    ∃z : NF7,z.Valid q ∧ z.Fresh ∧ ∀e,z.eval q e ↔ f.eval q e := by
  cases f <;> simp only [IsAdded7] at h7
  case n7regular t =>
    refine ⟨.creg t,hf,True.intro,?_⟩
    intro e; simp only [NF7.eval,NF6.eval,AddedForm.eval,Ct,Suffix,I,beta]
    repeat first | omega | (simp_all <;> omega) | split
  case n7exception => exact ⟨.cex,True.intro,True.intro,by
      intro e; simp only [NF7.eval,NF6.eval,AddedForm.eval,Ct,I]; omega⟩
  case n7point => exact ⟨.point,True.intro,True.intro,by
      intro e; simp only [NF7.eval,AddedForm.eval,or_assoc]⟩
  case n7right t =>
    have ht : t=0 ∨ (3*q+2≤t ∧ t≤4*q-1) := hf
    rcases ht with ht|ht
    · subst t
      exact ⟨.rex,True.intro,True.intro,by intro e; simp only [NF7.eval,AddedForm.eval,Lnew,I] <;> simp_all <;> omega⟩
    · refine ⟨.right t,ht,True.intro,?_⟩
      intro e; simp only [NF7.eval,AddedForm.eval,Lnew,I]; omega
  all_goals contradiction

theorem core7_new_partition (q : Nat) (hq : 4≤q) (R : Nat→Prop)
    (hg : Generated q R) (hc : Core123 R) :
    LuRazThreeRow.Generated q R ∨ ∃f : AddedForm,f.Valid q ∧ IsAdded7 f ∧ ∀e,R e ↔ f.eval q e := by
  obtain ⟨z,hz,he⟩ := core7_normal q hq R hg hc
  cases z with
  | old z => exact Or.inl (LuRazThreeRow.generated_congr q
      (LuRazThreeRow.retained123_generated q hq z ⟨hz.1,keep7_cut123 q z hz.2⟩) (fun e=>(he e).symm))
  | creg t =>
    right; refine ⟨.n7regular t,hz,True.intro,?_⟩
    intro e; refine (he e).trans ?_
    simp only [NF7.eval,NF6.eval,AddedForm.eval,Ct,Suffix,I,beta]
    repeat first | omega | (simp_all <;> omega) | split
  | cex => exact Or.inr ⟨.n7exception,True.intro,True.intro,by
      intro e; refine (he e).trans ?_; simp only [NF7.eval,NF6.eval,AddedForm.eval,Ct,I]; omega⟩
  | right c =>
    right
    have hc : 3*q+2≤c ∧ c≤4*q-1 := hz
    refine ⟨.n7right c,Or.inr hc,True.intro,?_⟩
    intro e; refine (he e).trans ?_; simp only [NF7.eval,AddedForm.eval,Lnew,I]; omega
  | rex => exact Or.inr ⟨.n7right 0,Or.inl rfl,True.intro,by
      intro e; refine (he e).trans ?_; simp only [NF7.eval,AddedForm.eval,Lnew,I] <;> simp_all <;> omega⟩
  | point => exact Or.inr ⟨.n7point,True.intro,True.intro,by
      intro e; refine (he e).trans ?_; simp only [NF7.eval,AddedForm.eval,or_assoc]⟩

theorem core7_added_exact (q : Nat) (hq : 4≤q) (R : Nat→Prop) (hc : Core123 R) :
    (Generated q R ∧ ¬LuRazThreeRow.Generated q R) ↔
      ∃f : AddedForm,f.Valid q ∧ IsAdded7 f ∧ ∀e,R e ↔ f.eval q e := by
  constructor
  · rintro ⟨hg,hn⟩
    exact (core7_new_partition q hq R hg hc).elim (fun h=>False.elim (hn h)) id
  · rintro ⟨f,hf,ht,he⟩
    obtain ⟨z,hz,hfresh,hze⟩ := added7_corresponds q hq f hf ht
    have hez : ∀e,z.eval q e ↔ R e := fun e=>(hze e).trans (he e).symm
    refine ⟨generated_congr q (z.generated q hq hz) hez,?_⟩
    intro hv
    exact fresh7_not_v q hq z hz hfresh
      (LuRazThreeRow.generated_congr q hv (fun e=>(hez e).symm))
end LuRazSixRowClosure
