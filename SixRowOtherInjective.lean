import SixRowDifferenceForms

namespace LuRazSixRowClosure.Difference
open LuRazClosure
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

theorem r6d_injective (q p u : Nat) (hq : 4≤q)
    (hp : RemovedForm.Valid q (.r6d p)) (hu : RemovedForm.Valid q (.r6d u))
    (he : ∀e,RemovedForm.eval q (.r6d p) e ↔ RemovedForm.eval q (.r6d u) e) : p=u := by
  by_cases hp0 : p=0
  · by_cases hu0 : u=0
    · omega
    · have h := he (2*q)
      simp only [RemovedForm.eval,I,RemovedForm.Valid,P] at h hp hu
      simp_all <;> omega
  · by_cases hu0 : u=0
    · have h := he (2*q)
      simp only [RemovedForm.eval,I,RemovedForm.Valid,P] at h hp hu
      simp_all <;> omega
    · have hpv : P q p ∧ p≤2*q-1 := by
        rcases hp with h|h
        · exact False.elim (hp0 h)
        · exact h
      have huv : P q u ∧ u≤2*q-1 := by
        rcases hu with h|h
        · exact False.elim (hu0 h)
        · exact h
      have ep (e : Nat) : RemovedForm.eval q (.r6d p) e ↔ NF23.eval q (.dgap p) e := by
        simp [RemovedForm.eval,NF23.eval,hp0,or_assoc]
      have eu (e : Nat) : RemovedForm.eval q (.r6d u) e ↔ NF23.eval q (.dgap u) e := by
        simp [RemovedForm.eval,NF23.eval,hu0,or_assoc]
      have hh := NF23.unique q hq (.dgap p) (.dgap u) hpv huv
        (fun e=>(ep e).symm.trans ((he e).trans (eu e)))
      exact NF23.dgap.inj hh

theorem n7right_injective (q t u : Nat) (hq : 4≤q)
    (ht : AddedForm.Valid q (.n7right t)) (hu : AddedForm.Valid q (.n7right u))
    (he : ∀e,AddedForm.eval q (.n7right t) e ↔ AddedForm.eval q (.n7right u) e) : t=u := by
  by_cases ht0 : t=0
  · by_cases hu0 : u=0
    · omega
    · have h := he (4*q)
      simp only [AddedForm.eval,AddedForm.Valid,Lnew,I] at h ht hu
      simp_all <;> omega
  · by_cases hu0 : u=0
    · have h := he (4*q)
      simp only [AddedForm.eval,AddedForm.Valid,Lnew,I] at h ht hu
      simp_all <;> omega
    · have htv : 3*q+2≤t ∧ t≤4*q-1 := by rcases ht with h|h; exact False.elim (ht0 h); exact h
      have huv : 3*q+2≤u ∧ u≤4*q-1 := by rcases hu with h|h; exact False.elim (hu0 h); exact h
      apply Classical.byContradiction; intro hne
      by_cases hlt : t<u
      · have h := he t
        simp only [AddedForm.eval,Lnew,I] at h
        simp_all <;> omega
      · have hlt' : u<t := by omega
        have h := he u
        simp only [AddedForm.eval,Lnew,I] at h
        simp_all <;> omega

theorem r15short_injective (q p t u v : Nat) (hq : 4≤q)
    (hp : RemovedForm.Valid q (.r15short p t)) (hu : RemovedForm.Valid q (.r15short u v))
    (he : ∀e,RemovedForm.eval q (.r15short p t) e ↔ RemovedForm.eval q (.r15short u v) e) :
    p=u ∧ t=v := by
  have hpt : 4≤p ∧ p≤q+1 ∧ (t=2*q+2 ∨ t=2*q+3) := hp
  have huv : 4≤u ∧ u≤q+1 ∧ (v=2*q+2 ∨ v=2*q+3) := hu
  have tv : t=v := by
    have h := he (2*q+2)
    simp only [RemovedForm.eval,I] at h
    simp_all <;> omega
  refine ⟨?_,tv⟩
  apply Classical.byContradiction; intro hne
  by_cases hlt : p<u
  · have h := he (p+1)
    simp only [RemovedForm.eval,I] at h
    simp_all <;> omega
  · have hlt' : u<p := by omega
    have h := he (u+1)
    simp only [RemovedForm.eval,I] at h
    simp_all <;> omega

end LuRazSixRowClosure.Difference

