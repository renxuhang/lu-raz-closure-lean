import SixRowDifferenceForms
namespace LuRazSixRowClosure.Difference
open LuRazClosure LuRazParametric
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

theorem r6regular_to_old (q t : Nat) (hq : 4≤q)
    (ht : RemovedForm.Valid q (.r6regular t)) (e : Nat) :
    RemovedForm.eval q (.r6regular t) e ↔ NF23.eval q (.creg t) e := by
  simp only [RemovedForm.eval,C,Suffix,NF23.eval,I,beta]
  split <;> omega

theorem n6regular_to_old (q t : Nat) (hq : 4≤q)
    (ht : AddedForm.Valid q (.n6regular t)) (e : Nat) :
    NF23.eval q (.creg t) e ↔ (AddedForm.eval q (.n6regular t) e ∨ e=2*q+2) := by
  simp only [AddedForm.eval,Ct,Suffix,NF23.eval,I,beta]
  split <;> omega

theorem n7regular_to_old (q t : Nat) (hq : 4≤q)
    (ht : AddedForm.Valid q (.n7regular t)) (e : Nat) :
    NF23.eval q (.creg t) e ↔ ((AddedForm.eval q (.n7regular t) e ∧ e≠1) ∨ e=2*q+2) := by
  have ht' : P q t ∧ t≤2*q ∧ t≠q+3 := ht
  have hp := ht'.1
  unfold P at hp
  simp only [AddedForm.eval,Ct,Suffix,NF23.eval,I,beta]
  split <;> omega

theorem removed6regular_injective (q t u : Nat) (hq : 4≤q)
    (ht : RemovedForm.Valid q (.r6regular t)) (hu : RemovedForm.Valid q (.r6regular u))
    (he : ∀e,RemovedForm.eval q (.r6regular t) e ↔ RemovedForm.eval q (.r6regular u) e) : t=u := by
  have htv : P q t ∧ t≤2*q ∧ t≠q+3 := ht
  have huv : P q u ∧ u≤2*q ∧ u≠q+3 := hu
  have hh := NF23.unique q hq (.creg t) (.creg u) ⟨htv.1,htv.2.2⟩ ⟨huv.1,huv.2.2⟩
    (fun e=>(r6regular_to_old q t hq ht e).symm.trans ((he e).trans (r6regular_to_old q u hq hu e)))
  exact NF23.creg.inj hh

theorem added6regular_injective (q t u : Nat) (hq : 4≤q)
    (ht : AddedForm.Valid q (.n6regular t)) (hu : AddedForm.Valid q (.n6regular u))
    (he : ∀e,AddedForm.eval q (.n6regular t) e ↔ AddedForm.eval q (.n6regular u) e) : t=u := by
  have htv : P q t ∧ t≤2*q ∧ t≠q+3 := ht
  have huv : P q u ∧ u≤2*q ∧ u≠q+3 := hu
  have hh := NF23.unique q hq (.creg t) (.creg u) ⟨htv.1,htv.2.2⟩ ⟨huv.1,huv.2.2⟩
    (fun e=>(n6regular_to_old q t hq ht e).trans ((or_congr (he e) Iff.rfl).trans (n6regular_to_old q u hq hu e).symm))
  exact NF23.creg.inj hh

theorem added7regular_injective (q t u : Nat) (hq : 4≤q)
    (ht : AddedForm.Valid q (.n7regular t)) (hu : AddedForm.Valid q (.n7regular u))
    (he : ∀e,AddedForm.eval q (.n7regular t) e ↔ AddedForm.eval q (.n7regular u) e) : t=u := by
  have htv : P q t ∧ t≤2*q ∧ t≠q+3 := ht
  have huv : P q u ∧ u≤2*q ∧ u≠q+3 := hu
  have hh := NF23.unique q hq (.creg t) (.creg u) ⟨htv.1,htv.2.2⟩ ⟨huv.1,huv.2.2⟩
    (fun e=>(n7regular_to_old q t hq ht e).trans
      ((or_congr (and_congr (he e) Iff.rfl) Iff.rfl).trans (n7regular_to_old q u hq hu e).symm))
  exact NF23.creg.inj hh
end LuRazSixRowClosure.Difference
