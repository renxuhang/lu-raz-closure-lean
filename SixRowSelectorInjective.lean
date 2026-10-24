import SixRowDifferenceForms
namespace LuRazSixRowClosure.Difference
open LuRazClosure
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

theorem n5_injective (q k j : Nat) (hq : 4≤q)
    (hk : AddedForm.Valid q (.n5 k)) (hj : AddedForm.Valid q (.n5 j))
    (he : ∀e,AddedForm.eval q (.n5 k) e ↔ AddedForm.eval q (.n5 j) e) : k=j := by
  have hks : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 := by change k≤6 at hk; omega
  have hjs : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 := by change j≤6 at hj; omega
  rcases hks with hk0|hk1|hk2|hk3|hk4|hk5|hk6 <;> subst k
  · rcases hjs with hj0|hj1|hj2|hj3|hj4|hj5|hj6 <;> subst j
    · rfl
    · have hh := he (2*q+2)
      simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I] at hh
      simp_all <;> omega
    · have hh := he (3*q+1)
      simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I] at hh
      simp_all <;> omega
    · have hh := he (4*q)
      simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I] at hh
      simp_all <;> omega
    · have hh := he (4*q)
      simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I] at hh
      simp_all <;> omega
    · have hh := he (4*q)
      simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I] at hh
      simp_all <;> omega
    · have hh := he (4*q)
      simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I] at hh
      simp_all <;> omega
  · rcases hjs with hj0|hj1|hj2|hj3|hj4|hj5|hj6 <;> subst j
    · have hh := he (2*q+2)
      simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I] at hh
      simp_all <;> omega
    · rfl
    · have hh := he (2*q+2)
      simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I] at hh
      simp_all <;> omega
    · have hh := he (4*q)
      simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I] at hh
      simp_all <;> omega
    · have hh := he (4*q)
      simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I] at hh
      simp_all <;> omega
    · have hh := he (4*q)
      simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I] at hh
      simp_all <;> omega
    · have hh := he (4*q)
      simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I] at hh
      simp_all <;> omega
  · rcases hjs with hj0|hj1|hj2|hj3|hj4|hj5|hj6 <;> subst j
    · have hh := he (3*q+1)
      simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I] at hh
      simp_all <;> omega
    · have hh := he (2*q+2)
      simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I] at hh
      simp_all <;> omega
    · rfl
    · have hh := he (4*q)
      simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I] at hh
      simp_all <;> omega
    · have hh := he (4*q)
      simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I] at hh
      simp_all <;> omega
    · have hh := he (4*q)
      simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I] at hh
      simp_all <;> omega
    · have hh := he (4*q)
      simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I] at hh
      simp_all <;> omega
  · rcases hjs with hj0|hj1|hj2|hj3|hj4|hj5|hj6 <;> subst j
    · have hh := he (4*q)
      simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I] at hh
      simp_all <;> omega
    · have hh := he (4*q)
      simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I] at hh
      simp_all <;> omega
    · have hh := he (4*q)
      simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I] at hh
      simp_all <;> omega
    · rfl
    · have hh := he (2*q+2)
      simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I] at hh
      simp_all <;> omega
    · have hh := he (3*q+2)
      simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I] at hh
      simp_all <;> omega
    · have hh := he (2*q+2)
      simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I] at hh
      simp_all <;> omega
  · rcases hjs with hj0|hj1|hj2|hj3|hj4|hj5|hj6 <;> subst j
    · have hh := he (4*q)
      simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I] at hh
      simp_all <;> omega
    · have hh := he (4*q)
      simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I] at hh
      simp_all <;> omega
    · have hh := he (4*q)
      simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I] at hh
      simp_all <;> omega
    · have hh := he (2*q+2)
      simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I] at hh
      simp_all <;> omega
    · rfl
    · have hh := he (2*q+2)
      simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I] at hh
      simp_all <;> omega
    · have hh := he (3*q+2)
      simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I] at hh
      simp_all <;> omega
  · rcases hjs with hj0|hj1|hj2|hj3|hj4|hj5|hj6 <;> subst j
    · have hh := he (4*q)
      simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I] at hh
      simp_all <;> omega
    · have hh := he (4*q)
      simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I] at hh
      simp_all <;> omega
    · have hh := he (4*q)
      simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I] at hh
      simp_all <;> omega
    · have hh := he (3*q+2)
      simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I] at hh
      simp_all <;> omega
    · have hh := he (2*q+2)
      simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I] at hh
      simp_all <;> omega
    · rfl
    · have hh := he (2*q+2)
      simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I] at hh
      simp_all <;> omega
  · rcases hjs with hj0|hj1|hj2|hj3|hj4|hj5|hj6 <;> subst j
    · have hh := he (4*q)
      simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I] at hh
      simp_all <;> omega
    · have hh := he (4*q)
      simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I] at hh
      simp_all <;> omega
    · have hh := he (4*q)
      simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I] at hh
      simp_all <;> omega
    · have hh := he (2*q+2)
      simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I] at hh
      simp_all <;> omega
    · have hh := he (3*q+2)
      simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I] at hh
      simp_all <;> omega
    · have hh := he (2*q+2)
      simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I] at hh
      simp_all <;> omega
    · rfl

theorem r12_injective (q k j : Nat) (hq : 4≤q)
    (hk : RemovedForm.Valid q (.r12 k)) (hj : RemovedForm.Valid q (.r12 j))
    (he : ∀e,RemovedForm.eval q (.r12 k) e ↔ RemovedForm.eval q (.r12 j) e) : k=j := by
  have hks : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by change k≤3 at hk; omega
  have hjs : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by change j≤3 at hj; omega
  rcases hks with hk0|hk1|hk2|hk3 <;> subst k
  · rcases hjs with hj0|hj1|hj2|hj3 <;> subst j
    · rfl
    · have hh := he (3*q+2)
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I] at hh
      simp_all <;> omega
    · have hh := he (2*q+2)
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I] at hh
      simp_all <;> omega
    · have hh := he (2*q+2)
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I] at hh
      simp_all <;> omega
  · rcases hjs with hj0|hj1|hj2|hj3 <;> subst j
    · have hh := he (3*q+2)
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I] at hh
      simp_all <;> omega
    · rfl
    · have hh := he (2*q+2)
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I] at hh
      simp_all <;> omega
    · have hh := he (2*q+2)
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I] at hh
      simp_all <;> omega
  · rcases hjs with hj0|hj1|hj2|hj3 <;> subst j
    · have hh := he (2*q+2)
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I] at hh
      simp_all <;> omega
    · have hh := he (2*q+2)
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I] at hh
      simp_all <;> omega
    · rfl
    · have hh := he (3*q+2)
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I] at hh
      simp_all <;> omega
  · rcases hjs with hj0|hj1|hj2|hj3 <;> subst j
    · have hh := he (2*q+2)
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I] at hh
      simp_all <;> omega
    · have hh := he (2*q+2)
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I] at hh
      simp_all <;> omega
    · have hh := he (3*q+2)
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I] at hh
      simp_all <;> omega
    · rfl

theorem r7fresh_injective (q k j : Nat) (hq : 4≤q)
    (hk : RemovedForm.Valid q (.r7fresh k)) (hj : RemovedForm.Valid q (.r7fresh j))
    (he : ∀e,RemovedForm.eval q (.r7fresh k) e ↔ RemovedForm.eval q (.r7fresh j) e) : k=j := by
  have hks : k=0 ∨ k=1 ∨ k=2 := by change k≤2 at hk; omega
  have hjs : j=0 ∨ j=1 ∨ j=2 := by change j≤2 at hj; omega
  rcases hks with hk0|hk1|hk2 <;> subst k
  · rcases hjs with hj0|hj1|hj2 <;> subst j
    · rfl
    · have hh := he (5)
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I] at hh
      simp_all <;> omega
    · have hh := he (5)
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I] at hh
      simp_all <;> omega
  · rcases hjs with hj0|hj1|hj2 <;> subst j
    · have hh := he (5)
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I] at hh
      simp_all <;> omega
    · rfl
    · have hh := he (2*q+2)
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I] at hh
      simp_all <;> omega
  · rcases hjs with hj0|hj1|hj2 <;> subst j
    · have hh := he (5)
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I] at hh
      simp_all <;> omega
    · have hh := he (2*q+2)
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I] at hh
      simp_all <;> omega
    · rfl

theorem r13points_injective (q k j : Nat) (hq : 4≤q)
    (hk : RemovedForm.Valid q (.r13points k)) (hj : RemovedForm.Valid q (.r13points j))
    (he : ∀e,RemovedForm.eval q (.r13points k) e ↔ RemovedForm.eval q (.r13points j) e) : k=j := by
  have hks : k=0 ∨ k=1 ∨ k=2 := by change k≤2 at hk; omega
  have hjs : j=0 ∨ j=1 ∨ j=2 := by change j≤2 at hj; omega
  rcases hks with hk0|hk1|hk2 <;> subst k
  · rcases hjs with hj0|hj1|hj2 <;> subst j
    · rfl
    · have hh := he (3*q+2)
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I] at hh
      simp_all <;> omega
    · have hh := he (4*q-1)
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I] at hh
      simp_all <;> omega
  · rcases hjs with hj0|hj1|hj2 <;> subst j
    · have hh := he (3*q+2)
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I] at hh
      simp_all <;> omega
    · rfl
    · have hh := he (3*q+2)
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I] at hh
      simp_all <;> omega
  · rcases hjs with hj0|hj1|hj2 <;> subst j
    · have hh := he (4*q-1)
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I] at hh
      simp_all <;> omega
    · have hh := he (3*q+2)
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I] at hh
      simp_all <;> omega
    · rfl

theorem r14points_injective (q k j : Nat) (hq : 4≤q)
    (hk : RemovedForm.Valid q (.r14points k)) (hj : RemovedForm.Valid q (.r14points j))
    (he : ∀e,RemovedForm.eval q (.r14points k) e ↔ RemovedForm.eval q (.r14points j) e) : k=j := by
  have hks : k=0 ∨ k=1 ∨ k=2 := by change k≤2 at hk; omega
  have hjs : j=0 ∨ j=1 ∨ j=2 := by change j≤2 at hj; omega
  rcases hks with hk0|hk1|hk2 <;> subst k
  · rcases hjs with hj0|hj1|hj2 <;> subst j
    · rfl
    · have hh := he (2*q+2)
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I] at hh
      simp_all <;> omega
    · have hh := he (4*q)
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I] at hh
      simp_all <;> omega
  · rcases hjs with hj0|hj1|hj2 <;> subst j
    · have hh := he (2*q+2)
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I] at hh
      simp_all <;> omega
    · rfl
    · have hh := he (4*q)
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I] at hh
      simp_all <;> omega
  · rcases hjs with hj0|hj1|hj2 <;> subst j
    · have hh := he (4*q)
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I] at hh
      simp_all <;> omega
    · have hh := he (4*q)
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I] at hh
      simp_all <;> omega
    · rfl

theorem r4_injective (q k j : Nat) (hq : 4≤q)
    (hk : RemovedForm.Valid q (.r4 k)) (hj : RemovedForm.Valid q (.r4 j))
    (he : ∀e,RemovedForm.eval q (.r4 k) e ↔ RemovedForm.eval q (.r4 j) e) : k=j := by
  have hks : k=0 ∨ k=1 := by change k≤1 at hk; omega
  have hjs : j=0 ∨ j=1 := by change j≤1 at hj; omega
  rcases hks with hk0|hk1 <;> subst k
  · rcases hjs with hj0|hj1 <;> subst j
    · rfl
    · have hh := he (4*q)
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I] at hh
      simp_all <;> omega
  · rcases hjs with hj0|hj1 <;> subst j
    · have hh := he (4*q)
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I] at hh
      simp_all <;> omega
    · rfl

theorem n4_injective (q k j : Nat) (hq : 4≤q)
    (hk : AddedForm.Valid q (.n4 k)) (hj : AddedForm.Valid q (.n4 j))
    (he : ∀e,AddedForm.eval q (.n4 k) e ↔ AddedForm.eval q (.n4 j) e) : k=j := by
  have hks : k=0 ∨ k=1 := by change k≤1 at hk; omega
  have hjs : j=0 ∨ j=1 := by change j≤1 at hj; omega
  rcases hks with hk0|hk1 <;> subst k
  · rcases hjs with hj0|hj1 <;> subst j
    · rfl
    · have hh := he (4*q)
      simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I] at hh
      simp_all <;> omega
  · rcases hjs with hj0|hj1 <;> subst j
    · have hh := he (4*q)
      simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I] at hh
      simp_all <;> omega
    · rfl

theorem r15points_injective (q k j : Nat) (hq : 4≤q)
    (hk : RemovedForm.Valid q (.r15points k)) (hj : RemovedForm.Valid q (.r15points j))
    (he : ∀e,RemovedForm.eval q (.r15points k) e ↔ RemovedForm.eval q (.r15points j) e) : k=j := by
  have hks : k=0 ∨ k=1 := by change k≤1 at hk; omega
  have hjs : j=0 ∨ j=1 := by change j≤1 at hj; omega
  rcases hks with hk0|hk1 <;> subst k
  · rcases hjs with hj0|hj1 <;> subst j
    · rfl
    · have hh := he (4*q)
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I] at hh
      simp_all <;> omega
  · rcases hjs with hj0|hj1 <;> subst j
    · have hh := he (4*q)
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I] at hh
      simp_all <;> omega
    · rfl
end LuRazSixRowClosure.Difference
