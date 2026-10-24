import SixRowRegularInjective
import SixRowSelectorInjective
import SixRowOtherInjective
import SixRowDifferencePredicates
namespace LuRazSixRowClosure.Difference
open LuRazClosure
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

theorem removed_form_unique (q : Nat) (hq : 4≤q) (x y : RemovedForm)
    (hx : x.Valid q) (hy : y.Valid q) (he : ∀e,x.eval q e ↔ y.eval q e) : x=y := by
  have hcx := RemovedForm.core_mask q hq x hx
  have hcy := RemovedForm.core_mask q hq y hy
  have hcore : x.core=y.core := core_mask_unique x.core y.core (by cases x <;> simp [RemovedForm.core]) (by cases y <;> simp [RemovedForm.core]) (x.eval q) hcx ((core_mask_congr y.core (x.eval q) (y.eval q) he).mpr hcy)
  clear hcx hcy
  cases x with
  | r2 =>
    cases y with
    | r2 =>
      rfl
    | r3 =>
      simp [RemovedForm.core] at hcore
    | r4 kY =>
      simp [RemovedForm.core] at hcore
    | r5 =>
      simp [RemovedForm.core] at hcore
    | r6regular tY =>
      simp [RemovedForm.core] at hcore
    | r6exception =>
      simp [RemovedForm.core] at hcore
    | r6d pY =>
      simp [RemovedForm.core] at hcore
    | r7fresh kY =>
      simp [RemovedForm.core] at hcore
    | r7e pY =>
      simp [RemovedForm.core] at hcore
    | r7d pY =>
      simp [RemovedForm.core] at hcore
    | r10 tY =>
      simp [RemovedForm.core] at hcore
    | r11j aY =>
      simp [RemovedForm.core] at hcore
    | r11aj aY =>
      simp [RemovedForm.core] at hcore
    | r11ak tY =>
      simp [RemovedForm.core] at hcore
    | r12 kY =>
      simp [RemovedForm.core] at hcore
    | r13cj bY =>
      simp [RemovedForm.core] at hcore
    | r13zj bY =>
      simp [RemovedForm.core] at hcore
    | r13czj bY =>
      simp [RemovedForm.core] at hcore
    | r13points kY =>
      simp [RemovedForm.core] at hcore
    | r14points kY =>
      simp [RemovedForm.core] at hcore
    | r14line tY =>
      simp [RemovedForm.core] at hcore
    | r14c tY =>
      simp [RemovedForm.core] at hcore
    | r15points kY =>
      simp [RemovedForm.core] at hcore
    | r15right aY =>
      simp [RemovedForm.core] at hcore
    | r15gap aY =>
      simp [RemovedForm.core] at hcore
    | r15line tY =>
      simp [RemovedForm.core] at hcore
    | r15short pY tY =>
      simp [RemovedForm.core] at hcore
  | r3 =>
    cases y with
    | r2 =>
      simp [RemovedForm.core] at hcore
    | r3 =>
      rfl
    | r4 kY =>
      simp [RemovedForm.core] at hcore
    | r5 =>
      simp [RemovedForm.core] at hcore
    | r6regular tY =>
      simp [RemovedForm.core] at hcore
    | r6exception =>
      simp [RemovedForm.core] at hcore
    | r6d pY =>
      simp [RemovedForm.core] at hcore
    | r7fresh kY =>
      simp [RemovedForm.core] at hcore
    | r7e pY =>
      simp [RemovedForm.core] at hcore
    | r7d pY =>
      simp [RemovedForm.core] at hcore
    | r10 tY =>
      simp [RemovedForm.core] at hcore
    | r11j aY =>
      simp [RemovedForm.core] at hcore
    | r11aj aY =>
      simp [RemovedForm.core] at hcore
    | r11ak tY =>
      simp [RemovedForm.core] at hcore
    | r12 kY =>
      simp [RemovedForm.core] at hcore
    | r13cj bY =>
      simp [RemovedForm.core] at hcore
    | r13zj bY =>
      simp [RemovedForm.core] at hcore
    | r13czj bY =>
      simp [RemovedForm.core] at hcore
    | r13points kY =>
      simp [RemovedForm.core] at hcore
    | r14points kY =>
      simp [RemovedForm.core] at hcore
    | r14line tY =>
      simp [RemovedForm.core] at hcore
    | r14c tY =>
      simp [RemovedForm.core] at hcore
    | r15points kY =>
      simp [RemovedForm.core] at hcore
    | r15right aY =>
      simp [RemovedForm.core] at hcore
    | r15gap aY =>
      simp [RemovedForm.core] at hcore
    | r15line tY =>
      simp [RemovedForm.core] at hcore
    | r15short pY tY =>
      simp [RemovedForm.core] at hcore
  | r4 kX =>
    cases y with
    | r2 =>
      simp [RemovedForm.core] at hcore
    | r3 =>
      simp [RemovedForm.core] at hcore
    | r4 kY =>
      have eq0 := r4_injective q kX kY hq hx hy he
      cases eq0
      rfl
    | r5 =>
      simp [RemovedForm.core] at hcore
    | r6regular tY =>
      simp [RemovedForm.core] at hcore
    | r6exception =>
      simp [RemovedForm.core] at hcore
    | r6d pY =>
      simp [RemovedForm.core] at hcore
    | r7fresh kY =>
      simp [RemovedForm.core] at hcore
    | r7e pY =>
      simp [RemovedForm.core] at hcore
    | r7d pY =>
      simp [RemovedForm.core] at hcore
    | r10 tY =>
      simp [RemovedForm.core] at hcore
    | r11j aY =>
      simp [RemovedForm.core] at hcore
    | r11aj aY =>
      simp [RemovedForm.core] at hcore
    | r11ak tY =>
      simp [RemovedForm.core] at hcore
    | r12 kY =>
      simp [RemovedForm.core] at hcore
    | r13cj bY =>
      simp [RemovedForm.core] at hcore
    | r13zj bY =>
      simp [RemovedForm.core] at hcore
    | r13czj bY =>
      simp [RemovedForm.core] at hcore
    | r13points kY =>
      simp [RemovedForm.core] at hcore
    | r14points kY =>
      simp [RemovedForm.core] at hcore
    | r14line tY =>
      simp [RemovedForm.core] at hcore
    | r14c tY =>
      simp [RemovedForm.core] at hcore
    | r15points kY =>
      simp [RemovedForm.core] at hcore
    | r15right aY =>
      simp [RemovedForm.core] at hcore
    | r15gap aY =>
      simp [RemovedForm.core] at hcore
    | r15line tY =>
      simp [RemovedForm.core] at hcore
    | r15short pY tY =>
      simp [RemovedForm.core] at hcore
  | r5 =>
    cases y with
    | r2 =>
      simp [RemovedForm.core] at hcore
    | r3 =>
      simp [RemovedForm.core] at hcore
    | r4 kY =>
      simp [RemovedForm.core] at hcore
    | r5 =>
      rfl
    | r6regular tY =>
      simp [RemovedForm.core] at hcore
    | r6exception =>
      simp [RemovedForm.core] at hcore
    | r6d pY =>
      simp [RemovedForm.core] at hcore
    | r7fresh kY =>
      simp [RemovedForm.core] at hcore
    | r7e pY =>
      simp [RemovedForm.core] at hcore
    | r7d pY =>
      simp [RemovedForm.core] at hcore
    | r10 tY =>
      simp [RemovedForm.core] at hcore
    | r11j aY =>
      simp [RemovedForm.core] at hcore
    | r11aj aY =>
      simp [RemovedForm.core] at hcore
    | r11ak tY =>
      simp [RemovedForm.core] at hcore
    | r12 kY =>
      simp [RemovedForm.core] at hcore
    | r13cj bY =>
      simp [RemovedForm.core] at hcore
    | r13zj bY =>
      simp [RemovedForm.core] at hcore
    | r13czj bY =>
      simp [RemovedForm.core] at hcore
    | r13points kY =>
      simp [RemovedForm.core] at hcore
    | r14points kY =>
      simp [RemovedForm.core] at hcore
    | r14line tY =>
      simp [RemovedForm.core] at hcore
    | r14c tY =>
      simp [RemovedForm.core] at hcore
    | r15points kY =>
      simp [RemovedForm.core] at hcore
    | r15right aY =>
      simp [RemovedForm.core] at hcore
    | r15gap aY =>
      simp [RemovedForm.core] at hcore
    | r15line tY =>
      simp [RemovedForm.core] at hcore
    | r15short pY tY =>
      simp [RemovedForm.core] at hcore
  | r6regular tX =>
    cases y with
    | r2 =>
      simp [RemovedForm.core] at hcore
    | r3 =>
      simp [RemovedForm.core] at hcore
    | r4 kY =>
      simp [RemovedForm.core] at hcore
    | r5 =>
      simp [RemovedForm.core] at hcore
    | r6regular tY =>
      have eq0 := removed6regular_injective q tX tY hq hx hy he
      cases eq0
      rfl
    | r6exception =>
      have h0 := he (4*q)
      clear he
      simp only [RemovedForm.Valid] at hx hy
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 hx hy
      exfalso
      simp_all <;> omega
    | r6d pY =>
      have h0 := he (2*q)
      have h1 := he (2*q+3)
      clear he
      simp only [RemovedForm.Valid] at hx hy
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 h1 hx hy
      exfalso
      simp_all <;> omega
    | r7fresh kY =>
      simp [RemovedForm.core] at hcore
    | r7e pY =>
      simp [RemovedForm.core] at hcore
    | r7d pY =>
      simp [RemovedForm.core] at hcore
    | r10 tY =>
      simp [RemovedForm.core] at hcore
    | r11j aY =>
      simp [RemovedForm.core] at hcore
    | r11aj aY =>
      simp [RemovedForm.core] at hcore
    | r11ak tY =>
      simp [RemovedForm.core] at hcore
    | r12 kY =>
      simp [RemovedForm.core] at hcore
    | r13cj bY =>
      simp [RemovedForm.core] at hcore
    | r13zj bY =>
      simp [RemovedForm.core] at hcore
    | r13czj bY =>
      simp [RemovedForm.core] at hcore
    | r13points kY =>
      simp [RemovedForm.core] at hcore
    | r14points kY =>
      simp [RemovedForm.core] at hcore
    | r14line tY =>
      simp [RemovedForm.core] at hcore
    | r14c tY =>
      simp [RemovedForm.core] at hcore
    | r15points kY =>
      simp [RemovedForm.core] at hcore
    | r15right aY =>
      simp [RemovedForm.core] at hcore
    | r15gap aY =>
      simp [RemovedForm.core] at hcore
    | r15line tY =>
      simp [RemovedForm.core] at hcore
    | r15short pY tY =>
      simp [RemovedForm.core] at hcore
  | r6exception =>
    cases y with
    | r2 =>
      simp [RemovedForm.core] at hcore
    | r3 =>
      simp [RemovedForm.core] at hcore
    | r4 kY =>
      simp [RemovedForm.core] at hcore
    | r5 =>
      simp [RemovedForm.core] at hcore
    | r6regular tY =>
      have h0 := he (4*q)
      clear he
      simp only [RemovedForm.Valid] at hx hy
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 hx hy
      exfalso
      simp_all <;> omega
    | r6exception =>
      rfl
    | r6d pY =>
      have h0 := he (4*q)
      clear he
      simp only [RemovedForm.Valid] at hx hy
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 hx hy
      exfalso
      simp_all <;> omega
    | r7fresh kY =>
      simp [RemovedForm.core] at hcore
    | r7e pY =>
      simp [RemovedForm.core] at hcore
    | r7d pY =>
      simp [RemovedForm.core] at hcore
    | r10 tY =>
      simp [RemovedForm.core] at hcore
    | r11j aY =>
      simp [RemovedForm.core] at hcore
    | r11aj aY =>
      simp [RemovedForm.core] at hcore
    | r11ak tY =>
      simp [RemovedForm.core] at hcore
    | r12 kY =>
      simp [RemovedForm.core] at hcore
    | r13cj bY =>
      simp [RemovedForm.core] at hcore
    | r13zj bY =>
      simp [RemovedForm.core] at hcore
    | r13czj bY =>
      simp [RemovedForm.core] at hcore
    | r13points kY =>
      simp [RemovedForm.core] at hcore
    | r14points kY =>
      simp [RemovedForm.core] at hcore
    | r14line tY =>
      simp [RemovedForm.core] at hcore
    | r14c tY =>
      simp [RemovedForm.core] at hcore
    | r15points kY =>
      simp [RemovedForm.core] at hcore
    | r15right aY =>
      simp [RemovedForm.core] at hcore
    | r15gap aY =>
      simp [RemovedForm.core] at hcore
    | r15line tY =>
      simp [RemovedForm.core] at hcore
    | r15short pY tY =>
      simp [RemovedForm.core] at hcore
  | r6d pX =>
    cases y with
    | r2 =>
      simp [RemovedForm.core] at hcore
    | r3 =>
      simp [RemovedForm.core] at hcore
    | r4 kY =>
      simp [RemovedForm.core] at hcore
    | r5 =>
      simp [RemovedForm.core] at hcore
    | r6regular tY =>
      have h0 := he (2*q)
      have h1 := he (2*q+3)
      clear he
      simp only [RemovedForm.Valid] at hx hy
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 h1 hx hy
      exfalso
      simp_all <;> omega
    | r6exception =>
      have h0 := he (4*q)
      clear he
      simp only [RemovedForm.Valid] at hx hy
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 hx hy
      exfalso
      simp_all <;> omega
    | r6d pY =>
      have eq0 := r6d_injective q pX pY hq hx hy he
      cases eq0
      rfl
    | r7fresh kY =>
      simp [RemovedForm.core] at hcore
    | r7e pY =>
      simp [RemovedForm.core] at hcore
    | r7d pY =>
      simp [RemovedForm.core] at hcore
    | r10 tY =>
      simp [RemovedForm.core] at hcore
    | r11j aY =>
      simp [RemovedForm.core] at hcore
    | r11aj aY =>
      simp [RemovedForm.core] at hcore
    | r11ak tY =>
      simp [RemovedForm.core] at hcore
    | r12 kY =>
      simp [RemovedForm.core] at hcore
    | r13cj bY =>
      simp [RemovedForm.core] at hcore
    | r13zj bY =>
      simp [RemovedForm.core] at hcore
    | r13czj bY =>
      simp [RemovedForm.core] at hcore
    | r13points kY =>
      simp [RemovedForm.core] at hcore
    | r14points kY =>
      simp [RemovedForm.core] at hcore
    | r14line tY =>
      simp [RemovedForm.core] at hcore
    | r14c tY =>
      simp [RemovedForm.core] at hcore
    | r15points kY =>
      simp [RemovedForm.core] at hcore
    | r15right aY =>
      simp [RemovedForm.core] at hcore
    | r15gap aY =>
      simp [RemovedForm.core] at hcore
    | r15line tY =>
      simp [RemovedForm.core] at hcore
    | r15short pY tY =>
      simp [RemovedForm.core] at hcore
  | r7fresh kX =>
    cases y with
    | r2 =>
      simp [RemovedForm.core] at hcore
    | r3 =>
      simp [RemovedForm.core] at hcore
    | r4 kY =>
      simp [RemovedForm.core] at hcore
    | r5 =>
      simp [RemovedForm.core] at hcore
    | r6regular tY =>
      simp [RemovedForm.core] at hcore
    | r6exception =>
      simp [RemovedForm.core] at hcore
    | r6d pY =>
      simp [RemovedForm.core] at hcore
    | r7fresh kY =>
      have eq0 := r7fresh_injective q kX kY hq hx hy he
      cases eq0
      rfl
    | r7e pY =>
      have h0 := he (4*q-1)
      clear he
      simp only [RemovedForm.Valid] at hx hy
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 hx hy
      exfalso
      simp_all <;> omega
    | r7d pY =>
      have h0 := he (4*q-1)
      clear he
      simp only [RemovedForm.Valid] at hx hy
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 hx hy
      exfalso
      simp_all <;> omega
    | r10 tY =>
      simp [RemovedForm.core] at hcore
    | r11j aY =>
      simp [RemovedForm.core] at hcore
    | r11aj aY =>
      simp [RemovedForm.core] at hcore
    | r11ak tY =>
      simp [RemovedForm.core] at hcore
    | r12 kY =>
      simp [RemovedForm.core] at hcore
    | r13cj bY =>
      simp [RemovedForm.core] at hcore
    | r13zj bY =>
      simp [RemovedForm.core] at hcore
    | r13czj bY =>
      simp [RemovedForm.core] at hcore
    | r13points kY =>
      simp [RemovedForm.core] at hcore
    | r14points kY =>
      simp [RemovedForm.core] at hcore
    | r14line tY =>
      simp [RemovedForm.core] at hcore
    | r14c tY =>
      simp [RemovedForm.core] at hcore
    | r15points kY =>
      simp [RemovedForm.core] at hcore
    | r15right aY =>
      simp [RemovedForm.core] at hcore
    | r15gap aY =>
      simp [RemovedForm.core] at hcore
    | r15line tY =>
      simp [RemovedForm.core] at hcore
    | r15short pY tY =>
      simp [RemovedForm.core] at hcore
  | r7e pX =>
    cases y with
    | r2 =>
      simp [RemovedForm.core] at hcore
    | r3 =>
      simp [RemovedForm.core] at hcore
    | r4 kY =>
      simp [RemovedForm.core] at hcore
    | r5 =>
      simp [RemovedForm.core] at hcore
    | r6regular tY =>
      simp [RemovedForm.core] at hcore
    | r6exception =>
      simp [RemovedForm.core] at hcore
    | r6d pY =>
      simp [RemovedForm.core] at hcore
    | r7fresh kY =>
      have h0 := he (4*q-1)
      clear he
      simp only [RemovedForm.Valid] at hx hy
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 hx hy
      exfalso
      simp_all <;> omega
    | r7e pY =>
      have h0 := he (pX)
      have h1 := he (pY)
      have h2 := he (pX+1)
      have h3 := he (pY+1)
      clear he
      simp only [RemovedForm.Valid] at hx hy
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 h1 h2 h3 hx hy
      have eq0 : pX=pY := by simp_all <;> omega
      cases eq0; rfl
    | r7d pY =>
      have h0 := he (2*q+1)
      clear he
      simp only [RemovedForm.Valid] at hx hy
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 hx hy
      exfalso
      simp_all <;> omega
    | r10 tY =>
      simp [RemovedForm.core] at hcore
    | r11j aY =>
      simp [RemovedForm.core] at hcore
    | r11aj aY =>
      simp [RemovedForm.core] at hcore
    | r11ak tY =>
      simp [RemovedForm.core] at hcore
    | r12 kY =>
      simp [RemovedForm.core] at hcore
    | r13cj bY =>
      simp [RemovedForm.core] at hcore
    | r13zj bY =>
      simp [RemovedForm.core] at hcore
    | r13czj bY =>
      simp [RemovedForm.core] at hcore
    | r13points kY =>
      simp [RemovedForm.core] at hcore
    | r14points kY =>
      simp [RemovedForm.core] at hcore
    | r14line tY =>
      simp [RemovedForm.core] at hcore
    | r14c tY =>
      simp [RemovedForm.core] at hcore
    | r15points kY =>
      simp [RemovedForm.core] at hcore
    | r15right aY =>
      simp [RemovedForm.core] at hcore
    | r15gap aY =>
      simp [RemovedForm.core] at hcore
    | r15line tY =>
      simp [RemovedForm.core] at hcore
    | r15short pY tY =>
      simp [RemovedForm.core] at hcore
  | r7d pX =>
    cases y with
    | r2 =>
      simp [RemovedForm.core] at hcore
    | r3 =>
      simp [RemovedForm.core] at hcore
    | r4 kY =>
      simp [RemovedForm.core] at hcore
    | r5 =>
      simp [RemovedForm.core] at hcore
    | r6regular tY =>
      simp [RemovedForm.core] at hcore
    | r6exception =>
      simp [RemovedForm.core] at hcore
    | r6d pY =>
      simp [RemovedForm.core] at hcore
    | r7fresh kY =>
      have h0 := he (4*q-1)
      clear he
      simp only [RemovedForm.Valid] at hx hy
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 hx hy
      exfalso
      simp_all <;> omega
    | r7e pY =>
      have h0 := he (2*q+1)
      clear he
      simp only [RemovedForm.Valid] at hx hy
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 hx hy
      exfalso
      simp_all <;> omega
    | r7d pY =>
      have h0 := he (pX)
      have h1 := he (pY)
      have h2 := he (pX+1)
      have h3 := he (pY+1)
      clear he
      simp only [RemovedForm.Valid] at hx hy
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 h1 h2 h3 hx hy
      have eq0 : pX=pY := by simp_all <;> omega
      cases eq0; rfl
    | r10 tY =>
      simp [RemovedForm.core] at hcore
    | r11j aY =>
      simp [RemovedForm.core] at hcore
    | r11aj aY =>
      simp [RemovedForm.core] at hcore
    | r11ak tY =>
      simp [RemovedForm.core] at hcore
    | r12 kY =>
      simp [RemovedForm.core] at hcore
    | r13cj bY =>
      simp [RemovedForm.core] at hcore
    | r13zj bY =>
      simp [RemovedForm.core] at hcore
    | r13czj bY =>
      simp [RemovedForm.core] at hcore
    | r13points kY =>
      simp [RemovedForm.core] at hcore
    | r14points kY =>
      simp [RemovedForm.core] at hcore
    | r14line tY =>
      simp [RemovedForm.core] at hcore
    | r14c tY =>
      simp [RemovedForm.core] at hcore
    | r15points kY =>
      simp [RemovedForm.core] at hcore
    | r15right aY =>
      simp [RemovedForm.core] at hcore
    | r15gap aY =>
      simp [RemovedForm.core] at hcore
    | r15line tY =>
      simp [RemovedForm.core] at hcore
    | r15short pY tY =>
      simp [RemovedForm.core] at hcore
  | r10 tX =>
    cases y with
    | r2 =>
      simp [RemovedForm.core] at hcore
    | r3 =>
      simp [RemovedForm.core] at hcore
    | r4 kY =>
      simp [RemovedForm.core] at hcore
    | r5 =>
      simp [RemovedForm.core] at hcore
    | r6regular tY =>
      simp [RemovedForm.core] at hcore
    | r6exception =>
      simp [RemovedForm.core] at hcore
    | r6d pY =>
      simp [RemovedForm.core] at hcore
    | r7fresh kY =>
      simp [RemovedForm.core] at hcore
    | r7e pY =>
      simp [RemovedForm.core] at hcore
    | r7d pY =>
      simp [RemovedForm.core] at hcore
    | r10 tY =>
      have h0 := he (2*q+2)
      clear he
      simp only [RemovedForm.Valid] at hx hy
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 hx hy
      have eq0 : tX=tY := by simp_all <;> omega
      cases eq0; rfl
    | r11j aY =>
      simp [RemovedForm.core] at hcore
    | r11aj aY =>
      simp [RemovedForm.core] at hcore
    | r11ak tY =>
      simp [RemovedForm.core] at hcore
    | r12 kY =>
      simp [RemovedForm.core] at hcore
    | r13cj bY =>
      simp [RemovedForm.core] at hcore
    | r13zj bY =>
      simp [RemovedForm.core] at hcore
    | r13czj bY =>
      simp [RemovedForm.core] at hcore
    | r13points kY =>
      simp [RemovedForm.core] at hcore
    | r14points kY =>
      simp [RemovedForm.core] at hcore
    | r14line tY =>
      simp [RemovedForm.core] at hcore
    | r14c tY =>
      simp [RemovedForm.core] at hcore
    | r15points kY =>
      simp [RemovedForm.core] at hcore
    | r15right aY =>
      simp [RemovedForm.core] at hcore
    | r15gap aY =>
      simp [RemovedForm.core] at hcore
    | r15line tY =>
      simp [RemovedForm.core] at hcore
    | r15short pY tY =>
      simp [RemovedForm.core] at hcore
  | r11j aX =>
    cases y with
    | r2 =>
      simp [RemovedForm.core] at hcore
    | r3 =>
      simp [RemovedForm.core] at hcore
    | r4 kY =>
      simp [RemovedForm.core] at hcore
    | r5 =>
      simp [RemovedForm.core] at hcore
    | r6regular tY =>
      simp [RemovedForm.core] at hcore
    | r6exception =>
      simp [RemovedForm.core] at hcore
    | r6d pY =>
      simp [RemovedForm.core] at hcore
    | r7fresh kY =>
      simp [RemovedForm.core] at hcore
    | r7e pY =>
      simp [RemovedForm.core] at hcore
    | r7d pY =>
      simp [RemovedForm.core] at hcore
    | r10 tY =>
      simp [RemovedForm.core] at hcore
    | r11j aY =>
      have h0 := he (aX)
      have h1 := he (aY)
      have h2 := he (aX+1)
      have h3 := he (aY+1)
      clear he
      simp only [RemovedForm.Valid] at hx hy
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 h1 h2 h3 hx hy
      have eq0 : aX=aY := by simp_all <;> omega
      cases eq0; rfl
    | r11aj aY =>
      have h0 := he (5)
      have h1 := he (q+3)
      clear he
      simp only [RemovedForm.Valid] at hx hy
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 h1 hx hy
      exfalso
      simp_all <;> omega
    | r11ak tY =>
      have h0 := he (2*q+1)
      clear he
      simp only [RemovedForm.Valid] at hx hy
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 hx hy
      exfalso
      simp_all <;> omega
    | r12 kY =>
      simp [RemovedForm.core] at hcore
    | r13cj bY =>
      simp [RemovedForm.core] at hcore
    | r13zj bY =>
      simp [RemovedForm.core] at hcore
    | r13czj bY =>
      simp [RemovedForm.core] at hcore
    | r13points kY =>
      simp [RemovedForm.core] at hcore
    | r14points kY =>
      simp [RemovedForm.core] at hcore
    | r14line tY =>
      simp [RemovedForm.core] at hcore
    | r14c tY =>
      simp [RemovedForm.core] at hcore
    | r15points kY =>
      simp [RemovedForm.core] at hcore
    | r15right aY =>
      simp [RemovedForm.core] at hcore
    | r15gap aY =>
      simp [RemovedForm.core] at hcore
    | r15line tY =>
      simp [RemovedForm.core] at hcore
    | r15short pY tY =>
      simp [RemovedForm.core] at hcore
  | r11aj aX =>
    cases y with
    | r2 =>
      simp [RemovedForm.core] at hcore
    | r3 =>
      simp [RemovedForm.core] at hcore
    | r4 kY =>
      simp [RemovedForm.core] at hcore
    | r5 =>
      simp [RemovedForm.core] at hcore
    | r6regular tY =>
      simp [RemovedForm.core] at hcore
    | r6exception =>
      simp [RemovedForm.core] at hcore
    | r6d pY =>
      simp [RemovedForm.core] at hcore
    | r7fresh kY =>
      simp [RemovedForm.core] at hcore
    | r7e pY =>
      simp [RemovedForm.core] at hcore
    | r7d pY =>
      simp [RemovedForm.core] at hcore
    | r10 tY =>
      simp [RemovedForm.core] at hcore
    | r11j aY =>
      have h0 := he (5)
      have h1 := he (q+3)
      clear he
      simp only [RemovedForm.Valid] at hx hy
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 h1 hx hy
      exfalso
      simp_all <;> omega
    | r11aj aY =>
      have h0 := he (aX)
      have h1 := he (aY)
      have h2 := he (aX+1)
      have h3 := he (aY+1)
      clear he
      simp only [RemovedForm.Valid] at hx hy
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 h1 h2 h3 hx hy
      have eq0 : aX=aY := by simp_all <;> omega
      cases eq0; rfl
    | r11ak tY =>
      have h0 := he (2*q+1)
      clear he
      simp only [RemovedForm.Valid] at hx hy
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 hx hy
      exfalso
      simp_all <;> omega
    | r12 kY =>
      simp [RemovedForm.core] at hcore
    | r13cj bY =>
      simp [RemovedForm.core] at hcore
    | r13zj bY =>
      simp [RemovedForm.core] at hcore
    | r13czj bY =>
      simp [RemovedForm.core] at hcore
    | r13points kY =>
      simp [RemovedForm.core] at hcore
    | r14points kY =>
      simp [RemovedForm.core] at hcore
    | r14line tY =>
      simp [RemovedForm.core] at hcore
    | r14c tY =>
      simp [RemovedForm.core] at hcore
    | r15points kY =>
      simp [RemovedForm.core] at hcore
    | r15right aY =>
      simp [RemovedForm.core] at hcore
    | r15gap aY =>
      simp [RemovedForm.core] at hcore
    | r15line tY =>
      simp [RemovedForm.core] at hcore
    | r15short pY tY =>
      simp [RemovedForm.core] at hcore
  | r11ak tX =>
    cases y with
    | r2 =>
      simp [RemovedForm.core] at hcore
    | r3 =>
      simp [RemovedForm.core] at hcore
    | r4 kY =>
      simp [RemovedForm.core] at hcore
    | r5 =>
      simp [RemovedForm.core] at hcore
    | r6regular tY =>
      simp [RemovedForm.core] at hcore
    | r6exception =>
      simp [RemovedForm.core] at hcore
    | r6d pY =>
      simp [RemovedForm.core] at hcore
    | r7fresh kY =>
      simp [RemovedForm.core] at hcore
    | r7e pY =>
      simp [RemovedForm.core] at hcore
    | r7d pY =>
      simp [RemovedForm.core] at hcore
    | r10 tY =>
      simp [RemovedForm.core] at hcore
    | r11j aY =>
      have h0 := he (2*q+1)
      clear he
      simp only [RemovedForm.Valid] at hx hy
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 hx hy
      exfalso
      simp_all <;> omega
    | r11aj aY =>
      have h0 := he (2*q+1)
      clear he
      simp only [RemovedForm.Valid] at hx hy
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 hx hy
      exfalso
      simp_all <;> omega
    | r11ak tY =>
      have h0 := he (2*q+2)
      clear he
      simp only [RemovedForm.Valid] at hx hy
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 hx hy
      have eq0 : tX=tY := by simp_all <;> omega
      cases eq0; rfl
    | r12 kY =>
      simp [RemovedForm.core] at hcore
    | r13cj bY =>
      simp [RemovedForm.core] at hcore
    | r13zj bY =>
      simp [RemovedForm.core] at hcore
    | r13czj bY =>
      simp [RemovedForm.core] at hcore
    | r13points kY =>
      simp [RemovedForm.core] at hcore
    | r14points kY =>
      simp [RemovedForm.core] at hcore
    | r14line tY =>
      simp [RemovedForm.core] at hcore
    | r14c tY =>
      simp [RemovedForm.core] at hcore
    | r15points kY =>
      simp [RemovedForm.core] at hcore
    | r15right aY =>
      simp [RemovedForm.core] at hcore
    | r15gap aY =>
      simp [RemovedForm.core] at hcore
    | r15line tY =>
      simp [RemovedForm.core] at hcore
    | r15short pY tY =>
      simp [RemovedForm.core] at hcore
  | r12 kX =>
    cases y with
    | r2 =>
      simp [RemovedForm.core] at hcore
    | r3 =>
      simp [RemovedForm.core] at hcore
    | r4 kY =>
      simp [RemovedForm.core] at hcore
    | r5 =>
      simp [RemovedForm.core] at hcore
    | r6regular tY =>
      simp [RemovedForm.core] at hcore
    | r6exception =>
      simp [RemovedForm.core] at hcore
    | r6d pY =>
      simp [RemovedForm.core] at hcore
    | r7fresh kY =>
      simp [RemovedForm.core] at hcore
    | r7e pY =>
      simp [RemovedForm.core] at hcore
    | r7d pY =>
      simp [RemovedForm.core] at hcore
    | r10 tY =>
      simp [RemovedForm.core] at hcore
    | r11j aY =>
      simp [RemovedForm.core] at hcore
    | r11aj aY =>
      simp [RemovedForm.core] at hcore
    | r11ak tY =>
      simp [RemovedForm.core] at hcore
    | r12 kY =>
      have eq0 := r12_injective q kX kY hq hx hy he
      cases eq0
      rfl
    | r13cj bY =>
      simp [RemovedForm.core] at hcore
    | r13zj bY =>
      simp [RemovedForm.core] at hcore
    | r13czj bY =>
      simp [RemovedForm.core] at hcore
    | r13points kY =>
      simp [RemovedForm.core] at hcore
    | r14points kY =>
      simp [RemovedForm.core] at hcore
    | r14line tY =>
      simp [RemovedForm.core] at hcore
    | r14c tY =>
      simp [RemovedForm.core] at hcore
    | r15points kY =>
      simp [RemovedForm.core] at hcore
    | r15right aY =>
      simp [RemovedForm.core] at hcore
    | r15gap aY =>
      simp [RemovedForm.core] at hcore
    | r15line tY =>
      simp [RemovedForm.core] at hcore
    | r15short pY tY =>
      simp [RemovedForm.core] at hcore
  | r13cj bX =>
    cases y with
    | r2 =>
      simp [RemovedForm.core] at hcore
    | r3 =>
      simp [RemovedForm.core] at hcore
    | r4 kY =>
      simp [RemovedForm.core] at hcore
    | r5 =>
      simp [RemovedForm.core] at hcore
    | r6regular tY =>
      simp [RemovedForm.core] at hcore
    | r6exception =>
      simp [RemovedForm.core] at hcore
    | r6d pY =>
      simp [RemovedForm.core] at hcore
    | r7fresh kY =>
      simp [RemovedForm.core] at hcore
    | r7e pY =>
      simp [RemovedForm.core] at hcore
    | r7d pY =>
      simp [RemovedForm.core] at hcore
    | r10 tY =>
      simp [RemovedForm.core] at hcore
    | r11j aY =>
      simp [RemovedForm.core] at hcore
    | r11aj aY =>
      simp [RemovedForm.core] at hcore
    | r11ak tY =>
      simp [RemovedForm.core] at hcore
    | r12 kY =>
      simp [RemovedForm.core] at hcore
    | r13cj bY =>
      have h0 := he (bX)
      have h1 := he (bY)
      have h2 := he (bX+1)
      have h3 := he (bY+1)
      clear he
      simp only [RemovedForm.Valid] at hx hy
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 h1 h2 h3 hx hy
      have eq0 : bX=bY := by simp_all <;> omega
      cases eq0; rfl
    | r13zj bY =>
      have h0 := he (4*q)
      clear he
      simp only [RemovedForm.Valid] at hx hy
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 hx hy
      exfalso
      simp_all <;> omega
    | r13czj bY =>
      have h0 := he (4*q)
      clear he
      simp only [RemovedForm.Valid] at hx hy
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 hx hy
      exfalso
      simp_all <;> omega
    | r13points kY =>
      have h0 := he (3*q+1)
      clear he
      simp only [RemovedForm.Valid] at hx hy
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 hx hy
      exfalso
      simp_all <;> omega
    | r14points kY =>
      simp [RemovedForm.core] at hcore
    | r14line tY =>
      simp [RemovedForm.core] at hcore
    | r14c tY =>
      simp [RemovedForm.core] at hcore
    | r15points kY =>
      simp [RemovedForm.core] at hcore
    | r15right aY =>
      simp [RemovedForm.core] at hcore
    | r15gap aY =>
      simp [RemovedForm.core] at hcore
    | r15line tY =>
      simp [RemovedForm.core] at hcore
    | r15short pY tY =>
      simp [RemovedForm.core] at hcore
  | r13zj bX =>
    cases y with
    | r2 =>
      simp [RemovedForm.core] at hcore
    | r3 =>
      simp [RemovedForm.core] at hcore
    | r4 kY =>
      simp [RemovedForm.core] at hcore
    | r5 =>
      simp [RemovedForm.core] at hcore
    | r6regular tY =>
      simp [RemovedForm.core] at hcore
    | r6exception =>
      simp [RemovedForm.core] at hcore
    | r6d pY =>
      simp [RemovedForm.core] at hcore
    | r7fresh kY =>
      simp [RemovedForm.core] at hcore
    | r7e pY =>
      simp [RemovedForm.core] at hcore
    | r7d pY =>
      simp [RemovedForm.core] at hcore
    | r10 tY =>
      simp [RemovedForm.core] at hcore
    | r11j aY =>
      simp [RemovedForm.core] at hcore
    | r11aj aY =>
      simp [RemovedForm.core] at hcore
    | r11ak tY =>
      simp [RemovedForm.core] at hcore
    | r12 kY =>
      simp [RemovedForm.core] at hcore
    | r13cj bY =>
      have h0 := he (4*q)
      clear he
      simp only [RemovedForm.Valid] at hx hy
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 hx hy
      exfalso
      simp_all <;> omega
    | r13zj bY =>
      have h0 := he (bX)
      have h1 := he (bY)
      have h2 := he (bX+1)
      have h3 := he (bY+1)
      clear he
      simp only [RemovedForm.Valid] at hx hy
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 h1 h2 h3 hx hy
      have eq0 : bX=bY := by simp_all <;> omega
      cases eq0; rfl
    | r13czj bY =>
      have h0 := he (3*q+1)
      have h1 := he (3*q)
      clear he
      simp only [RemovedForm.Valid] at hx hy
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 h1 hx hy
      exfalso
      simp_all <;> omega
    | r13points kY =>
      have h0 := he (2*q+2)
      clear he
      simp only [RemovedForm.Valid] at hx hy
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 hx hy
      exfalso
      simp_all <;> omega
    | r14points kY =>
      simp [RemovedForm.core] at hcore
    | r14line tY =>
      simp [RemovedForm.core] at hcore
    | r14c tY =>
      simp [RemovedForm.core] at hcore
    | r15points kY =>
      simp [RemovedForm.core] at hcore
    | r15right aY =>
      simp [RemovedForm.core] at hcore
    | r15gap aY =>
      simp [RemovedForm.core] at hcore
    | r15line tY =>
      simp [RemovedForm.core] at hcore
    | r15short pY tY =>
      simp [RemovedForm.core] at hcore
  | r13czj bX =>
    cases y with
    | r2 =>
      simp [RemovedForm.core] at hcore
    | r3 =>
      simp [RemovedForm.core] at hcore
    | r4 kY =>
      simp [RemovedForm.core] at hcore
    | r5 =>
      simp [RemovedForm.core] at hcore
    | r6regular tY =>
      simp [RemovedForm.core] at hcore
    | r6exception =>
      simp [RemovedForm.core] at hcore
    | r6d pY =>
      simp [RemovedForm.core] at hcore
    | r7fresh kY =>
      simp [RemovedForm.core] at hcore
    | r7e pY =>
      simp [RemovedForm.core] at hcore
    | r7d pY =>
      simp [RemovedForm.core] at hcore
    | r10 tY =>
      simp [RemovedForm.core] at hcore
    | r11j aY =>
      simp [RemovedForm.core] at hcore
    | r11aj aY =>
      simp [RemovedForm.core] at hcore
    | r11ak tY =>
      simp [RemovedForm.core] at hcore
    | r12 kY =>
      simp [RemovedForm.core] at hcore
    | r13cj bY =>
      have h0 := he (4*q)
      clear he
      simp only [RemovedForm.Valid] at hx hy
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 hx hy
      exfalso
      simp_all <;> omega
    | r13zj bY =>
      have h0 := he (3*q+1)
      have h1 := he (3*q)
      clear he
      simp only [RemovedForm.Valid] at hx hy
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 h1 hx hy
      exfalso
      simp_all <;> omega
    | r13czj bY =>
      have h0 := he (bX)
      have h1 := he (bY)
      have h2 := he (bX+1)
      have h3 := he (bY+1)
      clear he
      simp only [RemovedForm.Valid] at hx hy
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 h1 h2 h3 hx hy
      have eq0 : bX=bY := by simp_all <;> omega
      cases eq0; rfl
    | r13points kY =>
      have h0 := he (3*q+1)
      clear he
      simp only [RemovedForm.Valid] at hx hy
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 hx hy
      exfalso
      simp_all <;> omega
    | r14points kY =>
      simp [RemovedForm.core] at hcore
    | r14line tY =>
      simp [RemovedForm.core] at hcore
    | r14c tY =>
      simp [RemovedForm.core] at hcore
    | r15points kY =>
      simp [RemovedForm.core] at hcore
    | r15right aY =>
      simp [RemovedForm.core] at hcore
    | r15gap aY =>
      simp [RemovedForm.core] at hcore
    | r15line tY =>
      simp [RemovedForm.core] at hcore
    | r15short pY tY =>
      simp [RemovedForm.core] at hcore
  | r13points kX =>
    cases y with
    | r2 =>
      simp [RemovedForm.core] at hcore
    | r3 =>
      simp [RemovedForm.core] at hcore
    | r4 kY =>
      simp [RemovedForm.core] at hcore
    | r5 =>
      simp [RemovedForm.core] at hcore
    | r6regular tY =>
      simp [RemovedForm.core] at hcore
    | r6exception =>
      simp [RemovedForm.core] at hcore
    | r6d pY =>
      simp [RemovedForm.core] at hcore
    | r7fresh kY =>
      simp [RemovedForm.core] at hcore
    | r7e pY =>
      simp [RemovedForm.core] at hcore
    | r7d pY =>
      simp [RemovedForm.core] at hcore
    | r10 tY =>
      simp [RemovedForm.core] at hcore
    | r11j aY =>
      simp [RemovedForm.core] at hcore
    | r11aj aY =>
      simp [RemovedForm.core] at hcore
    | r11ak tY =>
      simp [RemovedForm.core] at hcore
    | r12 kY =>
      simp [RemovedForm.core] at hcore
    | r13cj bY =>
      have h0 := he (3*q+1)
      clear he
      simp only [RemovedForm.Valid] at hx hy
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 hx hy
      exfalso
      simp_all <;> omega
    | r13zj bY =>
      have h0 := he (2*q+2)
      clear he
      simp only [RemovedForm.Valid] at hx hy
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 hx hy
      exfalso
      simp_all <;> omega
    | r13czj bY =>
      have h0 := he (3*q+1)
      clear he
      simp only [RemovedForm.Valid] at hx hy
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 hx hy
      exfalso
      simp_all <;> omega
    | r13points kY =>
      have eq0 := r13points_injective q kX kY hq hx hy he
      cases eq0
      rfl
    | r14points kY =>
      simp [RemovedForm.core] at hcore
    | r14line tY =>
      simp [RemovedForm.core] at hcore
    | r14c tY =>
      simp [RemovedForm.core] at hcore
    | r15points kY =>
      simp [RemovedForm.core] at hcore
    | r15right aY =>
      simp [RemovedForm.core] at hcore
    | r15gap aY =>
      simp [RemovedForm.core] at hcore
    | r15line tY =>
      simp [RemovedForm.core] at hcore
    | r15short pY tY =>
      simp [RemovedForm.core] at hcore
  | r14points kX =>
    cases y with
    | r2 =>
      simp [RemovedForm.core] at hcore
    | r3 =>
      simp [RemovedForm.core] at hcore
    | r4 kY =>
      simp [RemovedForm.core] at hcore
    | r5 =>
      simp [RemovedForm.core] at hcore
    | r6regular tY =>
      simp [RemovedForm.core] at hcore
    | r6exception =>
      simp [RemovedForm.core] at hcore
    | r6d pY =>
      simp [RemovedForm.core] at hcore
    | r7fresh kY =>
      simp [RemovedForm.core] at hcore
    | r7e pY =>
      simp [RemovedForm.core] at hcore
    | r7d pY =>
      simp [RemovedForm.core] at hcore
    | r10 tY =>
      simp [RemovedForm.core] at hcore
    | r11j aY =>
      simp [RemovedForm.core] at hcore
    | r11aj aY =>
      simp [RemovedForm.core] at hcore
    | r11ak tY =>
      simp [RemovedForm.core] at hcore
    | r12 kY =>
      simp [RemovedForm.core] at hcore
    | r13cj bY =>
      simp [RemovedForm.core] at hcore
    | r13zj bY =>
      simp [RemovedForm.core] at hcore
    | r13czj bY =>
      simp [RemovedForm.core] at hcore
    | r13points kY =>
      simp [RemovedForm.core] at hcore
    | r14points kY =>
      have eq0 := r14points_injective q kX kY hq hx hy he
      cases eq0
      rfl
    | r14line tY =>
      have h0 := he (2*q+3)
      clear he
      simp only [RemovedForm.Valid] at hx hy
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 hx hy
      exfalso
      simp_all <;> omega
    | r14c tY =>
      have h0 := he (2*q+3)
      clear he
      simp only [RemovedForm.Valid] at hx hy
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 hx hy
      exfalso
      simp_all <;> omega
    | r15points kY =>
      simp [RemovedForm.core] at hcore
    | r15right aY =>
      simp [RemovedForm.core] at hcore
    | r15gap aY =>
      simp [RemovedForm.core] at hcore
    | r15line tY =>
      simp [RemovedForm.core] at hcore
    | r15short pY tY =>
      simp [RemovedForm.core] at hcore
  | r14line tX =>
    cases y with
    | r2 =>
      simp [RemovedForm.core] at hcore
    | r3 =>
      simp [RemovedForm.core] at hcore
    | r4 kY =>
      simp [RemovedForm.core] at hcore
    | r5 =>
      simp [RemovedForm.core] at hcore
    | r6regular tY =>
      simp [RemovedForm.core] at hcore
    | r6exception =>
      simp [RemovedForm.core] at hcore
    | r6d pY =>
      simp [RemovedForm.core] at hcore
    | r7fresh kY =>
      simp [RemovedForm.core] at hcore
    | r7e pY =>
      simp [RemovedForm.core] at hcore
    | r7d pY =>
      simp [RemovedForm.core] at hcore
    | r10 tY =>
      simp [RemovedForm.core] at hcore
    | r11j aY =>
      simp [RemovedForm.core] at hcore
    | r11aj aY =>
      simp [RemovedForm.core] at hcore
    | r11ak tY =>
      simp [RemovedForm.core] at hcore
    | r12 kY =>
      simp [RemovedForm.core] at hcore
    | r13cj bY =>
      simp [RemovedForm.core] at hcore
    | r13zj bY =>
      simp [RemovedForm.core] at hcore
    | r13czj bY =>
      simp [RemovedForm.core] at hcore
    | r13points kY =>
      simp [RemovedForm.core] at hcore
    | r14points kY =>
      have h0 := he (2*q+3)
      clear he
      simp only [RemovedForm.Valid] at hx hy
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 hx hy
      exfalso
      simp_all <;> omega
    | r14line tY =>
      have h0 := he (tX)
      have h1 := he (tY)
      have h2 := he (tX+1)
      have h3 := he (tY+1)
      clear he
      simp only [RemovedForm.Valid] at hx hy
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 h1 h2 h3 hx hy
      have eq0 : tX=tY := by simp_all <;> omega
      cases eq0; rfl
    | r14c tY =>
      have h0 := he (2*q+2)
      clear he
      simp only [RemovedForm.Valid] at hx hy
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 hx hy
      exfalso
      simp_all <;> omega
    | r15points kY =>
      simp [RemovedForm.core] at hcore
    | r15right aY =>
      simp [RemovedForm.core] at hcore
    | r15gap aY =>
      simp [RemovedForm.core] at hcore
    | r15line tY =>
      simp [RemovedForm.core] at hcore
    | r15short pY tY =>
      simp [RemovedForm.core] at hcore
  | r14c tX =>
    cases y with
    | r2 =>
      simp [RemovedForm.core] at hcore
    | r3 =>
      simp [RemovedForm.core] at hcore
    | r4 kY =>
      simp [RemovedForm.core] at hcore
    | r5 =>
      simp [RemovedForm.core] at hcore
    | r6regular tY =>
      simp [RemovedForm.core] at hcore
    | r6exception =>
      simp [RemovedForm.core] at hcore
    | r6d pY =>
      simp [RemovedForm.core] at hcore
    | r7fresh kY =>
      simp [RemovedForm.core] at hcore
    | r7e pY =>
      simp [RemovedForm.core] at hcore
    | r7d pY =>
      simp [RemovedForm.core] at hcore
    | r10 tY =>
      simp [RemovedForm.core] at hcore
    | r11j aY =>
      simp [RemovedForm.core] at hcore
    | r11aj aY =>
      simp [RemovedForm.core] at hcore
    | r11ak tY =>
      simp [RemovedForm.core] at hcore
    | r12 kY =>
      simp [RemovedForm.core] at hcore
    | r13cj bY =>
      simp [RemovedForm.core] at hcore
    | r13zj bY =>
      simp [RemovedForm.core] at hcore
    | r13czj bY =>
      simp [RemovedForm.core] at hcore
    | r13points kY =>
      simp [RemovedForm.core] at hcore
    | r14points kY =>
      have h0 := he (2*q+3)
      clear he
      simp only [RemovedForm.Valid] at hx hy
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 hx hy
      exfalso
      simp_all <;> omega
    | r14line tY =>
      have h0 := he (2*q+2)
      clear he
      simp only [RemovedForm.Valid] at hx hy
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 hx hy
      exfalso
      simp_all <;> omega
    | r14c tY =>
      have h0 := he (tX)
      have h1 := he (tY)
      have h2 := he (tX+1)
      have h3 := he (tY+1)
      clear he
      simp only [RemovedForm.Valid] at hx hy
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 h1 h2 h3 hx hy
      have eq0 : tX=tY := by simp_all <;> omega
      cases eq0; rfl
    | r15points kY =>
      simp [RemovedForm.core] at hcore
    | r15right aY =>
      simp [RemovedForm.core] at hcore
    | r15gap aY =>
      simp [RemovedForm.core] at hcore
    | r15line tY =>
      simp [RemovedForm.core] at hcore
    | r15short pY tY =>
      simp [RemovedForm.core] at hcore
  | r15points kX =>
    cases y with
    | r2 =>
      simp [RemovedForm.core] at hcore
    | r3 =>
      simp [RemovedForm.core] at hcore
    | r4 kY =>
      simp [RemovedForm.core] at hcore
    | r5 =>
      simp [RemovedForm.core] at hcore
    | r6regular tY =>
      simp [RemovedForm.core] at hcore
    | r6exception =>
      simp [RemovedForm.core] at hcore
    | r6d pY =>
      simp [RemovedForm.core] at hcore
    | r7fresh kY =>
      simp [RemovedForm.core] at hcore
    | r7e pY =>
      simp [RemovedForm.core] at hcore
    | r7d pY =>
      simp [RemovedForm.core] at hcore
    | r10 tY =>
      simp [RemovedForm.core] at hcore
    | r11j aY =>
      simp [RemovedForm.core] at hcore
    | r11aj aY =>
      simp [RemovedForm.core] at hcore
    | r11ak tY =>
      simp [RemovedForm.core] at hcore
    | r12 kY =>
      simp [RemovedForm.core] at hcore
    | r13cj bY =>
      simp [RemovedForm.core] at hcore
    | r13zj bY =>
      simp [RemovedForm.core] at hcore
    | r13czj bY =>
      simp [RemovedForm.core] at hcore
    | r13points kY =>
      simp [RemovedForm.core] at hcore
    | r14points kY =>
      simp [RemovedForm.core] at hcore
    | r14line tY =>
      simp [RemovedForm.core] at hcore
    | r14c tY =>
      simp [RemovedForm.core] at hcore
    | r15points kY =>
      have eq0 := r15points_injective q kX kY hq hx hy he
      cases eq0
      rfl
    | r15right aY =>
      have h0 := he (5)
      clear he
      simp only [RemovedForm.Valid] at hx hy
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 hx hy
      exfalso
      simp_all <;> omega
    | r15gap aY =>
      have h0 := he (2*q+2)
      clear he
      simp only [RemovedForm.Valid] at hx hy
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 hx hy
      exfalso
      simp_all <;> omega
    | r15line tY =>
      have h0 := he (4*q)
      have h1 := he (2*q+3)
      clear he
      simp only [RemovedForm.Valid] at hx hy
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 h1 hx hy
      exfalso
      simp_all <;> omega
    | r15short pY tY =>
      have h0 := he (4*q)
      have h1 := he (2*q+1)
      clear he
      simp only [RemovedForm.Valid] at hx hy
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 h1 hx hy
      exfalso
      simp_all <;> omega
  | r15right aX =>
    cases y with
    | r2 =>
      simp [RemovedForm.core] at hcore
    | r3 =>
      simp [RemovedForm.core] at hcore
    | r4 kY =>
      simp [RemovedForm.core] at hcore
    | r5 =>
      simp [RemovedForm.core] at hcore
    | r6regular tY =>
      simp [RemovedForm.core] at hcore
    | r6exception =>
      simp [RemovedForm.core] at hcore
    | r6d pY =>
      simp [RemovedForm.core] at hcore
    | r7fresh kY =>
      simp [RemovedForm.core] at hcore
    | r7e pY =>
      simp [RemovedForm.core] at hcore
    | r7d pY =>
      simp [RemovedForm.core] at hcore
    | r10 tY =>
      simp [RemovedForm.core] at hcore
    | r11j aY =>
      simp [RemovedForm.core] at hcore
    | r11aj aY =>
      simp [RemovedForm.core] at hcore
    | r11ak tY =>
      simp [RemovedForm.core] at hcore
    | r12 kY =>
      simp [RemovedForm.core] at hcore
    | r13cj bY =>
      simp [RemovedForm.core] at hcore
    | r13zj bY =>
      simp [RemovedForm.core] at hcore
    | r13czj bY =>
      simp [RemovedForm.core] at hcore
    | r13points kY =>
      simp [RemovedForm.core] at hcore
    | r14points kY =>
      simp [RemovedForm.core] at hcore
    | r14line tY =>
      simp [RemovedForm.core] at hcore
    | r14c tY =>
      simp [RemovedForm.core] at hcore
    | r15points kY =>
      have h0 := he (5)
      clear he
      simp only [RemovedForm.Valid] at hx hy
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 hx hy
      exfalso
      simp_all <;> omega
    | r15right aY =>
      have h0 := he (aX)
      have h1 := he (aY)
      have h2 := he (aX+1)
      have h3 := he (aY+1)
      clear he
      simp only [RemovedForm.Valid] at hx hy
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 h1 h2 h3 hx hy
      have eq0 : aX=aY := by simp_all <;> omega
      cases eq0; rfl
    | r15gap aY =>
      have h0 := he (5)
      clear he
      simp only [RemovedForm.Valid] at hx hy
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 hx hy
      exfalso
      simp_all <;> omega
    | r15line tY =>
      have h0 := he (4*q-1)
      clear he
      simp only [RemovedForm.Valid] at hx hy
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 hx hy
      exfalso
      simp_all <;> omega
    | r15short pY tY =>
      have h0 := he (4*q-1)
      clear he
      simp only [RemovedForm.Valid] at hx hy
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 hx hy
      exfalso
      simp_all <;> omega
  | r15gap aX =>
    cases y with
    | r2 =>
      simp [RemovedForm.core] at hcore
    | r3 =>
      simp [RemovedForm.core] at hcore
    | r4 kY =>
      simp [RemovedForm.core] at hcore
    | r5 =>
      simp [RemovedForm.core] at hcore
    | r6regular tY =>
      simp [RemovedForm.core] at hcore
    | r6exception =>
      simp [RemovedForm.core] at hcore
    | r6d pY =>
      simp [RemovedForm.core] at hcore
    | r7fresh kY =>
      simp [RemovedForm.core] at hcore
    | r7e pY =>
      simp [RemovedForm.core] at hcore
    | r7d pY =>
      simp [RemovedForm.core] at hcore
    | r10 tY =>
      simp [RemovedForm.core] at hcore
    | r11j aY =>
      simp [RemovedForm.core] at hcore
    | r11aj aY =>
      simp [RemovedForm.core] at hcore
    | r11ak tY =>
      simp [RemovedForm.core] at hcore
    | r12 kY =>
      simp [RemovedForm.core] at hcore
    | r13cj bY =>
      simp [RemovedForm.core] at hcore
    | r13zj bY =>
      simp [RemovedForm.core] at hcore
    | r13czj bY =>
      simp [RemovedForm.core] at hcore
    | r13points kY =>
      simp [RemovedForm.core] at hcore
    | r14points kY =>
      simp [RemovedForm.core] at hcore
    | r14line tY =>
      simp [RemovedForm.core] at hcore
    | r14c tY =>
      simp [RemovedForm.core] at hcore
    | r15points kY =>
      have h0 := he (2*q+2)
      clear he
      simp only [RemovedForm.Valid] at hx hy
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 hx hy
      exfalso
      simp_all <;> omega
    | r15right aY =>
      have h0 := he (5)
      clear he
      simp only [RemovedForm.Valid] at hx hy
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 hx hy
      exfalso
      simp_all <;> omega
    | r15gap aY =>
      have h0 := he (aX)
      have h1 := he (aY)
      have h2 := he (aX+1)
      have h3 := he (aY+1)
      clear he
      simp only [RemovedForm.Valid] at hx hy
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 h1 h2 h3 hx hy
      have eq0 : aX=aY := by simp_all <;> omega
      cases eq0; rfl
    | r15line tY =>
      have h0 := he (4*q-1)
      clear he
      simp only [RemovedForm.Valid] at hx hy
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 hx hy
      exfalso
      simp_all <;> omega
    | r15short pY tY =>
      have h0 := he (4*q-1)
      clear he
      simp only [RemovedForm.Valid] at hx hy
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 hx hy
      exfalso
      simp_all <;> omega
  | r15line tX =>
    cases y with
    | r2 =>
      simp [RemovedForm.core] at hcore
    | r3 =>
      simp [RemovedForm.core] at hcore
    | r4 kY =>
      simp [RemovedForm.core] at hcore
    | r5 =>
      simp [RemovedForm.core] at hcore
    | r6regular tY =>
      simp [RemovedForm.core] at hcore
    | r6exception =>
      simp [RemovedForm.core] at hcore
    | r6d pY =>
      simp [RemovedForm.core] at hcore
    | r7fresh kY =>
      simp [RemovedForm.core] at hcore
    | r7e pY =>
      simp [RemovedForm.core] at hcore
    | r7d pY =>
      simp [RemovedForm.core] at hcore
    | r10 tY =>
      simp [RemovedForm.core] at hcore
    | r11j aY =>
      simp [RemovedForm.core] at hcore
    | r11aj aY =>
      simp [RemovedForm.core] at hcore
    | r11ak tY =>
      simp [RemovedForm.core] at hcore
    | r12 kY =>
      simp [RemovedForm.core] at hcore
    | r13cj bY =>
      simp [RemovedForm.core] at hcore
    | r13zj bY =>
      simp [RemovedForm.core] at hcore
    | r13czj bY =>
      simp [RemovedForm.core] at hcore
    | r13points kY =>
      simp [RemovedForm.core] at hcore
    | r14points kY =>
      simp [RemovedForm.core] at hcore
    | r14line tY =>
      simp [RemovedForm.core] at hcore
    | r14c tY =>
      simp [RemovedForm.core] at hcore
    | r15points kY =>
      have h0 := he (4*q)
      have h1 := he (2*q+3)
      clear he
      simp only [RemovedForm.Valid] at hx hy
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 h1 hx hy
      exfalso
      simp_all <;> omega
    | r15right aY =>
      have h0 := he (4*q-1)
      clear he
      simp only [RemovedForm.Valid] at hx hy
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 hx hy
      exfalso
      simp_all <;> omega
    | r15gap aY =>
      have h0 := he (4*q-1)
      clear he
      simp only [RemovedForm.Valid] at hx hy
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 hx hy
      exfalso
      simp_all <;> omega
    | r15line tY =>
      have h0 := he (tX)
      have h1 := he (tY)
      have h2 := he (tX+1)
      have h3 := he (tY+1)
      clear he
      simp only [RemovedForm.Valid] at hx hy
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 h1 h2 h3 hx hy
      have eq0 : tX=tY := by simp_all <;> omega
      cases eq0; rfl
    | r15short pY tY =>
      have h0 := he (2*q+1)
      clear he
      simp only [RemovedForm.Valid] at hx hy
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 hx hy
      exfalso
      simp_all <;> omega
  | r15short pX tX =>
    cases y with
    | r2 =>
      simp [RemovedForm.core] at hcore
    | r3 =>
      simp [RemovedForm.core] at hcore
    | r4 kY =>
      simp [RemovedForm.core] at hcore
    | r5 =>
      simp [RemovedForm.core] at hcore
    | r6regular tY =>
      simp [RemovedForm.core] at hcore
    | r6exception =>
      simp [RemovedForm.core] at hcore
    | r6d pY =>
      simp [RemovedForm.core] at hcore
    | r7fresh kY =>
      simp [RemovedForm.core] at hcore
    | r7e pY =>
      simp [RemovedForm.core] at hcore
    | r7d pY =>
      simp [RemovedForm.core] at hcore
    | r10 tY =>
      simp [RemovedForm.core] at hcore
    | r11j aY =>
      simp [RemovedForm.core] at hcore
    | r11aj aY =>
      simp [RemovedForm.core] at hcore
    | r11ak tY =>
      simp [RemovedForm.core] at hcore
    | r12 kY =>
      simp [RemovedForm.core] at hcore
    | r13cj bY =>
      simp [RemovedForm.core] at hcore
    | r13zj bY =>
      simp [RemovedForm.core] at hcore
    | r13czj bY =>
      simp [RemovedForm.core] at hcore
    | r13points kY =>
      simp [RemovedForm.core] at hcore
    | r14points kY =>
      simp [RemovedForm.core] at hcore
    | r14line tY =>
      simp [RemovedForm.core] at hcore
    | r14c tY =>
      simp [RemovedForm.core] at hcore
    | r15points kY =>
      have h0 := he (4*q)
      have h1 := he (2*q+1)
      clear he
      simp only [RemovedForm.Valid] at hx hy
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 h1 hx hy
      exfalso
      simp_all <;> omega
    | r15right aY =>
      have h0 := he (4*q-1)
      clear he
      simp only [RemovedForm.Valid] at hx hy
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 hx hy
      exfalso
      simp_all <;> omega
    | r15gap aY =>
      have h0 := he (4*q-1)
      clear he
      simp only [RemovedForm.Valid] at hx hy
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 hx hy
      exfalso
      simp_all <;> omega
    | r15line tY =>
      have h0 := he (2*q+1)
      clear he
      simp only [RemovedForm.Valid] at hx hy
      simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 hx hy
      exfalso
      simp_all <;> omega
    | r15short pY tY =>
      have eq0 := r15short_injective q pX tX pY tY hq hx hy he
      cases eq0.1
      cases eq0.2
      rfl

theorem added_form_unique (q : Nat) (hq : 4≤q) (x y : AddedForm)
    (hx : x.Valid q) (hy : y.Valid q) (he : ∀e,x.eval q e ↔ y.eval q e) : x=y := by
  have hcx := AddedForm.core_mask q hq x hx
  have hcy := AddedForm.core_mask q hq y hy
  have hcore : x.core=y.core := core_mask_unique x.core y.core (by cases x <;> simp [AddedForm.core]) (by cases y <;> simp [AddedForm.core]) (x.eval q) hcx ((core_mask_congr y.core (x.eval q) (y.eval q) he).mpr hcy)
  clear hcx hcy
  cases x with
  | n4 kX =>
    cases y with
    | n4 kY =>
      have eq0 := n4_injective q kX kY hq hx hy he
      cases eq0
      rfl
    | n5 kY =>
      simp [AddedForm.core] at hcore
    | n6regular tY =>
      simp [AddedForm.core] at hcore
    | n6exception =>
      simp [AddedForm.core] at hcore
    | n6e pY =>
      simp [AddedForm.core] at hcore
    | n7regular tY =>
      simp [AddedForm.core] at hcore
    | n7exception =>
      simp [AddedForm.core] at hcore
    | n7right tY =>
      simp [AddedForm.core] at hcore
    | n7point =>
      simp [AddedForm.core] at hcore
    | n10 tY =>
      simp [AddedForm.core] at hcore
    | n11j aY =>
      simp [AddedForm.core] at hcore
    | n11aj aY =>
      simp [AddedForm.core] at hcore
    | n11ak tY =>
      simp [AddedForm.core] at hcore
    | n13plain bY =>
      simp [AddedForm.core] at hcore
    | n13isolated bY =>
      simp [AddedForm.core] at hcore
    | n13right bY =>
      simp [AddedForm.core] at hcore
  | n5 kX =>
    cases y with
    | n4 kY =>
      simp [AddedForm.core] at hcore
    | n5 kY =>
      have eq0 := n5_injective q kX kY hq hx hy he
      cases eq0
      rfl
    | n6regular tY =>
      simp [AddedForm.core] at hcore
    | n6exception =>
      simp [AddedForm.core] at hcore
    | n6e pY =>
      simp [AddedForm.core] at hcore
    | n7regular tY =>
      simp [AddedForm.core] at hcore
    | n7exception =>
      simp [AddedForm.core] at hcore
    | n7right tY =>
      simp [AddedForm.core] at hcore
    | n7point =>
      simp [AddedForm.core] at hcore
    | n10 tY =>
      simp [AddedForm.core] at hcore
    | n11j aY =>
      simp [AddedForm.core] at hcore
    | n11aj aY =>
      simp [AddedForm.core] at hcore
    | n11ak tY =>
      simp [AddedForm.core] at hcore
    | n13plain bY =>
      simp [AddedForm.core] at hcore
    | n13isolated bY =>
      simp [AddedForm.core] at hcore
    | n13right bY =>
      simp [AddedForm.core] at hcore
  | n6regular tX =>
    cases y with
    | n4 kY =>
      simp [AddedForm.core] at hcore
    | n5 kY =>
      simp [AddedForm.core] at hcore
    | n6regular tY =>
      have eq0 := added6regular_injective q tX tY hq hx hy he
      cases eq0
      rfl
    | n6exception =>
      have h0 := he (4*q)
      clear he
      simp only [AddedForm.Valid] at hx hy
      simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 hx hy
      exfalso
      simp_all <;> omega
    | n6e pY =>
      have h0 := he (2*q+3)
      clear he
      simp only [AddedForm.Valid] at hx hy
      simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 hx hy
      exfalso
      simp_all <;> omega
    | n7regular tY =>
      simp [AddedForm.core] at hcore
    | n7exception =>
      simp [AddedForm.core] at hcore
    | n7right tY =>
      simp [AddedForm.core] at hcore
    | n7point =>
      simp [AddedForm.core] at hcore
    | n10 tY =>
      simp [AddedForm.core] at hcore
    | n11j aY =>
      simp [AddedForm.core] at hcore
    | n11aj aY =>
      simp [AddedForm.core] at hcore
    | n11ak tY =>
      simp [AddedForm.core] at hcore
    | n13plain bY =>
      simp [AddedForm.core] at hcore
    | n13isolated bY =>
      simp [AddedForm.core] at hcore
    | n13right bY =>
      simp [AddedForm.core] at hcore
  | n6exception =>
    cases y with
    | n4 kY =>
      simp [AddedForm.core] at hcore
    | n5 kY =>
      simp [AddedForm.core] at hcore
    | n6regular tY =>
      have h0 := he (4*q)
      clear he
      simp only [AddedForm.Valid] at hx hy
      simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 hx hy
      exfalso
      simp_all <;> omega
    | n6exception =>
      rfl
    | n6e pY =>
      have h0 := he (4*q)
      clear he
      simp only [AddedForm.Valid] at hx hy
      simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 hx hy
      exfalso
      simp_all <;> omega
    | n7regular tY =>
      simp [AddedForm.core] at hcore
    | n7exception =>
      simp [AddedForm.core] at hcore
    | n7right tY =>
      simp [AddedForm.core] at hcore
    | n7point =>
      simp [AddedForm.core] at hcore
    | n10 tY =>
      simp [AddedForm.core] at hcore
    | n11j aY =>
      simp [AddedForm.core] at hcore
    | n11aj aY =>
      simp [AddedForm.core] at hcore
    | n11ak tY =>
      simp [AddedForm.core] at hcore
    | n13plain bY =>
      simp [AddedForm.core] at hcore
    | n13isolated bY =>
      simp [AddedForm.core] at hcore
    | n13right bY =>
      simp [AddedForm.core] at hcore
  | n6e pX =>
    cases y with
    | n4 kY =>
      simp [AddedForm.core] at hcore
    | n5 kY =>
      simp [AddedForm.core] at hcore
    | n6regular tY =>
      have h0 := he (2*q+3)
      clear he
      simp only [AddedForm.Valid] at hx hy
      simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 hx hy
      exfalso
      simp_all <;> omega
    | n6exception =>
      have h0 := he (4*q)
      clear he
      simp only [AddedForm.Valid] at hx hy
      simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 hx hy
      exfalso
      simp_all <;> omega
    | n6e pY =>
      have h0 := he (pX)
      have h1 := he (pY)
      have h2 := he (pX+1)
      have h3 := he (pY+1)
      clear he
      simp only [AddedForm.Valid] at hx hy
      simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 h1 h2 h3 hx hy
      have eq0 : pX=pY := by simp_all <;> omega
      cases eq0; rfl
    | n7regular tY =>
      simp [AddedForm.core] at hcore
    | n7exception =>
      simp [AddedForm.core] at hcore
    | n7right tY =>
      simp [AddedForm.core] at hcore
    | n7point =>
      simp [AddedForm.core] at hcore
    | n10 tY =>
      simp [AddedForm.core] at hcore
    | n11j aY =>
      simp [AddedForm.core] at hcore
    | n11aj aY =>
      simp [AddedForm.core] at hcore
    | n11ak tY =>
      simp [AddedForm.core] at hcore
    | n13plain bY =>
      simp [AddedForm.core] at hcore
    | n13isolated bY =>
      simp [AddedForm.core] at hcore
    | n13right bY =>
      simp [AddedForm.core] at hcore
  | n7regular tX =>
    cases y with
    | n4 kY =>
      simp [AddedForm.core] at hcore
    | n5 kY =>
      simp [AddedForm.core] at hcore
    | n6regular tY =>
      simp [AddedForm.core] at hcore
    | n6exception =>
      simp [AddedForm.core] at hcore
    | n6e pY =>
      simp [AddedForm.core] at hcore
    | n7regular tY =>
      have eq0 := added7regular_injective q tX tY hq hx hy he
      cases eq0
      rfl
    | n7exception =>
      have h0 := he (4*q)
      clear he
      simp only [AddedForm.Valid] at hx hy
      simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 hx hy
      exfalso
      simp_all <;> omega
    | n7right tY =>
      have h0 := he (2*q+2)
      clear he
      simp only [AddedForm.Valid] at hx hy
      simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 hx hy
      exfalso
      simp_all <;> omega
    | n7point =>
      have h0 := he (2*q+3)
      clear he
      simp only [AddedForm.Valid] at hx hy
      simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 hx hy
      exfalso
      simp_all <;> omega
    | n10 tY =>
      simp [AddedForm.core] at hcore
    | n11j aY =>
      simp [AddedForm.core] at hcore
    | n11aj aY =>
      simp [AddedForm.core] at hcore
    | n11ak tY =>
      simp [AddedForm.core] at hcore
    | n13plain bY =>
      simp [AddedForm.core] at hcore
    | n13isolated bY =>
      simp [AddedForm.core] at hcore
    | n13right bY =>
      simp [AddedForm.core] at hcore
  | n7exception =>
    cases y with
    | n4 kY =>
      simp [AddedForm.core] at hcore
    | n5 kY =>
      simp [AddedForm.core] at hcore
    | n6regular tY =>
      simp [AddedForm.core] at hcore
    | n6exception =>
      simp [AddedForm.core] at hcore
    | n6e pY =>
      simp [AddedForm.core] at hcore
    | n7regular tY =>
      have h0 := he (4*q)
      clear he
      simp only [AddedForm.Valid] at hx hy
      simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 hx hy
      exfalso
      simp_all <;> omega
    | n7exception =>
      rfl
    | n7right tY =>
      have h0 := he (2*q+2)
      clear he
      simp only [AddedForm.Valid] at hx hy
      simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 hx hy
      exfalso
      simp_all <;> omega
    | n7point =>
      have h0 := he (4*q)
      clear he
      simp only [AddedForm.Valid] at hx hy
      simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 hx hy
      exfalso
      simp_all <;> omega
    | n10 tY =>
      simp [AddedForm.core] at hcore
    | n11j aY =>
      simp [AddedForm.core] at hcore
    | n11aj aY =>
      simp [AddedForm.core] at hcore
    | n11ak tY =>
      simp [AddedForm.core] at hcore
    | n13plain bY =>
      simp [AddedForm.core] at hcore
    | n13isolated bY =>
      simp [AddedForm.core] at hcore
    | n13right bY =>
      simp [AddedForm.core] at hcore
  | n7right tX =>
    cases y with
    | n4 kY =>
      simp [AddedForm.core] at hcore
    | n5 kY =>
      simp [AddedForm.core] at hcore
    | n6regular tY =>
      simp [AddedForm.core] at hcore
    | n6exception =>
      simp [AddedForm.core] at hcore
    | n6e pY =>
      simp [AddedForm.core] at hcore
    | n7regular tY =>
      have h0 := he (2*q+2)
      clear he
      simp only [AddedForm.Valid] at hx hy
      simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 hx hy
      exfalso
      simp_all <;> omega
    | n7exception =>
      have h0 := he (2*q+2)
      clear he
      simp only [AddedForm.Valid] at hx hy
      simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 hx hy
      exfalso
      simp_all <;> omega
    | n7right tY =>
      have eq0 := n7right_injective q tX tY hq hx hy he
      cases eq0
      rfl
    | n7point =>
      have h0 := he (2*q+2)
      clear he
      simp only [AddedForm.Valid] at hx hy
      simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 hx hy
      exfalso
      simp_all <;> omega
    | n10 tY =>
      simp [AddedForm.core] at hcore
    | n11j aY =>
      simp [AddedForm.core] at hcore
    | n11aj aY =>
      simp [AddedForm.core] at hcore
    | n11ak tY =>
      simp [AddedForm.core] at hcore
    | n13plain bY =>
      simp [AddedForm.core] at hcore
    | n13isolated bY =>
      simp [AddedForm.core] at hcore
    | n13right bY =>
      simp [AddedForm.core] at hcore
  | n7point =>
    cases y with
    | n4 kY =>
      simp [AddedForm.core] at hcore
    | n5 kY =>
      simp [AddedForm.core] at hcore
    | n6regular tY =>
      simp [AddedForm.core] at hcore
    | n6exception =>
      simp [AddedForm.core] at hcore
    | n6e pY =>
      simp [AddedForm.core] at hcore
    | n7regular tY =>
      have h0 := he (2*q+3)
      clear he
      simp only [AddedForm.Valid] at hx hy
      simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 hx hy
      exfalso
      simp_all <;> omega
    | n7exception =>
      have h0 := he (4*q)
      clear he
      simp only [AddedForm.Valid] at hx hy
      simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 hx hy
      exfalso
      simp_all <;> omega
    | n7right tY =>
      have h0 := he (2*q+2)
      clear he
      simp only [AddedForm.Valid] at hx hy
      simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 hx hy
      exfalso
      simp_all <;> omega
    | n7point =>
      rfl
    | n10 tY =>
      simp [AddedForm.core] at hcore
    | n11j aY =>
      simp [AddedForm.core] at hcore
    | n11aj aY =>
      simp [AddedForm.core] at hcore
    | n11ak tY =>
      simp [AddedForm.core] at hcore
    | n13plain bY =>
      simp [AddedForm.core] at hcore
    | n13isolated bY =>
      simp [AddedForm.core] at hcore
    | n13right bY =>
      simp [AddedForm.core] at hcore
  | n10 tX =>
    cases y with
    | n4 kY =>
      simp [AddedForm.core] at hcore
    | n5 kY =>
      simp [AddedForm.core] at hcore
    | n6regular tY =>
      simp [AddedForm.core] at hcore
    | n6exception =>
      simp [AddedForm.core] at hcore
    | n6e pY =>
      simp [AddedForm.core] at hcore
    | n7regular tY =>
      simp [AddedForm.core] at hcore
    | n7exception =>
      simp [AddedForm.core] at hcore
    | n7right tY =>
      simp [AddedForm.core] at hcore
    | n7point =>
      simp [AddedForm.core] at hcore
    | n10 tY =>
      have h0 := he (2*q+1)
      have h1 := he (2*q+2)
      clear he
      simp only [AddedForm.Valid] at hx hy
      simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 h1 hx hy
      have eq0 : tX=tY := by simp_all <;> omega
      cases eq0; rfl
    | n11j aY =>
      simp [AddedForm.core] at hcore
    | n11aj aY =>
      simp [AddedForm.core] at hcore
    | n11ak tY =>
      simp [AddedForm.core] at hcore
    | n13plain bY =>
      simp [AddedForm.core] at hcore
    | n13isolated bY =>
      simp [AddedForm.core] at hcore
    | n13right bY =>
      simp [AddedForm.core] at hcore
  | n11j aX =>
    cases y with
    | n4 kY =>
      simp [AddedForm.core] at hcore
    | n5 kY =>
      simp [AddedForm.core] at hcore
    | n6regular tY =>
      simp [AddedForm.core] at hcore
    | n6exception =>
      simp [AddedForm.core] at hcore
    | n6e pY =>
      simp [AddedForm.core] at hcore
    | n7regular tY =>
      simp [AddedForm.core] at hcore
    | n7exception =>
      simp [AddedForm.core] at hcore
    | n7right tY =>
      simp [AddedForm.core] at hcore
    | n7point =>
      simp [AddedForm.core] at hcore
    | n10 tY =>
      simp [AddedForm.core] at hcore
    | n11j aY =>
      have h0 := he (aX)
      have h1 := he (aY)
      have h2 := he (aX+1)
      have h3 := he (aY+1)
      clear he
      simp only [AddedForm.Valid] at hx hy
      simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 h1 h2 h3 hx hy
      have eq0 : aX=aY := by simp_all <;> omega
      cases eq0; rfl
    | n11aj aY =>
      have h0 := he (5)
      have h1 := he (q+3)
      clear he
      simp only [AddedForm.Valid] at hx hy
      simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 h1 hx hy
      exfalso
      simp_all <;> omega
    | n11ak tY =>
      have h0 := he (2*q+1)
      clear he
      simp only [AddedForm.Valid] at hx hy
      simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 hx hy
      exfalso
      simp_all <;> omega
    | n13plain bY =>
      simp [AddedForm.core] at hcore
    | n13isolated bY =>
      simp [AddedForm.core] at hcore
    | n13right bY =>
      simp [AddedForm.core] at hcore
  | n11aj aX =>
    cases y with
    | n4 kY =>
      simp [AddedForm.core] at hcore
    | n5 kY =>
      simp [AddedForm.core] at hcore
    | n6regular tY =>
      simp [AddedForm.core] at hcore
    | n6exception =>
      simp [AddedForm.core] at hcore
    | n6e pY =>
      simp [AddedForm.core] at hcore
    | n7regular tY =>
      simp [AddedForm.core] at hcore
    | n7exception =>
      simp [AddedForm.core] at hcore
    | n7right tY =>
      simp [AddedForm.core] at hcore
    | n7point =>
      simp [AddedForm.core] at hcore
    | n10 tY =>
      simp [AddedForm.core] at hcore
    | n11j aY =>
      have h0 := he (5)
      have h1 := he (q+3)
      clear he
      simp only [AddedForm.Valid] at hx hy
      simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 h1 hx hy
      exfalso
      simp_all <;> omega
    | n11aj aY =>
      have h0 := he (aX)
      have h1 := he (aY)
      have h2 := he (aX+1)
      have h3 := he (aY+1)
      clear he
      simp only [AddedForm.Valid] at hx hy
      simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 h1 h2 h3 hx hy
      have eq0 : aX=aY := by simp_all <;> omega
      cases eq0; rfl
    | n11ak tY =>
      have h0 := he (2*q+1)
      clear he
      simp only [AddedForm.Valid] at hx hy
      simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 hx hy
      exfalso
      simp_all <;> omega
    | n13plain bY =>
      simp [AddedForm.core] at hcore
    | n13isolated bY =>
      simp [AddedForm.core] at hcore
    | n13right bY =>
      simp [AddedForm.core] at hcore
  | n11ak tX =>
    cases y with
    | n4 kY =>
      simp [AddedForm.core] at hcore
    | n5 kY =>
      simp [AddedForm.core] at hcore
    | n6regular tY =>
      simp [AddedForm.core] at hcore
    | n6exception =>
      simp [AddedForm.core] at hcore
    | n6e pY =>
      simp [AddedForm.core] at hcore
    | n7regular tY =>
      simp [AddedForm.core] at hcore
    | n7exception =>
      simp [AddedForm.core] at hcore
    | n7right tY =>
      simp [AddedForm.core] at hcore
    | n7point =>
      simp [AddedForm.core] at hcore
    | n10 tY =>
      simp [AddedForm.core] at hcore
    | n11j aY =>
      have h0 := he (2*q+1)
      clear he
      simp only [AddedForm.Valid] at hx hy
      simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 hx hy
      exfalso
      simp_all <;> omega
    | n11aj aY =>
      have h0 := he (2*q+1)
      clear he
      simp only [AddedForm.Valid] at hx hy
      simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 hx hy
      exfalso
      simp_all <;> omega
    | n11ak tY =>
      have h0 := he (2*q+2)
      clear he
      simp only [AddedForm.Valid] at hx hy
      simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 hx hy
      have eq0 : tX=tY := by simp_all <;> omega
      cases eq0; rfl
    | n13plain bY =>
      simp [AddedForm.core] at hcore
    | n13isolated bY =>
      simp [AddedForm.core] at hcore
    | n13right bY =>
      simp [AddedForm.core] at hcore
  | n13plain bX =>
    cases y with
    | n4 kY =>
      simp [AddedForm.core] at hcore
    | n5 kY =>
      simp [AddedForm.core] at hcore
    | n6regular tY =>
      simp [AddedForm.core] at hcore
    | n6exception =>
      simp [AddedForm.core] at hcore
    | n6e pY =>
      simp [AddedForm.core] at hcore
    | n7regular tY =>
      simp [AddedForm.core] at hcore
    | n7exception =>
      simp [AddedForm.core] at hcore
    | n7right tY =>
      simp [AddedForm.core] at hcore
    | n7point =>
      simp [AddedForm.core] at hcore
    | n10 tY =>
      simp [AddedForm.core] at hcore
    | n11j aY =>
      simp [AddedForm.core] at hcore
    | n11aj aY =>
      simp [AddedForm.core] at hcore
    | n11ak tY =>
      simp [AddedForm.core] at hcore
    | n13plain bY =>
      have h0 := he (bX)
      have h1 := he (bY)
      have h2 := he (bX+1)
      have h3 := he (bY+1)
      clear he
      simp only [AddedForm.Valid] at hx hy
      simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 h1 h2 h3 hx hy
      have eq0 : bX=bY := by simp_all <;> omega
      cases eq0; rfl
    | n13isolated bY =>
      have h0 := he (4*q-1)
      clear he
      simp only [AddedForm.Valid] at hx hy
      simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 hx hy
      exfalso
      simp_all <;> omega
    | n13right bY =>
      have h0 := he (4*q-1)
      clear he
      simp only [AddedForm.Valid] at hx hy
      simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 hx hy
      exfalso
      simp_all <;> omega
  | n13isolated bX =>
    cases y with
    | n4 kY =>
      simp [AddedForm.core] at hcore
    | n5 kY =>
      simp [AddedForm.core] at hcore
    | n6regular tY =>
      simp [AddedForm.core] at hcore
    | n6exception =>
      simp [AddedForm.core] at hcore
    | n6e pY =>
      simp [AddedForm.core] at hcore
    | n7regular tY =>
      simp [AddedForm.core] at hcore
    | n7exception =>
      simp [AddedForm.core] at hcore
    | n7right tY =>
      simp [AddedForm.core] at hcore
    | n7point =>
      simp [AddedForm.core] at hcore
    | n10 tY =>
      simp [AddedForm.core] at hcore
    | n11j aY =>
      simp [AddedForm.core] at hcore
    | n11aj aY =>
      simp [AddedForm.core] at hcore
    | n11ak tY =>
      simp [AddedForm.core] at hcore
    | n13plain bY =>
      have h0 := he (4*q-1)
      clear he
      simp only [AddedForm.Valid] at hx hy
      simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 hx hy
      exfalso
      simp_all <;> omega
    | n13isolated bY =>
      have h0 := he (bX)
      have h1 := he (bY)
      have h2 := he (bX+1)
      have h3 := he (bY+1)
      clear he
      simp only [AddedForm.Valid] at hx hy
      simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 h1 h2 h3 hx hy
      have eq0 : bX=bY := by simp_all <;> omega
      cases eq0; rfl
    | n13right bY =>
      have h0 := he (3*q)
      clear he
      simp only [AddedForm.Valid] at hx hy
      simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 hx hy
      exfalso
      simp_all <;> omega
  | n13right bX =>
    cases y with
    | n4 kY =>
      simp [AddedForm.core] at hcore
    | n5 kY =>
      simp [AddedForm.core] at hcore
    | n6regular tY =>
      simp [AddedForm.core] at hcore
    | n6exception =>
      simp [AddedForm.core] at hcore
    | n6e pY =>
      simp [AddedForm.core] at hcore
    | n7regular tY =>
      simp [AddedForm.core] at hcore
    | n7exception =>
      simp [AddedForm.core] at hcore
    | n7right tY =>
      simp [AddedForm.core] at hcore
    | n7point =>
      simp [AddedForm.core] at hcore
    | n10 tY =>
      simp [AddedForm.core] at hcore
    | n11j aY =>
      simp [AddedForm.core] at hcore
    | n11aj aY =>
      simp [AddedForm.core] at hcore
    | n11ak tY =>
      simp [AddedForm.core] at hcore
    | n13plain bY =>
      have h0 := he (4*q-1)
      clear he
      simp only [AddedForm.Valid] at hx hy
      simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 hx hy
      exfalso
      simp_all <;> omega
    | n13isolated bY =>
      have h0 := he (3*q)
      clear he
      simp only [AddedForm.Valid] at hx hy
      simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 hx hy
      exfalso
      simp_all <;> omega
    | n13right bY =>
      have h0 := he (bX)
      have h1 := he (bY)
      have h2 := he (bX+1)
      have h3 := he (bY+1)
      clear he
      simp only [AddedForm.Valid] at hx hy
      simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,Suffix,I,P] at h0 h1 h2 h3 hx hy
      have eq0 : bX=bY := by simp_all <;> omega
      cases eq0; rfl

end LuRazSixRowClosure.Difference
