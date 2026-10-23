import LuRazFullExact
namespace LuRazClosure
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

theorem NFFull.unique (q : Nat) (hq : 4≤q) (z w : NFFull)
    (hz : z.Valid q) (hw : w.Valid q) (heq : ∀ e, z.eval q e ↔ w.eval q e) : z=w := by
  cases z with
  | noNInterval k =>
    cases w with
    | noNInterval l =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q-1)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      have hk : k=l := by omega
      subst l
      rfl
    | noNMJRight d =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (3*q+1)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noNMJLeft u =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (q+4)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noNMK l =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (q+4)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noNCMJ d =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (3*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noH1Short r l =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noH1ZL u =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noH1Exception  =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noH2 u =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noFive u =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | leftGap r u =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | full  =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | rightGap d f =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | isolatedR d f =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
  | noNMJRight b =>
    cases w with
    | noNInterval l =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (3*q+1)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noNMJRight d =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (b+1)
      have h1 := heq (d+1)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0 h1
      have hb : b=d := by omega
      subst d
      rfl
    | noNMJLeft u =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (q+4)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noNMK l =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (q+4)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noNCMJ d =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (3*q+1)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noH1Short r l =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noH1ZL u =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noH1Exception  =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noH2 u =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noFive u =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | leftGap r u =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | full  =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | rightGap d f =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | isolatedR d f =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
  | noNMJLeft a =>
    cases w with
    | noNInterval l =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (q+4)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noNMJRight d =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (q+4)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noNMJLeft u =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (a)
      have h1 := heq (u)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0 h1
      have ha : a=u := by omega
      subst u
      rfl
    | noNMK l =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (2*q+1)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noNCMJ d =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (q+4)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noH1Short r l =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noH1ZL u =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noH1Exception  =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noH2 u =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noFive u =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | leftGap r u =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | full  =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | rightGap d f =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | isolatedR d f =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
  | noNMK k =>
    cases w with
    | noNInterval l =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (q+4)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noNMJRight d =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (q+4)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noNMJLeft u =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (2*q+1)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noNMK l =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (2*q+2)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      have hk : k=l := by omega
      subst l
      rfl
    | noNCMJ d =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (q+4)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noH1Short r l =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noH1ZL u =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noH1Exception  =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noH2 u =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noFive u =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | leftGap r u =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | full  =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | rightGap d f =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | isolatedR d f =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
  | noNCMJ b =>
    cases w with
    | noNInterval l =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (3*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noNMJRight d =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (3*q+1)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noNMJLeft u =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (q+4)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noNMK l =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (q+4)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noNCMJ d =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (b+1)
      have h1 := heq (d+1)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0 h1
      have hb : b=d := by omega
      subst d
      rfl
    | noH1Short r l =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noH1ZL u =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noH1Exception  =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noH2 u =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noFive u =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | leftGap r u =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | full  =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | rightGap d f =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | isolatedR d f =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
  | noH1Short p k =>
    cases w with
    | noNInterval l =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noNMJRight d =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noNMJLeft u =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noNMK l =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noNCMJ d =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noH1Short r l =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (p+1)
      have h1 := heq (r+1)
      have h2 := heq (2*q+2)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0 h1 h2
      have hp : p=r := by omega
      subst r
      have hk : k=l := by omega
      subst l
      rfl
    | noH1ZL u =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (2*q+3)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noH1Exception  =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q-1)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noH2 u =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (2*q+1)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noFive u =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (2*q+1)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | leftGap r u =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (2*q+1)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | full  =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (2*q+1)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | rightGap d f =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (2*q+1)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | isolatedR d f =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (2*q+1)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
  | noH1ZL a =>
    cases w with
    | noNInterval l =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noNMJRight d =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noNMJLeft u =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noNMK l =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noNCMJ d =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noH1Short r l =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (2*q+3)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noH1ZL u =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (a)
      have h1 := heq (u)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0 h1
      have ha : a=u := by omega
      subst u
      rfl
    | noH1Exception  =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (2*q+2)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noH2 u =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (2*q+1)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noFive u =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (2*q+1)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | leftGap r u =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (2*q+1)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | full  =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (2*q+1)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | rightGap d f =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (2*q+1)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | isolatedR d f =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (2*q+1)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
  | noH1Exception  =>
    cases w with
    | noNInterval l =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noNMJRight d =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noNMJLeft u =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noNMK l =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noNCMJ d =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noH1Short r l =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q-1)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noH1ZL u =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (2*q+2)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noH1Exception  =>
      rfl
    | noH2 u =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (2*q+1)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noFive u =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (2*q+1)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | leftGap r u =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (2*q+1)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | full  =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (2*q+1)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | rightGap d f =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (2*q+1)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | isolatedR d f =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (2*q+1)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
  | noH2 a =>
    cases w with
    | noNInterval l =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noNMJRight d =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noNMJLeft u =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noNMK l =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noNCMJ d =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noH1Short r l =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (2*q+1)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noH1ZL u =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (2*q+1)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noH1Exception  =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (2*q+1)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noH2 u =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (a)
      have h1 := heq (u)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0 h1
      have ha : a=u := by omega
      subst u
      rfl
    | noFive u =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (2*q+2)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | leftGap r u =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (2*q+2)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | full  =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (2*q+2)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | rightGap d f =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (2*q+2)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | isolatedR d f =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (2*q+2)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
  | noFive a =>
    cases w with
    | noNInterval l =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noNMJRight d =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noNMJLeft u =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noNMK l =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noNCMJ d =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noH1Short r l =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (2*q+1)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noH1ZL u =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (2*q+1)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noH1Exception  =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (2*q+1)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noH2 u =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (2*q+2)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noFive u =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (a)
      have h1 := heq (u)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0 h1
      have ha : a=u := by omega
      subst u
      rfl
    | leftGap r u =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (5)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | full  =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (5)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | rightGap d f =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (5)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | isolatedR d f =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (5)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
  | leftGap p a =>
    cases w with
    | noNInterval l =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noNMJRight d =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noNMJLeft u =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noNMK l =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noNCMJ d =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noH1Short r l =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (2*q+1)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noH1ZL u =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (2*q+1)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noH1Exception  =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (2*q+1)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noH2 u =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (2*q+2)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noFive u =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (5)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | leftGap r u =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (p+1)
      have h1 := heq (r+1)
      have h2 := heq (a)
      have h3 := heq (u)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0 h1 h2 h3
      have hp : p=r := by omega
      subst r
      have ha : a=u := by omega
      subst u
      rfl
    | full  =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (p+1)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | rightGap d f =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (p+1)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | isolatedR d f =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (p+1)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
  | full  =>
    cases w with
    | noNInterval l =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noNMJRight d =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noNMJLeft u =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noNMK l =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noNCMJ d =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noH1Short r l =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (2*q+1)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noH1ZL u =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (2*q+1)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noH1Exception  =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (2*q+1)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noH2 u =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (2*q+2)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noFive u =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (5)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | leftGap r u =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (r+1)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | full  =>
      rfl
    | rightGap d f =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (d+1)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | isolatedR d f =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (d+1)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
  | rightGap b c =>
    cases w with
    | noNInterval l =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noNMJRight d =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noNMJLeft u =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noNMK l =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noNCMJ d =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noH1Short r l =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (2*q+1)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noH1ZL u =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (2*q+1)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noH1Exception  =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (2*q+1)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noH2 u =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (2*q+2)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noFive u =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (5)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | leftGap r u =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (r+1)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | full  =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (b+1)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | rightGap d f =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (b+1)
      have h1 := heq (d+1)
      have h2 := heq (c)
      have h3 := heq (f)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0 h1 h2 h3
      have hb : b=d := by omega
      subst d
      have hc : c=f := by omega
      subst f
      rfl
    | isolatedR d f =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (3*q)
      have h1 := heq (3*q+1)
      have h2 := heq (3*q+2)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0 h1 h2
      exfalso
      omega
  | isolatedR b c =>
    cases w with
    | noNInterval l =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noNMJRight d =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noNMJLeft u =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noNMK l =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noNCMJ d =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noH1Short r l =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (2*q+1)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noH1ZL u =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (2*q+1)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noH1Exception  =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (2*q+1)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noH2 u =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (2*q+2)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | noFive u =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (5)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | leftGap r u =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (r+1)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | full  =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (b+1)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | rightGap d f =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (3*q)
      have h1 := heq (3*q+1)
      have h2 := heq (3*q+2)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0 h1 h2
      exfalso
      omega
    | isolatedR d f =>
      simp only [NFFull.Valid] at hz hw
      have h0 := heq (b+1)
      have h1 := heq (d+1)
      have h2 := heq (c)
      have h3 := heq (f)
      simp only [NFFull.eval,FullHead,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0 h1 h2 h3
      have hb : b=d := by omega
      subst d
      have hc : c=f := by omega
      subst f
      rfl
end LuRazClosure
