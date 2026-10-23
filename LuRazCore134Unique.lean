import LuRazCore134Exact
namespace LuRazClosure
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000

theorem NF134.unique (q : Nat) (hq : 4≤q) (z w : NF134)
    (hz : z.Valid q) (hw : w.Valid q) (heq : ∀ e, z.eval q e ↔ w.eval q e) : z=w := by
  cases z with
  | ej a =>
    cases w with
    | ej c =>
      simp only [NF134.Valid] at hz hw
      have h0 := heq (a)
      have h1 := heq (c)
      simp only [NF134.eval,T134,ZRow,BRow,ERow,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0 h1
      have h : a=c := by omega
      subst c; rfl
    | aej c =>
      simp only [NF134.Valid] at hz hw
      have h0 := heq (5)
      have h1 := heq (q+3)
      simp only [NF134.eval,T134,ZRow,BRow,ERow,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0 h1
      exfalso
      omega
    | cj d =>
      simp only [NF134.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NF134.eval,T134,ZRow,BRow,ERow,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | zj d =>
      simp only [NF134.Valid] at hz hw
      have h0 := heq (4*q-1)
      simp only [NF134.eval,T134,ZRow,BRow,ERow,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | czj d =>
      simp only [NF134.Valid] at hz hw
      have h0 := heq (4*q-1)
      simp only [NF134.eval,T134,ZRow,BRow,ERow,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | zjb d =>
      simp only [NF134.Valid] at hz hw
      have h0 := heq (3*q+1)
      simp only [NF134.eval,T134,ZRow,BRow,ERow,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | cjb d =>
      simp only [NF134.Valid] at hz hw
      have h0 := heq (3*q)
      simp only [NF134.eval,T134,ZRow,BRow,ERow,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | extra l =>
      simp only [NF134.Valid] at hz hw
      have h0 := heq (2*q+1)
      simp only [NF134.eval,T134,ZRow,BRow,ERow,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
  | aej a =>
    cases w with
    | ej c =>
      simp only [NF134.Valid] at hz hw
      have h0 := heq (5)
      have h1 := heq (q+3)
      simp only [NF134.eval,T134,ZRow,BRow,ERow,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0 h1
      exfalso
      omega
    | aej c =>
      simp only [NF134.Valid] at hz hw
      have h0 := heq (a)
      have h1 := heq (c)
      simp only [NF134.eval,T134,ZRow,BRow,ERow,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0 h1
      have h : a=c := by omega
      subst c; rfl
    | cj d =>
      simp only [NF134.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NF134.eval,T134,ZRow,BRow,ERow,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | zj d =>
      simp only [NF134.Valid] at hz hw
      have h0 := heq (4*q-1)
      simp only [NF134.eval,T134,ZRow,BRow,ERow,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | czj d =>
      simp only [NF134.Valid] at hz hw
      have h0 := heq (4*q-1)
      simp only [NF134.eval,T134,ZRow,BRow,ERow,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | zjb d =>
      simp only [NF134.Valid] at hz hw
      have h0 := heq (3*q+1)
      simp only [NF134.eval,T134,ZRow,BRow,ERow,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | cjb d =>
      simp only [NF134.Valid] at hz hw
      have h0 := heq (3*q)
      simp only [NF134.eval,T134,ZRow,BRow,ERow,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | extra l =>
      simp only [NF134.Valid] at hz hw
      have h0 := heq (2*q+1)
      simp only [NF134.eval,T134,ZRow,BRow,ERow,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
  | cj b =>
    cases w with
    | ej c =>
      simp only [NF134.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NF134.eval,T134,ZRow,BRow,ERow,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | aej c =>
      simp only [NF134.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NF134.eval,T134,ZRow,BRow,ERow,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | cj d =>
      simp only [NF134.Valid] at hz hw
      have h0 := heq (b+1)
      have h1 := heq (d+1)
      simp only [NF134.eval,T134,ZRow,BRow,ERow,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0 h1
      have h : b=d := by omega
      subst d; rfl
    | zj d =>
      simp only [NF134.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NF134.eval,T134,ZRow,BRow,ERow,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | czj d =>
      simp only [NF134.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NF134.eval,T134,ZRow,BRow,ERow,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | zjb d =>
      simp only [NF134.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NF134.eval,T134,ZRow,BRow,ERow,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | cjb d =>
      simp only [NF134.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NF134.eval,T134,ZRow,BRow,ERow,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | extra l =>
      simp only [NF134.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NF134.eval,T134,ZRow,BRow,ERow,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
  | zj b =>
    cases w with
    | ej c =>
      simp only [NF134.Valid] at hz hw
      have h0 := heq (4*q-1)
      simp only [NF134.eval,T134,ZRow,BRow,ERow,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | aej c =>
      simp only [NF134.Valid] at hz hw
      have h0 := heq (4*q-1)
      simp only [NF134.eval,T134,ZRow,BRow,ERow,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | cj d =>
      simp only [NF134.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NF134.eval,T134,ZRow,BRow,ERow,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | zj d =>
      simp only [NF134.Valid] at hz hw
      have h0 := heq (b+1)
      have h1 := heq (d+1)
      simp only [NF134.eval,T134,ZRow,BRow,ERow,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0 h1
      have h : b=d := by omega
      subst d; rfl
    | czj d =>
      simp only [NF134.Valid] at hz hw
      have h0 := heq (3*q+1)
      have h1 := heq (3*q)
      simp only [NF134.eval,T134,ZRow,BRow,ERow,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0 h1
      exfalso
      omega
    | zjb d =>
      simp only [NF134.Valid] at hz hw
      have h0 := heq (4*q-1)
      simp only [NF134.eval,T134,ZRow,BRow,ERow,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | cjb d =>
      simp only [NF134.Valid] at hz hw
      have h0 := heq (4*q-1)
      simp only [NF134.eval,T134,ZRow,BRow,ERow,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | extra l =>
      simp only [NF134.Valid] at hz hw
      have h0 := heq (2*q+2)
      simp only [NF134.eval,T134,ZRow,BRow,ERow,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
  | czj b =>
    cases w with
    | ej c =>
      simp only [NF134.Valid] at hz hw
      have h0 := heq (4*q-1)
      simp only [NF134.eval,T134,ZRow,BRow,ERow,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | aej c =>
      simp only [NF134.Valid] at hz hw
      have h0 := heq (4*q-1)
      simp only [NF134.eval,T134,ZRow,BRow,ERow,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | cj d =>
      simp only [NF134.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NF134.eval,T134,ZRow,BRow,ERow,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | zj d =>
      simp only [NF134.Valid] at hz hw
      have h0 := heq (3*q+1)
      have h1 := heq (3*q)
      simp only [NF134.eval,T134,ZRow,BRow,ERow,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0 h1
      exfalso
      omega
    | czj d =>
      simp only [NF134.Valid] at hz hw
      have h0 := heq (b+1)
      have h1 := heq (d+1)
      simp only [NF134.eval,T134,ZRow,BRow,ERow,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0 h1
      have h : b=d := by omega
      subst d; rfl
    | zjb d =>
      simp only [NF134.Valid] at hz hw
      have h0 := heq (4*q-1)
      simp only [NF134.eval,T134,ZRow,BRow,ERow,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | cjb d =>
      simp only [NF134.Valid] at hz hw
      have h0 := heq (4*q-1)
      simp only [NF134.eval,T134,ZRow,BRow,ERow,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | extra l =>
      simp only [NF134.Valid] at hz hw
      have h0 := heq (2*q+2)
      simp only [NF134.eval,T134,ZRow,BRow,ERow,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
  | zjb b =>
    cases w with
    | ej c =>
      simp only [NF134.Valid] at hz hw
      have h0 := heq (3*q+1)
      simp only [NF134.eval,T134,ZRow,BRow,ERow,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | aej c =>
      simp only [NF134.Valid] at hz hw
      have h0 := heq (3*q+1)
      simp only [NF134.eval,T134,ZRow,BRow,ERow,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | cj d =>
      simp only [NF134.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NF134.eval,T134,ZRow,BRow,ERow,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | zj d =>
      simp only [NF134.Valid] at hz hw
      have h0 := heq (4*q-1)
      simp only [NF134.eval,T134,ZRow,BRow,ERow,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | czj d =>
      simp only [NF134.Valid] at hz hw
      have h0 := heq (4*q-1)
      simp only [NF134.eval,T134,ZRow,BRow,ERow,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | zjb d =>
      simp only [NF134.Valid] at hz hw
      have h0 := heq (b+1)
      have h1 := heq (d+1)
      simp only [NF134.eval,T134,ZRow,BRow,ERow,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0 h1
      have h : b=d := by omega
      subst d; rfl
    | cjb d =>
      simp only [NF134.Valid] at hz hw
      have h0 := heq (3*q+1)
      simp only [NF134.eval,T134,ZRow,BRow,ERow,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | extra l =>
      simp only [NF134.Valid] at hz hw
      have h0 := heq (2*q+2)
      simp only [NF134.eval,T134,ZRow,BRow,ERow,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
  | cjb b =>
    cases w with
    | ej c =>
      simp only [NF134.Valid] at hz hw
      have h0 := heq (3*q)
      simp only [NF134.eval,T134,ZRow,BRow,ERow,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | aej c =>
      simp only [NF134.Valid] at hz hw
      have h0 := heq (3*q)
      simp only [NF134.eval,T134,ZRow,BRow,ERow,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | cj d =>
      simp only [NF134.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NF134.eval,T134,ZRow,BRow,ERow,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | zj d =>
      simp only [NF134.Valid] at hz hw
      have h0 := heq (4*q-1)
      simp only [NF134.eval,T134,ZRow,BRow,ERow,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | czj d =>
      simp only [NF134.Valid] at hz hw
      have h0 := heq (4*q-1)
      simp only [NF134.eval,T134,ZRow,BRow,ERow,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | zjb d =>
      simp only [NF134.Valid] at hz hw
      have h0 := heq (3*q+1)
      simp only [NF134.eval,T134,ZRow,BRow,ERow,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | cjb d =>
      simp only [NF134.Valid] at hz hw
      have h0 := heq (b+1)
      have h1 := heq (d+1)
      simp only [NF134.eval,T134,ZRow,BRow,ERow,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0 h1
      have h : b=d := by omega
      subst d; rfl
    | extra l =>
      simp only [NF134.Valid] at hz hw
      have h0 := heq (2*q+2)
      simp only [NF134.eval,T134,ZRow,BRow,ERow,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
  | extra k =>
    cases w with
    | ej c =>
      simp only [NF134.Valid] at hz hw
      have h0 := heq (2*q+1)
      simp only [NF134.eval,T134,ZRow,BRow,ERow,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | aej c =>
      simp only [NF134.Valid] at hz hw
      have h0 := heq (2*q+1)
      simp only [NF134.eval,T134,ZRow,BRow,ERow,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | cj d =>
      simp only [NF134.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NF134.eval,T134,ZRow,BRow,ERow,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | zj d =>
      simp only [NF134.Valid] at hz hw
      have h0 := heq (2*q+2)
      simp only [NF134.eval,T134,ZRow,BRow,ERow,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | czj d =>
      simp only [NF134.Valid] at hz hw
      have h0 := heq (2*q+2)
      simp only [NF134.eval,T134,ZRow,BRow,ERow,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | zjb d =>
      simp only [NF134.Valid] at hz hw
      have h0 := heq (2*q+2)
      simp only [NF134.eval,T134,ZRow,BRow,ERow,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | cjb d =>
      simp only [NF134.Valid] at hz hw
      have h0 := heq (2*q+2)
      simp only [NF134.eval,T134,ZRow,BRow,ERow,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | extra l =>
      simp only [NF134.Valid] at hz hw
      have h0 := heq (2*q+3)
      have h1 := heq (3*q+2)
      simp only [NF134.eval,T134,ZRow,BRow,ERow,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0 h1
      have h : k=l := by omega
      subst l; rfl
end LuRazClosure
