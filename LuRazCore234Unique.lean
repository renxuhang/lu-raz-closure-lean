import LuRazCore234Exact
namespace LuRazClosure
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

theorem NF234.unique (q : Nat) (hq : 4≤q) (z w : NF234)
    (hz : z.Valid q) (hw : w.Valid q) (heq : ∀ e, z.eval q e ↔ w.eval q e) : z=w := by
  cases z with
  | kr p k =>
    cases w with
    | kr c l =>
      simp only [NF234.Valid] at hz hw
      simp only [P] at hz hw
      have h0 := heq (p+1)
      have h1 := heq (c+1)
      have h2 := heq (2*q+2)
      simp only [NF234.eval,T234,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0 h1 h2
      have hp : p=c := by omega
      subst c
      have hk : k=l := by omega
      subst l
      rfl
    | dg c =>
      simp only [NF234.Valid] at hz hw
      simp only [P] at hz hw
      have h0 := heq (2*q+1)
      have h1 := heq (2*q)
      simp only [NF234.eval,T234,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0 h1
      exfalso
      omega
    | km l =>
      simp only [NF234.Valid] at hz hw
      simp only [P] at hz hw
      have h0 := heq (4*q)
      simp only [NF234.eval,T234,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | ck l =>
      simp only [NF234.Valid] at hz hw
      simp only [P] at hz hw
      have h0 := heq (4*q)
      simp only [NF234.eval,T234,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | last  =>
      simp only [NF234.Valid] at hz hw
      simp only [P] at hz hw
      have h0 := heq (4*q-1)
      simp only [NF234.eval,T234,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
  | dg p =>
    cases w with
    | kr c l =>
      simp only [NF234.Valid] at hz hw
      simp only [P] at hz hw
      have h0 := heq (2*q+1)
      have h1 := heq (2*q)
      simp only [NF234.eval,T234,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0 h1
      exfalso
      omega
    | dg c =>
      simp only [NF234.Valid] at hz hw
      simp only [P] at hz hw
      have h0 := heq (p+1)
      have h1 := heq (c+1)
      simp only [NF234.eval,T234,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0 h1
      have hp : p=c := by omega
      subst c
      rfl
    | km l =>
      simp only [NF234.Valid] at hz hw
      simp only [P] at hz hw
      have h0 := heq (4*q)
      simp only [NF234.eval,T234,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | ck l =>
      simp only [NF234.Valid] at hz hw
      simp only [P] at hz hw
      have h0 := heq (4*q)
      simp only [NF234.eval,T234,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | last  =>
      simp only [NF234.Valid] at hz hw
      simp only [P] at hz hw
      have h0 := heq (4*q-1)
      simp only [NF234.eval,T234,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
  | km k =>
    cases w with
    | kr c l =>
      simp only [NF234.Valid] at hz hw
      simp only [P] at hz hw
      have h0 := heq (4*q)
      simp only [NF234.eval,T234,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | dg c =>
      simp only [NF234.Valid] at hz hw
      simp only [P] at hz hw
      have h0 := heq (4*q)
      simp only [NF234.eval,T234,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | km l =>
      simp only [NF234.Valid] at hz hw
      have h0 := heq (2*q+2)
      simp only [NF234.eval,T234,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      have hk : k=l := by omega
      subst l
      rfl
    | ck l =>
      simp only [NF234.Valid] at hz hw
      have h0 := heq (q+4)
      simp only [NF234.eval,T234,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | last  =>
      simp only [NF234.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NF234.eval,T234,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
  | ck k =>
    cases w with
    | kr c l =>
      simp only [NF234.Valid] at hz hw
      simp only [P] at hz hw
      have h0 := heq (4*q)
      simp only [NF234.eval,T234,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | dg c =>
      simp only [NF234.Valid] at hz hw
      simp only [P] at hz hw
      have h0 := heq (4*q)
      simp only [NF234.eval,T234,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | km l =>
      simp only [NF234.Valid] at hz hw
      have h0 := heq (q+4)
      simp only [NF234.eval,T234,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | ck l =>
      simp only [NF234.Valid] at hz hw
      have h0 := heq (4*q-1)
      simp only [NF234.eval,T234,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      have hk : k=l := by omega
      subst l
      rfl
    | last  =>
      simp only [NF234.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NF234.eval,T234,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
  | last  =>
    cases w with
    | kr c l =>
      simp only [NF234.Valid] at hz hw
      simp only [P] at hz hw
      have h0 := heq (4*q-1)
      simp only [NF234.eval,T234,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | dg c =>
      simp only [NF234.Valid] at hz hw
      simp only [P] at hz hw
      have h0 := heq (4*q-1)
      simp only [NF234.eval,T234,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | km l =>
      simp only [NF234.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NF234.eval,T234,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | ck l =>
      simp only [NF234.Valid] at hz hw
      have h0 := heq (4*q)
      simp only [NF234.eval,T234,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | last  =>
      rfl
end LuRazClosure
