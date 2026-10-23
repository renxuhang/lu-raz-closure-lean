import LuRazCore124Normal
namespace LuRazClosure
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

theorem a_disjoint24 (q : Nat) (hq : 4≤q) (z : NF24) (e : Nat) (ha : ARow q e) : ¬z.eval q e := by
  cases z <;> simp only [NF24.eval,K1Row,K2Row,DRow,BRow,I] <;>
    (unfold ARow I at ha; omega)

theorem nf24_no_middle (q : Nat) (hq : 4≤q) (z : NF24) (hz : z≠.dBig) : ¬z.eval q (2*q+1) := by
  cases z <;> simp only [NF24.eval,K1Row,K2Row,DRow,BRow,I] <;> (simp_all <;> omega)

theorem NF124.unique (q : Nat) (hq : 4≤q) (z w : NF124)
    (hz : z.Valid q) (hw : w.Valid q) (heq : ∀ e, z.eval q e ↔ w.eval q e) : z=w := by
  have hA : ¬ARow q (2*q+1) := by unfold ARow I; omega
  cases z with
  | interval a k =>
    have hzb : (5≤a ∧ a≤2*q+1) ∧ k<3 := hz
    cases w with
    | interval c l =>
      have hwb : (5≤c ∧ c≤2*q+1) ∧ l<3 := hw
      have h0 := heq (a)
      change T124 a (4*q-2+k) (a) ↔ T124 c (4*q-2+l) (a) at h0
      have h1 := heq (c)
      change T124 a (4*q-2+k) (c) ↔ T124 c (4*q-2+l) (c) at h1
      have h2 := heq (4*q-2+k)
      change T124 a (4*q-2+k) (4*q-2+k) ↔ T124 c (4*q-2+l) (4*q-2+k) at h2
      have h3 := heq (4*q-2+l)
      change T124 a (4*q-2+k) (4*q-2+l) ↔ T124 c (4*q-2+l) (4*q-2+l) at h3
      simp only [T124,ARow,I] at h0 h1 h2 h3
      have hac : a=c := by omega
      have hkl : k=l := by omega
      subst c; subst l; rfl
    | agap c l =>
      have hwb : (q+4≤c ∧ c≤2*q+1) ∧ l<3 := hw
      have h0 := heq (5)
      change T124 a (4*q-2+k) (5) ↔ (T124 c (4*q-2+l) (5) ∨ ARow q (5)) at h0
      have h1 := heq (q+3)
      change T124 a (4*q-2+k) (q+3) ↔ (T124 c (4*q-2+l) (q+3) ∨ ARow q (q+3)) at h1
      simp only [T124,ARow,I] at h0 h1
      exfalso
      omega
    | ak w24 =>
      have hw24 := nf24_no_middle q hq w24 hw
      have h0 := heq (2*q+1)
      change T124 a (4*q-2+k) (2*q+1) ↔ (ARow q (2*q+1) ∨ NF24.eval q w24 (2*q+1)) at h0
      simp only [hA,hw24,false_or,iff_false,false_iff] at h0
      simp only [T124,ARow,I] at h0
      exfalso
      omega
  | agap a k =>
    have hzb : (q+4≤a ∧ a≤2*q+1) ∧ k<3 := hz
    cases w with
    | interval c l =>
      have hwb : (5≤c ∧ c≤2*q+1) ∧ l<3 := hw
      have h0 := heq (5)
      change (T124 a (4*q-2+k) (5) ∨ ARow q (5)) ↔ T124 c (4*q-2+l) (5) at h0
      have h1 := heq (q+3)
      change (T124 a (4*q-2+k) (q+3) ∨ ARow q (q+3)) ↔ T124 c (4*q-2+l) (q+3) at h1
      simp only [T124,ARow,I] at h0 h1
      exfalso
      omega
    | agap c l =>
      have hwb : (q+4≤c ∧ c≤2*q+1) ∧ l<3 := hw
      have h0 := heq (a)
      change (T124 a (4*q-2+k) (a) ∨ ARow q (a)) ↔ (T124 c (4*q-2+l) (a) ∨ ARow q (a)) at h0
      have h1 := heq (c)
      change (T124 a (4*q-2+k) (c) ∨ ARow q (c)) ↔ (T124 c (4*q-2+l) (c) ∨ ARow q (c)) at h1
      have h2 := heq (4*q-2+k)
      change (T124 a (4*q-2+k) (4*q-2+k) ∨ ARow q (4*q-2+k)) ↔ (T124 c (4*q-2+l) (4*q-2+k) ∨ ARow q (4*q-2+k)) at h2
      have h3 := heq (4*q-2+l)
      change (T124 a (4*q-2+k) (4*q-2+l) ∨ ARow q (4*q-2+l)) ↔ (T124 c (4*q-2+l) (4*q-2+l) ∨ ARow q (4*q-2+l)) at h3
      simp only [T124,ARow,I] at h0 h1 h2 h3
      have hac : a=c := by omega
      have hkl : k=l := by omega
      subst c; subst l; rfl
    | ak w24 =>
      have hw24 := nf24_no_middle q hq w24 hw
      have h0 := heq (2*q+1)
      change (T124 a (4*q-2+k) (2*q+1) ∨ ARow q (2*q+1)) ↔ (ARow q (2*q+1) ∨ NF24.eval q w24 (2*q+1)) at h0
      simp only [hA,hw24,false_or,iff_false,false_iff] at h0
      simp only [T124,ARow,I] at h0
      exfalso
      omega
  | ak z24 =>
    have hz24 := nf24_no_middle q hq z24 hz
    cases w with
    | interval c l =>
      have hwb : (5≤c ∧ c≤2*q+1) ∧ l<3 := hw
      have h0 := heq (2*q+1)
      change (ARow q (2*q+1) ∨ NF24.eval q z24 (2*q+1)) ↔ T124 c (4*q-2+l) (2*q+1) at h0
      simp only [hA,hz24,false_or,iff_false,false_iff] at h0
      simp only [T124,ARow,I] at h0
      exfalso
      omega
    | agap c l =>
      have hwb : (q+4≤c ∧ c≤2*q+1) ∧ l<3 := hw
      have h0 := heq (2*q+1)
      change (ARow q (2*q+1) ∨ NF24.eval q z24 (2*q+1)) ↔ (T124 c (4*q-2+l) (2*q+1) ∨ ARow q (2*q+1)) at h0
      simp only [hA,hz24,false_or,iff_false,false_iff] at h0
      simp only [T124,ARow,I] at h0
      exfalso
      omega
    | ak w24 =>
      have hw24 := nf24_no_middle q hq w24 hw
      have hzw : z24=w24 := by
        apply NF24.unique q hq z24 w24
        intro e
        by_cases ha : ARow q e
        · have hnz := a_disjoint24 q hq z24 e ha
          have hnw := a_disjoint24 q hq w24 e ha
          simp only [hnz,hnw]
        · simpa only [NF124.eval,ha,false_or] using heq e
      subst w24; rfl

end LuRazClosure
