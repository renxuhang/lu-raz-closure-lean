import SixRowCore14Original

namespace LuRazSixRowClosure
open LuRazClosure LuRazParametric LuRazEnumeration
set_option maxRecDepth 32768
set_option maxHeartbeats 14000000
set_option linter.unusedSimpArgs false

def Cut14 : NF234 → Prop
  | .km k => k=0 | .ck k => k=1 | .last => False | _ => True

theorem generated_l14 (q p : Nat) (hq : 4≤q) (hp : P q p) (hps : p≤2*q) :
    Generated q (LRow q p p) :=
  generated_congr q (generated_row q (LIndex q p)
    (by unfold LIndex beta; unfold P at hp; split <;> omega))
    (fun e => l_source14 q p e hq hp hps)

theorem generated_d14 (q : Nat) (hq : 4≤q) : Generated q (DPrime14 q) :=
  generated_congr q (generated_row q 1 (by omega)) (fun e => d_source14 q e hq)

theorem generated_e14 (q : Nat) (hq : 4≤q) : Generated q (E14 q) :=
  generated_congr q (generated_row q 4 (by omega)) (fun e => e_source14 q e hq)

theorem generated_k114 (q : Nat) (hq : 4≤q) : Generated q (K1Row q) :=
  generated_congr q (generated_row q (2*q+1) (by omega)) (fun e => k1_source14 q e hq)

theorem generated_k214 (q : Nat) (hq : 4≤q) : Generated q (KPrime14 q) :=
  generated_congr q (generated_row q (2*q+2) (by omega)) (fun e => k2_source14 q e hq)

theorem generated_c14 (q : Nat) (hq : 4≤q) : Generated q (CPrime q) :=
  generated_congr q (generated_row q (4*q) (by omega)) (fun e => c_source q e hq)

theorem normal14_retained_generated (q : Nat) (hq : 4≤q) (w : NF234)
    (hw : w.Valid q) (hcut : Cut14 w) : Generated q (w.eval q) := by
  cases w with
  | kr p k =>
    have hp : P q p := hw.1
    have hk : k=0 ∨ k=1 := by have := hw.2; omega
    have hpb := hp
    unfold P at hpb
    by_cases hpl : p≤2*q
    · rcases hk with rfl | rfl
      · apply generated_congr q (generated_join q (generated_join q (generated_l14 q p hq hp hpl)
          (generated_e14 q hq)) (generated_k114 q hq))
        intro e
        simp only [LRow,LNormal,NF234.eval,T234,E14,K1Row,I,beta]
        repeat first | (simp_all <;> omega) | split
      · apply generated_congr q (generated_join q (generated_join q (generated_l14 q p hq hp hpl)
          (generated_e14 q hq)) (generated_k214 q hq))
        intro e
        simp only [LRow,LNormal,NF234.eval,T234,E14,KPrime14,I,beta]
        repeat first | (simp_all <;> omega) | split
    · have hpe : p=2*q+1 := by omega
      subst p
      rcases hk with rfl | rfl
      · apply generated_congr q (generated_join q (generated_join q (generated_c14 q hq)
          (generated_e14 q hq)) (generated_k114 q hq))
        intro e
        simp only [CPrime,NF234.eval,T234,E14,K1Row,I]
        omega
      · apply generated_congr q (generated_join q (generated_join q (generated_c14 q hq)
          (generated_e14 q hq)) (generated_k214 q hq))
        intro e
        simp only [CPrime,NF234.eval,T234,E14,KPrime14,I]
        omega
  | dg p =>
    have hp : P q p := hw.1
    have hpl : p≤2*q := by have := hw.2; omega
    apply generated_congr q (generated_join q (generated_join q (generated_l14 q p hq hp hpl)
      (generated_d14 q hq)) (generated_e14 q hq))
    intro e
    have hpb := hp
    unfold P at hpb
    simp only [LRow,LNormal,NF234.eval,T234,DPrime14,E14,I,beta]
    repeat first | (simp_all <;> omega) | split
  | km k =>
    have hk : k=0 := hcut
    subst k
    have hp : P q (q+3) := by unfold P; omega
    apply generated_congr q (generated_join q (generated_l14 q (q+3) hq hp (by omega))
      (generated_k114 q hq))
    intro e
    simp only [LRow,LNormal,NF234.eval,T234,K1Row,I,beta]
    repeat first | (simp_all <;> omega) | split
  | ck k =>
    have hk : k=1 := hcut
    subst k
    apply generated_congr q (generated_join q (generated_c14 q hq) (generated_k114 q hq))
    intro e
    simp only [CPrime,NF234.eval,T234,K1Row,I]
    omega
  | last => exact False.elim hcut

theorem core14_exhaustive (q : Nat) (hq : 4≤q) (R : Nat → Prop) :
    Generated q R ∧ Core234 R ↔ ∃ w : NF234,w.Valid q ∧ Cut14 w ∧ ∀ e,R e ↔ w.eval q e := by
  constructor
  · rintro ⟨hg,hc⟩
    obtain ⟨w,hw,he⟩ := (core234_closure_exact q hq R).mp ⟨core14_original q hq R hg hc,hc⟩
    refine ⟨w,hw,?_,he⟩
    have hh := core14_horns q hq R hg hc
    have hh0 := (he (4*q-1)).mp hh.1
    have hh1 : w.eval q (4*q) ∨ w.eval q (2*q+2) :=
      hh.2.1.elim (fun h => Or.inl ((he _).mp h)) (fun h => Or.inr ((he _).mp h))
    cases w <;> simp_all [NF234.Valid,NF234.eval,Cut14,T234,I] <;> omega
  · rintro ⟨w,hw,hcut,he⟩
    refine ⟨generated_congr q (normal14_retained_generated q hq w hw hcut) (fun e => (he e).symm),?_⟩
    have hc := NF234.core q hq w hw
    unfold Core234 at *
    rw [he 1,he 2,he 3,he 4]
    exact hc

theorem core14_old (q : Nat) (hq : 4≤q) (R : Nat → Prop)
    (hg : Generated q R) (hc : Core234 R) : LuRazThreeRow.Generated q R :=
  LuRazThreeRow.old234_in_new q hq R (core14_original q hq R hg hc) hc

theorem core14_normal_unique (q : Nat) (hq : 4≤q) (a b : NF234)
    (ha : a.Valid q) (hb : b.Valid q) (he : ∀ e,a.eval q e ↔ b.eval q e) : a=b :=
  NF234.unique q hq a b ha hb he

end LuRazSixRowClosure
