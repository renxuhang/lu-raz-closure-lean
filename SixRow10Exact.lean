import SixRow10Parts
namespace LuRazSixRowClosure.Low
open LuRazClosure
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
inductive NF10 where
  | k1
  | k2
  | joinK
  | fill1
  | fill2
  | dSmall
  | dBig
  deriving DecidableEq, Repr

def NF10.eval (q : Nat) : NF10 → Nat → Prop
  | .k1 => fun e => K1 q e
  | .k2 => fun e => K2 q e
  | .joinK => fun e => K1 q e ∨ K2 q e
  | .fill1 => fun e => K1 q e ∨ BRow q e
  | .fill2 => fun e => K2 q e ∨ BRow q e
  | .dSmall => fun e => K0 q e
  | .dBig => fun e => K0 q e ∨ BRow q e

theorem mix10_normal (q : Nat) (hq : 4≤q) (u v d b : Prop) (hg : u ∨ v ∨ d) :
    ∃x : NF10,∀e,Mix24 q u v d b e ↔ x.eval q e := by
  classical
  by_cases hu : u
  ·
    by_cases hv : v
    ·
      by_cases hd : d
      ·
        by_cases hb : b
        ·
          refine ⟨.dBig,?_⟩
          intro e
          simp only [Mix24,NF10.eval,hu,hv,hd,hb,true_and,false_and,false_or,or_false]
          all_goals (simp only [K0,K1,K2,BRow,I] <;> omega)
        ·
          refine ⟨.dSmall,?_⟩
          intro e
          simp only [Mix24,NF10.eval,hu,hv,hd,hb,true_and,false_and,false_or,or_false]
          all_goals (simp only [K0,K1,K2,BRow,I] <;> omega)
      ·
        by_cases hb : b
        ·
          refine ⟨.fill1,?_⟩
          intro e
          simp only [Mix24,NF10.eval,hu,hv,hd,hb,true_and,false_and,false_or,or_false]
          all_goals (simp only [K0,K1,K2,BRow,I] <;> omega)
        ·
          refine ⟨.joinK,?_⟩
          intro e
          simp only [Mix24,NF10.eval,hu,hv,hd,hb,true_and,false_and,false_or,or_false]
          all_goals (simp only [K0,K1,K2,BRow,I] <;> omega)
    ·
      by_cases hd : d
      ·
        by_cases hb : b
        ·
          refine ⟨.dBig,?_⟩
          intro e
          simp only [Mix24,NF10.eval,hu,hv,hd,hb,true_and,false_and,false_or,or_false]
          all_goals (simp only [K0,K1,K2,BRow,I] <;> omega)
        ·
          refine ⟨.dSmall,?_⟩
          intro e
          simp only [Mix24,NF10.eval,hu,hv,hd,hb,true_and,false_and,false_or,or_false]
          all_goals (simp only [K0,K1,K2,BRow,I] <;> omega)
      ·
        by_cases hb : b
        ·
          refine ⟨.fill1,?_⟩
          intro e
          simp only [Mix24,NF10.eval,hu,hv,hd,hb,true_and,false_and,false_or,or_false]
          all_goals (simp only [K0,K1,K2,BRow,I] <;> omega)
        ·
          refine ⟨.k1,?_⟩
          intro e
          simp only [Mix24,NF10.eval,hu,hv,hd,hb,true_and,false_and,false_or,or_false]
          all_goals (simp only [K0,K1,K2,BRow,I] <;> omega)
  ·
    by_cases hv : v
    ·
      by_cases hd : d
      ·
        by_cases hb : b
        ·
          refine ⟨.dBig,?_⟩
          intro e
          simp only [Mix24,NF10.eval,hu,hv,hd,hb,true_and,false_and,false_or,or_false]
          all_goals (simp only [K0,K1,K2,BRow,I] <;> omega)
        ·
          refine ⟨.dSmall,?_⟩
          intro e
          simp only [Mix24,NF10.eval,hu,hv,hd,hb,true_and,false_and,false_or,or_false]
          all_goals (simp only [K0,K1,K2,BRow,I] <;> omega)
      ·
        by_cases hb : b
        ·
          refine ⟨.fill2,?_⟩
          intro e
          simp only [Mix24,NF10.eval,hu,hv,hd,hb,true_and,false_and,false_or,or_false]
          all_goals (simp only [K0,K1,K2,BRow,I] <;> omega)
        ·
          refine ⟨.k2,?_⟩
          intro e
          simp only [Mix24,NF10.eval,hu,hv,hd,hb,true_and,false_and,false_or,or_false]
          all_goals (simp only [K0,K1,K2,BRow,I] <;> omega)
    ·
      by_cases hd : d
      ·
        by_cases hb : b
        ·
          refine ⟨.dBig,?_⟩
          intro e
          simp only [Mix24,NF10.eval,hu,hv,hd,hb,true_and,false_and,false_or,or_false]
          all_goals (simp only [K0,K1,K2,BRow,I] <;> omega)
        ·
          refine ⟨.dSmall,?_⟩
          intro e
          simp only [Mix24,NF10.eval,hu,hv,hd,hb,true_and,false_and,false_or,or_false]
          all_goals (simp only [K0,K1,K2,BRow,I] <;> omega)
      ·
        by_cases hb : b
        ·
          exact False.elim (by simp_all)
        ·
          exact False.elim (by simp_all)

theorem NF10.generated (q : Nat) (hq : 4≤q) (x : NF10) : Generated q (x.eval q) := by
  have gu : Generated q (K1 q) := generated_congr q (generated_row q (2*q+1) (by omega)) (fun e=>k1_source q e hq)
  have gv : Generated q (K2 q) := generated_congr q (generated_row q (2*q+2) (by omega)) (fun e=>k2_source q e hq)
  have gd : Generated q (K0 q) := generated_congr q (generated_row q 1 (by omega)) (fun e=>k0_source q e hq)
  have gb : Generated q (BRow q) := generated_b0 q hq
  cases x with
  | k1 => exact gu
  | k2 => exact gv
  | joinK => exact (generated_join q gu gv)
  | fill1 => exact (generated_join q gu gb)
  | fill2 => exact (generated_join q gv gb)
  | dSmall => exact gd
  | dBig => exact (generated_join q gd gb)

theorem NF10.core (q : Nat) (hq : 4≤q) (x : NF10) : Core24 (x.eval q) := by
  cases x <;> simp [NF10.eval,K0,K1,K2,BRow,Core24,I] <;> omega

theorem NF10.unique (q : Nat) (hq : 4≤q) (x y : NF10)
    (he : ∀e,x.eval q e ↔ y.eval q e) : x=y := by
  cases x with
  | k1 =>
    cases y with
    | k1 =>
      rfl
    | k2 =>
      have h := he (2*q+2)
      exfalso
      simp only [NF10.eval,K0,K1,K2,BRow,I] at h
      simp_all <;> omega
    | joinK =>
      have h := he (4*q)
      exfalso
      simp only [NF10.eval,K0,K1,K2,BRow,I] at h
      simp_all <;> omega
    | fill1 =>
      have h := he (4*q-1)
      exfalso
      simp only [NF10.eval,K0,K1,K2,BRow,I] at h
      simp_all <;> omega
    | fill2 =>
      have h := he (2*q+2)
      exfalso
      simp only [NF10.eval,K0,K1,K2,BRow,I] at h
      simp_all <;> omega
    | dSmall =>
      have h := he (2*q+1)
      exfalso
      simp only [NF10.eval,K0,K1,K2,BRow,I] at h
      simp_all <;> omega
    | dBig =>
      have h := he (2*q+1)
      exfalso
      simp only [NF10.eval,K0,K1,K2,BRow,I] at h
      simp_all <;> omega
  | k2 =>
    cases y with
    | k1 =>
      have h := he (2*q+2)
      exfalso
      simp only [NF10.eval,K0,K1,K2,BRow,I] at h
      simp_all <;> omega
    | k2 =>
      rfl
    | joinK =>
      have h := he (2*q+2)
      exfalso
      simp only [NF10.eval,K0,K1,K2,BRow,I] at h
      simp_all <;> omega
    | fill1 =>
      have h := he (2*q+2)
      exfalso
      simp only [NF10.eval,K0,K1,K2,BRow,I] at h
      simp_all <;> omega
    | fill2 =>
      have h := he (4*q-1)
      exfalso
      simp only [NF10.eval,K0,K1,K2,BRow,I] at h
      simp_all <;> omega
    | dSmall =>
      have h := he (2*q+1)
      exfalso
      simp only [NF10.eval,K0,K1,K2,BRow,I] at h
      simp_all <;> omega
    | dBig =>
      have h := he (2*q+1)
      exfalso
      simp only [NF10.eval,K0,K1,K2,BRow,I] at h
      simp_all <;> omega
  | joinK =>
    cases y with
    | k1 =>
      have h := he (4*q)
      exfalso
      simp only [NF10.eval,K0,K1,K2,BRow,I] at h
      simp_all <;> omega
    | k2 =>
      have h := he (2*q+2)
      exfalso
      simp only [NF10.eval,K0,K1,K2,BRow,I] at h
      simp_all <;> omega
    | joinK =>
      rfl
    | fill1 =>
      have h := he (4*q-1)
      exfalso
      simp only [NF10.eval,K0,K1,K2,BRow,I] at h
      simp_all <;> omega
    | fill2 =>
      have h := he (2*q+2)
      exfalso
      simp only [NF10.eval,K0,K1,K2,BRow,I] at h
      simp_all <;> omega
    | dSmall =>
      have h := he (2*q+1)
      exfalso
      simp only [NF10.eval,K0,K1,K2,BRow,I] at h
      simp_all <;> omega
    | dBig =>
      have h := he (2*q+1)
      exfalso
      simp only [NF10.eval,K0,K1,K2,BRow,I] at h
      simp_all <;> omega
  | fill1 =>
    cases y with
    | k1 =>
      have h := he (4*q-1)
      exfalso
      simp only [NF10.eval,K0,K1,K2,BRow,I] at h
      simp_all <;> omega
    | k2 =>
      have h := he (2*q+2)
      exfalso
      simp only [NF10.eval,K0,K1,K2,BRow,I] at h
      simp_all <;> omega
    | joinK =>
      have h := he (4*q-1)
      exfalso
      simp only [NF10.eval,K0,K1,K2,BRow,I] at h
      simp_all <;> omega
    | fill1 =>
      rfl
    | fill2 =>
      have h := he (2*q+2)
      exfalso
      simp only [NF10.eval,K0,K1,K2,BRow,I] at h
      simp_all <;> omega
    | dSmall =>
      have h := he (2*q+1)
      exfalso
      simp only [NF10.eval,K0,K1,K2,BRow,I] at h
      simp_all <;> omega
    | dBig =>
      have h := he (2*q+1)
      exfalso
      simp only [NF10.eval,K0,K1,K2,BRow,I] at h
      simp_all <;> omega
  | fill2 =>
    cases y with
    | k1 =>
      have h := he (2*q+2)
      exfalso
      simp only [NF10.eval,K0,K1,K2,BRow,I] at h
      simp_all <;> omega
    | k2 =>
      have h := he (4*q-1)
      exfalso
      simp only [NF10.eval,K0,K1,K2,BRow,I] at h
      simp_all <;> omega
    | joinK =>
      have h := he (2*q+2)
      exfalso
      simp only [NF10.eval,K0,K1,K2,BRow,I] at h
      simp_all <;> omega
    | fill1 =>
      have h := he (2*q+2)
      exfalso
      simp only [NF10.eval,K0,K1,K2,BRow,I] at h
      simp_all <;> omega
    | fill2 =>
      rfl
    | dSmall =>
      have h := he (2*q+1)
      exfalso
      simp only [NF10.eval,K0,K1,K2,BRow,I] at h
      simp_all <;> omega
    | dBig =>
      have h := he (2*q+1)
      exfalso
      simp only [NF10.eval,K0,K1,K2,BRow,I] at h
      simp_all <;> omega
  | dSmall =>
    cases y with
    | k1 =>
      have h := he (2*q+1)
      exfalso
      simp only [NF10.eval,K0,K1,K2,BRow,I] at h
      simp_all <;> omega
    | k2 =>
      have h := he (2*q+1)
      exfalso
      simp only [NF10.eval,K0,K1,K2,BRow,I] at h
      simp_all <;> omega
    | joinK =>
      have h := he (2*q+1)
      exfalso
      simp only [NF10.eval,K0,K1,K2,BRow,I] at h
      simp_all <;> omega
    | fill1 =>
      have h := he (2*q+1)
      exfalso
      simp only [NF10.eval,K0,K1,K2,BRow,I] at h
      simp_all <;> omega
    | fill2 =>
      have h := he (2*q+1)
      exfalso
      simp only [NF10.eval,K0,K1,K2,BRow,I] at h
      simp_all <;> omega
    | dSmall =>
      rfl
    | dBig =>
      have h := he (4*q-1)
      exfalso
      simp only [NF10.eval,K0,K1,K2,BRow,I] at h
      simp_all <;> omega
  | dBig =>
    cases y with
    | k1 =>
      have h := he (2*q+1)
      exfalso
      simp only [NF10.eval,K0,K1,K2,BRow,I] at h
      simp_all <;> omega
    | k2 =>
      have h := he (2*q+1)
      exfalso
      simp only [NF10.eval,K0,K1,K2,BRow,I] at h
      simp_all <;> omega
    | joinK =>
      have h := he (2*q+1)
      exfalso
      simp only [NF10.eval,K0,K1,K2,BRow,I] at h
      simp_all <;> omega
    | fill1 =>
      have h := he (2*q+1)
      exfalso
      simp only [NF10.eval,K0,K1,K2,BRow,I] at h
      simp_all <;> omega
    | fill2 =>
      have h := he (2*q+1)
      exfalso
      simp only [NF10.eval,K0,K1,K2,BRow,I] at h
      simp_all <;> omega
    | dSmall =>
      have h := he (4*q-1)
      exfalso
      simp only [NF10.eval,K0,K1,K2,BRow,I] at h
      simp_all <;> omega
    | dBig =>
      rfl

theorem core10_exhaustive (q : Nat) (hq : 4≤q) (R : Nat→Prop) :
    Generated q R ∧ Core24 R ↔ ∃x : NF10,∀e,R e ↔ x.eval q e := by
  constructor
  · rintro ⟨hg,hc⟩
    obtain ⟨u,v,d,b,hguard,he⟩ := core24_mix q hq R hg hc
    obtain ⟨x,hx⟩ := mix10_normal q hq u v d b hguard
    exact ⟨x,fun e=>(he e).trans (hx e)⟩
  · rintro ⟨x,he⟩
    have hc := x.core q hq
    exact ⟨generated_congr q (x.generated q hq) (fun e=>(he e).symm),
      by
        unfold Core24 at *
        rw [he 1,he 2,he 3,he 4]
        exact hc⟩

end LuRazSixRowClosure.Low
