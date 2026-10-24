import Exhaustive134Parts
namespace LuRazThreeRow
open LuRazClosure LuRazParametric
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000
set_option linter.unusedSimpArgs false

def Cut134 : NF134 → Prop
  | .ej a => a=5 | .aej _ | .extra _ => False | _ => True
def Valid134 (q : Nat) (z : NF134) : Prop := z.Valid q ∧ Cut134 z
inductive Fresh134 where | lp | lb | zz (b : Nat) | cz (b : Nat) deriving DecidableEq, Repr
def Fresh134.Valid (q : Nat) : Fresh134 → Prop
  | .lp | .lb => True
  | .zz b => 2*q+1≤b ∧ b≤4*q-3
  | .cz b => 2*q+2≤b ∧ b≤3*q-1
def Fresh134.eval (q : Nat) : Fresh134 → Nat → Prop
  | .lp => fun e => T134 e ∨ I 5 (2*q+1) e ∨ e=4*q
  | .lb => fun e => T134 e ∨ I 5 (2*q+1) e ∨ BRow q e
  | .zz b => fun e => T134 e ∨ I 5 b e ∨ I (4*q-1) (4*q) e
  | .cz b => fun e => T134 e ∨ I 5 b e ∨ e=3*q+1 ∨ I (4*q-1) (4*q) e
inductive Normal134 where | old (z : NF134) | fresh (z : Fresh134) deriving DecidableEq, Repr
def Normal134.Valid (q : Nat) : Normal134 → Prop
  | .old z => Valid134 q z | .fresh z => z.Valid q
def Normal134.eval (q : Nat) : Normal134 → Nat → Prop
  | .old z => z.eval q | .fresh z => z.eval q

def Raw134 (q b : Nat) (v d l z : Prop) (e : Nat) : Prop :=
  T134 e ∨ I 5 b e ∨ (v∧BRow q e) ∨ (d∧e=3*q+1) ∨ ((l∨z)∧e=4*q) ∨ (z∧e=4*q-1)

theorem mixed134_raw (q a b : Nat) (hq : 4≤q) (hab : JReachable q a b)
    (u v d l z : Prop) (hg : d∨l∨z) (e : Nat) :
    Mixed134V q a b u v d l z e ↔ Raw134 q b v d l z e := by
  have hab' := hab
  unfold JReachable at hab'
  by_cases hu : u <;> by_cases hv : v <;> by_cases hd : d <;> by_cases hl : l <;> by_cases hz : z
  all_goals simp_all [Mixed134V,Fixed134V,JRow,Raw134,T134,ARow,BRow,CRow,LPrime,ZPrime,I] <;> omega

theorem raw134_normal (q b : Nat) (hq : 4≤q) (hb0 : 2*q+2≤b ∧ b≤4*q-3)
    (v d l z : Prop) (hg : d∨l∨z) :
    ∃ w : Normal134, w.Valid q ∧ ∀ e, Raw134 q b v d l z e ↔ w.eval q e := by
  classical
  by_cases hv : v
  ·
    by_cases hd : d
    ·
      by_cases hl : l
      ·
        by_cases hz : z
        ·
          by_cases hb : b≤3*q-1
          ·
            refine ⟨.old (.cjb b),?_,?_⟩
            · simp [Normal134.Valid,Normal134.eval,Valid134,Cut134,Fresh134.Valid,Fresh134.eval,NF134.Valid,NF134.eval,T134,BRow,I] <;> omega
            · intro e
              simp_all [Raw134,Normal134.Valid,Normal134.eval,Valid134,Cut134,Fresh134.Valid,Fresh134.eval,NF134.Valid,NF134.eval,T134,BRow,I] <;> omega
          ·
            refine ⟨.old (.ej 5),?_,?_⟩
            · simp [Normal134.Valid,Normal134.eval,Valid134,Cut134,Fresh134.Valid,Fresh134.eval,NF134.Valid,NF134.eval,T134,BRow,I] <;> omega
            · intro e
              simp_all [Raw134,Normal134.Valid,Normal134.eval,Valid134,Cut134,Fresh134.Valid,Fresh134.eval,NF134.Valid,NF134.eval,T134,BRow,I] <;> omega
        ·
          by_cases hb : b≤3*q-1
          ·
            refine ⟨.old (.cjb b),?_,?_⟩
            · simp [Normal134.Valid,Normal134.eval,Valid134,Cut134,Fresh134.Valid,Fresh134.eval,NF134.Valid,NF134.eval,T134,BRow,I] <;> omega
            · intro e
              simp_all [Raw134,Normal134.Valid,Normal134.eval,Valid134,Cut134,Fresh134.Valid,Fresh134.eval,NF134.Valid,NF134.eval,T134,BRow,I] <;> omega
          ·
            refine ⟨.old (.ej 5),?_,?_⟩
            · simp [Normal134.Valid,Normal134.eval,Valid134,Cut134,Fresh134.Valid,Fresh134.eval,NF134.Valid,NF134.eval,T134,BRow,I] <;> omega
            · intro e
              simp_all [Raw134,Normal134.Valid,Normal134.eval,Valid134,Cut134,Fresh134.Valid,Fresh134.eval,NF134.Valid,NF134.eval,T134,BRow,I] <;> omega
      ·
        by_cases hz : z
        ·
          by_cases hb : b≤3*q-1
          ·
            refine ⟨.old (.cjb b),?_,?_⟩
            · simp [Normal134.Valid,Normal134.eval,Valid134,Cut134,Fresh134.Valid,Fresh134.eval,NF134.Valid,NF134.eval,T134,BRow,I] <;> omega
            · intro e
              simp_all [Raw134,Normal134.Valid,Normal134.eval,Valid134,Cut134,Fresh134.Valid,Fresh134.eval,NF134.Valid,NF134.eval,T134,BRow,I] <;> omega
          ·
            refine ⟨.old (.ej 5),?_,?_⟩
            · simp [Normal134.Valid,Normal134.eval,Valid134,Cut134,Fresh134.Valid,Fresh134.eval,NF134.Valid,NF134.eval,T134,BRow,I] <;> omega
            · intro e
              simp_all [Raw134,Normal134.Valid,Normal134.eval,Valid134,Cut134,Fresh134.Valid,Fresh134.eval,NF134.Valid,NF134.eval,T134,BRow,I] <;> omega
        ·
          by_cases hb : b≤3*q-1
          ·
            refine ⟨.old (.cjb b),?_,?_⟩
            · simp [Normal134.Valid,Normal134.eval,Valid134,Cut134,Fresh134.Valid,Fresh134.eval,NF134.Valid,NF134.eval,T134,BRow,I] <;> omega
            · intro e
              simp_all [Raw134,Normal134.Valid,Normal134.eval,Valid134,Cut134,Fresh134.Valid,Fresh134.eval,NF134.Valid,NF134.eval,T134,BRow,I] <;> omega
          ·
            refine ⟨.old (.ej 5),?_,?_⟩
            · simp [Normal134.Valid,Normal134.eval,Valid134,Cut134,Fresh134.Valid,Fresh134.eval,NF134.Valid,NF134.eval,T134,BRow,I] <;> omega
            · intro e
              simp_all [Raw134,Normal134.Valid,Normal134.eval,Valid134,Cut134,Fresh134.Valid,Fresh134.eval,NF134.Valid,NF134.eval,T134,BRow,I] <;> omega
    ·
      by_cases hl : l
      ·
        by_cases hz : z
        ·
          by_cases hb : b≤3*q
          ·
            refine ⟨.old (.zjb b),?_,?_⟩
            · simp [Normal134.Valid,Normal134.eval,Valid134,Cut134,Fresh134.Valid,Fresh134.eval,NF134.Valid,NF134.eval,T134,BRow,I] <;> omega
            · intro e
              simp_all [Raw134,Normal134.Valid,Normal134.eval,Valid134,Cut134,Fresh134.Valid,Fresh134.eval,NF134.Valid,NF134.eval,T134,BRow,I] <;> omega
          ·
            refine ⟨.old (.ej 5),?_,?_⟩
            · simp [Normal134.Valid,Normal134.eval,Valid134,Cut134,Fresh134.Valid,Fresh134.eval,NF134.Valid,NF134.eval,T134,BRow,I] <;> omega
            · intro e
              simp_all [Raw134,Normal134.Valid,Normal134.eval,Valid134,Cut134,Fresh134.Valid,Fresh134.eval,NF134.Valid,NF134.eval,T134,BRow,I] <;> omega
        ·
          by_cases hb : b≤3*q
          ·
            refine ⟨.old (.zjb b),?_,?_⟩
            · simp [Normal134.Valid,Normal134.eval,Valid134,Cut134,Fresh134.Valid,Fresh134.eval,NF134.Valid,NF134.eval,T134,BRow,I] <;> omega
            · intro e
              simp_all [Raw134,Normal134.Valid,Normal134.eval,Valid134,Cut134,Fresh134.Valid,Fresh134.eval,NF134.Valid,NF134.eval,T134,BRow,I] <;> omega
          ·
            refine ⟨.old (.ej 5),?_,?_⟩
            · simp [Normal134.Valid,Normal134.eval,Valid134,Cut134,Fresh134.Valid,Fresh134.eval,NF134.Valid,NF134.eval,T134,BRow,I] <;> omega
            · intro e
              simp_all [Raw134,Normal134.Valid,Normal134.eval,Valid134,Cut134,Fresh134.Valid,Fresh134.eval,NF134.Valid,NF134.eval,T134,BRow,I] <;> omega
      ·
        by_cases hz : z
        ·
          by_cases hb : b≤3*q
          ·
            refine ⟨.old (.zjb b),?_,?_⟩
            · simp [Normal134.Valid,Normal134.eval,Valid134,Cut134,Fresh134.Valid,Fresh134.eval,NF134.Valid,NF134.eval,T134,BRow,I] <;> omega
            · intro e
              simp_all [Raw134,Normal134.Valid,Normal134.eval,Valid134,Cut134,Fresh134.Valid,Fresh134.eval,NF134.Valid,NF134.eval,T134,BRow,I] <;> omega
          ·
            refine ⟨.old (.ej 5),?_,?_⟩
            · simp [Normal134.Valid,Normal134.eval,Valid134,Cut134,Fresh134.Valid,Fresh134.eval,NF134.Valid,NF134.eval,T134,BRow,I] <;> omega
            · intro e
              simp_all [Raw134,Normal134.Valid,Normal134.eval,Valid134,Cut134,Fresh134.Valid,Fresh134.eval,NF134.Valid,NF134.eval,T134,BRow,I] <;> omega
        ·
          exact False.elim (by simp_all)
  ·
    by_cases hd : d
    ·
      by_cases hl : l
      ·
        by_cases hz : z
        ·
          by_cases hb : b≤3*q-1
          ·
            refine ⟨.fresh (.cz b),?_,?_⟩
            · simp [Normal134.Valid,Normal134.eval,Valid134,Cut134,Fresh134.Valid,Fresh134.eval,NF134.Valid,NF134.eval,T134,BRow,I] <;> omega
            · intro e
              simp_all [Raw134,Normal134.Valid,Normal134.eval,Valid134,Cut134,Fresh134.Valid,Fresh134.eval,NF134.Valid,NF134.eval,T134,BRow,I] <;> omega
          ·
            refine ⟨.fresh (.zz (max b (3*q+1))),?_,?_⟩
            · simp [Normal134.Valid,Normal134.eval,Valid134,Cut134,Fresh134.Valid,Fresh134.eval,NF134.Valid,NF134.eval,T134,BRow,I] <;> omega
            · intro e
              simp_all [Raw134,Normal134.Valid,Normal134.eval,Valid134,Cut134,Fresh134.Valid,Fresh134.eval,NF134.Valid,NF134.eval,T134,BRow,I] <;> omega
        ·
          by_cases hb : b≤3*q-1
          ·
            refine ⟨.old (.czj b),?_,?_⟩
            · simp [Normal134.Valid,Normal134.eval,Valid134,Cut134,Fresh134.Valid,Fresh134.eval,NF134.Valid,NF134.eval,T134,BRow,I] <;> omega
            · intro e
              simp_all [Raw134,Normal134.Valid,Normal134.eval,Valid134,Cut134,Fresh134.Valid,Fresh134.eval,NF134.Valid,NF134.eval,T134,BRow,I] <;> omega
          ·
            refine ⟨.old (.zj (max b (3*q+1))),?_,?_⟩
            · simp [Normal134.Valid,Normal134.eval,Valid134,Cut134,Fresh134.Valid,Fresh134.eval,NF134.Valid,NF134.eval,T134,BRow,I] <;> omega
            · intro e
              simp_all [Raw134,Normal134.Valid,Normal134.eval,Valid134,Cut134,Fresh134.Valid,Fresh134.eval,NF134.Valid,NF134.eval,T134,BRow,I] <;> omega
      ·
        by_cases hz : z
        ·
          by_cases hb : b≤3*q-1
          ·
            refine ⟨.fresh (.cz b),?_,?_⟩
            · simp [Normal134.Valid,Normal134.eval,Valid134,Cut134,Fresh134.Valid,Fresh134.eval,NF134.Valid,NF134.eval,T134,BRow,I] <;> omega
            · intro e
              simp_all [Raw134,Normal134.Valid,Normal134.eval,Valid134,Cut134,Fresh134.Valid,Fresh134.eval,NF134.Valid,NF134.eval,T134,BRow,I] <;> omega
          ·
            refine ⟨.fresh (.zz (max b (3*q+1))),?_,?_⟩
            · simp [Normal134.Valid,Normal134.eval,Valid134,Cut134,Fresh134.Valid,Fresh134.eval,NF134.Valid,NF134.eval,T134,BRow,I] <;> omega
            · intro e
              simp_all [Raw134,Normal134.Valid,Normal134.eval,Valid134,Cut134,Fresh134.Valid,Fresh134.eval,NF134.Valid,NF134.eval,T134,BRow,I] <;> omega
        ·
          by_cases hb : b=3*q
          ·
            refine ⟨.old (.cj (3*q+1)),?_,?_⟩
            · simp [Normal134.Valid,Normal134.eval,Valid134,Cut134,Fresh134.Valid,Fresh134.eval,NF134.Valid,NF134.eval,T134,BRow,I] <;> omega
            · intro e
              simp_all [Raw134,Normal134.Valid,Normal134.eval,Valid134,Cut134,Fresh134.Valid,Fresh134.eval,NF134.Valid,NF134.eval,T134,BRow,I] <;> omega
          ·
            refine ⟨.old (.cj b),?_,?_⟩
            · simp [Normal134.Valid,Normal134.eval,Valid134,Cut134,Fresh134.Valid,Fresh134.eval,NF134.Valid,NF134.eval,T134,BRow,I] <;> omega
            · intro e
              simp_all [Raw134,Normal134.Valid,Normal134.eval,Valid134,Cut134,Fresh134.Valid,Fresh134.eval,NF134.Valid,NF134.eval,T134,BRow,I] <;> omega
    ·
      by_cases hl : l
      ·
        by_cases hz : z
        ·
          refine ⟨.fresh (.zz b),?_,?_⟩
          · simp [Normal134.Valid,Normal134.eval,Valid134,Cut134,Fresh134.Valid,Fresh134.eval,NF134.Valid,NF134.eval,T134,BRow,I] <;> omega
          · intro e
            simp_all [Raw134,Normal134.Valid,Normal134.eval,Valid134,Cut134,Fresh134.Valid,Fresh134.eval,NF134.Valid,NF134.eval,T134,BRow,I] <;> omega
        ·
          refine ⟨.old (.zj b),?_,?_⟩
          · simp [Normal134.Valid,Normal134.eval,Valid134,Cut134,Fresh134.Valid,Fresh134.eval,NF134.Valid,NF134.eval,T134,BRow,I] <;> omega
          · intro e
            simp_all [Raw134,Normal134.Valid,Normal134.eval,Valid134,Cut134,Fresh134.Valid,Fresh134.eval,NF134.Valid,NF134.eval,T134,BRow,I] <;> omega
      ·
        by_cases hz : z
        ·
          refine ⟨.fresh (.zz b),?_,?_⟩
          · simp [Normal134.Valid,Normal134.eval,Valid134,Cut134,Fresh134.Valid,Fresh134.eval,NF134.Valid,NF134.eval,T134,BRow,I] <;> omega
          · intro e
            simp_all [Raw134,Normal134.Valid,Normal134.eval,Valid134,Cut134,Fresh134.Valid,Fresh134.eval,NF134.Valid,NF134.eval,T134,BRow,I] <;> omega
        ·
          exact False.elim (by simp_all)

theorem fixed134_v_normal (q : Nat) (hq : 4≤q) (u v d z : Prop) (hg : u∨z) :
    ∃ w : Normal134, w.Valid q ∧ ∀ e, Fixed134V q u v d True z e ↔ w.eval q e := by
  classical
  by_cases hu : u
  ·
    by_cases hv : v
    ·
      by_cases hd : d
      ·
        by_cases hz : z
        ·
          refine ⟨.old (.cjb (2*q+2)),?_,?_⟩
          · simp [Normal134.Valid,Normal134.eval,Valid134,Cut134,Fresh134.Valid,Fresh134.eval,NF134.Valid,NF134.eval,T134,BRow,I] <;> omega
          · intro e
            simp_all [Fixed134V,ARow,CRow,LPrime,ZPrime,Normal134.Valid,Normal134.eval,Valid134,Cut134,Fresh134.Valid,Fresh134.eval,NF134.Valid,NF134.eval,T134,BRow,I] <;> omega
        ·
          refine ⟨.old (.cjb (2*q+2)),?_,?_⟩
          · simp [Normal134.Valid,Normal134.eval,Valid134,Cut134,Fresh134.Valid,Fresh134.eval,NF134.Valid,NF134.eval,T134,BRow,I] <;> omega
          · intro e
            simp_all [Fixed134V,ARow,CRow,LPrime,ZPrime,Normal134.Valid,Normal134.eval,Valid134,Cut134,Fresh134.Valid,Fresh134.eval,NF134.Valid,NF134.eval,T134,BRow,I] <;> omega
      ·
        by_cases hz : z
        ·
          refine ⟨.fresh .lb,?_,?_⟩
          · simp [Normal134.Valid,Normal134.eval,Valid134,Cut134,Fresh134.Valid,Fresh134.eval,NF134.Valid,NF134.eval,T134,BRow,I] <;> omega
          · intro e
            simp_all [Fixed134V,ARow,CRow,LPrime,ZPrime,Normal134.Valid,Normal134.eval,Valid134,Cut134,Fresh134.Valid,Fresh134.eval,NF134.Valid,NF134.eval,T134,BRow,I] <;> omega
        ·
          refine ⟨.fresh .lb,?_,?_⟩
          · simp [Normal134.Valid,Normal134.eval,Valid134,Cut134,Fresh134.Valid,Fresh134.eval,NF134.Valid,NF134.eval,T134,BRow,I] <;> omega
          · intro e
            simp_all [Fixed134V,ARow,CRow,LPrime,ZPrime,Normal134.Valid,Normal134.eval,Valid134,Cut134,Fresh134.Valid,Fresh134.eval,NF134.Valid,NF134.eval,T134,BRow,I] <;> omega
    ·
      by_cases hd : d
      ·
        by_cases hz : z
        ·
          refine ⟨.fresh (.cz (2*q+2)),?_,?_⟩
          · simp [Normal134.Valid,Normal134.eval,Valid134,Cut134,Fresh134.Valid,Fresh134.eval,NF134.Valid,NF134.eval,T134,BRow,I] <;> omega
          · intro e
            simp_all [Fixed134V,ARow,CRow,LPrime,ZPrime,Normal134.Valid,Normal134.eval,Valid134,Cut134,Fresh134.Valid,Fresh134.eval,NF134.Valid,NF134.eval,T134,BRow,I] <;> omega
        ·
          refine ⟨.old (.czj (2*q+2)),?_,?_⟩
          · simp [Normal134.Valid,Normal134.eval,Valid134,Cut134,Fresh134.Valid,Fresh134.eval,NF134.Valid,NF134.eval,T134,BRow,I] <;> omega
          · intro e
            simp_all [Fixed134V,ARow,CRow,LPrime,ZPrime,Normal134.Valid,Normal134.eval,Valid134,Cut134,Fresh134.Valid,Fresh134.eval,NF134.Valid,NF134.eval,T134,BRow,I] <;> omega
      ·
        by_cases hz : z
        ·
          refine ⟨.fresh (.zz (2*q+1)),?_,?_⟩
          · simp [Normal134.Valid,Normal134.eval,Valid134,Cut134,Fresh134.Valid,Fresh134.eval,NF134.Valid,NF134.eval,T134,BRow,I] <;> omega
          · intro e
            simp_all [Fixed134V,ARow,CRow,LPrime,ZPrime,Normal134.Valid,Normal134.eval,Valid134,Cut134,Fresh134.Valid,Fresh134.eval,NF134.Valid,NF134.eval,T134,BRow,I] <;> omega
        ·
          refine ⟨.fresh .lp,?_,?_⟩
          · simp [Normal134.Valid,Normal134.eval,Valid134,Cut134,Fresh134.Valid,Fresh134.eval,NF134.Valid,NF134.eval,T134,BRow,I] <;> omega
          · intro e
            simp_all [Fixed134V,ARow,CRow,LPrime,ZPrime,Normal134.Valid,Normal134.eval,Valid134,Cut134,Fresh134.Valid,Fresh134.eval,NF134.Valid,NF134.eval,T134,BRow,I] <;> omega
  ·
    by_cases hv : v
    ·
      by_cases hd : d
      ·
        by_cases hz : z
        ·
          refine ⟨.old (.cjb (2*q+2)),?_,?_⟩
          · simp [Normal134.Valid,Normal134.eval,Valid134,Cut134,Fresh134.Valid,Fresh134.eval,NF134.Valid,NF134.eval,T134,BRow,I] <;> omega
          · intro e
            simp_all [Fixed134V,ARow,CRow,LPrime,ZPrime,Normal134.Valid,Normal134.eval,Valid134,Cut134,Fresh134.Valid,Fresh134.eval,NF134.Valid,NF134.eval,T134,BRow,I] <;> omega
        ·
          exact False.elim (by simp_all)
      ·
        by_cases hz : z
        ·
          refine ⟨.fresh .lb,?_,?_⟩
          · simp [Normal134.Valid,Normal134.eval,Valid134,Cut134,Fresh134.Valid,Fresh134.eval,NF134.Valid,NF134.eval,T134,BRow,I] <;> omega
          · intro e
            simp_all [Fixed134V,ARow,CRow,LPrime,ZPrime,Normal134.Valid,Normal134.eval,Valid134,Cut134,Fresh134.Valid,Fresh134.eval,NF134.Valid,NF134.eval,T134,BRow,I] <;> omega
        ·
          exact False.elim (by simp_all)
    ·
      by_cases hd : d
      ·
        by_cases hz : z
        ·
          refine ⟨.fresh (.cz (2*q+2)),?_,?_⟩
          · simp [Normal134.Valid,Normal134.eval,Valid134,Cut134,Fresh134.Valid,Fresh134.eval,NF134.Valid,NF134.eval,T134,BRow,I] <;> omega
          · intro e
            simp_all [Fixed134V,ARow,CRow,LPrime,ZPrime,Normal134.Valid,Normal134.eval,Valid134,Cut134,Fresh134.Valid,Fresh134.eval,NF134.Valid,NF134.eval,T134,BRow,I] <;> omega
        ·
          exact False.elim (by simp_all)
      ·
        by_cases hz : z
        ·
          refine ⟨.fresh (.zz (2*q+1)),?_,?_⟩
          · simp [Normal134.Valid,Normal134.eval,Valid134,Cut134,Fresh134.Valid,Fresh134.eval,NF134.Valid,NF134.eval,T134,BRow,I] <;> omega
          · intro e
            simp_all [Fixed134V,ARow,CRow,LPrime,ZPrime,Normal134.Valid,Normal134.eval,Valid134,Cut134,Fresh134.Valid,Fresh134.eval,NF134.Valid,NF134.eval,T134,BRow,I] <;> omega
        ·
          exact False.elim (by simp_all)

theorem core134_normal (q : Nat) (hq : 4≤q) (R : Nat → Prop)
    (hg : Generated q R) (hc : Core134 R) :
    ∃ z : Normal134, z.Valid q ∧ ∀ e, R e ↔ z.eval q e := by
  rcases core134_v_parts q hq R hg hc with ⟨u,v,d,z,hA,he⟩ | ⟨a,b,hab,u,v,d,l,z,hG,he⟩
  · obtain ⟨w,hw,hwe⟩ := fixed134_v_normal q hq u v d z hA
    exact ⟨w,hw,fun e => (he e).trans (hwe e)⟩
  · have hb : 2*q+2≤b ∧ b≤4*q-3 := ⟨hab.2.2.1,hab.2.2.2.1⟩
    obtain ⟨w,hw,hwe⟩ := raw134_normal q b hq hb v d l z hG
    exact ⟨w,hw,fun e => (he e).trans ((mixed134_raw q a b hq hab u v d l z hG e).trans (hwe e))⟩

end LuRazThreeRow
