import SixRowCore11Parts
import SixRowCore13Normal
namespace LuRazSixRowClosure
open LuRazClosure LuRazParametric LuRazEnumeration
set_option maxRecDepth 32768
set_option maxHeartbeats 18000000
set_option linter.unusedSimpArgs false

def Tail11 (q a k e : Nat) : Prop :=
  I a (4*q-2) e ∨ (k=1 ∧ e=4*q) ∨ (k=2 ∧ I (4*q-1) (4*q) e)

def Head11 (q a k e : Nat) : Prop := e=1 ∨ e=2 ∨ e=4 ∨ Tail11 q a k e

def FixedPick11 (q : Nat) : Nat → Nat → Prop
  | 0 => K1Row q
  | 1 => KPrime14 q
  | 2 => fun e => K1Row q e ∨ KPrime14 q e
  | 3 => fun e => K1Row q e ∨ LuRazClosure.BRow q e
  | 4 => fun e => KPrime14 q e ∨ LuRazClosure.BRow q e
  | _ => fun _ => False

inductive NF11 where
  | interval (a k : Nat) | agap (a k : Nat) | ak (k : Nat)
  deriving DecidableEq, Repr

def NF11.Valid (q : Nat) : NF11 → Prop
  | .interval a k => (5≤a ∧ a≤2*q+1) ∧ k<3
  | .agap a k => (q+4≤a ∧ a≤2*q+1) ∧ k<3
  | .ak k => k<5

def NF11.eval (q : Nat) : NF11 → Nat → Prop
  | .interval a k => Head11 q a k
  | .agap a k => fun e => Head11 q a k e ∨ ARow q e
  | .ak k => fun e => ARow q e ∨ FixedPick11 q k e

theorem mixed11_right (q a b : Nat) (hq : 4≤q) (hab : JReachable q a b)
    (u v d k1 k2 : Prop) (hg : d∨k1∨k2) :
    ∃ k,k<3 ∧ ∀ e,Mixed11 q a b u v d k1 k2 e ↔ Head11 q a k e ∨ (u∧ARow q e) := by
  classical
  unfold JReachable at hab
  by_cases hv : v
  · refine ⟨2,by decide,?_⟩
    intro e
    by_cases hu : u <;> by_cases hd : d <;> by_cases hk1 : k1 <;> by_cases hk2 : k2 <;>
      simp_all [Mixed11,Fixed11,Head11,Tail11,JRow,DPrime14,K1Row,KPrime14,LuRazClosure.BRow,ARow,I] <;> omega
  · by_cases hd : d
    · refine ⟨1,by decide,?_⟩
      intro e
      by_cases hu : u <;> by_cases hk1 : k1 <;> by_cases hk2 : k2 <;>
        simp_all [Mixed11,Fixed11,Head11,Tail11,JRow,DPrime14,K1Row,KPrime14,LuRazClosure.BRow,ARow,I] <;> omega
    · by_cases hk2 : k2
      · refine ⟨1,by decide,?_⟩
        intro e
        by_cases hu : u <;> by_cases hk1 : k1 <;>
          simp_all [Mixed11,Fixed11,Head11,Tail11,JRow,DPrime14,K1Row,KPrime14,LuRazClosure.BRow,ARow,I] <;> omega
      · have hk1 : k1 := by simp_all
        refine ⟨0,by decide,?_⟩
        intro e
        by_cases hu : u <;>
          simp_all [Mixed11,Fixed11,Head11,Tail11,JRow,DPrime14,K1Row,KPrime14,LuRazClosure.BRow,ARow,I] <;> omega

theorem head11_left_normal (q a k : Nat) (hq : 4≤q) (ha : 5≤a ∧ a≤2*q+1) (hk : k<3) (u : Prop) :
    ∃ w : NF11,w.Valid q ∧ ∀ e,(Head11 q a k e ∨ (u∧ARow q e)) ↔ w.eval q e := by
  classical
  by_cases hu : u
  · by_cases hal : a≤q+3
    · refine ⟨.interval 5 k,⟨by omega,hk⟩,?_⟩
      intro e
      simp only [Head11,Tail11,NF11.eval,hu,true_and,ARow,I]
      omega
    · exact ⟨.agap a k,⟨by omega,hk⟩,by intro e; simp only [NF11.eval,hu,true_and]⟩
  · exact ⟨.interval a k,⟨ha,hk⟩,by intro e; simp only [NF11.eval,hu,false_and,or_false]⟩

theorem fixed11_normal (q : Nat) (hq : 4≤q) (v d k1 k2 : Prop) (hg : d∨k1∨k2) :
    ∃ w : NF11,w.Valid q ∧ ∀ e,Fixed11 q True v d k1 k2 e ↔ w.eval q e := by
  classical
  by_cases hd : d
  · by_cases hv : v
    · refine ⟨.agap (2*q+1) 2,by simp [NF11.Valid]; omega,?_⟩
      intro e
      by_cases hk1 : k1 <;> by_cases hk2 : k2 <;>
        simp_all [Fixed11,NF11.eval,Head11,Tail11,ARow,LuRazClosure.BRow,DPrime14,K1Row,KPrime14,I] <;> omega
    · refine ⟨.agap (2*q+1) 1,by simp [NF11.Valid]; omega,?_⟩
      intro e
      by_cases hk1 : k1 <;> by_cases hk2 : k2 <;>
        simp_all [Fixed11,NF11.eval,Head11,Tail11,ARow,LuRazClosure.BRow,DPrime14,K1Row,KPrime14,I] <;> omega
  · by_cases hv : v
    · by_cases hk1 : k1
      · refine ⟨.ak 3,by simp [NF11.Valid],?_⟩
        intro e
        by_cases hk2 : k2 <;>
          simp_all [Fixed11,NF11.eval,FixedPick11,ARow,LuRazClosure.BRow,DPrime14,K1Row,KPrime14,I] <;> omega
      · have hk2 : k2 := by simp_all
        refine ⟨.ak 4,by simp [NF11.Valid],?_⟩
        intro e
        simp_all [Fixed11,NF11.eval,FixedPick11,ARow,LuRazClosure.BRow,DPrime14,K1Row,KPrime14,I] <;> omega
    · by_cases hk1 : k1
      · by_cases hk2 : k2
        · refine ⟨.ak 2,by simp [NF11.Valid],?_⟩
          intro e
          simp_all [Fixed11,NF11.eval,FixedPick11]
          all_goals omega
        · refine ⟨.ak 0,by simp [NF11.Valid],?_⟩
          intro e
          simp_all [Fixed11,NF11.eval,FixedPick11]
      · have hk2 : k2 := by simp_all
        refine ⟨.ak 1,by simp [NF11.Valid],?_⟩
        intro e
        simp_all [Fixed11,NF11.eval,FixedPick11]

theorem core11_normal (q : Nat) (hq : 4≤q) (R : Nat → Prop)
    (hg : Generated q R) (hc : Core124 R) :
    ∃ w : NF11,w.Valid q ∧ ∀ e,R e ↔ w.eval q e := by
  rcases core11_parts q hq R hg hc with ⟨v,d,k1,k2,hg,he⟩ | ⟨a,b,hab,u,v,d,k1,k2,hg,he⟩
  · obtain ⟨w,hw,hew⟩ := fixed11_normal q hq v d k1 k2 hg
    exact ⟨w,hw,fun e => (he e).trans (hew e)⟩
  · obtain ⟨k,hk,hek⟩ := mixed11_right q a b hq hab u v d k1 k2 hg
    obtain ⟨w,hw,hew⟩ := head11_left_normal q a k hq ⟨hab.1,hab.2.1⟩ hk u
    exact ⟨w,hw,fun e => (he e).trans ((hek e).trans (hew e))⟩

theorem generated_head11 (q a k : Nat) (hq : 4≤q) (ha : 5≤a ∧ a≤2*q+1) (hk : k<3) :
    Generated q (Head11 q a k) := by
  have hj := generated_j q a (g q a) hq (J_single_reachable q a hq ha)
  have hgb := g_bounds q a hq ha
  have hc : k=0 ∨ k=1 ∨ k=2 := by omega
  rcases hc with rfl | rfl | rfl
  · apply generated_congr q (generated_join q hj (generated_k114 q hq))
    intro e
    simp [JRow,Head11,Tail11,K1Row,I]
    omega
  · apply generated_congr q (generated_join q hj (generated_k214 q hq))
    intro e
    simp [JRow,Head11,Tail11,KPrime14,I]
    omega
  · apply generated_congr q (generated_join q (generated_join q hj (generated_k214 q hq))
      (generated_congr q (generated_row q (4*q+1) (by omega)) (fun e => b_source q e hq)))
    intro e
    simp [JRow,Head11,Tail11,KPrime14,LuRazClosure.BRow,I]
    omega

theorem generated_pick11 (q k : Nat) (hq : 4≤q) (hk : k<5) : Generated q (FixedPick11 q k) := by
  have hc : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 := by omega
  have hb := generated_congr q (generated_row q (4*q+1) (by omega)) (fun e => b_source q e hq)
  rcases hc with rfl | rfl | rfl | rfl | rfl
  · exact generated_k114 q hq
  · exact generated_k214 q hq
  · exact generated_join q (generated_k114 q hq) (generated_k214 q hq)
  · exact generated_join q (generated_k114 q hq) hb
  · exact generated_join q (generated_k214 q hq) hb

theorem NF11.generated (q : Nat) (hq : 4≤q) (w : NF11) (hw : w.Valid q) : Generated q (w.eval q) := by
  have ha := generated_congr q (generated_row q (4*q+2) (by omega)) (fun e => a_source q e hq)
  cases w with
  | interval a k => exact generated_head11 q a k hq hw.1 hw.2
  | agap a k => exact generated_join q (generated_head11 q a k hq (by have := hw.1; omega) hw.2) ha
  | ak k => exact generated_join q ha (generated_pick11 q k hq hw)

theorem NF11.core (q : Nat) (hq : 4≤q) (w : NF11) (hw : w.Valid q) : Core124 (w.eval q) := by
  cases w <;> simp [NF11.Valid] at hw
  case interval a k =>
    have hk : k=0 ∨ k=1 ∨ k=2 := by omega
    rcases hk with rfl | rfl | rfl <;> simp_all [NF11.eval,Head11,Tail11,Core124,I] <;> omega
  case agap a k =>
    have hk : k=0 ∨ k=1 ∨ k=2 := by omega
    rcases hk with rfl | rfl | rfl <;> simp_all [NF11.eval,Head11,Tail11,Core124,ARow,I] <;> omega
  case ak k =>
    have hk : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 := by omega
    rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      simp_all [NF11.eval,FixedPick11,Core124,ARow,K1Row,KPrime14,LuRazClosure.BRow,I] <;> omega

theorem core11_exhaustive (q : Nat) (hq : 4≤q) (R : Nat → Prop) :
    Generated q R ∧ Core124 R ↔ ∃ w : NF11,w.Valid q ∧ ∀ e,R e ↔ w.eval q e := by
  constructor
  · exact fun h => core11_normal q hq R h.1 h.2
  · rintro ⟨w,hw,he⟩
    refine ⟨generated_congr q (NF11.generated q hq w hw) (fun e => (he e).symm),?_⟩
    have hc := NF11.core q hq w hw
    unfold Core124 at *
    rw [he 1,he 2,he 3,he 4]
    exact hc

end LuRazSixRowClosure
