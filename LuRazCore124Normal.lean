import LuRazCore124

namespace LuRazClosure
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

def T124 (a b e : Nat) : Prop := e=1 ∨ e=2 ∨ e=4 ∨ I a b e
inductive NF124 where
  | interval (a k : Nat)
  | agap (a k : Nat)
  | ak (z : NF24)
  deriving DecidableEq, Repr

def NF124.Valid (q : Nat) : NF124 → Prop
  | .interval a k => (5≤a ∧ a≤2*q+1) ∧ k<3
  | .agap a k => (q+4≤a ∧ a≤2*q+1) ∧ k<3
  | .ak z => z≠.dBig
def NF124.eval (q : Nat) : NF124 → Nat → Prop
  | .interval a k => T124 a (4*q-2+k)
  | .agap a k => fun e => T124 a (4*q-2+k) e ∨ ARow q e
  | .ak z => fun e => ARow q e ∨ z.eval q e

theorem mixed124_right (q a b : Nat) (hq : 4≤q) (hab : JReachable q a b)
    (u v d k1 k2 : Prop) (hg : d ∨ k1 ∨ k2) :
    ∃ k, k<3 ∧ ∀ e, Mixed124 q a b u v d k1 k2 e ↔ T124 a (4*q-2+k) e ∨ (u ∧ ARow q e) := by
  classical
  have hab' := hab
  unfold JReachable at hab'
  by_cases hd : d
  · refine ⟨2,by decide,?_⟩
    intro e
    by_cases hu : u <;>
      simp only [hu,Mixed124,Fixed124,hd,true_and,T124,JRow,K1Row,K2Row,DRow,BRow,ARow,I,true_and,false_and,false_or,or_false] <;> omega
  · have hK : k1 ∨ k2 := by rcases hg with h | h | h; exact False.elim (hd h); exact Or.inl h; exact Or.inr h
    by_cases hv : v
    · rcases hK with hk1 | hk2
      · refine ⟨2,by decide,?_⟩
        intro e
        by_cases hu : u <;>
          simp only [hu,Mixed124,Fixed124,hd,hv,hk1,true_and,false_and,false_or,T124,JRow,K1Row,K2Row,DRow,BRow,ARow,I,true_and,false_and,false_or,or_false] <;> omega
      · refine ⟨2,by decide,?_⟩
        intro e
        by_cases hu : u <;>
          simp only [hu,Mixed124,Fixed124,hd,hv,hk2,true_and,false_and,false_or,T124,JRow,K1Row,K2Row,DRow,BRow,ARow,I,true_and,false_and,false_or,or_false] <;> omega
    · by_cases hk2 : k2
      · refine ⟨1,by decide,?_⟩
        intro e
        by_cases hu : u <;>
          simp only [hu,Mixed124,Fixed124,hd,hv,hk2,true_and,false_and,false_or,T124,JRow,K1Row,K2Row,DRow,BRow,ARow,I,true_and,false_and,false_or,or_false] <;> omega
      · have hk1 : k1 := by rcases hK with h | h; exact h; exact False.elim (hk2 h)
        refine ⟨0,by decide,?_⟩
        intro e
        by_cases hu : u <;>
          simp only [hu,Mixed124,Fixed124,hd,hv,hk2,hk1,true_and,false_and,false_or,T124,JRow,K1Row,K2Row,DRow,BRow,ARow,I,true_and,false_and,false_or,or_false] <;> omega

theorem t124_left_normal (q a k : Nat) (hq : 4≤q) (ha : 5≤a ∧ a≤2*q+1) (hk : k<3) (u : Prop) :
    ∃ z : NF124, z.Valid q ∧ ∀ e, (T124 a (4*q-2+k) e ∨ (u ∧ ARow q e)) ↔ z.eval q e := by
  classical
  by_cases hu : u
  · by_cases hal : a≤q+3
    · refine ⟨.interval 5 k,⟨by omega,hk⟩,?_⟩
      intro e
      simp only [NF124.eval,hu,true_and,T124,ARow,I]
      omega
    · exact ⟨.agap a k,⟨by omega,hk⟩,fun e => by simp only [NF124.eval,hu,true_and]⟩
  · exact ⟨.interval a k,⟨ha,hk⟩,fun e => by simp only [NF124.eval,hu,false_and,or_false]⟩

theorem a24_normal (q : Nat) (hq : 4≤q) (w : NF24) :
    ∃ z : NF124, z.Valid q ∧ ∀ e, (ARow q e ∨ w.eval q e) ↔ z.eval q e := by
  by_cases h : w=.dBig
  · subst w
    refine ⟨.agap (2*q+1) 2,⟨by omega,by decide⟩,?_⟩
    intro e
    simp only [NF124.eval,NF24.eval,T124,ARow,K1Row,DRow,I]
    omega
  · exact ⟨.ak w,h,fun _ => Iff.rfl⟩

theorem generated_t124 (q a k : Nat) (hq : 4≤q) (ha : 5≤a ∧ a≤2*q+1) (hk : k<3) :
    Generated q (T124 a (4*q-2+k)) := by
  have hj := generated_J q a (g q a) hq (J_single_reachable q a hq ha)
  have hgb := g_bounds q a hq ha
  have hc : k=0 ∨ k=1 ∨ k=2 := by omega
  rcases hc with h | h | h <;> subst k
  · apply generated_congr q (generated_join q hj (generated_K1 q hq))
    intro e
    unfold JRow K1Row T124 I
    omega
  · apply generated_congr q (generated_join q hj (generated_K2 q hq))
    intro e
    unfold JRow K2Row T124 I
    omega
  · apply generated_congr q (generated_join q hj (generated_join q (generated_K1 q hq) (generated_B q hq)))
    intro e
    unfold JRow K1Row BRow T124 I
    omega

theorem NF124.generated (q : Nat) (hq : 4≤q) (z : NF124) (hz : z.Valid q) : Generated q (z.eval q) := by
  cases z with
  | interval a k => exact generated_t124 q a k hq hz.1 hz.2
  | agap a k =>
    have ha : 5≤a ∧ a≤2*q+1 := by have := hz.1; omega
    exact generated_join q (generated_t124 q a k hq ha hz.2) (generated_A q hq)
  | ak w => exact generated_join q (generated_A q hq) (NF24.generated q hq w)

theorem NF124.core (q : Nat) (hq : 4≤q) (z : NF124) (hz : z.Valid q) : Core124 (z.eval q) := by
  cases z with
  | interval a k =>
    have hb : (5≤a ∧ a≤2*q+1) ∧ k<3 := hz
    simp only [Core124,NF124.eval,T124,I]
    simp_all <;> omega
  | agap a k =>
    have hb : (q+4≤a ∧ a≤2*q+1) ∧ k<3 := hz
    simp only [Core124,NF124.eval,T124,ARow,I]
    simp_all <;> omega
  | ak w =>
    have hc := NF24.core q hq w
    have hn : ¬ARow q 3 := by unfold ARow I; omega
    refine ⟨Or.inl (Or.inl rfl),Or.inr hc.2.1,?_,Or.inr hc.2.2.2⟩
    rintro (h | h)
    · exact hn h
    · exact hc.2.2.1 h

theorem core124_closure_exact (q : Nat) (hq : 4≤q) (R : Nat → Prop) :
    (Generated q R ∧ Core124 R) ↔ ∃ z : NF124, z.Valid q ∧ ∀ e, R e ↔ z.eval q e := by
  constructor
  · rintro ⟨hg,hc⟩
    rcases core124_parts q hq R hg hc with ⟨w,he⟩ | ⟨a,b,hab,u,v,d,k1,k2,hguard,he⟩
    · obtain ⟨z,hz,heq⟩ := a24_normal q hq w
      exact ⟨z,hz,fun e => (he e).trans (heq e)⟩
    · obtain ⟨k,hk,hr⟩ := mixed124_right q a b hq hab u v d k1 k2 hguard
      obtain ⟨z,hz,hl⟩ := t124_left_normal q a k hq ⟨hab.1,hab.2.1⟩ hk u
      exact ⟨z,hz,fun e => ((he e).trans (hr e)).trans (hl e)⟩
  · rintro ⟨z,hz,he⟩
    have hc := NF124.core q hq z hz
    exact ⟨generated_congr q (NF124.generated q hq z hz) (fun e => (he e).symm),
      (he 1).mpr hc.1,(he 2).mpr hc.2.1,fun h => hc.2.2.1 ((he 3).mp h),(he 4).mpr hc.2.2.2⟩

end LuRazClosure

