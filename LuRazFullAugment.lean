import LuRazFullFixed
namespace LuRazClosure
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

def FullNormalizes (q : Nat) (R : Nat → Prop) : Prop :=
  ∃ z : NFFull, z.Valid q ∧ ∀ e, R e ↔ z.eval q e

theorem full_normalizes_congr (q : Nat) (R T : Nat → Prop) (hR : FullNormalizes q R)
    (he : ∀ e, R e ↔ T e) : FullNormalizes q T := by
  obtain ⟨z,hz,hr⟩ := hR
  exact ⟨z,hz,fun e => (he e).symm.trans (hr e)⟩

theorem full_normalizes_optional (q : Nat) (R T : Nat → Prop)
    (hstab : ∀ z : NFFull, z.Valid q → ∃ w : NFFull, w.Valid q ∧ ∀ e, (z.eval q e ∨ T e) ↔ w.eval q e)
    (hR : FullNormalizes q R) (u : Prop) : FullNormalizes q (fun e => R e ∨ (u∧T e)) := by
  classical
  by_cases hu : u
  · obtain ⟨z,hz,hr⟩ := hR
    obtain ⟨w,hw,he⟩ := hstab z hz
    refine ⟨w,hw,?_⟩
    intro e
    simpa only [hu,true_and,hr e] using he e
  · exact full_normalizes_congr q R _ hR (fun e => by simp only [hu,false_and,or_false])

def FixedAug (q : Nat) (R : Nat → Prop) (u v c d f z k1 k2 : Prop) (e : Nat) : Prop :=
  R e ∨ (u∧ARow q e) ∨ (v∧BRow q e) ∨ (c∧CRow q e) ∨ (d∧DRow q e) ∨
    (f∧ERow q e) ∨ (z∧ZRow q e) ∨ (k1∧K1Row q e) ∨ (k2∧K2Row q e)

theorem full_normalizes_fixedAug (q : Nat) (hq : 4≤q) (R : Nat → Prop)
    (hR : FullNormalizes q R) (u v c d f z k1 k2 : Prop) :
    FullNormalizes q (FixedAug q R u v c d f z k1 k2) := by
  have h1 := full_normalizes_optional q R (ARow q) (NFFull.addA q hq) hR u
  have h2 := full_normalizes_optional q _ (BRow q) (NFFull.addB q hq) h1 v
  have h3 := full_normalizes_optional q _ (CRow q) (NFFull.addC q hq) h2 c
  have h4 := full_normalizes_optional q _ (DRow q) (NFFull.addD q hq) h3 d
  have h5 := full_normalizes_optional q _ (ERow q) (NFFull.addE q hq) h4 f
  have h6 := full_normalizes_optional q _ (ZRow q) (NFFull.addZ q hq) h5 z
  have h7 := full_normalizes_optional q _ (K1Row q) (NFFull.addK1 q hq) h6 k1
  have h8 := full_normalizes_optional q _ (K2Row q) (NFFull.addK2 q hq) h7 k2
  apply full_normalizes_congr q _ _ h8
  intro e
  simp only [FixedAug,or_assoc]

theorem pair23_14_full_normal (q : Nat) (hq : 4≤q) (U V : Nat → Prop)
    (hU : Generated q U) (hcU : Core23 U) (hV : Generated q V) (hcV : Core14 V) :
    FullNormalizes q (fun e => U e ∨ V e) := by
  obtain ⟨t,p,ht,hp,htp,c,d,v,hu⟩ := full_core23_mixed q hq U hU hcU
  obtain ⟨a,b,hab,u,v',hv⟩ := full_core14_mixed q hq V hV hcV
  have h0 : FullNormalizes q (fun e => LRow q t p e ∨ JRow a b e) := lp_j_full_normal q t p a b hq ht hp htp hab
  have h1 := full_normalizes_fixedAug q hq _ h0 u (v∨v') c d False False False False
  apply full_normalizes_congr q _ _ h1
  intro e
  rw [hu e,hv e]
  simp only [FixedAug,Mixed23,Mixed14,false_and,false_or,or_false,or_and_right,or_assoc,or_left_comm,or_comm]
end LuRazClosure
