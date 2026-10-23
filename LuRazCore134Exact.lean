import LuRazCore134Normal
namespace LuRazClosure
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

theorem j134_from_five (q b : Nat) (hq : 4≤q) (hb : 2*q+2≤b ∧ b≤4*q-3) : Generated q (JRow 5 b) := by
  apply generated_J q 5 b hq
  unfold JReachable g
  split <;> omega

theorem NF134.generated (q : Nat) (hq : 4≤q) (z : NF134) (hz : z.Valid q) : Generated q (z.eval q) := by
  cases z with
  | ej a =>
    have ha : 5≤a ∧ a≤2*q+1 := hz
    have hgB := g_bounds q a hq ha
    have hj := generated_J q a (4*q-3) hq (by unfold JReachable; omega)
    apply generated_congr q (generated_join q hj (generated_E q hq))
    intro e
    simp only [NF134.eval,T134,JRow,ERow,I]
    omega
  | aej a =>
    have ha : q+4≤a ∧ a≤2*q+1 := hz
    have hgB := g_bounds q a hq (by omega)
    have hj := generated_J q a (4*q-3) hq (by unfold JReachable; omega)
    apply generated_congr q (generated_join q (generated_join q hj (generated_E q hq)) (generated_A q hq))
    intro e
    simp only [NF134.eval,T134,JRow,ERow,ARow,I]
    omega
  | cj b =>
    have hb := hz
    simp only [NF134.Valid] at hb
    apply generated_congr q (generated_join q (j134_from_five q b hq (hz.1)) (generated_C q hq))
    intro e
    simp only [NF134.eval,T134,JRow,CRow,ZRow,BRow,I]
    omega
  | zj b =>
    have hb := hz
    simp only [NF134.Valid] at hb
    apply generated_congr q (generated_join q (j134_from_five q b hq (hz)) (generated_Z q hq))
    intro e
    simp only [NF134.eval,T134,JRow,CRow,ZRow,BRow,I]
    omega
  | czj b =>
    have hb := hz
    simp only [NF134.Valid] at hb
    apply generated_congr q (generated_join q (generated_join q (j134_from_five q b hq (by have hb : 2*q+2≤b ∧ b≤3*q-1 := hz; omega)) (generated_C q hq)) (generated_Z q hq))
    intro e
    simp only [NF134.eval,T134,JRow,CRow,ZRow,BRow,I]
    omega
  | zjb b =>
    have hb := hz
    simp only [NF134.Valid] at hb
    apply generated_congr q (generated_join q (generated_join q (j134_from_five q b hq (by have hb : 2*q+2≤b ∧ b≤3*q := hz; omega)) (generated_Z q hq)) (generated_B q hq))
    intro e
    simp only [NF134.eval,T134,JRow,CRow,ZRow,BRow,I]
    omega
  | cjb b =>
    have hb := hz
    simp only [NF134.Valid] at hb
    apply generated_congr q (generated_join q (generated_join q (j134_from_five q b hq (by have hb : 2*q+2≤b ∧ b≤3*q-1 := hz; omega)) (generated_C q hq)) (generated_B q hq))
    intro e
    simp only [NF134.eval,T134,JRow,CRow,ZRow,BRow,I]
    omega
  | extra k =>
    have hk : k<3 := hz
    have hc : k=0 ∨ k=1 ∨ k=2 := by omega
    rcases hc with h | h | h <;> subst k
    · apply generated_congr q (generated_Z q hq)
      intro e
      simp [NF134.eval]
    · apply generated_congr q (generated_join q (generated_Z q hq) (generated_B q hq))
      intro e
      simp [NF134.eval]
    · apply generated_congr q (generated_join q (generated_Z q hq) (generated_E q hq))
      intro e
      simp [NF134.eval]

theorem NF134.core (q : Nat) (hq : 4≤q) (z : NF134) (hz : z.Valid q) : Core134 (z.eval q) := by
  cases z <;> simp only [NF134.Valid] at hz <;>
    simp only [Core134,NF134.eval,T134,ZRow,BRow,ERow,I,true_or,or_true,false_or,or_false] <;> (simp_all <;> omega)

theorem core134_closure_exact (q : Nat) (hq : 4≤q) (R : Nat → Prop) :
    Generated q R ∧ Core134 R ↔ ∃ z : NF134, z.Valid q ∧ ∀ e, R e ↔ z.eval q e := by
  constructor
  · rintro ⟨hg,hc⟩
    rcases core134_parts q hq R hg hc with ⟨u,v,d,k1,he⟩ | ⟨a,b,hab,u,v,d,k1,k2,hguard,he⟩
    · obtain ⟨z,hz,hn⟩ := fixed134_normal q hq u v d k1
      exact ⟨z,hz,fun e => (he e).trans (hn e)⟩
    · obtain ⟨z,hz,hn⟩ := mixed134_normal q a b hq hab u v d k1 k2 hguard
      exact ⟨z,hz,fun e => (he e).trans (hn e)⟩
  · rintro ⟨z,hz,he⟩
    refine ⟨generated_congr q (NF134.generated q hq z hz) (fun e => (he e).symm),?_⟩
    have hc := NF134.core q hq z hz
    unfold Core134 at hc ⊢
    exact ⟨(he 1).mpr hc.1,fun h => hc.2.1 ((he 2).mp h),(he 3).mpr hc.2.2.1,(he 4).mpr hc.2.2.2⟩
end LuRazClosure
