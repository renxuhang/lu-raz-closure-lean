import LuRazCore234Normal
namespace LuRazClosure
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

theorem NF234.generated (q : Nat) (hq : 4≤q) (z : NF234) (hz : z.Valid q) : Generated q (z.eval q) := by
  have hpe : P q (q+3) := by unfold P; omega
  have hpl : P q (2*q+1) := by unfold P; omega
  cases z with
  | kr p k =>
    have hb : P q p ∧ k<2 := hz
    have hp' := hb.1
    unfold P at hp'
    have hks : k=0 ∨ k=1 := by omega
    rcases hks with h | h <;> subst k
    · have hg := generated_join q (generated_join q (generated_L q p p hq hb.1 hb.1 (by omega)) (generated_K1 q hq)) (generated_B q hq)
      apply generated_congr q hg
      intro e
      simp only [NF234.eval,T234,LRow,LNormal,K1Row,BRow,I,beta]
      repeat first | (simp_all <;> omega) | split
    · have hg := generated_join q (generated_join q (generated_L q p p hq hb.1 hb.1 (by omega)) (generated_K2 q hq)) (generated_B q hq)
      apply generated_congr q hg
      intro e
      simp only [NF234.eval,T234,LRow,LNormal,K2Row,BRow,I,beta]
      repeat first | (simp_all <;> omega) | split
  | dg p =>
    have hb : P q p ∧ p≤2*q-1 := hz
    have hp' := hb.1
    unfold P at hp'
    have hg := generated_join q (generated_join q (generated_L q p p hq hb.1 hb.1 (by omega)) (generated_D q hq)) (generated_K1 q hq)
    apply generated_congr q hg
    intro e
    simp only [NF234.eval,T234,LRow,LNormal,DRow,K1Row,I,beta]
    repeat first | (simp_all <;> omega) | split
  | km k =>
    have hk : k<2 := hz
    have hks : k=0 ∨ k=1 := by omega
    rcases hks with h | h <;> subst k
    · have hg := generated_join q (generated_L q (q+3) (q+3) hq hpe hpe (by omega)) (generated_K1 q hq)
      apply generated_congr q hg
      intro e
      simp only [NF234.eval,T234,LRow,LNormal,K1Row,I,beta]
      repeat first | (simp_all <;> omega) | split
    · have hg := generated_join q (generated_L q (q+3) (q+3) hq hpe hpe (by omega)) (generated_K2 q hq)
      apply generated_congr q hg
      intro e
      simp only [NF234.eval,T234,LRow,LNormal,K2Row,I,beta]
      repeat first | (simp_all <;> omega) | split
  | ck k =>
    have hk : k<2 := hz
    have hks : k=0 ∨ k=1 := by omega
    rcases hks with h | h <;> subst k
    · have hg := generated_join q (generated_C q hq) (generated_K1 q hq)
      apply generated_congr q hg
      intro e
      simp only [NF234.eval,T234,CRow,K1Row,I]
      omega
    · have hg := generated_join q (generated_C q hq) (generated_K2 q hq)
      apply generated_congr q hg
      intro e
      simp only [NF234.eval,T234,CRow,K2Row,I]
      omega
  | last =>
    have hg := generated_join q (generated_L q (2*q+1) (2*q+1) hq hpl hpl (by omega)) (generated_K1 q hq)
    apply generated_congr q hg
    intro e
    simp only [NF234.eval,T234,LRow,LNormal,K1Row,I,beta]
    repeat first | (simp_all <;> omega) | split

theorem NF234.core (q : Nat) (hq : 4≤q) (z : NF234) (hz : z.Valid q) : Core234 (z.eval q) := by
  unfold Core234
  cases z <;> simp only [NF234.Valid] at hz <;>
    simp only [NF234.eval,T234,I] <;> (simp_all <;> omega)

theorem core234_closure_exact (q : Nat) (hq : 4≤q) (R : Nat → Prop) :
    Generated q R ∧ Core234 R ↔ ∃ z : NF234, z.Valid q ∧ ∀ e, R e ↔ z.eval q e := by
  constructor
  · rintro ⟨hg,hc⟩
    rcases core234_parts q hq R hg hc with ⟨v,w,k1,k2,hK,he⟩ | ⟨t,p,ht,hp,htp,u,v,w,k1,k2,hK,he⟩
    · obtain ⟨z,hz,hn⟩ := fixed234_normal q hq v w k1 k2 hK
      exact ⟨z,hz,fun e => (he e).trans (hn e)⟩
    · obtain ⟨z,hz,hn⟩ := mixed234_normal q t p hq ht hp htp u v w k1 k2 hK
      exact ⟨z,hz,fun e => (he e).trans (hn e)⟩
  · rintro ⟨z,hz,he⟩
    refine ⟨generated_congr q (NF234.generated q hq z hz) (fun e => (he e).symm),?_⟩
    have hc := NF234.core q hq z hz
    unfold Core234 at hc ⊢
    exact ⟨fun h => hc.1 ((he 1).mp h),(he 2).mpr hc.2.1,(he 3).mpr hc.2.2.1,(he 4).mpr hc.2.2.2⟩
end LuRazClosure
