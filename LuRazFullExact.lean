import LuRazFullCoverage
namespace LuRazClosure
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000
set_option linter.unusedSimpArgs false

theorem generated_KRow (q k : Nat) (hq : 4≤q) (hk : k<2) : Generated q (KRow q k) := by
  have hc : k=0 ∨ k=1 := by omega
  rcases hc with h | h <;> subst k
  · exact generated_congr q (generated_K1 q hq) (fun e => (KRow_zero q e).symm)
  · exact generated_congr q (generated_K2 q hq) (fun e => (KRow_one q e hq).symm)

theorem NFFull.generated (q : Nat) (hq : 4≤q) (z : NFFull) (hz : z.Valid q) : Generated q (z.eval q) := by
  have hp4 : P q 4 := by unfold P; omega
  have hpe : P q (q+3) := by unfold P; omega
  have hplast : P q (2*q+1) := by unfold P; omega
  cases z with
  | noNInterval k =>
    have hb := hz
    simp only [NFFull.Valid] at hb
    apply generated_congr q (generated_join q (generated_join q (generated_A q hq) (generated_C q hq)) (generated_KRow q k hq hb))
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,KRow,K1Row,K2Row,JRow,LRow,LNormal,I,beta]
    repeat first | omega | (simp_all <;> omega) | split
  | noNMJRight b =>
    have hb := hz
    simp only [NFFull.Valid] at hb
    apply generated_congr q (generated_join q (generated_L q (q+3) (q+3) hq hpe hpe (by omega)) (j134_from_five q b hq (by omega)))
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,KRow,K1Row,K2Row,JRow,LRow,LNormal,I,beta]
    repeat first | omega | (simp_all <;> omega) | split
  | noNMJLeft a =>
    have hb := hz
    simp only [NFFull.Valid] at hb
    apply generated_congr q (generated_join q (generated_L q (q+3) (q+3) hq hpe hpe (by omega)) (generated_J q a (4*q-3) hq (J_max_reachable q a hq (by omega))))
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,KRow,K1Row,K2Row,JRow,LRow,LNormal,I,beta]
    repeat first | omega | (simp_all <;> omega) | split
  | noNMK k =>
    have hb := hz
    simp only [NFFull.Valid] at hb
    apply generated_congr q (generated_join q (generated_join q (generated_A q hq) (generated_L q (q+3) (q+3) hq hpe hpe (by omega))) (generated_KRow q k hq hb))
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,KRow,K1Row,K2Row,JRow,LRow,LNormal,I,beta]
    repeat first | omega | (simp_all <;> omega) | split
  | noNCMJ b =>
    have hb := hz
    simp only [NFFull.Valid] at hb
    apply generated_congr q (generated_join q (generated_join q (generated_C q hq) (generated_L q (q+3) (q+3) hq hpe hpe (by omega))) (j134_from_five q b hq (by omega)))
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,KRow,K1Row,K2Row,JRow,LRow,LNormal,I,beta]
    repeat first | omega | (simp_all <;> omega) | split
  | noH1Short p k =>
    have hb : (4≤p ∧ p≤2*q) ∧ k<2 := hz
    by_cases he : p=q+2
    · apply generated_congr q (generated_join q (generated_join q (generated_join q (generated_join q (generated_A q hq) (generated_L q 4 4 hq hp4 hp4 (by omega))) (generated_KRow q k hq hb.2)) (generated_E q hq)) (generated_B q hq))
      intro e
      simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,KRow,K1Row,K2Row,JRow,LRow,LNormal,I,beta]
      repeat first | omega | (simp_all <;> omega) | split
    · have hp : P q p := by unfold P; omega
      apply generated_congr q (generated_join q (generated_join q (generated_join q (generated_L q p p hq hp hp (by omega)) (generated_KRow q k hq hb.2)) (generated_E q hq)) (generated_B q hq))
      intro e
      simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,KRow,K1Row,K2Row,JRow,LRow,LNormal,I,beta]
      repeat first | omega | (simp_all <;> omega) | split
  | noH1ZL a =>
    have ha : 2*q+4≤a ∧ a≤4*q-1 := hz
    obtain ⟨t,ht,he⟩ := beta_surjective q a hq (by omega)
    have ht' := ht
    unfold P at ht'
    unfold beta at he
    apply generated_congr q (generated_join q (generated_Z q hq) (generated_L q t t hq ht ht (by omega)))
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,KRow,K1Row,K2Row,JRow,LRow,LNormal,I,beta]
    repeat first | omega | (simp_all <;> omega) | split
  | noH1Exception  =>
    have hb := hz
    simp only [NFFull.Valid] at hb
    apply generated_congr q (generated_join q (generated_Z q hq) (generated_K1 q hq))
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,KRow,K1Row,K2Row,JRow,LRow,LNormal,I,beta]
    repeat first | omega | (simp_all <;> omega) | split
  | noH2 a =>
    have ha : 2*q+3≤a ∧ a≤4*q := hz
    by_cases he : a=2*q+3
    · apply generated_congr q (generated_join q (generated_join q (generated_E q hq) (generated_L q (2*q+1) (2*q+1) hq hplast hplast (by omega))) (generated_K2 q hq))
      intro e
      simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,KRow,K1Row,K2Row,JRow,LRow,LNormal,I,beta]
      repeat first | omega | (simp_all <;> omega) | split
    · obtain ⟨t,ht,heq⟩ := beta_surjective q a hq (by omega)
      have ht' := ht
      unfold P at ht'
      unfold beta at heq
      apply generated_congr q (generated_join q (generated_join q (generated_Z q hq) (generated_L q t t hq ht ht (by omega))) (generated_L q (2*q+1) (2*q+1) hq hplast hplast (by omega)))
      intro e
      simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,KRow,K1Row,K2Row,JRow,LRow,LNormal,I,beta]
      repeat first | omega | (simp_all <;> omega) | split
  | noFive a =>
    have hb := hz
    simp only [NFFull.Valid] at hb
    apply generated_congr q (generated_join q (generated_J q a (4*q-3) hq (J_max_reachable q a hq (by omega))) (generated_L q 4 4 hq hp4 hp4 (by omega)))
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,KRow,K1Row,K2Row,JRow,LRow,LNormal,I,beta]
    repeat first | omega | (simp_all <;> omega) | split
  | leftGap p a =>
    have hb : (5≤p ∧ p≤2*q-1) ∧ p+2≤a ∧ a≤2*q+1 := hz
    by_cases he : p=q+2
    · apply generated_congr q (generated_join q (generated_join q (generated_A q hq) (generated_L q 4 4 hq hp4 hp4 (by omega))) (generated_J q a (4*q-3) hq (J_max_reachable q a hq (by omega))))
      intro e
      simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,KRow,K1Row,K2Row,JRow,LRow,LNormal,I,beta]
      repeat first | omega | (simp_all <;> omega) | split
    · have hp : P q p := by unfold P; omega
      have hp' := hp
      unfold P at hp'
      apply generated_congr q (generated_join q (generated_join q (generated_L q p p hq hp hp (by omega)) (generated_J q a (4*q-3) hq (J_max_reachable q a hq (by omega)))) (generated_B q hq))
      intro e
      simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,KRow,K1Row,K2Row,JRow,LRow,LNormal,I,beta]
      repeat first | omega | (simp_all <;> omega) | split
  | full =>
    apply generated_congr q (generated_row q 0 (by omega))
    intro e
    rw [LuRazParametric.row_case_0 q 0 e (by omega) rfl]
    simp only [NFFull.eval,FullHead,I]
    omega
  | rightGap b c =>
    have hb : (2*q+2≤b ∧ b≤4*q-2) ∧ b+2≤c ∧ c≤4*q := hz
    by_cases he : b≤4*q-3
    · obtain ⟨t,ht,heq⟩ := beta_surjective q c hq (by omega)
      have ht' := ht
      unfold P at ht'
      unfold beta at heq
      apply generated_congr q (generated_join q (generated_join q (j134_from_five q b hq (by omega)) (generated_L q t t hq ht ht (by omega))) (generated_Z q hq))
      intro e
      simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,KRow,K1Row,K2Row,JRow,LRow,LNormal,I,beta]
      repeat first | omega | (simp_all <;> omega) | split
    · apply generated_congr q (generated_join q (generated_join q (generated_C q hq) (generated_K1 q hq)) (generated_Z q hq))
      intro e
      simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,KRow,K1Row,K2Row,JRow,LRow,LNormal,I,beta]
      repeat first | omega | (simp_all <;> omega) | split
  | isolatedR b c =>
    have hb : (2*q+2≤b ∧ b≤3*q-1) ∧ 3*q+3≤c ∧ c≤4*q := hz
    obtain ⟨t,ht,heq⟩ := beta_surjective q c hq (by omega)
    have ht' := ht
    unfold P at ht'
    unfold beta at heq
    apply generated_congr q (generated_join q (generated_join q (generated_join q (j134_from_five q b hq (by omega)) (generated_C q hq)) (generated_L q t t hq ht ht (by omega))) (generated_Z q hq))
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,KRow,K1Row,K2Row,JRow,LRow,LNormal,I,beta]
    repeat first | omega | (simp_all <;> omega) | split

theorem NFFull.core (q : Nat) (hq : 4≤q) (z : NFFull) (hz : z.Valid q) : CoreFull (z.eval q) := by
  cases z <;> simp only [NFFull.Valid] at hz <;>
    simp only [CoreFull,NFFull.eval,FullHead,I] <;> (simp_all <;> omega)

theorem full_closure_exact (q : Nat) (hq : 4≤q) (R : Nat → Prop) :
    Generated q R ∧ CoreFull R ↔ ∃ z : NFFull, z.Valid q ∧ ∀ e, R e ↔ z.eval q e := by
  constructor
  · rintro ⟨hg,hc⟩
    exact full_closure_normalizes q hq R hg hc
  · rintro ⟨z,hz,he⟩
    refine ⟨generated_congr q (NFFull.generated q hq z hz) (fun e => (he e).symm),?_⟩
    have hc := NFFull.core q hq z hz
    unfold CoreFull at hc ⊢
    exact ⟨(he 1).mpr hc.1,(he 2).mpr hc.2.1,(he 3).mpr hc.2.2.1,(he 4).mpr hc.2.2.2⟩
end LuRazClosure
