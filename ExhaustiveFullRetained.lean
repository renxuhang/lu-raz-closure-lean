import ExhaustiveFullCovers
namespace LuRazThreeRow
open LuRazClosure LuRazParametric
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000
set_option linter.unusedSimpArgs false
theorem retained_full_generated (q : Nat) (hq : 4≤q) (z : NFFull) (hhz : z.Valid q ∧ ¬LostFull q z) : Generated q (z.eval q) := by
  have hz := hhz.1
  have hnot := hhz.2
  have hA := generated_congr q (generated_row q (4*q+2) (by omega)) (fun e => a_source q e hq)
  have hLP := generated_congr q (generated_row q (4*q-1) (by omega)) (fun e => last_source q e hq)
  have hp4 : P q 4 := by unfold P; omega
  have hpe : P q (q+3) := by unfold P; omega
  have hplast : P q (2*q+1) := by unfold P; omega
  cases z with
  | noNInterval k =>
    have hb := hz
    simp only [NFFull.Valid] at hb
    apply generated_congr q (generated_join q (generated_join q (hA) (generated_c q hq)) (generated_krow q k hq hb))
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,LPrime,KRow,K1Row,K2Row,JRow,LRow,LNormal,I,beta]
    repeat first | omega | (simp_all <;> omega) | split
  | noNMJRight b =>
    have hb := hz
    simp only [NFFull.Valid] at hb
    apply generated_congr q (generated_join q (generated_l q (q+3) (q+3) hq hpe hpe (by omega) (by omega)) (j134_five q b hq (by omega)))
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,LPrime,KRow,K1Row,K2Row,JRow,LRow,LNormal,I,beta]
    repeat first | omega | (simp_all <;> omega) | split
  | noNMJLeft a =>
    have hb := hz
    simp only [NFFull.Valid] at hb
    apply generated_congr q (generated_join q (generated_l q (q+3) (q+3) hq hpe hpe (by omega) (by omega)) (generated_j q a (4*q-3) hq (J_max_reachable q a hq (by omega))))
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,LPrime,KRow,K1Row,K2Row,JRow,LRow,LNormal,I,beta]
    repeat first | omega | (simp_all <;> omega) | split
  | noNMK k =>
    have hb := hz
    simp only [NFFull.Valid] at hb
    apply generated_congr q (generated_join q (generated_join q (hA) (generated_l q (q+3) (q+3) hq hpe hpe (by omega) (by omega))) (generated_krow q k hq hb))
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,LPrime,KRow,K1Row,K2Row,JRow,LRow,LNormal,I,beta]
    repeat first | omega | (simp_all <;> omega) | split
  | noNCMJ b =>
    have hb := hz
    simp only [NFFull.Valid] at hb
    apply generated_congr q (generated_join q (generated_join q (generated_c q hq) (generated_l q (q+3) (q+3) hq hpe hpe (by omega) (by omega))) (j134_five q b hq (by omega)))
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,LPrime,KRow,K1Row,K2Row,JRow,LRow,LNormal,I,beta]
    repeat first | omega | (simp_all <;> omega) | split
  | noH1Short p k =>
    have hb : (4≤p ∧ p≤2*q) ∧ k<2 := hz
    by_cases he : p=q+2
    · apply generated_congr q (generated_join q (generated_join q (generated_join q (generated_join q (hA) (generated_l q 4 4 hq hp4 hp4 (by omega) (by omega))) (generated_krow q k hq hb.2)) (generated_e2 q hq)) (generated_b q hq))
      intro e
      simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,LPrime,KRow,K1Row,K2Row,JRow,LRow,LNormal,I,beta]
      repeat first | omega | (simp_all <;> omega) | split
    · have hp : P q p := by unfold P; omega
      apply generated_congr q (generated_join q (generated_join q (generated_join q (generated_l q p p hq hp hp (by omega) (by omega)) (generated_krow q k hq hb.2)) (generated_e2 q hq)) (generated_b q hq))
      intro e
      simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,LPrime,KRow,K1Row,K2Row,JRow,LRow,LNormal,I,beta]
      repeat first | omega | (simp_all <;> omega) | split
  | noH1ZL a => exact False.elim (hnot True.intro)
  | noH1Exception => exact False.elim (hnot True.intro)
  | noH2 a =>
    have ha : 2*q+3≤a ∧ a≤4*q := hz
    have han : a≠4*q := hnot
    by_cases he : a=2*q+3
    · subst a
      apply generated_congr q (generated_join q (generated_join q hA hLP) (generated_k2 q hq))
      intro e
      simp only [NFFull.eval,FullHead,ARow,LPrime,K2Row,I]
      omega
    · obtain ⟨t,ht,heq⟩ := beta_surjective q a hq (by omega)
      have htl : t≤2*q := by unfold P at ht; unfold beta at heq; split at heq <;> omega
      apply generated_congr q (generated_join q (generated_join q hA hLP) (generated_l q t t hq ht ht (by omega) htl))
      intro e
      unfold P at ht; unfold beta at heq
      simp only [NFFull.eval,FullHead,ARow,LPrime,LRow,LNormal,I,beta]
      repeat first | (simp_all <;> omega) | split
  | noFive a =>
    have hb := hz
    simp only [NFFull.Valid] at hb
    apply generated_congr q (generated_join q (generated_j q a (4*q-3) hq (J_max_reachable q a hq (by omega))) (generated_l q 4 4 hq hp4 hp4 (by omega) (by omega)))
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,LPrime,KRow,K1Row,K2Row,JRow,LRow,LNormal,I,beta]
    repeat first | omega | (simp_all <;> omega) | split
  | leftGap p a =>
    have hb : (5≤p ∧ p≤2*q-1) ∧ p+2≤a ∧ a≤2*q+1 := hz
    by_cases he : p=q+2
    · apply generated_congr q (generated_join q (generated_join q (hA) (generated_l q 4 4 hq hp4 hp4 (by omega) (by omega))) (generated_j q a (4*q-3) hq (J_max_reachable q a hq (by omega))))
      intro e
      simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,LPrime,KRow,K1Row,K2Row,JRow,LRow,LNormal,I,beta]
      repeat first | omega | (simp_all <;> omega) | split
    · have hp : P q p := by unfold P; omega
      have hp' := hp
      unfold P at hp'
      apply generated_congr q (generated_join q (generated_join q (generated_l q p p hq hp hp (by omega) (by omega)) (generated_j q a (4*q-3) hq (J_max_reachable q a hq (by omega)))) (generated_b q hq))
      intro e
      simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,LPrime,KRow,K1Row,K2Row,JRow,LRow,LNormal,I,beta]
      repeat first | omega | (simp_all <;> omega) | split
  | full =>
    apply generated_congr q (generated_row q 0 (by omega))
    intro e
    rw [unchanged_row q 0 e (by unfold Special; omega),LuRazParametric.row_case_0 q 0 e (by omega) rfl]
    simp only [NFFull.eval,FullHead,I]
    omega
  | rightGap b c =>
    have hb : (2*q+2≤b ∧ b≤4*q-2) ∧ b+2≤c ∧ c≤4*q := hz
    by_cases he : b≤4*q-3
    · have hcn : c≠4*q := by intro hc; exact hnot ⟨hc,he⟩
      obtain ⟨t,ht,heq⟩ := beta_surjective q c hq (by omega)
      have htl : t≤2*q := by unfold P at ht; unfold beta at heq; split at heq <;> omega
      apply generated_congr q (generated_join q (generated_join q (j134_five q b hq (by omega))
        (generated_l q t t hq ht ht (by omega) htl)) hLP)
      intro e
      unfold P at ht; unfold beta at heq
      simp only [NFFull.eval,FullHead,JRow,LPrime,LRow,LNormal,I,beta]
      repeat first | (simp_all <;> omega) | split
    · apply generated_congr q (generated_join q (generated_join q (generated_join q hA hLP)
        (generated_c q hq)) (generated_k1 q hq))
      intro e
      simp only [NFFull.eval,FullHead,ARow,LPrime,CRow,K1Row,I]
      omega
  | isolatedR b c =>
    have hb : (2*q+2≤b ∧ b≤3*q-1) ∧ 3*q+3≤c ∧ c≤4*q := hz
    have hcn : c≠4*q := hnot
    obtain ⟨t,ht,heq⟩ := beta_surjective q c hq (by omega)
    have htl : t≤2*q := by unfold P at ht; unfold beta at heq; split at heq <;> omega
    have ht' := ht
    unfold P at ht'
    unfold beta at heq
    apply generated_congr q (generated_join q (generated_join q (generated_join q (j134_five q b hq (by omega)) (generated_c q hq)) (generated_l q t t hq ht ht (by omega) htl)) (hLP))
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,LPrime,KRow,K1Row,K2Row,JRow,LRow,LNormal,I,beta]
    repeat first | omega | (simp_all <;> omega) | split


end LuRazThreeRow
