import SixRowFullGenerated
import SixRowFullNecessary

namespace LuRazSixRowClosure
open LuRazClosure LuRazParametric
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

theorem full_retained_generated (q : Nat) (hq : 4≤q) (z : NFFull)
    (hzs : FullKeep q z) : Generated q (z.eval q) := by
  have hz := hzs.1
  have hnot := hzs.2.1
  have hkeep := hzs.2.2
  have hp4 : P q 4 := by unfold P; omega
  have hpe : P q (q+3) := by unfold P; omega
  cases z with
  | noNInterval k =>
    have hk : k<2 := hz
    by_cases he : k=0
    · subst k
      apply generated_congr q (generated_join q (full_gen_Last q hq) (full_gen_K1 q hq))
      intro e
      simp only [NFFull.eval,FullHead,ARow,LuRazClosure.BRow,FullLast,FullC,FullE,FullM,K1Row,JRow,LRow,LNormal,I,beta]
      repeat first | omega | (simp_all <;> omega) | split
    · have hk1 : k=1 := by omega
      subst k
      apply generated_congr q (generated_join q (generated_join q (full_gen_Last q hq) (full_gen_K1 q hq)) (full_gen_C q hq))
      intro e
      simp only [NFFull.eval,FullHead,ARow,LuRazClosure.BRow,FullLast,FullC,FullE,FullM,K1Row,JRow,LRow,LNormal,I,beta]
      repeat first | omega | (simp_all <;> omega) | split
  | noNMJRight b =>
    have hb : 2*q+2≤b ∧ b≤3*q := hz
    apply generated_congr q (generated_join q (full_gen_L q (q+3) (q+3) hq hpe hpe (by omega) (by omega)) (full_gen_Jfive q b hq (by omega)))
    intro e
    simp only [NFFull.eval,FullHead,ARow,LuRazClosure.BRow,FullLast,FullC,FullE,FullM,K1Row,JRow,LRow,LNormal,I,beta]
    repeat first | omega | (simp_all <;> omega) | split
  | noNMJLeft a =>
    have ha : q+5≤a ∧ a≤2*q+1 := hz
    apply generated_congr q (generated_join q (full_gen_L q (q+3) (q+3) hq hpe hpe (by omega) (by omega)) (full_gen_J q a (4*q-3) hq (J_max_reachable q a hq (by omega))))
    intro e
    simp only [NFFull.eval,FullHead,ARow,LuRazClosure.BRow,FullLast,FullC,FullE,FullM,K1Row,JRow,LRow,LNormal,I,beta]
    repeat first | omega | (simp_all <;> omega) | split
  | noNMK k =>
    have hk : k=0 := hkeep
    subst k
    apply generated_congr q (generated_join q (generated_join q (full_gen_A q hq) (full_gen_L q (q+3) (q+3) hq hpe hpe (by omega) (by omega))) (full_gen_K1 q hq))
    intro e
    simp only [NFFull.eval,FullHead,ARow,LuRazClosure.BRow,FullLast,FullC,FullE,FullM,K1Row,JRow,LRow,LNormal,I,beta]
    repeat first | omega | (simp_all <;> omega) | split
  | noNCMJ b =>
    have hb : 2*q+2≤b ∧ b≤3*q-1 := hz
    apply generated_congr q (generated_join q (generated_join q (full_gen_C q hq) (full_gen_L q (q+3) (q+3) hq hpe hpe (by omega) (by omega))) (full_gen_Jfive q b hq (by omega)))
    intro e
    simp only [NFFull.eval,FullHead,ARow,LuRazClosure.BRow,FullLast,FullC,FullE,FullM,K1Row,JRow,LRow,LNormal,I,beta]
    repeat first | omega | (simp_all <;> omega) | split
  | noH1Short p k =>
    have hpv : (4≤p ∧ p≤2*q) ∧ k<2 := hz
    have hpk : q+2≤p := hkeep
    by_cases hk : k=0
    · subst k
      by_cases he : p=q+2
      · subst p
        apply generated_congr q (generated_join q (generated_join q (full_gen_A q hq) (full_gen_E q hq)) (full_gen_K1 q hq))
        intro e
        simp only [NFFull.eval,FullHead,ARow,LuRazClosure.BRow,FullLast,FullC,FullE,FullM,K1Row,JRow,LRow,LNormal,I,beta]
        repeat first | omega | (simp_all <;> omega) | split
      · have hp : P q p := by unfold P; omega
        apply generated_congr q (generated_join q (generated_join q (generated_join q (full_gen_A q hq) (full_gen_E q hq)) (full_gen_K1 q hq)) (full_gen_L q p p hq hp hp (by omega) (by omega)))
        intro e
        simp only [NFFull.eval,FullHead,ARow,LuRazClosure.BRow,FullLast,FullC,FullE,FullM,K1Row,JRow,LRow,LNormal,I,beta]
        repeat first | omega | (simp_all <;> omega) | split
    · have hk1 : k=1 := by omega
      subst k
      by_cases he : p=q+2
      · subst p
        apply generated_congr q (generated_join q (generated_join q (full_gen_A q hq) (full_gen_E q hq)) (full_gen_M q hq))
        intro e
        simp only [NFFull.eval,FullHead,ARow,LuRazClosure.BRow,FullLast,FullC,FullE,FullM,K1Row,JRow,LRow,LNormal,I,beta]
        repeat first | omega | (simp_all <;> omega) | split
      · have hp : P q p := by unfold P; omega
        apply generated_congr q (generated_join q (generated_join q (generated_join q (full_gen_A q hq) (full_gen_E q hq)) (full_gen_M q hq)) (full_gen_L q p p hq hp hp (by omega) (by omega)))
        intro e
        simp only [NFFull.eval,FullHead,ARow,LuRazClosure.BRow,FullLast,FullC,FullE,FullM,K1Row,JRow,LRow,LNormal,I,beta]
        repeat first | omega | (simp_all <;> omega) | split
  | noH1ZL a => exact False.elim (hnot True.intro)
  | noH1Exception => exact False.elim (hnot True.intro)
  | noH2 a =>
    have ha : a=2*q+3 := hkeep
    subst a
    apply generated_congr q (generated_join q (generated_join q (generated_join q (full_gen_A q hq) (full_gen_C q hq)) (full_gen_E q hq)) (full_gen_M q hq))
    intro e
    simp only [NFFull.eval,FullHead,ARow,LuRazClosure.BRow,FullLast,FullC,FullE,FullM,K1Row,JRow,LRow,LNormal,I,beta]
    repeat first | omega | (simp_all <;> omega) | split
  | noFive a =>
    have ha : 6≤a ∧ a≤2*q+1 := hz
    apply generated_congr q (generated_join q (full_gen_J q a (4*q-3) hq (J_max_reachable q a hq (by omega))) (full_gen_L q 4 4 hq hp4 hp4 (by omega) (by omega)))
    intro e
    simp only [NFFull.eval,FullHead,ARow,LuRazClosure.BRow,FullLast,FullC,FullE,FullM,K1Row,JRow,LRow,LNormal,I,beta]
    repeat first | omega | (simp_all <;> omega) | split
  | leftGap p a =>
    have hb : (5≤p ∧ p≤2*q-1) ∧ p+2≤a ∧ a≤2*q+1 := hz
    by_cases he : p=q+2
    · subst p
      apply generated_congr q (generated_join q (generated_join q (full_gen_A q hq) (full_gen_L q 4 4 hq hp4 hp4 (by omega) (by omega))) (full_gen_J q a (4*q-3) hq (J_max_reachable q a hq (by omega))))
      intro e
      simp only [NFFull.eval,FullHead,ARow,LuRazClosure.BRow,FullLast,FullC,FullE,FullM,K1Row,JRow,LRow,LNormal,I,beta]
      repeat first | omega | (simp_all <;> omega) | split
    · have hp : P q p := by unfold P; omega
      apply generated_congr q (generated_join q (generated_join q (full_gen_L q p p hq hp hp (by omega) (by omega)) (full_gen_J q a (4*q-3) hq (J_max_reachable q a hq (by omega)))) (full_gen_B q hq))
      intro e
      simp only [NFFull.eval,FullHead,ARow,LuRazClosure.BRow,FullLast,FullC,FullE,FullM,K1Row,JRow,LRow,LNormal,I,beta]
      repeat first | omega | (simp_all <;> omega) | split
  | full =>
    apply generated_congr q (generated_row q 0 (by omega))
    intro e
    rw [full_unchanged q 0 e (by unfold FullChanged; omega),row_case_0 q 0 e (by omega) rfl]
    simp only [NFFull.eval,FullHead,I]
    omega
  | rightGap b c =>
    have hb : (2*q+2≤b ∧ b≤4*q-2) ∧ b+2≤c ∧ c≤4*q := hz
    by_cases hbb : b≤4*q-3
    · have hcn : c≠4*q := by intro hc; exact hnot ⟨hc,hbb⟩
      obtain ⟨t,ht,heq⟩ := beta_surjective q c hq (by omega)
      have htl : t≤2*q := by unfold P at ht; unfold beta at heq; split at heq <;> omega
      have htP := ht
      unfold P at htP
      by_cases hte : t=q+3
      · have heq' := heq
        unfold beta at heq'
        split at heq' <;> try omega
        apply generated_congr q (generated_join q (generated_join q (full_gen_Jfive q b hq (by omega)) (full_gen_L q t t hq ht ht (by omega) htl)) (full_gen_B q hq))
        intro e
        simp only [NFFull.eval,FullHead,ARow,LuRazClosure.BRow,FullLast,FullC,FullE,FullM,K1Row,JRow,LRow,LNormal,I,beta]
        repeat first | omega | (simp_all <;> omega) | split
      · have heq' := heq
        unfold beta at heq'
        split at heq'
        apply generated_congr q (generated_join q (full_gen_Jfive q b hq (by omega)) (full_gen_L q t t hq ht ht (by omega) htl))
        intro e
        simp only [NFFull.eval,FullHead,ARow,LuRazClosure.BRow,FullLast,FullC,FullE,FullM,K1Row,JRow,LRow,LNormal,I,beta]
        repeat first | omega | (simp_all <;> omega) | split
        apply generated_congr q (generated_join q (full_gen_Jfive q b hq (by omega)) (full_gen_L q t t hq ht ht (by omega) htl))
        intro e
        simp only [NFFull.eval,FullHead,ARow,LuRazClosure.BRow,FullLast,FullC,FullE,FullM,K1Row,JRow,LRow,LNormal,I,beta]
        repeat first | omega | (simp_all <;> omega) | split
    · have hbe : b=4*q-2 := by omega
      have hce : c=4*q := by omega
      subst b c
      apply generated_congr q (generated_join q (generated_join q (full_gen_Last q hq) (full_gen_K1 q hq)) (full_gen_M q hq))
      intro e
      simp only [NFFull.eval,FullHead,ARow,LuRazClosure.BRow,FullLast,FullC,FullE,FullM,K1Row,JRow,LRow,LNormal,I,beta]
      repeat first | omega | (simp_all <;> omega) | split
  | isolatedR b c =>
    have hb : (2*q+2≤b ∧ b≤3*q-1) ∧ 3*q+3≤c ∧ c≤4*q := hz
    have hcn : c≠4*q := hnot
    obtain ⟨t,ht,heq⟩ := beta_surjective q c hq (by omega)
    have htl : t≤2*q := by unfold P at ht; unfold beta at heq; split at heq <;> omega
    have htP := ht
    unfold P at htP
    have hte : t≠q+3 := by intro h; subst t; unfold beta at heq; split at heq <;> omega
    unfold beta at heq
    split at heq
    apply generated_congr q (generated_join q (generated_join q (full_gen_Jfive q b hq (by omega)) (full_gen_L q t t hq ht ht (by omega) htl)) (full_gen_C q hq))
    intro e
    simp only [NFFull.eval,FullHead,ARow,LuRazClosure.BRow,FullLast,FullC,FullE,FullM,K1Row,JRow,LRow,LNormal,I,beta]
    repeat first | omega | (simp_all <;> omega) | split
    apply generated_congr q (generated_join q (generated_join q (full_gen_Jfive q b hq (by omega)) (full_gen_L q t t hq ht ht (by omega) htl)) (full_gen_C q hq))
    intro e
    simp only [NFFull.eval,FullHead,ARow,LuRazClosure.BRow,FullLast,FullC,FullE,FullM,K1Row,JRow,LRow,LNormal,I,beta]
    repeat first | omega | (simp_all <;> omega) | split

end LuRazSixRowClosure
