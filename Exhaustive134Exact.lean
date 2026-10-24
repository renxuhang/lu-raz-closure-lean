import Exhaustive134Normal

namespace LuRazThreeRow
open LuRazClosure LuRazParametric
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000
set_option linter.unusedSimpArgs false

theorem j134_five (q b : Nat) (hq : 4≤q) (hb : 2*q+2≤b ∧ b≤4*q-3) : Generated q (JRow 5 b) := by
  apply generated_j q 5 b hq
  unfold JReachable g
  split <;> omega

theorem retained134_generated (q : Nat) (hq : 4≤q) (z : NF134) (hz : Valid134 q z) : Generated q (z.eval q) := by
  have hL := generated_congr q (generated_row q (4*q-1) (by omega)) (fun e => last_source q e hq)
  cases z with
  | ej a =>
    have ha : a=5 := hz.2
    subst a
    apply generated_congr q (generated_join q (generated_join q
      (j134_five q (4*q-3) hq (by omega)) (generated_c q hq)) (generated_b q hq))
    intro e
    simp only [NF134.eval,T134,JRow,CRow,BRow,I]
    omega
  | aej a => exact False.elim hz.2
  | extra k => exact False.elim hz.2
  | cj b =>
    have hb : 2*q+2≤b ∧ b≤4*q-3 := hz.1.1
    apply generated_congr q (generated_join q (j134_five q b hq hz.1.1) (generated_c q hq))
    intro e
    simp only [NF134.eval,T134,JRow,CRow,I]
    omega
  | zj b =>
    apply generated_congr q (generated_join q (j134_five q b hq hz.1) hL)
    intro e
    have hb : 2*q+2≤b ∧ b≤4*q-3 := hz.1
    simp only [NF134.eval,T134,JRow,LPrime,I]
    omega
  | czj b =>
    have hb : 2*q+2≤b ∧ b≤3*q-1 := hz.1
    apply generated_congr q (generated_join q (generated_join q (j134_five q b hq (by omega)) (generated_c q hq)) hL)
    intro e
    simp only [NF134.eval,T134,JRow,CRow,LPrime,I]
    omega
  | zjb b =>
    have hb : 2*q+2≤b ∧ b≤3*q := hz.1
    apply generated_congr q (generated_join q (generated_join q (j134_five q b hq (by omega)) hL) (generated_b q hq))
    intro e
    simp only [NF134.eval,T134,JRow,BRow,LPrime,I]
    omega
  | cjb b =>
    have hb : 2*q+2≤b ∧ b≤3*q-1 := hz.1
    apply generated_congr q (generated_join q (generated_join q (j134_five q b hq (by omega)) (generated_c q hq)) (generated_b q hq))
    intro e
    simp only [NF134.eval,T134,JRow,CRow,BRow,I]
    omega

theorem fresh134_generated (q : Nat) (hq : 4≤q) (z : Fresh134) (hz : z.Valid q) : Generated q (z.eval q) := by
  have hL := generated_congr q (generated_row q (4*q-1) (by omega)) (fun e => last_source q e hq)
  have hZ := generated_congr q (generated_row q 2 (by omega)) (fun e => z_source q e hq)
  have hA := generated_congr q (generated_row q (4*q+2) (by omega)) (fun e => a_source q e hq)
  cases z with
  | lp =>
    apply generated_congr q (generated_join q hL hA)
    intro e
    simp only [Fresh134.eval,T134,LPrime,ARow,I]
    omega
  | lb =>
    apply generated_congr q (generated_join q (generated_join q hL hA) (generated_b q hq))
    intro e
    simp only [Fresh134.eval,T134,LPrime,ARow,BRow,I]
    omega
  | zz b =>
    have hb : 2*q+1≤b ∧ b≤4*q-3 := hz
    by_cases he : b=2*q+1
    · subst b
      apply generated_congr q (generated_join q hL hZ)
      intro e
      simp only [Fresh134.eval,T134,LPrime,ZPrime,I]
      omega
    · apply generated_congr q (generated_join q (j134_five q b hq (by omega)) hZ)
      intro e
      simp only [Fresh134.eval,T134,JRow,ZPrime,I]
      omega
  | cz b =>
    have hb : 2*q+2≤b ∧ b≤3*q-1 := hz
    apply generated_congr q (generated_join q (generated_join q (j134_five q b hq (by omega)) (generated_c q hq)) hZ)
    intro e
    simp only [Fresh134.eval,T134,JRow,CRow,ZPrime,I]
    omega

theorem fresh134_core (q : Nat) (hq : 4≤q) (z : Fresh134) (hz : z.Valid q) : Core134 (z.eval q) := by
  cases z <;> simp only [Fresh134.Valid] at hz <;>
    simp [Core134,Fresh134.eval,T134,BRow,I] <;> omega

theorem old134_end (q : Nat) (hq : 4≤q) (z : NF134) (hz : z.Valid q) :
    z.eval q (4*q-1) → z.eval q (4*q-2) := by
  cases z <;> simp only [NF134.Valid] at hz <;>
    simp only [NF134.eval,T134,ERow,ZRow,BRow,I] <;> simp_all <;> omega

theorem old134_prefix (q : Nat) (hq : 4≤q) (z : NF134) (hz : z.Valid q)
    (h5 : z.eval q 5) (hq3 : z.eval q (q+3)) (hh1 : z.eval q (2*q+1)) : z.eval q (2*q+2) := by
  cases z <;> simp only [NF134.Valid] at hz <;>
    simp only [NF134.eval,T134,ERow,ZRow,BRow,I] at h5 hq3 hh1 ⊢ <;> simp_all <;> omega

theorem fresh134_not_old (q : Nat) (hq : 4≤q) (z : Fresh134) (hz : z.Valid q) :
    ¬LuRazClosure.Generated q (z.eval q) := by
  intro hg
  obtain ⟨w,hw,he⟩ := (core134_closure_exact q hq _).mp ⟨hg,fresh134_core q hq z hz⟩
  have hend := old134_end q hq w hw
  have hpre := old134_prefix q hq w hw
  have hp : z.eval q 5 → z.eval q (q+3) → z.eval q (2*q+1) → z.eval q (2*q+2) := by
    rw [he _,he _,he _,he _]; exact hpre
  have hn : z.eval q (4*q-1) → z.eval q (4*q-2) := by
    rw [he _,he _]; exact hend
  cases z <;> simp only [Fresh134.Valid] at hz <;>
    simp only [Fresh134.eval,T134,BRow,I] at hp hn <;> simp_all <;> omega

theorem fresh134_unique (q : Nat) (hq : 4≤q) (z w : Fresh134) (hz : z.Valid q) (hw : w.Valid q)
    (he : ∀ e, z.eval q e ↔ w.eval q e) : z=w := by
  have hn1 := he (4*q-1)
  have hn2 := he (4*q-2)
  cases z <;> cases w
  case zz.zz a b =>
    have ha := he a; have hb := he b
    simp only [Fresh134.Valid] at hz hw
    simp only [Fresh134.eval,T134,I] at ha hb
    have hab : a=b := by omega
    rw [hab]
  case cz.cz a b =>
    have ha := he a; have hb := he b
    simp only [Fresh134.Valid] at hz hw
    simp only [Fresh134.eval,T134,I] at ha hb
    have hab : a=b := by omega
    rw [hab]
  case zz.cz a b =>
    have hr := he (3*q+1); have hb := he (b+1)
    simp only [Fresh134.Valid] at hz hw
    simp only [Fresh134.eval,T134,I] at hr hb
    simp_all <;> omega
  case cz.zz a b =>
    have hr := he (3*q+1); have ha := he (a+1)
    simp only [Fresh134.Valid] at hz hw
    simp only [Fresh134.eval,T134,I] at hr ha
    simp_all <;> omega
  all_goals try rfl
  all_goals simp only [Fresh134.Valid] at hz hw
  all_goals simp only [Fresh134.eval,T134,BRow,I] at hn1 hn2
  all_goals simp_all <;> omega

theorem normal134_generated (q : Nat) (hq : 4≤q) (z : Normal134) (hz : z.Valid q) : Generated q (z.eval q) := by
  cases z with
  | old z => exact retained134_generated q hq z hz
  | fresh z => exact fresh134_generated q hq z hz

theorem normal134_core (q : Nat) (hq : 4≤q) (z : Normal134) (hz : z.Valid q) : Core134 (z.eval q) := by
  cases z with
  | old z => exact NF134.core q hq z hz.1
  | fresh z => exact fresh134_core q hq z hz

theorem core134_exhaustive (q : Nat) (hq : 4≤q) (R : Nat → Prop) :
    Generated q R ∧ Core134 R ↔ ∃ z : Normal134, z.Valid q ∧ ∀ e, R e ↔ z.eval q e := by
  constructor
  · exact fun h => core134_normal q hq R h.1 h.2
  · rintro ⟨z,hz,he⟩
    refine ⟨generated_congr q (normal134_generated q hq z hz) (fun e => (he e).symm),?_⟩
    have hc := normal134_core q hq z hz
    unfold Core134 at *
    rw [he 1,he 2,he 3,he 4]
    exact hc

theorem normal134_unique (q : Nat) (hq : 4≤q) (z w : Normal134) (hz : z.Valid q) (hw : w.Valid q)
    (he : ∀ e, z.eval q e ↔ w.eval q e) : z=w := by
  cases z with
  | old z =>
    cases w with
    | old w => exact congrArg Normal134.old (NF134.unique q hq z w hz.1 hw.1 he)
    | fresh w =>
      exact False.elim (fresh134_not_old q hq w hw (LuRazClosure.generated_congr q
        (NF134.generated q hq z hz.1) he))
  | fresh z =>
    cases w with
    | old w =>
      exact False.elim (fresh134_not_old q hq z hz (LuRazClosure.generated_congr q
        (NF134.generated q hq w hw.1) (fun e => (he e).symm)))
    | fresh w => exact congrArg Normal134.fresh (fresh134_unique q hq z w hz hw he)

end LuRazThreeRow
