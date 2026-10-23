import LuRazCore14

namespace LuRazClosure

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

inductive NF14 where
  | base (a b : Nat)
  | agap (a b : Nat)
  | bgap (a b : Nat)
  | joined (a : Nat)
  | doubleGap
  | ajoined (a : Nat)
  deriving DecidableEq, Repr

def NF14.Valid (q : Nat) : NF14 → Prop
  | .base a b => JReachable q a b
  | .agap a b => JReachable q a b ∧ q+4 ≤ a
  | .bgap a b => JReachable q a b ∧ b ≤ 3*q
  | .joined a => 5 ≤ a ∧ a ≤ 2*q+1
  | .doubleGap => True
  | .ajoined a => q+4 ≤ a ∧ a ≤ 2*q+1

def NF14.eval (q : Nat) : NF14 → Nat → Prop
  | .base a b => JRow a b
  | .agap a b => fun e => JRow a b e ∨ ARow q e
  | .bgap a b => fun e => JRow a b e ∨ BRow q e
  | .joined a => JRow a (4*q)
  | .doubleGap => fun e => JRow (q+4) (3*q) e ∨ ARow q e ∨ BRow q e
  | .ajoined a => fun e => JRow a (4*q) e ∨ ARow q e

theorem J_prefix_reachable (q b : Nat) (hq : 4 ≤ q)
    (hb : 2*q+2 ≤ b ∧ b ≤ 4*q-3) : JReachable q 5 b := by
  unfold JReachable g
  split <;> omega

theorem J_max_reachable (q a : Nat) (hq : 4 ≤ q)
    (ha : 5 ≤ a ∧ a ≤ 2*q+1) : JReachable q a (4*q-3) := by
  have hg := g_bounds q a hq ha
  unfold JReachable
  omega

theorem J_double_reachable (q : Nat) (hq : 4 ≤ q) : JReachable q (q+4) (3*q) := by
  unfold JReachable g
  split <;> omega

theorem mixed14_normal (q a b : Nat) (hq : 4 ≤ q)
    (hab : JReachable q a b) (u v : Prop) :
    ∃ z : NF14, z.Valid q ∧ ∀ e, Mixed14 q a b u v e ↔ z.eval q e := by
  classical
  have hb : 2*q+2 ≤ b ∧ b ≤ 4*q-3 := ⟨hab.2.2.1,hab.2.2.2.1⟩
  have hab' := hab
  unfold JReachable at hab'
  by_cases hu : u <;> by_cases hv : v
  · by_cases ha : a ≤ q+3
    · by_cases hbr : b ≤ 3*q
      · refine ⟨.bgap 5 b,⟨J_prefix_reachable q b hq hb,hbr⟩,?_⟩
        intro e
        simp only [Mixed14,hu,hv,true_and,NF14.eval]
        unfold JRow ARow BRow I
        omega
      · refine ⟨.joined 5,by unfold NF14.Valid; omega,?_⟩
        intro e
        simp only [Mixed14,hu,hv,true_and,NF14.eval]
        unfold JRow ARow BRow I
        omega
    · by_cases hbr : b ≤ 3*q
      · have heq : a=q+4 ∧ b=3*q := by
          unfold g at hab'
          split at hab' <;> omega
        refine ⟨.doubleGap,True.intro,?_⟩
        intro e
        simp only [Mixed14,hu,hv,true_and,NF14.eval,heq.1,heq.2]
      · refine ⟨.ajoined a,by unfold NF14.Valid; omega,?_⟩
        intro e
        simp only [Mixed14,hu,hv,true_and,NF14.eval]
        unfold JRow ARow BRow I
        omega
  · by_cases ha : a ≤ q+3
    · refine ⟨.base 5 b,J_prefix_reachable q b hq hb,?_⟩
      intro e
      simp only [Mixed14,hu,hv,true_and,false_and,or_false,NF14.eval]
      unfold JRow ARow I
      omega
    · refine ⟨.agap a b,⟨hab,by omega⟩,?_⟩
      intro e
      simp only [Mixed14,hu,hv,true_and,false_and,or_false,NF14.eval]
  · by_cases hbr : b ≤ 3*q
    · refine ⟨.bgap a b,⟨hab,hbr⟩,?_⟩
      intro e
      simp only [Mixed14,hu,hv,true_and,false_and,false_or,NF14.eval]
    · refine ⟨.joined a,⟨hab'.1,hab'.2.1⟩,?_⟩
      intro e
      simp only [Mixed14,hu,hv,true_and,false_and,false_or,NF14.eval]
      unfold JRow BRow I
      omega
  · refine ⟨.base a b,hab,?_⟩
    intro e
    simp only [Mixed14,hu,hv,false_and,or_false,NF14.eval]

theorem NF14.generated (q : Nat) (hq : 4 ≤ q) (z : NF14) (hz : z.Valid q) :
    Generated q (z.eval q) := by
  cases z with
  | base a b => exact generated_J q a b hq hz
  | agap a b => exact generated_join q (generated_J q a b hq hz.1) (generated_A q hq)
  | bgap a b => exact generated_join q (generated_J q a b hq hz.1) (generated_B q hq)
  | joined a =>
    have ha : 5 ≤ a ∧ a ≤ 2*q+1 := hz
    have hab := J_max_reachable q a hq ha
    apply generated_congr q (mixed14_generated q a (4*q-3) hq hab False True)
    intro e
    change Mixed14 q a (4*q-3) False True e ↔ JRow a (4*q) e
    unfold Mixed14 JRow BRow I
    simp only [true_and,false_and,or_false,false_or]
    omega
  | doubleGap =>
    exact generated_congr q (mixed14_generated q (q+4) (3*q) hq (J_double_reachable q hq) True True)
      (fun _ => by simp only [Mixed14,NF14.eval,true_and])
  | ajoined a =>
    have ha : 5 ≤ a ∧ a ≤ 2*q+1 := by unfold NF14.Valid at hz; omega
    have hab := J_max_reachable q a hq ha
    apply generated_congr q (mixed14_generated q a (4*q-3) hq hab True True)
    intro e
    change Mixed14 q a (4*q-3) True True e ↔ (JRow a (4*q) e ∨ ARow q e)
    unfold Mixed14 JRow ARow BRow I
    simp only [true_and,false_and,or_false,false_or]
    omega

theorem NF14.core (q : Nat) (hq : 4 ≤ q) (z : NF14) (hz : z.Valid q) :
    Core14 (z.eval q) := by
  cases z <;> unfold NF14.Valid JReachable at hz <;>
    unfold Core14 NF14.eval JRow ARow BRow I <;> omega

/-- This equivalence refers to the closure of ALL 4q+3 source rows. -/
theorem core14_closure_exact (q : Nat) (hq : 4 ≤ q) (R : Nat → Prop) :
    (Generated q R ∧ Core14 R) ↔
      ∃ z : NF14, z.Valid q ∧ ∀ e, R e ↔ z.eval q e := by
  constructor
  · rintro ⟨hgen,hcore⟩
    obtain ⟨a,b,hab,u,v,heq⟩ := full_core14_mixed q hq R hgen hcore
    obtain ⟨z,hz,hzn⟩ := mixed14_normal q a b hq hab u v
    exact ⟨z,hz,fun e => (heq e).trans (hzn e)⟩
  · rintro ⟨z,hz,heq⟩
    refine ⟨generated_congr q (NF14.generated q hq z hz) (fun e => (heq e).symm),?_⟩
    have hc := NF14.core q hq z hz
    exact ⟨(heq 1).mpr hc.1,fun h => hc.2.1 ((heq 2).mp h),
      fun h => hc.2.2.1 ((heq 3).mp h),(heq 4).mpr hc.2.2.2⟩

end LuRazClosure
