import LatticeShapeDefs
namespace LuRazClosure.SourcePieces
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
theorem inverse_valid_NF14 (q : Nat) (hq : 4≤q) (z : NF14) (hz : z.Valid q) :
    let p := invNF14 q z
    Domain q p.1 p.2.1 p.2.2 ∧ decode q p.1 p.2.1 p.2.2=.c14 z := by
  cases z with
  | base a b =>
    skip
    by_cases h : a≤q+3
    · simp only [NF14.Valid,JReachable,g,ite_eq_left h] at hz
      simp [invNF14,h,Domain,decode,p39Domain,p39NF]; omega
    · simp only [NF14.Valid,JReachable,g,ite_eq_right h] at hz
      simp [invNF14,h,Domain,decode,p40Domain,p40NF]; omega
  | agap a b =>
    have ha : q+4≤a := hz.2
    have h : ¬a≤q+3 := by omega
    simp only [NF14.Valid,JReachable,g,ite_eq_right h] at hz
    simp_all [invNF14,Domain,decode,p41Domain,p41NF]
    omega
  | bgap a b =>
    skip
    by_cases h : a≤q+3
    · simp only [NF14.Valid,JReachable,g,ite_eq_left h] at hz
      simp [invNF14,h,Domain,decode,p42Domain,p42NF]; omega
    · simp only [NF14.Valid,JReachable,g,ite_eq_right h] at hz
      simp [invNF14,h,Domain,decode,p43Domain,p43NF]; omega
  | joined a =>
    simp_all [NF14.Valid,invNF14,Domain,decode,p44Domain,p44NF]
    omega
  | doubleGap =>
    simp [invNF14,Domain,decode,p45Domain,p45NF]
  | ajoined a =>
    simp_all [NF14.Valid,invNF14,Domain,decode,p46Domain,p46NF]
    omega
#print axioms inverse_valid_NF14
end LuRazClosure.SourcePieces
