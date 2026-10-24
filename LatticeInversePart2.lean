import LatticeShapeDefs
namespace LuRazClosure.SourcePieces
set_option maxHeartbeats 100000
set_option linter.unusedVariables false
theorem p21_identify (q a b : Nat) (hq : 4≤q) (hd : p21Domain q a b) :
    identify q (.c23 (p21NF q a b))=(21,a,b) := by
  simp only [p21Domain] at hd
  simp [identify,invNF23,p21NF]
  all_goals repeat first | (simp_all <;> omega) | split | congr 1
theorem p22_identify (q a b : Nat) (hq : 4≤q) (hd : p22Domain q a b) :
    identify q (.c23 (p22NF q a b))=(22,a,b) := by
  simp only [p22Domain] at hd
  simp [identify,invNF23,p22NF]
  all_goals repeat first | (simp_all <;> omega) | split | congr 1
theorem p23_identify (q a b : Nat) (hq : 4≤q) (hd : p23Domain q a b) :
    identify q (.c23 (p23NF q a b))=(23,a,b) := by
  simp only [p23Domain] at hd
  simp [identify,invNF23,p23NF]
  all_goals repeat first | (simp_all <;> omega) | split | congr 1
theorem p24_identify (q a b : Nat) (hq : 4≤q) (hd : p24Domain q a b) :
    identify q (.c123 (p24NF q a b))=(24,a,b) := by
  simp only [p24Domain] at hd
  simp [identify,invNF123,p24NF]
  all_goals repeat first | (simp_all <;> omega) | split | congr 1
theorem p25_identify (q a b : Nat) (hq : 4≤q) (hd : p25Domain q a b) :
    identify q (.c123 (p25NF q a b))=(25,a,b) := by
  simp only [p25Domain] at hd
  simp [identify,invNF123,p25NF]
  all_goals repeat first | (simp_all <;> omega) | split | congr 1
theorem p26_identify (q a b : Nat) (hq : 4≤q) (hd : p26Domain q a b) :
    identify q (.c123 (p26NF q a b))=(26,a,b) := by
  simp only [p26Domain] at hd
  simp [identify,invNF123,p26NF]
  all_goals repeat first | (simp_all <;> omega) | split | congr 1
theorem p28_identify (q a b : Nat) (hq : 4≤q) (hd : p28Domain q a b) :
    identify q (.c123 (p28NF q a b))=(28,a,b) := by
  simp only [p28Domain] at hd
  simp [identify,invNF123,p28NF]
  all_goals repeat first | (simp_all <;> omega) | split | congr 1
theorem p29_identify (q a b : Nat) (hq : 4≤q) (hd : p29Domain q a b) :
    identify q (.c123 (p29NF q a b))=(29,a,b) := by
  simp only [p29Domain] at hd
  simp [identify,invNF123,p29NF]
  all_goals repeat first | (simp_all <;> omega) | split | congr 1
theorem p30_identify (q a b : Nat) (hq : 4≤q) (hd : p30Domain q a b) :
    identify q (.c123 (p30NF q a b))=(30,a,b) := by
  simp only [p30Domain] at hd
  simp [identify,invNF123,p30NF]
  all_goals repeat first | (simp_all <;> omega) | split | congr 1
theorem p31_identify (q a b : Nat) (hq : 4≤q) (hd : p31Domain q a b) :
    identify q (.c123 (p31NF q a b))=(31,a,b) := by
  simp only [p31Domain] at hd
  simp [identify,invNF123,p31NF]
  all_goals repeat first | (simp_all <;> omega) | split | congr 1
#print axioms p21_identify
#print axioms p22_identify
#print axioms p23_identify
#print axioms p24_identify
#print axioms p25_identify
#print axioms p26_identify
#print axioms p28_identify
#print axioms p29_identify
#print axioms p30_identify
#print axioms p31_identify
end LuRazClosure.SourcePieces
