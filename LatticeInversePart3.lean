import LatticeShapeDefs
namespace LuRazClosure.SourcePieces
set_option maxHeartbeats 100000
set_option linter.unusedVariables false
theorem p32_identify (q a b : Nat) (hq : 4≤q) (hd : p32Domain q a b) :
    identify q (.c123 (p32NF q a b))=(32,a,b) := by
  simp only [p32Domain] at hd
  simp [identify,invNF123,p32NF]
  all_goals repeat first | (simp_all <;> omega) | split | congr 1
theorem p33_identify (q a b : Nat) (hq : 4≤q) (hd : p33Domain q a b) :
    identify q (.c123 (p33NF q a b))=(33,a,b) := by
  simp only [p33Domain] at hd
  simp [identify,invNF123,p33NF]
  all_goals repeat first | (simp_all <;> omega) | split | congr 1
theorem p34_identify (q a b : Nat) (hq : 4≤q) (hd : p34Domain q a b) :
    identify q (.c123 (p34NF q a b))=(34,a,b) := by
  simp only [p34Domain] at hd
  simp [identify,invNF123,p34NF]
  all_goals repeat first | (simp_all <;> omega) | split | congr 1
theorem p35_identify (q a b : Nat) (hq : 4≤q) (hd : p35Domain q a b) :
    identify q (.c123 (p35NF q a b))=(35,a,b) := by
  simp only [p35Domain] at hd
  simp [identify,invNF123,p35NF]
  all_goals repeat first | (simp_all <;> omega) | split | congr 1
theorem p36_identify (q a b : Nat) (hq : 4≤q) (hd : p36Domain q a b) :
    identify q (.c123 (p36NF q a b))=(36,a,b) := by
  simp only [p36Domain] at hd
  simp [identify,invNF123,p36NF]
  all_goals repeat first | (simp_all <;> omega) | split | congr 1
theorem p37_identify (q a b : Nat) (hq : 4≤q) (hd : p37Domain q a b) :
    identify q (.c123 (p37NF q a b))=(37,a,b) := by
  simp only [p37Domain] at hd
  simp [identify,invNF123,p37NF]
  all_goals repeat first | (simp_all <;> omega) | split | congr 1
theorem p38_identify (q a b : Nat) (hq : 4≤q) (hd : p38Domain q a b) :
    identify q (.c123 (p38NF q a b))=(38,a,b) := by
  simp only [p38Domain] at hd
  simp [identify,invNF123,p38NF]
  all_goals repeat first | (simp_all <;> omega) | split | congr 1
theorem p39_identify (q a b : Nat) (hq : 4≤q) (hd : p39Domain q a b) :
    identify q (.c14 (p39NF q a b))=(39,a,b) := by
  simp only [p39Domain] at hd
  simp [identify,invNF14,p39NF]
  all_goals repeat first | (simp_all <;> omega) | split | congr 1
theorem p40_identify (q a b : Nat) (hq : 4≤q) (hd : p40Domain q a b) :
    identify q (.c14 (p40NF q a b))=(40,a,b) := by
  simp only [p40Domain] at hd
  simp [identify,invNF14,p40NF]
  all_goals repeat first | (simp_all <;> omega) | split | congr 1
theorem p41_identify (q a b : Nat) (hq : 4≤q) (hd : p41Domain q a b) :
    identify q (.c14 (p41NF q a b))=(41,a,b) := by
  simp only [p41Domain] at hd
  simp [identify,invNF14,p41NF]
  all_goals repeat first | (simp_all <;> omega) | split | congr 1
#print axioms p32_identify
#print axioms p33_identify
#print axioms p34_identify
#print axioms p35_identify
#print axioms p36_identify
#print axioms p37_identify
#print axioms p38_identify
#print axioms p39_identify
#print axioms p40_identify
#print axioms p41_identify
end LuRazClosure.SourcePieces
