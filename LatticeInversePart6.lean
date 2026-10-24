import LatticeShapeDefs
namespace LuRazClosure.SourcePieces
set_option maxHeartbeats 100000
set_option linter.unusedVariables false
theorem p62_identify (q a b : Nat) (hq : 4≤q) (hd : p62Domain q a b) :
    identify q (.c134 (p62NF q a b))=(62,a,b) := by
  simp only [p62Domain] at hd
  simp [identify,invNF134,p62NF]
  all_goals repeat first | (simp_all <;> omega) | split | congr 1
theorem p63_identify (q a b : Nat) (hq : 4≤q) (hd : p63Domain q a b) :
    identify q (.c134 (p63NF q a b))=(63,a,b) := by
  simp only [p63Domain] at hd
  simp [identify,invNF134,p63NF]
  all_goals repeat first | (simp_all <;> omega) | split | congr 1
theorem p64_identify (q a b : Nat) (hq : 4≤q) (hd : p64Domain q a b) :
    identify q (.c134 (p64NF q a b))=(64,a,b) := by
  simp only [p64Domain] at hd
  simp [identify,invNF134,p64NF]
  all_goals repeat first | (simp_all <;> omega) | split | congr 1
theorem p65_identify (q a b : Nat) (hq : 4≤q) (hd : p65Domain q a b) :
    identify q (.c134 (p65NF q a b))=(65,a,b) := by
  simp only [p65Domain] at hd
  simp [identify,invNF134,p65NF]
  all_goals repeat first | (simp_all <;> omega) | split | congr 1
theorem p66_identify (q a b : Nat) (hq : 4≤q) (hd : p66Domain q a b) :
    identify q (.c134 (p66NF q a b))=(66,a,b) := by
  simp only [p66Domain] at hd
  simp [identify,invNF134,p66NF]
  all_goals repeat first | (simp_all <;> omega) | split | congr 1
theorem p67_identify (q a b : Nat) (hq : 4≤q) (hd : p67Domain q a b) :
    identify q (.c134 (p67NF q a b))=(67,a,b) := by
  simp only [p67Domain] at hd
  simp [identify,invNF134,p67NF]
  all_goals repeat first | (simp_all <;> omega) | split | congr 1
theorem p68_identify (q a b : Nat) (hq : 4≤q) (hd : p68Domain q a b) :
    identify q (.c134 (p68NF q a b))=(68,a,b) := by
  simp only [p68Domain] at hd
  simp [identify,invNF134,p68NF]
  all_goals repeat first | (simp_all <;> omega) | split | congr 1
theorem p69_identify (q a b : Nat) (hq : 4≤q) (hd : p69Domain q a b) :
    identify q (.c134 (p69NF q a b))=(69,a,b) := by
  simp only [p69Domain] at hd
  simp [identify,invNF134,p69NF]
  all_goals repeat first | (simp_all <;> omega) | split | congr 1
theorem p70_identify (q a b : Nat) (hq : 4≤q) (hd : p70Domain q a b) :
    identify q (.c134 (p70NF q a b))=(70,a,b) := by
  simp only [p70Domain] at hd
  simp [identify,invNF134,p70NF]
  all_goals repeat first | (simp_all <;> omega) | split | congr 1
theorem p71_identify (q a b : Nat) (hq : 4≤q) (hd : p71Domain q a b) :
    identify q (.c234 (p71NF q a b))=(71,a,b) := by
  simp only [p71Domain] at hd
  simp [identify,invNF234,p71NF]
  all_goals repeat first | (simp_all <;> omega) | split | congr 1
#print axioms p62_identify
#print axioms p63_identify
#print axioms p64_identify
#print axioms p65_identify
#print axioms p66_identify
#print axioms p67_identify
#print axioms p68_identify
#print axioms p69_identify
#print axioms p70_identify
#print axioms p71_identify
end LuRazClosure.SourcePieces
