import LatticeShapeDefs
namespace LuRazClosure.SourcePieces
set_option maxHeartbeats 50000
theorem p10_identify (q a b : Nat) (hq : 4≤q) (hd : p10Domain q a b) :
    identify q (.small (p10NF q a b))=(10,a,b) := by
  simp only [p10Domain] at hd
  simp only [identify,invNFSmall,p10NF]
  repeat first | rfl | omega | split | congr 1
theorem p11_identify (q a b : Nat) (hq : 4≤q) (hd : p11Domain q a b) :
    identify q (.small (p11NF q a b))=(11,a,b) := by
  simp only [p11Domain] at hd
  simp only [identify,invNFSmall,p11NF]
  repeat first | rfl | omega | split | congr 1
theorem p12_identify (q a b : Nat) (hq : 4≤q) (hd : p12Domain q a b) :
    identify q (.c23 (p12NF q a b))=(12,a,b) := by
  simp only [p12Domain] at hd
  simp only [identify,invNF23,p12NF]
  repeat first | rfl | omega | split | congr 1
theorem p13_identify (q a b : Nat) (hq : 4≤q) (hd : p13Domain q a b) :
    identify q (.c23 (p13NF q a b))=(13,a,b) := by
  simp only [p13Domain] at hd
  simp only [identify,invNF23,p13NF]
  repeat first | rfl | omega | split | congr 1
theorem p14_identify (q a b : Nat) (hq : 4≤q) (hd : p14Domain q a b) :
    identify q (.c23 (p14NF q a b))=(14,a,b) := by
  simp only [p14Domain] at hd
  simp only [identify,invNF23,p14NF]
  repeat first | rfl | omega | split | congr 1
theorem p15_identify (q a b : Nat) (hq : 4≤q) (hd : p15Domain q a b) :
    identify q (.c23 (p15NF q a b))=(15,a,b) := by
  simp only [p15Domain] at hd
  simp only [identify,invNF23,p15NF]
  repeat first | rfl | omega | split | congr 1
theorem p17_identify (q a b : Nat) (hq : 4≤q) (hd : p17Domain q a b) :
    identify q (.c23 (p17NF q a b))=(17,a,b) := by
  simp only [p17Domain] at hd
  simp only [identify,invNF23,p17NF]
  repeat first | rfl | omega | split | congr 1
theorem p18_identify (q a b : Nat) (hq : 4≤q) (hd : p18Domain q a b) :
    identify q (.c23 (p18NF q a b))=(18,a,b) := by
  simp only [p18Domain] at hd
  simp only [identify,invNF23,p18NF]
  repeat first | rfl | omega | split | congr 1
theorem p19_identify (q a b : Nat) (hq : 4≤q) (hd : p19Domain q a b) :
    identify q (.c23 (p19NF q a b))=(19,a,b) := by
  simp only [p19Domain] at hd
  simp only [identify,invNF23,p19NF]
  repeat first | rfl | omega | split | congr 1
theorem p20_identify (q a b : Nat) (hq : 4≤q) (hd : p20Domain q a b) :
    identify q (.c23 (p20NF q a b))=(20,a,b) := by
  simp only [p20Domain] at hd
  simp only [identify,invNF23,p20NF]
  repeat first | rfl | omega | split | congr 1
#print axioms p10_identify
#print axioms p11_identify
#print axioms p12_identify
#print axioms p13_identify
#print axioms p14_identify
#print axioms p15_identify
#print axioms p17_identify
#print axioms p18_identify
#print axioms p19_identify
#print axioms p20_identify
end LuRazClosure.SourcePieces
