import LatticeShapeDefs
namespace LuRazClosure.SourcePieces
set_option maxHeartbeats 50000
theorem p42_identify (q a b : Nat) (hq : 4≤q) (hd : p42Domain q a b) :
    identify q (.c14 (p42NF q a b))=(42,a,b) := by
  simp only [p42Domain] at hd
  simp only [identify,invNF14,p42NF]
  repeat first | rfl | omega | split | congr 1
theorem p43_identify (q a b : Nat) (hq : 4≤q) (hd : p43Domain q a b) :
    identify q (.c14 (p43NF q a b))=(43,a,b) := by
  simp only [p43Domain] at hd
  simp only [identify,invNF14,p43NF]
  repeat first | rfl | omega | split | congr 1
theorem p44_identify (q a b : Nat) (hq : 4≤q) (hd : p44Domain q a b) :
    identify q (.c14 (p44NF q a b))=(44,a,b) := by
  simp only [p44Domain] at hd
  simp only [identify,invNF14,p44NF]
  repeat first | rfl | omega | split | congr 1
theorem p45_identify (q a b : Nat) (hq : 4≤q) (hd : p45Domain q a b) :
    identify q (.c14 (p45NF q a b))=(45,a,b) := by
  simp only [p45Domain] at hd
  simp only [identify,invNF14,p45NF]
  repeat first | rfl | omega | split | congr 1
theorem p46_identify (q a b : Nat) (hq : 4≤q) (hd : p46Domain q a b) :
    identify q (.c14 (p46NF q a b))=(46,a,b) := by
  simp only [p46Domain] at hd
  simp only [identify,invNF14,p46NF]
  repeat first | rfl | omega | split | congr 1
theorem p47_identify (q a b : Nat) (hq : 4≤q) (hd : p47Domain q a b) :
    identify q (.c24 (p47NF q a b))=(47,a,b) := by
  simp only [p47Domain] at hd
  simp only [identify,invNF24,p47NF]
  repeat first | rfl | omega | split | congr 1
theorem p48_identify (q a b : Nat) (hq : 4≤q) (hd : p48Domain q a b) :
    identify q (.c24 (p48NF q a b))=(48,a,b) := by
  simp only [p48Domain] at hd
  simp only [identify,invNF24,p48NF]
  repeat first | rfl | omega | split | congr 1
theorem p49_identify (q a b : Nat) (hq : 4≤q) (hd : p49Domain q a b) :
    identify q (.c24 (p49NF q a b))=(49,a,b) := by
  simp only [p49Domain] at hd
  simp only [identify,invNF24,p49NF]
  repeat first | rfl | omega | split | congr 1
theorem p50_identify (q a b : Nat) (hq : 4≤q) (hd : p50Domain q a b) :
    identify q (.c24 (p50NF q a b))=(50,a,b) := by
  simp only [p50Domain] at hd
  simp only [identify,invNF24,p50NF]
  repeat first | rfl | omega | split | congr 1
theorem p51_identify (q a b : Nat) (hq : 4≤q) (hd : p51Domain q a b) :
    identify q (.c24 (p51NF q a b))=(51,a,b) := by
  simp only [p51Domain] at hd
  simp only [identify,invNF24,p51NF]
  repeat first | rfl | omega | split | congr 1
#print axioms p42_identify
#print axioms p43_identify
#print axioms p44_identify
#print axioms p45_identify
#print axioms p46_identify
#print axioms p47_identify
#print axioms p48_identify
#print axioms p49_identify
#print axioms p50_identify
#print axioms p51_identify
end LuRazClosure.SourcePieces
