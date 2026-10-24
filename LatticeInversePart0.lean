import LatticeShapeDefs
namespace LuRazClosure.SourcePieces
set_option maxHeartbeats 50000
theorem p0_identify (q a b : Nat) (hq : 4≤q) (hd : p0Domain q a b) :
    identify q (.small (p0NF q a b))=(0,a,b) := by
  simp only [p0Domain] at hd
  simp only [identify,invNFSmall,p0NF]
  repeat first | rfl | omega | split | congr 1
theorem p1_identify (q a b : Nat) (hq : 4≤q) (hd : p1Domain q a b) :
    identify q (.small (p1NF q a b))=(1,a,b) := by
  simp only [p1Domain] at hd
  simp only [identify,invNFSmall,p1NF]
  repeat first | rfl | omega | split | congr 1
theorem p2_identify (q a b : Nat) (hq : 4≤q) (hd : p2Domain q a b) :
    identify q (.small (p2NF q a b))=(2,a,b) := by
  simp only [p2Domain] at hd
  simp only [identify,invNFSmall,p2NF]
  repeat first | rfl | omega | split | congr 1
theorem p3_identify (q a b : Nat) (hq : 4≤q) (hd : p3Domain q a b) :
    identify q (.small (p3NF q a b))=(3,a,b) := by
  simp only [p3Domain] at hd
  simp only [identify,invNFSmall,p3NF]
  repeat first | rfl | omega | split | congr 1
theorem p4_identify (q a b : Nat) (hq : 4≤q) (hd : p4Domain q a b) :
    identify q (.small (p4NF q a b))=(4,a,b) := by
  simp only [p4Domain] at hd
  simp only [identify,invNFSmall,p4NF]
  repeat first | rfl | omega | split | congr 1
theorem p5_identify (q a b : Nat) (hq : 4≤q) (hd : p5Domain q a b) :
    identify q (.small (p5NF q a b))=(5,a,b) := by
  simp only [p5Domain] at hd
  simp only [identify,invNFSmall,p5NF]
  repeat first | rfl | omega | split | congr 1
theorem p6_identify (q a b : Nat) (hq : 4≤q) (hd : p6Domain q a b) :
    identify q (.small (p6NF q a b))=(6,a,b) := by
  simp only [p6Domain] at hd
  simp only [identify,invNFSmall,p6NF]
  repeat first | rfl | omega | split | congr 1
theorem p7_identify (q a b : Nat) (hq : 4≤q) (hd : p7Domain q a b) :
    identify q (.small (p7NF q a b))=(7,a,b) := by
  simp only [p7Domain] at hd
  simp only [identify,invNFSmall,p7NF]
  repeat first | rfl | omega | split | congr 1
theorem p8_identify (q a b : Nat) (hq : 4≤q) (hd : p8Domain q a b) :
    identify q (.small (p8NF q a b))=(8,a,b) := by
  simp only [p8Domain] at hd
  simp only [identify,invNFSmall,p8NF]
  repeat first | rfl | omega | split | congr 1
theorem p9_identify (q a b : Nat) (hq : 4≤q) (hd : p9Domain q a b) :
    identify q (.small (p9NF q a b))=(9,a,b) := by
  simp only [p9Domain] at hd
  simp only [identify,invNFSmall,p9NF]
  repeat first | rfl | omega | split | congr 1
#print axioms p0_identify
#print axioms p1_identify
#print axioms p2_identify
#print axioms p3_identify
#print axioms p4_identify
#print axioms p5_identify
#print axioms p6_identify
#print axioms p7_identify
#print axioms p8_identify
#print axioms p9_identify
end LuRazClosure.SourcePieces
