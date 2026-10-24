import LatticeShapeDefs
namespace LuRazClosure.SourcePieces
set_option maxHeartbeats 50000
theorem p82_identify (q a b : Nat) (hq : 4≤q) (hd : p82Domain q a b) :
    identify q (.full (p82NF q a b))=(82,a,b) := by
  simp only [p82Domain] at hd
  simp only [identify,invNFFull,p82NF]
  repeat first | rfl | omega | split | congr 1
theorem p83_identify (q a b : Nat) (hq : 4≤q) (hd : p83Domain q a b) :
    identify q (.full (p83NF q a b))=(83,a,b) := by
  simp only [p83Domain] at hd
  simp only [identify,invNFFull,p83NF]
  repeat first | rfl | omega | split | congr 1
theorem p84_identify (q a b : Nat) (hq : 4≤q) (hd : p84Domain q a b) :
    identify q (.full (p84NF q a b))=(84,a,b) := by
  simp only [p84Domain] at hd
  simp only [identify,invNFFull,p84NF]
  repeat first | rfl | omega | split | congr 1
theorem p85_identify (q a b : Nat) (hq : 4≤q) (hd : p85Domain q a b) :
    identify q (.full (p85NF q a b))=(85,a,b) := by
  simp only [p85Domain] at hd
  simp only [identify,invNFFull,p85NF]
  repeat first | rfl | omega | split | congr 1
theorem p86_identify (q a b : Nat) (hq : 4≤q) (hd : p86Domain q a b) :
    identify q (.full (p86NF q a b))=(86,a,b) := by
  simp only [p86Domain] at hd
  simp only [identify,invNFFull,p86NF]
  repeat first | rfl | omega | split | congr 1
theorem p87_identify (q a b : Nat) (hq : 4≤q) (hd : p87Domain q a b) :
    identify q (.full (p87NF q a b))=(87,a,b) := by
  simp only [p87Domain] at hd
  simp only [identify,invNFFull,p87NF]
  repeat first | rfl | omega | split | congr 1
theorem p88_identify (q a b : Nat) (hq : 4≤q) (hd : p88Domain q a b) :
    identify q (.full (p88NF q a b))=(88,a,b) := by
  simp only [p88Domain] at hd
  simp only [identify,invNFFull,p88NF]
  repeat first | rfl | omega | split | congr 1
theorem p89_identify (q a b : Nat) (hq : 4≤q) (hd : p89Domain q a b) :
    identify q (.full (p89NF q a b))=(89,a,b) := by
  simp only [p89Domain] at hd
  simp only [identify,invNFFull,p89NF]
  repeat first | rfl | omega | split | congr 1
theorem p90_identify (q a b : Nat) (hq : 4≤q) (hd : p90Domain q a b) :
    identify q (.full (p90NF q a b))=(90,a,b) := by
  simp only [p90Domain] at hd
  simp only [identify,invNFFull,p90NF]
  repeat first | rfl | omega | split | congr 1
theorem p91_identify (q a b : Nat) (hq : 4≤q) (hd : p91Domain q a b) :
    identify q (.full (p91NF q a b))=(91,a,b) := by
  simp only [p91Domain] at hd
  simp only [identify,invNFFull,p91NF]
  repeat first | rfl | omega | split | congr 1
#print axioms p82_identify
#print axioms p83_identify
#print axioms p84_identify
#print axioms p85_identify
#print axioms p86_identify
#print axioms p87_identify
#print axioms p88_identify
#print axioms p89_identify
#print axioms p90_identify
#print axioms p91_identify
end LuRazClosure.SourcePieces
