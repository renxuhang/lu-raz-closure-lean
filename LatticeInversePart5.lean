import LatticeShapeDefs
namespace LuRazClosure.SourcePieces
set_option maxHeartbeats 50000
theorem p52_identify (q a b : Nat) (hq : 4≤q) (hd : p52Domain q a b) :
    identify q (.c24 (p52NF q a b))=(52,a,b) := by
  simp only [p52Domain] at hd
  simp only [identify,invNF24,p52NF]
  repeat first | rfl | omega | split | congr 1
theorem p53_identify (q a b : Nat) (hq : 4≤q) (hd : p53Domain q a b) :
    identify q (.c124 (p53NF q a b))=(53,a,b) := by
  simp only [p53Domain] at hd
  simp only [identify,invNF124,p53NF]
  repeat first | rfl | omega | split | congr 1
theorem p54_identify (q a b : Nat) (hq : 4≤q) (hd : p54Domain q a b) :
    identify q (.c124 (p54NF q a b))=(54,a,b) := by
  simp only [p54Domain] at hd
  simp only [identify,invNF124,p54NF]
  repeat first | rfl | omega | split | congr 1
theorem p55_identify (q a b : Nat) (hq : 4≤q) (hd : p55Domain q a b) :
    identify q (.c124 (p55NF q a b))=(55,a,b) := by
  simp only [p55Domain] at hd
  simp only [identify,invNF124,p55NF]
  repeat first | rfl | omega | split | congr 1
theorem p56_identify (q a b : Nat) (hq : 4≤q) (hd : p56Domain q a b) :
    identify q (.c124 (p56NF q a b))=(56,a,b) := by
  simp only [p56Domain] at hd
  simp only [identify,invNF124,p56NF]
  repeat first | rfl | omega | split | congr 1
theorem p57_identify (q a b : Nat) (hq : 4≤q) (hd : p57Domain q a b) :
    identify q (.c124 (p57NF q a b))=(57,a,b) := by
  simp only [p57Domain] at hd
  simp only [identify,invNF124,p57NF]
  repeat first | rfl | omega | split | congr 1
theorem p58_identify (q a b : Nat) (hq : 4≤q) (hd : p58Domain q a b) :
    identify q (.c124 (p58NF q a b))=(58,a,b) := by
  simp only [p58Domain] at hd
  simp only [identify,invNF124,p58NF]
  repeat first | rfl | omega | split | congr 1
theorem p59_identify (q a b : Nat) (hq : 4≤q) (hd : p59Domain q a b) :
    identify q (.c124 (p59NF q a b))=(59,a,b) := by
  simp only [p59Domain] at hd
  simp only [identify,invNF124,p59NF]
  repeat first | rfl | omega | split | congr 1
theorem p60_identify (q a b : Nat) (hq : 4≤q) (hd : p60Domain q a b) :
    identify q (.c134 (p60NF q a b))=(60,a,b) := by
  simp only [p60Domain] at hd
  simp only [identify,invNF134,p60NF]
  repeat first | rfl | omega | split | congr 1
theorem p61_identify (q a b : Nat) (hq : 4≤q) (hd : p61Domain q a b) :
    identify q (.c134 (p61NF q a b))=(61,a,b) := by
  simp only [p61Domain] at hd
  simp only [identify,invNF134,p61NF]
  repeat first | rfl | omega | split | congr 1
#print axioms p52_identify
#print axioms p53_identify
#print axioms p54_identify
#print axioms p55_identify
#print axioms p56_identify
#print axioms p57_identify
#print axioms p58_identify
#print axioms p59_identify
#print axioms p60_identify
#print axioms p61_identify
end LuRazClosure.SourcePieces
