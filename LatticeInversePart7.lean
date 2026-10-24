import LatticeShapeDefs
namespace LuRazClosure.SourcePieces
set_option maxHeartbeats 50000
theorem p72_identify (q a b : Nat) (hq : 4≤q) (hd : p72Domain q a b) :
    identify q (.c234 (p72NF q a b))=(72,a,b) := by
  simp only [p72Domain] at hd
  simp only [identify,invNF234,p72NF]
  repeat first | rfl | omega | split | congr 1
theorem p73_identify (q a b : Nat) (hq : 4≤q) (hd : p73Domain q a b) :
    identify q (.c234 (p73NF q a b))=(73,a,b) := by
  simp only [p73Domain] at hd
  simp only [identify,invNF234,p73NF]
  repeat first | rfl | omega | split | congr 1
theorem p74_identify (q a b : Nat) (hq : 4≤q) (hd : p74Domain q a b) :
    identify q (.c234 (p74NF q a b))=(74,a,b) := by
  simp only [p74Domain] at hd
  simp only [identify,invNF234,p74NF]
  repeat first | rfl | omega | split | congr 1
theorem p75_identify (q a b : Nat) (hq : 4≤q) (hd : p75Domain q a b) :
    identify q (.c234 (p75NF q a b))=(75,a,b) := by
  simp only [p75Domain] at hd
  simp only [identify,invNF234,p75NF]
  repeat first | rfl | omega | split | congr 1
theorem p76_identify (q a b : Nat) (hq : 4≤q) (hd : p76Domain q a b) :
    identify q (.c234 (p76NF q a b))=(76,a,b) := by
  simp only [p76Domain] at hd
  simp only [identify,invNF234,p76NF]
  repeat first | rfl | omega | split | congr 1
theorem p77_identify (q a b : Nat) (hq : 4≤q) (hd : p77Domain q a b) :
    identify q (.c234 (p77NF q a b))=(77,a,b) := by
  simp only [p77Domain] at hd
  simp only [identify,invNF234,p77NF]
  repeat first | rfl | omega | split | congr 1
theorem p78_identify (q a b : Nat) (hq : 4≤q) (hd : p78Domain q a b) :
    identify q (.full (p78NF q a b))=(78,a,b) := by
  simp only [p78Domain] at hd
  simp only [identify,invNFFull,p78NF]
  repeat first | rfl | omega | split | congr 1
theorem p79_identify (q a b : Nat) (hq : 4≤q) (hd : p79Domain q a b) :
    identify q (.full (p79NF q a b))=(79,a,b) := by
  simp only [p79Domain] at hd
  simp only [identify,invNFFull,p79NF]
  repeat first | rfl | omega | split | congr 1
theorem p80_identify (q a b : Nat) (hq : 4≤q) (hd : p80Domain q a b) :
    identify q (.full (p80NF q a b))=(80,a,b) := by
  simp only [p80Domain] at hd
  simp only [identify,invNFFull,p80NF]
  repeat first | rfl | omega | split | congr 1
theorem p81_identify (q a b : Nat) (hq : 4≤q) (hd : p81Domain q a b) :
    identify q (.full (p81NF q a b))=(81,a,b) := by
  simp only [p81Domain] at hd
  simp only [identify,invNFFull,p81NF]
  repeat first | rfl | omega | split | congr 1
#print axioms p72_identify
#print axioms p73_identify
#print axioms p74_identify
#print axioms p75_identify
#print axioms p76_identify
#print axioms p77_identify
#print axioms p78_identify
#print axioms p79_identify
#print axioms p80_identify
#print axioms p81_identify
end LuRazClosure.SourcePieces
