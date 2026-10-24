import LatticeSourceTally
import LatticeSpectrumIdentity
import LuRazCoreFrequencies
import LatticeActualCountsPart0
import LatticeActualCountsPart1
import LatticeActualCountsPart2
import LatticeActualCountsPart3
namespace LuRazClosure.SourcePieces
open LuRazLattice
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
noncomputable section
theorem elementFrequency_tail_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*elementFrequency q e=latticeTail2 (q:Int) (e:Int) := by
  rw [elementFrequency_sum q e hq]
  simp only [positiveIds,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    Int.mul_add,Int.mul_zero,Int.add_zero]
  rw [actual0_count q e hq he,actual1_count q e hq he,actual2_count q e hq he,actual3_count q e hq he,actual4_count q e hq he,actual5_count q e hq he,actual6_count q e hq he,actual7_count q e hq he,actual8_count q e hq he,actual9_count q e hq he,actual10_count q e hq he,actual11_count q e hq he,actual12_count q e hq he,actual13_count q e hq he,actual14_count q e hq he,actual15_count q e hq he,actual17_count q e hq he,actual18_count q e hq he,actual19_count q e hq he,actual20_count q e hq he,actual21_count q e hq he,actual22_count q e hq he,actual23_count q e hq he,actual24_count q e hq he,actual25_count q e hq he,actual26_count q e hq he,actual28_count q e hq he,actual29_count q e hq he,actual30_count q e hq he,actual31_count q e hq he,actual32_count q e hq he,actual33_count q e hq he,actual34_count q e hq he,actual35_count q e hq he,actual36_count q e hq he,actual37_count q e hq he,actual38_count q e hq he,actual39_count q e hq he,actual40_count q e hq he,actual41_count q e hq he,actual42_count q e hq he,actual43_count q e hq he,actual44_count q e hq he,actual45_count q e hq he,actual46_count q e hq he,actual47_count q e hq he,actual48_count q e hq he,actual49_count q e hq he,actual50_count q e hq he,actual51_count q e hq he,actual52_count q e hq he,actual53_count q e hq he,actual54_count q e hq he,actual55_count q e hq he,actual56_count q e hq he,actual57_count q e hq he,actual58_count q e hq he,actual59_count q e hq he,actual60_count q e hq he,actual61_count q e hq he,actual62_count q e hq he,actual63_count q e hq he,actual64_count q e hq he,actual65_count q e hq he,actual66_count q e hq he,actual67_count q e hq he,actual68_count q e hq he,actual69_count q e hq he,actual70_count q e hq he,actual71_count q e hq he,actual72_count q e hq he,actual73_count q e hq he,actual74_count q e hq he,actual75_count q e hq he,actual76_count q e hq he,actual77_count q e hq he,actual78_count q e hq he,actual79_count q e hq he,actual80_count q e hq he,actual81_count q e hq he,actual82_count q e hq he,actual83_count q e hq he,actual84_count q e hq he,actual85_count q e hq he,actual86_count q e hq he,actual87_count q e hq he,actual88_count q e hq he,actual89_count q e hq he,actual90_count q e hq he,actual91_count q e hq he]
  simp (maxSteps := 1000000) only [latticeTail2,Identity_left1_0.sumTerms,Int.add_assoc]
theorem elementFrequency_1 (q : Nat) (hq : 4≤q) :
    2*elementFrequency q 1=19*(q:Int)*(q:Int)+25*(q:Int)-44 := by
  exact containingOneMembers_length q hq
theorem elementFrequency_2 (q : Nat) (hq : 4≤q) :
    2*elementFrequency q 2=17*(q:Int)*(q:Int)+25*(q:Int)-34 := by
  exact containingTwoMembers_length q hq
theorem elementFrequency_3 (q : Nat) (hq : 4≤q) :
    2*elementFrequency q 3=17*(q:Int)*(q:Int)+27*(q:Int)-48 := by
  exact containingThreeMembers_length q hq
theorem elementFrequency_4 (q : Nat) (hq : 4≤q) :
    2*elementFrequency q 4=16*(q:Int)*(q:Int)+30*(q:Int)-46 := by
  exact containingFourMembers_length q hq
/-- Exact full spectrum for the original generated, nonempty-union closure. -/
theorem elementFrequency_spectrum (q e : Nat) (hq : 4≤q) (he : 1≤e) (hen : e≤4*q) :
    2*elementFrequency q e=frequencyPolynomial2 (q:Int) (e:Int) := by
  by_cases h1 : e=1
  · subst e; rw [elementFrequency_1 q hq]; simp [frequencyPolynomial2,Int.sub_eq_add_neg]
  by_cases h2 : e=2
  · subst e; rw [elementFrequency_2 q hq]; simp [frequencyPolynomial2,Int.sub_eq_add_neg]
  by_cases h3 : e=3
  · subst e; rw [elementFrequency_3 q hq]; simp [frequencyPolynomial2,Int.sub_eq_add_neg]
  by_cases h4 : e=4
  · subst e; rw [elementFrequency_4 q hq]; simp [frequencyPolynomial2,Int.sub_eq_add_neg]
  have ht := elementFrequency_tail_count q e hq (by omega)
  have hp := lattice_spectrum_identity (q:Int) (e:Int) (by omega) (by omega) (by omega)
  have hn1 : (e:Int)≠1 := by omega
  have hn2 : (e:Int)≠2 := by omega
  have hn3 : (e:Int)≠3 := by omega
  have hn4 : (e:Int)≠4 := by omega
  simp only [latticeFrequency2,ite_eq_right hn1,ite_eq_right hn2,ite_eq_right hn3,ite_eq_right hn4] at hp
  exact ht.trans hp
#print axioms elementFrequency_tail_count
#print axioms elementFrequency_spectrum
end
end LuRazClosure.SourcePieces
