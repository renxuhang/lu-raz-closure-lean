import ThreeRowWeightTools
import SixRowSpectrumSum

namespace LuRazSixRowSpectrum

open LuRazThreeRow LuRazLattice
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

/-- A proved coordinate spectrum determines the actual total family weight. -/
theorem family_weight_formula_of_spectrum (q : Nat) (l : List (Nat → Prop))
    (hq : 4≤q)
    (hs : ∀ e : Nat, 1≤e → e≤4*q →
      2*CountAt l e=spectrumPolynomial2 (q:Int) (e:Int)) :
    2*familyTotalWeight q l=
      69*(q:Int)*(q:Int)*(q:Int)+15*(q:Int)*(q:Int)-18*(q:Int)-34 := by
  calc
    2*familyTotalWeight q l=
        ((List.range' 1 (4*q)).map (fun e => 2*CountAt l e)).sum := by
      rw [family_weight_double_count,sum_scale]
    _=((List.range' 1 (4*q)).map
        (fun e : Nat => spectrumPolynomial2 (q:Int) (e:Int))).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro e he
      have hb := (LuRazEnumeration.range_mem e 1 (4*q)).mp he
      exact hs e (by omega) (by omega)
    _=69*(q:Int)*(q:Int)*(q:Int)+15*(q:Int)*(q:Int)-18*(q:Int)-34 :=
      spectrum_polynomial_sum q hq

/-- Exact deficit from the benchmark mean member size 3q. -/
theorem weight_average_deficit_identity (q : Int) :
    3*q*(23*q*q+7*q+2)-(69*q*q*q+15*q*q-18*q-34)=
      6*q*q+24*q+34 := by
  grind

theorem weight_average_below_threeq (q : Int) (hq : 4≤q) :
    69*q*q*q+15*q*q-18*q-34<3*q*(23*q*q+7*q+2) := by
  have h : 0≤q*q := Int.mul_nonneg (by omega) (by omega)
  grind

/-- Exact doubled-weight improvement compared with the old three-row family. -/
theorem weight_improvement_identity (q : Int) :
    (69*q*q*q+85*q*q-88*q-86)-(69*q*q*q+15*q*q-18*q-34)=
      70*q*q-70*q-52 := by
  grind

theorem weight_improvement_positive (q : Int) (hq : 4≤q) :
    0<70*q*q-70*q-52 := by
  have h : 0≤(q-4)*(q-4) := Int.mul_nonneg (by omega) (by omega)
  grind

#print axioms family_weight_formula_of_spectrum
#print axioms weight_average_deficit_identity
#print axioms weight_average_below_threeq
#print axioms weight_improvement_identity
#print axioms weight_improvement_positive

end LuRazSixRowSpectrum
