import Std

namespace LuRazSixRowSpectrum.RatioArithmetic

set_option maxHeartbeats 2000000

/-- These are integer polynomial facts; the actual spectrum is bridged separately. -/
theorem minimum_uniform_bound (q : Int) (hq : 4≤q) :
    127*(23*q*q+7*q+2)≤199*(15*q*q+7*q-14) := by
  have h : 0≤(q-4)*(8*q+95) := Int.mul_nonneg (by omega) (by omega)
  grind

theorem minimum_uniform_equality (q : Int) (hq : 4≤q) :
    127*(23*q*q+7*q+2)=199*(15*q*q+7*q-14) ↔ q=4 := by
  constructor
  · intro he
    by_cases hn : q=4
    · exact hn
    have h : 0<(q-4)*(8*q+95) := Int.mul_pos (by omega) (by omega)
    grind
  · intro h; subst q; decide

theorem minimum_fifteen_twenty_three_threshold (q : Int) :
    15*(23*q*q+7*q+2)<23*(15*q*q+7*q-14) ↔ 7≤q := by
  grind

theorem maximum_strict_upper_bound (q : Int) (hq : 4≤q) :
    23*(19*q*q+q+2)<19*(23*q*q+7*q+2) := by
  grind

theorem minimum_strict_half (q : Int) (hq : 4≤q) :
    23*q*q+7*q+2<2*(15*q*q+7*q-14) := by
  have h : 0≤(q-4)*(q-4) := Int.mul_nonneg (by omega) (by omega)
  grind

theorem cardinality_positive (q : Int) (hq : 4≤q) :
    0<23*q*q+7*q+2 := by
  have h : 0≤q*q := Int.mul_nonneg (by omega) (by omega)
  grind

/-- No rational number strictly larger than 15/23 is a lower bound on any tail. -/
theorem minimum_eventually_below (a b Q : Int)
    (hb : 0<b) (ha : 15*b<23*a) (hQ : 4≤Q) :
    ∃ q : Int, Q≤q ∧
      b*(15*q*q+7*q-14)<a*(23*q*q+7*q+2) := by
  let q := 7*b+Q
  have hq : Q≤q := by dsimp [q]; omega
  have ha0 : 0<a := by omega
  have hq0 : 0<q := by omega
  have hprod : 0≤(23*a-15*b-1)*q*q :=
    Int.mul_nonneg (Int.mul_nonneg (by omega) (by omega)) (by omega)
  have hcross : 0≤a*q := Int.mul_nonneg (by omega) (by omega)
  have htail : 0<q*(q-7*b) := Int.mul_pos hq0 (by dsimp [q]; omega)
  refine ⟨q,hq,?_⟩
  grind

/-- Every positive rational smaller than 19/23 is exceeded on every sufficiently late tail. -/
theorem maximum_eventually_above (a b Q : Int)
    (ha0 : 0≤a) (hb : 0<b) (ha : 23*a<19*b) (hQ : 4≤Q) :
    ∃ q : Int, Q≤q ∧
      a*(23*q*q+7*q+2)<b*(19*q*q+q+2) := by
  let q := 7*a+Q
  have hq : Q≤q := by dsimp [q]; omega
  have hq0 : 0<q := by omega
  have hab : a<b := by omega
  have hprod : 0≤(19*b-23*a-1)*q*q :=
    Int.mul_nonneg (Int.mul_nonneg (by omega) (by omega)) (by omega)
  have hcross : 0≤b*q := Int.mul_nonneg (by omega) (by omega)
  have htail : 0<q*(q-7*a) := Int.mul_pos hq0 (by dsimp [q]; omega)
  refine ⟨q,hq,?_⟩
  grind

/-- Among integer parameters q≥4, the minimum-frequency ratio peaks uniquely at q=13. -/
theorem minimum_parameter_maximum (q : Int) (hq : 4≤q) :
    995*(15*q*q+7*q-14)≤653*(23*q*q+7*q+2) ∧
      (995*(15*q*q+7*q-14)=653*(23*q*q+7*q+2) ↔ q=13) := by
  have hb : 995*(15*q*q+7*q-14)≤653*(23*q*q+7*q+2) := by
    by_cases h : q≤12
    · have hp : 0≤(q-13)*(94*q-1172) :=
        Int.mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
      grind
    · have hp : 0≤(q-13)*(94*q-1172) := Int.mul_nonneg (by omega) (by omega)
      grind
  refine ⟨hb,?_⟩
  constructor
  · intro he
    by_cases h13 : q=13
    · exact h13
    by_cases h : q≤12
    · have hp : 0<(13-q)*(1172-94*q) := Int.mul_pos (by omega) (by omega)
      grind
    · have hp : 0<(q-13)*(94*q-1172) := Int.mul_pos (by omega) (by omega)
      grind
  · intro h; subst q; decide

#print axioms minimum_uniform_bound
#print axioms minimum_uniform_equality
#print axioms minimum_fifteen_twenty_three_threshold
#print axioms maximum_strict_upper_bound
#print axioms minimum_strict_half
#print axioms cardinality_positive
#print axioms minimum_eventually_below
#print axioms maximum_eventually_above
#print axioms minimum_parameter_maximum

end LuRazSixRowSpectrum.RatioArithmetic
