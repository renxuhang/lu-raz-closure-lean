import SixRowSpectrumExtrema
import SixRowRatioArithmetic

namespace LuRazSixRowSpectrum

open RatioArithmetic
set_option maxHeartbeats 3000000

theorem spectrum_uniform_lower (q e : Int) (hq : 4≤q)
    (he : 1≤e) (hen : e≤4*q) :
    127*(23*q*q+7*q+2)≤199*spectrumPolynomial2 q e := by
  have hm := (spectrum_min_exact q e hq he hen).1
  have hr := minimum_uniform_bound q hq
  omega

theorem spectrum_strict_half (q e : Int) (hq : 4≤q)
    (he : 1≤e) (hen : e≤4*q) :
    23*q*q+7*q+2<2*spectrumPolynomial2 q e := by
  have hm := (spectrum_min_exact q e hq he hen).1
  have hr := minimum_strict_half q hq
  omega

theorem spectrum_strict_upper (q e : Int) (hq : 4≤q)
    (he : 1≤e) (hen : e≤4*q) :
    23*spectrumPolynomial2 q e<19*(23*q*q+7*q+2) := by
  have hm := spectrum_max_bound q e hq he hen
  have hr := maximum_strict_upper_bound q hq
  omega

theorem spectrum_fifteen_twenty_three_threshold (q : Int) (hq : 4≤q) :
    (∀ e : Int, 1≤e → e≤4*q →
      15*(23*q*q+7*q+2)<23*spectrumPolynomial2 q e) ↔ 7≤q := by
  constructor
  · intro h
    have hm := h (3*q) (by omega) (by omega)
    rw [spectrum_at_threeq q hq] at hm
    exact (minimum_fifteen_twenty_three_threshold q).mp hm
  · intro h7 e he hen
    have hm := (spectrum_min_exact q e hq he hen).1
    have hr := (minimum_fifteen_twenty_three_threshold q).mpr h7
    omega

/-- The best uniform lower frequency ratio, across all parameters q≥4, is 127/199. -/
theorem spectrum_uniform_lower_sharp (a b : Int) (hb : 0<b) :
    (∀ q e : Int, 4≤q → 1≤e → e≤4*q →
      a*(23*q*q+7*q+2)≤b*spectrumPolynomial2 q e) ↔ 199*a≤127*b := by
  constructor
  · intro h
    have h4 := h 4 12 (by decide) (by decide) (by decide)
    have he : spectrumPolynomial2 4 12=254 := by decide
    rw [he] at h4
    omega
  · intro hab q e hq he hen
    have hcard := cardinality_positive q hq
    have hbound := spectrum_uniform_lower q e hq he hen
    have hp := Int.mul_le_mul_of_nonneg_right hab (show 0≤23*q*q+7*q+2 by omega)
    have hbnd := Int.mul_le_mul_of_nonneg_left hbound (show 0≤b by omega)
    grind

/-- The lower ratios approach 15/23 on every arbitrarily late parameter tail. -/
theorem spectrum_minimum_tail_sharp (a b Q : Int)
    (hb : 0<b) (ha : 15*b<23*a) (hQ : 4≤Q) :
    ∃ q : Int, Q≤q ∧
      b*spectrumPolynomial2 q (3*q)<a*(23*q*q+7*q+2) := by
  obtain ⟨q,hq,hr⟩ := minimum_eventually_below a b Q hb ha hQ
  refine ⟨q,hq,?_⟩
  rw [spectrum_at_threeq q (by omega)]
  exact hr

/-- The upper ratios approach 19/23 from below on every parameter tail. -/
theorem spectrum_maximum_tail_sharp (a b Q : Int)
    (ha0 : 0≤a) (hb : 0<b) (ha : 23*a<19*b) (hQ : 4≤Q) :
    ∃ q : Int, Q≤q ∧
      a*(23*q*q+7*q+2)<b*spectrumPolynomial2 q (q+2) := by
  obtain ⟨q,hq,hr⟩ := maximum_eventually_above a b Q ha0 hb ha hQ
  refine ⟨q,hq,?_⟩
  rw [spectrum_at_qplus2 q (by omega)]
  exact hr

#print axioms spectrum_uniform_lower
#print axioms spectrum_strict_half
#print axioms spectrum_strict_upper
#print axioms spectrum_fifteen_twenty_three_threshold
#print axioms spectrum_uniform_lower_sharp
#print axioms spectrum_minimum_tail_sharp
#print axioms spectrum_maximum_tail_sharp

end LuRazSixRowSpectrum
