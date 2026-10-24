import SixRowDeltaIdentity_one
import SixRowDeltaIdentity_two
import SixRowDeltaIdentity_three
import SixRowDeltaIdentity_four
import SixRowDeltaIdentity_left1
import SixRowDeltaIdentity_q3
import SixRowDeltaIdentity_left2
import SixRowDeltaIdentity_h1
import SixRowDeltaIdentity_h2
import SixRowDeltaIdentity_middle
import SixRowDeltaIdentity_r1
import SixRowDeltaIdentity_right
import SixRowDeltaIdentity_n1
import SixRowDeltaIdentity_n
import SixRowSpectrumPolynomial
namespace LuRazSixRowSpectrum
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
theorem difference_count_delta (q e : Int) (hq : 4≤q) (he : 1≤e) (hen : e≤4*q) :
    (addedGroupCounts q e).sum-(removedGroupCounts q e).sum=deltaPolynomial q e := by
  by_cases h0 : e=1
  ·
    have ht := delta_one q e (by omega) (by omega) (by omega) (by omega) (by omega)
    simp only [deltaPolynomial,ite_eq_left h0]
    omega
  by_cases h1 : e=2
  ·
    have ht := delta_two q e (by omega) (by omega) (by omega) (by omega) (by omega)
    simp only [deltaPolynomial,ite_eq_right h0,ite_eq_left h1]
    omega
  by_cases h2 : e=3
  ·
    have ht := delta_three q e (by omega) (by omega) (by omega) (by omega) (by omega)
    simp only [deltaPolynomial,ite_eq_right h0,ite_eq_right h1,ite_eq_left h2]
    omega
  by_cases h3 : e=4
  ·
    have ht := delta_four q e (by omega) (by omega) (by omega) (by omega) (by omega)
    simp only [deltaPolynomial,ite_eq_right h0,ite_eq_right h1,ite_eq_right h2,ite_eq_left h3]
    omega
  by_cases h4 : e≤q+2
  ·
    have ht := delta_left1 q e (by omega) (by omega) (by omega) (by omega) (by omega)
    simp only [deltaPolynomial,ite_eq_right h0,ite_eq_right h1,ite_eq_right h2,ite_eq_right h3,ite_eq_left h4]
    omega
  by_cases h5 : e=q+3
  ·
    have ht := delta_q3 q e (by omega) (by omega) (by omega) (by omega) (by omega)
    simp only [deltaPolynomial,ite_eq_right h0,ite_eq_right h1,ite_eq_right h2,ite_eq_right h3,ite_eq_right h4,ite_eq_left h5]
    omega
  by_cases h6 : e≤2*q
  ·
    have ht := delta_left2 q e (by omega) (by omega) (by omega) (by omega) (by omega)
    simp only [deltaPolynomial,ite_eq_right h0,ite_eq_right h1,ite_eq_right h2,ite_eq_right h3,ite_eq_right h4,ite_eq_right h5,ite_eq_left h6]
    omega
  by_cases h7 : e=2*q+1
  ·
    have ht := delta_h1 q e (by omega) (by omega) (by omega) (by omega) (by omega)
    simp only [deltaPolynomial,ite_eq_right h0,ite_eq_right h1,ite_eq_right h2,ite_eq_right h3,ite_eq_right h4,ite_eq_right h5,ite_eq_right h6,ite_eq_left h7]
    omega
  by_cases h8 : e=2*q+2
  ·
    have ht := delta_h2 q e (by omega) (by omega) (by omega) (by omega) (by omega)
    simp only [deltaPolynomial,ite_eq_right h0,ite_eq_right h1,ite_eq_right h2,ite_eq_right h3,ite_eq_right h4,ite_eq_right h5,ite_eq_right h6,ite_eq_right h7,ite_eq_left h8]
    omega
  by_cases h9 : e≤3*q
  ·
    have ht := delta_middle q e (by omega) (by omega) (by omega) (by omega) (by omega)
    simp only [deltaPolynomial,ite_eq_right h0,ite_eq_right h1,ite_eq_right h2,ite_eq_right h3,ite_eq_right h4,ite_eq_right h5,ite_eq_right h6,ite_eq_right h7,ite_eq_right h8,ite_eq_left h9]
    omega
  by_cases h10 : e=3*q+1
  ·
    have ht := delta_r1 q e (by omega) (by omega) (by omega) (by omega) (by omega)
    simp only [deltaPolynomial,ite_eq_right h0,ite_eq_right h1,ite_eq_right h2,ite_eq_right h3,ite_eq_right h4,ite_eq_right h5,ite_eq_right h6,ite_eq_right h7,ite_eq_right h8,ite_eq_right h9,ite_eq_left h10]
    omega
  by_cases h11 : e≤4*q-2
  ·
    have ht := delta_right q e (by omega) (by omega) (by omega) (by omega) (by omega)
    simp only [deltaPolynomial,ite_eq_right h0,ite_eq_right h1,ite_eq_right h2,ite_eq_right h3,ite_eq_right h4,ite_eq_right h5,ite_eq_right h6,ite_eq_right h7,ite_eq_right h8,ite_eq_right h9,ite_eq_right h10,ite_eq_left h11]
    omega
  by_cases h12 : e=4*q-1
  ·
    have ht := delta_n1 q e (by omega) (by omega) (by omega) (by omega) (by omega)
    simp only [deltaPolynomial,ite_eq_right h0,ite_eq_right h1,ite_eq_right h2,ite_eq_right h3,ite_eq_right h4,ite_eq_right h5,ite_eq_right h6,ite_eq_right h7,ite_eq_right h8,ite_eq_right h9,ite_eq_right h10,ite_eq_right h11,ite_eq_left h12]
    omega
  have ht := delta_n q e (by omega) (by omega) (by omega) (by omega) (by omega)
  simp only [deltaPolynomial,ite_eq_right h0,ite_eq_right h1,ite_eq_right h2,ite_eq_right h3,ite_eq_right h4,ite_eq_right h5,ite_eq_right h6,ite_eq_right h7,ite_eq_right h8,ite_eq_right h9,ite_eq_right h10,ite_eq_right h11,ite_eq_right h12]
  omega
end LuRazSixRowSpectrum
