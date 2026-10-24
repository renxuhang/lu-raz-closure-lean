import SixRowDifferenceCounts
import SixRowDifferenceCountIdentity
import SixRowSpectrumOldRelation

namespace LuRazSixRowSpectrum
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

/-- Complete spectrum of the actual, duplicate-free nonempty union closure B. -/
theorem six_row_frequency_spectrum (q e : Nat) (hq : 4≤q)
    (he : 1≤e) (hen : e≤4*q) :
    2*sixRowFrequency q e=spectrumPolynomial2 (q:Int) (e:Int) := by
  have hd := six_row_frequency_delta_closed q e hq he hen
  have hi := difference_count_delta (q:Int) (e:Int) (by omega) (by omega) (by omega)
  have hv := LuRazThreeRow.variant_frequency_spectrum q e hq he hen
  have hp := spectrum_old_relation (q:Int) (e:Int)
  omega

/-- The same spectrum on the original finite source's ordinary finite subsets. -/
theorem six_row_fin_frequency_spectrum (q : Nat) (e : Fin (4*q)) (hq : 4≤q) :
    2*sixRowFinFrequency q e=spectrumPolynomial2 (q:Int) ((e.val+1:Nat):Int) := by
  rw [six_row_fin_frequency_eq]
  exact six_row_frequency_spectrum q (e.val+1) hq (by omega)
    (by have := e.isLt; omega)

end LuRazSixRowSpectrum
