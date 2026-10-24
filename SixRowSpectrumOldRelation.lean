import SixRowSpectrumPolynomial
import ThreeRowSpectrumPolynomial

namespace LuRazSixRowSpectrum

/-- Pure algebraic consistency of the old spectrum and the 43-group change. -/
theorem spectrum_old_relation (q e : Int) :
    LuRazThreeRow.spectrumPolynomial2 q e + 2*deltaPolynomial q e =
      spectrumPolynomial2 q e := by
  unfold LuRazThreeRow.spectrumPolynomial2 deltaPolynomial spectrumPolynomial2
  repeat' first | split <;> simp_all | omega

end LuRazSixRowSpectrum
