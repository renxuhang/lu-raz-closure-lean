import Std

namespace LuRazSixRowSpectrum

/-- Twice the ordinary coordinate frequency of the six-row construction.
The identification with the actual nonempty union closure is proved separately. -/
def spectrumPolynomial2 (q e : Int) : Int :=
  if e=1 then 19*q*q+q else
  if e=2 then 17*q*q-q else
  if e=3 then 17*q*q-q-2 else
  if e=4 then 16*q*q+10*q-22 else
  if e≤q+2 then 18*q*q+2*q*e-4*q-e*e+5*e-4 else
  if e=q+3 then 18*q*q-4*q+4 else
  if e≤2*q then 16*q*q+4*q*e-24*q-2*e*e+18*e-32 else
  if e=2*q+1 then 16*q*q+12*q-24 else
  if e=2*q+2 then 16*q*q+10*q-20 else
  if e≤3*q then 12*q*q+4*q*e+16*q-e*e-3*e-14 else
  if e=3*q+1 then 17*q*q+11*q-24 else
  if e≤4*q-2 then -14*q*q+16*q*e+26*q-2*e*e-6*e else
  if e=4*q-1 then 18*q*q+6*q-2 else
  18*q*q+2*q-4

/-- Ordinary coordinate frequency change from the verified three-row variant V. -/
def deltaPolynomial (q e : Int) : Int :=
  if e=1 then 13-8*q else
  if e=2 then 15-11*q else
  if e=3 then 17-12*q else
  if e=4 then 12-12*q else
  if e≤q+2 then 3*e-10*q+3 else
  if e=q+3 then 10-6*q else
  if e≤2*q then 15-5*q-e else
  if e=2*q+1 then 20-11*q else
  if e=2*q+2 then 19-12*q else
  if e≤3*q then 13-7*q-e else
  if e=3*q+1 then 15-11*q else
  if e≤4*q-2 then 13-7*q-e else
  if e=4*q-1 then 15-9*q else
  18-11*q

end LuRazSixRowSpectrum
