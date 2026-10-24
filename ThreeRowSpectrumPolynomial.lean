import Std

namespace LuRazThreeRow

/-- Twice the frequency at a coordinate in the three-row modified closure.
The identification with the actual closure is proved in a separate module. -/
def spectrumPolynomial2 (q e : Int) : Int :=
  if e=1 then 19*q*q+17*q-26 else
  if e=2 then 17*q*q+21*q-30 else
  if e=3 then 17*q*q+23*q-36 else
  if e=4 then 16*q*q+34*q-46 else
  if e≤q+2 then 18*q*q+2*q*e+16*q-e*e-e-10 else
  if e=q+3 then 18*q*q+8*q-16 else
  if e≤2*q then 16*q*q+4*q*e-14*q-2*e*e+20*e-62 else
  if e=2*q+1 then 16*q*q+34*q-64 else
  if e=2*q+2 then 16*q*q+34*q-58 else
  if e≤3*q then 12*q*q+4*q*e+30*q-e*e-e-40 else
  if e=3*q+1 then 17*q*q+33*q-54 else
  if e≤4*q-2 then -14*q*q+16*q*e+40*q-2*e*e-4*e-26 else
  if e=4*q-1 then 18*q*q+24*q-32 else
  18*q*q+24*q-40

/-- The change in the ordinary (not doubled) coordinate frequency. -/
def deltaPolynomial (q e : Int) : Int :=
  if e=1 then 9-4*q else
  if e=2 then 2-2*q else
  if e=3 then 6-2*q else
  if e=4 then 2*q else
  if e≤q+2 then 5-2*q else
  if e≤2*q then 4-2*q else
  if e=2*q+1 then 2 else
  if e=2*q+2 then 2*q-3 else
  if e≤3*q then 2*q+3-e else
  if e=3*q+1 then 0 else
  if e≤4*q-2 then 2*q+5-e else
  if e=4*q-1 then 4-2*q else
  6-2*q

end LuRazThreeRow
