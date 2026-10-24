import ThreeRowSpectrumPolynomial
import LatticeSpectrumIdentity

namespace LuRazThreeRow
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

theorem spectrum_old_relation_one (q e : Int) (hq : 4≤q) (hregion : e=1) :
    LuRazLattice.frequencyPolynomial2 q e + 2*deltaPolynomial q e = spectrumPolynomial2 q e := by
  have ha0 : e=1 := by omega
  have ha1 : ¬(e=2) := by omega
  have ha2 : ¬(e=3) := by omega
  have ha3 : ¬(e=4) := by omega
  have ha4 : e≤q+2 := by omega
  have ha5 : ¬(e=q+3) := by omega
  have ha6 : e≤2*q := by omega
  have ha7 : ¬(e=2*q+1) := by omega
  have ha8 : ¬(e=2*q+2) := by omega
  have ha9 : e≤3*q := by omega
  have ha10 : ¬(e=3*q+1) := by omega
  have ha11 : e≤4*q-2 := by omega
  have ha12 : ¬(e=4*q-1) := by omega
  simp only [LuRazLattice.frequencyPolynomial2,deltaPolynomial,spectrumPolynomial2,ha0,ha1,ha2,ha3,ha4,ha5,ha6,ha7,ha8,ha9,ha10,ha11,ha12,ite_true,ite_false]
  grind

theorem spectrum_old_relation_two (q e : Int) (hq : 4≤q) (hregion : e=2) :
    LuRazLattice.frequencyPolynomial2 q e + 2*deltaPolynomial q e = spectrumPolynomial2 q e := by
  have ha0 : ¬(e=1) := by omega
  have ha1 : e=2 := by omega
  have ha2 : ¬(e=3) := by omega
  have ha3 : ¬(e=4) := by omega
  have ha4 : e≤q+2 := by omega
  have ha5 : ¬(e=q+3) := by omega
  have ha6 : e≤2*q := by omega
  have ha7 : ¬(e=2*q+1) := by omega
  have ha8 : ¬(e=2*q+2) := by omega
  have ha9 : e≤3*q := by omega
  have ha10 : ¬(e=3*q+1) := by omega
  have ha11 : e≤4*q-2 := by omega
  have ha12 : ¬(e=4*q-1) := by omega
  simp only [LuRazLattice.frequencyPolynomial2,deltaPolynomial,spectrumPolynomial2,ha0,ha1,ha2,ha3,ha4,ha5,ha6,ha7,ha8,ha9,ha10,ha11,ha12,ite_true,ite_false]
  grind

theorem spectrum_old_relation_three (q e : Int) (hq : 4≤q) (hregion : e=3) :
    LuRazLattice.frequencyPolynomial2 q e + 2*deltaPolynomial q e = spectrumPolynomial2 q e := by
  have ha0 : ¬(e=1) := by omega
  have ha1 : ¬(e=2) := by omega
  have ha2 : e=3 := by omega
  have ha3 : ¬(e=4) := by omega
  have ha4 : e≤q+2 := by omega
  have ha5 : ¬(e=q+3) := by omega
  have ha6 : e≤2*q := by omega
  have ha7 : ¬(e=2*q+1) := by omega
  have ha8 : ¬(e=2*q+2) := by omega
  have ha9 : e≤3*q := by omega
  have ha10 : ¬(e=3*q+1) := by omega
  have ha11 : e≤4*q-2 := by omega
  have ha12 : ¬(e=4*q-1) := by omega
  simp only [LuRazLattice.frequencyPolynomial2,deltaPolynomial,spectrumPolynomial2,ha0,ha1,ha2,ha3,ha4,ha5,ha6,ha7,ha8,ha9,ha10,ha11,ha12,ite_true,ite_false]
  grind

theorem spectrum_old_relation_four (q e : Int) (hq : 4≤q) (hregion : e=4) :
    LuRazLattice.frequencyPolynomial2 q e + 2*deltaPolynomial q e = spectrumPolynomial2 q e := by
  have ha0 : ¬(e=1) := by omega
  have ha1 : ¬(e=2) := by omega
  have ha2 : ¬(e=3) := by omega
  have ha3 : e=4 := by omega
  have ha4 : e≤q+2 := by omega
  have ha5 : ¬(e=q+3) := by omega
  have ha6 : e≤2*q := by omega
  have ha7 : ¬(e=2*q+1) := by omega
  have ha8 : ¬(e=2*q+2) := by omega
  have ha9 : e≤3*q := by omega
  have ha10 : ¬(e=3*q+1) := by omega
  have ha11 : e≤4*q-2 := by omega
  have ha12 : ¬(e=4*q-1) := by omega
  simp only [LuRazLattice.frequencyPolynomial2,deltaPolynomial,spectrumPolynomial2,ha0,ha1,ha2,ha3,ha4,ha5,ha6,ha7,ha8,ha9,ha10,ha11,ha12,ite_true,ite_false]
  grind

theorem spectrum_old_relation_left1 (q e : Int) (hq : 4≤q) (hregion : 5≤e ∧ e≤q+2) :
    LuRazLattice.frequencyPolynomial2 q e + 2*deltaPolynomial q e = spectrumPolynomial2 q e := by
  have ha0 : ¬(e=1) := by omega
  have ha1 : ¬(e=2) := by omega
  have ha2 : ¬(e=3) := by omega
  have ha3 : ¬(e=4) := by omega
  have ha4 : e≤q+2 := by omega
  have ha5 : ¬(e=q+3) := by omega
  have ha6 : e≤2*q := by omega
  have ha7 : ¬(e=2*q+1) := by omega
  have ha8 : ¬(e=2*q+2) := by omega
  have ha9 : e≤3*q := by omega
  have ha10 : ¬(e=3*q+1) := by omega
  have ha11 : e≤4*q-2 := by omega
  have ha12 : ¬(e=4*q-1) := by omega
  simp only [LuRazLattice.frequencyPolynomial2,deltaPolynomial,spectrumPolynomial2,ha0,ha1,ha2,ha3,ha4,ha5,ha6,ha7,ha8,ha9,ha10,ha11,ha12,ite_true,ite_false]
  grind

theorem spectrum_old_relation_q3 (q e : Int) (hq : 4≤q) (hregion : e=q+3) :
    LuRazLattice.frequencyPolynomial2 q e + 2*deltaPolynomial q e = spectrumPolynomial2 q e := by
  have ha0 : ¬(e=1) := by omega
  have ha1 : ¬(e=2) := by omega
  have ha2 : ¬(e=3) := by omega
  have ha3 : ¬(e=4) := by omega
  have ha4 : ¬(e≤q+2) := by omega
  have ha5 : e=q+3 := by omega
  have ha6 : e≤2*q := by omega
  have ha7 : ¬(e=2*q+1) := by omega
  have ha8 : ¬(e=2*q+2) := by omega
  have ha9 : e≤3*q := by omega
  have ha10 : ¬(e=3*q+1) := by omega
  have ha11 : e≤4*q-2 := by omega
  have ha12 : ¬(e=4*q-1) := by omega
  simp only [LuRazLattice.frequencyPolynomial2,deltaPolynomial,spectrumPolynomial2,ha0,ha1,ha2,ha3,ha4,ha5,ha6,ha7,ha8,ha9,ha10,ha11,ha12,ite_true,ite_false]
  grind

theorem spectrum_old_relation_left2 (q e : Int) (hq : 4≤q) (hregion : q+4≤e ∧ e≤2*q) :
    LuRazLattice.frequencyPolynomial2 q e + 2*deltaPolynomial q e = spectrumPolynomial2 q e := by
  have ha0 : ¬(e=1) := by omega
  have ha1 : ¬(e=2) := by omega
  have ha2 : ¬(e=3) := by omega
  have ha3 : ¬(e=4) := by omega
  have ha4 : ¬(e≤q+2) := by omega
  have ha5 : ¬(e=q+3) := by omega
  have ha6 : e≤2*q := by omega
  have ha7 : ¬(e=2*q+1) := by omega
  have ha8 : ¬(e=2*q+2) := by omega
  have ha9 : e≤3*q := by omega
  have ha10 : ¬(e=3*q+1) := by omega
  have ha11 : e≤4*q-2 := by omega
  have ha12 : ¬(e=4*q-1) := by omega
  simp only [LuRazLattice.frequencyPolynomial2,deltaPolynomial,spectrumPolynomial2,ha0,ha1,ha2,ha3,ha4,ha5,ha6,ha7,ha8,ha9,ha10,ha11,ha12,ite_true,ite_false]
  grind

theorem spectrum_old_relation_h1 (q e : Int) (hq : 4≤q) (hregion : e=2*q+1) :
    LuRazLattice.frequencyPolynomial2 q e + 2*deltaPolynomial q e = spectrumPolynomial2 q e := by
  have ha0 : ¬(e=1) := by omega
  have ha1 : ¬(e=2) := by omega
  have ha2 : ¬(e=3) := by omega
  have ha3 : ¬(e=4) := by omega
  have ha4 : ¬(e≤q+2) := by omega
  have ha5 : ¬(e=q+3) := by omega
  have ha6 : ¬(e≤2*q) := by omega
  have ha7 : e=2*q+1 := by omega
  have ha8 : ¬(e=2*q+2) := by omega
  have ha9 : e≤3*q := by omega
  have ha10 : ¬(e=3*q+1) := by omega
  have ha11 : e≤4*q-2 := by omega
  have ha12 : ¬(e=4*q-1) := by omega
  simp only [LuRazLattice.frequencyPolynomial2,deltaPolynomial,spectrumPolynomial2,ha0,ha1,ha2,ha3,ha4,ha5,ha6,ha7,ha8,ha9,ha10,ha11,ha12,ite_true,ite_false]
  grind

theorem spectrum_old_relation_h2 (q e : Int) (hq : 4≤q) (hregion : e=2*q+2) :
    LuRazLattice.frequencyPolynomial2 q e + 2*deltaPolynomial q e = spectrumPolynomial2 q e := by
  have ha0 : ¬(e=1) := by omega
  have ha1 : ¬(e=2) := by omega
  have ha2 : ¬(e=3) := by omega
  have ha3 : ¬(e=4) := by omega
  have ha4 : ¬(e≤q+2) := by omega
  have ha5 : ¬(e=q+3) := by omega
  have ha6 : ¬(e≤2*q) := by omega
  have ha7 : ¬(e=2*q+1) := by omega
  have ha8 : e=2*q+2 := by omega
  have ha9 : e≤3*q := by omega
  have ha10 : ¬(e=3*q+1) := by omega
  have ha11 : e≤4*q-2 := by omega
  have ha12 : ¬(e=4*q-1) := by omega
  simp only [LuRazLattice.frequencyPolynomial2,deltaPolynomial,spectrumPolynomial2,ha0,ha1,ha2,ha3,ha4,ha5,ha6,ha7,ha8,ha9,ha10,ha11,ha12,ite_true,ite_false]
  grind

theorem spectrum_old_relation_right1 (q e : Int) (hq : 4≤q) (hregion : 2*q+3≤e ∧ e≤3*q) :
    LuRazLattice.frequencyPolynomial2 q e + 2*deltaPolynomial q e = spectrumPolynomial2 q e := by
  have ha0 : ¬(e=1) := by omega
  have ha1 : ¬(e=2) := by omega
  have ha2 : ¬(e=3) := by omega
  have ha3 : ¬(e=4) := by omega
  have ha4 : ¬(e≤q+2) := by omega
  have ha5 : ¬(e=q+3) := by omega
  have ha6 : ¬(e≤2*q) := by omega
  have ha7 : ¬(e=2*q+1) := by omega
  have ha8 : ¬(e=2*q+2) := by omega
  have ha9 : e≤3*q := by omega
  have ha10 : ¬(e=3*q+1) := by omega
  have ha11 : e≤4*q-2 := by omega
  have ha12 : ¬(e=4*q-1) := by omega
  simp only [LuRazLattice.frequencyPolynomial2,deltaPolynomial,spectrumPolynomial2,ha0,ha1,ha2,ha3,ha4,ha5,ha6,ha7,ha8,ha9,ha10,ha11,ha12,ite_true,ite_false]
  grind

theorem spectrum_old_relation_r1 (q e : Int) (hq : 4≤q) (hregion : e=3*q+1) :
    LuRazLattice.frequencyPolynomial2 q e + 2*deltaPolynomial q e = spectrumPolynomial2 q e := by
  have ha0 : ¬(e=1) := by omega
  have ha1 : ¬(e=2) := by omega
  have ha2 : ¬(e=3) := by omega
  have ha3 : ¬(e=4) := by omega
  have ha4 : ¬(e≤q+2) := by omega
  have ha5 : ¬(e=q+3) := by omega
  have ha6 : ¬(e≤2*q) := by omega
  have ha7 : ¬(e=2*q+1) := by omega
  have ha8 : ¬(e=2*q+2) := by omega
  have ha9 : ¬(e≤3*q) := by omega
  have ha10 : e=3*q+1 := by omega
  have ha11 : e≤4*q-2 := by omega
  have ha12 : ¬(e=4*q-1) := by omega
  simp only [LuRazLattice.frequencyPolynomial2,deltaPolynomial,spectrumPolynomial2,ha0,ha1,ha2,ha3,ha4,ha5,ha6,ha7,ha8,ha9,ha10,ha11,ha12,ite_true,ite_false]
  grind

theorem spectrum_old_relation_right2 (q e : Int) (hq : 4≤q) (hregion : 3*q+2≤e ∧ e≤4*q-2) :
    LuRazLattice.frequencyPolynomial2 q e + 2*deltaPolynomial q e = spectrumPolynomial2 q e := by
  have ha0 : ¬(e=1) := by omega
  have ha1 : ¬(e=2) := by omega
  have ha2 : ¬(e=3) := by omega
  have ha3 : ¬(e=4) := by omega
  have ha4 : ¬(e≤q+2) := by omega
  have ha5 : ¬(e=q+3) := by omega
  have ha6 : ¬(e≤2*q) := by omega
  have ha7 : ¬(e=2*q+1) := by omega
  have ha8 : ¬(e=2*q+2) := by omega
  have ha9 : ¬(e≤3*q) := by omega
  have ha10 : ¬(e=3*q+1) := by omega
  have ha11 : e≤4*q-2 := by omega
  have ha12 : ¬(e=4*q-1) := by omega
  simp only [LuRazLattice.frequencyPolynomial2,deltaPolynomial,spectrumPolynomial2,ha0,ha1,ha2,ha3,ha4,ha5,ha6,ha7,ha8,ha9,ha10,ha11,ha12,ite_true,ite_false]
  grind

theorem spectrum_old_relation_n1 (q e : Int) (hq : 4≤q) (hregion : e=4*q-1) :
    LuRazLattice.frequencyPolynomial2 q e + 2*deltaPolynomial q e = spectrumPolynomial2 q e := by
  have ha0 : ¬(e=1) := by omega
  have ha1 : ¬(e=2) := by omega
  have ha2 : ¬(e=3) := by omega
  have ha3 : ¬(e=4) := by omega
  have ha4 : ¬(e≤q+2) := by omega
  have ha5 : ¬(e=q+3) := by omega
  have ha6 : ¬(e≤2*q) := by omega
  have ha7 : ¬(e=2*q+1) := by omega
  have ha8 : ¬(e=2*q+2) := by omega
  have ha9 : ¬(e≤3*q) := by omega
  have ha10 : ¬(e=3*q+1) := by omega
  have ha11 : ¬(e≤4*q-2) := by omega
  have ha12 : e=4*q-1 := by omega
  simp only [LuRazLattice.frequencyPolynomial2,deltaPolynomial,spectrumPolynomial2,ha0,ha1,ha2,ha3,ha4,ha5,ha6,ha7,ha8,ha9,ha10,ha11,ha12,ite_true,ite_false]
  grind

theorem spectrum_old_relation_n (q e : Int) (hq : 4≤q) (hregion : e=4*q) :
    LuRazLattice.frequencyPolynomial2 q e + 2*deltaPolynomial q e = spectrumPolynomial2 q e := by
  have ha0 : ¬(e=1) := by omega
  have ha1 : ¬(e=2) := by omega
  have ha2 : ¬(e=3) := by omega
  have ha3 : ¬(e=4) := by omega
  have ha4 : ¬(e≤q+2) := by omega
  have ha5 : ¬(e=q+3) := by omega
  have ha6 : ¬(e≤2*q) := by omega
  have ha7 : ¬(e=2*q+1) := by omega
  have ha8 : ¬(e=2*q+2) := by omega
  have ha9 : ¬(e≤3*q) := by omega
  have ha10 : ¬(e=3*q+1) := by omega
  have ha11 : ¬(e≤4*q-2) := by omega
  have ha12 : ¬(e=4*q-1) := by omega
  simp only [LuRazLattice.frequencyPolynomial2,deltaPolynomial,spectrumPolynomial2,ha0,ha1,ha2,ha3,ha4,ha5,ha6,ha7,ha8,ha9,ha10,ha11,ha12,ite_true,ite_false]
  grind

theorem spectrum_old_relation (q e : Int) (hq : 4≤q) (he : 1≤e) (hen : e≤4*q) :
    LuRazLattice.frequencyPolynomial2 q e + 2*deltaPolynomial q e = spectrumPolynomial2 q e := by
  by_cases hc0 : e=1
  · exact spectrum_old_relation_one q e hq (by omega)
  by_cases hc1 : e=2
  · exact spectrum_old_relation_two q e hq (by omega)
  by_cases hc2 : e=3
  · exact spectrum_old_relation_three q e hq (by omega)
  by_cases hc3 : e=4
  · exact spectrum_old_relation_four q e hq (by omega)
  by_cases hc4 : e≤q+2
  · exact spectrum_old_relation_left1 q e hq (by omega)
  by_cases hc5 : e=q+3
  · exact spectrum_old_relation_q3 q e hq (by omega)
  by_cases hc6 : e≤2*q
  · exact spectrum_old_relation_left2 q e hq (by omega)
  by_cases hc7 : e=2*q+1
  · exact spectrum_old_relation_h1 q e hq (by omega)
  by_cases hc8 : e=2*q+2
  · exact spectrum_old_relation_h2 q e hq (by omega)
  by_cases hc9 : e≤3*q
  · exact spectrum_old_relation_right1 q e hq (by omega)
  by_cases hc10 : e=3*q+1
  · exact spectrum_old_relation_r1 q e hq (by omega)
  by_cases hc11 : e≤4*q-2
  · exact spectrum_old_relation_right2 q e hq (by omega)
  by_cases hc12 : e=4*q-1
  · exact spectrum_old_relation_n1 q e hq (by omega)
  exact spectrum_old_relation_n q e hq (by omega)

end LuRazThreeRow
