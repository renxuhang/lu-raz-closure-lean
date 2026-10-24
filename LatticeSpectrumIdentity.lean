import SpectrumIdentity_one_0
import SpectrumIdentity_two_0
import SpectrumIdentity_three_0
import SpectrumIdentity_four_0
import SpectrumIdentity_left1_0
import SpectrumIdentity_left1_1
import SpectrumIdentity_left1_2
import SpectrumIdentity_q3_0
import SpectrumIdentity_left2_0
import SpectrumIdentity_left2_1
import SpectrumIdentity_left2_2
import SpectrumIdentity_left2_3
import SpectrumIdentity_h1_0
import SpectrumIdentity_h2_0
import SpectrumIdentity_right1_0
import SpectrumIdentity_right1_1
import SpectrumIdentity_right1_2
import SpectrumIdentity_r1_0
import SpectrumIdentity_right2_0
import SpectrumIdentity_right2_1
import SpectrumIdentity_right2_2
import SpectrumIdentity_right2_3
import SpectrumIdentity_n1_0
import SpectrumIdentity_n_0
namespace LuRazLattice
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
def latticeTail2 (q e : Int) : Int := Identity_left1_0.sumTerms q e
def latticeFrequency2 (q e : Int) : Int :=
  if e=1 then Identity_one_0.sumTerms q e else
  if e=2 then Identity_two_0.sumTerms q e else
  if e=3 then Identity_three_0.sumTerms q e else
  if e=4 then Identity_four_0.sumTerms q e else latticeTail2 q e
theorem region_one (q e : Int) (hq : 4≤q) (hl : (1)≤e) (hu : e≤(1)) :
    Identity_one_0.sumTerms q e=(19*q*q+25*q+(-44)) := by
  exact Identity_one_0.cell_identity q e (by omega) (by omega) (by omega)
theorem region_two (q e : Int) (hq : 4≤q) (hl : (2)≤e) (hu : e≤(2)) :
    Identity_two_0.sumTerms q e=(17*q*q+25*q+(-34)) := by
  exact Identity_two_0.cell_identity q e (by omega) (by omega) (by omega)
theorem region_three (q e : Int) (hq : 4≤q) (hl : (3)≤e) (hu : e≤(3)) :
    Identity_three_0.sumTerms q e=(17*q*q+27*q+(-48)) := by
  exact Identity_three_0.cell_identity q e (by omega) (by omega) (by omega)
theorem region_four (q e : Int) (hq : 4≤q) (hl : (4)≤e) (hu : e≤(4)) :
    Identity_four_0.sumTerms q e=(16*q*q+30*q+(-46)) := by
  exact Identity_four_0.cell_identity q e (by omega) (by omega) (by omega)
theorem region_left1 (q e : Int) (hq : 4≤q) (hl : (5)≤e) (hu : e≤(q+2)) :
    latticeTail2 q e=(18*q*q+2*q*e+20*q+(-1)*e*e+(-1)*e+(-20)) := by
  by_cases hcell0 : 0≤(q+(-e)+1)
  ·
    by_cases hcell1 : 0≤(e+(-6))
    ·
      exact Identity_left1_0.cell_identity q e (by omega) (by omega) (by omega) (by omega) (by omega)
    ·
      exact Identity_left1_1.cell_identity q e (by omega) (by omega) (by omega) (by omega) (by omega)
  ·
    exact Identity_left1_2.cell_identity q e (by omega) (by omega) (by omega) (by omega)
theorem region_q3 (q e : Int) (hq : 4≤q) (hl : (q+3)≤e) (hu : e≤(q+3)) :
    latticeTail2 q e=(18*q*q+12*q+(-24)) := by
  exact Identity_q3_0.cell_identity q e (by omega) (by omega) (by omega)
theorem region_left2 (q e : Int) (hq : 4≤q) (hl : (q+4)≤e) (hu : e≤((2)*q)) :
    latticeTail2 q e=(16*q*q+4*q*e+(-10)*q+(-2)*e*e+20*e+(-70)) := by
  by_cases hcell0 : 0≤((2)*q+(-e)+(-1))
  ·
    by_cases hcell1 : 0≤(q+(-e)+4)
    ·
      exact Identity_left2_0.cell_identity q e (by omega) (by omega) (by omega) (by omega) (by omega)
    ·
      exact Identity_left2_1.cell_identity q e (by omega) (by omega) (by omega) (by omega) (by omega)
  ·
    by_cases hcell1 : 0≤(q+(-e)+4)
    ·
      exact Identity_left2_2.cell_identity q e (by omega) (by omega) (by omega) (by omega) (by omega)
    ·
      exact Identity_left2_3.cell_identity q e (by omega) (by omega) (by omega) (by omega) (by omega)
theorem region_h1 (q e : Int) (hq : 4≤q) (hl : ((2)*q+1)≤e) (hu : e≤((2)*q+1)) :
    latticeTail2 q e=(16*q*q+34*q+(-68)) := by
  exact Identity_h1_0.cell_identity q e (by omega) (by omega) (by omega)
theorem region_h2 (q e : Int) (hq : 4≤q) (hl : ((2)*q+2)≤e) (hu : e≤((2)*q+2)) :
    latticeTail2 q e=(16*q*q+30*q+(-52)) := by
  exact Identity_h2_0.cell_identity q e (by omega) (by omega) (by omega)
theorem region_right1 (q e : Int) (hq : 4≤q) (hl : ((2)*q+3)≤e) (hu : e≤((3)*q)) :
    latticeTail2 q e=(12*q*q+4*q*e+26*q+(-1)*e*e+1*e+(-46)) := by
  by_cases hcell0 : 0≤((-2)*q+e+(-4))
  ·
    by_cases hcell1 : 0≤((-3)*q+e)
    ·
      exact Identity_right1_0.cell_identity q e (by omega) (by omega) (by omega) (by omega) (by omega)
    ·
      exact Identity_right1_1.cell_identity q e (by omega) (by omega) (by omega) (by omega) (by omega)
  ·
    exact Identity_right1_2.cell_identity q e (by omega) (by omega) (by omega) (by omega)
theorem region_r1 (q e : Int) (hq : 4≤q) (hl : ((3)*q+1)≤e) (hu : e≤((3)*q+1)) :
    latticeTail2 q e=(17*q*q+33*q+(-54)) := by
  exact Identity_r1_0.cell_identity q e (by omega) (by omega) (by omega)
theorem region_right2 (q e : Int) (hq : 4≤q) (hl : ((3)*q+2)≤e) (hu : e≤((4)*q+(-2))) :
    latticeTail2 q e=((-14)*q*q+16*q*e+36*q+(-2)*e*e+(-2)*e+(-36)) := by
  by_cases hcell0 : 0≤((-3)*q+e+(-3))
  ·
    by_cases hcell1 : 0≤((4)*q+(-e)+(-3))
    ·
      exact Identity_right2_0.cell_identity q e (by omega) (by omega) (by omega) (by omega) (by omega)
    ·
      exact Identity_right2_1.cell_identity q e (by omega) (by omega) (by omega) (by omega) (by omega)
  ·
    by_cases hcell1 : 0≤((4)*q+(-e)+(-3))
    ·
      exact Identity_right2_2.cell_identity q e (by omega) (by omega) (by omega) (by omega) (by omega)
    ·
      exact Identity_right2_3.cell_identity q e (by omega) (by omega) (by omega) (by omega) (by omega)
theorem region_n1 (q e : Int) (hq : 4≤q) (hl : ((4)*q+(-1))≤e) (hu : e≤((4)*q+(-1))) :
    latticeTail2 q e=(18*q*q+28*q+(-40)) := by
  exact Identity_n1_0.cell_identity q e (by omega) (by omega) (by omega)
theorem region_n (q e : Int) (hq : 4≤q) (hl : ((4)*q)≤e) (hu : e≤((4)*q)) :
    latticeTail2 q e=(18*q*q+28*q+(-52)) := by
  exact Identity_n_0.cell_identity q e (by omega) (by omega) (by omega)
def frequencyPolynomial2 (q e : Int) : Int :=
  if e=1 then (19*q*q+25*q+(-44)) else
  if e=2 then (17*q*q+25*q+(-34)) else
  if e=3 then (17*q*q+27*q+(-48)) else
  if e=4 then (16*q*q+30*q+(-46)) else
  if e≤q+2 then (18*q*q+2*q*e+20*q+(-1)*e*e+(-1)*e+(-20)) else
  if e=q+3 then (18*q*q+12*q+(-24)) else
  if e≤2*q then (16*q*q+4*q*e+(-10)*q+(-2)*e*e+20*e+(-70)) else
  if e=2*q+1 then (16*q*q+34*q+(-68)) else
  if e=2*q+2 then (16*q*q+30*q+(-52)) else
  if e≤3*q then (12*q*q+4*q*e+26*q+(-1)*e*e+1*e+(-46)) else
  if e=3*q+1 then (17*q*q+33*q+(-54)) else
  if e≤4*q-2 then ((-14)*q*q+16*q*e+36*q+(-2)*e*e+(-2)*e+(-36)) else
  if e=4*q-1 then (18*q*q+28*q+(-40)) else
  (18*q*q+28*q+(-52))
theorem lattice_spectrum_identity (q e : Int) (hq : 4≤q) (he : 1≤e) (hen : e≤4*q) :
    latticeFrequency2 q e=frequencyPolynomial2 q e := by
  by_cases h0 : e=1
  ·
    simp only [latticeFrequency2,frequencyPolynomial2,ite_eq_left h0]
    exact region_one q e hq (by omega) (by omega)
  ·
    by_cases h1 : e=2
    ·
      simp only [latticeFrequency2,frequencyPolynomial2,ite_eq_right h0,ite_eq_left h1]
      exact region_two q e hq (by omega) (by omega)
    ·
      by_cases h2 : e=3
      ·
        simp only [latticeFrequency2,frequencyPolynomial2,ite_eq_right h0,ite_eq_right h1,ite_eq_left h2]
        exact region_three q e hq (by omega) (by omega)
      ·
        by_cases h3 : e=4
        ·
          simp only [latticeFrequency2,frequencyPolynomial2,ite_eq_right h0,ite_eq_right h1,ite_eq_right h2,ite_eq_left h3]
          exact region_four q e hq (by omega) (by omega)
        ·
          by_cases h4 : e≤q+2
          ·
            simp only [latticeFrequency2,frequencyPolynomial2,ite_eq_right h0,ite_eq_right h1,ite_eq_right h2,ite_eq_right h3,ite_eq_left h4]
            exact region_left1 q e hq (by omega) (by omega)
          ·
            by_cases h5 : e=q+3
            ·
              simp only [latticeFrequency2,frequencyPolynomial2,ite_eq_right h0,ite_eq_right h1,ite_eq_right h2,ite_eq_right h3,ite_eq_right h4,ite_eq_left h5]
              exact region_q3 q e hq (by omega) (by omega)
            ·
              by_cases h6 : e≤2*q
              ·
                simp only [latticeFrequency2,frequencyPolynomial2,ite_eq_right h0,ite_eq_right h1,ite_eq_right h2,ite_eq_right h3,ite_eq_right h4,ite_eq_right h5,ite_eq_left h6]
                exact region_left2 q e hq (by omega) (by omega)
              ·
                by_cases h7 : e=2*q+1
                ·
                  simp only [latticeFrequency2,frequencyPolynomial2,ite_eq_right h0,ite_eq_right h1,ite_eq_right h2,ite_eq_right h3,ite_eq_right h4,ite_eq_right h5,ite_eq_right h6,ite_eq_left h7]
                  exact region_h1 q e hq (by omega) (by omega)
                ·
                  by_cases h8 : e=2*q+2
                  ·
                    simp only [latticeFrequency2,frequencyPolynomial2,ite_eq_right h0,ite_eq_right h1,ite_eq_right h2,ite_eq_right h3,ite_eq_right h4,ite_eq_right h5,ite_eq_right h6,ite_eq_right h7,ite_eq_left h8]
                    exact region_h2 q e hq (by omega) (by omega)
                  ·
                    by_cases h9 : e≤3*q
                    ·
                      simp only [latticeFrequency2,frequencyPolynomial2,ite_eq_right h0,ite_eq_right h1,ite_eq_right h2,ite_eq_right h3,ite_eq_right h4,ite_eq_right h5,ite_eq_right h6,ite_eq_right h7,ite_eq_right h8,ite_eq_left h9]
                      exact region_right1 q e hq (by omega) (by omega)
                    ·
                      by_cases h10 : e=3*q+1
                      ·
                        simp only [latticeFrequency2,frequencyPolynomial2,ite_eq_right h0,ite_eq_right h1,ite_eq_right h2,ite_eq_right h3,ite_eq_right h4,ite_eq_right h5,ite_eq_right h6,ite_eq_right h7,ite_eq_right h8,ite_eq_right h9,ite_eq_left h10]
                        exact region_r1 q e hq (by omega) (by omega)
                      ·
                        by_cases h11 : e≤4*q-2
                        ·
                          simp only [latticeFrequency2,frequencyPolynomial2,ite_eq_right h0,ite_eq_right h1,ite_eq_right h2,ite_eq_right h3,ite_eq_right h4,ite_eq_right h5,ite_eq_right h6,ite_eq_right h7,ite_eq_right h8,ite_eq_right h9,ite_eq_right h10,ite_eq_left h11]
                          exact region_right2 q e hq (by omega) (by omega)
                        ·
                          by_cases h12 : e=4*q-1
                          ·
                            simp only [latticeFrequency2,frequencyPolynomial2,ite_eq_right h0,ite_eq_right h1,ite_eq_right h2,ite_eq_right h3,ite_eq_right h4,ite_eq_right h5,ite_eq_right h6,ite_eq_right h7,ite_eq_right h8,ite_eq_right h9,ite_eq_right h10,ite_eq_right h11,ite_eq_left h12]
                            exact region_n1 q e hq (by omega) (by omega)
                          ·
                            simp only [latticeFrequency2,frequencyPolynomial2,ite_eq_right h0,ite_eq_right h1,ite_eq_right h2,ite_eq_right h3,ite_eq_right h4,ite_eq_right h5,ite_eq_right h6,ite_eq_right h7,ite_eq_right h8,ite_eq_right h9,ite_eq_right h10,ite_eq_right h11,ite_eq_right h12]
                            exact region_n q e hq (by omega) (by omega)
#print axioms lattice_spectrum_identity
end LuRazLattice
