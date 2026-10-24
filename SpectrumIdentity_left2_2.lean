import LatticeCounting
namespace LuRazLattice
namespace Identity_left2_2
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
def term_0 (q e : Int) : Int := (if (((3)*q+2)≤(e) ∧ (e)≤((4)*q)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_0_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_0 q e=(0*q+0*e+0) := by
  have v0 : ¬(((3)*q+2)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_0,tri2,pos,v0]
  grind
def term_1 (q e : Int) : Int := (if ((5)≤(e) ∧ (e)≤(q+2)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_1_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_1 q e=(0*q+0*e+0) := by
  have v0 : ¬((5)≤(e) ∧ (e)≤(q+2)) := by omega
  simp only [term_1,tri2,pos,v0]
  grind
def term_2 (q e : Int) : Int := (if ((5)≤(e) ∧ (e)≤(q+2)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_2_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_2 q e=(0*q+0*e+0) := by
  have v0 : ¬((5)≤(e) ∧ (e)≤(q+2)) := by omega
  simp only [term_2,tri2,pos,v0]
  grind
def term_3 (q e : Int) : Int := (if (((3)*q+2)≤(e) ∧ (e)≤((4)*q)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_3_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_3 q e=(0*q+0*e+0) := by
  have v0 : ¬(((3)*q+2)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_3,tri2,pos,v0]
  grind
def term_4 (q e : Int) : Int := (((-1))*(if ((5)≤(e) ∧ (e)≤(q+2) ∧ ((3)*q+2)≤(e) ∧ (e)≤((4)*q)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int)))
theorem term_4_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_4 q e=(0:Int) := by
  have v0 : ¬((5)≤(e) ∧ (e)≤(q+2) ∧ ((3)*q+2)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_4,tri2,pos,v0]
  grind
def term_5 (q e : Int) : Int := (if (((2)*q+1)≤(e) ∧ (e)≤((4)*q)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_5_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_5 q e=(0*q+0*e+0) := by
  have v0 : ¬(((2)*q+1)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_5,tri2,pos,v0]
  grind
def term_6 (q e : Int) : Int := (if ((5)≤(e) ∧ (e)≤(q+2)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_6_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_6 q e=(0*q+0*e+0) := by
  have v0 : ¬((5)≤(e) ∧ (e)≤(q+2)) := by omega
  simp only [term_6,tri2,pos,v0]
  grind
def term_7 (q e : Int) : Int := (if (((2)*q+1)≤(e) ∧ (e)≤((4)*q)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_7_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_7 q e=(0*q+0*e+0) := by
  have v0 : ¬(((2)*q+1)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_7,tri2,pos,v0]
  grind
def term_8 (q e : Int) : Int := (((-1))*(if ((5)≤(e) ∧ (e)≤(q+2) ∧ ((2)*q+1)≤(e) ∧ (e)≤((4)*q)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int)))
theorem term_8_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_8 q e=(0:Int) := by
  have v0 : ¬((5)≤(e) ∧ (e)≤(q+2) ∧ ((2)*q+1)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_8,tri2,pos,v0]
  grind
def term_9 (q e : Int) : Int := (if ((5)≤(e) ∧ (e)≤((2)*q+2)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_9_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_9 q e=(2) := by
  have v0 : ((5)≤(e) ∧ (e)≤((2)*q+2)) := by omega
  have v1 : ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) := by omega
  have v2 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_9,tri2,pos,v0,v1,v2]
  grind
def term_10 (q e : Int) : Int := (if (((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_10_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_10 q e=(0*q+0*e+0) := by
  have v0 : ¬(((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)) := by omega
  simp only [term_10,tri2,pos,v0]
  grind
def term_11 (q e : Int) : Int := (((-1))*(if ((5)≤(e) ∧ (e)≤((2)*q+2) ∧ ((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int)))
theorem term_11_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_11 q e=(0:Int) := by
  have v0 : ¬((5)≤(e) ∧ (e)≤((2)*q+2) ∧ ((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)) := by omega
  simp only [term_11,tri2,pos,v0]
  grind
def term_12 (q e : Int) : Int := (if ((5)≤(e) ∧ (e)≤((2)*q+2)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_12_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_12 q e=(2) := by
  have v0 : ((5)≤(e) ∧ (e)≤((2)*q+2)) := by omega
  have v1 : ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) := by omega
  have v2 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_12,tri2,pos,v0,v1,v2]
  grind
def term_13 (q e : Int) : Int := (if (((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_13_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_13 q e=(0*q+0*e+0) := by
  have v0 : ¬(((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)) := by omega
  simp only [term_13,tri2,pos,v0]
  grind
def term_14 (q e : Int) : Int := (if (((3)*q+2)≤(e) ∧ (e)≤((4)*q)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_14_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_14 q e=(0*q+0*e+0) := by
  have v0 : ¬(((3)*q+2)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_14,tri2,pos,v0]
  grind
def term_15 (q e : Int) : Int := (((-1))*(if ((5)≤(e) ∧ (e)≤((2)*q+2) ∧ ((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int)))
theorem term_15_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_15 q e=(0:Int) := by
  have v0 : ¬((5)≤(e) ∧ (e)≤((2)*q+2) ∧ ((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)) := by omega
  simp only [term_15,tri2,pos,v0]
  grind
def term_16 (q e : Int) : Int := (((-1))*(if ((5)≤(e) ∧ (e)≤((2)*q+2) ∧ ((3)*q+2)≤(e) ∧ (e)≤((4)*q)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int)))
theorem term_16_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_16 q e=(0:Int) := by
  have v0 : ¬((5)≤(e) ∧ (e)≤((2)*q+2) ∧ ((3)*q+2)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_16,tri2,pos,v0]
  grind
def term_17 (q e : Int) : Int := (((-1))*(if (((3)*q+1)≤(e) ∧ (e)≤((3)*q+1) ∧ ((3)*q+2)≤(e) ∧ (e)≤((4)*q)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int)))
theorem term_17_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_17 q e=(0:Int) := by
  have v0 : ¬(((3)*q+1)≤(e) ∧ (e)≤((3)*q+1) ∧ ((3)*q+2)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_17,tri2,pos,v0]
  grind
def term_18 (q e : Int) : Int := (if ((5)≤(e) ∧ (e)≤((2)*q+2) ∧ ((3)*q+1)≤(e) ∧ (e)≤((3)*q+1) ∧ ((3)*q+2)≤(e) ∧ (e)≤((4)*q)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_18_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_18 q e=(0*q+0*e+0) := by
  have v0 : ¬((5)≤(e) ∧ (e)≤((2)*q+2) ∧ ((3)*q+1)≤(e) ∧ (e)≤((3)*q+1) ∧ ((3)*q+2)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_18,tri2,pos,v0]
  grind
def term_19 (q e : Int) : Int := (if (((2)*q+3)≤(e) ∧ (e)≤((4)*q)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_19_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_19 q e=(0*q+0*e+0) := by
  have v0 : ¬(((2)*q+3)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_19,tri2,pos,v0]
  grind
def term_20 (q e : Int) : Int := (if ((5)≤(e) ∧ (e)≤(q+2)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_20_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_20 q e=(0*q+0*e+0) := by
  have v0 : ¬((5)≤(e) ∧ (e)≤(q+2)) := by omega
  simp only [term_20,tri2,pos,v0]
  grind
def term_21 (q e : Int) : Int := (if (((2)*q+3)≤(e) ∧ (e)≤((4)*q)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_21_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_21 q e=(0*q+0*e+0) := by
  have v0 : ¬(((2)*q+3)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_21,tri2,pos,v0]
  grind
def term_22 (q e : Int) : Int := (((-1))*(if ((5)≤(e) ∧ (e)≤(q+2) ∧ ((2)*q+3)≤(e) ∧ (e)≤((4)*q)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int)))
theorem term_22_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_22 q e=(0:Int) := by
  have v0 : ¬((5)≤(e) ∧ (e)≤(q+2) ∧ ((2)*q+3)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_22,tri2,pos,v0]
  grind
def term_23 (q e : Int) : Int := (if ((5)≤(e) ∧ (e)≤((4)*q)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_23_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_23 q e=(2) := by
  have v0 : ((5)≤(e) ∧ (e)≤((4)*q)) := by omega
  have v1 : ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) := by omega
  have v2 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_23,tri2,pos,v0,v1,v2]
  grind
def term_24 (q e : Int) : Int := (if ((5)≤(e) ∧ (e)≤((2)*q+2)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_24_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_24 q e=(2) := by
  have v0 : ((5)≤(e) ∧ (e)≤((2)*q+2)) := by omega
  have v1 : ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) := by omega
  have v2 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_24,tri2,pos,v0,v1,v2]
  grind
def term_25 (q e : Int) : Int := (if (((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_25_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_25 q e=(0*q+0*e+0) := by
  have v0 : ¬(((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)) := by omega
  simp only [term_25,tri2,pos,v0]
  grind
def term_26 (q e : Int) : Int := (((-1))*(if ((5)≤(e) ∧ (e)≤((2)*q+2) ∧ ((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int)))
theorem term_26_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_26 q e=(0:Int) := by
  have v0 : ¬((5)≤(e) ∧ (e)≤((2)*q+2) ∧ ((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)) := by omega
  simp only [term_26,tri2,pos,v0]
  grind
def term_27 (q e : Int) : Int := (if ((5)≤(e) ∧ (e)≤((2)*q+2)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_27_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_27 q e=(2) := by
  have v0 : ((5)≤(e) ∧ (e)≤((2)*q+2)) := by omega
  have v1 : ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) := by omega
  have v2 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_27,tri2,pos,v0,v1,v2]
  grind
def term_28 (q e : Int) : Int := (if (((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_28_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_28 q e=(0*q+0*e+0) := by
  have v0 : ¬(((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)) := by omega
  simp only [term_28,tri2,pos,v0]
  grind
def term_29 (q e : Int) : Int := (if (((3)*q+2)≤(e) ∧ (e)≤((4)*q)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_29_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_29 q e=(0*q+0*e+0) := by
  have v0 : ¬(((3)*q+2)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_29,tri2,pos,v0]
  grind
def term_30 (q e : Int) : Int := (((-1))*(if ((5)≤(e) ∧ (e)≤((2)*q+2) ∧ ((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int)))
theorem term_30_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_30 q e=(0:Int) := by
  have v0 : ¬((5)≤(e) ∧ (e)≤((2)*q+2) ∧ ((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)) := by omega
  simp only [term_30,tri2,pos,v0]
  grind
def term_31 (q e : Int) : Int := (((-1))*(if ((5)≤(e) ∧ (e)≤((2)*q+2) ∧ ((3)*q+2)≤(e) ∧ (e)≤((4)*q)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int)))
theorem term_31_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_31 q e=(0:Int) := by
  have v0 : ¬((5)≤(e) ∧ (e)≤((2)*q+2) ∧ ((3)*q+2)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_31,tri2,pos,v0]
  grind
def term_32 (q e : Int) : Int := (((-1))*(if (((3)*q+1)≤(e) ∧ (e)≤((3)*q+1) ∧ ((3)*q+2)≤(e) ∧ (e)≤((4)*q)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int)))
theorem term_32_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_32 q e=(0:Int) := by
  have v0 : ¬(((3)*q+1)≤(e) ∧ (e)≤((3)*q+1) ∧ ((3)*q+2)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_32,tri2,pos,v0]
  grind
def term_33 (q e : Int) : Int := (if ((5)≤(e) ∧ (e)≤((2)*q+2) ∧ ((3)*q+1)≤(e) ∧ (e)≤((3)*q+1) ∧ ((3)*q+2)≤(e) ∧ (e)≤((4)*q)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_33_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_33 q e=(0*q+0*e+0) := by
  have v0 : ¬((5)≤(e) ∧ (e)≤((2)*q+2) ∧ ((3)*q+1)≤(e) ∧ (e)≤((3)*q+1) ∧ ((3)*q+2)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_33,tri2,pos,v0]
  grind
def term_34 (q e : Int) : Int := (if ((5)≤(e)) then (if ((4)≤(q+1) ∧ (max (4) (e))≤(q+1)) then ((((tri2 ((((q+1)-(0:Int))+(1))-(4)))-(tri2 (((q+1)-(0:Int))-(q+1))))-(tri2 (((max (4) (e))-(0:Int))-(4))))+(tri2 ((((max (4) (e))-(0:Int))-(q+1))-(1)))) else (0:Int)) else (0:Int))
theorem term_34_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_34 q e=(0*q+0*e+0) := by
  have v0 : ((5)≤(e)) := by omega
  have v1 : max (4) (e)=(e) := by omega
  have v2 : ¬((4)≤(q+1) ∧ (max (4) (e))≤(q+1)) := by omega
  have v3 : ¬((4)≤(q+1) ∧ (e)≤(q+1)) := by omega
  simp only [term_34,tri2,pos,v0,v1,v2,v3]
  grind
def term_35 (q e : Int) : Int := (if ((e)≤((4)*q)) then (if ((4)≤(min (q+1) ((-2)*q+e)) ∧ (4)≤(q+1)) then ((((tri2 ((((q+1)-(0:Int))+(1))-(4)))-(tri2 (((q+1)-(0:Int))-(min (q+1) ((-2)*q+e)))))-(tri2 (((4)-(0:Int))-(4))))+(tri2 ((((4)-(0:Int))-(min (q+1) ((-2)*q+e)))-(1)))) else (0:Int)) else (0:Int))
theorem term_35_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_35 q e=(0*q+0*e+0) := by
  have v0 : ((e)≤((4)*q)) := by omega
  have v1 : min (q+1) ((-2)*q+e)=((-2)*q+e) := by omega
  have v2 : ¬((4)≤(min (q+1) ((-2)*q+e)) ∧ (4)≤(q+1)) := by omega
  have v3 : ¬((4)≤((-2)*q+e) ∧ (4)≤(q+1)) := by omega
  simp only [term_35,tri2,pos,v0,v1,v2,v3]
  grind
def term_36 (q e : Int) : Int := (((-1))*(if ((5)≤(e) ∧ (e)≤((4)*q)) then (if ((4)≤(min (q+1) ((-2)*q+e)) ∧ (max (4) (e))≤(q+1)) then ((((tri2 ((((q+1)-(0:Int))+(1))-(4)))-(tri2 (((q+1)-(0:Int))-(min (q+1) ((-2)*q+e)))))-(tri2 (((max (4) (e))-(0:Int))-(4))))+(tri2 ((((max (4) (e))-(0:Int))-(min (q+1) ((-2)*q+e)))-(1)))) else (0:Int)) else (0:Int)))
theorem term_36_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_36 q e=(0:Int) := by
  have v0 : ((5)≤(e) ∧ (e)≤((4)*q)) := by omega
  have v1 : min (q+1) ((-2)*q+e)=((-2)*q+e) := by omega
  have v2 : max (4) (e)=(e) := by omega
  have v3 : ¬((4)≤(min (q+1) ((-2)*q+e)) ∧ (max (4) (e))≤(q+1)) := by omega
  have v4 : ¬((4)≤((-2)*q+e) ∧ (e)≤(q+1)) := by omega
  simp only [term_36,tri2,pos,v0,v1,v2,v3,v4]
  grind
def term_37 (q e : Int) : Int := (if ((5)≤(e)) then (if ((q+3)≤((2)*q+1) ∧ (max (4) (e))≤(q+1)) then ((((tri2 ((((q+1)-(0:Int))+(1))-(q+3)))-(tri2 (((q+1)-(0:Int))-((2)*q+1))))-(tri2 (((max (4) (e))-(0:Int))-(q+3))))+(tri2 ((((max (4) (e))-(0:Int))-((2)*q+1))-(1)))) else (0:Int)) else (0:Int))
theorem term_37_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_37 q e=(0*q+0*e+0) := by
  have v0 : ((5)≤(e)) := by omega
  have v1 : max (4) (e)=(e) := by omega
  have v2 : ¬((q+3)≤((2)*q+1) ∧ (max (4) (e))≤(q+1)) := by omega
  have v3 : ¬((q+3)≤((2)*q+1) ∧ (e)≤(q+1)) := by omega
  simp only [term_37,tri2,pos,v0,v1,v2,v3]
  grind
def term_38 (q e : Int) : Int := (if ((e)≤((4)*q)) then (if ((q+3)≤(min ((2)*q+1) ((-2)*q+e+1)) ∧ (4)≤(q+1)) then ((((tri2 ((((q+1)-(0:Int))+(1))-(q+3)))-(tri2 (((q+1)-(0:Int))-(min ((2)*q+1) ((-2)*q+e+1)))))-(tri2 (((4)-(0:Int))-(q+3))))+(tri2 ((((4)-(0:Int))-(min ((2)*q+1) ((-2)*q+e+1)))-(1)))) else (0:Int)) else (0:Int))
theorem term_38_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_38 q e=(0*q+0*e+0) := by
  have v0 : ((e)≤((4)*q)) := by omega
  have v1 : min ((2)*q+1) ((-2)*q+e+1)=((-2)*q+e+1) := by omega
  have v2 : ¬((q+3)≤(min ((2)*q+1) ((-2)*q+e+1)) ∧ (4)≤(q+1)) := by omega
  have v3 : ¬((q+3)≤((-2)*q+e+1) ∧ (4)≤(q+1)) := by omega
  simp only [term_38,tri2,pos,v0,v1,v2,v3]
  grind
def term_39 (q e : Int) : Int := (((-1))*(if ((5)≤(e) ∧ (e)≤((4)*q)) then (if ((q+3)≤(min ((2)*q+1) ((-2)*q+e+1)) ∧ (max (4) (e))≤(q+1)) then ((((tri2 ((((q+1)-(0:Int))+(1))-(q+3)))-(tri2 (((q+1)-(0:Int))-(min ((2)*q+1) ((-2)*q+e+1)))))-(tri2 (((max (4) (e))-(0:Int))-(q+3))))+(tri2 ((((max (4) (e))-(0:Int))-(min ((2)*q+1) ((-2)*q+e+1)))-(1)))) else (0:Int)) else (0:Int)))
theorem term_39_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_39 q e=(0:Int) := by
  have v0 : ((5)≤(e) ∧ (e)≤((4)*q)) := by omega
  have v1 : min ((2)*q+1) ((-2)*q+e+1)=((-2)*q+e+1) := by omega
  have v2 : max (4) (e)=(e) := by omega
  have v3 : ¬((q+3)≤(min ((2)*q+1) ((-2)*q+e+1)) ∧ (max (4) (e))≤(q+1)) := by omega
  have v4 : ¬((q+3)≤((-2)*q+e+1) ∧ (e)≤(q+1)) := by omega
  simp only [term_39,tri2,pos,v0,v1,v2,v3,v4]
  grind
def term_40 (q e : Int) : Int := (if ((5)≤(e)) then (if ((4)≤(q+1) ∧ (max (q+3) (e))≤((2)*q+1)) then ((((tri2 (((((2)*q+1)-(0:Int))+(1))-(4)))-(tri2 ((((2)*q+1)-(0:Int))-(q+1))))-(tri2 (((max (q+3) (e))-(0:Int))-(4))))+(tri2 ((((max (q+3) (e))-(0:Int))-(q+1))-(1)))) else (0:Int)) else (0:Int))
theorem term_40_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_40 q e=(4*q*q+(-2)*q*e+(-4)*q+4*e+(-8)) := by
  have v0 : ((5)≤(e)) := by omega
  have v1 : max (q+3) (e)=(e) := by omega
  have v2 : ((4)≤(q+1) ∧ (max (q+3) (e))≤((2)*q+1)) := by omega
  have v3 : ((4)≤(q+1) ∧ (e)≤((2)*q+1)) := by omega
  have v4 : max (0:Int) (((((2)*q+1)-(0:Int))+(1))-(4))=((2)*q+(-2)) := by omega
  have v5 : max (0:Int) ((((2)*q+1)-(0:Int))-(q+1))=(q) := by omega
  have v6 : max (0:Int) (((max (q+3) (e))-(0:Int))-(4))=(e+(-4)) := by omega
  have v7 : max (0:Int) (((e)-(0:Int))-(4))=(e+(-4)) := by omega
  have v8 : max (0:Int) ((((max (q+3) (e))-(0:Int))-(q+1))-(1))=((-q)+e+(-2)) := by omega
  have v9 : max (0:Int) ((((e)-(0:Int))-(q+1))-(1))=((-q)+e+(-2)) := by omega
  simp only [term_40,tri2,pos,v0,v1,v2,v3,v4,v5,v6,v7,v8,v9]
  grind
def term_41 (q e : Int) : Int := (if ((e)≤((4)*q)) then (if ((4)≤(min (q+1) ((-2)*q+e)) ∧ (q+3)≤((2)*q+1)) then ((((tri2 (((((2)*q+1)-(0:Int))+(1))-(4)))-(tri2 ((((2)*q+1)-(0:Int))-(min (q+1) ((-2)*q+e)))))-(tri2 (((q+3)-(0:Int))-(4))))+(tri2 ((((q+3)-(0:Int))-(min (q+1) ((-2)*q+e)))-(1)))) else (0:Int)) else (0:Int))
theorem term_41_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_41 q e=(0*q+0*e+0) := by
  have v0 : ((e)≤((4)*q)) := by omega
  have v1 : min (q+1) ((-2)*q+e)=((-2)*q+e) := by omega
  have v2 : ¬((4)≤(min (q+1) ((-2)*q+e)) ∧ (q+3)≤((2)*q+1)) := by omega
  have v3 : ¬((4)≤((-2)*q+e) ∧ (q+3)≤((2)*q+1)) := by omega
  simp only [term_41,tri2,pos,v0,v1,v2,v3]
  grind
def term_42 (q e : Int) : Int := (((-1))*(if ((5)≤(e) ∧ (e)≤((4)*q)) then (if ((4)≤(min (q+1) ((-2)*q+e)) ∧ (max (q+3) (e))≤((2)*q+1)) then ((((tri2 (((((2)*q+1)-(0:Int))+(1))-(4)))-(tri2 ((((2)*q+1)-(0:Int))-(min (q+1) ((-2)*q+e)))))-(tri2 (((max (q+3) (e))-(0:Int))-(4))))+(tri2 ((((max (q+3) (e))-(0:Int))-(min (q+1) ((-2)*q+e)))-(1)))) else (0:Int)) else (0:Int)))
theorem term_42_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_42 q e=(0:Int) := by
  have v0 : ((5)≤(e) ∧ (e)≤((4)*q)) := by omega
  have v1 : min (q+1) ((-2)*q+e)=((-2)*q+e) := by omega
  have v2 : max (q+3) (e)=(e) := by omega
  have v3 : ¬((4)≤(min (q+1) ((-2)*q+e)) ∧ (max (q+3) (e))≤((2)*q+1)) := by omega
  have v4 : ¬((4)≤((-2)*q+e) ∧ (e)≤((2)*q+1)) := by omega
  simp only [term_42,tri2,pos,v0,v1,v2,v3,v4]
  grind
def term_43 (q e : Int) : Int := (if ((5)≤(e)) then (if ((q+3)≤((2)*q+1) ∧ (max (q+3) (e))≤((2)*q+1)) then ((((tri2 (((((2)*q+1)-(0:Int))+(1))-(q+3)))-(tri2 ((((2)*q+1)-(0:Int))-((2)*q+1))))-(tri2 (((max (q+3) (e))-(0:Int))-(q+3))))+(tri2 ((((max (q+3) (e))-(0:Int))-((2)*q+1))-(1)))) else (0:Int)) else (0:Int))
theorem term_43_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_43 q e=(2*q*e+(-6)*q+(-1)*e*e+5*e+(-6)) := by
  have v0 : ((5)≤(e)) := by omega
  have v1 : max (q+3) (e)=(e) := by omega
  have v2 : ((q+3)≤((2)*q+1) ∧ (max (q+3) (e))≤((2)*q+1)) := by omega
  have v3 : ((q+3)≤((2)*q+1) ∧ (e)≤((2)*q+1)) := by omega
  have v4 : max (0:Int) (((((2)*q+1)-(0:Int))+(1))-(q+3))=(q+(-1)) := by omega
  have v5 : max (0:Int) ((((2)*q+1)-(0:Int))-((2)*q+1))=(0:Int) := by omega
  have v6 : max (0:Int) (((max (q+3) (e))-(0:Int))-(q+3))=((-q)+e+(-3)) := by omega
  have v7 : max (0:Int) (((e)-(0:Int))-(q+3))=((-q)+e+(-3)) := by omega
  have v8 : max (0:Int) ((((max (q+3) (e))-(0:Int))-((2)*q+1))-(1))=(0:Int) := by omega
  have v9 : max (0:Int) ((((e)-(0:Int))-((2)*q+1))-(1))=(0:Int) := by omega
  simp only [term_43,tri2,pos,v0,v1,v2,v3,v4,v5,v6,v7,v8,v9]
  grind
def term_44 (q e : Int) : Int := (if ((e)≤((4)*q)) then (if ((q+3)≤(min ((2)*q+1) ((-2)*q+e+1)) ∧ (q+3)≤((2)*q+1)) then ((((tri2 (((((2)*q+1)-(0:Int))+(1))-(q+3)))-(tri2 ((((2)*q+1)-(0:Int))-(min ((2)*q+1) ((-2)*q+e+1)))))-(tri2 (((q+3)-(0:Int))-(q+3))))+(tri2 ((((q+3)-(0:Int))-(min ((2)*q+1) ((-2)*q+e+1)))-(1)))) else (0:Int)) else (0:Int))
theorem term_44_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_44 q e=(0*q+0*e+0) := by
  have v0 : ((e)≤((4)*q)) := by omega
  have v1 : min ((2)*q+1) ((-2)*q+e+1)=((-2)*q+e+1) := by omega
  have v2 : ¬((q+3)≤(min ((2)*q+1) ((-2)*q+e+1)) ∧ (q+3)≤((2)*q+1)) := by omega
  have v3 : ¬((q+3)≤((-2)*q+e+1) ∧ (q+3)≤((2)*q+1)) := by omega
  simp only [term_44,tri2,pos,v0,v1,v2,v3]
  grind
def term_45 (q e : Int) : Int := (((-1))*(if ((5)≤(e) ∧ (e)≤((4)*q)) then (if ((q+3)≤(min ((2)*q+1) ((-2)*q+e+1)) ∧ (max (q+3) (e))≤((2)*q+1)) then ((((tri2 (((((2)*q+1)-(0:Int))+(1))-(q+3)))-(tri2 ((((2)*q+1)-(0:Int))-(min ((2)*q+1) ((-2)*q+e+1)))))-(tri2 (((max (q+3) (e))-(0:Int))-(q+3))))+(tri2 ((((max (q+3) (e))-(0:Int))-(min ((2)*q+1) ((-2)*q+e+1)))-(1)))) else (0:Int)) else (0:Int)))
theorem term_45_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_45 q e=(0:Int) := by
  have v0 : ((5)≤(e) ∧ (e)≤((4)*q)) := by omega
  have v1 : min ((2)*q+1) ((-2)*q+e+1)=((-2)*q+e+1) := by omega
  have v2 : max (q+3) (e)=(e) := by omega
  have v3 : ¬((q+3)≤(min ((2)*q+1) ((-2)*q+e+1)) ∧ (max (q+3) (e))≤((2)*q+1)) := by omega
  have v4 : ¬((q+3)≤((-2)*q+e+1) ∧ (e)≤((2)*q+1)) := by omega
  simp only [term_45,tri2,pos,v0,v1,v2,v3,v4]
  grind
def term_46 (q e : Int) : Int := (((-1))*(if (((4)*q)≤(e) ∧ (e)≤((4)*q)) then (if ((q+3)≤(q+3) ∧ (q+3)≤(q+3)) then (((2)*(max (0:Int) (((q+3)-(q+3))+(1))))*(max (0:Int) (((q+3)-(q+3))+(1)))) else (0:Int)) else (0:Int)))
theorem term_46_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_46 q e=(0:Int) := by
  have v0 : ¬(((4)*q)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_46,tri2,pos,v0]
  grind
def term_47 (q e : Int) : Int := (if ((5)≤(e) ∧ (e)≤(q+3)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_47_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_47 q e=(0*q+0*e+0) := by
  have v0 : ¬((5)≤(e) ∧ (e)≤(q+3)) := by omega
  simp only [term_47,tri2,pos,v0]
  grind
def term_48 (q e : Int) : Int := (if (((3)*q+2)≤(e) ∧ (e)≤((4)*q)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_48_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_48 q e=(0*q+0*e+0) := by
  have v0 : ¬(((3)*q+2)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_48,tri2,pos,v0]
  grind
def term_49 (q e : Int) : Int := (((-1))*(if ((5)≤(e) ∧ (e)≤(q+3) ∧ ((3)*q+2)≤(e) ∧ (e)≤((4)*q)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int)))
theorem term_49_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_49 q e=(0:Int) := by
  have v0 : ¬((5)≤(e) ∧ (e)≤(q+3) ∧ ((3)*q+2)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_49,tri2,pos,v0]
  grind
def term_50 (q e : Int) : Int := (if ((5)≤(e)) then (if ((max (4) (e))≤(q+1) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((q+1)-(max (4) (e)))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_50_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_50 q e=(0*q+0*e+0) := by
  have v0 : ((5)≤(e)) := by omega
  have v1 : max (4) (e)=(e) := by omega
  have v2 : ¬((max (4) (e))≤(q+1) ∧ (0:Int)≤(0:Int)) := by omega
  have v3 : ¬((e)≤(q+1) ∧ (0:Int)≤(0:Int)) := by omega
  simp only [term_50,tri2,pos,v0,v1,v2,v3]
  grind
def term_51 (q e : Int) : Int := (if (((2)*q+1)≤(e) ∧ (e)≤((4)*q)) then (if ((4)≤(q+1) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((q+1)-(4))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_51_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_51 q e=(0*q+0*e+0) := by
  have v0 : ¬(((2)*q+1)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_51,tri2,pos,v0]
  grind
def term_52 (q e : Int) : Int := (((-1))*(if ((5)≤(e) ∧ ((2)*q+1)≤(e) ∧ (e)≤((4)*q)) then (if ((max (4) (e))≤(q+1) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((q+1)-(max (4) (e)))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int)))
theorem term_52_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_52 q e=(0:Int) := by
  have v0 : ¬((5)≤(e) ∧ ((2)*q+1)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_52,tri2,pos,v0]
  grind
def term_53 (q e : Int) : Int := (if ((5)≤(e)) then (if ((max (q+3) (e))≤((2)*q+(-1)) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) ((((2)*q+(-1))-(max (q+3) (e)))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_53_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_53 q e=(0*q+0*e+0) := by
  have v0 : ((5)≤(e)) := by omega
  have v1 : max (q+3) (e)=(e) := by omega
  have v2 : ¬((max (q+3) (e))≤((2)*q+(-1)) ∧ (0:Int)≤(0:Int)) := by omega
  have v3 : ¬((e)≤((2)*q+(-1)) ∧ (0:Int)≤(0:Int)) := by omega
  simp only [term_53,tri2,pos,v0,v1,v2,v3]
  grind
def term_54 (q e : Int) : Int := (if (((2)*q+1)≤(e) ∧ (e)≤((4)*q)) then (if ((q+3)≤((2)*q+(-1)) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) ((((2)*q+(-1))-(q+3))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_54_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_54 q e=(0*q+0*e+0) := by
  have v0 : ¬(((2)*q+1)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_54,tri2,pos,v0]
  grind
def term_55 (q e : Int) : Int := (((-1))*(if ((5)≤(e) ∧ ((2)*q+1)≤(e) ∧ (e)≤((4)*q)) then (if ((max (q+3) (e))≤((2)*q+(-1)) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) ((((2)*q+(-1))-(max (q+3) (e)))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int)))
theorem term_55_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_55 q e=(0:Int) := by
  have v0 : ¬((5)≤(e) ∧ ((2)*q+1)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_55,tri2,pos,v0]
  grind
def term_56 (q e : Int) : Int := (if ((5)≤(e) ∧ (e)≤((4)*q)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_56_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_56 q e=(2) := by
  have v0 : ((5)≤(e) ∧ (e)≤((4)*q)) := by omega
  have v1 : ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) := by omega
  have v2 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_56,tri2,pos,v0,v1,v2]
  grind
def term_57 (q e : Int) : Int := (if ((5)≤(e) ∧ (e)≤((2)*q+2)) then (if ((4)≤(q+1) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((q+1)-(4))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_57_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_57 q e=(2*q+(-4)) := by
  have v0 : ((5)≤(e) ∧ (e)≤((2)*q+2)) := by omega
  have v1 : ((4)≤(q+1) ∧ (0:Int)≤(0:Int)) := by omega
  have v2 : max (0:Int) (((q+1)-(4))+(1))=(q+(-2)) := by omega
  have v3 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_57,tri2,pos,v0,v1,v2,v3]
  grind
def term_58 (q e : Int) : Int := (if (((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)) then (if ((4)≤(q+1) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((q+1)-(4))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_58_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_58 q e=(0*q+0*e+0) := by
  have v0 : ¬(((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)) := by omega
  simp only [term_58,tri2,pos,v0]
  grind
def term_59 (q e : Int) : Int := (if ((e)≤((4)*q)) then (if ((4)≤(min (q+1) ((-2)*q+e)) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((min (q+1) ((-2)*q+e))-(4))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_59_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_59 q e=(0*q+0*e+0) := by
  have v0 : ((e)≤((4)*q)) := by omega
  have v1 : min (q+1) ((-2)*q+e)=((-2)*q+e) := by omega
  have v2 : ¬((4)≤(min (q+1) ((-2)*q+e)) ∧ (0:Int)≤(0:Int)) := by omega
  have v3 : ¬((4)≤((-2)*q+e) ∧ (0:Int)≤(0:Int)) := by omega
  simp only [term_59,tri2,pos,v0,v1,v2,v3]
  grind
def term_60 (q e : Int) : Int := (((-1))*(if ((5)≤(e) ∧ (e)≤((2)*q+2) ∧ ((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)) then (if ((4)≤(q+1) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((q+1)-(4))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int)))
theorem term_60_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_60 q e=(0:Int) := by
  have v0 : ¬((5)≤(e) ∧ (e)≤((2)*q+2) ∧ ((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)) := by omega
  simp only [term_60,tri2,pos,v0]
  grind
def term_61 (q e : Int) : Int := (((-1))*(if ((5)≤(e) ∧ (e)≤((2)*q+2) ∧ (e)≤((4)*q)) then (if ((4)≤(min (q+1) ((-2)*q+e)) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((min (q+1) ((-2)*q+e))-(4))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int)))
theorem term_61_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_61 q e=(0:Int) := by
  have v0 : ((5)≤(e) ∧ (e)≤((2)*q+2) ∧ (e)≤((4)*q)) := by omega
  have v1 : min (q+1) ((-2)*q+e)=((-2)*q+e) := by omega
  have v2 : ¬((4)≤(min (q+1) ((-2)*q+e)) ∧ (0:Int)≤(0:Int)) := by omega
  have v3 : ¬((4)≤((-2)*q+e) ∧ (0:Int)≤(0:Int)) := by omega
  simp only [term_61,tri2,pos,v0,v1,v2,v3]
  grind
def term_62 (q e : Int) : Int := (((-1))*(if (((3)*q+1)≤(e) ∧ (e)≤((3)*q+1) ∧ (e)≤((4)*q)) then (if ((4)≤(min (q+1) ((-2)*q+e)) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((min (q+1) ((-2)*q+e))-(4))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int)))
theorem term_62_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_62 q e=(0:Int) := by
  have v0 : ¬(((3)*q+1)≤(e) ∧ (e)≤((3)*q+1) ∧ (e)≤((4)*q)) := by omega
  simp only [term_62,tri2,pos,v0]
  grind
def term_63 (q e : Int) : Int := (if ((5)≤(e) ∧ (e)≤((2)*q+2) ∧ ((3)*q+1)≤(e) ∧ (e)≤((3)*q+1) ∧ (e)≤((4)*q)) then (if ((4)≤(min (q+1) ((-2)*q+e)) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((min (q+1) ((-2)*q+e))-(4))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_63_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_63 q e=(0*q+0*e+0) := by
  have v0 : ¬((5)≤(e) ∧ (e)≤((2)*q+2) ∧ ((3)*q+1)≤(e) ∧ (e)≤((3)*q+1) ∧ (e)≤((4)*q)) := by omega
  simp only [term_63,tri2,pos,v0]
  grind
def term_64 (q e : Int) : Int := (if ((5)≤(e) ∧ (e)≤((2)*q+2)) then (if ((q+4)≤((2)*q+1) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) ((((2)*q+1)-(q+4))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_64_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_64 q e=(2*q+(-4)) := by
  have v0 : ((5)≤(e) ∧ (e)≤((2)*q+2)) := by omega
  have v1 : ((q+4)≤((2)*q+1) ∧ (0:Int)≤(0:Int)) := by omega
  have v2 : max (0:Int) ((((2)*q+1)-(q+4))+(1))=(q+(-2)) := by omega
  have v3 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_64,tri2,pos,v0,v1,v2,v3]
  grind
def term_65 (q e : Int) : Int := (if (((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)) then (if ((q+4)≤((2)*q+1) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) ((((2)*q+1)-(q+4))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_65_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_65 q e=(0*q+0*e+0) := by
  have v0 : ¬(((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)) := by omega
  simp only [term_65,tri2,pos,v0]
  grind
def term_66 (q e : Int) : Int := (if ((e)≤((4)*q)) then (if ((q+4)≤(min ((2)*q+1) ((-2)*q+e+1)) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((min ((2)*q+1) ((-2)*q+e+1))-(q+4))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_66_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_66 q e=(0*q+0*e+0) := by
  have v0 : ((e)≤((4)*q)) := by omega
  have v1 : min ((2)*q+1) ((-2)*q+e+1)=((-2)*q+e+1) := by omega
  have v2 : ¬((q+4)≤(min ((2)*q+1) ((-2)*q+e+1)) ∧ (0:Int)≤(0:Int)) := by omega
  have v3 : ¬((q+4)≤((-2)*q+e+1) ∧ (0:Int)≤(0:Int)) := by omega
  simp only [term_66,tri2,pos,v0,v1,v2,v3]
  grind
def term_67 (q e : Int) : Int := (((-1))*(if ((5)≤(e) ∧ (e)≤((2)*q+2) ∧ ((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)) then (if ((q+4)≤((2)*q+1) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) ((((2)*q+1)-(q+4))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int)))
theorem term_67_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_67 q e=(0:Int) := by
  have v0 : ¬((5)≤(e) ∧ (e)≤((2)*q+2) ∧ ((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)) := by omega
  simp only [term_67,tri2,pos,v0]
  grind
def term_68 (q e : Int) : Int := (((-1))*(if ((5)≤(e) ∧ (e)≤((2)*q+2) ∧ (e)≤((4)*q)) then (if ((q+4)≤(min ((2)*q+1) ((-2)*q+e+1)) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((min ((2)*q+1) ((-2)*q+e+1))-(q+4))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int)))
theorem term_68_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_68 q e=(0:Int) := by
  have v0 : ((5)≤(e) ∧ (e)≤((2)*q+2) ∧ (e)≤((4)*q)) := by omega
  have v1 : min ((2)*q+1) ((-2)*q+e+1)=((-2)*q+e+1) := by omega
  have v2 : ¬((q+4)≤(min ((2)*q+1) ((-2)*q+e+1)) ∧ (0:Int)≤(0:Int)) := by omega
  have v3 : ¬((q+4)≤((-2)*q+e+1) ∧ (0:Int)≤(0:Int)) := by omega
  simp only [term_68,tri2,pos,v0,v1,v2,v3]
  grind
def term_69 (q e : Int) : Int := (((-1))*(if (((3)*q+1)≤(e) ∧ (e)≤((3)*q+1) ∧ (e)≤((4)*q)) then (if ((q+4)≤(min ((2)*q+1) ((-2)*q+e+1)) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((min ((2)*q+1) ((-2)*q+e+1))-(q+4))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int)))
theorem term_69_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_69 q e=(0:Int) := by
  have v0 : ¬(((3)*q+1)≤(e) ∧ (e)≤((3)*q+1) ∧ (e)≤((4)*q)) := by omega
  simp only [term_69,tri2,pos,v0]
  grind
def term_70 (q e : Int) : Int := (if ((5)≤(e) ∧ (e)≤((2)*q+2) ∧ ((3)*q+1)≤(e) ∧ (e)≤((3)*q+1) ∧ (e)≤((4)*q)) then (if ((q+4)≤(min ((2)*q+1) ((-2)*q+e+1)) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((min ((2)*q+1) ((-2)*q+e+1))-(q+4))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_70_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_70 q e=(0*q+0*e+0) := by
  have v0 : ¬((5)≤(e) ∧ (e)≤((2)*q+2) ∧ ((3)*q+1)≤(e) ∧ (e)≤((3)*q+1) ∧ (e)≤((4)*q)) := by omega
  simp only [term_70,tri2,pos,v0]
  grind
def term_71 (q e : Int) : Int := (if ((5)≤(e) ∧ (e)≤((2)*q+2)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_71_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_71 q e=(2) := by
  have v0 : ((5)≤(e) ∧ (e)≤((2)*q+2)) := by omega
  have v1 : ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) := by omega
  have v2 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_71,tri2,pos,v0,v1,v2]
  grind
def term_72 (q e : Int) : Int := (if (((3)*q+1)≤(e) ∧ (e)≤((4)*q+(-1))) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_72_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_72 q e=(0*q+0*e+0) := by
  have v0 : ¬(((3)*q+1)≤(e) ∧ (e)≤((4)*q+(-1))) := by omega
  simp only [term_72,tri2,pos,v0]
  grind
def term_73 (q e : Int) : Int := (((-1))*(if ((5)≤(e) ∧ (e)≤((2)*q+2) ∧ ((3)*q+1)≤(e) ∧ (e)≤((4)*q+(-1))) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int)))
theorem term_73_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_73 q e=(0:Int) := by
  have v0 : ¬((5)≤(e) ∧ (e)≤((2)*q+2) ∧ ((3)*q+1)≤(e) ∧ (e)≤((4)*q+(-1))) := by omega
  simp only [term_73,tri2,pos,v0]
  grind
def term_74 (q e : Int) : Int := (if ((5)≤(e) ∧ (e)≤(q+2)) then (if ((4)≤(q+1) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((q+1)-(4))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_74_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_74 q e=(0*q+0*e+0) := by
  have v0 : ¬((5)≤(e) ∧ (e)≤(q+2)) := by omega
  simp only [term_74,tri2,pos,v0]
  grind
def term_75 (q e : Int) : Int := (if ((e)≤((4)*q)) then (if ((4)≤(min (q+1) ((-2)*q+e)) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((min (q+1) ((-2)*q+e))-(4))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_75_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_75 q e=(0*q+0*e+0) := by
  have v0 : ((e)≤((4)*q)) := by omega
  have v1 : min (q+1) ((-2)*q+e)=((-2)*q+e) := by omega
  have v2 : ¬((4)≤(min (q+1) ((-2)*q+e)) ∧ (0:Int)≤(0:Int)) := by omega
  have v3 : ¬((4)≤((-2)*q+e) ∧ (0:Int)≤(0:Int)) := by omega
  simp only [term_75,tri2,pos,v0,v1,v2,v3]
  grind
def term_76 (q e : Int) : Int := (((-1))*(if ((5)≤(e) ∧ (e)≤(q+2) ∧ (e)≤((4)*q)) then (if ((4)≤(min (q+1) ((-2)*q+e)) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((min (q+1) ((-2)*q+e))-(4))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int)))
theorem term_76_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_76 q e=(0:Int) := by
  have v0 : ¬((5)≤(e) ∧ (e)≤(q+2) ∧ (e)≤((4)*q)) := by omega
  simp only [term_76,tri2,pos,v0]
  grind
def term_77 (q e : Int) : Int := (if ((5)≤(e)) then (if ((4)≤(q+1) ∧ (max (q+3) (e))≤((2)*q+1)) then ((((tri2 (((((2)*q+1)-(0:Int))+(1))-(4)))-(tri2 ((((2)*q+1)-(0:Int))-(q+1))))-(tri2 (((max (q+3) (e))-(0:Int))-(4))))+(tri2 ((((max (q+3) (e))-(0:Int))-(q+1))-(1)))) else (0:Int)) else (0:Int))
theorem term_77_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_77 q e=(4*q*q+(-2)*q*e+(-4)*q+4*e+(-8)) := by
  have v0 : ((5)≤(e)) := by omega
  have v1 : max (q+3) (e)=(e) := by omega
  have v2 : ((4)≤(q+1) ∧ (max (q+3) (e))≤((2)*q+1)) := by omega
  have v3 : ((4)≤(q+1) ∧ (e)≤((2)*q+1)) := by omega
  have v4 : max (0:Int) (((((2)*q+1)-(0:Int))+(1))-(4))=((2)*q+(-2)) := by omega
  have v5 : max (0:Int) ((((2)*q+1)-(0:Int))-(q+1))=(q) := by omega
  have v6 : max (0:Int) (((max (q+3) (e))-(0:Int))-(4))=(e+(-4)) := by omega
  have v7 : max (0:Int) (((e)-(0:Int))-(4))=(e+(-4)) := by omega
  have v8 : max (0:Int) ((((max (q+3) (e))-(0:Int))-(q+1))-(1))=((-q)+e+(-2)) := by omega
  have v9 : max (0:Int) ((((e)-(0:Int))-(q+1))-(1))=((-q)+e+(-2)) := by omega
  simp only [term_77,tri2,pos,v0,v1,v2,v3,v4,v5,v6,v7,v8,v9]
  grind
def term_78 (q e : Int) : Int := (if ((e)≤((4)*q)) then (if ((4)≤(min (q+1) ((-2)*q+e)) ∧ (q+3)≤((2)*q+1)) then ((((tri2 (((((2)*q+1)-(0:Int))+(1))-(4)))-(tri2 ((((2)*q+1)-(0:Int))-(min (q+1) ((-2)*q+e)))))-(tri2 (((q+3)-(0:Int))-(4))))+(tri2 ((((q+3)-(0:Int))-(min (q+1) ((-2)*q+e)))-(1)))) else (0:Int)) else (0:Int))
theorem term_78_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_78 q e=(0*q+0*e+0) := by
  have v0 : ((e)≤((4)*q)) := by omega
  have v1 : min (q+1) ((-2)*q+e)=((-2)*q+e) := by omega
  have v2 : ¬((4)≤(min (q+1) ((-2)*q+e)) ∧ (q+3)≤((2)*q+1)) := by omega
  have v3 : ¬((4)≤((-2)*q+e) ∧ (q+3)≤((2)*q+1)) := by omega
  simp only [term_78,tri2,pos,v0,v1,v2,v3]
  grind
def term_79 (q e : Int) : Int := (((-1))*(if ((5)≤(e) ∧ (e)≤((4)*q)) then (if ((4)≤(min (q+1) ((-2)*q+e)) ∧ (max (q+3) (e))≤((2)*q+1)) then ((((tri2 (((((2)*q+1)-(0:Int))+(1))-(4)))-(tri2 ((((2)*q+1)-(0:Int))-(min (q+1) ((-2)*q+e)))))-(tri2 (((max (q+3) (e))-(0:Int))-(4))))+(tri2 ((((max (q+3) (e))-(0:Int))-(min (q+1) ((-2)*q+e)))-(1)))) else (0:Int)) else (0:Int)))
theorem term_79_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_79 q e=(0:Int) := by
  have v0 : ((5)≤(e) ∧ (e)≤((4)*q)) := by omega
  have v1 : min (q+1) ((-2)*q+e)=((-2)*q+e) := by omega
  have v2 : max (q+3) (e)=(e) := by omega
  have v3 : ¬((4)≤(min (q+1) ((-2)*q+e)) ∧ (max (q+3) (e))≤((2)*q+1)) := by omega
  have v4 : ¬((4)≤((-2)*q+e) ∧ (e)≤((2)*q+1)) := by omega
  simp only [term_79,tri2,pos,v0,v1,v2,v3,v4]
  grind
def term_80 (q e : Int) : Int := (if ((5)≤(e)) then (if ((q+3)≤((2)*q+1) ∧ (max (q+3) (e))≤((2)*q+1)) then ((((tri2 (((((2)*q+1)-(0:Int))+(1))-(q+3)))-(tri2 ((((2)*q+1)-(0:Int))-((2)*q+1))))-(tri2 (((max (q+3) (e))-(0:Int))-(q+3))))+(tri2 ((((max (q+3) (e))-(0:Int))-((2)*q+1))-(1)))) else (0:Int)) else (0:Int))
theorem term_80_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_80 q e=(2*q*e+(-6)*q+(-1)*e*e+5*e+(-6)) := by
  have v0 : ((5)≤(e)) := by omega
  have v1 : max (q+3) (e)=(e) := by omega
  have v2 : ((q+3)≤((2)*q+1) ∧ (max (q+3) (e))≤((2)*q+1)) := by omega
  have v3 : ((q+3)≤((2)*q+1) ∧ (e)≤((2)*q+1)) := by omega
  have v4 : max (0:Int) (((((2)*q+1)-(0:Int))+(1))-(q+3))=(q+(-1)) := by omega
  have v5 : max (0:Int) ((((2)*q+1)-(0:Int))-((2)*q+1))=(0:Int) := by omega
  have v6 : max (0:Int) (((max (q+3) (e))-(0:Int))-(q+3))=((-q)+e+(-3)) := by omega
  have v7 : max (0:Int) (((e)-(0:Int))-(q+3))=((-q)+e+(-3)) := by omega
  have v8 : max (0:Int) ((((max (q+3) (e))-(0:Int))-((2)*q+1))-(1))=(0:Int) := by omega
  have v9 : max (0:Int) ((((e)-(0:Int))-((2)*q+1))-(1))=(0:Int) := by omega
  simp only [term_80,tri2,pos,v0,v1,v2,v3,v4,v5,v6,v7,v8,v9]
  grind
def term_81 (q e : Int) : Int := (if ((e)≤((4)*q)) then (if ((q+3)≤(min ((2)*q+1) ((-2)*q+e+1)) ∧ (q+3)≤((2)*q+1)) then ((((tri2 (((((2)*q+1)-(0:Int))+(1))-(q+3)))-(tri2 ((((2)*q+1)-(0:Int))-(min ((2)*q+1) ((-2)*q+e+1)))))-(tri2 (((q+3)-(0:Int))-(q+3))))+(tri2 ((((q+3)-(0:Int))-(min ((2)*q+1) ((-2)*q+e+1)))-(1)))) else (0:Int)) else (0:Int))
theorem term_81_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_81 q e=(0*q+0*e+0) := by
  have v0 : ((e)≤((4)*q)) := by omega
  have v1 : min ((2)*q+1) ((-2)*q+e+1)=((-2)*q+e+1) := by omega
  have v2 : ¬((q+3)≤(min ((2)*q+1) ((-2)*q+e+1)) ∧ (q+3)≤((2)*q+1)) := by omega
  have v3 : ¬((q+3)≤((-2)*q+e+1) ∧ (q+3)≤((2)*q+1)) := by omega
  simp only [term_81,tri2,pos,v0,v1,v2,v3]
  grind
def term_82 (q e : Int) : Int := (((-1))*(if ((5)≤(e) ∧ (e)≤((4)*q)) then (if ((q+3)≤(min ((2)*q+1) ((-2)*q+e+1)) ∧ (max (q+3) (e))≤((2)*q+1)) then ((((tri2 (((((2)*q+1)-(0:Int))+(1))-(q+3)))-(tri2 ((((2)*q+1)-(0:Int))-(min ((2)*q+1) ((-2)*q+e+1)))))-(tri2 (((max (q+3) (e))-(0:Int))-(q+3))))+(tri2 ((((max (q+3) (e))-(0:Int))-(min ((2)*q+1) ((-2)*q+e+1)))-(1)))) else (0:Int)) else (0:Int)))
theorem term_82_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_82 q e=(0:Int) := by
  have v0 : ((5)≤(e) ∧ (e)≤((4)*q)) := by omega
  have v1 : min ((2)*q+1) ((-2)*q+e+1)=((-2)*q+e+1) := by omega
  have v2 : max (q+3) (e)=(e) := by omega
  have v3 : ¬((q+3)≤(min ((2)*q+1) ((-2)*q+e+1)) ∧ (max (q+3) (e))≤((2)*q+1)) := by omega
  have v4 : ¬((q+3)≤((-2)*q+e+1) ∧ (e)≤((2)*q+1)) := by omega
  simp only [term_82,tri2,pos,v0,v1,v2,v3,v4]
  grind
def term_83 (q e : Int) : Int := (((-1))*(if (((4)*q)≤(e) ∧ (e)≤((4)*q)) then (if ((q+3)≤(q+3) ∧ (q+3)≤(q+3)) then (((2)*(max (0:Int) (((q+3)-(q+3))+(1))))*(max (0:Int) (((q+3)-(q+3))+(1)))) else (0:Int)) else (0:Int)))
theorem term_83_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_83 q e=(0:Int) := by
  have v0 : ¬(((4)*q)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_83,tri2,pos,v0]
  grind
def term_84 (q e : Int) : Int := (if ((5)≤(e) ∧ (e)≤(q+3)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_84_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_84 q e=(0*q+0*e+0) := by
  have v0 : ¬((5)≤(e) ∧ (e)≤(q+3)) := by omega
  simp only [term_84,tri2,pos,v0]
  grind
def term_85 (q e : Int) : Int := (if (((3)*q+2)≤(e) ∧ (e)≤((4)*q)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_85_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_85 q e=(0*q+0*e+0) := by
  have v0 : ¬(((3)*q+2)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_85,tri2,pos,v0]
  grind
def term_86 (q e : Int) : Int := (((-1))*(if ((5)≤(e) ∧ (e)≤(q+3) ∧ ((3)*q+2)≤(e) ∧ (e)≤((4)*q)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int)))
theorem term_86_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_86 q e=(0:Int) := by
  have v0 : ¬((5)≤(e) ∧ (e)≤(q+3) ∧ ((3)*q+2)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_86,tri2,pos,v0]
  grind
def term_87 (q e : Int) : Int := (if ((5)≤(e) ∧ (e)≤(q+2)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_87_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_87 q e=(0*q+0*e+0) := by
  have v0 : ¬((5)≤(e) ∧ (e)≤(q+2)) := by omega
  simp only [term_87,tri2,pos,v0]
  grind
def term_88 (q e : Int) : Int := (if (((2)*q+1)≤(e) ∧ (e)≤((4)*q)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_88_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_88 q e=(0*q+0*e+0) := by
  have v0 : ¬(((2)*q+1)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_88,tri2,pos,v0]
  grind
def term_89 (q e : Int) : Int := (((-1))*(if ((5)≤(e) ∧ (e)≤(q+2) ∧ ((2)*q+1)≤(e) ∧ (e)≤((4)*q)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int)))
theorem term_89_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_89 q e=(0:Int) := by
  have v0 : ¬((5)≤(e) ∧ (e)≤(q+2) ∧ ((2)*q+1)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_89,tri2,pos,v0]
  grind
def term_90 (q e : Int) : Int := (if ((5)≤(e)) then (if ((max (q+3) (e))≤((2)*q+(-1)) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) ((((2)*q+(-1))-(max (q+3) (e)))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_90_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_90 q e=(0*q+0*e+0) := by
  have v0 : ((5)≤(e)) := by omega
  have v1 : max (q+3) (e)=(e) := by omega
  have v2 : ¬((max (q+3) (e))≤((2)*q+(-1)) ∧ (0:Int)≤(0:Int)) := by omega
  have v3 : ¬((e)≤((2)*q+(-1)) ∧ (0:Int)≤(0:Int)) := by omega
  simp only [term_90,tri2,pos,v0,v1,v2,v3]
  grind
def term_91 (q e : Int) : Int := (if (((2)*q+1)≤(e) ∧ (e)≤((4)*q)) then (if ((q+3)≤((2)*q+(-1)) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) ((((2)*q+(-1))-(q+3))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_91_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_91 q e=(0*q+0*e+0) := by
  have v0 : ¬(((2)*q+1)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_91,tri2,pos,v0]
  grind
def term_92 (q e : Int) : Int := (((-1))*(if ((5)≤(e) ∧ ((2)*q+1)≤(e) ∧ (e)≤((4)*q)) then (if ((max (q+3) (e))≤((2)*q+(-1)) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) ((((2)*q+(-1))-(max (q+3) (e)))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int)))
theorem term_92_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_92 q e=(0:Int) := by
  have v0 : ¬((5)≤(e) ∧ ((2)*q+1)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_92,tri2,pos,v0]
  grind
def term_93 (q e : Int) : Int := (if ((5)≤(e) ∧ (e)≤((4)*q)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_93_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_93 q e=(2) := by
  have v0 : ((5)≤(e) ∧ (e)≤((4)*q)) := by omega
  have v1 : ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) := by omega
  have v2 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_93,tri2,pos,v0,v1,v2]
  grind
def term_94 (q e : Int) : Int := (if ((5)≤(e) ∧ (e)≤((2)*q+2)) then (if ((4)≤(q+1) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((q+1)-(4))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_94_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_94 q e=(2*q+(-4)) := by
  have v0 : ((5)≤(e) ∧ (e)≤((2)*q+2)) := by omega
  have v1 : ((4)≤(q+1) ∧ (0:Int)≤(0:Int)) := by omega
  have v2 : max (0:Int) (((q+1)-(4))+(1))=(q+(-2)) := by omega
  have v3 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_94,tri2,pos,v0,v1,v2,v3]
  grind
def term_95 (q e : Int) : Int := (if (((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)) then (if ((4)≤(q+1) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((q+1)-(4))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_95_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_95 q e=(0*q+0*e+0) := by
  have v0 : ¬(((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)) := by omega
  simp only [term_95,tri2,pos,v0]
  grind
def term_96 (q e : Int) : Int := (if ((e)≤((4)*q)) then (if ((4)≤(min (q+1) ((-2)*q+e)) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((min (q+1) ((-2)*q+e))-(4))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_96_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_96 q e=(0*q+0*e+0) := by
  have v0 : ((e)≤((4)*q)) := by omega
  have v1 : min (q+1) ((-2)*q+e)=((-2)*q+e) := by omega
  have v2 : ¬((4)≤(min (q+1) ((-2)*q+e)) ∧ (0:Int)≤(0:Int)) := by omega
  have v3 : ¬((4)≤((-2)*q+e) ∧ (0:Int)≤(0:Int)) := by omega
  simp only [term_96,tri2,pos,v0,v1,v2,v3]
  grind
def term_97 (q e : Int) : Int := (((-1))*(if ((5)≤(e) ∧ (e)≤((2)*q+2) ∧ ((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)) then (if ((4)≤(q+1) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((q+1)-(4))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int)))
theorem term_97_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_97 q e=(0:Int) := by
  have v0 : ¬((5)≤(e) ∧ (e)≤((2)*q+2) ∧ ((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)) := by omega
  simp only [term_97,tri2,pos,v0]
  grind
def term_98 (q e : Int) : Int := (((-1))*(if ((5)≤(e) ∧ (e)≤((2)*q+2) ∧ (e)≤((4)*q)) then (if ((4)≤(min (q+1) ((-2)*q+e)) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((min (q+1) ((-2)*q+e))-(4))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int)))
theorem term_98_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_98 q e=(0:Int) := by
  have v0 : ((5)≤(e) ∧ (e)≤((2)*q+2) ∧ (e)≤((4)*q)) := by omega
  have v1 : min (q+1) ((-2)*q+e)=((-2)*q+e) := by omega
  have v2 : ¬((4)≤(min (q+1) ((-2)*q+e)) ∧ (0:Int)≤(0:Int)) := by omega
  have v3 : ¬((4)≤((-2)*q+e) ∧ (0:Int)≤(0:Int)) := by omega
  simp only [term_98,tri2,pos,v0,v1,v2,v3]
  grind
def term_99 (q e : Int) : Int := (((-1))*(if (((3)*q+1)≤(e) ∧ (e)≤((3)*q+1) ∧ (e)≤((4)*q)) then (if ((4)≤(min (q+1) ((-2)*q+e)) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((min (q+1) ((-2)*q+e))-(4))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int)))
theorem term_99_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_99 q e=(0:Int) := by
  have v0 : ¬(((3)*q+1)≤(e) ∧ (e)≤((3)*q+1) ∧ (e)≤((4)*q)) := by omega
  simp only [term_99,tri2,pos,v0]
  grind
def term_100 (q e : Int) : Int := (if ((5)≤(e) ∧ (e)≤((2)*q+2) ∧ ((3)*q+1)≤(e) ∧ (e)≤((3)*q+1) ∧ (e)≤((4)*q)) then (if ((4)≤(min (q+1) ((-2)*q+e)) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((min (q+1) ((-2)*q+e))-(4))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_100_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_100 q e=(0*q+0*e+0) := by
  have v0 : ¬((5)≤(e) ∧ (e)≤((2)*q+2) ∧ ((3)*q+1)≤(e) ∧ (e)≤((3)*q+1) ∧ (e)≤((4)*q)) := by omega
  simp only [term_100,tri2,pos,v0]
  grind
def term_101 (q e : Int) : Int := (if ((5)≤(e) ∧ (e)≤((2)*q+2)) then (if ((q+4)≤((2)*q+1) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) ((((2)*q+1)-(q+4))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_101_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_101 q e=(2*q+(-4)) := by
  have v0 : ((5)≤(e) ∧ (e)≤((2)*q+2)) := by omega
  have v1 : ((q+4)≤((2)*q+1) ∧ (0:Int)≤(0:Int)) := by omega
  have v2 : max (0:Int) ((((2)*q+1)-(q+4))+(1))=(q+(-2)) := by omega
  have v3 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_101,tri2,pos,v0,v1,v2,v3]
  grind
def term_102 (q e : Int) : Int := (if (((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)) then (if ((q+4)≤((2)*q+1) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) ((((2)*q+1)-(q+4))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_102_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_102 q e=(0*q+0*e+0) := by
  have v0 : ¬(((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)) := by omega
  simp only [term_102,tri2,pos,v0]
  grind
def term_103 (q e : Int) : Int := (if ((e)≤((4)*q)) then (if ((q+4)≤(min ((2)*q+1) ((-2)*q+e+1)) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((min ((2)*q+1) ((-2)*q+e+1))-(q+4))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_103_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_103 q e=(0*q+0*e+0) := by
  have v0 : ((e)≤((4)*q)) := by omega
  have v1 : min ((2)*q+1) ((-2)*q+e+1)=((-2)*q+e+1) := by omega
  have v2 : ¬((q+4)≤(min ((2)*q+1) ((-2)*q+e+1)) ∧ (0:Int)≤(0:Int)) := by omega
  have v3 : ¬((q+4)≤((-2)*q+e+1) ∧ (0:Int)≤(0:Int)) := by omega
  simp only [term_103,tri2,pos,v0,v1,v2,v3]
  grind
def term_104 (q e : Int) : Int := (((-1))*(if ((5)≤(e) ∧ (e)≤((2)*q+2) ∧ ((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)) then (if ((q+4)≤((2)*q+1) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) ((((2)*q+1)-(q+4))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int)))
theorem term_104_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_104 q e=(0:Int) := by
  have v0 : ¬((5)≤(e) ∧ (e)≤((2)*q+2) ∧ ((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)) := by omega
  simp only [term_104,tri2,pos,v0]
  grind
def term_105 (q e : Int) : Int := (((-1))*(if ((5)≤(e) ∧ (e)≤((2)*q+2) ∧ (e)≤((4)*q)) then (if ((q+4)≤(min ((2)*q+1) ((-2)*q+e+1)) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((min ((2)*q+1) ((-2)*q+e+1))-(q+4))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int)))
theorem term_105_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_105 q e=(0:Int) := by
  have v0 : ((5)≤(e) ∧ (e)≤((2)*q+2) ∧ (e)≤((4)*q)) := by omega
  have v1 : min ((2)*q+1) ((-2)*q+e+1)=((-2)*q+e+1) := by omega
  have v2 : ¬((q+4)≤(min ((2)*q+1) ((-2)*q+e+1)) ∧ (0:Int)≤(0:Int)) := by omega
  have v3 : ¬((q+4)≤((-2)*q+e+1) ∧ (0:Int)≤(0:Int)) := by omega
  simp only [term_105,tri2,pos,v0,v1,v2,v3]
  grind
def term_106 (q e : Int) : Int := (((-1))*(if (((3)*q+1)≤(e) ∧ (e)≤((3)*q+1) ∧ (e)≤((4)*q)) then (if ((q+4)≤(min ((2)*q+1) ((-2)*q+e+1)) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((min ((2)*q+1) ((-2)*q+e+1))-(q+4))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int)))
theorem term_106_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_106 q e=(0:Int) := by
  have v0 : ¬(((3)*q+1)≤(e) ∧ (e)≤((3)*q+1) ∧ (e)≤((4)*q)) := by omega
  simp only [term_106,tri2,pos,v0]
  grind
def term_107 (q e : Int) : Int := (if ((5)≤(e) ∧ (e)≤((2)*q+2) ∧ ((3)*q+1)≤(e) ∧ (e)≤((3)*q+1) ∧ (e)≤((4)*q)) then (if ((q+4)≤(min ((2)*q+1) ((-2)*q+e+1)) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((min ((2)*q+1) ((-2)*q+e+1))-(q+4))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_107_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_107 q e=(0*q+0*e+0) := by
  have v0 : ¬((5)≤(e) ∧ (e)≤((2)*q+2) ∧ ((3)*q+1)≤(e) ∧ (e)≤((3)*q+1) ∧ (e)≤((4)*q)) := by omega
  simp only [term_107,tri2,pos,v0]
  grind
def term_108 (q e : Int) : Int := (if ((5)≤(e) ∧ (e)≤((2)*q+2)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_108_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_108 q e=(2) := by
  have v0 : ((5)≤(e) ∧ (e)≤((2)*q+2)) := by omega
  have v1 : ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) := by omega
  have v2 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_108,tri2,pos,v0,v1,v2]
  grind
def term_109 (q e : Int) : Int := (if (((3)*q+1)≤(e) ∧ (e)≤((4)*q+(-1))) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_109_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_109 q e=(0*q+0*e+0) := by
  have v0 : ¬(((3)*q+1)≤(e) ∧ (e)≤((4)*q+(-1))) := by omega
  simp only [term_109,tri2,pos,v0]
  grind
def term_110 (q e : Int) : Int := (((-1))*(if ((5)≤(e) ∧ (e)≤((2)*q+2) ∧ ((3)*q+1)≤(e) ∧ (e)≤((4)*q+(-1))) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int)))
theorem term_110_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_110 q e=(0:Int) := by
  have v0 : ¬((5)≤(e) ∧ (e)≤((2)*q+2) ∧ ((3)*q+1)≤(e) ∧ (e)≤((4)*q+(-1))) := by omega
  simp only [term_110,tri2,pos,v0]
  grind
def term_111 (q e : Int) : Int := (if ((5)≤(e)) then (if ((max (4) (e))≤(q+1) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((q+1)-(max (4) (e)))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_111_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_111 q e=(0*q+0*e+0) := by
  have v0 : ((5)≤(e)) := by omega
  have v1 : max (4) (e)=(e) := by omega
  have v2 : ¬((max (4) (e))≤(q+1) ∧ (0:Int)≤(0:Int)) := by omega
  have v3 : ¬((e)≤(q+1) ∧ (0:Int)≤(0:Int)) := by omega
  simp only [term_111,tri2,pos,v0,v1,v2,v3]
  grind
def term_112 (q e : Int) : Int := (if (((2)*q+3)≤(e) ∧ (e)≤((4)*q)) then (if ((4)≤(q+1) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((q+1)-(4))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_112_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_112 q e=(0*q+0*e+0) := by
  have v0 : ¬(((2)*q+3)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_112,tri2,pos,v0]
  grind
def term_113 (q e : Int) : Int := (((-1))*(if ((5)≤(e) ∧ ((2)*q+3)≤(e) ∧ (e)≤((4)*q)) then (if ((max (4) (e))≤(q+1) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((q+1)-(max (4) (e)))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int)))
theorem term_113_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_113 q e=(0:Int) := by
  have v0 : ¬((5)≤(e) ∧ ((2)*q+3)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_113,tri2,pos,v0]
  grind
def term_114 (q e : Int) : Int := (if ((5)≤(e)) then (if ((max (q+3) (e))≤((2)*q+1) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) ((((2)*q+1)-(max (q+3) (e)))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_114_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_114 q e=(4*q+(-2)*e+4) := by
  have v0 : ((5)≤(e)) := by omega
  have v1 : max (q+3) (e)=(e) := by omega
  have v2 : ((max (q+3) (e))≤((2)*q+1) ∧ (0:Int)≤(0:Int)) := by omega
  have v3 : ((e)≤((2)*q+1) ∧ (0:Int)≤(0:Int)) := by omega
  have v4 : max (0:Int) ((((2)*q+1)-(max (q+3) (e)))+(1))=((2)*q+(-e)+2) := by omega
  have v5 : max (0:Int) ((((2)*q+1)-(e))+(1))=((2)*q+(-e)+2) := by omega
  have v6 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_114,tri2,pos,v0,v1,v2,v3,v4,v5,v6]
  grind
def term_115 (q e : Int) : Int := (if (((2)*q+3)≤(e) ∧ (e)≤((4)*q)) then (if ((q+3)≤((2)*q+1) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) ((((2)*q+1)-(q+3))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_115_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_115 q e=(0*q+0*e+0) := by
  have v0 : ¬(((2)*q+3)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_115,tri2,pos,v0]
  grind
def term_116 (q e : Int) : Int := (((-1))*(if ((5)≤(e) ∧ ((2)*q+3)≤(e) ∧ (e)≤((4)*q)) then (if ((max (q+3) (e))≤((2)*q+1) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) ((((2)*q+1)-(max (q+3) (e)))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int)))
theorem term_116_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_116 q e=(0:Int) := by
  have v0 : ¬((5)≤(e) ∧ ((2)*q+3)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_116,tri2,pos,v0]
  grind
def term_117 (q e : Int) : Int := (if ((5)≤(e) ∧ (e)≤(q+2)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_117_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_117 q e=(0*q+0*e+0) := by
  have v0 : ¬((5)≤(e) ∧ (e)≤(q+2)) := by omega
  simp only [term_117,tri2,pos,v0]
  grind
def term_118 (q e : Int) : Int := (if (((2)*q+3)≤(e) ∧ (e)≤((4)*q)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_118_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_118 q e=(0*q+0*e+0) := by
  have v0 : ¬(((2)*q+3)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_118,tri2,pos,v0]
  grind
def term_119 (q e : Int) : Int := (((-1))*(if ((5)≤(e) ∧ (e)≤(q+2) ∧ ((2)*q+3)≤(e) ∧ (e)≤((4)*q)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int)))
theorem term_119_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_119 q e=(0:Int) := by
  have v0 : ¬((5)≤(e) ∧ (e)≤(q+2) ∧ ((2)*q+3)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_119,tri2,pos,v0]
  grind
def term_120 (q e : Int) : Int := (if ((5)≤(e)) then (if ((max (4) (e))≤(q+1) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((q+1)-(max (4) (e)))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_120_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_120 q e=(0*q+0*e+0) := by
  have v0 : ((5)≤(e)) := by omega
  have v1 : max (4) (e)=(e) := by omega
  have v2 : ¬((max (4) (e))≤(q+1) ∧ (0:Int)≤(0:Int)) := by omega
  have v3 : ¬((e)≤(q+1) ∧ (0:Int)≤(0:Int)) := by omega
  simp only [term_120,tri2,pos,v0,v1,v2,v3]
  grind
def term_121 (q e : Int) : Int := (if (((2)*q+1)≤(e) ∧ (e)≤((4)*q)) then (if ((4)≤(q+1) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((q+1)-(4))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_121_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_121 q e=(0*q+0*e+0) := by
  have v0 : ¬(((2)*q+1)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_121,tri2,pos,v0]
  grind
def term_122 (q e : Int) : Int := (((-1))*(if ((5)≤(e) ∧ ((2)*q+1)≤(e) ∧ (e)≤((4)*q)) then (if ((max (4) (e))≤(q+1) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((q+1)-(max (4) (e)))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int)))
theorem term_122_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_122 q e=(0:Int) := by
  have v0 : ¬((5)≤(e) ∧ ((2)*q+1)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_122,tri2,pos,v0]
  grind
def term_123 (q e : Int) : Int := (if ((5)≤(min (q+3) (e)) ∧ (max (0:Int) (e))≤((4)*q+(-3))) then ((((tri2 (((((4)*q+(-3))-((2)*q+(-3)))+(1))-(5)))-(tri2 ((((4)*q+(-3))-((2)*q+(-3)))-(min (q+3) (e)))))-(tri2 (((max (0:Int) (e))-((2)*q+(-3)))-(5))))+(tri2 ((((max (0:Int) (e))-((2)*q+(-3)))-(min (q+3) (e)))-(1)))) else (0:Int))
theorem term_123_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_123 q e=(3*q*q+(-9)*q+6) := by
  have v0 : min (q+3) (e)=(q+3) := by omega
  have v1 : max (0:Int) (e)=(e) := by omega
  have v2 : ((5)≤(min (q+3) (e)) ∧ (max (0:Int) (e))≤((4)*q+(-3))) := by omega
  have v3 : ((5)≤(q+3) ∧ (e)≤((4)*q+(-3))) := by omega
  have v4 : max (0:Int) (((((4)*q+(-3))-((2)*q+(-3)))+(1))-(5))=((2)*q+(-4)) := by omega
  have v5 : max (0:Int) ((((4)*q+(-3))-((2)*q+(-3)))-(min (q+3) (e)))=(q+(-3)) := by omega
  have v6 : max (0:Int) ((((4)*q+(-3))-((2)*q+(-3)))-(q+3))=(q+(-3)) := by omega
  have v7 : max (0:Int) (((max (0:Int) (e))-((2)*q+(-3)))-(5))=(0:Int) := by omega
  have v8 : max (0:Int) (((e)-((2)*q+(-3)))-(5))=(0:Int) := by omega
  have v9 : max (0:Int) ((((max (0:Int) (e))-((2)*q+(-3)))-(min (q+3) (e)))-(1))=(0:Int) := by omega
  have v10 : max (0:Int) ((((e)-((2)*q+(-3)))-(q+3))-(1))=(0:Int) := by omega
  simp only [term_123,tri2,pos,v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10]
  grind
def term_124 (q e : Int) : Int := (if ((q+4)≤(min ((2)*q+1) (e)) ∧ (max (0:Int) (e))≤((4)*q+(-3))) then ((((tri2 (((((4)*q+(-3))-((2)*q+(-4)))+(1))-(q+4)))-(tri2 ((((4)*q+(-3))-((2)*q+(-4)))-(min ((2)*q+1) (e)))))-(tri2 (((max (0:Int) (e))-((2)*q+(-4)))-(q+4))))+(tri2 ((((max (0:Int) (e))-((2)*q+(-4)))-(min ((2)*q+1) (e)))-(1)))) else (0:Int))
theorem term_124_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_124 q e=((-3)*q*q+4*q*e+(-9)*q+(-1)*e*e+3*e) := by
  have v0 : min ((2)*q+1) (e)=(e) := by omega
  have v1 : max (0:Int) (e)=(e) := by omega
  have v2 : ((q+4)≤(min ((2)*q+1) (e)) ∧ (max (0:Int) (e))≤((4)*q+(-3))) := by omega
  have v3 : ((q+4)≤(e) ∧ (e)≤((4)*q+(-3))) := by omega
  have v4 : max (0:Int) (((((4)*q+(-3))-((2)*q+(-4)))+(1))-(q+4))=(q+(-2)) := by omega
  have v5 : max (0:Int) ((((4)*q+(-3))-((2)*q+(-4)))-(min ((2)*q+1) (e)))=((2)*q+(-e)+1) := by omega
  have v6 : max (0:Int) ((((4)*q+(-3))-((2)*q+(-4)))-(e))=((2)*q+(-e)+1) := by omega
  have v7 : max (0:Int) (((max (0:Int) (e))-((2)*q+(-4)))-(q+4))=(0:Int) := by omega
  have v8 : max (0:Int) (((e)-((2)*q+(-4)))-(q+4))=(0:Int) := by omega
  have v9 : max (0:Int) ((((max (0:Int) (e))-((2)*q+(-4)))-(min ((2)*q+1) (e)))-(1))=(0:Int) := by omega
  have v10 : max (0:Int) ((((e)-((2)*q+(-4)))-(e))-(1))=(0:Int) := by omega
  simp only [term_124,tri2,pos,v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10]
  grind
def term_125 (q e : Int) : Int := (if ((5)≤(e) ∧ (e)≤(q+2)) then (if ((q+4)≤((2)*q+1) ∧ (0:Int)≤((4)*q+(-3))) then ((((tri2 (((((4)*q+(-3))-((2)*q+(-4)))+(1))-(q+4)))-(tri2 ((((4)*q+(-3))-((2)*q+(-4)))-((2)*q+1))))-(tri2 (((0:Int)-((2)*q+(-4)))-(q+4))))+(tri2 ((((0:Int)-((2)*q+(-4)))-((2)*q+1))-(1)))) else (0:Int)) else (0:Int))
theorem term_125_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_125 q e=(0*q+0*e+0) := by
  have v0 : ¬((5)≤(e) ∧ (e)≤(q+2)) := by omega
  simp only [term_125,tri2,pos,v0]
  grind
def term_126 (q e : Int) : Int := (if ((q+4)≤(min ((2)*q+1) (e)) ∧ (max (0:Int) (e))≤((4)*q+(-3))) then ((((tri2 (((((4)*q+(-3))-((2)*q+(-4)))+(1))-(q+4)))-(tri2 ((((4)*q+(-3))-((2)*q+(-4)))-(min ((2)*q+1) (e)))))-(tri2 (((max (0:Int) (e))-((2)*q+(-4)))-(q+4))))+(tri2 ((((max (0:Int) (e))-((2)*q+(-4)))-(min ((2)*q+1) (e)))-(1)))) else (0:Int))
theorem term_126_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_126 q e=((-3)*q*q+4*q*e+(-9)*q+(-1)*e*e+3*e) := by
  have v0 : min ((2)*q+1) (e)=(e) := by omega
  have v1 : max (0:Int) (e)=(e) := by omega
  have v2 : ((q+4)≤(min ((2)*q+1) (e)) ∧ (max (0:Int) (e))≤((4)*q+(-3))) := by omega
  have v3 : ((q+4)≤(e) ∧ (e)≤((4)*q+(-3))) := by omega
  have v4 : max (0:Int) (((((4)*q+(-3))-((2)*q+(-4)))+(1))-(q+4))=(q+(-2)) := by omega
  have v5 : max (0:Int) ((((4)*q+(-3))-((2)*q+(-4)))-(min ((2)*q+1) (e)))=((2)*q+(-e)+1) := by omega
  have v6 : max (0:Int) ((((4)*q+(-3))-((2)*q+(-4)))-(e))=((2)*q+(-e)+1) := by omega
  have v7 : max (0:Int) (((max (0:Int) (e))-((2)*q+(-4)))-(q+4))=(0:Int) := by omega
  have v8 : max (0:Int) (((e)-((2)*q+(-4)))-(q+4))=(0:Int) := by omega
  have v9 : max (0:Int) ((((max (0:Int) (e))-((2)*q+(-4)))-(min ((2)*q+1) (e)))-(1))=(0:Int) := by omega
  have v10 : max (0:Int) ((((e)-((2)*q+(-4)))-(e))-(1))=(0:Int) := by omega
  simp only [term_126,tri2,pos,v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10]
  grind
def term_127 (q e : Int) : Int := (((-1))*(if ((5)≤(e) ∧ (e)≤(q+2)) then (if ((q+4)≤(min ((2)*q+1) (e)) ∧ (max (0:Int) (e))≤((4)*q+(-3))) then ((((tri2 (((((4)*q+(-3))-((2)*q+(-4)))+(1))-(q+4)))-(tri2 ((((4)*q+(-3))-((2)*q+(-4)))-(min ((2)*q+1) (e)))))-(tri2 (((max (0:Int) (e))-((2)*q+(-4)))-(q+4))))+(tri2 ((((max (0:Int) (e))-((2)*q+(-4)))-(min ((2)*q+1) (e)))-(1)))) else (0:Int)) else (0:Int)))
theorem term_127_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_127 q e=(0:Int) := by
  have v0 : ¬((5)≤(e) ∧ (e)≤(q+2)) := by omega
  simp only [term_127,tri2,pos,v0]
  grind
def term_128 (q e : Int) : Int := (if ((5)≤(min (q+3) (e)) ∧ (max (0:Int) (e))≤((3)*q)) then ((((tri2 (((((3)*q)-((2)*q+(-3)))+(1))-(5)))-(tri2 ((((3)*q)-((2)*q+(-3)))-(min (q+3) (e)))))-(tri2 (((max (0:Int) (e))-((2)*q+(-3)))-(5))))+(tri2 ((((max (0:Int) (e))-((2)*q+(-3)))-(min (q+3) (e)))-(1)))) else (0:Int))
theorem term_128_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_128 q e=(1*q*q+(-1)*q) := by
  have v0 : min (q+3) (e)=(q+3) := by omega
  have v1 : max (0:Int) (e)=(e) := by omega
  have v2 : ((5)≤(min (q+3) (e)) ∧ (max (0:Int) (e))≤((3)*q)) := by omega
  have v3 : ((5)≤(q+3) ∧ (e)≤((3)*q)) := by omega
  have v4 : max (0:Int) (((((3)*q)-((2)*q+(-3)))+(1))-(5))=(q+(-1)) := by omega
  have v5 : max (0:Int) ((((3)*q)-((2)*q+(-3)))-(min (q+3) (e)))=(0:Int) := by omega
  have v6 : max (0:Int) ((((3)*q)-((2)*q+(-3)))-(q+3))=(0:Int) := by omega
  have v7 : max (0:Int) (((max (0:Int) (e))-((2)*q+(-3)))-(5))=(0:Int) := by omega
  have v8 : max (0:Int) (((e)-((2)*q+(-3)))-(5))=(0:Int) := by omega
  have v9 : max (0:Int) ((((max (0:Int) (e))-((2)*q+(-3)))-(min (q+3) (e)))-(1))=(0:Int) := by omega
  have v10 : max (0:Int) ((((e)-((2)*q+(-3)))-(q+3))-(1))=(0:Int) := by omega
  simp only [term_128,tri2,pos,v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10]
  grind
def term_129 (q e : Int) : Int := (if (((3)*q+2)≤(e) ∧ (e)≤((4)*q)) then (if ((5)≤(q+3) ∧ (0:Int)≤((3)*q)) then ((((tri2 (((((3)*q)-((2)*q+(-3)))+(1))-(5)))-(tri2 ((((3)*q)-((2)*q+(-3)))-(q+3))))-(tri2 (((0:Int)-((2)*q+(-3)))-(5))))+(tri2 ((((0:Int)-((2)*q+(-3)))-(q+3))-(1)))) else (0:Int)) else (0:Int))
theorem term_129_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_129 q e=(0*q+0*e+0) := by
  have v0 : ¬(((3)*q+2)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_129,tri2,pos,v0]
  grind
def term_130 (q e : Int) : Int := (((-1))*(if (((3)*q+2)≤(e) ∧ (e)≤((4)*q)) then (if ((5)≤(min (q+3) (e)) ∧ (max (0:Int) (e))≤((3)*q)) then ((((tri2 (((((3)*q)-((2)*q+(-3)))+(1))-(5)))-(tri2 ((((3)*q)-((2)*q+(-3)))-(min (q+3) (e)))))-(tri2 (((max (0:Int) (e))-((2)*q+(-3)))-(5))))+(tri2 ((((max (0:Int) (e))-((2)*q+(-3)))-(min (q+3) (e)))-(1)))) else (0:Int)) else (0:Int)))
theorem term_130_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_130 q e=(0:Int) := by
  have v0 : ¬(((3)*q+2)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_130,tri2,pos,v0]
  grind
def term_131 (q e : Int) : Int := (if ((q+4)≤(min (q+4) (e)) ∧ (max (0:Int) (e))≤((3)*q)) then ((((tri2 (((((3)*q)-((2)*q+(-4)))+(1))-(q+4)))-(tri2 ((((3)*q)-((2)*q+(-4)))-(min (q+4) (e)))))-(tri2 (((max (0:Int) (e))-((2)*q+(-4)))-(q+4))))+(tri2 ((((max (0:Int) (e))-((2)*q+(-4)))-(min (q+4) (e)))-(1)))) else (0:Int))
theorem term_131_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_131 q e=((-1)*q*q+2*q*e+(-9)*q+(-1)*e*e+9*e+(-18)) := by
  have v0 : min (q+4) (e)=(e) := by omega
  have v1 : max (0:Int) (e)=(e) := by omega
  have v2 : ((q+4)≤(min (q+4) (e)) ∧ (max (0:Int) (e))≤((3)*q)) := by omega
  have v3 : ((q+4)≤(e) ∧ (e)≤((3)*q)) := by omega
  have v4 : max (0:Int) (((((3)*q)-((2)*q+(-4)))+(1))-(q+4))=(1) := by omega
  have v5 : max (0:Int) ((((3)*q)-((2)*q+(-4)))-(min (q+4) (e)))=(q+(-e)+4) := by omega
  have v6 : max (0:Int) ((((3)*q)-((2)*q+(-4)))-(e))=(q+(-e)+4) := by omega
  have v7 : max (0:Int) (((max (0:Int) (e))-((2)*q+(-4)))-(q+4))=(0:Int) := by omega
  have v8 : max (0:Int) (((e)-((2)*q+(-4)))-(q+4))=(0:Int) := by omega
  have v9 : max (0:Int) ((((max (0:Int) (e))-((2)*q+(-4)))-(min (q+4) (e)))-(1))=(0:Int) := by omega
  have v10 : max (0:Int) ((((e)-((2)*q+(-4)))-(e))-(1))=(0:Int) := by omega
  simp only [term_131,tri2,pos,v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10]
  grind
def term_132 (q e : Int) : Int := (if (((3)*q+2)≤(e) ∧ (e)≤((4)*q)) then (if ((q+4)≤(q+4) ∧ (0:Int)≤((3)*q)) then ((((tri2 (((((3)*q)-((2)*q+(-4)))+(1))-(q+4)))-(tri2 ((((3)*q)-((2)*q+(-4)))-(q+4))))-(tri2 (((0:Int)-((2)*q+(-4)))-(q+4))))+(tri2 ((((0:Int)-((2)*q+(-4)))-(q+4))-(1)))) else (0:Int)) else (0:Int))
theorem term_132_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_132 q e=(0*q+0*e+0) := by
  have v0 : ¬(((3)*q+2)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_132,tri2,pos,v0]
  grind
def term_133 (q e : Int) : Int := (((-1))*(if (((3)*q+2)≤(e) ∧ (e)≤((4)*q)) then (if ((q+4)≤(min (q+4) (e)) ∧ (max (0:Int) (e))≤((3)*q)) then ((((tri2 (((((3)*q)-((2)*q+(-4)))+(1))-(q+4)))-(tri2 ((((3)*q)-((2)*q+(-4)))-(min (q+4) (e)))))-(tri2 (((max (0:Int) (e))-((2)*q+(-4)))-(q+4))))+(tri2 ((((max (0:Int) (e))-((2)*q+(-4)))-(min (q+4) (e)))-(1)))) else (0:Int)) else (0:Int)))
theorem term_133_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_133 q e=(0:Int) := by
  have v0 : ¬(((3)*q+2)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_133,tri2,pos,v0]
  grind
def term_134 (q e : Int) : Int := (if ((e)≤((4)*q)) then (if ((5)≤(min ((2)*q+1) (e)) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((min ((2)*q+1) (e))-(5))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_134_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_134 q e=(2*e+(-8)) := by
  have v0 : ((e)≤((4)*q)) := by omega
  have v1 : min ((2)*q+1) (e)=(e) := by omega
  have v2 : ((5)≤(min ((2)*q+1) (e)) ∧ (0:Int)≤(0:Int)) := by omega
  have v3 : ((5)≤(e) ∧ (0:Int)≤(0:Int)) := by omega
  have v4 : max (0:Int) (((min ((2)*q+1) (e))-(5))+(1))=(e+(-4)) := by omega
  have v5 : max (0:Int) (((e)-(5))+(1))=(e+(-4)) := by omega
  have v6 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_134,tri2,pos,v0,v1,v2,v3,v4,v5,v6]
  grind
def term_135 (q e : Int) : Int := (if ((5)≤(e) ∧ (e)≤(q+2)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_135_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_135 q e=(0*q+0*e+0) := by
  have v0 : ¬((5)≤(e) ∧ (e)≤(q+2)) := by omega
  simp only [term_135,tri2,pos,v0]
  grind
def term_136 (q e : Int) : Int := (if ((q+4)≤(e) ∧ (e)≤((3)*q)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_136_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_136 q e=(2) := by
  have v0 : ((q+4)≤(e) ∧ (e)≤((3)*q)) := by omega
  have v1 : ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) := by omega
  have v2 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_136,tri2,pos,v0,v1,v2]
  grind
def term_137 (q e : Int) : Int := (if (((3)*q+2)≤(e) ∧ (e)≤((4)*q)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_137_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_137 q e=(0*q+0*e+0) := by
  have v0 : ¬(((3)*q+2)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_137,tri2,pos,v0]
  grind
def term_138 (q e : Int) : Int := (((-1))*(if ((5)≤(e) ∧ (e)≤(q+2) ∧ (q+4)≤(e) ∧ (e)≤((3)*q)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int)))
theorem term_138_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_138 q e=(0:Int) := by
  have v0 : ¬((5)≤(e) ∧ (e)≤(q+2) ∧ (q+4)≤(e) ∧ (e)≤((3)*q)) := by omega
  simp only [term_138,tri2,pos,v0]
  grind
def term_139 (q e : Int) : Int := (((-1))*(if ((5)≤(e) ∧ (e)≤(q+2) ∧ ((3)*q+2)≤(e) ∧ (e)≤((4)*q)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int)))
theorem term_139_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_139 q e=(0:Int) := by
  have v0 : ¬((5)≤(e) ∧ (e)≤(q+2) ∧ ((3)*q+2)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_139,tri2,pos,v0]
  grind
def term_140 (q e : Int) : Int := (((-1))*(if ((q+4)≤(e) ∧ (e)≤((3)*q) ∧ ((3)*q+2)≤(e) ∧ (e)≤((4)*q)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int)))
theorem term_140_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_140 q e=(0:Int) := by
  have v0 : ¬((q+4)≤(e) ∧ (e)≤((3)*q) ∧ ((3)*q+2)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_140,tri2,pos,v0]
  grind
def term_141 (q e : Int) : Int := (if ((5)≤(e) ∧ (e)≤(q+2) ∧ (q+4)≤(e) ∧ (e)≤((3)*q) ∧ ((3)*q+2)≤(e) ∧ (e)≤((4)*q)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_141_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_141 q e=(0*q+0*e+0) := by
  have v0 : ¬((5)≤(e) ∧ (e)≤(q+2) ∧ (q+4)≤(e) ∧ (e)≤((3)*q) ∧ ((3)*q+2)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_141,tri2,pos,v0]
  grind
def term_142 (q e : Int) : Int := (if ((5)≤(e) ∧ (e)≤(q+2)) then (if ((q+4)≤((2)*q+1) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) ((((2)*q+1)-(q+4))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_142_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_142 q e=(0*q+0*e+0) := by
  have v0 : ¬((5)≤(e) ∧ (e)≤(q+2)) := by omega
  simp only [term_142,tri2,pos,v0]
  grind
def term_143 (q e : Int) : Int := (if ((e)≤((4)*q)) then (if ((q+4)≤(min ((2)*q+1) (e)) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((min ((2)*q+1) (e))-(q+4))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_143_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_143 q e=((-2)*q+2*e+(-6)) := by
  have v0 : ((e)≤((4)*q)) := by omega
  have v1 : min ((2)*q+1) (e)=(e) := by omega
  have v2 : ((q+4)≤(min ((2)*q+1) (e)) ∧ (0:Int)≤(0:Int)) := by omega
  have v3 : ((q+4)≤(e) ∧ (0:Int)≤(0:Int)) := by omega
  have v4 : max (0:Int) (((min ((2)*q+1) (e))-(q+4))+(1))=((-q)+e+(-3)) := by omega
  have v5 : max (0:Int) (((e)-(q+4))+(1))=((-q)+e+(-3)) := by omega
  have v6 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_143,tri2,pos,v0,v1,v2,v3,v4,v5,v6]
  grind
def term_144 (q e : Int) : Int := (((-1))*(if ((5)≤(e) ∧ (e)≤(q+2) ∧ (e)≤((4)*q)) then (if ((q+4)≤(min ((2)*q+1) (e)) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((min ((2)*q+1) (e))-(q+4))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int)))
theorem term_144_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_144 q e=(0:Int) := by
  have v0 : ¬((5)≤(e) ∧ (e)≤(q+2) ∧ (e)≤((4)*q)) := by omega
  simp only [term_144,tri2,pos,v0]
  grind
def term_145 (q e : Int) : Int := (if (((2)*q+2)≤(e) ∧ (e)≤((4)*q+(-2))) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_145_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_145 q e=(0*q+0*e+0) := by
  have v0 : ¬(((2)*q+2)≤(e) ∧ (e)≤((4)*q+(-2))) := by omega
  simp only [term_145,tri2,pos,v0]
  grind
def term_146 (q e : Int) : Int := (if (((2)*q+3)≤(e) ∧ (e)≤((4)*q+(-1))) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_146_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_146 q e=(0*q+0*e+0) := by
  have v0 : ¬(((2)*q+3)≤(e) ∧ (e)≤((4)*q+(-1))) := by omega
  simp only [term_146,tri2,pos,v0]
  grind
def term_147 (q e : Int) : Int := (if (((2)*q+2)≤(e) ∧ (e)≤((4)*q+(-1))) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_147_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_147 q e=(0*q+0*e+0) := by
  have v0 : ¬(((2)*q+2)≤(e) ∧ (e)≤((4)*q+(-1))) := by omega
  simp only [term_147,tri2,pos,v0]
  grind
def term_148 (q e : Int) : Int := (if (((2)*q+2)≤(e) ∧ (e)≤((4)*q)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_148_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_148 q e=(0*q+0*e+0) := by
  have v0 : ¬(((2)*q+2)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_148,tri2,pos,v0]
  grind
def term_149 (q e : Int) : Int := (if (((2)*q+3)≤(e) ∧ (e)≤((4)*q)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_149_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_149 q e=(0*q+0*e+0) := by
  have v0 : ¬(((2)*q+3)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_149,tri2,pos,v0]
  grind
def term_150 (q e : Int) : Int := (if (((2)*q+1)≤(e) ∧ (e)≤((4)*q)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_150_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_150 q e=(0*q+0*e+0) := by
  have v0 : ¬(((2)*q+1)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_150,tri2,pos,v0]
  grind
def term_151 (q e : Int) : Int := (if ((5)≤(min ((2)*q+1) (e)) ∧ (max ((4)*q+(-2)) (e))≤((4)*q)) then (((2)*(max (0:Int) (((min ((2)*q+1) (e))-(5))+(1))))*(max (0:Int) ((((4)*q)-(max ((4)*q+(-2)) (e)))+(1)))) else (0:Int))
theorem term_151_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_151 q e=(6*e+(-24)) := by
  have v0 : min ((2)*q+1) (e)=(e) := by omega
  have v1 : max ((4)*q+(-2)) (e)=((4)*q+(-2)) := by omega
  have v2 : ((5)≤(min ((2)*q+1) (e)) ∧ (max ((4)*q+(-2)) (e))≤((4)*q)) := by omega
  have v3 : ((5)≤(e) ∧ ((4)*q+(-2))≤((4)*q)) := by omega
  have v4 : max (0:Int) (((min ((2)*q+1) (e))-(5))+(1))=(e+(-4)) := by omega
  have v5 : max (0:Int) (((e)-(5))+(1))=(e+(-4)) := by omega
  have v6 : max (0:Int) ((((4)*q)-(max ((4)*q+(-2)) (e)))+(1))=(3) := by omega
  have v7 : max (0:Int) ((((4)*q)-((4)*q+(-2)))+(1))=(3) := by omega
  simp only [term_151,tri2,pos,v0,v1,v2,v3,v4,v5,v6,v7]
  grind
def term_152 (q e : Int) : Int := (if ((5)≤(e) ∧ (e)≤(q+2)) then (if ((q+4)≤((2)*q+1) ∧ ((4)*q+(-2))≤((4)*q)) then (((2)*(max (0:Int) ((((2)*q+1)-(q+4))+(1))))*(max (0:Int) ((((4)*q)-((4)*q+(-2)))+(1)))) else (0:Int)) else (0:Int))
theorem term_152_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_152 q e=(0*q+0*e+0) := by
  have v0 : ¬((5)≤(e) ∧ (e)≤(q+2)) := by omega
  simp only [term_152,tri2,pos,v0]
  grind
def term_153 (q e : Int) : Int := (if ((q+4)≤(min ((2)*q+1) (e)) ∧ (max ((4)*q+(-2)) (e))≤((4)*q)) then (((2)*(max (0:Int) (((min ((2)*q+1) (e))-(q+4))+(1))))*(max (0:Int) ((((4)*q)-(max ((4)*q+(-2)) (e)))+(1)))) else (0:Int))
theorem term_153_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_153 q e=((-6)*q+6*e+(-18)) := by
  have v0 : min ((2)*q+1) (e)=(e) := by omega
  have v1 : max ((4)*q+(-2)) (e)=((4)*q+(-2)) := by omega
  have v2 : ((q+4)≤(min ((2)*q+1) (e)) ∧ (max ((4)*q+(-2)) (e))≤((4)*q)) := by omega
  have v3 : ((q+4)≤(e) ∧ ((4)*q+(-2))≤((4)*q)) := by omega
  have v4 : max (0:Int) (((min ((2)*q+1) (e))-(q+4))+(1))=((-q)+e+(-3)) := by omega
  have v5 : max (0:Int) (((e)-(q+4))+(1))=((-q)+e+(-3)) := by omega
  have v6 : max (0:Int) ((((4)*q)-(max ((4)*q+(-2)) (e)))+(1))=(3) := by omega
  have v7 : max (0:Int) ((((4)*q)-((4)*q+(-2)))+(1))=(3) := by omega
  simp only [term_153,tri2,pos,v0,v1,v2,v3,v4,v5,v6,v7]
  grind
def term_154 (q e : Int) : Int := (((-1))*(if ((5)≤(e) ∧ (e)≤(q+2)) then (if ((q+4)≤(min ((2)*q+1) (e)) ∧ (max ((4)*q+(-2)) (e))≤((4)*q)) then (((2)*(max (0:Int) (((min ((2)*q+1) (e))-(q+4))+(1))))*(max (0:Int) ((((4)*q)-(max ((4)*q+(-2)) (e)))+(1)))) else (0:Int)) else (0:Int)))
theorem term_154_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_154 q e=(0:Int) := by
  have v0 : ¬((5)≤(e) ∧ (e)≤(q+2)) := by omega
  simp only [term_154,tri2,pos,v0]
  grind
def term_155 (q e : Int) : Int := (if ((5)≤(e) ∧ (e)≤(q+2)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_155_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_155 q e=(0*q+0*e+0) := by
  have v0 : ¬((5)≤(e) ∧ (e)≤(q+2)) := by omega
  simp only [term_155,tri2,pos,v0]
  grind
def term_156 (q e : Int) : Int := (if (((2)*q+2)≤(e) ∧ (e)≤((4)*q+(-2))) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_156_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_156 q e=(0*q+0*e+0) := by
  have v0 : ¬(((2)*q+2)≤(e) ∧ (e)≤((4)*q+(-2))) := by omega
  simp only [term_156,tri2,pos,v0]
  grind
def term_157 (q e : Int) : Int := (((-1))*(if ((5)≤(e) ∧ (e)≤(q+2) ∧ ((2)*q+2)≤(e) ∧ (e)≤((4)*q+(-2))) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int)))
theorem term_157_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_157 q e=(0:Int) := by
  have v0 : ¬((5)≤(e) ∧ (e)≤(q+2) ∧ ((2)*q+2)≤(e) ∧ (e)≤((4)*q+(-2))) := by omega
  simp only [term_157,tri2,pos,v0]
  grind
def term_158 (q e : Int) : Int := (if ((5)≤(e) ∧ (e)≤(q+2)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_158_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_158 q e=(0*q+0*e+0) := by
  have v0 : ¬((5)≤(e) ∧ (e)≤(q+2)) := by omega
  simp only [term_158,tri2,pos,v0]
  grind
def term_159 (q e : Int) : Int := (if (((2)*q+3)≤(e) ∧ (e)≤((4)*q+(-1))) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_159_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_159 q e=(0*q+0*e+0) := by
  have v0 : ¬(((2)*q+3)≤(e) ∧ (e)≤((4)*q+(-1))) := by omega
  simp only [term_159,tri2,pos,v0]
  grind
def term_160 (q e : Int) : Int := (((-1))*(if ((5)≤(e) ∧ (e)≤(q+2) ∧ ((2)*q+3)≤(e) ∧ (e)≤((4)*q+(-1))) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int)))
theorem term_160_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_160 q e=(0:Int) := by
  have v0 : ¬((5)≤(e) ∧ (e)≤(q+2) ∧ ((2)*q+3)≤(e) ∧ (e)≤((4)*q+(-1))) := by omega
  simp only [term_160,tri2,pos,v0]
  grind
def term_161 (q e : Int) : Int := (if ((5)≤(e) ∧ (e)≤(q+2)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_161_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_161 q e=(0*q+0*e+0) := by
  have v0 : ¬((5)≤(e) ∧ (e)≤(q+2)) := by omega
  simp only [term_161,tri2,pos,v0]
  grind
def term_162 (q e : Int) : Int := (if (((2)*q+2)≤(e) ∧ (e)≤((4)*q+(-1))) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_162_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_162 q e=(0*q+0*e+0) := by
  have v0 : ¬(((2)*q+2)≤(e) ∧ (e)≤((4)*q+(-1))) := by omega
  simp only [term_162,tri2,pos,v0]
  grind
def term_163 (q e : Int) : Int := (((-1))*(if ((5)≤(e) ∧ (e)≤(q+2) ∧ ((2)*q+2)≤(e) ∧ (e)≤((4)*q+(-1))) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int)))
theorem term_163_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_163 q e=(0:Int) := by
  have v0 : ¬((5)≤(e) ∧ (e)≤(q+2) ∧ ((2)*q+2)≤(e) ∧ (e)≤((4)*q+(-1))) := by omega
  simp only [term_163,tri2,pos,v0]
  grind
def term_164 (q e : Int) : Int := (if ((5)≤(e) ∧ (e)≤(q+2)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_164_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_164 q e=(0*q+0*e+0) := by
  have v0 : ¬((5)≤(e) ∧ (e)≤(q+2)) := by omega
  simp only [term_164,tri2,pos,v0]
  grind
def term_165 (q e : Int) : Int := (if (((2)*q+2)≤(e) ∧ (e)≤((4)*q)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_165_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_165 q e=(0*q+0*e+0) := by
  have v0 : ¬(((2)*q+2)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_165,tri2,pos,v0]
  grind
def term_166 (q e : Int) : Int := (((-1))*(if ((5)≤(e) ∧ (e)≤(q+2) ∧ ((2)*q+2)≤(e) ∧ (e)≤((4)*q)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int)))
theorem term_166_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_166 q e=(0:Int) := by
  have v0 : ¬((5)≤(e) ∧ (e)≤(q+2) ∧ ((2)*q+2)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_166,tri2,pos,v0]
  grind
def term_167 (q e : Int) : Int := (if ((5)≤(e) ∧ (e)≤(q+2)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_167_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_167 q e=(0*q+0*e+0) := by
  have v0 : ¬((5)≤(e) ∧ (e)≤(q+2)) := by omega
  simp only [term_167,tri2,pos,v0]
  grind
def term_168 (q e : Int) : Int := (if (((2)*q+3)≤(e) ∧ (e)≤((4)*q)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_168_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_168 q e=(0*q+0*e+0) := by
  have v0 : ¬(((2)*q+3)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_168,tri2,pos,v0]
  grind
def term_169 (q e : Int) : Int := (((-1))*(if ((5)≤(e) ∧ (e)≤(q+2) ∧ ((2)*q+3)≤(e) ∧ (e)≤((4)*q)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int)))
theorem term_169_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_169 q e=(0:Int) := by
  have v0 : ¬((5)≤(e) ∧ (e)≤(q+2) ∧ ((2)*q+3)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_169,tri2,pos,v0]
  grind
def term_170 (q e : Int) : Int := (if ((e)≤((4)*q)) then (if ((5)≤(min ((2)*q+1) (e)) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((min ((2)*q+1) (e))-(5))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_170_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_170 q e=(2*e+(-8)) := by
  have v0 : ((e)≤((4)*q)) := by omega
  have v1 : min ((2)*q+1) (e)=(e) := by omega
  have v2 : ((5)≤(min ((2)*q+1) (e)) ∧ (0:Int)≤(0:Int)) := by omega
  have v3 : ((5)≤(e) ∧ (0:Int)≤(0:Int)) := by omega
  have v4 : max (0:Int) (((min ((2)*q+1) (e))-(5))+(1))=(e+(-4)) := by omega
  have v5 : max (0:Int) (((e)-(5))+(1))=(e+(-4)) := by omega
  have v6 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_170,tri2,pos,v0,v1,v2,v3,v4,v5,v6]
  grind
def term_171 (q e : Int) : Int := (if ((5)≤(e) ∧ (e)≤(q+2)) then (if ((q+4)≤((2)*q+1) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) ((((2)*q+1)-(q+4))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_171_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_171 q e=(0*q+0*e+0) := by
  have v0 : ¬((5)≤(e) ∧ (e)≤(q+2)) := by omega
  simp only [term_171,tri2,pos,v0]
  grind
def term_172 (q e : Int) : Int := (if ((e)≤((4)*q)) then (if ((q+4)≤(min ((2)*q+1) (e)) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((min ((2)*q+1) (e))-(q+4))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_172_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_172 q e=((-2)*q+2*e+(-6)) := by
  have v0 : ((e)≤((4)*q)) := by omega
  have v1 : min ((2)*q+1) (e)=(e) := by omega
  have v2 : ((q+4)≤(min ((2)*q+1) (e)) ∧ (0:Int)≤(0:Int)) := by omega
  have v3 : ((q+4)≤(e) ∧ (0:Int)≤(0:Int)) := by omega
  have v4 : max (0:Int) (((min ((2)*q+1) (e))-(q+4))+(1))=((-q)+e+(-3)) := by omega
  have v5 : max (0:Int) (((e)-(q+4))+(1))=((-q)+e+(-3)) := by omega
  have v6 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_172,tri2,pos,v0,v1,v2,v3,v4,v5,v6]
  grind
def term_173 (q e : Int) : Int := (((-1))*(if ((5)≤(e) ∧ (e)≤(q+2) ∧ (e)≤((4)*q)) then (if ((q+4)≤(min ((2)*q+1) (e)) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((min ((2)*q+1) (e))-(q+4))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int)))
theorem term_173_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_173 q e=(0:Int) := by
  have v0 : ¬((5)≤(e) ∧ (e)≤(q+2) ∧ (e)≤((4)*q)) := by omega
  simp only [term_173,tri2,pos,v0]
  grind
def term_174 (q e : Int) : Int := (if ((5)≤(e)) then (if ((max ((2)*q+2) (e))≤((3)*q+(-1)) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) ((((3)*q+(-1))-(max ((2)*q+2) (e)))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_174_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_174 q e=(2*q+(-4)) := by
  have v0 : ((5)≤(e)) := by omega
  have v1 : max ((2)*q+2) (e)=((2)*q+2) := by omega
  have v2 : ((max ((2)*q+2) (e))≤((3)*q+(-1)) ∧ (0:Int)≤(0:Int)) := by omega
  have v3 : (((2)*q+2)≤((3)*q+(-1)) ∧ (0:Int)≤(0:Int)) := by omega
  have v4 : max (0:Int) ((((3)*q+(-1))-(max ((2)*q+2) (e)))+(1))=(q+(-2)) := by omega
  have v5 : max (0:Int) ((((3)*q+(-1))-((2)*q+2))+(1))=(q+(-2)) := by omega
  have v6 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_174,tri2,pos,v0,v1,v2,v3,v4,v5,v6]
  grind
def term_175 (q e : Int) : Int := (if (((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)) then (if (((2)*q+2)≤((3)*q+(-1)) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) ((((3)*q+(-1))-((2)*q+2))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_175_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_175 q e=(0*q+0*e+0) := by
  have v0 : ¬(((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)) := by omega
  simp only [term_175,tri2,pos,v0]
  grind
def term_176 (q e : Int) : Int := (((-1))*(if ((5)≤(e) ∧ ((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)) then (if ((max ((2)*q+2) (e))≤((3)*q+(-1)) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) ((((3)*q+(-1))-(max ((2)*q+2) (e)))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int)))
theorem term_176_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_176 q e=(0:Int) := by
  have v0 : ¬((5)≤(e) ∧ ((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)) := by omega
  simp only [term_176,tri2,pos,v0]
  grind
def term_177 (q e : Int) : Int := (if ((5)≤(e)) then (if ((max ((3)*q+1) (e))≤((4)*q+(-3)) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) ((((4)*q+(-3))-(max ((3)*q+1) (e)))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_177_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_177 q e=(2*q+(-6)) := by
  have v0 : ((5)≤(e)) := by omega
  have v1 : max ((3)*q+1) (e)=((3)*q+1) := by omega
  have v2 : ((max ((3)*q+1) (e))≤((4)*q+(-3)) ∧ (0:Int)≤(0:Int)) := by omega
  have v3 : (((3)*q+1)≤((4)*q+(-3)) ∧ (0:Int)≤(0:Int)) := by omega
  have v4 : max (0:Int) ((((4)*q+(-3))-(max ((3)*q+1) (e)))+(1))=(q+(-3)) := by omega
  have v5 : max (0:Int) ((((4)*q+(-3))-((3)*q+1))+(1))=(q+(-3)) := by omega
  have v6 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_177,tri2,pos,v0,v1,v2,v3,v4,v5,v6]
  grind
def term_178 (q e : Int) : Int := (if (((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)) then (if (((3)*q+1)≤((4)*q+(-3)) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) ((((4)*q+(-3))-((3)*q+1))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_178_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_178 q e=(0*q+0*e+0) := by
  have v0 : ¬(((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)) := by omega
  simp only [term_178,tri2,pos,v0]
  grind
def term_179 (q e : Int) : Int := (((-1))*(if ((5)≤(e) ∧ ((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)) then (if ((max ((3)*q+1) (e))≤((4)*q+(-3)) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) ((((4)*q+(-3))-(max ((3)*q+1) (e)))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int)))
theorem term_179_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_179 q e=(0:Int) := by
  have v0 : ¬((5)≤(e) ∧ ((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)) := by omega
  simp only [term_179,tri2,pos,v0]
  grind
def term_180 (q e : Int) : Int := (if ((5)≤(e)) then (if ((max ((2)*q+2) (e))≤((4)*q+(-3)) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) ((((4)*q+(-3))-(max ((2)*q+2) (e)))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_180_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_180 q e=(4*q+(-8)) := by
  have v0 : ((5)≤(e)) := by omega
  have v1 : max ((2)*q+2) (e)=((2)*q+2) := by omega
  have v2 : ((max ((2)*q+2) (e))≤((4)*q+(-3)) ∧ (0:Int)≤(0:Int)) := by omega
  have v3 : (((2)*q+2)≤((4)*q+(-3)) ∧ (0:Int)≤(0:Int)) := by omega
  have v4 : max (0:Int) ((((4)*q+(-3))-(max ((2)*q+2) (e)))+(1))=((2)*q+(-4)) := by omega
  have v5 : max (0:Int) ((((4)*q+(-3))-((2)*q+2))+(1))=((2)*q+(-4)) := by omega
  have v6 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_180,tri2,pos,v0,v1,v2,v3,v4,v5,v6]
  grind
def term_181 (q e : Int) : Int := (if (((4)*q)≤(e) ∧ (e)≤((4)*q)) then (if (((2)*q+2)≤((4)*q+(-3)) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) ((((4)*q+(-3))-((2)*q+2))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_181_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_181 q e=(0*q+0*e+0) := by
  have v0 : ¬(((4)*q)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_181,tri2,pos,v0]
  grind
def term_182 (q e : Int) : Int := (((-1))*(if ((5)≤(e) ∧ ((4)*q)≤(e) ∧ (e)≤((4)*q)) then (if ((max ((2)*q+2) (e))≤((4)*q+(-3)) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) ((((4)*q+(-3))-(max ((2)*q+2) (e)))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int)))
theorem term_182_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_182 q e=(0:Int) := by
  have v0 : ¬((5)≤(e) ∧ ((4)*q)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_182,tri2,pos,v0]
  grind
def term_183 (q e : Int) : Int := (if ((5)≤(e)) then (if ((max ((2)*q+2) (e))≤((3)*q+(-1)) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) ((((3)*q+(-1))-(max ((2)*q+2) (e)))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_183_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_183 q e=(2*q+(-4)) := by
  have v0 : ((5)≤(e)) := by omega
  have v1 : max ((2)*q+2) (e)=((2)*q+2) := by omega
  have v2 : ((max ((2)*q+2) (e))≤((3)*q+(-1)) ∧ (0:Int)≤(0:Int)) := by omega
  have v3 : (((2)*q+2)≤((3)*q+(-1)) ∧ (0:Int)≤(0:Int)) := by omega
  have v4 : max (0:Int) ((((3)*q+(-1))-(max ((2)*q+2) (e)))+(1))=(q+(-2)) := by omega
  have v5 : max (0:Int) ((((3)*q+(-1))-((2)*q+2))+(1))=(q+(-2)) := by omega
  have v6 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_183,tri2,pos,v0,v1,v2,v3,v4,v5,v6]
  grind
def term_184 (q e : Int) : Int := (if (((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)) then (if (((2)*q+2)≤((3)*q+(-1)) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) ((((3)*q+(-1))-((2)*q+2))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_184_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_184 q e=(0*q+0*e+0) := by
  have v0 : ¬(((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)) := by omega
  simp only [term_184,tri2,pos,v0]
  grind
def term_185 (q e : Int) : Int := (if (((4)*q)≤(e) ∧ (e)≤((4)*q)) then (if (((2)*q+2)≤((3)*q+(-1)) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) ((((3)*q+(-1))-((2)*q+2))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_185_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_185 q e=(0*q+0*e+0) := by
  have v0 : ¬(((4)*q)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_185,tri2,pos,v0]
  grind
def term_186 (q e : Int) : Int := (((-1))*(if ((5)≤(e) ∧ ((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)) then (if ((max ((2)*q+2) (e))≤((3)*q+(-1)) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) ((((3)*q+(-1))-(max ((2)*q+2) (e)))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int)))
theorem term_186_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_186 q e=(0:Int) := by
  have v0 : ¬((5)≤(e) ∧ ((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)) := by omega
  simp only [term_186,tri2,pos,v0]
  grind
def term_187 (q e : Int) : Int := (((-1))*(if ((5)≤(e) ∧ ((4)*q)≤(e) ∧ (e)≤((4)*q)) then (if ((max ((2)*q+2) (e))≤((3)*q+(-1)) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) ((((3)*q+(-1))-(max ((2)*q+2) (e)))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int)))
theorem term_187_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_187 q e=(0:Int) := by
  have v0 : ¬((5)≤(e) ∧ ((4)*q)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_187,tri2,pos,v0]
  grind
def term_188 (q e : Int) : Int := (((-1))*(if (((3)*q+1)≤(e) ∧ (e)≤((3)*q+1) ∧ ((4)*q)≤(e) ∧ (e)≤((4)*q)) then (if (((2)*q+2)≤((3)*q+(-1)) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) ((((3)*q+(-1))-((2)*q+2))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int)))
theorem term_188_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_188 q e=(0:Int) := by
  have v0 : ¬(((3)*q+1)≤(e) ∧ (e)≤((3)*q+1) ∧ ((4)*q)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_188,tri2,pos,v0]
  grind
def term_189 (q e : Int) : Int := (if ((5)≤(e) ∧ ((3)*q+1)≤(e) ∧ (e)≤((3)*q+1) ∧ ((4)*q)≤(e) ∧ (e)≤((4)*q)) then (if ((max ((2)*q+2) (e))≤((3)*q+(-1)) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) ((((3)*q+(-1))-(max ((2)*q+2) (e)))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_189_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_189 q e=(0*q+0*e+0) := by
  have v0 : ¬((5)≤(e) ∧ ((3)*q+1)≤(e) ∧ (e)≤((3)*q+1) ∧ ((4)*q)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_189,tri2,pos,v0]
  grind
def term_190 (q e : Int) : Int := (if ((5)≤(e)) then (if ((max ((2)*q+2) (e))≤((3)*q) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) ((((3)*q)-(max ((2)*q+2) (e)))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_190_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_190 q e=(2*q+(-2)) := by
  have v0 : ((5)≤(e)) := by omega
  have v1 : max ((2)*q+2) (e)=((2)*q+2) := by omega
  have v2 : ((max ((2)*q+2) (e))≤((3)*q) ∧ (0:Int)≤(0:Int)) := by omega
  have v3 : (((2)*q+2)≤((3)*q) ∧ (0:Int)≤(0:Int)) := by omega
  have v4 : max (0:Int) ((((3)*q)-(max ((2)*q+2) (e)))+(1))=(q+(-1)) := by omega
  have v5 : max (0:Int) ((((3)*q)-((2)*q+2))+(1))=(q+(-1)) := by omega
  have v6 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_190,tri2,pos,v0,v1,v2,v3,v4,v5,v6]
  grind
def term_191 (q e : Int) : Int := (if (((3)*q+2)≤(e) ∧ (e)≤((4)*q)) then (if (((2)*q+2)≤((3)*q) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) ((((3)*q)-((2)*q+2))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_191_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_191 q e=(0*q+0*e+0) := by
  have v0 : ¬(((3)*q+2)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_191,tri2,pos,v0]
  grind
def term_192 (q e : Int) : Int := (((-1))*(if ((5)≤(e) ∧ ((3)*q+2)≤(e) ∧ (e)≤((4)*q)) then (if ((max ((2)*q+2) (e))≤((3)*q) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) ((((3)*q)-(max ((2)*q+2) (e)))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int)))
theorem term_192_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_192 q e=(0:Int) := by
  have v0 : ¬((5)≤(e) ∧ ((3)*q+2)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_192,tri2,pos,v0]
  grind
def term_193 (q e : Int) : Int := (if ((5)≤(e)) then (if ((max ((2)*q+2) (e))≤((3)*q+(-1)) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) ((((3)*q+(-1))-(max ((2)*q+2) (e)))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_193_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_193 q e=(2*q+(-4)) := by
  have v0 : ((5)≤(e)) := by omega
  have v1 : max ((2)*q+2) (e)=((2)*q+2) := by omega
  have v2 : ((max ((2)*q+2) (e))≤((3)*q+(-1)) ∧ (0:Int)≤(0:Int)) := by omega
  have v3 : (((2)*q+2)≤((3)*q+(-1)) ∧ (0:Int)≤(0:Int)) := by omega
  have v4 : max (0:Int) ((((3)*q+(-1))-(max ((2)*q+2) (e)))+(1))=(q+(-2)) := by omega
  have v5 : max (0:Int) ((((3)*q+(-1))-((2)*q+2))+(1))=(q+(-2)) := by omega
  have v6 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_193,tri2,pos,v0,v1,v2,v3,v4,v5,v6]
  grind
def term_194 (q e : Int) : Int := (if (((3)*q+1)≤(e) ∧ (e)≤((4)*q)) then (if (((2)*q+2)≤((3)*q+(-1)) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) ((((3)*q+(-1))-((2)*q+2))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_194_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_194 q e=(0*q+0*e+0) := by
  have v0 : ¬(((3)*q+1)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_194,tri2,pos,v0]
  grind
def term_195 (q e : Int) : Int := (((-1))*(if ((5)≤(e) ∧ ((3)*q+1)≤(e) ∧ (e)≤((4)*q)) then (if ((max ((2)*q+2) (e))≤((3)*q+(-1)) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) ((((3)*q+(-1))-(max ((2)*q+2) (e)))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int)))
theorem term_195_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_195 q e=(0:Int) := by
  have v0 : ¬((5)≤(e) ∧ ((3)*q+1)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_195,tri2,pos,v0]
  grind
def term_196 (q e : Int) : Int := (if ((5)≤(e) ∧ (e)≤((2)*q)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_196_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_196 q e=(2) := by
  have v0 : ((5)≤(e) ∧ (e)≤((2)*q)) := by omega
  have v1 : ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) := by omega
  have v2 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_196,tri2,pos,v0,v1,v2]
  grind
def term_197 (q e : Int) : Int := (if (((4)*q)≤(e) ∧ (e)≤((4)*q)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_197_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_197 q e=(0*q+0*e+0) := by
  have v0 : ¬(((4)*q)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_197,tri2,pos,v0]
  grind
def term_198 (q e : Int) : Int := (((-1))*(if ((5)≤(e) ∧ (e)≤((2)*q) ∧ ((4)*q)≤(e) ∧ (e)≤((4)*q)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int)))
theorem term_198_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_198 q e=(0:Int) := by
  have v0 : ¬((5)≤(e) ∧ (e)≤((2)*q) ∧ ((4)*q)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_198,tri2,pos,v0]
  grind
def term_199 (q e : Int) : Int := (if ((5)≤(e) ∧ (e)≤((2)*q)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_199_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_199 q e=(2) := by
  have v0 : ((5)≤(e) ∧ (e)≤((2)*q)) := by omega
  have v1 : ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) := by omega
  have v2 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_199,tri2,pos,v0,v1,v2]
  grind
def term_200 (q e : Int) : Int := (if (((4)*q)≤(e) ∧ (e)≤((4)*q)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_200_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_200 q e=(0*q+0*e+0) := by
  have v0 : ¬(((4)*q)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_200,tri2,pos,v0]
  grind
def term_201 (q e : Int) : Int := (if (((3)*q+2)≤(e) ∧ (e)≤((4)*q)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_201_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_201 q e=(0*q+0*e+0) := by
  have v0 : ¬(((3)*q+2)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_201,tri2,pos,v0]
  grind
def term_202 (q e : Int) : Int := (((-1))*(if ((5)≤(e) ∧ (e)≤((2)*q) ∧ ((4)*q)≤(e) ∧ (e)≤((4)*q)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int)))
theorem term_202_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_202 q e=(0:Int) := by
  have v0 : ¬((5)≤(e) ∧ (e)≤((2)*q) ∧ ((4)*q)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_202,tri2,pos,v0]
  grind
def term_203 (q e : Int) : Int := (((-1))*(if ((5)≤(e) ∧ (e)≤((2)*q) ∧ ((3)*q+2)≤(e) ∧ (e)≤((4)*q)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int)))
theorem term_203_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_203 q e=(0:Int) := by
  have v0 : ¬((5)≤(e) ∧ (e)≤((2)*q) ∧ ((3)*q+2)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_203,tri2,pos,v0]
  grind
def term_204 (q e : Int) : Int := (((-1))*(if (((4)*q)≤(e) ∧ (e)≤((4)*q) ∧ ((3)*q+2)≤(e) ∧ (e)≤((4)*q)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int)))
theorem term_204_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_204 q e=(0:Int) := by
  have v0 : ¬(((4)*q)≤(e) ∧ (e)≤((4)*q) ∧ ((3)*q+2)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_204,tri2,pos,v0]
  grind
def term_205 (q e : Int) : Int := (if ((5)≤(e) ∧ (e)≤((2)*q) ∧ ((4)*q)≤(e) ∧ (e)≤((4)*q) ∧ ((3)*q+2)≤(e) ∧ (e)≤((4)*q)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_205_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_205 q e=(0*q+0*e+0) := by
  have v0 : ¬((5)≤(e) ∧ (e)≤((2)*q) ∧ ((4)*q)≤(e) ∧ (e)≤((4)*q) ∧ ((3)*q+2)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_205,tri2,pos,v0]
  grind
def term_206 (q e : Int) : Int := (if ((5)≤(e) ∧ (e)≤((2)*q)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_206_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_206 q e=(2) := by
  have v0 : ((5)≤(e) ∧ (e)≤((2)*q)) := by omega
  have v1 : ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) := by omega
  have v2 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_206,tri2,pos,v0,v1,v2]
  grind
def term_207 (q e : Int) : Int := (if (((4)*q)≤(e) ∧ (e)≤((4)*q)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_207_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_207 q e=(0*q+0*e+0) := by
  have v0 : ¬(((4)*q)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_207,tri2,pos,v0]
  grind
def term_208 (q e : Int) : Int := (if (((2)*q+3)≤(e) ∧ (e)≤((4)*q)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_208_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_208 q e=(0*q+0*e+0) := by
  have v0 : ¬(((2)*q+3)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_208,tri2,pos,v0]
  grind
def term_209 (q e : Int) : Int := (((-1))*(if ((5)≤(e) ∧ (e)≤((2)*q) ∧ ((4)*q)≤(e) ∧ (e)≤((4)*q)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int)))
theorem term_209_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_209 q e=(0:Int) := by
  have v0 : ¬((5)≤(e) ∧ (e)≤((2)*q) ∧ ((4)*q)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_209,tri2,pos,v0]
  grind
def term_210 (q e : Int) : Int := (((-1))*(if ((5)≤(e) ∧ (e)≤((2)*q) ∧ ((2)*q+3)≤(e) ∧ (e)≤((4)*q)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int)))
theorem term_210_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_210 q e=(0:Int) := by
  have v0 : ¬((5)≤(e) ∧ (e)≤((2)*q) ∧ ((2)*q+3)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_210,tri2,pos,v0]
  grind
def term_211 (q e : Int) : Int := (((-1))*(if (((4)*q)≤(e) ∧ (e)≤((4)*q) ∧ ((2)*q+3)≤(e) ∧ (e)≤((4)*q)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int)))
theorem term_211_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_211 q e=(0:Int) := by
  have v0 : ¬(((4)*q)≤(e) ∧ (e)≤((4)*q) ∧ ((2)*q+3)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_211,tri2,pos,v0]
  grind
def term_212 (q e : Int) : Int := (if ((5)≤(e) ∧ (e)≤((2)*q) ∧ ((4)*q)≤(e) ∧ (e)≤((4)*q) ∧ ((2)*q+3)≤(e) ∧ (e)≤((4)*q)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_212_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_212 q e=(0*q+0*e+0) := by
  have v0 : ¬((5)≤(e) ∧ (e)≤((2)*q) ∧ ((4)*q)≤(e) ∧ (e)≤((4)*q) ∧ ((2)*q+3)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_212,tri2,pos,v0]
  grind
def term_213 (q e : Int) : Int := (if ((5)≤(e)) then (if ((max (4) (e))≤(q+1) ∧ ((2)*q+2)≤((2)*q+3)) then (((2)*(max (0:Int) (((q+1)-(max (4) (e)))+(1))))*(max (0:Int) ((((2)*q+3)-((2)*q+2))+(1)))) else (0:Int)) else (0:Int))
theorem term_213_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_213 q e=(0*q+0*e+0) := by
  have v0 : ((5)≤(e)) := by omega
  have v1 : max (4) (e)=(e) := by omega
  have v2 : ¬((max (4) (e))≤(q+1) ∧ ((2)*q+2)≤((2)*q+3)) := by omega
  have v3 : ¬((e)≤(q+1) ∧ ((2)*q+2)≤((2)*q+3)) := by omega
  simp only [term_213,tri2,pos,v0,v1,v2,v3]
  grind
def term_214 (q e : Int) : Int := (if ((e)≤((4)*q)) then (if ((4)≤(q+1) ∧ ((2)*q+2)≤(min ((2)*q+3) (e))) then (((2)*(max (0:Int) (((q+1)-(4))+(1))))*(max (0:Int) (((min ((2)*q+3) (e))-((2)*q+2))+(1)))) else (0:Int)) else (0:Int))
theorem term_214_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_214 q e=(0*q+0*e+0) := by
  have v0 : ((e)≤((4)*q)) := by omega
  have v1 : min ((2)*q+3) (e)=(e) := by omega
  have v2 : ¬((4)≤(q+1) ∧ ((2)*q+2)≤(min ((2)*q+3) (e))) := by omega
  have v3 : ¬((4)≤(q+1) ∧ ((2)*q+2)≤(e)) := by omega
  simp only [term_214,tri2,pos,v0,v1,v2,v3]
  grind
def term_215 (q e : Int) : Int := (((-1))*(if ((5)≤(e) ∧ (e)≤((4)*q)) then (if ((max (4) (e))≤(q+1) ∧ ((2)*q+2)≤(min ((2)*q+3) (e))) then (((2)*(max (0:Int) (((q+1)-(max (4) (e)))+(1))))*(max (0:Int) (((min ((2)*q+3) (e))-((2)*q+2))+(1)))) else (0:Int)) else (0:Int)))
theorem term_215_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_215 q e=(0:Int) := by
  have v0 : ((5)≤(e) ∧ (e)≤((4)*q)) := by omega
  have v1 : max (4) (e)=(e) := by omega
  have v2 : min ((2)*q+3) (e)=(e) := by omega
  have v3 : ¬((max (4) (e))≤(q+1) ∧ ((2)*q+2)≤(min ((2)*q+3) (e))) := by omega
  have v4 : ¬((e)≤(q+1) ∧ ((2)*q+2)≤(e)) := by omega
  simp only [term_215,tri2,pos,v0,v1,v2,v3,v4]
  grind
def term_216 (q e : Int) : Int := (if ((5)≤(e)) then (if ((max (q+3) (e))≤((2)*q+1) ∧ ((2)*q+2)≤((2)*q+3)) then (((2)*(max (0:Int) ((((2)*q+1)-(max (q+3) (e)))+(1))))*(max (0:Int) ((((2)*q+3)-((2)*q+2))+(1)))) else (0:Int)) else (0:Int))
theorem term_216_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_216 q e=(8*q+(-4)*e+8) := by
  have v0 : ((5)≤(e)) := by omega
  have v1 : max (q+3) (e)=(e) := by omega
  have v2 : ((max (q+3) (e))≤((2)*q+1) ∧ ((2)*q+2)≤((2)*q+3)) := by omega
  have v3 : ((e)≤((2)*q+1) ∧ ((2)*q+2)≤((2)*q+3)) := by omega
  have v4 : max (0:Int) ((((2)*q+1)-(max (q+3) (e)))+(1))=((2)*q+(-e)+2) := by omega
  have v5 : max (0:Int) ((((2)*q+1)-(e))+(1))=((2)*q+(-e)+2) := by omega
  have v6 : max (0:Int) ((((2)*q+3)-((2)*q+2))+(1))=(2) := by omega
  simp only [term_216,tri2,pos,v0,v1,v2,v3,v4,v5,v6]
  grind
def term_217 (q e : Int) : Int := (if ((e)≤((4)*q)) then (if ((q+3)≤((2)*q+1) ∧ ((2)*q+2)≤(min ((2)*q+3) (e))) then (((2)*(max (0:Int) ((((2)*q+1)-(q+3))+(1))))*(max (0:Int) (((min ((2)*q+3) (e))-((2)*q+2))+(1)))) else (0:Int)) else (0:Int))
theorem term_217_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_217 q e=(0*q+0*e+0) := by
  have v0 : ((e)≤((4)*q)) := by omega
  have v1 : min ((2)*q+3) (e)=(e) := by omega
  have v2 : ¬((q+3)≤((2)*q+1) ∧ ((2)*q+2)≤(min ((2)*q+3) (e))) := by omega
  have v3 : ¬((q+3)≤((2)*q+1) ∧ ((2)*q+2)≤(e)) := by omega
  simp only [term_217,tri2,pos,v0,v1,v2,v3]
  grind
def term_218 (q e : Int) : Int := (((-1))*(if ((5)≤(e) ∧ (e)≤((4)*q)) then (if ((max (q+3) (e))≤((2)*q+1) ∧ ((2)*q+2)≤(min ((2)*q+3) (e))) then (((2)*(max (0:Int) ((((2)*q+1)-(max (q+3) (e)))+(1))))*(max (0:Int) (((min ((2)*q+3) (e))-((2)*q+2))+(1)))) else (0:Int)) else (0:Int)))
theorem term_218_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_218 q e=(0:Int) := by
  have v0 : ((5)≤(e) ∧ (e)≤((4)*q)) := by omega
  have v1 : max (q+3) (e)=(e) := by omega
  have v2 : min ((2)*q+3) (e)=(e) := by omega
  have v3 : ¬((max (q+3) (e))≤((2)*q+1) ∧ ((2)*q+2)≤(min ((2)*q+3) (e))) := by omega
  have v4 : ¬((e)≤((2)*q+1) ∧ ((2)*q+2)≤(e)) := by omega
  simp only [term_218,tri2,pos,v0,v1,v2,v3,v4]
  grind
def term_219 (q e : Int) : Int := (if ((5)≤(e)) then (if ((max (4) (e))≤(q+1) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((q+1)-(max (4) (e)))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_219_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_219 q e=(0*q+0*e+0) := by
  have v0 : ((5)≤(e)) := by omega
  have v1 : max (4) (e)=(e) := by omega
  have v2 : ¬((max (4) (e))≤(q+1) ∧ (0:Int)≤(0:Int)) := by omega
  have v3 : ¬((e)≤(q+1) ∧ (0:Int)≤(0:Int)) := by omega
  simp only [term_219,tri2,pos,v0,v1,v2,v3]
  grind
def term_220 (q e : Int) : Int := (if (((2)*q+1)≤(e) ∧ (e)≤((4)*q)) then (if ((4)≤(q+1) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((q+1)-(4))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_220_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_220 q e=(0*q+0*e+0) := by
  have v0 : ¬(((2)*q+1)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_220,tri2,pos,v0]
  grind
def term_221 (q e : Int) : Int := (((-1))*(if ((5)≤(e) ∧ ((2)*q+1)≤(e) ∧ (e)≤((4)*q)) then (if ((max (4) (e))≤(q+1) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((q+1)-(max (4) (e)))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int)))
theorem term_221_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_221 q e=(0:Int) := by
  have v0 : ¬((5)≤(e) ∧ ((2)*q+1)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_221,tri2,pos,v0]
  grind
def term_222 (q e : Int) : Int := (if ((5)≤(e)) then (if ((max (q+3) (e))≤((2)*q+(-1)) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) ((((2)*q+(-1))-(max (q+3) (e)))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_222_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_222 q e=(0*q+0*e+0) := by
  have v0 : ((5)≤(e)) := by omega
  have v1 : max (q+3) (e)=(e) := by omega
  have v2 : ¬((max (q+3) (e))≤((2)*q+(-1)) ∧ (0:Int)≤(0:Int)) := by omega
  have v3 : ¬((e)≤((2)*q+(-1)) ∧ (0:Int)≤(0:Int)) := by omega
  simp only [term_222,tri2,pos,v0,v1,v2,v3]
  grind
def term_223 (q e : Int) : Int := (if (((2)*q+1)≤(e) ∧ (e)≤((4)*q)) then (if ((q+3)≤((2)*q+(-1)) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) ((((2)*q+(-1))-(q+3))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_223_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_223 q e=(0*q+0*e+0) := by
  have v0 : ¬(((2)*q+1)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_223,tri2,pos,v0]
  grind
def term_224 (q e : Int) : Int := (((-1))*(if ((5)≤(e) ∧ ((2)*q+1)≤(e) ∧ (e)≤((4)*q)) then (if ((max (q+3) (e))≤((2)*q+(-1)) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) ((((2)*q+(-1))-(max (q+3) (e)))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int)))
theorem term_224_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_224 q e=(0:Int) := by
  have v0 : ¬((5)≤(e) ∧ ((2)*q+1)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_224,tri2,pos,v0]
  grind
def term_225 (q e : Int) : Int := (if ((5)≤(e) ∧ (e)≤(q+3)) then (if (((2)*q+2)≤((2)*q+3) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) ((((2)*q+3)-((2)*q+2))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_225_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_225 q e=(0*q+0*e+0) := by
  have v0 : ¬((5)≤(e) ∧ (e)≤(q+3)) := by omega
  simp only [term_225,tri2,pos,v0]
  grind
def term_226 (q e : Int) : Int := (if ((e)≤((4)*q+(-1))) then (if (((2)*q+2)≤(min ((2)*q+3) (e)) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((min ((2)*q+3) (e))-((2)*q+2))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_226_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_226 q e=(0*q+0*e+0) := by
  have v0 : ((e)≤((4)*q+(-1))) := by omega
  have v1 : min ((2)*q+3) (e)=(e) := by omega
  have v2 : ¬(((2)*q+2)≤(min ((2)*q+3) (e)) ∧ (0:Int)≤(0:Int)) := by omega
  have v3 : ¬(((2)*q+2)≤(e) ∧ (0:Int)≤(0:Int)) := by omega
  simp only [term_226,tri2,pos,v0,v1,v2,v3]
  grind
def term_227 (q e : Int) : Int := (((-1))*(if ((5)≤(e) ∧ (e)≤(q+3) ∧ (e)≤((4)*q+(-1))) then (if (((2)*q+2)≤(min ((2)*q+3) (e)) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((min ((2)*q+3) (e))-((2)*q+2))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int)))
theorem term_227_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_227 q e=(0:Int) := by
  have v0 : ¬((5)≤(e) ∧ (e)≤(q+3) ∧ (e)≤((4)*q+(-1))) := by omega
  simp only [term_227,tri2,pos,v0]
  grind
def term_228 (q e : Int) : Int := (if ((5)≤(e)) then (if ((max ((4)*q+(-2)) (e))≤((4)*q+(-1)) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) ((((4)*q+(-1))-(max ((4)*q+(-2)) (e)))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_228_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_228 q e=(4) := by
  have v0 : ((5)≤(e)) := by omega
  have v1 : max ((4)*q+(-2)) (e)=((4)*q+(-2)) := by omega
  have v2 : ((max ((4)*q+(-2)) (e))≤((4)*q+(-1)) ∧ (0:Int)≤(0:Int)) := by omega
  have v3 : (((4)*q+(-2))≤((4)*q+(-1)) ∧ (0:Int)≤(0:Int)) := by omega
  have v4 : max (0:Int) ((((4)*q+(-1))-(max ((4)*q+(-2)) (e)))+(1))=(2) := by omega
  have v5 : max (0:Int) ((((4)*q+(-1))-((4)*q+(-2)))+(1))=(2) := by omega
  have v6 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_228,tri2,pos,v0,v1,v2,v3,v4,v5,v6]
  grind
def term_229 (q e : Int) : Int := (if ((5)≤(e) ∧ (e)≤((4)*q+(-2))) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_229_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_229 q e=(2) := by
  have v0 : ((5)≤(e) ∧ (e)≤((4)*q+(-2))) := by omega
  have v1 : ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) := by omega
  have v2 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_229,tri2,pos,v0,v1,v2]
  grind
def term_230 (q e : Int) : Int := (if (((4)*q)≤(e) ∧ (e)≤((4)*q)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_230_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_230 q e=(0*q+0*e+0) := by
  have v0 : ¬(((4)*q)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_230,tri2,pos,v0]
  grind
def term_231 (q e : Int) : Int := (((-1))*(if ((5)≤(e) ∧ (e)≤((4)*q+(-2)) ∧ ((4)*q)≤(e) ∧ (e)≤((4)*q)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int)))
theorem term_231_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_231 q e=(0:Int) := by
  have v0 : ¬((5)≤(e) ∧ (e)≤((4)*q+(-2)) ∧ ((4)*q)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_231,tri2,pos,v0]
  grind
def term_232 (q e : Int) : Int := (if ((5)≤(e)) then (if ((max ((4)*q+(-2)) (e))≤((4)*q+(-1)) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) ((((4)*q+(-1))-(max ((4)*q+(-2)) (e)))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_232_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_232 q e=(4) := by
  have v0 : ((5)≤(e)) := by omega
  have v1 : max ((4)*q+(-2)) (e)=((4)*q+(-2)) := by omega
  have v2 : ((max ((4)*q+(-2)) (e))≤((4)*q+(-1)) ∧ (0:Int)≤(0:Int)) := by omega
  have v3 : (((4)*q+(-2))≤((4)*q+(-1)) ∧ (0:Int)≤(0:Int)) := by omega
  have v4 : max (0:Int) ((((4)*q+(-1))-(max ((4)*q+(-2)) (e)))+(1))=(2) := by omega
  have v5 : max (0:Int) ((((4)*q+(-1))-((4)*q+(-2)))+(1))=(2) := by omega
  have v6 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_232,tri2,pos,v0,v1,v2,v3,v4,v5,v6]
  grind
def term_233 (q e : Int) : Int := (if ((5)≤(e)) then (if ((max ((2)*q+2) (e))≤((3)*q) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) ((((3)*q)-(max ((2)*q+2) (e)))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_233_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_233 q e=(2*q+(-2)) := by
  have v0 : ((5)≤(e)) := by omega
  have v1 : max ((2)*q+2) (e)=((2)*q+2) := by omega
  have v2 : ((max ((2)*q+2) (e))≤((3)*q) ∧ (0:Int)≤(0:Int)) := by omega
  have v3 : (((2)*q+2)≤((3)*q) ∧ (0:Int)≤(0:Int)) := by omega
  have v4 : max (0:Int) ((((3)*q)-(max ((2)*q+2) (e)))+(1))=(q+(-1)) := by omega
  have v5 : max (0:Int) ((((3)*q)-((2)*q+2))+(1))=(q+(-1)) := by omega
  have v6 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_233,tri2,pos,v0,v1,v2,v3,v4,v5,v6]
  grind
def term_234 (q e : Int) : Int := (if (((3)*q+2)≤(e) ∧ (e)≤((4)*q+(-1))) then (if (((2)*q+2)≤((3)*q) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) ((((3)*q)-((2)*q+2))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_234_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_234 q e=(0*q+0*e+0) := by
  have v0 : ¬(((3)*q+2)≤(e) ∧ (e)≤((4)*q+(-1))) := by omega
  simp only [term_234,tri2,pos,v0]
  grind
def term_235 (q e : Int) : Int := (((-1))*(if ((5)≤(e) ∧ ((3)*q+2)≤(e) ∧ (e)≤((4)*q+(-1))) then (if ((max ((2)*q+2) (e))≤((3)*q) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) ((((3)*q)-(max ((2)*q+2) (e)))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int)))
theorem term_235_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_235 q e=(0:Int) := by
  have v0 : ¬((5)≤(e) ∧ ((3)*q+2)≤(e) ∧ (e)≤((4)*q+(-1))) := by omega
  simp only [term_235,tri2,pos,v0]
  grind
def term_236 (q e : Int) : Int := (if ((5)≤(e) ∧ (e)≤(q+3)) then (if ((q+5)≤((2)*q+1) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) ((((2)*q+1)-(q+5))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_236_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_236 q e=(0*q+0*e+0) := by
  have v0 : ¬((5)≤(e) ∧ (e)≤(q+3)) := by omega
  simp only [term_236,tri2,pos,v0]
  grind
def term_237 (q e : Int) : Int := (if ((e)≤((4)*q+(-1))) then (if ((q+5)≤(min ((2)*q+1) (e)) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((min ((2)*q+1) (e))-(q+5))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_237_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_237 q e=(0*q+0*e+0) := by
  have v0 : ((e)≤((4)*q+(-1))) := by omega
  have v1 : min ((2)*q+1) (e)=(e) := by omega
  have v2 : ¬((q+5)≤(min ((2)*q+1) (e)) ∧ (0:Int)≤(0:Int)) := by omega
  have v3 : ¬((q+5)≤(e) ∧ (0:Int)≤(0:Int)) := by omega
  simp only [term_237,tri2,pos,v0,v1,v2,v3]
  grind
def term_238 (q e : Int) : Int := (((-1))*(if ((5)≤(e) ∧ (e)≤(q+3) ∧ (e)≤((4)*q+(-1))) then (if ((q+5)≤(min ((2)*q+1) (e)) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((min ((2)*q+1) (e))-(q+5))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int)))
theorem term_238_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_238 q e=(0:Int) := by
  have v0 : ¬((5)≤(e) ∧ (e)≤(q+3) ∧ (e)≤((4)*q+(-1))) := by omega
  simp only [term_238,tri2,pos,v0]
  grind
def term_239 (q e : Int) : Int := (if ((5)≤(e) ∧ (e)≤(q+3)) then (if (((2)*q+2)≤((2)*q+3) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) ((((2)*q+3)-((2)*q+2))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_239_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_239 q e=(0*q+0*e+0) := by
  have v0 : ¬((5)≤(e) ∧ (e)≤(q+3)) := by omega
  simp only [term_239,tri2,pos,v0]
  grind
def term_240 (q e : Int) : Int := (if ((e)≤((4)*q+(-1))) then (if (((2)*q+2)≤(min ((2)*q+3) (e)) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((min ((2)*q+3) (e))-((2)*q+2))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_240_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_240 q e=(0*q+0*e+0) := by
  have v0 : ((e)≤((4)*q+(-1))) := by omega
  have v1 : min ((2)*q+3) (e)=(e) := by omega
  have v2 : ¬(((2)*q+2)≤(min ((2)*q+3) (e)) ∧ (0:Int)≤(0:Int)) := by omega
  have v3 : ¬(((2)*q+2)≤(e) ∧ (0:Int)≤(0:Int)) := by omega
  simp only [term_240,tri2,pos,v0,v1,v2,v3]
  grind
def term_241 (q e : Int) : Int := (((-1))*(if ((5)≤(e) ∧ (e)≤(q+3) ∧ (e)≤((4)*q+(-1))) then (if (((2)*q+2)≤(min ((2)*q+3) (e)) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((min ((2)*q+3) (e))-((2)*q+2))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int)))
theorem term_241_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_241 q e=(0:Int) := by
  have v0 : ¬((5)≤(e) ∧ (e)≤(q+3) ∧ (e)≤((4)*q+(-1))) := by omega
  simp only [term_241,tri2,pos,v0]
  grind
def term_242 (q e : Int) : Int := (if ((5)≤(e)) then (if ((max ((2)*q+2) (e))≤((3)*q+(-1)) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) ((((3)*q+(-1))-(max ((2)*q+2) (e)))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_242_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_242 q e=(2*q+(-4)) := by
  have v0 : ((5)≤(e)) := by omega
  have v1 : max ((2)*q+2) (e)=((2)*q+2) := by omega
  have v2 : ((max ((2)*q+2) (e))≤((3)*q+(-1)) ∧ (0:Int)≤(0:Int)) := by omega
  have v3 : (((2)*q+2)≤((3)*q+(-1)) ∧ (0:Int)≤(0:Int)) := by omega
  have v4 : max (0:Int) ((((3)*q+(-1))-(max ((2)*q+2) (e)))+(1))=(q+(-2)) := by omega
  have v5 : max (0:Int) ((((3)*q+(-1))-((2)*q+2))+(1))=(q+(-2)) := by omega
  have v6 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_242,tri2,pos,v0,v1,v2,v3,v4,v5,v6]
  grind
def term_243 (q e : Int) : Int := (if (((3)*q+1)≤(e) ∧ (e)≤((4)*q+(-1))) then (if (((2)*q+2)≤((3)*q+(-1)) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) ((((3)*q+(-1))-((2)*q+2))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_243_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_243 q e=(0*q+0*e+0) := by
  have v0 : ¬(((3)*q+1)≤(e) ∧ (e)≤((4)*q+(-1))) := by omega
  simp only [term_243,tri2,pos,v0]
  grind
def term_244 (q e : Int) : Int := (((-1))*(if ((5)≤(e) ∧ ((3)*q+1)≤(e) ∧ (e)≤((4)*q+(-1))) then (if ((max ((2)*q+2) (e))≤((3)*q+(-1)) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) ((((3)*q+(-1))-(max ((2)*q+2) (e)))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int)))
theorem term_244_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_244 q e=(0:Int) := by
  have v0 : ¬((5)≤(e) ∧ ((3)*q+1)≤(e) ∧ (e)≤((4)*q+(-1))) := by omega
  simp only [term_244,tri2,pos,v0]
  grind
def term_245 (q e : Int) : Int := (if ((5)≤(e)) then (if ((max (4) (e))≤((2)*q) ∧ ((2)*q+2)≤((2)*q+3)) then (((2)*(max (0:Int) ((((2)*q)-(max (4) (e)))+(1))))*(max (0:Int) ((((2)*q+3)-((2)*q+2))+(1)))) else (0:Int)) else (0:Int))
theorem term_245_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_245 q e=(8*q+(-4)*e+4) := by
  have v0 : ((5)≤(e)) := by omega
  have v1 : max (4) (e)=(e) := by omega
  have v2 : ((max (4) (e))≤((2)*q) ∧ ((2)*q+2)≤((2)*q+3)) := by omega
  have v3 : ((e)≤((2)*q) ∧ ((2)*q+2)≤((2)*q+3)) := by omega
  have v4 : max (0:Int) ((((2)*q)-(max (4) (e)))+(1))=((2)*q+(-e)+1) := by omega
  have v5 : max (0:Int) ((((2)*q)-(e))+(1))=((2)*q+(-e)+1) := by omega
  have v6 : max (0:Int) ((((2)*q+3)-((2)*q+2))+(1))=(2) := by omega
  simp only [term_245,tri2,pos,v0,v1,v2,v3,v4,v5,v6]
  grind
def term_246 (q e : Int) : Int := (if ((e)≤((4)*q)) then (if ((4)≤((2)*q) ∧ ((2)*q+2)≤(min ((2)*q+3) (e))) then (((2)*(max (0:Int) ((((2)*q)-(4))+(1))))*(max (0:Int) (((min ((2)*q+3) (e))-((2)*q+2))+(1)))) else (0:Int)) else (0:Int))
theorem term_246_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_246 q e=(0*q+0*e+0) := by
  have v0 : ((e)≤((4)*q)) := by omega
  have v1 : min ((2)*q+3) (e)=(e) := by omega
  have v2 : ¬((4)≤((2)*q) ∧ ((2)*q+2)≤(min ((2)*q+3) (e))) := by omega
  have v3 : ¬((4)≤((2)*q) ∧ ((2)*q+2)≤(e)) := by omega
  simp only [term_246,tri2,pos,v0,v1,v2,v3]
  grind
def term_247 (q e : Int) : Int := (((-1))*(if ((5)≤(e) ∧ (e)≤((4)*q)) then (if ((max (4) (e))≤((2)*q) ∧ ((2)*q+2)≤(min ((2)*q+3) (e))) then (((2)*(max (0:Int) ((((2)*q)-(max (4) (e)))+(1))))*(max (0:Int) (((min ((2)*q+3) (e))-((2)*q+2))+(1)))) else (0:Int)) else (0:Int)))
theorem term_247_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_247 q e=(0:Int) := by
  have v0 : ((5)≤(e) ∧ (e)≤((4)*q)) := by omega
  have v1 : max (4) (e)=(e) := by omega
  have v2 : min ((2)*q+3) (e)=(e) := by omega
  have v3 : ¬((max (4) (e))≤((2)*q) ∧ ((2)*q+2)≤(min ((2)*q+3) (e))) := by omega
  have v4 : ¬((e)≤((2)*q) ∧ ((2)*q+2)≤(e)) := by omega
  simp only [term_247,tri2,pos,v0,v1,v2,v3,v4]
  grind
def term_248 (q e : Int) : Int := (if ((5)≤(e) ∧ (e)≤((2)*q)) then (if (((2)*q+4)≤((4)*q+(-1)) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) ((((4)*q+(-1))-((2)*q+4))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_248_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_248 q e=(4*q+(-8)) := by
  have v0 : ((5)≤(e) ∧ (e)≤((2)*q)) := by omega
  have v1 : (((2)*q+4)≤((4)*q+(-1)) ∧ (0:Int)≤(0:Int)) := by omega
  have v2 : max (0:Int) ((((4)*q+(-1))-((2)*q+4))+(1))=((2)*q+(-4)) := by omega
  have v3 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_248,tri2,pos,v0,v1,v2,v3]
  grind
def term_249 (q e : Int) : Int := (if ((e)≤((4)*q)) then (if (((2)*q+4)≤(min ((4)*q+(-1)) (e)) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((min ((4)*q+(-1)) (e))-((2)*q+4))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_249_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_249 q e=(0*q+0*e+0) := by
  have v0 : ((e)≤((4)*q)) := by omega
  have v1 : min ((4)*q+(-1)) (e)=(e) := by omega
  have v2 : ¬(((2)*q+4)≤(min ((4)*q+(-1)) (e)) ∧ (0:Int)≤(0:Int)) := by omega
  have v3 : ¬(((2)*q+4)≤(e) ∧ (0:Int)≤(0:Int)) := by omega
  simp only [term_249,tri2,pos,v0,v1,v2,v3]
  grind
def term_250 (q e : Int) : Int := (((-1))*(if ((5)≤(e) ∧ (e)≤((2)*q) ∧ (e)≤((4)*q)) then (if (((2)*q+4)≤(min ((4)*q+(-1)) (e)) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((min ((4)*q+(-1)) (e))-((2)*q+4))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int)))
theorem term_250_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_250 q e=(0:Int) := by
  have v0 : ((5)≤(e) ∧ (e)≤((2)*q) ∧ (e)≤((4)*q)) := by omega
  have v1 : min ((4)*q+(-1)) (e)=(e) := by omega
  have v2 : ¬(((2)*q+4)≤(min ((4)*q+(-1)) (e)) ∧ (0:Int)≤(0:Int)) := by omega
  have v3 : ¬(((2)*q+4)≤(e) ∧ (0:Int)≤(0:Int)) := by omega
  simp only [term_250,tri2,pos,v0,v1,v2,v3]
  grind
def term_251 (q e : Int) : Int := (if ((5)≤(e) ∧ (e)≤((2)*q)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_251_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_251 q e=(2) := by
  have v0 : ((5)≤(e) ∧ (e)≤((2)*q)) := by omega
  have v1 : ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) := by omega
  have v2 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_251,tri2,pos,v0,v1,v2]
  grind
def term_252 (q e : Int) : Int := (if (((2)*q+2)≤(e) ∧ (e)≤((4)*q+(-2))) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_252_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_252 q e=(0*q+0*e+0) := by
  have v0 : ¬(((2)*q+2)≤(e) ∧ (e)≤((4)*q+(-2))) := by omega
  simp only [term_252,tri2,pos,v0]
  grind
def term_253 (q e : Int) : Int := (if (((4)*q)≤(e) ∧ (e)≤((4)*q)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_253_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_253 q e=(0*q+0*e+0) := by
  have v0 : ¬(((4)*q)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_253,tri2,pos,v0]
  grind
def term_254 (q e : Int) : Int := (((-1))*(if ((5)≤(e) ∧ (e)≤((2)*q) ∧ ((2)*q+2)≤(e) ∧ (e)≤((4)*q+(-2))) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int)))
theorem term_254_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_254 q e=(0:Int) := by
  have v0 : ¬((5)≤(e) ∧ (e)≤((2)*q) ∧ ((2)*q+2)≤(e) ∧ (e)≤((4)*q+(-2))) := by omega
  simp only [term_254,tri2,pos,v0]
  grind
def term_255 (q e : Int) : Int := (((-1))*(if ((5)≤(e) ∧ (e)≤((2)*q) ∧ ((4)*q)≤(e) ∧ (e)≤((4)*q)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int)))
theorem term_255_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_255 q e=(0:Int) := by
  have v0 : ¬((5)≤(e) ∧ (e)≤((2)*q) ∧ ((4)*q)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_255,tri2,pos,v0]
  grind
def term_256 (q e : Int) : Int := (((-1))*(if (((2)*q+2)≤(e) ∧ (e)≤((4)*q+(-2)) ∧ ((4)*q)≤(e) ∧ (e)≤((4)*q)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int)))
theorem term_256_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_256 q e=(0:Int) := by
  have v0 : ¬(((2)*q+2)≤(e) ∧ (e)≤((4)*q+(-2)) ∧ ((4)*q)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_256,tri2,pos,v0]
  grind
def term_257 (q e : Int) : Int := (if ((5)≤(e) ∧ (e)≤((2)*q) ∧ ((2)*q+2)≤(e) ∧ (e)≤((4)*q+(-2)) ∧ ((4)*q)≤(e) ∧ (e)≤((4)*q)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_257_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_257 q e=(0*q+0*e+0) := by
  have v0 : ¬((5)≤(e) ∧ (e)≤((2)*q) ∧ ((2)*q+2)≤(e) ∧ (e)≤((4)*q+(-2)) ∧ ((4)*q)≤(e) ∧ (e)≤((4)*q)) := by omega
  simp only [term_257,tri2,pos,v0]
  grind
def term_258 (q e : Int) : Int := (if ((5)≤(e) ∧ (e)≤((2)*q+1)) then (if (((2)*q+3)≤((4)*q) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) ((((4)*q)-((2)*q+3))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_258_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_258 q e=(4*q+(-4)) := by
  have v0 : ((5)≤(e) ∧ (e)≤((2)*q+1)) := by omega
  have v1 : (((2)*q+3)≤((4)*q) ∧ (0:Int)≤(0:Int)) := by omega
  have v2 : max (0:Int) ((((4)*q)-((2)*q+3))+(1))=((2)*q+(-2)) := by omega
  have v3 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_258,tri2,pos,v0,v1,v2,v3]
  grind
def term_259 (q e : Int) : Int := (if ((e)≤((4)*q)) then (if (((2)*q+3)≤(min ((4)*q) (e)) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((min ((4)*q) (e))-((2)*q+3))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_259_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_259 q e=(0*q+0*e+0) := by
  have v0 : ((e)≤((4)*q)) := by omega
  have v1 : min ((4)*q) (e)=(e) := by omega
  have v2 : ¬(((2)*q+3)≤(min ((4)*q) (e)) ∧ (0:Int)≤(0:Int)) := by omega
  have v3 : ¬(((2)*q+3)≤(e) ∧ (0:Int)≤(0:Int)) := by omega
  simp only [term_259,tri2,pos,v0,v1,v2,v3]
  grind
def term_260 (q e : Int) : Int := (((-1))*(if ((5)≤(e) ∧ (e)≤((2)*q+1) ∧ (e)≤((4)*q)) then (if (((2)*q+3)≤(min ((4)*q) (e)) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((min ((4)*q) (e))-((2)*q+3))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int)))
theorem term_260_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_260 q e=(0:Int) := by
  have v0 : ((5)≤(e) ∧ (e)≤((2)*q+1) ∧ (e)≤((4)*q)) := by omega
  have v1 : min ((4)*q) (e)=(e) := by omega
  have v2 : ¬(((2)*q+3)≤(min ((4)*q) (e)) ∧ (0:Int)≤(0:Int)) := by omega
  have v3 : ¬(((2)*q+3)≤(e) ∧ (0:Int)≤(0:Int)) := by omega
  simp only [term_260,tri2,pos,v0,v1,v2,v3]
  grind
def term_261 (q e : Int) : Int := (if ((e)≤((4)*q)) then (if ((6)≤(min ((2)*q+1) (e)) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((min ((2)*q+1) (e))-(6))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_261_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_261 q e=(2*e+(-10)) := by
  have v0 : ((e)≤((4)*q)) := by omega
  have v1 : min ((2)*q+1) (e)=(e) := by omega
  have v2 : ((6)≤(min ((2)*q+1) (e)) ∧ (0:Int)≤(0:Int)) := by omega
  have v3 : ((6)≤(e) ∧ (0:Int)≤(0:Int)) := by omega
  have v4 : max (0:Int) (((min ((2)*q+1) (e))-(6))+(1))=(e+(-5)) := by omega
  have v5 : max (0:Int) (((e)-(6))+(1))=(e+(-5)) := by omega
  have v6 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_261,tri2,pos,v0,v1,v2,v3,v4,v5,v6]
  grind
def term_262 (q e : Int) : Int := (if ((5)≤(e)) then (if ((max (5) (e))≤((2)*q+(-1)) ∧ (0:Int)≤((2)*q+1)) then ((((tri2 (((((2)*q+1)-(2))+(1))-(max (5) (e))))-(tri2 ((((2)*q+1)-(2))-((2)*q+(-1)))))-(tri2 (((0:Int)-(2))-(max (5) (e)))))+(tri2 ((((0:Int)-(2))-((2)*q+(-1)))-(1)))) else (0:Int)) else (0:Int))
theorem term_262_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_262 q e=(0*q+0*e+0) := by
  have v0 : ((5)≤(e)) := by omega
  have v1 : max (5) (e)=(e) := by omega
  have v2 : ¬((max (5) (e))≤((2)*q+(-1)) ∧ (0:Int)≤((2)*q+1)) := by omega
  have v3 : ¬((e)≤((2)*q+(-1)) ∧ (0:Int)≤((2)*q+1)) := by omega
  simp only [term_262,tri2,pos,v0,v1,v2,v3]
  grind
def term_263 (q e : Int) : Int := (if ((e)≤((4)*q)) then (if ((5)≤((2)*q+(-1)) ∧ (0:Int)≤(min ((2)*q+1) (e))) then ((((tri2 ((((min ((2)*q+1) (e))-(2))+(1))-(5)))-(tri2 (((min ((2)*q+1) (e))-(2))-((2)*q+(-1)))))-(tri2 (((0:Int)-(2))-(5))))+(tri2 ((((0:Int)-(2))-((2)*q+(-1)))-(1)))) else (0:Int)) else (0:Int))
theorem term_263_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_263 q e=(1*e*e+(-11)*e+30) := by
  have v0 : ((e)≤((4)*q)) := by omega
  have v1 : min ((2)*q+1) (e)=(e) := by omega
  have v2 : ((5)≤((2)*q+(-1)) ∧ (0:Int)≤(min ((2)*q+1) (e))) := by omega
  have v3 : ((5)≤((2)*q+(-1)) ∧ (0:Int)≤(e)) := by omega
  have v4 : max (0:Int) ((((min ((2)*q+1) (e))-(2))+(1))-(5))=(e+(-6)) := by omega
  have v5 : max (0:Int) ((((e)-(2))+(1))-(5))=(e+(-6)) := by omega
  have v6 : max (0:Int) (((min ((2)*q+1) (e))-(2))-((2)*q+(-1)))=(0:Int) := by omega
  have v7 : max (0:Int) (((e)-(2))-((2)*q+(-1)))=(0:Int) := by omega
  have v8 : max (0:Int) (((0:Int)-(2))-(5))=(0:Int) := by omega
  have v9 : max (0:Int) ((((0:Int)-(2))-((2)*q+(-1)))-(1))=(0:Int) := by omega
  simp only [term_263,tri2,pos,v0,v1,v2,v3,v4,v5,v6,v7,v8,v9]
  grind
def term_264 (q e : Int) : Int := (((-1))*(if ((5)≤(e) ∧ (e)≤((4)*q)) then (if ((max (5) (e))≤((2)*q+(-1)) ∧ (0:Int)≤(min ((2)*q+1) (e))) then ((((tri2 ((((min ((2)*q+1) (e))-(2))+(1))-(max (5) (e))))-(tri2 (((min ((2)*q+1) (e))-(2))-((2)*q+(-1)))))-(tri2 (((0:Int)-(2))-(max (5) (e)))))+(tri2 ((((0:Int)-(2))-((2)*q+(-1)))-(1)))) else (0:Int)) else (0:Int)))
theorem term_264_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_264 q e=(0:Int) := by
  have v0 : ((5)≤(e) ∧ (e)≤((4)*q)) := by omega
  have v1 : max (5) (e)=(e) := by omega
  have v2 : min ((2)*q+1) (e)=(e) := by omega
  have v3 : ¬((max (5) (e))≤((2)*q+(-1)) ∧ (0:Int)≤(min ((2)*q+1) (e))) := by omega
  have v4 : ¬((e)≤((2)*q+(-1)) ∧ (0:Int)≤(e)) := by omega
  simp only [term_264,tri2,pos,v0,v1,v2,v3,v4]
  grind
def term_265 (q e : Int) : Int := (if ((5)≤(e) ∧ (e)≤((4)*q)) then (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int)) else (0:Int))
theorem term_265_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_265 q e=(2) := by
  have v0 : ((5)≤(e) ∧ (e)≤((4)*q)) := by omega
  have v1 : ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) := by omega
  have v2 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_265,tri2,pos,v0,v1,v2]
  grind
def term_266 (q e : Int) : Int := (if ((5)≤(e)) then (if ((max ((2)*q+2) (e))≤((4)*q+(-2)) ∧ (0:Int)≤((4)*q)) then ((((tri2 (((((4)*q)-(2))+(1))-(max ((2)*q+2) (e))))-(tri2 ((((4)*q)-(2))-((4)*q+(-2)))))-(tri2 (((0:Int)-(2))-(max ((2)*q+2) (e)))))+(tri2 ((((0:Int)-(2))-((4)*q+(-2)))-(1)))) else (0:Int)) else (0:Int))
theorem term_266_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_266 q e=(4*q*q+(-10)*q+6) := by
  have v0 : ((5)≤(e)) := by omega
  have v1 : max ((2)*q+2) (e)=((2)*q+2) := by omega
  have v2 : ((max ((2)*q+2) (e))≤((4)*q+(-2)) ∧ (0:Int)≤((4)*q)) := by omega
  have v3 : (((2)*q+2)≤((4)*q+(-2)) ∧ (0:Int)≤((4)*q)) := by omega
  have v4 : max (0:Int) (((((4)*q)-(2))+(1))-(max ((2)*q+2) (e)))=((2)*q+(-3)) := by omega
  have v5 : max (0:Int) (((((4)*q)-(2))+(1))-((2)*q+2))=((2)*q+(-3)) := by omega
  have v6 : max (0:Int) ((((4)*q)-(2))-((4)*q+(-2)))=(0:Int) := by omega
  have v7 : max (0:Int) (((0:Int)-(2))-(max ((2)*q+2) (e)))=(0:Int) := by omega
  have v8 : max (0:Int) (((0:Int)-(2))-((2)*q+2))=(0:Int) := by omega
  have v9 : max (0:Int) ((((0:Int)-(2))-((4)*q+(-2)))-(1))=(0:Int) := by omega
  simp only [term_266,tri2,pos,v0,v1,v2,v3,v4,v5,v6,v7,v8,v9]
  grind
def term_267 (q e : Int) : Int := (if ((e)≤((4)*q)) then (if (((2)*q+2)≤((4)*q+(-2)) ∧ (0:Int)≤(min ((4)*q) (e))) then ((((tri2 ((((min ((4)*q) (e))-(2))+(1))-((2)*q+2)))-(tri2 (((min ((4)*q) (e))-(2))-((4)*q+(-2)))))-(tri2 (((0:Int)-(2))-((2)*q+2))))+(tri2 ((((0:Int)-(2))-((4)*q+(-2)))-(1)))) else (0:Int)) else (0:Int))
theorem term_267_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_267 q e=(0:Int) := by
  have v0 : ((e)≤((4)*q)) := by omega
  have v1 : min ((4)*q) (e)=(e) := by omega
  have v2 : (((2)*q+2)≤((4)*q+(-2)) ∧ (0:Int)≤(min ((4)*q) (e))) := by omega
  have v3 : (((2)*q+2)≤((4)*q+(-2)) ∧ (0:Int)≤(e)) := by omega
  have v4 : max (0:Int) ((((min ((4)*q) (e))-(2))+(1))-((2)*q+2))=(0:Int) := by omega
  have v5 : max (0:Int) ((((e)-(2))+(1))-((2)*q+2))=(0:Int) := by omega
  have v6 : max (0:Int) (((min ((4)*q) (e))-(2))-((4)*q+(-2)))=(0:Int) := by omega
  have v7 : max (0:Int) (((e)-(2))-((4)*q+(-2)))=(0:Int) := by omega
  have v8 : max (0:Int) (((0:Int)-(2))-((2)*q+2))=(0:Int) := by omega
  have v9 : max (0:Int) ((((0:Int)-(2))-((4)*q+(-2)))-(1))=(0:Int) := by omega
  simp only [term_267,tri2,pos,v0,v1,v2,v3,v4,v5,v6,v7,v8,v9]
  grind
def term_268 (q e : Int) : Int := (((-1))*(if ((5)≤(e) ∧ (e)≤((4)*q)) then (if ((max ((2)*q+2) (e))≤((4)*q+(-2)) ∧ (0:Int)≤(min ((4)*q) (e))) then ((((tri2 ((((min ((4)*q) (e))-(2))+(1))-(max ((2)*q+2) (e))))-(tri2 (((min ((4)*q) (e))-(2))-((4)*q+(-2)))))-(tri2 (((0:Int)-(2))-(max ((2)*q+2) (e)))))+(tri2 ((((0:Int)-(2))-((4)*q+(-2)))-(1)))) else (0:Int)) else (0:Int)))
theorem term_268_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_268 q e=(0:Int) := by
  have v0 : ((5)≤(e) ∧ (e)≤((4)*q)) := by omega
  have v1 : max ((2)*q+2) (e)=((2)*q+2) := by omega
  have v2 : min ((4)*q) (e)=(e) := by omega
  have v3 : ((max ((2)*q+2) (e))≤((4)*q+(-2)) ∧ (0:Int)≤(min ((4)*q) (e))) := by omega
  have v4 : (((2)*q+2)≤((4)*q+(-2)) ∧ (0:Int)≤(e)) := by omega
  have v5 : max (0:Int) ((((min ((4)*q) (e))-(2))+(1))-(max ((2)*q+2) (e)))=(0:Int) := by omega
  have v6 : max (0:Int) ((((e)-(2))+(1))-((2)*q+2))=(0:Int) := by omega
  have v7 : max (0:Int) (((min ((4)*q) (e))-(2))-((4)*q+(-2)))=(0:Int) := by omega
  have v8 : max (0:Int) (((e)-(2))-((4)*q+(-2)))=(0:Int) := by omega
  have v9 : max (0:Int) (((0:Int)-(2))-(max ((2)*q+2) (e)))=(0:Int) := by omega
  have v10 : max (0:Int) (((0:Int)-(2))-((2)*q+2))=(0:Int) := by omega
  have v11 : max (0:Int) ((((0:Int)-(2))-((4)*q+(-2)))-(1))=(0:Int) := by omega
  simp only [term_268,tri2,pos,v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11]
  grind
def term_269 (q e : Int) : Int := (if ((5)≤(e)) then (if ((max ((2)*q+2) (e))≤((3)*q+(-1)) ∧ ((3)*q+3)≤((4)*q)) then (((2)*(max (0:Int) ((((3)*q+(-1))-(max ((2)*q+2) (e)))+(1))))*(max (0:Int) ((((4)*q)-((3)*q+3))+(1)))) else (0:Int)) else (0:Int))
theorem term_269_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_269 q e=(2*q*q+(-8)*q+8) := by
  have v0 : ((5)≤(e)) := by omega
  have v1 : max ((2)*q+2) (e)=((2)*q+2) := by omega
  have v2 : ((max ((2)*q+2) (e))≤((3)*q+(-1)) ∧ ((3)*q+3)≤((4)*q)) := by omega
  have v3 : (((2)*q+2)≤((3)*q+(-1)) ∧ ((3)*q+3)≤((4)*q)) := by omega
  have v4 : max (0:Int) ((((3)*q+(-1))-(max ((2)*q+2) (e)))+(1))=(q+(-2)) := by omega
  have v5 : max (0:Int) ((((3)*q+(-1))-((2)*q+2))+(1))=(q+(-2)) := by omega
  have v6 : max (0:Int) ((((4)*q)-((3)*q+3))+(1))=(q+(-2)) := by omega
  simp only [term_269,tri2,pos,v0,v1,v2,v3,v4,v5,v6]
  grind
def term_270 (q e : Int) : Int := (if (((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)) then (if (((2)*q+2)≤((3)*q+(-1)) ∧ ((3)*q+3)≤((4)*q)) then (((2)*(max (0:Int) ((((3)*q+(-1))-((2)*q+2))+(1))))*(max (0:Int) ((((4)*q)-((3)*q+3))+(1)))) else (0:Int)) else (0:Int))
theorem term_270_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_270 q e=(0*q+0*e+0) := by
  have v0 : ¬(((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)) := by omega
  simp only [term_270,tri2,pos,v0]
  grind
def term_271 (q e : Int) : Int := (if ((e)≤((4)*q)) then (if (((2)*q+2)≤((3)*q+(-1)) ∧ ((3)*q+3)≤(min ((4)*q) (e))) then (((2)*(max (0:Int) ((((3)*q+(-1))-((2)*q+2))+(1))))*(max (0:Int) (((min ((4)*q) (e))-((3)*q+3))+(1)))) else (0:Int)) else (0:Int))
theorem term_271_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_271 q e=(0*q+0*e+0) := by
  have v0 : ((e)≤((4)*q)) := by omega
  have v1 : min ((4)*q) (e)=(e) := by omega
  have v2 : ¬(((2)*q+2)≤((3)*q+(-1)) ∧ ((3)*q+3)≤(min ((4)*q) (e))) := by omega
  have v3 : ¬(((2)*q+2)≤((3)*q+(-1)) ∧ ((3)*q+3)≤(e)) := by omega
  simp only [term_271,tri2,pos,v0,v1,v2,v3]
  grind
def term_272 (q e : Int) : Int := (((-1))*(if ((5)≤(e) ∧ ((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)) then (if ((max ((2)*q+2) (e))≤((3)*q+(-1)) ∧ ((3)*q+3)≤((4)*q)) then (((2)*(max (0:Int) ((((3)*q+(-1))-(max ((2)*q+2) (e)))+(1))))*(max (0:Int) ((((4)*q)-((3)*q+3))+(1)))) else (0:Int)) else (0:Int)))
theorem term_272_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_272 q e=(0:Int) := by
  have v0 : ¬((5)≤(e) ∧ ((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)) := by omega
  simp only [term_272,tri2,pos,v0]
  grind
def term_273 (q e : Int) : Int := (((-1))*(if ((5)≤(e) ∧ (e)≤((4)*q)) then (if ((max ((2)*q+2) (e))≤((3)*q+(-1)) ∧ ((3)*q+3)≤(min ((4)*q) (e))) then (((2)*(max (0:Int) ((((3)*q+(-1))-(max ((2)*q+2) (e)))+(1))))*(max (0:Int) (((min ((4)*q) (e))-((3)*q+3))+(1)))) else (0:Int)) else (0:Int)))
theorem term_273_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_273 q e=(0:Int) := by
  have v0 : ((5)≤(e) ∧ (e)≤((4)*q)) := by omega
  have v1 : max ((2)*q+2) (e)=((2)*q+2) := by omega
  have v2 : min ((4)*q) (e)=(e) := by omega
  have v3 : ¬((max ((2)*q+2) (e))≤((3)*q+(-1)) ∧ ((3)*q+3)≤(min ((4)*q) (e))) := by omega
  have v4 : ¬(((2)*q+2)≤((3)*q+(-1)) ∧ ((3)*q+3)≤(e)) := by omega
  simp only [term_273,tri2,pos,v0,v1,v2,v3,v4]
  grind
def term_274 (q e : Int) : Int := (((-1))*(if (((3)*q+1)≤(e) ∧ (e)≤((3)*q+1) ∧ (e)≤((4)*q)) then (if (((2)*q+2)≤((3)*q+(-1)) ∧ ((3)*q+3)≤(min ((4)*q) (e))) then (((2)*(max (0:Int) ((((3)*q+(-1))-((2)*q+2))+(1))))*(max (0:Int) (((min ((4)*q) (e))-((3)*q+3))+(1)))) else (0:Int)) else (0:Int)))
theorem term_274_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_274 q e=(0:Int) := by
  have v0 : ¬(((3)*q+1)≤(e) ∧ (e)≤((3)*q+1) ∧ (e)≤((4)*q)) := by omega
  simp only [term_274,tri2,pos,v0]
  grind
def term_275 (q e : Int) : Int := (if ((5)≤(e) ∧ ((3)*q+1)≤(e) ∧ (e)≤((3)*q+1) ∧ (e)≤((4)*q)) then (if ((max ((2)*q+2) (e))≤((3)*q+(-1)) ∧ ((3)*q+3)≤(min ((4)*q) (e))) then (((2)*(max (0:Int) ((((3)*q+(-1))-(max ((2)*q+2) (e)))+(1))))*(max (0:Int) (((min ((4)*q) (e))-((3)*q+3))+(1)))) else (0:Int)) else (0:Int))
theorem term_275_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : term_275 q e=(0*q+0*e+0) := by
  have v0 : ¬((5)≤(e) ∧ ((3)*q+1)≤(e) ∧ (e)≤((3)*q+1) ∧ (e)≤((4)*q)) := by omega
  simp only [term_275,tri2,pos,v0]
  grind
def sumTerms (q e : Int) : Int := term_0 q e + term_1 q e + term_2 q e + term_3 q e + term_4 q e + term_5 q e + term_6 q e + term_7 q e + term_8 q e + term_9 q e + term_10 q e + term_11 q e + term_12 q e + term_13 q e + term_14 q e + term_15 q e + term_16 q e + term_17 q e + term_18 q e + term_19 q e + term_20 q e + term_21 q e + term_22 q e + term_23 q e + term_24 q e + term_25 q e + term_26 q e + term_27 q e + term_28 q e + term_29 q e + term_30 q e + term_31 q e + term_32 q e + term_33 q e + term_34 q e + term_35 q e + term_36 q e + term_37 q e + term_38 q e + term_39 q e + term_40 q e + term_41 q e + term_42 q e + term_43 q e + term_44 q e + term_45 q e + term_46 q e + term_47 q e + term_48 q e + term_49 q e + term_50 q e + term_51 q e + term_52 q e + term_53 q e + term_54 q e + term_55 q e + term_56 q e + term_57 q e + term_58 q e + term_59 q e + term_60 q e + term_61 q e + term_62 q e + term_63 q e + term_64 q e + term_65 q e + term_66 q e + term_67 q e + term_68 q e + term_69 q e + term_70 q e + term_71 q e + term_72 q e + term_73 q e + term_74 q e + term_75 q e + term_76 q e + term_77 q e + term_78 q e + term_79 q e + term_80 q e + term_81 q e + term_82 q e + term_83 q e + term_84 q e + term_85 q e + term_86 q e + term_87 q e + term_88 q e + term_89 q e + term_90 q e + term_91 q e + term_92 q e + term_93 q e + term_94 q e + term_95 q e + term_96 q e + term_97 q e + term_98 q e + term_99 q e + term_100 q e + term_101 q e + term_102 q e + term_103 q e + term_104 q e + term_105 q e + term_106 q e + term_107 q e + term_108 q e + term_109 q e + term_110 q e + term_111 q e + term_112 q e + term_113 q e + term_114 q e + term_115 q e + term_116 q e + term_117 q e + term_118 q e + term_119 q e + term_120 q e + term_121 q e + term_122 q e + term_123 q e + term_124 q e + term_125 q e + term_126 q e + term_127 q e + term_128 q e + term_129 q e + term_130 q e + term_131 q e + term_132 q e + term_133 q e + term_134 q e + term_135 q e + term_136 q e + term_137 q e + term_138 q e + term_139 q e + term_140 q e + term_141 q e + term_142 q e + term_143 q e + term_144 q e + term_145 q e + term_146 q e + term_147 q e + term_148 q e + term_149 q e + term_150 q e + term_151 q e + term_152 q e + term_153 q e + term_154 q e + term_155 q e + term_156 q e + term_157 q e + term_158 q e + term_159 q e + term_160 q e + term_161 q e + term_162 q e + term_163 q e + term_164 q e + term_165 q e + term_166 q e + term_167 q e + term_168 q e + term_169 q e + term_170 q e + term_171 q e + term_172 q e + term_173 q e + term_174 q e + term_175 q e + term_176 q e + term_177 q e + term_178 q e + term_179 q e + term_180 q e + term_181 q e + term_182 q e + term_183 q e + term_184 q e + term_185 q e + term_186 q e + term_187 q e + term_188 q e + term_189 q e + term_190 q e + term_191 q e + term_192 q e + term_193 q e + term_194 q e + term_195 q e + term_196 q e + term_197 q e + term_198 q e + term_199 q e + term_200 q e + term_201 q e + term_202 q e + term_203 q e + term_204 q e + term_205 q e + term_206 q e + term_207 q e + term_208 q e + term_209 q e + term_210 q e + term_211 q e + term_212 q e + term_213 q e + term_214 q e + term_215 q e + term_216 q e + term_217 q e + term_218 q e + term_219 q e + term_220 q e + term_221 q e + term_222 q e + term_223 q e + term_224 q e + term_225 q e + term_226 q e + term_227 q e + term_228 q e + term_229 q e + term_230 q e + term_231 q e + term_232 q e + term_233 q e + term_234 q e + term_235 q e + term_236 q e + term_237 q e + term_238 q e + term_239 q e + term_240 q e + term_241 q e + term_242 q e + term_243 q e + term_244 q e + term_245 q e + term_246 q e + term_247 q e + term_248 q e + term_249 q e + term_250 q e + term_251 q e + term_252 q e + term_253 q e + term_254 q e + term_255 q e + term_256 q e + term_257 q e + term_258 q e + term_259 q e + term_260 q e + term_261 q e + term_262 q e + term_263 q e + term_264 q e + term_265 q e + term_266 q e + term_267 q e + term_268 q e + term_269 q e + term_270 q e + term_271 q e + term_272 q e + term_273 q e + term_274 q e + term_275 q e
theorem cell_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤((-q)+e+(-4))) (h2 : 0≤((2)*q+(-e))) (h3 : 0≤((-2)*q+e)) (h4 : 0≤(q+(-e)+4)) : sumTerms q e=(16*q*q+4*q*e+(-10)*q+(-2)*e*e+20*e+(-70)) := by
  simp only [sumTerms,term_0_identity q e h0 h1 h2 h3 h4,term_1_identity q e h0 h1 h2 h3 h4,term_2_identity q e h0 h1 h2 h3 h4,term_3_identity q e h0 h1 h2 h3 h4,term_4_identity q e h0 h1 h2 h3 h4,term_5_identity q e h0 h1 h2 h3 h4,term_6_identity q e h0 h1 h2 h3 h4,term_7_identity q e h0 h1 h2 h3 h4,term_8_identity q e h0 h1 h2 h3 h4,term_9_identity q e h0 h1 h2 h3 h4,term_10_identity q e h0 h1 h2 h3 h4,term_11_identity q e h0 h1 h2 h3 h4,term_12_identity q e h0 h1 h2 h3 h4,term_13_identity q e h0 h1 h2 h3 h4,term_14_identity q e h0 h1 h2 h3 h4,term_15_identity q e h0 h1 h2 h3 h4,term_16_identity q e h0 h1 h2 h3 h4,term_17_identity q e h0 h1 h2 h3 h4,term_18_identity q e h0 h1 h2 h3 h4,term_19_identity q e h0 h1 h2 h3 h4,term_20_identity q e h0 h1 h2 h3 h4,term_21_identity q e h0 h1 h2 h3 h4,term_22_identity q e h0 h1 h2 h3 h4,term_23_identity q e h0 h1 h2 h3 h4,term_24_identity q e h0 h1 h2 h3 h4,term_25_identity q e h0 h1 h2 h3 h4,term_26_identity q e h0 h1 h2 h3 h4,term_27_identity q e h0 h1 h2 h3 h4,term_28_identity q e h0 h1 h2 h3 h4,term_29_identity q e h0 h1 h2 h3 h4,term_30_identity q e h0 h1 h2 h3 h4,term_31_identity q e h0 h1 h2 h3 h4,term_32_identity q e h0 h1 h2 h3 h4,term_33_identity q e h0 h1 h2 h3 h4,term_34_identity q e h0 h1 h2 h3 h4,term_35_identity q e h0 h1 h2 h3 h4,term_36_identity q e h0 h1 h2 h3 h4,term_37_identity q e h0 h1 h2 h3 h4,term_38_identity q e h0 h1 h2 h3 h4,term_39_identity q e h0 h1 h2 h3 h4,term_40_identity q e h0 h1 h2 h3 h4,term_41_identity q e h0 h1 h2 h3 h4,term_42_identity q e h0 h1 h2 h3 h4,term_43_identity q e h0 h1 h2 h3 h4,term_44_identity q e h0 h1 h2 h3 h4,term_45_identity q e h0 h1 h2 h3 h4,term_46_identity q e h0 h1 h2 h3 h4,term_47_identity q e h0 h1 h2 h3 h4,term_48_identity q e h0 h1 h2 h3 h4,term_49_identity q e h0 h1 h2 h3 h4,term_50_identity q e h0 h1 h2 h3 h4,term_51_identity q e h0 h1 h2 h3 h4,term_52_identity q e h0 h1 h2 h3 h4,term_53_identity q e h0 h1 h2 h3 h4,term_54_identity q e h0 h1 h2 h3 h4,term_55_identity q e h0 h1 h2 h3 h4,term_56_identity q e h0 h1 h2 h3 h4,term_57_identity q e h0 h1 h2 h3 h4,term_58_identity q e h0 h1 h2 h3 h4,term_59_identity q e h0 h1 h2 h3 h4,term_60_identity q e h0 h1 h2 h3 h4,term_61_identity q e h0 h1 h2 h3 h4,term_62_identity q e h0 h1 h2 h3 h4,term_63_identity q e h0 h1 h2 h3 h4,term_64_identity q e h0 h1 h2 h3 h4,term_65_identity q e h0 h1 h2 h3 h4,term_66_identity q e h0 h1 h2 h3 h4,term_67_identity q e h0 h1 h2 h3 h4,term_68_identity q e h0 h1 h2 h3 h4,term_69_identity q e h0 h1 h2 h3 h4,term_70_identity q e h0 h1 h2 h3 h4,term_71_identity q e h0 h1 h2 h3 h4,term_72_identity q e h0 h1 h2 h3 h4,term_73_identity q e h0 h1 h2 h3 h4,term_74_identity q e h0 h1 h2 h3 h4,term_75_identity q e h0 h1 h2 h3 h4,term_76_identity q e h0 h1 h2 h3 h4,term_77_identity q e h0 h1 h2 h3 h4,term_78_identity q e h0 h1 h2 h3 h4,term_79_identity q e h0 h1 h2 h3 h4,term_80_identity q e h0 h1 h2 h3 h4,term_81_identity q e h0 h1 h2 h3 h4,term_82_identity q e h0 h1 h2 h3 h4,term_83_identity q e h0 h1 h2 h3 h4,term_84_identity q e h0 h1 h2 h3 h4,term_85_identity q e h0 h1 h2 h3 h4,term_86_identity q e h0 h1 h2 h3 h4,term_87_identity q e h0 h1 h2 h3 h4,term_88_identity q e h0 h1 h2 h3 h4,term_89_identity q e h0 h1 h2 h3 h4,term_90_identity q e h0 h1 h2 h3 h4,term_91_identity q e h0 h1 h2 h3 h4,term_92_identity q e h0 h1 h2 h3 h4,term_93_identity q e h0 h1 h2 h3 h4,term_94_identity q e h0 h1 h2 h3 h4,term_95_identity q e h0 h1 h2 h3 h4,term_96_identity q e h0 h1 h2 h3 h4,term_97_identity q e h0 h1 h2 h3 h4,term_98_identity q e h0 h1 h2 h3 h4,term_99_identity q e h0 h1 h2 h3 h4,term_100_identity q e h0 h1 h2 h3 h4,term_101_identity q e h0 h1 h2 h3 h4,term_102_identity q e h0 h1 h2 h3 h4,term_103_identity q e h0 h1 h2 h3 h4,term_104_identity q e h0 h1 h2 h3 h4,term_105_identity q e h0 h1 h2 h3 h4,term_106_identity q e h0 h1 h2 h3 h4,term_107_identity q e h0 h1 h2 h3 h4,term_108_identity q e h0 h1 h2 h3 h4,term_109_identity q e h0 h1 h2 h3 h4,term_110_identity q e h0 h1 h2 h3 h4,term_111_identity q e h0 h1 h2 h3 h4,term_112_identity q e h0 h1 h2 h3 h4,term_113_identity q e h0 h1 h2 h3 h4,term_114_identity q e h0 h1 h2 h3 h4,term_115_identity q e h0 h1 h2 h3 h4,term_116_identity q e h0 h1 h2 h3 h4,term_117_identity q e h0 h1 h2 h3 h4,term_118_identity q e h0 h1 h2 h3 h4,term_119_identity q e h0 h1 h2 h3 h4,term_120_identity q e h0 h1 h2 h3 h4,term_121_identity q e h0 h1 h2 h3 h4,term_122_identity q e h0 h1 h2 h3 h4,term_123_identity q e h0 h1 h2 h3 h4,term_124_identity q e h0 h1 h2 h3 h4,term_125_identity q e h0 h1 h2 h3 h4,term_126_identity q e h0 h1 h2 h3 h4,term_127_identity q e h0 h1 h2 h3 h4,term_128_identity q e h0 h1 h2 h3 h4,term_129_identity q e h0 h1 h2 h3 h4,term_130_identity q e h0 h1 h2 h3 h4,term_131_identity q e h0 h1 h2 h3 h4,term_132_identity q e h0 h1 h2 h3 h4,term_133_identity q e h0 h1 h2 h3 h4,term_134_identity q e h0 h1 h2 h3 h4,term_135_identity q e h0 h1 h2 h3 h4,term_136_identity q e h0 h1 h2 h3 h4,term_137_identity q e h0 h1 h2 h3 h4,term_138_identity q e h0 h1 h2 h3 h4,term_139_identity q e h0 h1 h2 h3 h4,term_140_identity q e h0 h1 h2 h3 h4,term_141_identity q e h0 h1 h2 h3 h4,term_142_identity q e h0 h1 h2 h3 h4,term_143_identity q e h0 h1 h2 h3 h4,term_144_identity q e h0 h1 h2 h3 h4,term_145_identity q e h0 h1 h2 h3 h4,term_146_identity q e h0 h1 h2 h3 h4,term_147_identity q e h0 h1 h2 h3 h4,term_148_identity q e h0 h1 h2 h3 h4,term_149_identity q e h0 h1 h2 h3 h4,term_150_identity q e h0 h1 h2 h3 h4,term_151_identity q e h0 h1 h2 h3 h4,term_152_identity q e h0 h1 h2 h3 h4,term_153_identity q e h0 h1 h2 h3 h4,term_154_identity q e h0 h1 h2 h3 h4,term_155_identity q e h0 h1 h2 h3 h4,term_156_identity q e h0 h1 h2 h3 h4,term_157_identity q e h0 h1 h2 h3 h4,term_158_identity q e h0 h1 h2 h3 h4,term_159_identity q e h0 h1 h2 h3 h4,term_160_identity q e h0 h1 h2 h3 h4,term_161_identity q e h0 h1 h2 h3 h4,term_162_identity q e h0 h1 h2 h3 h4,term_163_identity q e h0 h1 h2 h3 h4,term_164_identity q e h0 h1 h2 h3 h4,term_165_identity q e h0 h1 h2 h3 h4,term_166_identity q e h0 h1 h2 h3 h4,term_167_identity q e h0 h1 h2 h3 h4,term_168_identity q e h0 h1 h2 h3 h4,term_169_identity q e h0 h1 h2 h3 h4,term_170_identity q e h0 h1 h2 h3 h4,term_171_identity q e h0 h1 h2 h3 h4,term_172_identity q e h0 h1 h2 h3 h4,term_173_identity q e h0 h1 h2 h3 h4,term_174_identity q e h0 h1 h2 h3 h4,term_175_identity q e h0 h1 h2 h3 h4,term_176_identity q e h0 h1 h2 h3 h4,term_177_identity q e h0 h1 h2 h3 h4,term_178_identity q e h0 h1 h2 h3 h4,term_179_identity q e h0 h1 h2 h3 h4,term_180_identity q e h0 h1 h2 h3 h4,term_181_identity q e h0 h1 h2 h3 h4,term_182_identity q e h0 h1 h2 h3 h4,term_183_identity q e h0 h1 h2 h3 h4,term_184_identity q e h0 h1 h2 h3 h4,term_185_identity q e h0 h1 h2 h3 h4,term_186_identity q e h0 h1 h2 h3 h4,term_187_identity q e h0 h1 h2 h3 h4,term_188_identity q e h0 h1 h2 h3 h4,term_189_identity q e h0 h1 h2 h3 h4,term_190_identity q e h0 h1 h2 h3 h4,term_191_identity q e h0 h1 h2 h3 h4,term_192_identity q e h0 h1 h2 h3 h4,term_193_identity q e h0 h1 h2 h3 h4,term_194_identity q e h0 h1 h2 h3 h4,term_195_identity q e h0 h1 h2 h3 h4,term_196_identity q e h0 h1 h2 h3 h4,term_197_identity q e h0 h1 h2 h3 h4,term_198_identity q e h0 h1 h2 h3 h4,term_199_identity q e h0 h1 h2 h3 h4,term_200_identity q e h0 h1 h2 h3 h4,term_201_identity q e h0 h1 h2 h3 h4,term_202_identity q e h0 h1 h2 h3 h4,term_203_identity q e h0 h1 h2 h3 h4,term_204_identity q e h0 h1 h2 h3 h4,term_205_identity q e h0 h1 h2 h3 h4,term_206_identity q e h0 h1 h2 h3 h4,term_207_identity q e h0 h1 h2 h3 h4,term_208_identity q e h0 h1 h2 h3 h4,term_209_identity q e h0 h1 h2 h3 h4,term_210_identity q e h0 h1 h2 h3 h4,term_211_identity q e h0 h1 h2 h3 h4,term_212_identity q e h0 h1 h2 h3 h4,term_213_identity q e h0 h1 h2 h3 h4,term_214_identity q e h0 h1 h2 h3 h4,term_215_identity q e h0 h1 h2 h3 h4,term_216_identity q e h0 h1 h2 h3 h4,term_217_identity q e h0 h1 h2 h3 h4,term_218_identity q e h0 h1 h2 h3 h4,term_219_identity q e h0 h1 h2 h3 h4,term_220_identity q e h0 h1 h2 h3 h4,term_221_identity q e h0 h1 h2 h3 h4,term_222_identity q e h0 h1 h2 h3 h4,term_223_identity q e h0 h1 h2 h3 h4,term_224_identity q e h0 h1 h2 h3 h4,term_225_identity q e h0 h1 h2 h3 h4,term_226_identity q e h0 h1 h2 h3 h4,term_227_identity q e h0 h1 h2 h3 h4,term_228_identity q e h0 h1 h2 h3 h4,term_229_identity q e h0 h1 h2 h3 h4,term_230_identity q e h0 h1 h2 h3 h4,term_231_identity q e h0 h1 h2 h3 h4,term_232_identity q e h0 h1 h2 h3 h4,term_233_identity q e h0 h1 h2 h3 h4,term_234_identity q e h0 h1 h2 h3 h4,term_235_identity q e h0 h1 h2 h3 h4,term_236_identity q e h0 h1 h2 h3 h4,term_237_identity q e h0 h1 h2 h3 h4,term_238_identity q e h0 h1 h2 h3 h4,term_239_identity q e h0 h1 h2 h3 h4,term_240_identity q e h0 h1 h2 h3 h4,term_241_identity q e h0 h1 h2 h3 h4,term_242_identity q e h0 h1 h2 h3 h4,term_243_identity q e h0 h1 h2 h3 h4,term_244_identity q e h0 h1 h2 h3 h4,term_245_identity q e h0 h1 h2 h3 h4,term_246_identity q e h0 h1 h2 h3 h4,term_247_identity q e h0 h1 h2 h3 h4,term_248_identity q e h0 h1 h2 h3 h4,term_249_identity q e h0 h1 h2 h3 h4,term_250_identity q e h0 h1 h2 h3 h4,term_251_identity q e h0 h1 h2 h3 h4,term_252_identity q e h0 h1 h2 h3 h4,term_253_identity q e h0 h1 h2 h3 h4,term_254_identity q e h0 h1 h2 h3 h4,term_255_identity q e h0 h1 h2 h3 h4,term_256_identity q e h0 h1 h2 h3 h4,term_257_identity q e h0 h1 h2 h3 h4,term_258_identity q e h0 h1 h2 h3 h4,term_259_identity q e h0 h1 h2 h3 h4,term_260_identity q e h0 h1 h2 h3 h4,term_261_identity q e h0 h1 h2 h3 h4,term_262_identity q e h0 h1 h2 h3 h4,term_263_identity q e h0 h1 h2 h3 h4,term_264_identity q e h0 h1 h2 h3 h4,term_265_identity q e h0 h1 h2 h3 h4,term_266_identity q e h0 h1 h2 h3 h4,term_267_identity q e h0 h1 h2 h3 h4,term_268_identity q e h0 h1 h2 h3 h4,term_269_identity q e h0 h1 h2 h3 h4,term_270_identity q e h0 h1 h2 h3 h4,term_271_identity q e h0 h1 h2 h3 h4,term_272_identity q e h0 h1 h2 h3 h4,term_273_identity q e h0 h1 h2 h3 h4,term_274_identity q e h0 h1 h2 h3 h4,term_275_identity q e h0 h1 h2 h3 h4]
  have heq : e=((2)*q) := by omega
  try simp only [heq]
  have hqeq : q=4 := by omega
  try simp only [hqeq]
  grind
#print axioms cell_identity
end Identity_left2_2
end LuRazLattice
