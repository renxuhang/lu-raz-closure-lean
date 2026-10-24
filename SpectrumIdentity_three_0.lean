import LatticeCounting
namespace LuRazLattice
namespace Identity_three_0
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
def term_0 (q e : Int) : Int := (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int))
theorem term_0_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤(e+(-3))) (h2 : 0≤((-e)+3)) : term_0 q e=(2) := by
  have v0 : ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) := by omega
  have v1 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_0,tri2,pos,v0,v1]
  grind
def term_1 (q e : Int) : Int := (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int))
theorem term_1_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤(e+(-3))) (h2 : 0≤((-e)+3)) : term_1 q e=(2) := by
  have v0 : ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) := by omega
  have v1 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_1,tri2,pos,v0,v1]
  grind
def term_2 (q e : Int) : Int := (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int))
theorem term_2_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤(e+(-3))) (h2 : 0≤((-e)+3)) : term_2 q e=(2) := by
  have v0 : ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) := by omega
  have v1 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_2,tri2,pos,v0,v1]
  grind
def term_3 (q e : Int) : Int := (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int))
theorem term_3_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤(e+(-3))) (h2 : 0≤((-e)+3)) : term_3 q e=(2) := by
  have v0 : ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) := by omega
  have v1 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_3,tri2,pos,v0,v1]
  grind
def term_4 (q e : Int) : Int := (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int))
theorem term_4_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤(e+(-3))) (h2 : 0≤((-e)+3)) : term_4 q e=(2) := by
  have v0 : ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) := by omega
  have v1 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_4,tri2,pos,v0,v1]
  grind
def term_5 (q e : Int) : Int := (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int))
theorem term_5_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤(e+(-3))) (h2 : 0≤((-e)+3)) : term_5 q e=(2) := by
  have v0 : ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) := by omega
  have v1 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_5,tri2,pos,v0,v1]
  grind
def term_6 (q e : Int) : Int := (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int))
theorem term_6_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤(e+(-3))) (h2 : 0≤((-e)+3)) : term_6 q e=(2) := by
  have v0 : ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) := by omega
  have v1 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_6,tri2,pos,v0,v1]
  grind
def term_7 (q e : Int) : Int := (if ((4)≤(q+1) ∧ (4)≤(q+1)) then ((((tri2 ((((q+1)-(0:Int))+(1))-(4)))-(tri2 (((q+1)-(0:Int))-(q+1))))-(tri2 (((4)-(0:Int))-(4))))+(tri2 ((((4)-(0:Int))-(q+1))-(1)))) else (0:Int))
theorem term_7_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤(e+(-3))) (h2 : 0≤((-e)+3)) : term_7 q e=(1*q*q+(-3)*q+2) := by
  have v0 : ((4)≤(q+1) ∧ (4)≤(q+1)) := by omega
  have v1 : max (0:Int) ((((q+1)-(0:Int))+(1))-(4))=(q+(-2)) := by omega
  have v2 : max (0:Int) (((q+1)-(0:Int))-(q+1))=(0:Int) := by omega
  have v3 : max (0:Int) (((4)-(0:Int))-(4))=(0:Int) := by omega
  have v4 : max (0:Int) ((((4)-(0:Int))-(q+1))-(1))=(0:Int) := by omega
  simp only [term_7,tri2,pos,v0,v1,v2,v3,v4]
  grind
def term_8 (q e : Int) : Int := (if ((q+3)≤((2)*q+1) ∧ (4)≤(q+1)) then ((((tri2 ((((q+1)-(0:Int))+(1))-(q+3)))-(tri2 (((q+1)-(0:Int))-((2)*q+1))))-(tri2 (((4)-(0:Int))-(q+3))))+(tri2 ((((4)-(0:Int))-((2)*q+1))-(1)))) else (0:Int))
theorem term_8_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤(e+(-3))) (h2 : 0≤((-e)+3)) : term_8 q e=(0:Int) := by
  have v0 : ((q+3)≤((2)*q+1) ∧ (4)≤(q+1)) := by omega
  have v1 : max (0:Int) ((((q+1)-(0:Int))+(1))-(q+3))=(0:Int) := by omega
  have v2 : max (0:Int) (((q+1)-(0:Int))-((2)*q+1))=(0:Int) := by omega
  have v3 : max (0:Int) (((4)-(0:Int))-(q+3))=(0:Int) := by omega
  have v4 : max (0:Int) ((((4)-(0:Int))-((2)*q+1))-(1))=(0:Int) := by omega
  simp only [term_8,tri2,pos,v0,v1,v2,v3,v4]
  grind
def term_9 (q e : Int) : Int := (if ((4)≤(q+1) ∧ (q+3)≤((2)*q+1)) then ((((tri2 (((((2)*q+1)-(0:Int))+(1))-(4)))-(tri2 ((((2)*q+1)-(0:Int))-(q+1))))-(tri2 (((q+3)-(0:Int))-(4))))+(tri2 ((((q+3)-(0:Int))-(q+1))-(1)))) else (0:Int))
theorem term_9_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤(e+(-3))) (h2 : 0≤((-e)+3)) : term_9 q e=(2*q*q+(-6)*q+4) := by
  have v0 : ((4)≤(q+1) ∧ (q+3)≤((2)*q+1)) := by omega
  have v1 : max (0:Int) (((((2)*q+1)-(0:Int))+(1))-(4))=((2)*q+(-2)) := by omega
  have v2 : max (0:Int) ((((2)*q+1)-(0:Int))-(q+1))=(q) := by omega
  have v3 : max (0:Int) (((q+3)-(0:Int))-(4))=(q+(-1)) := by omega
  have v4 : max (0:Int) ((((q+3)-(0:Int))-(q+1))-(1))=(1) := by omega
  simp only [term_9,tri2,pos,v0,v1,v2,v3,v4]
  grind
def term_10 (q e : Int) : Int := (if ((q+3)≤((2)*q+1) ∧ (q+3)≤((2)*q+1)) then ((((tri2 (((((2)*q+1)-(0:Int))+(1))-(q+3)))-(tri2 ((((2)*q+1)-(0:Int))-((2)*q+1))))-(tri2 (((q+3)-(0:Int))-(q+3))))+(tri2 ((((q+3)-(0:Int))-((2)*q+1))-(1)))) else (0:Int))
theorem term_10_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤(e+(-3))) (h2 : 0≤((-e)+3)) : term_10 q e=(1*q*q+(-1)*q) := by
  have v0 : ((q+3)≤((2)*q+1) ∧ (q+3)≤((2)*q+1)) := by omega
  have v1 : max (0:Int) (((((2)*q+1)-(0:Int))+(1))-(q+3))=(q+(-1)) := by omega
  have v2 : max (0:Int) ((((2)*q+1)-(0:Int))-((2)*q+1))=(0:Int) := by omega
  have v3 : max (0:Int) (((q+3)-(0:Int))-(q+3))=(0:Int) := by omega
  have v4 : max (0:Int) ((((q+3)-(0:Int))-((2)*q+1))-(1))=(0:Int) := by omega
  simp only [term_10,tri2,pos,v0,v1,v2,v3,v4]
  grind
def term_11 (q e : Int) : Int := (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int))
theorem term_11_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤(e+(-3))) (h2 : 0≤((-e)+3)) : term_11 q e=(2) := by
  have v0 : ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) := by omega
  have v1 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_11,tri2,pos,v0,v1]
  grind
def term_12 (q e : Int) : Int := (if ((4)≤(q+1) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((q+1)-(4))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int))
theorem term_12_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤(e+(-3))) (h2 : 0≤((-e)+3)) : term_12 q e=(2*q+(-4)) := by
  have v0 : ((4)≤(q+1) ∧ (0:Int)≤(0:Int)) := by omega
  have v1 : max (0:Int) (((q+1)-(4))+(1))=(q+(-2)) := by omega
  have v2 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_12,tri2,pos,v0,v1,v2]
  grind
def term_13 (q e : Int) : Int := (if ((q+3)≤((2)*q+(-1)) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) ((((2)*q+(-1))-(q+3))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int))
theorem term_13_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤(e+(-3))) (h2 : 0≤((-e)+3)) : term_13 q e=(2*q+(-6)) := by
  have v0 : ((q+3)≤((2)*q+(-1)) ∧ (0:Int)≤(0:Int)) := by omega
  have v1 : max (0:Int) ((((2)*q+(-1))-(q+3))+(1))=(q+(-3)) := by omega
  have v2 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_13,tri2,pos,v0,v1,v2]
  grind
def term_14 (q e : Int) : Int := (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int))
theorem term_14_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤(e+(-3))) (h2 : 0≤((-e)+3)) : term_14 q e=(2) := by
  have v0 : ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) := by omega
  have v1 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_14,tri2,pos,v0,v1]
  grind
def term_15 (q e : Int) : Int := (if ((4)≤(q+1) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((q+1)-(4))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int))
theorem term_15_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤(e+(-3))) (h2 : 0≤((-e)+3)) : term_15 q e=(2*q+(-4)) := by
  have v0 : ((4)≤(q+1) ∧ (0:Int)≤(0:Int)) := by omega
  have v1 : max (0:Int) (((q+1)-(4))+(1))=(q+(-2)) := by omega
  have v2 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_15,tri2,pos,v0,v1,v2]
  grind
def term_16 (q e : Int) : Int := (if ((q+4)≤((2)*q+1) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) ((((2)*q+1)-(q+4))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int))
theorem term_16_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤(e+(-3))) (h2 : 0≤((-e)+3)) : term_16 q e=(2*q+(-4)) := by
  have v0 : ((q+4)≤((2)*q+1) ∧ (0:Int)≤(0:Int)) := by omega
  have v1 : max (0:Int) ((((2)*q+1)-(q+4))+(1))=(q+(-2)) := by omega
  have v2 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_16,tri2,pos,v0,v1,v2]
  grind
def term_17 (q e : Int) : Int := (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int))
theorem term_17_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤(e+(-3))) (h2 : 0≤((-e)+3)) : term_17 q e=(2) := by
  have v0 : ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) := by omega
  have v1 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_17,tri2,pos,v0,v1]
  grind
def term_18 (q e : Int) : Int := (if ((4)≤(q+1) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((q+1)-(4))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int))
theorem term_18_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤(e+(-3))) (h2 : 0≤((-e)+3)) : term_18 q e=(2*q+(-4)) := by
  have v0 : ((4)≤(q+1) ∧ (0:Int)≤(0:Int)) := by omega
  have v1 : max (0:Int) (((q+1)-(4))+(1))=(q+(-2)) := by omega
  have v2 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_18,tri2,pos,v0,v1,v2]
  grind
def term_19 (q e : Int) : Int := (if ((4)≤(q+1) ∧ (q+3)≤((2)*q+1)) then ((((tri2 (((((2)*q+1)-(0:Int))+(1))-(4)))-(tri2 ((((2)*q+1)-(0:Int))-(q+1))))-(tri2 (((q+3)-(0:Int))-(4))))+(tri2 ((((q+3)-(0:Int))-(q+1))-(1)))) else (0:Int))
theorem term_19_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤(e+(-3))) (h2 : 0≤((-e)+3)) : term_19 q e=(2*q*q+(-6)*q+4) := by
  have v0 : ((4)≤(q+1) ∧ (q+3)≤((2)*q+1)) := by omega
  have v1 : max (0:Int) (((((2)*q+1)-(0:Int))+(1))-(4))=((2)*q+(-2)) := by omega
  have v2 : max (0:Int) ((((2)*q+1)-(0:Int))-(q+1))=(q) := by omega
  have v3 : max (0:Int) (((q+3)-(0:Int))-(4))=(q+(-1)) := by omega
  have v4 : max (0:Int) ((((q+3)-(0:Int))-(q+1))-(1))=(1) := by omega
  simp only [term_19,tri2,pos,v0,v1,v2,v3,v4]
  grind
def term_20 (q e : Int) : Int := (if ((q+3)≤((2)*q+1) ∧ (q+3)≤((2)*q+1)) then ((((tri2 (((((2)*q+1)-(0:Int))+(1))-(q+3)))-(tri2 ((((2)*q+1)-(0:Int))-((2)*q+1))))-(tri2 (((q+3)-(0:Int))-(q+3))))+(tri2 ((((q+3)-(0:Int))-((2)*q+1))-(1)))) else (0:Int))
theorem term_20_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤(e+(-3))) (h2 : 0≤((-e)+3)) : term_20 q e=(1*q*q+(-1)*q) := by
  have v0 : ((q+3)≤((2)*q+1) ∧ (q+3)≤((2)*q+1)) := by omega
  have v1 : max (0:Int) (((((2)*q+1)-(0:Int))+(1))-(q+3))=(q+(-1)) := by omega
  have v2 : max (0:Int) ((((2)*q+1)-(0:Int))-((2)*q+1))=(0:Int) := by omega
  have v3 : max (0:Int) (((q+3)-(0:Int))-(q+3))=(0:Int) := by omega
  have v4 : max (0:Int) ((((q+3)-(0:Int))-((2)*q+1))-(1))=(0:Int) := by omega
  simp only [term_20,tri2,pos,v0,v1,v2,v3,v4]
  grind
def term_21 (q e : Int) : Int := (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int))
theorem term_21_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤(e+(-3))) (h2 : 0≤((-e)+3)) : term_21 q e=(2) := by
  have v0 : ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) := by omega
  have v1 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_21,tri2,pos,v0,v1]
  grind
def term_22 (q e : Int) : Int := (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int))
theorem term_22_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤(e+(-3))) (h2 : 0≤((-e)+3)) : term_22 q e=(2) := by
  have v0 : ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) := by omega
  have v1 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_22,tri2,pos,v0,v1]
  grind
def term_23 (q e : Int) : Int := (if ((q+3)≤((2)*q+(-1)) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) ((((2)*q+(-1))-(q+3))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int))
theorem term_23_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤(e+(-3))) (h2 : 0≤((-e)+3)) : term_23 q e=(2*q+(-6)) := by
  have v0 : ((q+3)≤((2)*q+(-1)) ∧ (0:Int)≤(0:Int)) := by omega
  have v1 : max (0:Int) ((((2)*q+(-1))-(q+3))+(1))=(q+(-3)) := by omega
  have v2 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_23,tri2,pos,v0,v1,v2]
  grind
def term_24 (q e : Int) : Int := (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int))
theorem term_24_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤(e+(-3))) (h2 : 0≤((-e)+3)) : term_24 q e=(2) := by
  have v0 : ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) := by omega
  have v1 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_24,tri2,pos,v0,v1]
  grind
def term_25 (q e : Int) : Int := (if ((4)≤(q+1) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((q+1)-(4))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int))
theorem term_25_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤(e+(-3))) (h2 : 0≤((-e)+3)) : term_25 q e=(2*q+(-4)) := by
  have v0 : ((4)≤(q+1) ∧ (0:Int)≤(0:Int)) := by omega
  have v1 : max (0:Int) (((q+1)-(4))+(1))=(q+(-2)) := by omega
  have v2 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_25,tri2,pos,v0,v1,v2]
  grind
def term_26 (q e : Int) : Int := (if ((q+4)≤((2)*q+1) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) ((((2)*q+1)-(q+4))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int))
theorem term_26_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤(e+(-3))) (h2 : 0≤((-e)+3)) : term_26 q e=(2*q+(-4)) := by
  have v0 : ((q+4)≤((2)*q+1) ∧ (0:Int)≤(0:Int)) := by omega
  have v1 : max (0:Int) ((((2)*q+1)-(q+4))+(1))=(q+(-2)) := by omega
  have v2 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_26,tri2,pos,v0,v1,v2]
  grind
def term_27 (q e : Int) : Int := (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int))
theorem term_27_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤(e+(-3))) (h2 : 0≤((-e)+3)) : term_27 q e=(2) := by
  have v0 : ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) := by omega
  have v1 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_27,tri2,pos,v0,v1]
  grind
def term_28 (q e : Int) : Int := (if ((4)≤(q+1) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((q+1)-(4))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int))
theorem term_28_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤(e+(-3))) (h2 : 0≤((-e)+3)) : term_28 q e=(2*q+(-4)) := by
  have v0 : ((4)≤(q+1) ∧ (0:Int)≤(0:Int)) := by omega
  have v1 : max (0:Int) (((q+1)-(4))+(1))=(q+(-2)) := by omega
  have v2 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_28,tri2,pos,v0,v1,v2]
  grind
def term_29 (q e : Int) : Int := (if ((q+3)≤((2)*q+1) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) ((((2)*q+1)-(q+3))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int))
theorem term_29_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤(e+(-3))) (h2 : 0≤((-e)+3)) : term_29 q e=(2*q+(-2)) := by
  have v0 : ((q+3)≤((2)*q+1) ∧ (0:Int)≤(0:Int)) := by omega
  have v1 : max (0:Int) ((((2)*q+1)-(q+3))+(1))=(q+(-1)) := by omega
  have v2 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_29,tri2,pos,v0,v1,v2]
  grind
def term_30 (q e : Int) : Int := (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int))
theorem term_30_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤(e+(-3))) (h2 : 0≤((-e)+3)) : term_30 q e=(2) := by
  have v0 : ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) := by omega
  have v1 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_30,tri2,pos,v0,v1]
  grind
def term_31 (q e : Int) : Int := (if ((4)≤(q+1) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((q+1)-(4))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int))
theorem term_31_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤(e+(-3))) (h2 : 0≤((-e)+3)) : term_31 q e=(2*q+(-4)) := by
  have v0 : ((4)≤(q+1) ∧ (0:Int)≤(0:Int)) := by omega
  have v1 : max (0:Int) (((q+1)-(4))+(1))=(q+(-2)) := by omega
  have v2 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_31,tri2,pos,v0,v1,v2]
  grind
def term_32 (q e : Int) : Int := (if ((5)≤((2)*q+1) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) ((((2)*q+1)-(5))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int))
theorem term_32_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤(e+(-3))) (h2 : 0≤((-e)+3)) : term_32 q e=(4*q+(-6)) := by
  have v0 : ((5)≤((2)*q+1) ∧ (0:Int)≤(0:Int)) := by omega
  have v1 : max (0:Int) ((((2)*q+1)-(5))+(1))=((2)*q+(-3)) := by omega
  have v2 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_32,tri2,pos,v0,v1,v2]
  grind
def term_33 (q e : Int) : Int := (if ((q+4)≤((2)*q+1) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) ((((2)*q+1)-(q+4))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int))
theorem term_33_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤(e+(-3))) (h2 : 0≤((-e)+3)) : term_33 q e=(2*q+(-4)) := by
  have v0 : ((q+4)≤((2)*q+1) ∧ (0:Int)≤(0:Int)) := by omega
  have v1 : max (0:Int) ((((2)*q+1)-(q+4))+(1))=(q+(-2)) := by omega
  have v2 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_33,tri2,pos,v0,v1,v2]
  grind
def term_34 (q e : Int) : Int := (if (((2)*q+2)≤((3)*q+(-1)) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) ((((3)*q+(-1))-((2)*q+2))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int))
theorem term_34_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤(e+(-3))) (h2 : 0≤((-e)+3)) : term_34 q e=(2*q+(-4)) := by
  have v0 : (((2)*q+2)≤((3)*q+(-1)) ∧ (0:Int)≤(0:Int)) := by omega
  have v1 : max (0:Int) ((((3)*q+(-1))-((2)*q+2))+(1))=(q+(-2)) := by omega
  have v2 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_34,tri2,pos,v0,v1,v2]
  grind
def term_35 (q e : Int) : Int := (if (((3)*q+1)≤((4)*q+(-3)) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) ((((4)*q+(-3))-((3)*q+1))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int))
theorem term_35_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤(e+(-3))) (h2 : 0≤((-e)+3)) : term_35 q e=(2*q+(-6)) := by
  have v0 : (((3)*q+1)≤((4)*q+(-3)) ∧ (0:Int)≤(0:Int)) := by omega
  have v1 : max (0:Int) ((((4)*q+(-3))-((3)*q+1))+(1))=(q+(-3)) := by omega
  have v2 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_35,tri2,pos,v0,v1,v2]
  grind
def term_36 (q e : Int) : Int := (if (((2)*q+2)≤((4)*q+(-3)) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) ((((4)*q+(-3))-((2)*q+2))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int))
theorem term_36_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤(e+(-3))) (h2 : 0≤((-e)+3)) : term_36 q e=(4*q+(-8)) := by
  have v0 : (((2)*q+2)≤((4)*q+(-3)) ∧ (0:Int)≤(0:Int)) := by omega
  have v1 : max (0:Int) ((((4)*q+(-3))-((2)*q+2))+(1))=((2)*q+(-4)) := by omega
  have v2 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_36,tri2,pos,v0,v1,v2]
  grind
def term_37 (q e : Int) : Int := (if (((2)*q+2)≤((3)*q+(-1)) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) ((((3)*q+(-1))-((2)*q+2))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int))
theorem term_37_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤(e+(-3))) (h2 : 0≤((-e)+3)) : term_37 q e=(2*q+(-4)) := by
  have v0 : (((2)*q+2)≤((3)*q+(-1)) ∧ (0:Int)≤(0:Int)) := by omega
  have v1 : max (0:Int) ((((3)*q+(-1))-((2)*q+2))+(1))=(q+(-2)) := by omega
  have v2 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_37,tri2,pos,v0,v1,v2]
  grind
def term_38 (q e : Int) : Int := (if (((2)*q+2)≤((3)*q) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) ((((3)*q)-((2)*q+2))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int))
theorem term_38_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤(e+(-3))) (h2 : 0≤((-e)+3)) : term_38 q e=(2*q+(-2)) := by
  have v0 : (((2)*q+2)≤((3)*q) ∧ (0:Int)≤(0:Int)) := by omega
  have v1 : max (0:Int) ((((3)*q)-((2)*q+2))+(1))=(q+(-1)) := by omega
  have v2 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_38,tri2,pos,v0,v1,v2]
  grind
def term_39 (q e : Int) : Int := (if (((2)*q+2)≤((3)*q+(-1)) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) ((((3)*q+(-1))-((2)*q+2))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int))
theorem term_39_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤(e+(-3))) (h2 : 0≤((-e)+3)) : term_39 q e=(2*q+(-4)) := by
  have v0 : (((2)*q+2)≤((3)*q+(-1)) ∧ (0:Int)≤(0:Int)) := by omega
  have v1 : max (0:Int) ((((3)*q+(-1))-((2)*q+2))+(1))=(q+(-2)) := by omega
  have v2 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_39,tri2,pos,v0,v1,v2]
  grind
def term_40 (q e : Int) : Int := (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int))
theorem term_40_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤(e+(-3))) (h2 : 0≤((-e)+3)) : term_40 q e=(2) := by
  have v0 : ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) := by omega
  have v1 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_40,tri2,pos,v0,v1]
  grind
def term_41 (q e : Int) : Int := (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int))
theorem term_41_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤(e+(-3))) (h2 : 0≤((-e)+3)) : term_41 q e=(2) := by
  have v0 : ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) := by omega
  have v1 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_41,tri2,pos,v0,v1]
  grind
def term_42 (q e : Int) : Int := (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int))
theorem term_42_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤(e+(-3))) (h2 : 0≤((-e)+3)) : term_42 q e=(2) := by
  have v0 : ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) := by omega
  have v1 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_42,tri2,pos,v0,v1]
  grind
def term_43 (q e : Int) : Int := (if ((4)≤(q+1) ∧ ((2)*q+2)≤((2)*q+3)) then (((2)*(max (0:Int) (((q+1)-(4))+(1))))*(max (0:Int) ((((2)*q+3)-((2)*q+2))+(1)))) else (0:Int))
theorem term_43_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤(e+(-3))) (h2 : 0≤((-e)+3)) : term_43 q e=(4*q+(-8)) := by
  have v0 : ((4)≤(q+1) ∧ ((2)*q+2)≤((2)*q+3)) := by omega
  have v1 : max (0:Int) (((q+1)-(4))+(1))=(q+(-2)) := by omega
  have v2 : max (0:Int) ((((2)*q+3)-((2)*q+2))+(1))=(2) := by omega
  simp only [term_43,tri2,pos,v0,v1,v2]
  grind
def term_44 (q e : Int) : Int := (if ((q+3)≤((2)*q+1) ∧ ((2)*q+2)≤((2)*q+3)) then (((2)*(max (0:Int) ((((2)*q+1)-(q+3))+(1))))*(max (0:Int) ((((2)*q+3)-((2)*q+2))+(1)))) else (0:Int))
theorem term_44_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤(e+(-3))) (h2 : 0≤((-e)+3)) : term_44 q e=(4*q+(-4)) := by
  have v0 : ((q+3)≤((2)*q+1) ∧ ((2)*q+2)≤((2)*q+3)) := by omega
  have v1 : max (0:Int) ((((2)*q+1)-(q+3))+(1))=(q+(-1)) := by omega
  have v2 : max (0:Int) ((((2)*q+3)-((2)*q+2))+(1))=(2) := by omega
  simp only [term_44,tri2,pos,v0,v1,v2]
  grind
def term_45 (q e : Int) : Int := (if ((4)≤(q+1) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((q+1)-(4))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int))
theorem term_45_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤(e+(-3))) (h2 : 0≤((-e)+3)) : term_45 q e=(2*q+(-4)) := by
  have v0 : ((4)≤(q+1) ∧ (0:Int)≤(0:Int)) := by omega
  have v1 : max (0:Int) (((q+1)-(4))+(1))=(q+(-2)) := by omega
  have v2 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_45,tri2,pos,v0,v1,v2]
  grind
def term_46 (q e : Int) : Int := (if ((q+3)≤((2)*q+(-1)) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) ((((2)*q+(-1))-(q+3))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int))
theorem term_46_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤(e+(-3))) (h2 : 0≤((-e)+3)) : term_46 q e=(2*q+(-6)) := by
  have v0 : ((q+3)≤((2)*q+(-1)) ∧ (0:Int)≤(0:Int)) := by omega
  have v1 : max (0:Int) ((((2)*q+(-1))-(q+3))+(1))=(q+(-3)) := by omega
  have v2 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_46,tri2,pos,v0,v1,v2]
  grind
def term_47 (q e : Int) : Int := (if (((2)*q+2)≤((2)*q+3) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) ((((2)*q+3)-((2)*q+2))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int))
theorem term_47_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤(e+(-3))) (h2 : 0≤((-e)+3)) : term_47 q e=(4) := by
  have v0 : (((2)*q+2)≤((2)*q+3) ∧ (0:Int)≤(0:Int)) := by omega
  have v1 : max (0:Int) ((((2)*q+3)-((2)*q+2))+(1))=(2) := by omega
  have v2 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_47,tri2,pos,v0,v1,v2]
  grind
def term_48 (q e : Int) : Int := (if (((4)*q+(-2))≤((4)*q+(-1)) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) ((((4)*q+(-1))-((4)*q+(-2)))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int))
theorem term_48_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤(e+(-3))) (h2 : 0≤((-e)+3)) : term_48 q e=(4) := by
  have v0 : (((4)*q+(-2))≤((4)*q+(-1)) ∧ (0:Int)≤(0:Int)) := by omega
  have v1 : max (0:Int) ((((4)*q+(-1))-((4)*q+(-2)))+(1))=(2) := by omega
  have v2 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_48,tri2,pos,v0,v1,v2]
  grind
def term_49 (q e : Int) : Int := (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int))
theorem term_49_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤(e+(-3))) (h2 : 0≤((-e)+3)) : term_49 q e=(2) := by
  have v0 : ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) := by omega
  have v1 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_49,tri2,pos,v0,v1]
  grind
def term_50 (q e : Int) : Int := (if (((4)*q+(-2))≤((4)*q+(-1)) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) ((((4)*q+(-1))-((4)*q+(-2)))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int))
theorem term_50_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤(e+(-3))) (h2 : 0≤((-e)+3)) : term_50 q e=(4) := by
  have v0 : (((4)*q+(-2))≤((4)*q+(-1)) ∧ (0:Int)≤(0:Int)) := by omega
  have v1 : max (0:Int) ((((4)*q+(-1))-((4)*q+(-2)))+(1))=(2) := by omega
  have v2 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_50,tri2,pos,v0,v1,v2]
  grind
def term_51 (q e : Int) : Int := (if (((2)*q+2)≤((3)*q) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) ((((3)*q)-((2)*q+2))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int))
theorem term_51_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤(e+(-3))) (h2 : 0≤((-e)+3)) : term_51 q e=(2*q+(-2)) := by
  have v0 : (((2)*q+2)≤((3)*q) ∧ (0:Int)≤(0:Int)) := by omega
  have v1 : max (0:Int) ((((3)*q)-((2)*q+2))+(1))=(q+(-1)) := by omega
  have v2 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_51,tri2,pos,v0,v1,v2]
  grind
def term_52 (q e : Int) : Int := (if ((q+5)≤((2)*q+1) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) ((((2)*q+1)-(q+5))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int))
theorem term_52_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤(e+(-3))) (h2 : 0≤((-e)+3)) : term_52 q e=(2*q+(-6)) := by
  have v0 : ((q+5)≤((2)*q+1) ∧ (0:Int)≤(0:Int)) := by omega
  have v1 : max (0:Int) ((((2)*q+1)-(q+5))+(1))=(q+(-3)) := by omega
  have v2 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_52,tri2,pos,v0,v1,v2]
  grind
def term_53 (q e : Int) : Int := (if (((2)*q+2)≤((2)*q+3) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) ((((2)*q+3)-((2)*q+2))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int))
theorem term_53_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤(e+(-3))) (h2 : 0≤((-e)+3)) : term_53 q e=(4) := by
  have v0 : (((2)*q+2)≤((2)*q+3) ∧ (0:Int)≤(0:Int)) := by omega
  have v1 : max (0:Int) ((((2)*q+3)-((2)*q+2))+(1))=(2) := by omega
  have v2 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_53,tri2,pos,v0,v1,v2]
  grind
def term_54 (q e : Int) : Int := (if (((2)*q+2)≤((3)*q+(-1)) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) ((((3)*q+(-1))-((2)*q+2))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int))
theorem term_54_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤(e+(-3))) (h2 : 0≤((-e)+3)) : term_54 q e=(2*q+(-4)) := by
  have v0 : (((2)*q+2)≤((3)*q+(-1)) ∧ (0:Int)≤(0:Int)) := by omega
  have v1 : max (0:Int) ((((3)*q+(-1))-((2)*q+2))+(1))=(q+(-2)) := by omega
  have v2 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_54,tri2,pos,v0,v1,v2]
  grind
def term_55 (q e : Int) : Int := (if ((4)≤((2)*q) ∧ ((2)*q+2)≤((2)*q+3)) then (((2)*(max (0:Int) ((((2)*q)-(4))+(1))))*(max (0:Int) ((((2)*q+3)-((2)*q+2))+(1)))) else (0:Int))
theorem term_55_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤(e+(-3))) (h2 : 0≤((-e)+3)) : term_55 q e=(8*q+(-12)) := by
  have v0 : ((4)≤((2)*q) ∧ ((2)*q+2)≤((2)*q+3)) := by omega
  have v1 : max (0:Int) ((((2)*q)-(4))+(1))=((2)*q+(-3)) := by omega
  have v2 : max (0:Int) ((((2)*q+3)-((2)*q+2))+(1))=(2) := by omega
  simp only [term_55,tri2,pos,v0,v1,v2]
  grind
def term_56 (q e : Int) : Int := (if (((2)*q+4)≤((4)*q+(-1)) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) ((((4)*q+(-1))-((2)*q+4))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int))
theorem term_56_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤(e+(-3))) (h2 : 0≤((-e)+3)) : term_56 q e=(4*q+(-8)) := by
  have v0 : (((2)*q+4)≤((4)*q+(-1)) ∧ (0:Int)≤(0:Int)) := by omega
  have v1 : max (0:Int) ((((4)*q+(-1))-((2)*q+4))+(1))=((2)*q+(-4)) := by omega
  have v2 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_56,tri2,pos,v0,v1,v2]
  grind
def term_57 (q e : Int) : Int := (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int))
theorem term_57_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤(e+(-3))) (h2 : 0≤((-e)+3)) : term_57 q e=(2) := by
  have v0 : ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) := by omega
  have v1 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_57,tri2,pos,v0,v1]
  grind
def term_58 (q e : Int) : Int := (if (((2)*q+3)≤((4)*q) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) ((((4)*q)-((2)*q+3))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int))
theorem term_58_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤(e+(-3))) (h2 : 0≤((-e)+3)) : term_58 q e=(4*q+(-4)) := by
  have v0 : (((2)*q+3)≤((4)*q) ∧ (0:Int)≤(0:Int)) := by omega
  have v1 : max (0:Int) ((((4)*q)-((2)*q+3))+(1))=((2)*q+(-2)) := by omega
  have v2 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_58,tri2,pos,v0,v1,v2]
  grind
def term_59 (q e : Int) : Int := (if ((6)≤((2)*q+1) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) ((((2)*q+1)-(6))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int))
theorem term_59_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤(e+(-3))) (h2 : 0≤((-e)+3)) : term_59 q e=(4*q+(-8)) := by
  have v0 : ((6)≤((2)*q+1) ∧ (0:Int)≤(0:Int)) := by omega
  have v1 : max (0:Int) ((((2)*q+1)-(6))+(1))=((2)*q+(-4)) := by omega
  have v2 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_59,tri2,pos,v0,v1,v2]
  grind
def term_60 (q e : Int) : Int := (if ((5)≤((2)*q+(-1)) ∧ (0:Int)≤((2)*q+1)) then ((((tri2 (((((2)*q+1)-(2))+(1))-(5)))-(tri2 ((((2)*q+1)-(2))-((2)*q+(-1)))))-(tri2 (((0:Int)-(2))-(5))))+(tri2 ((((0:Int)-(2))-((2)*q+(-1)))-(1)))) else (0:Int))
theorem term_60_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤(e+(-3))) (h2 : 0≤((-e)+3)) : term_60 q e=(4*q*q+(-18)*q+20) := by
  have v0 : ((5)≤((2)*q+(-1)) ∧ (0:Int)≤((2)*q+1)) := by omega
  have v1 : max (0:Int) (((((2)*q+1)-(2))+(1))-(5))=((2)*q+(-5)) := by omega
  have v2 : max (0:Int) ((((2)*q+1)-(2))-((2)*q+(-1)))=(0:Int) := by omega
  have v3 : max (0:Int) (((0:Int)-(2))-(5))=(0:Int) := by omega
  have v4 : max (0:Int) ((((0:Int)-(2))-((2)*q+(-1)))-(1))=(0:Int) := by omega
  simp only [term_60,tri2,pos,v0,v1,v2,v3,v4]
  grind
def term_61 (q e : Int) : Int := (if ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) then (((2)*(max (0:Int) (((0:Int)-(0:Int))+(1))))*(max (0:Int) (((0:Int)-(0:Int))+(1)))) else (0:Int))
theorem term_61_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤(e+(-3))) (h2 : 0≤((-e)+3)) : term_61 q e=(2) := by
  have v0 : ((0:Int)≤(0:Int) ∧ (0:Int)≤(0:Int)) := by omega
  have v1 : max (0:Int) (((0:Int)-(0:Int))+(1))=(1) := by omega
  simp only [term_61,tri2,pos,v0,v1]
  grind
def term_62 (q e : Int) : Int := (if (((2)*q+2)≤((4)*q+(-2)) ∧ (0:Int)≤((4)*q)) then ((((tri2 (((((4)*q)-(2))+(1))-((2)*q+2)))-(tri2 ((((4)*q)-(2))-((4)*q+(-2)))))-(tri2 (((0:Int)-(2))-((2)*q+2))))+(tri2 ((((0:Int)-(2))-((4)*q+(-2)))-(1)))) else (0:Int))
theorem term_62_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤(e+(-3))) (h2 : 0≤((-e)+3)) : term_62 q e=(4*q*q+(-10)*q+6) := by
  have v0 : (((2)*q+2)≤((4)*q+(-2)) ∧ (0:Int)≤((4)*q)) := by omega
  have v1 : max (0:Int) (((((4)*q)-(2))+(1))-((2)*q+2))=((2)*q+(-3)) := by omega
  have v2 : max (0:Int) ((((4)*q)-(2))-((4)*q+(-2)))=(0:Int) := by omega
  have v3 : max (0:Int) (((0:Int)-(2))-((2)*q+2))=(0:Int) := by omega
  have v4 : max (0:Int) ((((0:Int)-(2))-((4)*q+(-2)))-(1))=(0:Int) := by omega
  simp only [term_62,tri2,pos,v0,v1,v2,v3,v4]
  grind
def term_63 (q e : Int) : Int := (if (((2)*q+2)≤((3)*q+(-1)) ∧ ((3)*q+3)≤((4)*q)) then (((2)*(max (0:Int) ((((3)*q+(-1))-((2)*q+2))+(1))))*(max (0:Int) ((((4)*q)-((3)*q+3))+(1)))) else (0:Int))
theorem term_63_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤(e+(-3))) (h2 : 0≤((-e)+3)) : term_63 q e=(2*q*q+(-8)*q+8) := by
  have v0 : (((2)*q+2)≤((3)*q+(-1)) ∧ ((3)*q+3)≤((4)*q)) := by omega
  have v1 : max (0:Int) ((((3)*q+(-1))-((2)*q+2))+(1))=(q+(-2)) := by omega
  have v2 : max (0:Int) ((((4)*q)-((3)*q+3))+(1))=(q+(-2)) := by omega
  simp only [term_63,tri2,pos,v0,v1,v2]
  grind
def sumTerms (q e : Int) : Int := term_0 q e + term_1 q e + term_2 q e + term_3 q e + term_4 q e + term_5 q e + term_6 q e + term_7 q e + term_8 q e + term_9 q e + term_10 q e + term_11 q e + term_12 q e + term_13 q e + term_14 q e + term_15 q e + term_16 q e + term_17 q e + term_18 q e + term_19 q e + term_20 q e + term_21 q e + term_22 q e + term_23 q e + term_24 q e + term_25 q e + term_26 q e + term_27 q e + term_28 q e + term_29 q e + term_30 q e + term_31 q e + term_32 q e + term_33 q e + term_34 q e + term_35 q e + term_36 q e + term_37 q e + term_38 q e + term_39 q e + term_40 q e + term_41 q e + term_42 q e + term_43 q e + term_44 q e + term_45 q e + term_46 q e + term_47 q e + term_48 q e + term_49 q e + term_50 q e + term_51 q e + term_52 q e + term_53 q e + term_54 q e + term_55 q e + term_56 q e + term_57 q e + term_58 q e + term_59 q e + term_60 q e + term_61 q e + term_62 q e + term_63 q e
theorem cell_identity (q e : Int) (h0 : 0≤(q+(-4))) (h1 : 0≤(e+(-3))) (h2 : 0≤((-e)+3)) : sumTerms q e=(17*q*q+27*q+(-48)) := by
  simp only [sumTerms,term_0_identity q e h0 h1 h2,term_1_identity q e h0 h1 h2,term_2_identity q e h0 h1 h2,term_3_identity q e h0 h1 h2,term_4_identity q e h0 h1 h2,term_5_identity q e h0 h1 h2,term_6_identity q e h0 h1 h2,term_7_identity q e h0 h1 h2,term_8_identity q e h0 h1 h2,term_9_identity q e h0 h1 h2,term_10_identity q e h0 h1 h2,term_11_identity q e h0 h1 h2,term_12_identity q e h0 h1 h2,term_13_identity q e h0 h1 h2,term_14_identity q e h0 h1 h2,term_15_identity q e h0 h1 h2,term_16_identity q e h0 h1 h2,term_17_identity q e h0 h1 h2,term_18_identity q e h0 h1 h2,term_19_identity q e h0 h1 h2,term_20_identity q e h0 h1 h2,term_21_identity q e h0 h1 h2,term_22_identity q e h0 h1 h2,term_23_identity q e h0 h1 h2,term_24_identity q e h0 h1 h2,term_25_identity q e h0 h1 h2,term_26_identity q e h0 h1 h2,term_27_identity q e h0 h1 h2,term_28_identity q e h0 h1 h2,term_29_identity q e h0 h1 h2,term_30_identity q e h0 h1 h2,term_31_identity q e h0 h1 h2,term_32_identity q e h0 h1 h2,term_33_identity q e h0 h1 h2,term_34_identity q e h0 h1 h2,term_35_identity q e h0 h1 h2,term_36_identity q e h0 h1 h2,term_37_identity q e h0 h1 h2,term_38_identity q e h0 h1 h2,term_39_identity q e h0 h1 h2,term_40_identity q e h0 h1 h2,term_41_identity q e h0 h1 h2,term_42_identity q e h0 h1 h2,term_43_identity q e h0 h1 h2,term_44_identity q e h0 h1 h2,term_45_identity q e h0 h1 h2,term_46_identity q e h0 h1 h2,term_47_identity q e h0 h1 h2,term_48_identity q e h0 h1 h2,term_49_identity q e h0 h1 h2,term_50_identity q e h0 h1 h2,term_51_identity q e h0 h1 h2,term_52_identity q e h0 h1 h2,term_53_identity q e h0 h1 h2,term_54_identity q e h0 h1 h2,term_55_identity q e h0 h1 h2,term_56_identity q e h0 h1 h2,term_57_identity q e h0 h1 h2,term_58_identity q e h0 h1 h2,term_59_identity q e h0 h1 h2,term_60_identity q e h0 h1 h2,term_61_identity q e h0 h1 h2,term_62_identity q e h0 h1 h2,term_63_identity q e h0 h1 h2]
  have heq : e=(3) := by omega
  try simp only [heq]
  grind
#print axioms cell_identity
end Identity_three_0
end LuRazLattice
