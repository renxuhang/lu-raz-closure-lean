import LatticeTally
import SpectrumIdentity_left1_0
namespace LuRazLattice.AtomCounts
set_option maxRecDepth 32768
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
noncomputable section
def event12 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤((2)*q+2))
theorem atom12_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event12 q e)=
      Identity_left1_0.term_12 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event12 q e)=
      if ((5)≤(e) ∧ (e)≤((2)*q+2)) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event12 q e) (((5)≤(e) ∧ (e)≤((2)*q+2)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp only [event12]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_12,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event13 (q e : Int) (p : Int×Int) : Prop := (((3)*q+1)≤e ∧ e≤((3)*q+1))
theorem atom13_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event13 q e)=
      Identity_left1_0.term_13 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event13 q e)=
      if (((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event13 q e) ((((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp only [event13]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_13,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event14 (q e : Int) (p : Int×Int) : Prop := (((3)*q+2)≤e ∧ e≤((4)*q))
theorem atom14_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event14 q e)=
      Identity_left1_0.term_14 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event14 q e)=
      if (((3)*q+2)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event14 q e) ((((3)*q+2)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp only [event14]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_14,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event15 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤((2)*q+2)) ∧ (((3)*q+1)≤e ∧ e≤((3)*q+1))
theorem atom15_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event15 q e)=
      Identity_left1_0.term_15 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event15 q e)=
      if ((5)≤(e) ∧ (e)≤((2)*q+2) ∧ ((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event15 q e) (((5)≤(e) ∧ (e)≤((2)*q+2) ∧ ((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp only [event15]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_15,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event16 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤((2)*q+2)) ∧ (((3)*q+2)≤e ∧ e≤((4)*q))
theorem atom16_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event16 q e)=
      Identity_left1_0.term_16 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event16 q e)=
      if ((5)≤(e) ∧ (e)≤((2)*q+2) ∧ ((3)*q+2)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event16 q e) (((5)≤(e) ∧ (e)≤((2)*q+2) ∧ ((3)*q+2)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp only [event16]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_16,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event17 (q e : Int) (p : Int×Int) : Prop := (((3)*q+1)≤e ∧ e≤((3)*q+1)) ∧ (((3)*q+2)≤e ∧ e≤((4)*q))
theorem atom17_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event17 q e)=
      Identity_left1_0.term_17 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event17 q e)=
      if (((3)*q+1)≤(e) ∧ (e)≤((3)*q+1) ∧ ((3)*q+2)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event17 q e) ((((3)*q+1)≤(e) ∧ (e)≤((3)*q+1) ∧ ((3)*q+2)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp only [event17]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_17,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event18 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤((2)*q+2)) ∧ (((3)*q+1)≤e ∧ e≤((3)*q+1)) ∧ (((3)*q+2)≤e ∧ e≤((4)*q))
theorem atom18_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event18 q e)=
      Identity_left1_0.term_18 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event18 q e)=
      if ((5)≤(e) ∧ (e)≤((2)*q+2) ∧ ((3)*q+1)≤(e) ∧ (e)≤((3)*q+1) ∧ ((3)*q+2)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event18 q e) (((5)≤(e) ∧ (e)≤((2)*q+2) ∧ ((3)*q+1)≤(e) ∧ (e)≤((3)*q+1) ∧ ((3)*q+2)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp only [event18]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_18,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event19 (q e : Int) (p : Int×Int) : Prop := (((2)*q+3)≤e ∧ e≤((4)*q))
theorem atom19_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event19 q e)=
      Identity_left1_0.term_19 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event19 q e)=
      if (((2)*q+3)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event19 q e) ((((2)*q+3)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp only [event19]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_19,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event20 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(q+2))
theorem atom20_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event20 q e)=
      Identity_left1_0.term_20 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event20 q e)=
      if ((5)≤(e) ∧ (e)≤(q+2)) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event20 q e) (((5)≤(e) ∧ (e)≤(q+2)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp only [event20]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_20,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event21 (q e : Int) (p : Int×Int) : Prop := (((2)*q+3)≤e ∧ e≤((4)*q))
theorem atom21_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event21 q e)=
      Identity_left1_0.term_21 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event21 q e)=
      if (((2)*q+3)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event21 q e) ((((2)*q+3)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp only [event21]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_21,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event22 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(q+2)) ∧ (((2)*q+3)≤e ∧ e≤((4)*q))
theorem atom22_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event22 q e)=
      Identity_left1_0.term_22 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event22 q e)=
      if ((5)≤(e) ∧ (e)≤(q+2) ∧ ((2)*q+3)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event22 q e) (((5)≤(e) ∧ (e)≤(q+2) ∧ ((2)*q+3)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp only [event22]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_22,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event23 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤((4)*q))
theorem atom23_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event23 q e)=
      Identity_left1_0.term_23 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event23 q e)=
      if ((5)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event23 q e) (((5)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp only [event23]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_23,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event24 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤((2)*q+2))
theorem atom24_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event24 q e)=
      Identity_left1_0.term_24 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event24 q e)=
      if ((5)≤(e) ∧ (e)≤((2)*q+2)) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event24 q e) (((5)≤(e) ∧ (e)≤((2)*q+2)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp only [event24]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_24,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event25 (q e : Int) (p : Int×Int) : Prop := (((3)*q+1)≤e ∧ e≤((3)*q+1))
theorem atom25_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event25 q e)=
      Identity_left1_0.term_25 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event25 q e)=
      if (((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event25 q e) ((((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp only [event25]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_25,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event26 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤((2)*q+2)) ∧ (((3)*q+1)≤e ∧ e≤((3)*q+1))
theorem atom26_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event26 q e)=
      Identity_left1_0.term_26 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event26 q e)=
      if ((5)≤(e) ∧ (e)≤((2)*q+2) ∧ ((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event26 q e) (((5)≤(e) ∧ (e)≤((2)*q+2) ∧ ((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp only [event26]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_26,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event27 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤((2)*q+2))
theorem atom27_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event27 q e)=
      Identity_left1_0.term_27 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event27 q e)=
      if ((5)≤(e) ∧ (e)≤((2)*q+2)) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event27 q e) (((5)≤(e) ∧ (e)≤((2)*q+2)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp only [event27]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_27,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event28 (q e : Int) (p : Int×Int) : Prop := (((3)*q+1)≤e ∧ e≤((3)*q+1))
theorem atom28_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event28 q e)=
      Identity_left1_0.term_28 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event28 q e)=
      if (((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event28 q e) ((((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp only [event28]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_28,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event29 (q e : Int) (p : Int×Int) : Prop := (((3)*q+2)≤e ∧ e≤((4)*q))
theorem atom29_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event29 q e)=
      Identity_left1_0.term_29 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event29 q e)=
      if (((3)*q+2)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event29 q e) ((((3)*q+2)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp only [event29]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_29,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event30 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤((2)*q+2)) ∧ (((3)*q+1)≤e ∧ e≤((3)*q+1))
theorem atom30_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event30 q e)=
      Identity_left1_0.term_30 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event30 q e)=
      if ((5)≤(e) ∧ (e)≤((2)*q+2) ∧ ((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event30 q e) (((5)≤(e) ∧ (e)≤((2)*q+2) ∧ ((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp only [event30]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_30,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event31 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤((2)*q+2)) ∧ (((3)*q+2)≤e ∧ e≤((4)*q))
theorem atom31_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event31 q e)=
      Identity_left1_0.term_31 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event31 q e)=
      if ((5)≤(e) ∧ (e)≤((2)*q+2) ∧ ((3)*q+2)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event31 q e) (((5)≤(e) ∧ (e)≤((2)*q+2) ∧ ((3)*q+2)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp only [event31]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_31,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event32 (q e : Int) (p : Int×Int) : Prop := (((3)*q+1)≤e ∧ e≤((3)*q+1)) ∧ (((3)*q+2)≤e ∧ e≤((4)*q))
theorem atom32_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event32 q e)=
      Identity_left1_0.term_32 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event32 q e)=
      if (((3)*q+1)≤(e) ∧ (e)≤((3)*q+1) ∧ ((3)*q+2)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event32 q e) ((((3)*q+1)≤(e) ∧ (e)≤((3)*q+1) ∧ ((3)*q+2)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp only [event32]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_32,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event33 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤((2)*q+2)) ∧ (((3)*q+1)≤e ∧ e≤((3)*q+1)) ∧ (((3)*q+2)≤e ∧ e≤((4)*q))
theorem atom33_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event33 q e)=
      Identity_left1_0.term_33 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event33 q e)=
      if ((5)≤(e) ∧ (e)≤((2)*q+2) ∧ ((3)*q+1)≤(e) ∧ (e)≤((3)*q+1) ∧ ((3)*q+2)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event33 q e) (((5)≤(e) ∧ (e)≤((2)*q+2) ∧ ((3)*q+1)≤(e) ∧ (e)≤((3)*q+1) ∧ ((3)*q+2)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp only [event33]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_33,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event34 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(p.1))
theorem atom34_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .upper (4) (q+1) (4) (q+1) (0:Int)) (event34 q e)=
      Identity_left1_0.term_34 q e := by
  classical
  have hc : 2*tally (orientedPoints .upper (4) (q+1) (4) (q+1) (0:Int)) (event34 q e)=
      if ((5)≤(e)) then orientedCount2 .upper (max (4) (e)) (q+1) (4) (q+1) (0:Int) else 0 := by
    apply tally_oriented_predicate .upper (4) (q+1) (4) (q+1) (0:Int) (max (4) (e)) (q+1) (4) (q+1) (event34 q e) (((5)≤(e)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .upper (4) (q+1) (4) (q+1) (0:Int) p.1 p.2).mp hp
      simp only [event34]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_34,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event35 (q e : Int) (p : Int×Int) : Prop := (((2)*q+p.2)≤e ∧ e≤((4)*q))
theorem atom35_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .upper (4) (q+1) (4) (q+1) (0:Int)) (event35 q e)=
      Identity_left1_0.term_35 q e := by
  classical
  have hc : 2*tally (orientedPoints .upper (4) (q+1) (4) (q+1) (0:Int)) (event35 q e)=
      if ((e)≤((4)*q)) then orientedCount2 .upper (4) (q+1) (4) (min (q+1) ((-2)*q+e)) (0:Int) else 0 := by
    apply tally_oriented_predicate .upper (4) (q+1) (4) (q+1) (0:Int) (4) (q+1) (4) (min (q+1) ((-2)*q+e)) (event35 q e) (((e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .upper (4) (q+1) (4) (q+1) (0:Int) p.1 p.2).mp hp
      simp only [event35]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_35,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event36 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(p.1)) ∧ (((2)*q+p.2)≤e ∧ e≤((4)*q))
theorem atom36_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .upper (4) (q+1) (4) (q+1) (0:Int)) (event36 q e)=
      Identity_left1_0.term_36 q e := by
  classical
  have hc : 2*tally (orientedPoints .upper (4) (q+1) (4) (q+1) (0:Int)) (event36 q e)=
      if ((5)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .upper (max (4) (e)) (q+1) (4) (min (q+1) ((-2)*q+e)) (0:Int) else 0 := by
    apply tally_oriented_predicate .upper (4) (q+1) (4) (q+1) (0:Int) (max (4) (e)) (q+1) (4) (min (q+1) ((-2)*q+e)) (event36 q e) (((5)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .upper (4) (q+1) (4) (q+1) (0:Int) p.1 p.2).mp hp
      simp only [event36]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_36,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event37 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(p.1))
theorem atom37_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .upper (4) (q+1) (q+3) ((2)*q+1) (0:Int)) (event37 q e)=
      Identity_left1_0.term_37 q e := by
  classical
  have hc : 2*tally (orientedPoints .upper (4) (q+1) (q+3) ((2)*q+1) (0:Int)) (event37 q e)=
      if ((5)≤(e)) then orientedCount2 .upper (max (4) (e)) (q+1) (q+3) ((2)*q+1) (0:Int) else 0 := by
    apply tally_oriented_predicate .upper (4) (q+1) (q+3) ((2)*q+1) (0:Int) (max (4) (e)) (q+1) (q+3) ((2)*q+1) (event37 q e) (((5)≤(e)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .upper (4) (q+1) (q+3) ((2)*q+1) (0:Int) p.1 p.2).mp hp
      simp only [event37]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_37,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event38 (q e : Int) (p : Int×Int) : Prop := (((2)*q+p.2+(-1))≤e ∧ e≤((4)*q))
theorem atom38_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .upper (4) (q+1) (q+3) ((2)*q+1) (0:Int)) (event38 q e)=
      Identity_left1_0.term_38 q e := by
  classical
  have hc : 2*tally (orientedPoints .upper (4) (q+1) (q+3) ((2)*q+1) (0:Int)) (event38 q e)=
      if ((e)≤((4)*q)) then orientedCount2 .upper (4) (q+1) (q+3) (min ((2)*q+1) ((-2)*q+e+1)) (0:Int) else 0 := by
    apply tally_oriented_predicate .upper (4) (q+1) (q+3) ((2)*q+1) (0:Int) (4) (q+1) (q+3) (min ((2)*q+1) ((-2)*q+e+1)) (event38 q e) (((e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .upper (4) (q+1) (q+3) ((2)*q+1) (0:Int) p.1 p.2).mp hp
      simp only [event38]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_38,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event39 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(p.1)) ∧ (((2)*q+p.2+(-1))≤e ∧ e≤((4)*q))
theorem atom39_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .upper (4) (q+1) (q+3) ((2)*q+1) (0:Int)) (event39 q e)=
      Identity_left1_0.term_39 q e := by
  classical
  have hc : 2*tally (orientedPoints .upper (4) (q+1) (q+3) ((2)*q+1) (0:Int)) (event39 q e)=
      if ((5)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .upper (max (4) (e)) (q+1) (q+3) (min ((2)*q+1) ((-2)*q+e+1)) (0:Int) else 0 := by
    apply tally_oriented_predicate .upper (4) (q+1) (q+3) ((2)*q+1) (0:Int) (max (4) (e)) (q+1) (q+3) (min ((2)*q+1) ((-2)*q+e+1)) (event39 q e) (((5)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .upper (4) (q+1) (q+3) ((2)*q+1) (0:Int) p.1 p.2).mp hp
      simp only [event39]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_39,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event40 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(p.1))
theorem atom40_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .upper (q+3) ((2)*q+1) (4) (q+1) (0:Int)) (event40 q e)=
      Identity_left1_0.term_40 q e := by
  classical
  have hc : 2*tally (orientedPoints .upper (q+3) ((2)*q+1) (4) (q+1) (0:Int)) (event40 q e)=
      if ((5)≤(e)) then orientedCount2 .upper (max (q+3) (e)) ((2)*q+1) (4) (q+1) (0:Int) else 0 := by
    apply tally_oriented_predicate .upper (q+3) ((2)*q+1) (4) (q+1) (0:Int) (max (q+3) (e)) ((2)*q+1) (4) (q+1) (event40 q e) (((5)≤(e)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .upper (q+3) ((2)*q+1) (4) (q+1) (0:Int) p.1 p.2).mp hp
      simp only [event40]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_40,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event41 (q e : Int) (p : Int×Int) : Prop := (((2)*q+p.2)≤e ∧ e≤((4)*q))
theorem atom41_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .upper (q+3) ((2)*q+1) (4) (q+1) (0:Int)) (event41 q e)=
      Identity_left1_0.term_41 q e := by
  classical
  have hc : 2*tally (orientedPoints .upper (q+3) ((2)*q+1) (4) (q+1) (0:Int)) (event41 q e)=
      if ((e)≤((4)*q)) then orientedCount2 .upper (q+3) ((2)*q+1) (4) (min (q+1) ((-2)*q+e)) (0:Int) else 0 := by
    apply tally_oriented_predicate .upper (q+3) ((2)*q+1) (4) (q+1) (0:Int) (q+3) ((2)*q+1) (4) (min (q+1) ((-2)*q+e)) (event41 q e) (((e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .upper (q+3) ((2)*q+1) (4) (q+1) (0:Int) p.1 p.2).mp hp
      simp only [event41]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_41,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event42 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(p.1)) ∧ (((2)*q+p.2)≤e ∧ e≤((4)*q))
theorem atom42_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .upper (q+3) ((2)*q+1) (4) (q+1) (0:Int)) (event42 q e)=
      Identity_left1_0.term_42 q e := by
  classical
  have hc : 2*tally (orientedPoints .upper (q+3) ((2)*q+1) (4) (q+1) (0:Int)) (event42 q e)=
      if ((5)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .upper (max (q+3) (e)) ((2)*q+1) (4) (min (q+1) ((-2)*q+e)) (0:Int) else 0 := by
    apply tally_oriented_predicate .upper (q+3) ((2)*q+1) (4) (q+1) (0:Int) (max (q+3) (e)) ((2)*q+1) (4) (min (q+1) ((-2)*q+e)) (event42 q e) (((5)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .upper (q+3) ((2)*q+1) (4) (q+1) (0:Int) p.1 p.2).mp hp
      simp only [event42]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_42,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event43 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(p.1))
theorem atom43_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .upper (q+3) ((2)*q+1) (q+3) ((2)*q+1) (0:Int)) (event43 q e)=
      Identity_left1_0.term_43 q e := by
  classical
  have hc : 2*tally (orientedPoints .upper (q+3) ((2)*q+1) (q+3) ((2)*q+1) (0:Int)) (event43 q e)=
      if ((5)≤(e)) then orientedCount2 .upper (max (q+3) (e)) ((2)*q+1) (q+3) ((2)*q+1) (0:Int) else 0 := by
    apply tally_oriented_predicate .upper (q+3) ((2)*q+1) (q+3) ((2)*q+1) (0:Int) (max (q+3) (e)) ((2)*q+1) (q+3) ((2)*q+1) (event43 q e) (((5)≤(e)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .upper (q+3) ((2)*q+1) (q+3) ((2)*q+1) (0:Int) p.1 p.2).mp hp
      simp only [event43]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_43,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event44 (q e : Int) (p : Int×Int) : Prop := (((2)*q+p.2+(-1))≤e ∧ e≤((4)*q))
theorem atom44_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .upper (q+3) ((2)*q+1) (q+3) ((2)*q+1) (0:Int)) (event44 q e)=
      Identity_left1_0.term_44 q e := by
  classical
  have hc : 2*tally (orientedPoints .upper (q+3) ((2)*q+1) (q+3) ((2)*q+1) (0:Int)) (event44 q e)=
      if ((e)≤((4)*q)) then orientedCount2 .upper (q+3) ((2)*q+1) (q+3) (min ((2)*q+1) ((-2)*q+e+1)) (0:Int) else 0 := by
    apply tally_oriented_predicate .upper (q+3) ((2)*q+1) (q+3) ((2)*q+1) (0:Int) (q+3) ((2)*q+1) (q+3) (min ((2)*q+1) ((-2)*q+e+1)) (event44 q e) (((e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .upper (q+3) ((2)*q+1) (q+3) ((2)*q+1) (0:Int) p.1 p.2).mp hp
      simp only [event44]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_44,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event45 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(p.1)) ∧ (((2)*q+p.2+(-1))≤e ∧ e≤((4)*q))
theorem atom45_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .upper (q+3) ((2)*q+1) (q+3) ((2)*q+1) (0:Int)) (event45 q e)=
      Identity_left1_0.term_45 q e := by
  classical
  have hc : 2*tally (orientedPoints .upper (q+3) ((2)*q+1) (q+3) ((2)*q+1) (0:Int)) (event45 q e)=
      if ((5)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .upper (max (q+3) (e)) ((2)*q+1) (q+3) (min ((2)*q+1) ((-2)*q+e+1)) (0:Int) else 0 := by
    apply tally_oriented_predicate .upper (q+3) ((2)*q+1) (q+3) ((2)*q+1) (0:Int) (max (q+3) (e)) ((2)*q+1) (q+3) (min ((2)*q+1) ((-2)*q+e+1)) (event45 q e) (((5)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .upper (q+3) ((2)*q+1) (q+3) ((2)*q+1) (0:Int) p.1 p.2).mp hp
      simp only [event45]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_45,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event46 (q e : Int) (p : Int×Int) : Prop := (((4)*q)≤e ∧ e≤((4)*q))
theorem atom46_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .rect (q+3) (q+3) (q+3) (q+3) (0:Int)) (event46 q e)=
      Identity_left1_0.term_46 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (q+3) (q+3) (q+3) (q+3) (0:Int)) (event46 q e)=
      if (((4)*q)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect (q+3) (q+3) (q+3) (q+3) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (q+3) (q+3) (q+3) (q+3) (0:Int) (q+3) (q+3) (q+3) (q+3) (event46 q e) ((((4)*q)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (q+3) (q+3) (q+3) (q+3) (0:Int) p.1 p.2).mp hp
      simp only [event46]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_46,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event47 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(q+3))
theorem atom47_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event47 q e)=
      Identity_left1_0.term_47 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event47 q e)=
      if ((5)≤(e) ∧ (e)≤(q+3)) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event47 q e) (((5)≤(e) ∧ (e)≤(q+3)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp only [event47]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_47,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event48 (q e : Int) (p : Int×Int) : Prop := (((3)*q+2)≤e ∧ e≤((4)*q))
theorem atom48_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event48 q e)=
      Identity_left1_0.term_48 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event48 q e)=
      if (((3)*q+2)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event48 q e) ((((3)*q+2)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp only [event48]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_48,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event49 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(q+3)) ∧ (((3)*q+2)≤e ∧ e≤((4)*q))
theorem atom49_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event49 q e)=
      Identity_left1_0.term_49 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event49 q e)=
      if ((5)≤(e) ∧ (e)≤(q+3) ∧ ((3)*q+2)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event49 q e) (((5)≤(e) ∧ (e)≤(q+3) ∧ ((3)*q+2)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp only [event49]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_49,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event50 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(p.1))
theorem atom50_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (4) (q+1) (0:Int) (0:Int) (0:Int)) (event50 q e)=
      Identity_left1_0.term_50 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (4) (q+1) (0:Int) (0:Int) (0:Int)) (event50 q e)=
      if ((5)≤(e)) then orientedCount2 .rect (max (4) (e)) (q+1) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (4) (q+1) (0:Int) (0:Int) (0:Int) (max (4) (e)) (q+1) (0:Int) (0:Int) (event50 q e) (((5)≤(e)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (4) (q+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp only [event50]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_50,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event51 (q e : Int) (p : Int×Int) : Prop := (((2)*q+1)≤e ∧ e≤((4)*q))
theorem atom51_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (4) (q+1) (0:Int) (0:Int) (0:Int)) (event51 q e)=
      Identity_left1_0.term_51 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (4) (q+1) (0:Int) (0:Int) (0:Int)) (event51 q e)=
      if (((2)*q+1)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect (4) (q+1) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (4) (q+1) (0:Int) (0:Int) (0:Int) (4) (q+1) (0:Int) (0:Int) (event51 q e) ((((2)*q+1)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (4) (q+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp only [event51]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_51,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event52 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(p.1)) ∧ (((2)*q+1)≤e ∧ e≤((4)*q))
theorem atom52_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .rect (4) (q+1) (0:Int) (0:Int) (0:Int)) (event52 q e)=
      Identity_left1_0.term_52 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (4) (q+1) (0:Int) (0:Int) (0:Int)) (event52 q e)=
      if ((5)≤(e) ∧ ((2)*q+1)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect (max (4) (e)) (q+1) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (4) (q+1) (0:Int) (0:Int) (0:Int) (max (4) (e)) (q+1) (0:Int) (0:Int) (event52 q e) (((5)≤(e) ∧ ((2)*q+1)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (4) (q+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp only [event52]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_52,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event53 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(p.1))
theorem atom53_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (q+3) ((2)*q+(-1)) (0:Int) (0:Int) (0:Int)) (event53 q e)=
      Identity_left1_0.term_53 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (q+3) ((2)*q+(-1)) (0:Int) (0:Int) (0:Int)) (event53 q e)=
      if ((5)≤(e)) then orientedCount2 .rect (max (q+3) (e)) ((2)*q+(-1)) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (q+3) ((2)*q+(-1)) (0:Int) (0:Int) (0:Int) (max (q+3) (e)) ((2)*q+(-1)) (0:Int) (0:Int) (event53 q e) (((5)≤(e)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (q+3) ((2)*q+(-1)) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp only [event53]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_53,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event54 (q e : Int) (p : Int×Int) : Prop := (((2)*q+1)≤e ∧ e≤((4)*q))
theorem atom54_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (q+3) ((2)*q+(-1)) (0:Int) (0:Int) (0:Int)) (event54 q e)=
      Identity_left1_0.term_54 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (q+3) ((2)*q+(-1)) (0:Int) (0:Int) (0:Int)) (event54 q e)=
      if (((2)*q+1)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect (q+3) ((2)*q+(-1)) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (q+3) ((2)*q+(-1)) (0:Int) (0:Int) (0:Int) (q+3) ((2)*q+(-1)) (0:Int) (0:Int) (event54 q e) ((((2)*q+1)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (q+3) ((2)*q+(-1)) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp only [event54]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_54,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event55 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(p.1)) ∧ (((2)*q+1)≤e ∧ e≤((4)*q))
theorem atom55_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .rect (q+3) ((2)*q+(-1)) (0:Int) (0:Int) (0:Int)) (event55 q e)=
      Identity_left1_0.term_55 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (q+3) ((2)*q+(-1)) (0:Int) (0:Int) (0:Int)) (event55 q e)=
      if ((5)≤(e) ∧ ((2)*q+1)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect (max (q+3) (e)) ((2)*q+(-1)) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (q+3) ((2)*q+(-1)) (0:Int) (0:Int) (0:Int) (max (q+3) (e)) ((2)*q+(-1)) (0:Int) (0:Int) (event55 q e) (((5)≤(e) ∧ ((2)*q+1)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (q+3) ((2)*q+(-1)) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp only [event55]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_55,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event56 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤((4)*q))
theorem atom56_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event56 q e)=
      Identity_left1_0.term_56 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event56 q e)=
      if ((5)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event56 q e) (((5)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp only [event56]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_56,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event57 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤((2)*q+2))
theorem atom57_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (4) (q+1) (0:Int) (0:Int) (0:Int)) (event57 q e)=
      Identity_left1_0.term_57 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (4) (q+1) (0:Int) (0:Int) (0:Int)) (event57 q e)=
      if ((5)≤(e) ∧ (e)≤((2)*q+2)) then orientedCount2 .rect (4) (q+1) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (4) (q+1) (0:Int) (0:Int) (0:Int) (4) (q+1) (0:Int) (0:Int) (event57 q e) (((5)≤(e) ∧ (e)≤((2)*q+2)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (4) (q+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp only [event57]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_57,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
#print axioms atom12_count
#print axioms atom13_count
#print axioms atom14_count
#print axioms atom15_count
#print axioms atom16_count
#print axioms atom17_count
#print axioms atom18_count
#print axioms atom19_count
#print axioms atom20_count
#print axioms atom21_count
#print axioms atom22_count
#print axioms atom23_count
#print axioms atom24_count
#print axioms atom25_count
#print axioms atom26_count
#print axioms atom27_count
#print axioms atom28_count
#print axioms atom29_count
#print axioms atom30_count
#print axioms atom31_count
#print axioms atom32_count
#print axioms atom33_count
#print axioms atom34_count
#print axioms atom35_count
#print axioms atom36_count
#print axioms atom37_count
#print axioms atom38_count
#print axioms atom39_count
#print axioms atom40_count
#print axioms atom41_count
#print axioms atom42_count
#print axioms atom43_count
#print axioms atom44_count
#print axioms atom45_count
#print axioms atom46_count
#print axioms atom47_count
#print axioms atom48_count
#print axioms atom49_count
#print axioms atom50_count
#print axioms atom51_count
#print axioms atom52_count
#print axioms atom53_count
#print axioms atom54_count
#print axioms atom55_count
#print axioms atom56_count
#print axioms atom57_count
end
end LuRazLattice.AtomCounts
