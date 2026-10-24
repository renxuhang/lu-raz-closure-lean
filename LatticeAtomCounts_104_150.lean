import LatticeTally
import SpectrumIdentity_left1_0
namespace LuRazLattice.AtomCounts
set_option maxRecDepth 32768
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
noncomputable section
def event104 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤((2)*q+2)) ∧ (((3)*q+1)≤e ∧ e≤((3)*q+1))
theorem atom104_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int)) (event104 q e)=
      Identity_left1_0.term_104 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int)) (event104 q e)=
      if ((5)≤(e) ∧ (e)≤((2)*q+2) ∧ ((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)) then orientedCount2 .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int) (q+4) ((2)*q+1) (0:Int) (0:Int) (event104 q e) (((5)≤(e) ∧ (e)≤((2)*q+2) ∧ ((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event104,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_104,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event105 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤((2)*q+2)) ∧ (((2)*q+p.1+(-1))≤e ∧ e≤((4)*q))
theorem atom105_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int)) (event105 q e)=
      Identity_left1_0.term_105 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int)) (event105 q e)=
      if ((5)≤(e) ∧ (e)≤((2)*q+2) ∧ (e)≤((4)*q)) then orientedCount2 .rect (q+4) (min ((2)*q+1) ((-2)*q+e+1)) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int) (q+4) (min ((2)*q+1) ((-2)*q+e+1)) (0:Int) (0:Int) (event105 q e) (((5)≤(e) ∧ (e)≤((2)*q+2) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event105,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_105,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event106 (q e : Int) (p : Int×Int) : Prop := (((3)*q+1)≤e ∧ e≤((3)*q+1)) ∧ (((2)*q+p.1+(-1))≤e ∧ e≤((4)*q))
theorem atom106_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int)) (event106 q e)=
      Identity_left1_0.term_106 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int)) (event106 q e)=
      if (((3)*q+1)≤(e) ∧ (e)≤((3)*q+1) ∧ (e)≤((4)*q)) then orientedCount2 .rect (q+4) (min ((2)*q+1) ((-2)*q+e+1)) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int) (q+4) (min ((2)*q+1) ((-2)*q+e+1)) (0:Int) (0:Int) (event106 q e) ((((3)*q+1)≤(e) ∧ (e)≤((3)*q+1) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event106,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_106,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event107 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤((2)*q+2)) ∧ (((3)*q+1)≤e ∧ e≤((3)*q+1)) ∧ (((2)*q+p.1+(-1))≤e ∧ e≤((4)*q))
theorem atom107_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int)) (event107 q e)=
      Identity_left1_0.term_107 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int)) (event107 q e)=
      if ((5)≤(e) ∧ (e)≤((2)*q+2) ∧ ((3)*q+1)≤(e) ∧ (e)≤((3)*q+1) ∧ (e)≤((4)*q)) then orientedCount2 .rect (q+4) (min ((2)*q+1) ((-2)*q+e+1)) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int) (q+4) (min ((2)*q+1) ((-2)*q+e+1)) (0:Int) (0:Int) (event107 q e) (((5)≤(e) ∧ (e)≤((2)*q+2) ∧ ((3)*q+1)≤(e) ∧ (e)≤((3)*q+1) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event107,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_107,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event108 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤((2)*q+2))
theorem atom108_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event108 q e)=
      Identity_left1_0.term_108 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event108 q e)=
      if ((5)≤(e) ∧ (e)≤((2)*q+2)) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event108 q e) (((5)≤(e) ∧ (e)≤((2)*q+2)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event108,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_108,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event109 (q e : Int) (p : Int×Int) : Prop := (((3)*q+1)≤e ∧ e≤((4)*q+(-1)))
theorem atom109_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event109 q e)=
      Identity_left1_0.term_109 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event109 q e)=
      if (((3)*q+1)≤(e) ∧ (e)≤((4)*q+(-1))) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event109 q e) ((((3)*q+1)≤(e) ∧ (e)≤((4)*q+(-1))))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event109,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_109,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event110 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤((2)*q+2)) ∧ (((3)*q+1)≤e ∧ e≤((4)*q+(-1)))
theorem atom110_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event110 q e)=
      Identity_left1_0.term_110 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event110 q e)=
      if ((5)≤(e) ∧ (e)≤((2)*q+2) ∧ ((3)*q+1)≤(e) ∧ (e)≤((4)*q+(-1))) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event110 q e) (((5)≤(e) ∧ (e)≤((2)*q+2) ∧ ((3)*q+1)≤(e) ∧ (e)≤((4)*q+(-1))))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event110,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_110,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event111 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(p.1))
theorem atom111_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (4) (q+1) (0:Int) (0:Int) (0:Int)) (event111 q e)=
      Identity_left1_0.term_111 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (4) (q+1) (0:Int) (0:Int) (0:Int)) (event111 q e)=
      if ((5)≤(e)) then orientedCount2 .rect (max (4) (e)) (q+1) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (4) (q+1) (0:Int) (0:Int) (0:Int) (max (4) (e)) (q+1) (0:Int) (0:Int) (event111 q e) (((5)≤(e)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (4) (q+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event111,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_111,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event112 (q e : Int) (p : Int×Int) : Prop := (((2)*q+3)≤e ∧ e≤((4)*q))
theorem atom112_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (4) (q+1) (0:Int) (0:Int) (0:Int)) (event112 q e)=
      Identity_left1_0.term_112 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (4) (q+1) (0:Int) (0:Int) (0:Int)) (event112 q e)=
      if (((2)*q+3)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect (4) (q+1) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (4) (q+1) (0:Int) (0:Int) (0:Int) (4) (q+1) (0:Int) (0:Int) (event112 q e) ((((2)*q+3)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (4) (q+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event112,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_112,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event113 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(p.1)) ∧ (((2)*q+3)≤e ∧ e≤((4)*q))
theorem atom113_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .rect (4) (q+1) (0:Int) (0:Int) (0:Int)) (event113 q e)=
      Identity_left1_0.term_113 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (4) (q+1) (0:Int) (0:Int) (0:Int)) (event113 q e)=
      if ((5)≤(e) ∧ ((2)*q+3)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect (max (4) (e)) (q+1) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (4) (q+1) (0:Int) (0:Int) (0:Int) (max (4) (e)) (q+1) (0:Int) (0:Int) (event113 q e) (((5)≤(e) ∧ ((2)*q+3)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (4) (q+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event113,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_113,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event114 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(p.1))
theorem atom114_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (q+3) ((2)*q+1) (0:Int) (0:Int) (0:Int)) (event114 q e)=
      Identity_left1_0.term_114 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (q+3) ((2)*q+1) (0:Int) (0:Int) (0:Int)) (event114 q e)=
      if ((5)≤(e)) then orientedCount2 .rect (max (q+3) (e)) ((2)*q+1) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (q+3) ((2)*q+1) (0:Int) (0:Int) (0:Int) (max (q+3) (e)) ((2)*q+1) (0:Int) (0:Int) (event114 q e) (((5)≤(e)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (q+3) ((2)*q+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event114,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_114,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event115 (q e : Int) (p : Int×Int) : Prop := (((2)*q+3)≤e ∧ e≤((4)*q))
theorem atom115_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (q+3) ((2)*q+1) (0:Int) (0:Int) (0:Int)) (event115 q e)=
      Identity_left1_0.term_115 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (q+3) ((2)*q+1) (0:Int) (0:Int) (0:Int)) (event115 q e)=
      if (((2)*q+3)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect (q+3) ((2)*q+1) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (q+3) ((2)*q+1) (0:Int) (0:Int) (0:Int) (q+3) ((2)*q+1) (0:Int) (0:Int) (event115 q e) ((((2)*q+3)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (q+3) ((2)*q+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event115,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_115,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event116 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(p.1)) ∧ (((2)*q+3)≤e ∧ e≤((4)*q))
theorem atom116_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .rect (q+3) ((2)*q+1) (0:Int) (0:Int) (0:Int)) (event116 q e)=
      Identity_left1_0.term_116 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (q+3) ((2)*q+1) (0:Int) (0:Int) (0:Int)) (event116 q e)=
      if ((5)≤(e) ∧ ((2)*q+3)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect (max (q+3) (e)) ((2)*q+1) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (q+3) ((2)*q+1) (0:Int) (0:Int) (0:Int) (max (q+3) (e)) ((2)*q+1) (0:Int) (0:Int) (event116 q e) (((5)≤(e) ∧ ((2)*q+3)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (q+3) ((2)*q+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event116,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_116,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event117 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(q+2))
theorem atom117_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event117 q e)=
      Identity_left1_0.term_117 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event117 q e)=
      if ((5)≤(e) ∧ (e)≤(q+2)) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event117 q e) (((5)≤(e) ∧ (e)≤(q+2)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event117,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_117,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event118 (q e : Int) (p : Int×Int) : Prop := (((2)*q+3)≤e ∧ e≤((4)*q))
theorem atom118_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event118 q e)=
      Identity_left1_0.term_118 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event118 q e)=
      if (((2)*q+3)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event118 q e) ((((2)*q+3)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event118,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_118,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event119 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(q+2)) ∧ (((2)*q+3)≤e ∧ e≤((4)*q))
theorem atom119_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event119 q e)=
      Identity_left1_0.term_119 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event119 q e)=
      if ((5)≤(e) ∧ (e)≤(q+2) ∧ ((2)*q+3)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event119 q e) (((5)≤(e) ∧ (e)≤(q+2) ∧ ((2)*q+3)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event119,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_119,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event120 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(p.1))
theorem atom120_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (4) (q+1) (0:Int) (0:Int) (0:Int)) (event120 q e)=
      Identity_left1_0.term_120 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (4) (q+1) (0:Int) (0:Int) (0:Int)) (event120 q e)=
      if ((5)≤(e)) then orientedCount2 .rect (max (4) (e)) (q+1) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (4) (q+1) (0:Int) (0:Int) (0:Int) (max (4) (e)) (q+1) (0:Int) (0:Int) (event120 q e) (((5)≤(e)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (4) (q+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event120,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_120,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event121 (q e : Int) (p : Int×Int) : Prop := (((2)*q+1)≤e ∧ e≤((4)*q))
theorem atom121_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (4) (q+1) (0:Int) (0:Int) (0:Int)) (event121 q e)=
      Identity_left1_0.term_121 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (4) (q+1) (0:Int) (0:Int) (0:Int)) (event121 q e)=
      if (((2)*q+1)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect (4) (q+1) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (4) (q+1) (0:Int) (0:Int) (0:Int) (4) (q+1) (0:Int) (0:Int) (event121 q e) ((((2)*q+1)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (4) (q+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event121,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_121,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event122 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(p.1)) ∧ (((2)*q+1)≤e ∧ e≤((4)*q))
theorem atom122_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .rect (4) (q+1) (0:Int) (0:Int) (0:Int)) (event122 q e)=
      Identity_left1_0.term_122 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (4) (q+1) (0:Int) (0:Int) (0:Int)) (event122 q e)=
      if ((5)≤(e) ∧ ((2)*q+1)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect (max (4) (e)) (q+1) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (4) (q+1) (0:Int) (0:Int) (0:Int) (max (4) (e)) (q+1) (0:Int) (0:Int) (event122 q e) (((5)≤(e) ∧ ((2)*q+1)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (4) (q+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event122,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_122,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event123 (q e : Int) (p : Int×Int) : Prop := ((p.1)≤e ∧ e≤(p.2))
theorem atom123_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .lower (5) (q+3) (0:Int) ((4)*q+(-3)) ((2)*q+(-3))) (event123 q e)=
      Identity_left1_0.term_123 q e := by
  classical
  have hc : 2*tally (orientedPoints .lower (5) (q+3) (0:Int) ((4)*q+(-3)) ((2)*q+(-3))) (event123 q e)=
      if True then orientedCount2 .lower (5) (min (q+3) (e)) (max (0:Int) (e)) ((4)*q+(-3)) ((2)*q+(-3)) else 0 := by
    apply tally_oriented_predicate .lower (5) (q+3) (0:Int) ((4)*q+(-3)) ((2)*q+(-3)) (5) (min (q+3) (e)) (max (0:Int) (e)) ((4)*q+(-3)) (event123 q e) (True)
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .lower (5) (q+3) (0:Int) ((4)*q+(-3)) ((2)*q+(-3)) p.1 p.2).mp hp
      simp at hb
      simp only [event123,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_123,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event124 (q e : Int) (p : Int×Int) : Prop := ((p.1)≤e ∧ e≤(p.2))
theorem atom124_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .lower (q+4) ((2)*q+1) (0:Int) ((4)*q+(-3)) ((2)*q+(-4))) (event124 q e)=
      Identity_left1_0.term_124 q e := by
  classical
  have hc : 2*tally (orientedPoints .lower (q+4) ((2)*q+1) (0:Int) ((4)*q+(-3)) ((2)*q+(-4))) (event124 q e)=
      if True then orientedCount2 .lower (q+4) (min ((2)*q+1) (e)) (max (0:Int) (e)) ((4)*q+(-3)) ((2)*q+(-4)) else 0 := by
    apply tally_oriented_predicate .lower (q+4) ((2)*q+1) (0:Int) ((4)*q+(-3)) ((2)*q+(-4)) (q+4) (min ((2)*q+1) (e)) (max (0:Int) (e)) ((4)*q+(-3)) (event124 q e) (True)
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .lower (q+4) ((2)*q+1) (0:Int) ((4)*q+(-3)) ((2)*q+(-4)) p.1 p.2).mp hp
      simp at hb
      simp only [event124,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_124,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event125 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(q+2))
theorem atom125_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .lower (q+4) ((2)*q+1) (0:Int) ((4)*q+(-3)) ((2)*q+(-4))) (event125 q e)=
      Identity_left1_0.term_125 q e := by
  classical
  have hc : 2*tally (orientedPoints .lower (q+4) ((2)*q+1) (0:Int) ((4)*q+(-3)) ((2)*q+(-4))) (event125 q e)=
      if ((5)≤(e) ∧ (e)≤(q+2)) then orientedCount2 .lower (q+4) ((2)*q+1) (0:Int) ((4)*q+(-3)) ((2)*q+(-4)) else 0 := by
    apply tally_oriented_predicate .lower (q+4) ((2)*q+1) (0:Int) ((4)*q+(-3)) ((2)*q+(-4)) (q+4) ((2)*q+1) (0:Int) ((4)*q+(-3)) (event125 q e) (((5)≤(e) ∧ (e)≤(q+2)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .lower (q+4) ((2)*q+1) (0:Int) ((4)*q+(-3)) ((2)*q+(-4)) p.1 p.2).mp hp
      simp at hb
      simp only [event125,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_125,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event126 (q e : Int) (p : Int×Int) : Prop := ((p.1)≤e ∧ e≤(p.2))
theorem atom126_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .lower (q+4) ((2)*q+1) (0:Int) ((4)*q+(-3)) ((2)*q+(-4))) (event126 q e)=
      Identity_left1_0.term_126 q e := by
  classical
  have hc : 2*tally (orientedPoints .lower (q+4) ((2)*q+1) (0:Int) ((4)*q+(-3)) ((2)*q+(-4))) (event126 q e)=
      if True then orientedCount2 .lower (q+4) (min ((2)*q+1) (e)) (max (0:Int) (e)) ((4)*q+(-3)) ((2)*q+(-4)) else 0 := by
    apply tally_oriented_predicate .lower (q+4) ((2)*q+1) (0:Int) ((4)*q+(-3)) ((2)*q+(-4)) (q+4) (min ((2)*q+1) (e)) (max (0:Int) (e)) ((4)*q+(-3)) (event126 q e) (True)
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .lower (q+4) ((2)*q+1) (0:Int) ((4)*q+(-3)) ((2)*q+(-4)) p.1 p.2).mp hp
      simp at hb
      simp only [event126,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_126,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event127 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(q+2)) ∧ ((p.1)≤e ∧ e≤(p.2))
theorem atom127_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .lower (q+4) ((2)*q+1) (0:Int) ((4)*q+(-3)) ((2)*q+(-4))) (event127 q e)=
      Identity_left1_0.term_127 q e := by
  classical
  have hc : 2*tally (orientedPoints .lower (q+4) ((2)*q+1) (0:Int) ((4)*q+(-3)) ((2)*q+(-4))) (event127 q e)=
      if ((5)≤(e) ∧ (e)≤(q+2)) then orientedCount2 .lower (q+4) (min ((2)*q+1) (e)) (max (0:Int) (e)) ((4)*q+(-3)) ((2)*q+(-4)) else 0 := by
    apply tally_oriented_predicate .lower (q+4) ((2)*q+1) (0:Int) ((4)*q+(-3)) ((2)*q+(-4)) (q+4) (min ((2)*q+1) (e)) (max (0:Int) (e)) ((4)*q+(-3)) (event127 q e) (((5)≤(e) ∧ (e)≤(q+2)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .lower (q+4) ((2)*q+1) (0:Int) ((4)*q+(-3)) ((2)*q+(-4)) p.1 p.2).mp hp
      simp at hb
      simp only [event127,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_127,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event128 (q e : Int) (p : Int×Int) : Prop := ((p.1)≤e ∧ e≤(p.2))
theorem atom128_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .lower (5) (q+3) (0:Int) ((3)*q) ((2)*q+(-3))) (event128 q e)=
      Identity_left1_0.term_128 q e := by
  classical
  have hc : 2*tally (orientedPoints .lower (5) (q+3) (0:Int) ((3)*q) ((2)*q+(-3))) (event128 q e)=
      if True then orientedCount2 .lower (5) (min (q+3) (e)) (max (0:Int) (e)) ((3)*q) ((2)*q+(-3)) else 0 := by
    apply tally_oriented_predicate .lower (5) (q+3) (0:Int) ((3)*q) ((2)*q+(-3)) (5) (min (q+3) (e)) (max (0:Int) (e)) ((3)*q) (event128 q e) (True)
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .lower (5) (q+3) (0:Int) ((3)*q) ((2)*q+(-3)) p.1 p.2).mp hp
      simp at hb
      simp only [event128,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_128,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event129 (q e : Int) (p : Int×Int) : Prop := (((3)*q+2)≤e ∧ e≤((4)*q))
theorem atom129_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .lower (5) (q+3) (0:Int) ((3)*q) ((2)*q+(-3))) (event129 q e)=
      Identity_left1_0.term_129 q e := by
  classical
  have hc : 2*tally (orientedPoints .lower (5) (q+3) (0:Int) ((3)*q) ((2)*q+(-3))) (event129 q e)=
      if (((3)*q+2)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .lower (5) (q+3) (0:Int) ((3)*q) ((2)*q+(-3)) else 0 := by
    apply tally_oriented_predicate .lower (5) (q+3) (0:Int) ((3)*q) ((2)*q+(-3)) (5) (q+3) (0:Int) ((3)*q) (event129 q e) ((((3)*q+2)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .lower (5) (q+3) (0:Int) ((3)*q) ((2)*q+(-3)) p.1 p.2).mp hp
      simp at hb
      simp only [event129,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_129,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event130 (q e : Int) (p : Int×Int) : Prop := ((p.1)≤e ∧ e≤(p.2)) ∧ (((3)*q+2)≤e ∧ e≤((4)*q))
theorem atom130_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .lower (5) (q+3) (0:Int) ((3)*q) ((2)*q+(-3))) (event130 q e)=
      Identity_left1_0.term_130 q e := by
  classical
  have hc : 2*tally (orientedPoints .lower (5) (q+3) (0:Int) ((3)*q) ((2)*q+(-3))) (event130 q e)=
      if (((3)*q+2)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .lower (5) (min (q+3) (e)) (max (0:Int) (e)) ((3)*q) ((2)*q+(-3)) else 0 := by
    apply tally_oriented_predicate .lower (5) (q+3) (0:Int) ((3)*q) ((2)*q+(-3)) (5) (min (q+3) (e)) (max (0:Int) (e)) ((3)*q) (event130 q e) ((((3)*q+2)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .lower (5) (q+3) (0:Int) ((3)*q) ((2)*q+(-3)) p.1 p.2).mp hp
      simp at hb
      simp only [event130,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_130,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event131 (q e : Int) (p : Int×Int) : Prop := ((p.1)≤e ∧ e≤(p.2))
theorem atom131_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .lower (q+4) (q+4) (0:Int) ((3)*q) ((2)*q+(-4))) (event131 q e)=
      Identity_left1_0.term_131 q e := by
  classical
  have hc : 2*tally (orientedPoints .lower (q+4) (q+4) (0:Int) ((3)*q) ((2)*q+(-4))) (event131 q e)=
      if True then orientedCount2 .lower (q+4) (min (q+4) (e)) (max (0:Int) (e)) ((3)*q) ((2)*q+(-4)) else 0 := by
    apply tally_oriented_predicate .lower (q+4) (q+4) (0:Int) ((3)*q) ((2)*q+(-4)) (q+4) (min (q+4) (e)) (max (0:Int) (e)) ((3)*q) (event131 q e) (True)
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .lower (q+4) (q+4) (0:Int) ((3)*q) ((2)*q+(-4)) p.1 p.2).mp hp
      simp at hb
      simp only [event131,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_131,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event132 (q e : Int) (p : Int×Int) : Prop := (((3)*q+2)≤e ∧ e≤((4)*q))
theorem atom132_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .lower (q+4) (q+4) (0:Int) ((3)*q) ((2)*q+(-4))) (event132 q e)=
      Identity_left1_0.term_132 q e := by
  classical
  have hc : 2*tally (orientedPoints .lower (q+4) (q+4) (0:Int) ((3)*q) ((2)*q+(-4))) (event132 q e)=
      if (((3)*q+2)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .lower (q+4) (q+4) (0:Int) ((3)*q) ((2)*q+(-4)) else 0 := by
    apply tally_oriented_predicate .lower (q+4) (q+4) (0:Int) ((3)*q) ((2)*q+(-4)) (q+4) (q+4) (0:Int) ((3)*q) (event132 q e) ((((3)*q+2)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .lower (q+4) (q+4) (0:Int) ((3)*q) ((2)*q+(-4)) p.1 p.2).mp hp
      simp at hb
      simp only [event132,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_132,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event133 (q e : Int) (p : Int×Int) : Prop := ((p.1)≤e ∧ e≤(p.2)) ∧ (((3)*q+2)≤e ∧ e≤((4)*q))
theorem atom133_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .lower (q+4) (q+4) (0:Int) ((3)*q) ((2)*q+(-4))) (event133 q e)=
      Identity_left1_0.term_133 q e := by
  classical
  have hc : 2*tally (orientedPoints .lower (q+4) (q+4) (0:Int) ((3)*q) ((2)*q+(-4))) (event133 q e)=
      if (((3)*q+2)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .lower (q+4) (min (q+4) (e)) (max (0:Int) (e)) ((3)*q) ((2)*q+(-4)) else 0 := by
    apply tally_oriented_predicate .lower (q+4) (q+4) (0:Int) ((3)*q) ((2)*q+(-4)) (q+4) (min (q+4) (e)) (max (0:Int) (e)) ((3)*q) (event133 q e) ((((3)*q+2)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .lower (q+4) (q+4) (0:Int) ((3)*q) ((2)*q+(-4)) p.1 p.2).mp hp
      simp at hb
      simp only [event133,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_133,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event134 (q e : Int) (p : Int×Int) : Prop := ((p.1)≤e ∧ e≤((4)*q))
theorem atom134_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (5) ((2)*q+1) (0:Int) (0:Int) (0:Int)) (event134 q e)=
      Identity_left1_0.term_134 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (5) ((2)*q+1) (0:Int) (0:Int) (0:Int)) (event134 q e)=
      if ((e)≤((4)*q)) then orientedCount2 .rect (5) (min ((2)*q+1) (e)) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (5) ((2)*q+1) (0:Int) (0:Int) (0:Int) (5) (min ((2)*q+1) (e)) (0:Int) (0:Int) (event134 q e) (((e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (5) ((2)*q+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event134,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_134,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event135 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(q+2))
theorem atom135_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event135 q e)=
      Identity_left1_0.term_135 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event135 q e)=
      if ((5)≤(e) ∧ (e)≤(q+2)) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event135 q e) (((5)≤(e) ∧ (e)≤(q+2)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event135,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_135,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event136 (q e : Int) (p : Int×Int) : Prop := ((q+4)≤e ∧ e≤((3)*q))
theorem atom136_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event136 q e)=
      Identity_left1_0.term_136 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event136 q e)=
      if ((q+4)≤(e) ∧ (e)≤((3)*q)) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event136 q e) (((q+4)≤(e) ∧ (e)≤((3)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event136,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_136,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event137 (q e : Int) (p : Int×Int) : Prop := (((3)*q+2)≤e ∧ e≤((4)*q))
theorem atom137_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event137 q e)=
      Identity_left1_0.term_137 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event137 q e)=
      if (((3)*q+2)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event137 q e) ((((3)*q+2)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event137,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_137,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event138 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(q+2)) ∧ ((q+4)≤e ∧ e≤((3)*q))
theorem atom138_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event138 q e)=
      Identity_left1_0.term_138 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event138 q e)=
      if ((5)≤(e) ∧ (e)≤(q+2) ∧ (q+4)≤(e) ∧ (e)≤((3)*q)) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event138 q e) (((5)≤(e) ∧ (e)≤(q+2) ∧ (q+4)≤(e) ∧ (e)≤((3)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event138,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_138,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event139 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(q+2)) ∧ (((3)*q+2)≤e ∧ e≤((4)*q))
theorem atom139_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event139 q e)=
      Identity_left1_0.term_139 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event139 q e)=
      if ((5)≤(e) ∧ (e)≤(q+2) ∧ ((3)*q+2)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event139 q e) (((5)≤(e) ∧ (e)≤(q+2) ∧ ((3)*q+2)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event139,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_139,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event140 (q e : Int) (p : Int×Int) : Prop := ((q+4)≤e ∧ e≤((3)*q)) ∧ (((3)*q+2)≤e ∧ e≤((4)*q))
theorem atom140_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event140 q e)=
      Identity_left1_0.term_140 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event140 q e)=
      if ((q+4)≤(e) ∧ (e)≤((3)*q) ∧ ((3)*q+2)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event140 q e) (((q+4)≤(e) ∧ (e)≤((3)*q) ∧ ((3)*q+2)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event140,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_140,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event141 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(q+2)) ∧ ((q+4)≤e ∧ e≤((3)*q)) ∧ (((3)*q+2)≤e ∧ e≤((4)*q))
theorem atom141_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event141 q e)=
      Identity_left1_0.term_141 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event141 q e)=
      if ((5)≤(e) ∧ (e)≤(q+2) ∧ (q+4)≤(e) ∧ (e)≤((3)*q) ∧ ((3)*q+2)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event141 q e) (((5)≤(e) ∧ (e)≤(q+2) ∧ (q+4)≤(e) ∧ (e)≤((3)*q) ∧ ((3)*q+2)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event141,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_141,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event142 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(q+2))
theorem atom142_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int)) (event142 q e)=
      Identity_left1_0.term_142 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int)) (event142 q e)=
      if ((5)≤(e) ∧ (e)≤(q+2)) then orientedCount2 .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int) (q+4) ((2)*q+1) (0:Int) (0:Int) (event142 q e) (((5)≤(e) ∧ (e)≤(q+2)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event142,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_142,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event143 (q e : Int) (p : Int×Int) : Prop := ((p.1)≤e ∧ e≤((4)*q))
theorem atom143_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int)) (event143 q e)=
      Identity_left1_0.term_143 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int)) (event143 q e)=
      if ((e)≤((4)*q)) then orientedCount2 .rect (q+4) (min ((2)*q+1) (e)) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int) (q+4) (min ((2)*q+1) (e)) (0:Int) (0:Int) (event143 q e) (((e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event143,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_143,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event144 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(q+2)) ∧ ((p.1)≤e ∧ e≤((4)*q))
theorem atom144_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int)) (event144 q e)=
      Identity_left1_0.term_144 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int)) (event144 q e)=
      if ((5)≤(e) ∧ (e)≤(q+2) ∧ (e)≤((4)*q)) then orientedCount2 .rect (q+4) (min ((2)*q+1) (e)) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int) (q+4) (min ((2)*q+1) (e)) (0:Int) (0:Int) (event144 q e) (((5)≤(e) ∧ (e)≤(q+2) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event144,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_144,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event145 (q e : Int) (p : Int×Int) : Prop := (((2)*q+2)≤e ∧ e≤((4)*q+(-2)))
theorem atom145_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event145 q e)=
      Identity_left1_0.term_145 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event145 q e)=
      if (((2)*q+2)≤(e) ∧ (e)≤((4)*q+(-2))) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event145 q e) ((((2)*q+2)≤(e) ∧ (e)≤((4)*q+(-2))))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event145,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_145,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event146 (q e : Int) (p : Int×Int) : Prop := (((2)*q+3)≤e ∧ e≤((4)*q+(-1)))
theorem atom146_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event146 q e)=
      Identity_left1_0.term_146 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event146 q e)=
      if (((2)*q+3)≤(e) ∧ (e)≤((4)*q+(-1))) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event146 q e) ((((2)*q+3)≤(e) ∧ (e)≤((4)*q+(-1))))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event146,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_146,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event147 (q e : Int) (p : Int×Int) : Prop := (((2)*q+2)≤e ∧ e≤((4)*q+(-1)))
theorem atom147_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event147 q e)=
      Identity_left1_0.term_147 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event147 q e)=
      if (((2)*q+2)≤(e) ∧ (e)≤((4)*q+(-1))) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event147 q e) ((((2)*q+2)≤(e) ∧ (e)≤((4)*q+(-1))))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event147,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_147,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event148 (q e : Int) (p : Int×Int) : Prop := (((2)*q+2)≤e ∧ e≤((4)*q))
theorem atom148_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event148 q e)=
      Identity_left1_0.term_148 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event148 q e)=
      if (((2)*q+2)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event148 q e) ((((2)*q+2)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event148,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_148,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event149 (q e : Int) (p : Int×Int) : Prop := (((2)*q+3)≤e ∧ e≤((4)*q))
theorem atom149_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event149 q e)=
      Identity_left1_0.term_149 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event149 q e)=
      if (((2)*q+3)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event149 q e) ((((2)*q+3)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event149,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_149,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
#print axioms atom104_count
#print axioms atom105_count
#print axioms atom106_count
#print axioms atom107_count
#print axioms atom108_count
#print axioms atom109_count
#print axioms atom110_count
#print axioms atom111_count
#print axioms atom112_count
#print axioms atom113_count
#print axioms atom114_count
#print axioms atom115_count
#print axioms atom116_count
#print axioms atom117_count
#print axioms atom118_count
#print axioms atom119_count
#print axioms atom120_count
#print axioms atom121_count
#print axioms atom122_count
#print axioms atom123_count
#print axioms atom124_count
#print axioms atom125_count
#print axioms atom126_count
#print axioms atom127_count
#print axioms atom128_count
#print axioms atom129_count
#print axioms atom130_count
#print axioms atom131_count
#print axioms atom132_count
#print axioms atom133_count
#print axioms atom134_count
#print axioms atom135_count
#print axioms atom136_count
#print axioms atom137_count
#print axioms atom138_count
#print axioms atom139_count
#print axioms atom140_count
#print axioms atom141_count
#print axioms atom142_count
#print axioms atom143_count
#print axioms atom144_count
#print axioms atom145_count
#print axioms atom146_count
#print axioms atom147_count
#print axioms atom148_count
#print axioms atom149_count
end
end LuRazLattice.AtomCounts
