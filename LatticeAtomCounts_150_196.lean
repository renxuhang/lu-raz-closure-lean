import LatticeTally
import SpectrumIdentity_left1_0
namespace LuRazLattice.AtomCounts
set_option maxRecDepth 32768
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
noncomputable section
def event150 (q e : Int) (p : Int×Int) : Prop := (((2)*q+1)≤e ∧ e≤((4)*q))
theorem atom150_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event150 q e)=
      Identity_left1_0.term_150 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event150 q e)=
      if (((2)*q+1)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event150 q e) ((((2)*q+1)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event150,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_150,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event151 (q e : Int) (p : Int×Int) : Prop := ((p.1)≤e ∧ e≤(p.2))
theorem atom151_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (5) ((2)*q+1) ((4)*q+(-2)) ((4)*q) (0:Int)) (event151 q e)=
      Identity_left1_0.term_151 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (5) ((2)*q+1) ((4)*q+(-2)) ((4)*q) (0:Int)) (event151 q e)=
      if True then orientedCount2 .rect (5) (min ((2)*q+1) (e)) (max ((4)*q+(-2)) (e)) ((4)*q) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (5) ((2)*q+1) ((4)*q+(-2)) ((4)*q) (0:Int) (5) (min ((2)*q+1) (e)) (max ((4)*q+(-2)) (e)) ((4)*q) (event151 q e) (True)
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (5) ((2)*q+1) ((4)*q+(-2)) ((4)*q) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event151,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_151,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event152 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(q+2))
theorem atom152_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (q+4) ((2)*q+1) ((4)*q+(-2)) ((4)*q) (0:Int)) (event152 q e)=
      Identity_left1_0.term_152 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (q+4) ((2)*q+1) ((4)*q+(-2)) ((4)*q) (0:Int)) (event152 q e)=
      if ((5)≤(e) ∧ (e)≤(q+2)) then orientedCount2 .rect (q+4) ((2)*q+1) ((4)*q+(-2)) ((4)*q) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (q+4) ((2)*q+1) ((4)*q+(-2)) ((4)*q) (0:Int) (q+4) ((2)*q+1) ((4)*q+(-2)) ((4)*q) (event152 q e) (((5)≤(e) ∧ (e)≤(q+2)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (q+4) ((2)*q+1) ((4)*q+(-2)) ((4)*q) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event152,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_152,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event153 (q e : Int) (p : Int×Int) : Prop := ((p.1)≤e ∧ e≤(p.2))
theorem atom153_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (q+4) ((2)*q+1) ((4)*q+(-2)) ((4)*q) (0:Int)) (event153 q e)=
      Identity_left1_0.term_153 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (q+4) ((2)*q+1) ((4)*q+(-2)) ((4)*q) (0:Int)) (event153 q e)=
      if True then orientedCount2 .rect (q+4) (min ((2)*q+1) (e)) (max ((4)*q+(-2)) (e)) ((4)*q) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (q+4) ((2)*q+1) ((4)*q+(-2)) ((4)*q) (0:Int) (q+4) (min ((2)*q+1) (e)) (max ((4)*q+(-2)) (e)) ((4)*q) (event153 q e) (True)
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (q+4) ((2)*q+1) ((4)*q+(-2)) ((4)*q) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event153,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_153,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event154 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(q+2)) ∧ ((p.1)≤e ∧ e≤(p.2))
theorem atom154_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .rect (q+4) ((2)*q+1) ((4)*q+(-2)) ((4)*q) (0:Int)) (event154 q e)=
      Identity_left1_0.term_154 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (q+4) ((2)*q+1) ((4)*q+(-2)) ((4)*q) (0:Int)) (event154 q e)=
      if ((5)≤(e) ∧ (e)≤(q+2)) then orientedCount2 .rect (q+4) (min ((2)*q+1) (e)) (max ((4)*q+(-2)) (e)) ((4)*q) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (q+4) ((2)*q+1) ((4)*q+(-2)) ((4)*q) (0:Int) (q+4) (min ((2)*q+1) (e)) (max ((4)*q+(-2)) (e)) ((4)*q) (event154 q e) (((5)≤(e) ∧ (e)≤(q+2)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (q+4) ((2)*q+1) ((4)*q+(-2)) ((4)*q) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event154,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_154,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event155 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(q+2))
theorem atom155_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event155 q e)=
      Identity_left1_0.term_155 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event155 q e)=
      if ((5)≤(e) ∧ (e)≤(q+2)) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event155 q e) (((5)≤(e) ∧ (e)≤(q+2)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event155,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_155,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event156 (q e : Int) (p : Int×Int) : Prop := (((2)*q+2)≤e ∧ e≤((4)*q+(-2)))
theorem atom156_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event156 q e)=
      Identity_left1_0.term_156 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event156 q e)=
      if (((2)*q+2)≤(e) ∧ (e)≤((4)*q+(-2))) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event156 q e) ((((2)*q+2)≤(e) ∧ (e)≤((4)*q+(-2))))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event156,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_156,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event157 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(q+2)) ∧ (((2)*q+2)≤e ∧ e≤((4)*q+(-2)))
theorem atom157_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event157 q e)=
      Identity_left1_0.term_157 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event157 q e)=
      if ((5)≤(e) ∧ (e)≤(q+2) ∧ ((2)*q+2)≤(e) ∧ (e)≤((4)*q+(-2))) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event157 q e) (((5)≤(e) ∧ (e)≤(q+2) ∧ ((2)*q+2)≤(e) ∧ (e)≤((4)*q+(-2))))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event157,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_157,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event158 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(q+2))
theorem atom158_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event158 q e)=
      Identity_left1_0.term_158 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event158 q e)=
      if ((5)≤(e) ∧ (e)≤(q+2)) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event158 q e) (((5)≤(e) ∧ (e)≤(q+2)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event158,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_158,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event159 (q e : Int) (p : Int×Int) : Prop := (((2)*q+3)≤e ∧ e≤((4)*q+(-1)))
theorem atom159_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event159 q e)=
      Identity_left1_0.term_159 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event159 q e)=
      if (((2)*q+3)≤(e) ∧ (e)≤((4)*q+(-1))) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event159 q e) ((((2)*q+3)≤(e) ∧ (e)≤((4)*q+(-1))))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event159,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_159,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event160 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(q+2)) ∧ (((2)*q+3)≤e ∧ e≤((4)*q+(-1)))
theorem atom160_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event160 q e)=
      Identity_left1_0.term_160 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event160 q e)=
      if ((5)≤(e) ∧ (e)≤(q+2) ∧ ((2)*q+3)≤(e) ∧ (e)≤((4)*q+(-1))) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event160 q e) (((5)≤(e) ∧ (e)≤(q+2) ∧ ((2)*q+3)≤(e) ∧ (e)≤((4)*q+(-1))))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event160,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_160,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event161 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(q+2))
theorem atom161_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event161 q e)=
      Identity_left1_0.term_161 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event161 q e)=
      if ((5)≤(e) ∧ (e)≤(q+2)) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event161 q e) (((5)≤(e) ∧ (e)≤(q+2)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event161,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_161,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event162 (q e : Int) (p : Int×Int) : Prop := (((2)*q+2)≤e ∧ e≤((4)*q+(-1)))
theorem atom162_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event162 q e)=
      Identity_left1_0.term_162 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event162 q e)=
      if (((2)*q+2)≤(e) ∧ (e)≤((4)*q+(-1))) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event162 q e) ((((2)*q+2)≤(e) ∧ (e)≤((4)*q+(-1))))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event162,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_162,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event163 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(q+2)) ∧ (((2)*q+2)≤e ∧ e≤((4)*q+(-1)))
theorem atom163_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event163 q e)=
      Identity_left1_0.term_163 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event163 q e)=
      if ((5)≤(e) ∧ (e)≤(q+2) ∧ ((2)*q+2)≤(e) ∧ (e)≤((4)*q+(-1))) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event163 q e) (((5)≤(e) ∧ (e)≤(q+2) ∧ ((2)*q+2)≤(e) ∧ (e)≤((4)*q+(-1))))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event163,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_163,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event164 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(q+2))
theorem atom164_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event164 q e)=
      Identity_left1_0.term_164 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event164 q e)=
      if ((5)≤(e) ∧ (e)≤(q+2)) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event164 q e) (((5)≤(e) ∧ (e)≤(q+2)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event164,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_164,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event165 (q e : Int) (p : Int×Int) : Prop := (((2)*q+2)≤e ∧ e≤((4)*q))
theorem atom165_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event165 q e)=
      Identity_left1_0.term_165 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event165 q e)=
      if (((2)*q+2)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event165 q e) ((((2)*q+2)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event165,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_165,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event166 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(q+2)) ∧ (((2)*q+2)≤e ∧ e≤((4)*q))
theorem atom166_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event166 q e)=
      Identity_left1_0.term_166 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event166 q e)=
      if ((5)≤(e) ∧ (e)≤(q+2) ∧ ((2)*q+2)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event166 q e) (((5)≤(e) ∧ (e)≤(q+2) ∧ ((2)*q+2)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event166,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_166,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event167 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(q+2))
theorem atom167_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event167 q e)=
      Identity_left1_0.term_167 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event167 q e)=
      if ((5)≤(e) ∧ (e)≤(q+2)) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event167 q e) (((5)≤(e) ∧ (e)≤(q+2)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event167,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_167,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event168 (q e : Int) (p : Int×Int) : Prop := (((2)*q+3)≤e ∧ e≤((4)*q))
theorem atom168_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event168 q e)=
      Identity_left1_0.term_168 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event168 q e)=
      if (((2)*q+3)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event168 q e) ((((2)*q+3)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event168,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_168,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event169 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(q+2)) ∧ (((2)*q+3)≤e ∧ e≤((4)*q))
theorem atom169_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event169 q e)=
      Identity_left1_0.term_169 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event169 q e)=
      if ((5)≤(e) ∧ (e)≤(q+2) ∧ ((2)*q+3)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event169 q e) (((5)≤(e) ∧ (e)≤(q+2) ∧ ((2)*q+3)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event169,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_169,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event170 (q e : Int) (p : Int×Int) : Prop := ((p.1)≤e ∧ e≤((4)*q))
theorem atom170_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (5) ((2)*q+1) (0:Int) (0:Int) (0:Int)) (event170 q e)=
      Identity_left1_0.term_170 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (5) ((2)*q+1) (0:Int) (0:Int) (0:Int)) (event170 q e)=
      if ((e)≤((4)*q)) then orientedCount2 .rect (5) (min ((2)*q+1) (e)) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (5) ((2)*q+1) (0:Int) (0:Int) (0:Int) (5) (min ((2)*q+1) (e)) (0:Int) (0:Int) (event170 q e) (((e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (5) ((2)*q+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event170,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_170,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event171 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(q+2))
theorem atom171_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int)) (event171 q e)=
      Identity_left1_0.term_171 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int)) (event171 q e)=
      if ((5)≤(e) ∧ (e)≤(q+2)) then orientedCount2 .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int) (q+4) ((2)*q+1) (0:Int) (0:Int) (event171 q e) (((5)≤(e) ∧ (e)≤(q+2)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event171,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_171,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event172 (q e : Int) (p : Int×Int) : Prop := ((p.1)≤e ∧ e≤((4)*q))
theorem atom172_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int)) (event172 q e)=
      Identity_left1_0.term_172 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int)) (event172 q e)=
      if ((e)≤((4)*q)) then orientedCount2 .rect (q+4) (min ((2)*q+1) (e)) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int) (q+4) (min ((2)*q+1) (e)) (0:Int) (0:Int) (event172 q e) (((e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event172,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_172,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event173 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(q+2)) ∧ ((p.1)≤e ∧ e≤((4)*q))
theorem atom173_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int)) (event173 q e)=
      Identity_left1_0.term_173 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int)) (event173 q e)=
      if ((5)≤(e) ∧ (e)≤(q+2) ∧ (e)≤((4)*q)) then orientedCount2 .rect (q+4) (min ((2)*q+1) (e)) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int) (q+4) (min ((2)*q+1) (e)) (0:Int) (0:Int) (event173 q e) (((5)≤(e) ∧ (e)≤(q+2) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event173,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_173,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event174 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(p.1))
theorem atom174_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect ((2)*q+2) ((3)*q+(-1)) (0:Int) (0:Int) (0:Int)) (event174 q e)=
      Identity_left1_0.term_174 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect ((2)*q+2) ((3)*q+(-1)) (0:Int) (0:Int) (0:Int)) (event174 q e)=
      if ((5)≤(e)) then orientedCount2 .rect (max ((2)*q+2) (e)) ((3)*q+(-1)) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect ((2)*q+2) ((3)*q+(-1)) (0:Int) (0:Int) (0:Int) (max ((2)*q+2) (e)) ((3)*q+(-1)) (0:Int) (0:Int) (event174 q e) (((5)≤(e)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect ((2)*q+2) ((3)*q+(-1)) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event174,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_174,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event175 (q e : Int) (p : Int×Int) : Prop := (((3)*q+1)≤e ∧ e≤((3)*q+1))
theorem atom175_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect ((2)*q+2) ((3)*q+(-1)) (0:Int) (0:Int) (0:Int)) (event175 q e)=
      Identity_left1_0.term_175 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect ((2)*q+2) ((3)*q+(-1)) (0:Int) (0:Int) (0:Int)) (event175 q e)=
      if (((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)) then orientedCount2 .rect ((2)*q+2) ((3)*q+(-1)) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect ((2)*q+2) ((3)*q+(-1)) (0:Int) (0:Int) (0:Int) ((2)*q+2) ((3)*q+(-1)) (0:Int) (0:Int) (event175 q e) ((((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect ((2)*q+2) ((3)*q+(-1)) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event175,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_175,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event176 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(p.1)) ∧ (((3)*q+1)≤e ∧ e≤((3)*q+1))
theorem atom176_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .rect ((2)*q+2) ((3)*q+(-1)) (0:Int) (0:Int) (0:Int)) (event176 q e)=
      Identity_left1_0.term_176 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect ((2)*q+2) ((3)*q+(-1)) (0:Int) (0:Int) (0:Int)) (event176 q e)=
      if ((5)≤(e) ∧ ((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)) then orientedCount2 .rect (max ((2)*q+2) (e)) ((3)*q+(-1)) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect ((2)*q+2) ((3)*q+(-1)) (0:Int) (0:Int) (0:Int) (max ((2)*q+2) (e)) ((3)*q+(-1)) (0:Int) (0:Int) (event176 q e) (((5)≤(e) ∧ ((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect ((2)*q+2) ((3)*q+(-1)) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event176,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_176,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event177 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(p.1))
theorem atom177_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect ((3)*q+1) ((4)*q+(-3)) (0:Int) (0:Int) (0:Int)) (event177 q e)=
      Identity_left1_0.term_177 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect ((3)*q+1) ((4)*q+(-3)) (0:Int) (0:Int) (0:Int)) (event177 q e)=
      if ((5)≤(e)) then orientedCount2 .rect (max ((3)*q+1) (e)) ((4)*q+(-3)) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect ((3)*q+1) ((4)*q+(-3)) (0:Int) (0:Int) (0:Int) (max ((3)*q+1) (e)) ((4)*q+(-3)) (0:Int) (0:Int) (event177 q e) (((5)≤(e)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect ((3)*q+1) ((4)*q+(-3)) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event177,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_177,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event178 (q e : Int) (p : Int×Int) : Prop := (((3)*q+1)≤e ∧ e≤((3)*q+1))
theorem atom178_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect ((3)*q+1) ((4)*q+(-3)) (0:Int) (0:Int) (0:Int)) (event178 q e)=
      Identity_left1_0.term_178 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect ((3)*q+1) ((4)*q+(-3)) (0:Int) (0:Int) (0:Int)) (event178 q e)=
      if (((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)) then orientedCount2 .rect ((3)*q+1) ((4)*q+(-3)) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect ((3)*q+1) ((4)*q+(-3)) (0:Int) (0:Int) (0:Int) ((3)*q+1) ((4)*q+(-3)) (0:Int) (0:Int) (event178 q e) ((((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect ((3)*q+1) ((4)*q+(-3)) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event178,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_178,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event179 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(p.1)) ∧ (((3)*q+1)≤e ∧ e≤((3)*q+1))
theorem atom179_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .rect ((3)*q+1) ((4)*q+(-3)) (0:Int) (0:Int) (0:Int)) (event179 q e)=
      Identity_left1_0.term_179 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect ((3)*q+1) ((4)*q+(-3)) (0:Int) (0:Int) (0:Int)) (event179 q e)=
      if ((5)≤(e) ∧ ((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)) then orientedCount2 .rect (max ((3)*q+1) (e)) ((4)*q+(-3)) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect ((3)*q+1) ((4)*q+(-3)) (0:Int) (0:Int) (0:Int) (max ((3)*q+1) (e)) ((4)*q+(-3)) (0:Int) (0:Int) (event179 q e) (((5)≤(e) ∧ ((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect ((3)*q+1) ((4)*q+(-3)) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event179,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_179,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event180 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(p.1))
theorem atom180_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect ((2)*q+2) ((4)*q+(-3)) (0:Int) (0:Int) (0:Int)) (event180 q e)=
      Identity_left1_0.term_180 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect ((2)*q+2) ((4)*q+(-3)) (0:Int) (0:Int) (0:Int)) (event180 q e)=
      if ((5)≤(e)) then orientedCount2 .rect (max ((2)*q+2) (e)) ((4)*q+(-3)) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect ((2)*q+2) ((4)*q+(-3)) (0:Int) (0:Int) (0:Int) (max ((2)*q+2) (e)) ((4)*q+(-3)) (0:Int) (0:Int) (event180 q e) (((5)≤(e)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect ((2)*q+2) ((4)*q+(-3)) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event180,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_180,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event181 (q e : Int) (p : Int×Int) : Prop := (((4)*q)≤e ∧ e≤((4)*q))
theorem atom181_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect ((2)*q+2) ((4)*q+(-3)) (0:Int) (0:Int) (0:Int)) (event181 q e)=
      Identity_left1_0.term_181 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect ((2)*q+2) ((4)*q+(-3)) (0:Int) (0:Int) (0:Int)) (event181 q e)=
      if (((4)*q)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect ((2)*q+2) ((4)*q+(-3)) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect ((2)*q+2) ((4)*q+(-3)) (0:Int) (0:Int) (0:Int) ((2)*q+2) ((4)*q+(-3)) (0:Int) (0:Int) (event181 q e) ((((4)*q)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect ((2)*q+2) ((4)*q+(-3)) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event181,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_181,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event182 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(p.1)) ∧ (((4)*q)≤e ∧ e≤((4)*q))
theorem atom182_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .rect ((2)*q+2) ((4)*q+(-3)) (0:Int) (0:Int) (0:Int)) (event182 q e)=
      Identity_left1_0.term_182 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect ((2)*q+2) ((4)*q+(-3)) (0:Int) (0:Int) (0:Int)) (event182 q e)=
      if ((5)≤(e) ∧ ((4)*q)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect (max ((2)*q+2) (e)) ((4)*q+(-3)) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect ((2)*q+2) ((4)*q+(-3)) (0:Int) (0:Int) (0:Int) (max ((2)*q+2) (e)) ((4)*q+(-3)) (0:Int) (0:Int) (event182 q e) (((5)≤(e) ∧ ((4)*q)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect ((2)*q+2) ((4)*q+(-3)) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event182,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_182,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event183 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(p.1))
theorem atom183_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect ((2)*q+2) ((3)*q+(-1)) (0:Int) (0:Int) (0:Int)) (event183 q e)=
      Identity_left1_0.term_183 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect ((2)*q+2) ((3)*q+(-1)) (0:Int) (0:Int) (0:Int)) (event183 q e)=
      if ((5)≤(e)) then orientedCount2 .rect (max ((2)*q+2) (e)) ((3)*q+(-1)) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect ((2)*q+2) ((3)*q+(-1)) (0:Int) (0:Int) (0:Int) (max ((2)*q+2) (e)) ((3)*q+(-1)) (0:Int) (0:Int) (event183 q e) (((5)≤(e)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect ((2)*q+2) ((3)*q+(-1)) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event183,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_183,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event184 (q e : Int) (p : Int×Int) : Prop := (((3)*q+1)≤e ∧ e≤((3)*q+1))
theorem atom184_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect ((2)*q+2) ((3)*q+(-1)) (0:Int) (0:Int) (0:Int)) (event184 q e)=
      Identity_left1_0.term_184 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect ((2)*q+2) ((3)*q+(-1)) (0:Int) (0:Int) (0:Int)) (event184 q e)=
      if (((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)) then orientedCount2 .rect ((2)*q+2) ((3)*q+(-1)) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect ((2)*q+2) ((3)*q+(-1)) (0:Int) (0:Int) (0:Int) ((2)*q+2) ((3)*q+(-1)) (0:Int) (0:Int) (event184 q e) ((((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect ((2)*q+2) ((3)*q+(-1)) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event184,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_184,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event185 (q e : Int) (p : Int×Int) : Prop := (((4)*q)≤e ∧ e≤((4)*q))
theorem atom185_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect ((2)*q+2) ((3)*q+(-1)) (0:Int) (0:Int) (0:Int)) (event185 q e)=
      Identity_left1_0.term_185 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect ((2)*q+2) ((3)*q+(-1)) (0:Int) (0:Int) (0:Int)) (event185 q e)=
      if (((4)*q)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect ((2)*q+2) ((3)*q+(-1)) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect ((2)*q+2) ((3)*q+(-1)) (0:Int) (0:Int) (0:Int) ((2)*q+2) ((3)*q+(-1)) (0:Int) (0:Int) (event185 q e) ((((4)*q)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect ((2)*q+2) ((3)*q+(-1)) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event185,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_185,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event186 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(p.1)) ∧ (((3)*q+1)≤e ∧ e≤((3)*q+1))
theorem atom186_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .rect ((2)*q+2) ((3)*q+(-1)) (0:Int) (0:Int) (0:Int)) (event186 q e)=
      Identity_left1_0.term_186 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect ((2)*q+2) ((3)*q+(-1)) (0:Int) (0:Int) (0:Int)) (event186 q e)=
      if ((5)≤(e) ∧ ((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)) then orientedCount2 .rect (max ((2)*q+2) (e)) ((3)*q+(-1)) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect ((2)*q+2) ((3)*q+(-1)) (0:Int) (0:Int) (0:Int) (max ((2)*q+2) (e)) ((3)*q+(-1)) (0:Int) (0:Int) (event186 q e) (((5)≤(e) ∧ ((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect ((2)*q+2) ((3)*q+(-1)) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event186,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_186,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event187 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(p.1)) ∧ (((4)*q)≤e ∧ e≤((4)*q))
theorem atom187_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .rect ((2)*q+2) ((3)*q+(-1)) (0:Int) (0:Int) (0:Int)) (event187 q e)=
      Identity_left1_0.term_187 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect ((2)*q+2) ((3)*q+(-1)) (0:Int) (0:Int) (0:Int)) (event187 q e)=
      if ((5)≤(e) ∧ ((4)*q)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect (max ((2)*q+2) (e)) ((3)*q+(-1)) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect ((2)*q+2) ((3)*q+(-1)) (0:Int) (0:Int) (0:Int) (max ((2)*q+2) (e)) ((3)*q+(-1)) (0:Int) (0:Int) (event187 q e) (((5)≤(e) ∧ ((4)*q)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect ((2)*q+2) ((3)*q+(-1)) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event187,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_187,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event188 (q e : Int) (p : Int×Int) : Prop := (((3)*q+1)≤e ∧ e≤((3)*q+1)) ∧ (((4)*q)≤e ∧ e≤((4)*q))
theorem atom188_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .rect ((2)*q+2) ((3)*q+(-1)) (0:Int) (0:Int) (0:Int)) (event188 q e)=
      Identity_left1_0.term_188 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect ((2)*q+2) ((3)*q+(-1)) (0:Int) (0:Int) (0:Int)) (event188 q e)=
      if (((3)*q+1)≤(e) ∧ (e)≤((3)*q+1) ∧ ((4)*q)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect ((2)*q+2) ((3)*q+(-1)) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect ((2)*q+2) ((3)*q+(-1)) (0:Int) (0:Int) (0:Int) ((2)*q+2) ((3)*q+(-1)) (0:Int) (0:Int) (event188 q e) ((((3)*q+1)≤(e) ∧ (e)≤((3)*q+1) ∧ ((4)*q)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect ((2)*q+2) ((3)*q+(-1)) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event188,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_188,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event189 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(p.1)) ∧ (((3)*q+1)≤e ∧ e≤((3)*q+1)) ∧ (((4)*q)≤e ∧ e≤((4)*q))
theorem atom189_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect ((2)*q+2) ((3)*q+(-1)) (0:Int) (0:Int) (0:Int)) (event189 q e)=
      Identity_left1_0.term_189 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect ((2)*q+2) ((3)*q+(-1)) (0:Int) (0:Int) (0:Int)) (event189 q e)=
      if ((5)≤(e) ∧ ((3)*q+1)≤(e) ∧ (e)≤((3)*q+1) ∧ ((4)*q)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect (max ((2)*q+2) (e)) ((3)*q+(-1)) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect ((2)*q+2) ((3)*q+(-1)) (0:Int) (0:Int) (0:Int) (max ((2)*q+2) (e)) ((3)*q+(-1)) (0:Int) (0:Int) (event189 q e) (((5)≤(e) ∧ ((3)*q+1)≤(e) ∧ (e)≤((3)*q+1) ∧ ((4)*q)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect ((2)*q+2) ((3)*q+(-1)) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event189,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_189,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event190 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(p.1))
theorem atom190_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect ((2)*q+2) ((3)*q) (0:Int) (0:Int) (0:Int)) (event190 q e)=
      Identity_left1_0.term_190 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect ((2)*q+2) ((3)*q) (0:Int) (0:Int) (0:Int)) (event190 q e)=
      if ((5)≤(e)) then orientedCount2 .rect (max ((2)*q+2) (e)) ((3)*q) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect ((2)*q+2) ((3)*q) (0:Int) (0:Int) (0:Int) (max ((2)*q+2) (e)) ((3)*q) (0:Int) (0:Int) (event190 q e) (((5)≤(e)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect ((2)*q+2) ((3)*q) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event190,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_190,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event191 (q e : Int) (p : Int×Int) : Prop := (((3)*q+2)≤e ∧ e≤((4)*q))
theorem atom191_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect ((2)*q+2) ((3)*q) (0:Int) (0:Int) (0:Int)) (event191 q e)=
      Identity_left1_0.term_191 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect ((2)*q+2) ((3)*q) (0:Int) (0:Int) (0:Int)) (event191 q e)=
      if (((3)*q+2)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect ((2)*q+2) ((3)*q) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect ((2)*q+2) ((3)*q) (0:Int) (0:Int) (0:Int) ((2)*q+2) ((3)*q) (0:Int) (0:Int) (event191 q e) ((((3)*q+2)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect ((2)*q+2) ((3)*q) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event191,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_191,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event192 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(p.1)) ∧ (((3)*q+2)≤e ∧ e≤((4)*q))
theorem atom192_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .rect ((2)*q+2) ((3)*q) (0:Int) (0:Int) (0:Int)) (event192 q e)=
      Identity_left1_0.term_192 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect ((2)*q+2) ((3)*q) (0:Int) (0:Int) (0:Int)) (event192 q e)=
      if ((5)≤(e) ∧ ((3)*q+2)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect (max ((2)*q+2) (e)) ((3)*q) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect ((2)*q+2) ((3)*q) (0:Int) (0:Int) (0:Int) (max ((2)*q+2) (e)) ((3)*q) (0:Int) (0:Int) (event192 q e) (((5)≤(e) ∧ ((3)*q+2)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect ((2)*q+2) ((3)*q) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event192,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_192,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event193 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(p.1))
theorem atom193_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect ((2)*q+2) ((3)*q+(-1)) (0:Int) (0:Int) (0:Int)) (event193 q e)=
      Identity_left1_0.term_193 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect ((2)*q+2) ((3)*q+(-1)) (0:Int) (0:Int) (0:Int)) (event193 q e)=
      if ((5)≤(e)) then orientedCount2 .rect (max ((2)*q+2) (e)) ((3)*q+(-1)) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect ((2)*q+2) ((3)*q+(-1)) (0:Int) (0:Int) (0:Int) (max ((2)*q+2) (e)) ((3)*q+(-1)) (0:Int) (0:Int) (event193 q e) (((5)≤(e)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect ((2)*q+2) ((3)*q+(-1)) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event193,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_193,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event194 (q e : Int) (p : Int×Int) : Prop := (((3)*q+1)≤e ∧ e≤((4)*q))
theorem atom194_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect ((2)*q+2) ((3)*q+(-1)) (0:Int) (0:Int) (0:Int)) (event194 q e)=
      Identity_left1_0.term_194 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect ((2)*q+2) ((3)*q+(-1)) (0:Int) (0:Int) (0:Int)) (event194 q e)=
      if (((3)*q+1)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect ((2)*q+2) ((3)*q+(-1)) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect ((2)*q+2) ((3)*q+(-1)) (0:Int) (0:Int) (0:Int) ((2)*q+2) ((3)*q+(-1)) (0:Int) (0:Int) (event194 q e) ((((3)*q+1)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect ((2)*q+2) ((3)*q+(-1)) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event194,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_194,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event195 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(p.1)) ∧ (((3)*q+1)≤e ∧ e≤((4)*q))
theorem atom195_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .rect ((2)*q+2) ((3)*q+(-1)) (0:Int) (0:Int) (0:Int)) (event195 q e)=
      Identity_left1_0.term_195 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect ((2)*q+2) ((3)*q+(-1)) (0:Int) (0:Int) (0:Int)) (event195 q e)=
      if ((5)≤(e) ∧ ((3)*q+1)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect (max ((2)*q+2) (e)) ((3)*q+(-1)) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect ((2)*q+2) ((3)*q+(-1)) (0:Int) (0:Int) (0:Int) (max ((2)*q+2) (e)) ((3)*q+(-1)) (0:Int) (0:Int) (event195 q e) (((5)≤(e) ∧ ((3)*q+1)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect ((2)*q+2) ((3)*q+(-1)) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event195,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_195,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
#print axioms atom150_count
#print axioms atom151_count
#print axioms atom152_count
#print axioms atom153_count
#print axioms atom154_count
#print axioms atom155_count
#print axioms atom156_count
#print axioms atom157_count
#print axioms atom158_count
#print axioms atom159_count
#print axioms atom160_count
#print axioms atom161_count
#print axioms atom162_count
#print axioms atom163_count
#print axioms atom164_count
#print axioms atom165_count
#print axioms atom166_count
#print axioms atom167_count
#print axioms atom168_count
#print axioms atom169_count
#print axioms atom170_count
#print axioms atom171_count
#print axioms atom172_count
#print axioms atom173_count
#print axioms atom174_count
#print axioms atom175_count
#print axioms atom176_count
#print axioms atom177_count
#print axioms atom178_count
#print axioms atom179_count
#print axioms atom180_count
#print axioms atom181_count
#print axioms atom182_count
#print axioms atom183_count
#print axioms atom184_count
#print axioms atom185_count
#print axioms atom186_count
#print axioms atom187_count
#print axioms atom188_count
#print axioms atom189_count
#print axioms atom190_count
#print axioms atom191_count
#print axioms atom192_count
#print axioms atom193_count
#print axioms atom194_count
#print axioms atom195_count
end
end LuRazLattice.AtomCounts
