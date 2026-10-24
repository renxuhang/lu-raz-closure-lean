import LatticeTally
import SpectrumIdentity_left1_0
namespace LuRazLattice.AtomCounts
set_option maxRecDepth 32768
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
noncomputable section
def event196 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤((2)*q))
theorem atom196_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event196 q e)=
      Identity_left1_0.term_196 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event196 q e)=
      if ((5)≤(e) ∧ (e)≤((2)*q)) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event196 q e) (((5)≤(e) ∧ (e)≤((2)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event196,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_196,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event197 (q e : Int) (p : Int×Int) : Prop := (((4)*q)≤e ∧ e≤((4)*q))
theorem atom197_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event197 q e)=
      Identity_left1_0.term_197 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event197 q e)=
      if (((4)*q)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event197 q e) ((((4)*q)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event197,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_197,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event198 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤((2)*q)) ∧ (((4)*q)≤e ∧ e≤((4)*q))
theorem atom198_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event198 q e)=
      Identity_left1_0.term_198 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event198 q e)=
      if ((5)≤(e) ∧ (e)≤((2)*q) ∧ ((4)*q)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event198 q e) (((5)≤(e) ∧ (e)≤((2)*q) ∧ ((4)*q)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event198,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_198,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event199 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤((2)*q))
theorem atom199_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event199 q e)=
      Identity_left1_0.term_199 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event199 q e)=
      if ((5)≤(e) ∧ (e)≤((2)*q)) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event199 q e) (((5)≤(e) ∧ (e)≤((2)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event199,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_199,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event200 (q e : Int) (p : Int×Int) : Prop := (((4)*q)≤e ∧ e≤((4)*q))
theorem atom200_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event200 q e)=
      Identity_left1_0.term_200 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event200 q e)=
      if (((4)*q)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event200 q e) ((((4)*q)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event200,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_200,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event201 (q e : Int) (p : Int×Int) : Prop := (((3)*q+2)≤e ∧ e≤((4)*q))
theorem atom201_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event201 q e)=
      Identity_left1_0.term_201 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event201 q e)=
      if (((3)*q+2)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event201 q e) ((((3)*q+2)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event201,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_201,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event202 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤((2)*q)) ∧ (((4)*q)≤e ∧ e≤((4)*q))
theorem atom202_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event202 q e)=
      Identity_left1_0.term_202 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event202 q e)=
      if ((5)≤(e) ∧ (e)≤((2)*q) ∧ ((4)*q)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event202 q e) (((5)≤(e) ∧ (e)≤((2)*q) ∧ ((4)*q)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event202,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_202,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event203 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤((2)*q)) ∧ (((3)*q+2)≤e ∧ e≤((4)*q))
theorem atom203_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event203 q e)=
      Identity_left1_0.term_203 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event203 q e)=
      if ((5)≤(e) ∧ (e)≤((2)*q) ∧ ((3)*q+2)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event203 q e) (((5)≤(e) ∧ (e)≤((2)*q) ∧ ((3)*q+2)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event203,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_203,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event204 (q e : Int) (p : Int×Int) : Prop := (((4)*q)≤e ∧ e≤((4)*q)) ∧ (((3)*q+2)≤e ∧ e≤((4)*q))
theorem atom204_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event204 q e)=
      Identity_left1_0.term_204 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event204 q e)=
      if (((4)*q)≤(e) ∧ (e)≤((4)*q) ∧ ((3)*q+2)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event204 q e) ((((4)*q)≤(e) ∧ (e)≤((4)*q) ∧ ((3)*q+2)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event204,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_204,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event205 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤((2)*q)) ∧ (((4)*q)≤e ∧ e≤((4)*q)) ∧ (((3)*q+2)≤e ∧ e≤((4)*q))
theorem atom205_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event205 q e)=
      Identity_left1_0.term_205 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event205 q e)=
      if ((5)≤(e) ∧ (e)≤((2)*q) ∧ ((4)*q)≤(e) ∧ (e)≤((4)*q) ∧ ((3)*q+2)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event205 q e) (((5)≤(e) ∧ (e)≤((2)*q) ∧ ((4)*q)≤(e) ∧ (e)≤((4)*q) ∧ ((3)*q+2)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event205,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_205,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event206 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤((2)*q))
theorem atom206_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event206 q e)=
      Identity_left1_0.term_206 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event206 q e)=
      if ((5)≤(e) ∧ (e)≤((2)*q)) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event206 q e) (((5)≤(e) ∧ (e)≤((2)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event206,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_206,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event207 (q e : Int) (p : Int×Int) : Prop := (((4)*q)≤e ∧ e≤((4)*q))
theorem atom207_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event207 q e)=
      Identity_left1_0.term_207 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event207 q e)=
      if (((4)*q)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event207 q e) ((((4)*q)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event207,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_207,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event208 (q e : Int) (p : Int×Int) : Prop := (((2)*q+3)≤e ∧ e≤((4)*q))
theorem atom208_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event208 q e)=
      Identity_left1_0.term_208 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event208 q e)=
      if (((2)*q+3)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event208 q e) ((((2)*q+3)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event208,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_208,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event209 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤((2)*q)) ∧ (((4)*q)≤e ∧ e≤((4)*q))
theorem atom209_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event209 q e)=
      Identity_left1_0.term_209 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event209 q e)=
      if ((5)≤(e) ∧ (e)≤((2)*q) ∧ ((4)*q)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event209 q e) (((5)≤(e) ∧ (e)≤((2)*q) ∧ ((4)*q)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event209,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_209,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event210 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤((2)*q)) ∧ (((2)*q+3)≤e ∧ e≤((4)*q))
theorem atom210_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event210 q e)=
      Identity_left1_0.term_210 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event210 q e)=
      if ((5)≤(e) ∧ (e)≤((2)*q) ∧ ((2)*q+3)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event210 q e) (((5)≤(e) ∧ (e)≤((2)*q) ∧ ((2)*q+3)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event210,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_210,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event211 (q e : Int) (p : Int×Int) : Prop := (((4)*q)≤e ∧ e≤((4)*q)) ∧ (((2)*q+3)≤e ∧ e≤((4)*q))
theorem atom211_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event211 q e)=
      Identity_left1_0.term_211 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event211 q e)=
      if (((4)*q)≤(e) ∧ (e)≤((4)*q) ∧ ((2)*q+3)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event211 q e) ((((4)*q)≤(e) ∧ (e)≤((4)*q) ∧ ((2)*q+3)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event211,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_211,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event212 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤((2)*q)) ∧ (((4)*q)≤e ∧ e≤((4)*q)) ∧ (((2)*q+3)≤e ∧ e≤((4)*q))
theorem atom212_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event212 q e)=
      Identity_left1_0.term_212 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event212 q e)=
      if ((5)≤(e) ∧ (e)≤((2)*q) ∧ ((4)*q)≤(e) ∧ (e)≤((4)*q) ∧ ((2)*q+3)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event212 q e) (((5)≤(e) ∧ (e)≤((2)*q) ∧ ((4)*q)≤(e) ∧ (e)≤((4)*q) ∧ ((2)*q+3)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event212,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_212,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event213 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(p.1))
theorem atom213_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (4) (q+1) ((2)*q+2) ((2)*q+3) (0:Int)) (event213 q e)=
      Identity_left1_0.term_213 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (4) (q+1) ((2)*q+2) ((2)*q+3) (0:Int)) (event213 q e)=
      if ((5)≤(e)) then orientedCount2 .rect (max (4) (e)) (q+1) ((2)*q+2) ((2)*q+3) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (4) (q+1) ((2)*q+2) ((2)*q+3) (0:Int) (max (4) (e)) (q+1) ((2)*q+2) ((2)*q+3) (event213 q e) (((5)≤(e)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (4) (q+1) ((2)*q+2) ((2)*q+3) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event213,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_213,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event214 (q e : Int) (p : Int×Int) : Prop := ((p.2)≤e ∧ e≤((4)*q))
theorem atom214_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (4) (q+1) ((2)*q+2) ((2)*q+3) (0:Int)) (event214 q e)=
      Identity_left1_0.term_214 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (4) (q+1) ((2)*q+2) ((2)*q+3) (0:Int)) (event214 q e)=
      if ((e)≤((4)*q)) then orientedCount2 .rect (4) (q+1) ((2)*q+2) (min ((2)*q+3) (e)) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (4) (q+1) ((2)*q+2) ((2)*q+3) (0:Int) (4) (q+1) ((2)*q+2) (min ((2)*q+3) (e)) (event214 q e) (((e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (4) (q+1) ((2)*q+2) ((2)*q+3) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event214,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_214,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event215 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(p.1)) ∧ ((p.2)≤e ∧ e≤((4)*q))
theorem atom215_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .rect (4) (q+1) ((2)*q+2) ((2)*q+3) (0:Int)) (event215 q e)=
      Identity_left1_0.term_215 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (4) (q+1) ((2)*q+2) ((2)*q+3) (0:Int)) (event215 q e)=
      if ((5)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect (max (4) (e)) (q+1) ((2)*q+2) (min ((2)*q+3) (e)) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (4) (q+1) ((2)*q+2) ((2)*q+3) (0:Int) (max (4) (e)) (q+1) ((2)*q+2) (min ((2)*q+3) (e)) (event215 q e) (((5)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (4) (q+1) ((2)*q+2) ((2)*q+3) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event215,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_215,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event216 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(p.1))
theorem atom216_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (q+3) ((2)*q+1) ((2)*q+2) ((2)*q+3) (0:Int)) (event216 q e)=
      Identity_left1_0.term_216 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (q+3) ((2)*q+1) ((2)*q+2) ((2)*q+3) (0:Int)) (event216 q e)=
      if ((5)≤(e)) then orientedCount2 .rect (max (q+3) (e)) ((2)*q+1) ((2)*q+2) ((2)*q+3) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (q+3) ((2)*q+1) ((2)*q+2) ((2)*q+3) (0:Int) (max (q+3) (e)) ((2)*q+1) ((2)*q+2) ((2)*q+3) (event216 q e) (((5)≤(e)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (q+3) ((2)*q+1) ((2)*q+2) ((2)*q+3) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event216,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_216,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event217 (q e : Int) (p : Int×Int) : Prop := ((p.2)≤e ∧ e≤((4)*q))
theorem atom217_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (q+3) ((2)*q+1) ((2)*q+2) ((2)*q+3) (0:Int)) (event217 q e)=
      Identity_left1_0.term_217 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (q+3) ((2)*q+1) ((2)*q+2) ((2)*q+3) (0:Int)) (event217 q e)=
      if ((e)≤((4)*q)) then orientedCount2 .rect (q+3) ((2)*q+1) ((2)*q+2) (min ((2)*q+3) (e)) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (q+3) ((2)*q+1) ((2)*q+2) ((2)*q+3) (0:Int) (q+3) ((2)*q+1) ((2)*q+2) (min ((2)*q+3) (e)) (event217 q e) (((e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (q+3) ((2)*q+1) ((2)*q+2) ((2)*q+3) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event217,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_217,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event218 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(p.1)) ∧ ((p.2)≤e ∧ e≤((4)*q))
theorem atom218_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .rect (q+3) ((2)*q+1) ((2)*q+2) ((2)*q+3) (0:Int)) (event218 q e)=
      Identity_left1_0.term_218 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (q+3) ((2)*q+1) ((2)*q+2) ((2)*q+3) (0:Int)) (event218 q e)=
      if ((5)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect (max (q+3) (e)) ((2)*q+1) ((2)*q+2) (min ((2)*q+3) (e)) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (q+3) ((2)*q+1) ((2)*q+2) ((2)*q+3) (0:Int) (max (q+3) (e)) ((2)*q+1) ((2)*q+2) (min ((2)*q+3) (e)) (event218 q e) (((5)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (q+3) ((2)*q+1) ((2)*q+2) ((2)*q+3) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event218,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_218,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event219 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(p.1))
theorem atom219_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (4) (q+1) (0:Int) (0:Int) (0:Int)) (event219 q e)=
      Identity_left1_0.term_219 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (4) (q+1) (0:Int) (0:Int) (0:Int)) (event219 q e)=
      if ((5)≤(e)) then orientedCount2 .rect (max (4) (e)) (q+1) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (4) (q+1) (0:Int) (0:Int) (0:Int) (max (4) (e)) (q+1) (0:Int) (0:Int) (event219 q e) (((5)≤(e)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (4) (q+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event219,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_219,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event220 (q e : Int) (p : Int×Int) : Prop := (((2)*q+1)≤e ∧ e≤((4)*q))
theorem atom220_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (4) (q+1) (0:Int) (0:Int) (0:Int)) (event220 q e)=
      Identity_left1_0.term_220 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (4) (q+1) (0:Int) (0:Int) (0:Int)) (event220 q e)=
      if (((2)*q+1)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect (4) (q+1) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (4) (q+1) (0:Int) (0:Int) (0:Int) (4) (q+1) (0:Int) (0:Int) (event220 q e) ((((2)*q+1)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (4) (q+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event220,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_220,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event221 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(p.1)) ∧ (((2)*q+1)≤e ∧ e≤((4)*q))
theorem atom221_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .rect (4) (q+1) (0:Int) (0:Int) (0:Int)) (event221 q e)=
      Identity_left1_0.term_221 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (4) (q+1) (0:Int) (0:Int) (0:Int)) (event221 q e)=
      if ((5)≤(e) ∧ ((2)*q+1)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect (max (4) (e)) (q+1) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (4) (q+1) (0:Int) (0:Int) (0:Int) (max (4) (e)) (q+1) (0:Int) (0:Int) (event221 q e) (((5)≤(e) ∧ ((2)*q+1)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (4) (q+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event221,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_221,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event222 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(p.1))
theorem atom222_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (q+3) ((2)*q+(-1)) (0:Int) (0:Int) (0:Int)) (event222 q e)=
      Identity_left1_0.term_222 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (q+3) ((2)*q+(-1)) (0:Int) (0:Int) (0:Int)) (event222 q e)=
      if ((5)≤(e)) then orientedCount2 .rect (max (q+3) (e)) ((2)*q+(-1)) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (q+3) ((2)*q+(-1)) (0:Int) (0:Int) (0:Int) (max (q+3) (e)) ((2)*q+(-1)) (0:Int) (0:Int) (event222 q e) (((5)≤(e)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (q+3) ((2)*q+(-1)) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event222,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_222,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event223 (q e : Int) (p : Int×Int) : Prop := (((2)*q+1)≤e ∧ e≤((4)*q))
theorem atom223_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (q+3) ((2)*q+(-1)) (0:Int) (0:Int) (0:Int)) (event223 q e)=
      Identity_left1_0.term_223 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (q+3) ((2)*q+(-1)) (0:Int) (0:Int) (0:Int)) (event223 q e)=
      if (((2)*q+1)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect (q+3) ((2)*q+(-1)) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (q+3) ((2)*q+(-1)) (0:Int) (0:Int) (0:Int) (q+3) ((2)*q+(-1)) (0:Int) (0:Int) (event223 q e) ((((2)*q+1)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (q+3) ((2)*q+(-1)) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event223,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_223,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event224 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(p.1)) ∧ (((2)*q+1)≤e ∧ e≤((4)*q))
theorem atom224_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .rect (q+3) ((2)*q+(-1)) (0:Int) (0:Int) (0:Int)) (event224 q e)=
      Identity_left1_0.term_224 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (q+3) ((2)*q+(-1)) (0:Int) (0:Int) (0:Int)) (event224 q e)=
      if ((5)≤(e) ∧ ((2)*q+1)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect (max (q+3) (e)) ((2)*q+(-1)) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (q+3) ((2)*q+(-1)) (0:Int) (0:Int) (0:Int) (max (q+3) (e)) ((2)*q+(-1)) (0:Int) (0:Int) (event224 q e) (((5)≤(e) ∧ ((2)*q+1)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (q+3) ((2)*q+(-1)) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event224,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_224,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event225 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(q+3))
theorem atom225_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect ((2)*q+2) ((2)*q+3) (0:Int) (0:Int) (0:Int)) (event225 q e)=
      Identity_left1_0.term_225 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect ((2)*q+2) ((2)*q+3) (0:Int) (0:Int) (0:Int)) (event225 q e)=
      if ((5)≤(e) ∧ (e)≤(q+3)) then orientedCount2 .rect ((2)*q+2) ((2)*q+3) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect ((2)*q+2) ((2)*q+3) (0:Int) (0:Int) (0:Int) ((2)*q+2) ((2)*q+3) (0:Int) (0:Int) (event225 q e) (((5)≤(e) ∧ (e)≤(q+3)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect ((2)*q+2) ((2)*q+3) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event225,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_225,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event226 (q e : Int) (p : Int×Int) : Prop := ((p.1)≤e ∧ e≤((4)*q+(-1)))
theorem atom226_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect ((2)*q+2) ((2)*q+3) (0:Int) (0:Int) (0:Int)) (event226 q e)=
      Identity_left1_0.term_226 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect ((2)*q+2) ((2)*q+3) (0:Int) (0:Int) (0:Int)) (event226 q e)=
      if ((e)≤((4)*q+(-1))) then orientedCount2 .rect ((2)*q+2) (min ((2)*q+3) (e)) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect ((2)*q+2) ((2)*q+3) (0:Int) (0:Int) (0:Int) ((2)*q+2) (min ((2)*q+3) (e)) (0:Int) (0:Int) (event226 q e) (((e)≤((4)*q+(-1))))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect ((2)*q+2) ((2)*q+3) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event226,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_226,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event227 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(q+3)) ∧ ((p.1)≤e ∧ e≤((4)*q+(-1)))
theorem atom227_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .rect ((2)*q+2) ((2)*q+3) (0:Int) (0:Int) (0:Int)) (event227 q e)=
      Identity_left1_0.term_227 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect ((2)*q+2) ((2)*q+3) (0:Int) (0:Int) (0:Int)) (event227 q e)=
      if ((5)≤(e) ∧ (e)≤(q+3) ∧ (e)≤((4)*q+(-1))) then orientedCount2 .rect ((2)*q+2) (min ((2)*q+3) (e)) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect ((2)*q+2) ((2)*q+3) (0:Int) (0:Int) (0:Int) ((2)*q+2) (min ((2)*q+3) (e)) (0:Int) (0:Int) (event227 q e) (((5)≤(e) ∧ (e)≤(q+3) ∧ (e)≤((4)*q+(-1))))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect ((2)*q+2) ((2)*q+3) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event227,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_227,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event228 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(p.1))
theorem atom228_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect ((4)*q+(-2)) ((4)*q+(-1)) (0:Int) (0:Int) (0:Int)) (event228 q e)=
      Identity_left1_0.term_228 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect ((4)*q+(-2)) ((4)*q+(-1)) (0:Int) (0:Int) (0:Int)) (event228 q e)=
      if ((5)≤(e)) then orientedCount2 .rect (max ((4)*q+(-2)) (e)) ((4)*q+(-1)) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect ((4)*q+(-2)) ((4)*q+(-1)) (0:Int) (0:Int) (0:Int) (max ((4)*q+(-2)) (e)) ((4)*q+(-1)) (0:Int) (0:Int) (event228 q e) (((5)≤(e)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect ((4)*q+(-2)) ((4)*q+(-1)) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event228,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_228,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event229 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤((4)*q+(-2)))
theorem atom229_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event229 q e)=
      Identity_left1_0.term_229 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event229 q e)=
      if ((5)≤(e) ∧ (e)≤((4)*q+(-2))) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event229 q e) (((5)≤(e) ∧ (e)≤((4)*q+(-2))))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event229,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_229,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event230 (q e : Int) (p : Int×Int) : Prop := (((4)*q)≤e ∧ e≤((4)*q))
theorem atom230_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event230 q e)=
      Identity_left1_0.term_230 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event230 q e)=
      if (((4)*q)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event230 q e) ((((4)*q)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event230,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_230,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event231 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤((4)*q+(-2))) ∧ (((4)*q)≤e ∧ e≤((4)*q))
theorem atom231_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event231 q e)=
      Identity_left1_0.term_231 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event231 q e)=
      if ((5)≤(e) ∧ (e)≤((4)*q+(-2)) ∧ ((4)*q)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event231 q e) (((5)≤(e) ∧ (e)≤((4)*q+(-2)) ∧ ((4)*q)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event231,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_231,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event232 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(p.1))
theorem atom232_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect ((4)*q+(-2)) ((4)*q+(-1)) (0:Int) (0:Int) (0:Int)) (event232 q e)=
      Identity_left1_0.term_232 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect ((4)*q+(-2)) ((4)*q+(-1)) (0:Int) (0:Int) (0:Int)) (event232 q e)=
      if ((5)≤(e)) then orientedCount2 .rect (max ((4)*q+(-2)) (e)) ((4)*q+(-1)) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect ((4)*q+(-2)) ((4)*q+(-1)) (0:Int) (0:Int) (0:Int) (max ((4)*q+(-2)) (e)) ((4)*q+(-1)) (0:Int) (0:Int) (event232 q e) (((5)≤(e)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect ((4)*q+(-2)) ((4)*q+(-1)) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event232,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_232,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event233 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(p.1))
theorem atom233_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect ((2)*q+2) ((3)*q) (0:Int) (0:Int) (0:Int)) (event233 q e)=
      Identity_left1_0.term_233 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect ((2)*q+2) ((3)*q) (0:Int) (0:Int) (0:Int)) (event233 q e)=
      if ((5)≤(e)) then orientedCount2 .rect (max ((2)*q+2) (e)) ((3)*q) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect ((2)*q+2) ((3)*q) (0:Int) (0:Int) (0:Int) (max ((2)*q+2) (e)) ((3)*q) (0:Int) (0:Int) (event233 q e) (((5)≤(e)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect ((2)*q+2) ((3)*q) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event233,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_233,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event234 (q e : Int) (p : Int×Int) : Prop := (((3)*q+2)≤e ∧ e≤((4)*q+(-1)))
theorem atom234_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect ((2)*q+2) ((3)*q) (0:Int) (0:Int) (0:Int)) (event234 q e)=
      Identity_left1_0.term_234 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect ((2)*q+2) ((3)*q) (0:Int) (0:Int) (0:Int)) (event234 q e)=
      if (((3)*q+2)≤(e) ∧ (e)≤((4)*q+(-1))) then orientedCount2 .rect ((2)*q+2) ((3)*q) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect ((2)*q+2) ((3)*q) (0:Int) (0:Int) (0:Int) ((2)*q+2) ((3)*q) (0:Int) (0:Int) (event234 q e) ((((3)*q+2)≤(e) ∧ (e)≤((4)*q+(-1))))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect ((2)*q+2) ((3)*q) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event234,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_234,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event235 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(p.1)) ∧ (((3)*q+2)≤e ∧ e≤((4)*q+(-1)))
theorem atom235_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .rect ((2)*q+2) ((3)*q) (0:Int) (0:Int) (0:Int)) (event235 q e)=
      Identity_left1_0.term_235 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect ((2)*q+2) ((3)*q) (0:Int) (0:Int) (0:Int)) (event235 q e)=
      if ((5)≤(e) ∧ ((3)*q+2)≤(e) ∧ (e)≤((4)*q+(-1))) then orientedCount2 .rect (max ((2)*q+2) (e)) ((3)*q) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect ((2)*q+2) ((3)*q) (0:Int) (0:Int) (0:Int) (max ((2)*q+2) (e)) ((3)*q) (0:Int) (0:Int) (event235 q e) (((5)≤(e) ∧ ((3)*q+2)≤(e) ∧ (e)≤((4)*q+(-1))))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect ((2)*q+2) ((3)*q) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event235,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_235,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event236 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(q+3))
theorem atom236_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (q+5) ((2)*q+1) (0:Int) (0:Int) (0:Int)) (event236 q e)=
      Identity_left1_0.term_236 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (q+5) ((2)*q+1) (0:Int) (0:Int) (0:Int)) (event236 q e)=
      if ((5)≤(e) ∧ (e)≤(q+3)) then orientedCount2 .rect (q+5) ((2)*q+1) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (q+5) ((2)*q+1) (0:Int) (0:Int) (0:Int) (q+5) ((2)*q+1) (0:Int) (0:Int) (event236 q e) (((5)≤(e) ∧ (e)≤(q+3)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (q+5) ((2)*q+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event236,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_236,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event237 (q e : Int) (p : Int×Int) : Prop := ((p.1)≤e ∧ e≤((4)*q+(-1)))
theorem atom237_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (q+5) ((2)*q+1) (0:Int) (0:Int) (0:Int)) (event237 q e)=
      Identity_left1_0.term_237 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (q+5) ((2)*q+1) (0:Int) (0:Int) (0:Int)) (event237 q e)=
      if ((e)≤((4)*q+(-1))) then orientedCount2 .rect (q+5) (min ((2)*q+1) (e)) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (q+5) ((2)*q+1) (0:Int) (0:Int) (0:Int) (q+5) (min ((2)*q+1) (e)) (0:Int) (0:Int) (event237 q e) (((e)≤((4)*q+(-1))))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (q+5) ((2)*q+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event237,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_237,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event238 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(q+3)) ∧ ((p.1)≤e ∧ e≤((4)*q+(-1)))
theorem atom238_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .rect (q+5) ((2)*q+1) (0:Int) (0:Int) (0:Int)) (event238 q e)=
      Identity_left1_0.term_238 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (q+5) ((2)*q+1) (0:Int) (0:Int) (0:Int)) (event238 q e)=
      if ((5)≤(e) ∧ (e)≤(q+3) ∧ (e)≤((4)*q+(-1))) then orientedCount2 .rect (q+5) (min ((2)*q+1) (e)) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (q+5) ((2)*q+1) (0:Int) (0:Int) (0:Int) (q+5) (min ((2)*q+1) (e)) (0:Int) (0:Int) (event238 q e) (((5)≤(e) ∧ (e)≤(q+3) ∧ (e)≤((4)*q+(-1))))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (q+5) ((2)*q+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event238,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_238,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event239 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(q+3))
theorem atom239_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect ((2)*q+2) ((2)*q+3) (0:Int) (0:Int) (0:Int)) (event239 q e)=
      Identity_left1_0.term_239 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect ((2)*q+2) ((2)*q+3) (0:Int) (0:Int) (0:Int)) (event239 q e)=
      if ((5)≤(e) ∧ (e)≤(q+3)) then orientedCount2 .rect ((2)*q+2) ((2)*q+3) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect ((2)*q+2) ((2)*q+3) (0:Int) (0:Int) (0:Int) ((2)*q+2) ((2)*q+3) (0:Int) (0:Int) (event239 q e) (((5)≤(e) ∧ (e)≤(q+3)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect ((2)*q+2) ((2)*q+3) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event239,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_239,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event240 (q e : Int) (p : Int×Int) : Prop := ((p.1)≤e ∧ e≤((4)*q+(-1)))
theorem atom240_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect ((2)*q+2) ((2)*q+3) (0:Int) (0:Int) (0:Int)) (event240 q e)=
      Identity_left1_0.term_240 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect ((2)*q+2) ((2)*q+3) (0:Int) (0:Int) (0:Int)) (event240 q e)=
      if ((e)≤((4)*q+(-1))) then orientedCount2 .rect ((2)*q+2) (min ((2)*q+3) (e)) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect ((2)*q+2) ((2)*q+3) (0:Int) (0:Int) (0:Int) ((2)*q+2) (min ((2)*q+3) (e)) (0:Int) (0:Int) (event240 q e) (((e)≤((4)*q+(-1))))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect ((2)*q+2) ((2)*q+3) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event240,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_240,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event241 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(q+3)) ∧ ((p.1)≤e ∧ e≤((4)*q+(-1)))
theorem atom241_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .rect ((2)*q+2) ((2)*q+3) (0:Int) (0:Int) (0:Int)) (event241 q e)=
      Identity_left1_0.term_241 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect ((2)*q+2) ((2)*q+3) (0:Int) (0:Int) (0:Int)) (event241 q e)=
      if ((5)≤(e) ∧ (e)≤(q+3) ∧ (e)≤((4)*q+(-1))) then orientedCount2 .rect ((2)*q+2) (min ((2)*q+3) (e)) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect ((2)*q+2) ((2)*q+3) (0:Int) (0:Int) (0:Int) ((2)*q+2) (min ((2)*q+3) (e)) (0:Int) (0:Int) (event241 q e) (((5)≤(e) ∧ (e)≤(q+3) ∧ (e)≤((4)*q+(-1))))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect ((2)*q+2) ((2)*q+3) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event241,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_241,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
#print axioms atom196_count
#print axioms atom197_count
#print axioms atom198_count
#print axioms atom199_count
#print axioms atom200_count
#print axioms atom201_count
#print axioms atom202_count
#print axioms atom203_count
#print axioms atom204_count
#print axioms atom205_count
#print axioms atom206_count
#print axioms atom207_count
#print axioms atom208_count
#print axioms atom209_count
#print axioms atom210_count
#print axioms atom211_count
#print axioms atom212_count
#print axioms atom213_count
#print axioms atom214_count
#print axioms atom215_count
#print axioms atom216_count
#print axioms atom217_count
#print axioms atom218_count
#print axioms atom219_count
#print axioms atom220_count
#print axioms atom221_count
#print axioms atom222_count
#print axioms atom223_count
#print axioms atom224_count
#print axioms atom225_count
#print axioms atom226_count
#print axioms atom227_count
#print axioms atom228_count
#print axioms atom229_count
#print axioms atom230_count
#print axioms atom231_count
#print axioms atom232_count
#print axioms atom233_count
#print axioms atom234_count
#print axioms atom235_count
#print axioms atom236_count
#print axioms atom237_count
#print axioms atom238_count
#print axioms atom239_count
#print axioms atom240_count
#print axioms atom241_count
end
end LuRazLattice.AtomCounts
