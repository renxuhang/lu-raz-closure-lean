import LatticeTally
import SpectrumIdentity_left1_0
namespace LuRazLattice.AtomCounts
set_option maxRecDepth 32768
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
noncomputable section
def event242 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(p.1))
theorem atom242_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect ((2)*q+2) ((3)*q+(-1)) (0:Int) (0:Int) (0:Int)) (event242 q e)=
      Identity_left1_0.term_242 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect ((2)*q+2) ((3)*q+(-1)) (0:Int) (0:Int) (0:Int)) (event242 q e)=
      if ((5)≤(e)) then orientedCount2 .rect (max ((2)*q+2) (e)) ((3)*q+(-1)) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect ((2)*q+2) ((3)*q+(-1)) (0:Int) (0:Int) (0:Int) (max ((2)*q+2) (e)) ((3)*q+(-1)) (0:Int) (0:Int) (event242 q e) (((5)≤(e)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect ((2)*q+2) ((3)*q+(-1)) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event242,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_242,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event243 (q e : Int) (p : Int×Int) : Prop := (((3)*q+1)≤e ∧ e≤((4)*q+(-1)))
theorem atom243_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect ((2)*q+2) ((3)*q+(-1)) (0:Int) (0:Int) (0:Int)) (event243 q e)=
      Identity_left1_0.term_243 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect ((2)*q+2) ((3)*q+(-1)) (0:Int) (0:Int) (0:Int)) (event243 q e)=
      if (((3)*q+1)≤(e) ∧ (e)≤((4)*q+(-1))) then orientedCount2 .rect ((2)*q+2) ((3)*q+(-1)) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect ((2)*q+2) ((3)*q+(-1)) (0:Int) (0:Int) (0:Int) ((2)*q+2) ((3)*q+(-1)) (0:Int) (0:Int) (event243 q e) ((((3)*q+1)≤(e) ∧ (e)≤((4)*q+(-1))))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect ((2)*q+2) ((3)*q+(-1)) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event243,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_243,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event244 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(p.1)) ∧ (((3)*q+1)≤e ∧ e≤((4)*q+(-1)))
theorem atom244_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .rect ((2)*q+2) ((3)*q+(-1)) (0:Int) (0:Int) (0:Int)) (event244 q e)=
      Identity_left1_0.term_244 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect ((2)*q+2) ((3)*q+(-1)) (0:Int) (0:Int) (0:Int)) (event244 q e)=
      if ((5)≤(e) ∧ ((3)*q+1)≤(e) ∧ (e)≤((4)*q+(-1))) then orientedCount2 .rect (max ((2)*q+2) (e)) ((3)*q+(-1)) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect ((2)*q+2) ((3)*q+(-1)) (0:Int) (0:Int) (0:Int) (max ((2)*q+2) (e)) ((3)*q+(-1)) (0:Int) (0:Int) (event244 q e) (((5)≤(e) ∧ ((3)*q+1)≤(e) ∧ (e)≤((4)*q+(-1))))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect ((2)*q+2) ((3)*q+(-1)) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event244,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_244,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event245 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(p.1))
theorem atom245_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (4) ((2)*q) ((2)*q+2) ((2)*q+3) (0:Int)) (event245 q e)=
      Identity_left1_0.term_245 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (4) ((2)*q) ((2)*q+2) ((2)*q+3) (0:Int)) (event245 q e)=
      if ((5)≤(e)) then orientedCount2 .rect (max (4) (e)) ((2)*q) ((2)*q+2) ((2)*q+3) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (4) ((2)*q) ((2)*q+2) ((2)*q+3) (0:Int) (max (4) (e)) ((2)*q) ((2)*q+2) ((2)*q+3) (event245 q e) (((5)≤(e)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (4) ((2)*q) ((2)*q+2) ((2)*q+3) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event245,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_245,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event246 (q e : Int) (p : Int×Int) : Prop := ((p.2)≤e ∧ e≤((4)*q))
theorem atom246_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (4) ((2)*q) ((2)*q+2) ((2)*q+3) (0:Int)) (event246 q e)=
      Identity_left1_0.term_246 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (4) ((2)*q) ((2)*q+2) ((2)*q+3) (0:Int)) (event246 q e)=
      if ((e)≤((4)*q)) then orientedCount2 .rect (4) ((2)*q) ((2)*q+2) (min ((2)*q+3) (e)) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (4) ((2)*q) ((2)*q+2) ((2)*q+3) (0:Int) (4) ((2)*q) ((2)*q+2) (min ((2)*q+3) (e)) (event246 q e) (((e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (4) ((2)*q) ((2)*q+2) ((2)*q+3) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event246,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_246,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event247 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(p.1)) ∧ ((p.2)≤e ∧ e≤((4)*q))
theorem atom247_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .rect (4) ((2)*q) ((2)*q+2) ((2)*q+3) (0:Int)) (event247 q e)=
      Identity_left1_0.term_247 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (4) ((2)*q) ((2)*q+2) ((2)*q+3) (0:Int)) (event247 q e)=
      if ((5)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect (max (4) (e)) ((2)*q) ((2)*q+2) (min ((2)*q+3) (e)) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (4) ((2)*q) ((2)*q+2) ((2)*q+3) (0:Int) (max (4) (e)) ((2)*q) ((2)*q+2) (min ((2)*q+3) (e)) (event247 q e) (((5)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (4) ((2)*q) ((2)*q+2) ((2)*q+3) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event247,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_247,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event248 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤((2)*q))
theorem atom248_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect ((2)*q+4) ((4)*q+(-1)) (0:Int) (0:Int) (0:Int)) (event248 q e)=
      Identity_left1_0.term_248 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect ((2)*q+4) ((4)*q+(-1)) (0:Int) (0:Int) (0:Int)) (event248 q e)=
      if ((5)≤(e) ∧ (e)≤((2)*q)) then orientedCount2 .rect ((2)*q+4) ((4)*q+(-1)) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect ((2)*q+4) ((4)*q+(-1)) (0:Int) (0:Int) (0:Int) ((2)*q+4) ((4)*q+(-1)) (0:Int) (0:Int) (event248 q e) (((5)≤(e) ∧ (e)≤((2)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect ((2)*q+4) ((4)*q+(-1)) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event248,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_248,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event249 (q e : Int) (p : Int×Int) : Prop := ((p.1)≤e ∧ e≤((4)*q))
theorem atom249_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect ((2)*q+4) ((4)*q+(-1)) (0:Int) (0:Int) (0:Int)) (event249 q e)=
      Identity_left1_0.term_249 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect ((2)*q+4) ((4)*q+(-1)) (0:Int) (0:Int) (0:Int)) (event249 q e)=
      if ((e)≤((4)*q)) then orientedCount2 .rect ((2)*q+4) (min ((4)*q+(-1)) (e)) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect ((2)*q+4) ((4)*q+(-1)) (0:Int) (0:Int) (0:Int) ((2)*q+4) (min ((4)*q+(-1)) (e)) (0:Int) (0:Int) (event249 q e) (((e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect ((2)*q+4) ((4)*q+(-1)) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event249,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_249,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event250 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤((2)*q)) ∧ ((p.1)≤e ∧ e≤((4)*q))
theorem atom250_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .rect ((2)*q+4) ((4)*q+(-1)) (0:Int) (0:Int) (0:Int)) (event250 q e)=
      Identity_left1_0.term_250 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect ((2)*q+4) ((4)*q+(-1)) (0:Int) (0:Int) (0:Int)) (event250 q e)=
      if ((5)≤(e) ∧ (e)≤((2)*q) ∧ (e)≤((4)*q)) then orientedCount2 .rect ((2)*q+4) (min ((4)*q+(-1)) (e)) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect ((2)*q+4) ((4)*q+(-1)) (0:Int) (0:Int) (0:Int) ((2)*q+4) (min ((4)*q+(-1)) (e)) (0:Int) (0:Int) (event250 q e) (((5)≤(e) ∧ (e)≤((2)*q) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect ((2)*q+4) ((4)*q+(-1)) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event250,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_250,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event251 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤((2)*q))
theorem atom251_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event251 q e)=
      Identity_left1_0.term_251 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event251 q e)=
      if ((5)≤(e) ∧ (e)≤((2)*q)) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event251 q e) (((5)≤(e) ∧ (e)≤((2)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event251,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_251,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event252 (q e : Int) (p : Int×Int) : Prop := (((2)*q+2)≤e ∧ e≤((4)*q+(-2)))
theorem atom252_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event252 q e)=
      Identity_left1_0.term_252 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event252 q e)=
      if (((2)*q+2)≤(e) ∧ (e)≤((4)*q+(-2))) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event252 q e) ((((2)*q+2)≤(e) ∧ (e)≤((4)*q+(-2))))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event252,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_252,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event253 (q e : Int) (p : Int×Int) : Prop := (((4)*q)≤e ∧ e≤((4)*q))
theorem atom253_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event253 q e)=
      Identity_left1_0.term_253 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event253 q e)=
      if (((4)*q)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event253 q e) ((((4)*q)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event253,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_253,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event254 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤((2)*q)) ∧ (((2)*q+2)≤e ∧ e≤((4)*q+(-2)))
theorem atom254_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event254 q e)=
      Identity_left1_0.term_254 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event254 q e)=
      if ((5)≤(e) ∧ (e)≤((2)*q) ∧ ((2)*q+2)≤(e) ∧ (e)≤((4)*q+(-2))) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event254 q e) (((5)≤(e) ∧ (e)≤((2)*q) ∧ ((2)*q+2)≤(e) ∧ (e)≤((4)*q+(-2))))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event254,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_254,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event255 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤((2)*q)) ∧ (((4)*q)≤e ∧ e≤((4)*q))
theorem atom255_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event255 q e)=
      Identity_left1_0.term_255 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event255 q e)=
      if ((5)≤(e) ∧ (e)≤((2)*q) ∧ ((4)*q)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event255 q e) (((5)≤(e) ∧ (e)≤((2)*q) ∧ ((4)*q)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event255,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_255,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event256 (q e : Int) (p : Int×Int) : Prop := (((2)*q+2)≤e ∧ e≤((4)*q+(-2))) ∧ (((4)*q)≤e ∧ e≤((4)*q))
theorem atom256_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event256 q e)=
      Identity_left1_0.term_256 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event256 q e)=
      if (((2)*q+2)≤(e) ∧ (e)≤((4)*q+(-2)) ∧ ((4)*q)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event256 q e) ((((2)*q+2)≤(e) ∧ (e)≤((4)*q+(-2)) ∧ ((4)*q)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event256,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_256,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event257 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤((2)*q)) ∧ (((2)*q+2)≤e ∧ e≤((4)*q+(-2))) ∧ (((4)*q)≤e ∧ e≤((4)*q))
theorem atom257_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event257 q e)=
      Identity_left1_0.term_257 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event257 q e)=
      if ((5)≤(e) ∧ (e)≤((2)*q) ∧ ((2)*q+2)≤(e) ∧ (e)≤((4)*q+(-2)) ∧ ((4)*q)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event257 q e) (((5)≤(e) ∧ (e)≤((2)*q) ∧ ((2)*q+2)≤(e) ∧ (e)≤((4)*q+(-2)) ∧ ((4)*q)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event257,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_257,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event258 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤((2)*q+1))
theorem atom258_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect ((2)*q+3) ((4)*q) (0:Int) (0:Int) (0:Int)) (event258 q e)=
      Identity_left1_0.term_258 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect ((2)*q+3) ((4)*q) (0:Int) (0:Int) (0:Int)) (event258 q e)=
      if ((5)≤(e) ∧ (e)≤((2)*q+1)) then orientedCount2 .rect ((2)*q+3) ((4)*q) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect ((2)*q+3) ((4)*q) (0:Int) (0:Int) (0:Int) ((2)*q+3) ((4)*q) (0:Int) (0:Int) (event258 q e) (((5)≤(e) ∧ (e)≤((2)*q+1)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect ((2)*q+3) ((4)*q) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event258,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_258,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event259 (q e : Int) (p : Int×Int) : Prop := ((p.1)≤e ∧ e≤((4)*q))
theorem atom259_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect ((2)*q+3) ((4)*q) (0:Int) (0:Int) (0:Int)) (event259 q e)=
      Identity_left1_0.term_259 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect ((2)*q+3) ((4)*q) (0:Int) (0:Int) (0:Int)) (event259 q e)=
      if ((e)≤((4)*q)) then orientedCount2 .rect ((2)*q+3) (min ((4)*q) (e)) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect ((2)*q+3) ((4)*q) (0:Int) (0:Int) (0:Int) ((2)*q+3) (min ((4)*q) (e)) (0:Int) (0:Int) (event259 q e) (((e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect ((2)*q+3) ((4)*q) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event259,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_259,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event260 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤((2)*q+1)) ∧ ((p.1)≤e ∧ e≤((4)*q))
theorem atom260_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .rect ((2)*q+3) ((4)*q) (0:Int) (0:Int) (0:Int)) (event260 q e)=
      Identity_left1_0.term_260 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect ((2)*q+3) ((4)*q) (0:Int) (0:Int) (0:Int)) (event260 q e)=
      if ((5)≤(e) ∧ (e)≤((2)*q+1) ∧ (e)≤((4)*q)) then orientedCount2 .rect ((2)*q+3) (min ((4)*q) (e)) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect ((2)*q+3) ((4)*q) (0:Int) (0:Int) (0:Int) ((2)*q+3) (min ((4)*q) (e)) (0:Int) (0:Int) (event260 q e) (((5)≤(e) ∧ (e)≤((2)*q+1) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect ((2)*q+3) ((4)*q) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event260,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_260,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event261 (q e : Int) (p : Int×Int) : Prop := ((p.1)≤e ∧ e≤((4)*q))
theorem atom261_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (6) ((2)*q+1) (0:Int) (0:Int) (0:Int)) (event261 q e)=
      Identity_left1_0.term_261 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (6) ((2)*q+1) (0:Int) (0:Int) (0:Int)) (event261 q e)=
      if ((e)≤((4)*q)) then orientedCount2 .rect (6) (min ((2)*q+1) (e)) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (6) ((2)*q+1) (0:Int) (0:Int) (0:Int) (6) (min ((2)*q+1) (e)) (0:Int) (0:Int) (event261 q e) (((e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (6) ((2)*q+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event261,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_261,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event262 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(p.1))
theorem atom262_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .lower (5) ((2)*q+(-1)) (0:Int) ((2)*q+1) (2)) (event262 q e)=
      Identity_left1_0.term_262 q e := by
  classical
  have hc : 2*tally (orientedPoints .lower (5) ((2)*q+(-1)) (0:Int) ((2)*q+1) (2)) (event262 q e)=
      if ((5)≤(e)) then orientedCount2 .lower (max (5) (e)) ((2)*q+(-1)) (0:Int) ((2)*q+1) (2) else 0 := by
    apply tally_oriented_predicate .lower (5) ((2)*q+(-1)) (0:Int) ((2)*q+1) (2) (max (5) (e)) ((2)*q+(-1)) (0:Int) ((2)*q+1) (event262 q e) (((5)≤(e)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .lower (5) ((2)*q+(-1)) (0:Int) ((2)*q+1) (2) p.1 p.2).mp hp
      simp at hb
      simp only [event262,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_262,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event263 (q e : Int) (p : Int×Int) : Prop := ((p.2)≤e ∧ e≤((4)*q))
theorem atom263_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .lower (5) ((2)*q+(-1)) (0:Int) ((2)*q+1) (2)) (event263 q e)=
      Identity_left1_0.term_263 q e := by
  classical
  have hc : 2*tally (orientedPoints .lower (5) ((2)*q+(-1)) (0:Int) ((2)*q+1) (2)) (event263 q e)=
      if ((e)≤((4)*q)) then orientedCount2 .lower (5) ((2)*q+(-1)) (0:Int) (min ((2)*q+1) (e)) (2) else 0 := by
    apply tally_oriented_predicate .lower (5) ((2)*q+(-1)) (0:Int) ((2)*q+1) (2) (5) ((2)*q+(-1)) (0:Int) (min ((2)*q+1) (e)) (event263 q e) (((e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .lower (5) ((2)*q+(-1)) (0:Int) ((2)*q+1) (2) p.1 p.2).mp hp
      simp at hb
      simp only [event263,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_263,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event264 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(p.1)) ∧ ((p.2)≤e ∧ e≤((4)*q))
theorem atom264_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .lower (5) ((2)*q+(-1)) (0:Int) ((2)*q+1) (2)) (event264 q e)=
      Identity_left1_0.term_264 q e := by
  classical
  have hc : 2*tally (orientedPoints .lower (5) ((2)*q+(-1)) (0:Int) ((2)*q+1) (2)) (event264 q e)=
      if ((5)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .lower (max (5) (e)) ((2)*q+(-1)) (0:Int) (min ((2)*q+1) (e)) (2) else 0 := by
    apply tally_oriented_predicate .lower (5) ((2)*q+(-1)) (0:Int) ((2)*q+1) (2) (max (5) (e)) ((2)*q+(-1)) (0:Int) (min ((2)*q+1) (e)) (event264 q e) (((5)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .lower (5) ((2)*q+(-1)) (0:Int) ((2)*q+1) (2) p.1 p.2).mp hp
      simp at hb
      simp only [event264,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_264,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event265 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤((4)*q))
theorem atom265_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event265 q e)=
      Identity_left1_0.term_265 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event265 q e)=
      if ((5)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event265 q e) (((5)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event265,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_265,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event266 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(p.1))
theorem atom266_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .lower ((2)*q+2) ((4)*q+(-2)) (0:Int) ((4)*q) (2)) (event266 q e)=
      Identity_left1_0.term_266 q e := by
  classical
  have hc : 2*tally (orientedPoints .lower ((2)*q+2) ((4)*q+(-2)) (0:Int) ((4)*q) (2)) (event266 q e)=
      if ((5)≤(e)) then orientedCount2 .lower (max ((2)*q+2) (e)) ((4)*q+(-2)) (0:Int) ((4)*q) (2) else 0 := by
    apply tally_oriented_predicate .lower ((2)*q+2) ((4)*q+(-2)) (0:Int) ((4)*q) (2) (max ((2)*q+2) (e)) ((4)*q+(-2)) (0:Int) ((4)*q) (event266 q e) (((5)≤(e)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .lower ((2)*q+2) ((4)*q+(-2)) (0:Int) ((4)*q) (2) p.1 p.2).mp hp
      simp at hb
      simp only [event266,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_266,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event267 (q e : Int) (p : Int×Int) : Prop := ((p.2)≤e ∧ e≤((4)*q))
theorem atom267_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .lower ((2)*q+2) ((4)*q+(-2)) (0:Int) ((4)*q) (2)) (event267 q e)=
      Identity_left1_0.term_267 q e := by
  classical
  have hc : 2*tally (orientedPoints .lower ((2)*q+2) ((4)*q+(-2)) (0:Int) ((4)*q) (2)) (event267 q e)=
      if ((e)≤((4)*q)) then orientedCount2 .lower ((2)*q+2) ((4)*q+(-2)) (0:Int) (min ((4)*q) (e)) (2) else 0 := by
    apply tally_oriented_predicate .lower ((2)*q+2) ((4)*q+(-2)) (0:Int) ((4)*q) (2) ((2)*q+2) ((4)*q+(-2)) (0:Int) (min ((4)*q) (e)) (event267 q e) (((e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .lower ((2)*q+2) ((4)*q+(-2)) (0:Int) ((4)*q) (2) p.1 p.2).mp hp
      simp at hb
      simp only [event267,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_267,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event268 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(p.1)) ∧ ((p.2)≤e ∧ e≤((4)*q))
theorem atom268_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .lower ((2)*q+2) ((4)*q+(-2)) (0:Int) ((4)*q) (2)) (event268 q e)=
      Identity_left1_0.term_268 q e := by
  classical
  have hc : 2*tally (orientedPoints .lower ((2)*q+2) ((4)*q+(-2)) (0:Int) ((4)*q) (2)) (event268 q e)=
      if ((5)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .lower (max ((2)*q+2) (e)) ((4)*q+(-2)) (0:Int) (min ((4)*q) (e)) (2) else 0 := by
    apply tally_oriented_predicate .lower ((2)*q+2) ((4)*q+(-2)) (0:Int) ((4)*q) (2) (max ((2)*q+2) (e)) ((4)*q+(-2)) (0:Int) (min ((4)*q) (e)) (event268 q e) (((5)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .lower ((2)*q+2) ((4)*q+(-2)) (0:Int) ((4)*q) (2) p.1 p.2).mp hp
      simp at hb
      simp only [event268,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_268,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event269 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(p.1))
theorem atom269_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect ((2)*q+2) ((3)*q+(-1)) ((3)*q+3) ((4)*q) (0:Int)) (event269 q e)=
      Identity_left1_0.term_269 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect ((2)*q+2) ((3)*q+(-1)) ((3)*q+3) ((4)*q) (0:Int)) (event269 q e)=
      if ((5)≤(e)) then orientedCount2 .rect (max ((2)*q+2) (e)) ((3)*q+(-1)) ((3)*q+3) ((4)*q) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect ((2)*q+2) ((3)*q+(-1)) ((3)*q+3) ((4)*q) (0:Int) (max ((2)*q+2) (e)) ((3)*q+(-1)) ((3)*q+3) ((4)*q) (event269 q e) (((5)≤(e)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect ((2)*q+2) ((3)*q+(-1)) ((3)*q+3) ((4)*q) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event269,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_269,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event270 (q e : Int) (p : Int×Int) : Prop := (((3)*q+1)≤e ∧ e≤((3)*q+1))
theorem atom270_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect ((2)*q+2) ((3)*q+(-1)) ((3)*q+3) ((4)*q) (0:Int)) (event270 q e)=
      Identity_left1_0.term_270 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect ((2)*q+2) ((3)*q+(-1)) ((3)*q+3) ((4)*q) (0:Int)) (event270 q e)=
      if (((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)) then orientedCount2 .rect ((2)*q+2) ((3)*q+(-1)) ((3)*q+3) ((4)*q) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect ((2)*q+2) ((3)*q+(-1)) ((3)*q+3) ((4)*q) (0:Int) ((2)*q+2) ((3)*q+(-1)) ((3)*q+3) ((4)*q) (event270 q e) ((((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect ((2)*q+2) ((3)*q+(-1)) ((3)*q+3) ((4)*q) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event270,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_270,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event271 (q e : Int) (p : Int×Int) : Prop := ((p.2)≤e ∧ e≤((4)*q))
theorem atom271_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect ((2)*q+2) ((3)*q+(-1)) ((3)*q+3) ((4)*q) (0:Int)) (event271 q e)=
      Identity_left1_0.term_271 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect ((2)*q+2) ((3)*q+(-1)) ((3)*q+3) ((4)*q) (0:Int)) (event271 q e)=
      if ((e)≤((4)*q)) then orientedCount2 .rect ((2)*q+2) ((3)*q+(-1)) ((3)*q+3) (min ((4)*q) (e)) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect ((2)*q+2) ((3)*q+(-1)) ((3)*q+3) ((4)*q) (0:Int) ((2)*q+2) ((3)*q+(-1)) ((3)*q+3) (min ((4)*q) (e)) (event271 q e) (((e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect ((2)*q+2) ((3)*q+(-1)) ((3)*q+3) ((4)*q) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event271,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_271,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event272 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(p.1)) ∧ (((3)*q+1)≤e ∧ e≤((3)*q+1))
theorem atom272_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .rect ((2)*q+2) ((3)*q+(-1)) ((3)*q+3) ((4)*q) (0:Int)) (event272 q e)=
      Identity_left1_0.term_272 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect ((2)*q+2) ((3)*q+(-1)) ((3)*q+3) ((4)*q) (0:Int)) (event272 q e)=
      if ((5)≤(e) ∧ ((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)) then orientedCount2 .rect (max ((2)*q+2) (e)) ((3)*q+(-1)) ((3)*q+3) ((4)*q) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect ((2)*q+2) ((3)*q+(-1)) ((3)*q+3) ((4)*q) (0:Int) (max ((2)*q+2) (e)) ((3)*q+(-1)) ((3)*q+3) ((4)*q) (event272 q e) (((5)≤(e) ∧ ((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect ((2)*q+2) ((3)*q+(-1)) ((3)*q+3) ((4)*q) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event272,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_272,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event273 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(p.1)) ∧ ((p.2)≤e ∧ e≤((4)*q))
theorem atom273_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .rect ((2)*q+2) ((3)*q+(-1)) ((3)*q+3) ((4)*q) (0:Int)) (event273 q e)=
      Identity_left1_0.term_273 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect ((2)*q+2) ((3)*q+(-1)) ((3)*q+3) ((4)*q) (0:Int)) (event273 q e)=
      if ((5)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect (max ((2)*q+2) (e)) ((3)*q+(-1)) ((3)*q+3) (min ((4)*q) (e)) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect ((2)*q+2) ((3)*q+(-1)) ((3)*q+3) ((4)*q) (0:Int) (max ((2)*q+2) (e)) ((3)*q+(-1)) ((3)*q+3) (min ((4)*q) (e)) (event273 q e) (((5)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect ((2)*q+2) ((3)*q+(-1)) ((3)*q+3) ((4)*q) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event273,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_273,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event274 (q e : Int) (p : Int×Int) : Prop := (((3)*q+1)≤e ∧ e≤((3)*q+1)) ∧ ((p.2)≤e ∧ e≤((4)*q))
theorem atom274_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .rect ((2)*q+2) ((3)*q+(-1)) ((3)*q+3) ((4)*q) (0:Int)) (event274 q e)=
      Identity_left1_0.term_274 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect ((2)*q+2) ((3)*q+(-1)) ((3)*q+3) ((4)*q) (0:Int)) (event274 q e)=
      if (((3)*q+1)≤(e) ∧ (e)≤((3)*q+1) ∧ (e)≤((4)*q)) then orientedCount2 .rect ((2)*q+2) ((3)*q+(-1)) ((3)*q+3) (min ((4)*q) (e)) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect ((2)*q+2) ((3)*q+(-1)) ((3)*q+3) ((4)*q) (0:Int) ((2)*q+2) ((3)*q+(-1)) ((3)*q+3) (min ((4)*q) (e)) (event274 q e) ((((3)*q+1)≤(e) ∧ (e)≤((3)*q+1) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect ((2)*q+2) ((3)*q+(-1)) ((3)*q+3) ((4)*q) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event274,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_274,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
def event275 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(p.1)) ∧ (((3)*q+1)≤e ∧ e≤((3)*q+1)) ∧ ((p.2)≤e ∧ e≤((4)*q))
theorem atom275_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect ((2)*q+2) ((3)*q+(-1)) ((3)*q+3) ((4)*q) (0:Int)) (event275 q e)=
      Identity_left1_0.term_275 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect ((2)*q+2) ((3)*q+(-1)) ((3)*q+3) ((4)*q) (0:Int)) (event275 q e)=
      if ((5)≤(e) ∧ ((3)*q+1)≤(e) ∧ (e)≤((3)*q+1) ∧ (e)≤((4)*q)) then orientedCount2 .rect (max ((2)*q+2) (e)) ((3)*q+(-1)) ((3)*q+3) (min ((4)*q) (e)) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect ((2)*q+2) ((3)*q+(-1)) ((3)*q+3) ((4)*q) (0:Int) (max ((2)*q+2) (e)) ((3)*q+(-1)) ((3)*q+3) (min ((4)*q) (e)) (event275 q e) (((5)≤(e) ∧ ((3)*q+1)≤(e) ∧ (e)≤((3)*q+1) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect ((2)*q+2) ((3)*q+(-1)) ((3)*q+3) ((4)*q) (0:Int) p.1 p.2).mp hp
      simp at hb
      simp only [event275,true_and]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_275,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero,ite_true] using hs
#print axioms atom242_count
#print axioms atom243_count
#print axioms atom244_count
#print axioms atom245_count
#print axioms atom246_count
#print axioms atom247_count
#print axioms atom248_count
#print axioms atom249_count
#print axioms atom250_count
#print axioms atom251_count
#print axioms atom252_count
#print axioms atom253_count
#print axioms atom254_count
#print axioms atom255_count
#print axioms atom256_count
#print axioms atom257_count
#print axioms atom258_count
#print axioms atom259_count
#print axioms atom260_count
#print axioms atom261_count
#print axioms atom262_count
#print axioms atom263_count
#print axioms atom264_count
#print axioms atom265_count
#print axioms atom266_count
#print axioms atom267_count
#print axioms atom268_count
#print axioms atom269_count
#print axioms atom270_count
#print axioms atom271_count
#print axioms atom272_count
#print axioms atom273_count
#print axioms atom274_count
#print axioms atom275_count
end
end LuRazLattice.AtomCounts
