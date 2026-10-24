import LatticeTally
import SpectrumIdentity_left1_0
namespace LuRazLattice.AtomCounts
set_option maxRecDepth 32768
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
noncomputable section
def event58 (q e : Int) (p : Int×Int) : Prop := (((3)*q+1)≤e ∧ e≤((3)*q+1))
theorem atom58_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (4) (q+1) (0:Int) (0:Int) (0:Int)) (event58 q e)=
      Identity_left1_0.term_58 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (4) (q+1) (0:Int) (0:Int) (0:Int)) (event58 q e)=
      if (((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)) then orientedCount2 .rect (4) (q+1) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (4) (q+1) (0:Int) (0:Int) (0:Int) (4) (q+1) (0:Int) (0:Int) (event58 q e) ((((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (4) (q+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp only [event58]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_58,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event59 (q e : Int) (p : Int×Int) : Prop := (((2)*q+p.1)≤e ∧ e≤((4)*q))
theorem atom59_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (4) (q+1) (0:Int) (0:Int) (0:Int)) (event59 q e)=
      Identity_left1_0.term_59 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (4) (q+1) (0:Int) (0:Int) (0:Int)) (event59 q e)=
      if ((e)≤((4)*q)) then orientedCount2 .rect (4) (min (q+1) ((-2)*q+e)) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (4) (q+1) (0:Int) (0:Int) (0:Int) (4) (min (q+1) ((-2)*q+e)) (0:Int) (0:Int) (event59 q e) (((e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (4) (q+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp only [event59]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_59,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event60 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤((2)*q+2)) ∧ (((3)*q+1)≤e ∧ e≤((3)*q+1))
theorem atom60_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .rect (4) (q+1) (0:Int) (0:Int) (0:Int)) (event60 q e)=
      Identity_left1_0.term_60 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (4) (q+1) (0:Int) (0:Int) (0:Int)) (event60 q e)=
      if ((5)≤(e) ∧ (e)≤((2)*q+2) ∧ ((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)) then orientedCount2 .rect (4) (q+1) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (4) (q+1) (0:Int) (0:Int) (0:Int) (4) (q+1) (0:Int) (0:Int) (event60 q e) (((5)≤(e) ∧ (e)≤((2)*q+2) ∧ ((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (4) (q+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp only [event60]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_60,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event61 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤((2)*q+2)) ∧ (((2)*q+p.1)≤e ∧ e≤((4)*q))
theorem atom61_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .rect (4) (q+1) (0:Int) (0:Int) (0:Int)) (event61 q e)=
      Identity_left1_0.term_61 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (4) (q+1) (0:Int) (0:Int) (0:Int)) (event61 q e)=
      if ((5)≤(e) ∧ (e)≤((2)*q+2) ∧ (e)≤((4)*q)) then orientedCount2 .rect (4) (min (q+1) ((-2)*q+e)) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (4) (q+1) (0:Int) (0:Int) (0:Int) (4) (min (q+1) ((-2)*q+e)) (0:Int) (0:Int) (event61 q e) (((5)≤(e) ∧ (e)≤((2)*q+2) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (4) (q+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp only [event61]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_61,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event62 (q e : Int) (p : Int×Int) : Prop := (((3)*q+1)≤e ∧ e≤((3)*q+1)) ∧ (((2)*q+p.1)≤e ∧ e≤((4)*q))
theorem atom62_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .rect (4) (q+1) (0:Int) (0:Int) (0:Int)) (event62 q e)=
      Identity_left1_0.term_62 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (4) (q+1) (0:Int) (0:Int) (0:Int)) (event62 q e)=
      if (((3)*q+1)≤(e) ∧ (e)≤((3)*q+1) ∧ (e)≤((4)*q)) then orientedCount2 .rect (4) (min (q+1) ((-2)*q+e)) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (4) (q+1) (0:Int) (0:Int) (0:Int) (4) (min (q+1) ((-2)*q+e)) (0:Int) (0:Int) (event62 q e) ((((3)*q+1)≤(e) ∧ (e)≤((3)*q+1) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (4) (q+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp only [event62]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_62,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event63 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤((2)*q+2)) ∧ (((3)*q+1)≤e ∧ e≤((3)*q+1)) ∧ (((2)*q+p.1)≤e ∧ e≤((4)*q))
theorem atom63_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (4) (q+1) (0:Int) (0:Int) (0:Int)) (event63 q e)=
      Identity_left1_0.term_63 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (4) (q+1) (0:Int) (0:Int) (0:Int)) (event63 q e)=
      if ((5)≤(e) ∧ (e)≤((2)*q+2) ∧ ((3)*q+1)≤(e) ∧ (e)≤((3)*q+1) ∧ (e)≤((4)*q)) then orientedCount2 .rect (4) (min (q+1) ((-2)*q+e)) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (4) (q+1) (0:Int) (0:Int) (0:Int) (4) (min (q+1) ((-2)*q+e)) (0:Int) (0:Int) (event63 q e) (((5)≤(e) ∧ (e)≤((2)*q+2) ∧ ((3)*q+1)≤(e) ∧ (e)≤((3)*q+1) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (4) (q+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp only [event63]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_63,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event64 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤((2)*q+2))
theorem atom64_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int)) (event64 q e)=
      Identity_left1_0.term_64 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int)) (event64 q e)=
      if ((5)≤(e) ∧ (e)≤((2)*q+2)) then orientedCount2 .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int) (q+4) ((2)*q+1) (0:Int) (0:Int) (event64 q e) (((5)≤(e) ∧ (e)≤((2)*q+2)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp only [event64]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_64,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event65 (q e : Int) (p : Int×Int) : Prop := (((3)*q+1)≤e ∧ e≤((3)*q+1))
theorem atom65_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int)) (event65 q e)=
      Identity_left1_0.term_65 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int)) (event65 q e)=
      if (((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)) then orientedCount2 .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int) (q+4) ((2)*q+1) (0:Int) (0:Int) (event65 q e) ((((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp only [event65]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_65,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event66 (q e : Int) (p : Int×Int) : Prop := (((2)*q+p.1+(-1))≤e ∧ e≤((4)*q))
theorem atom66_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int)) (event66 q e)=
      Identity_left1_0.term_66 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int)) (event66 q e)=
      if ((e)≤((4)*q)) then orientedCount2 .rect (q+4) (min ((2)*q+1) ((-2)*q+e+1)) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int) (q+4) (min ((2)*q+1) ((-2)*q+e+1)) (0:Int) (0:Int) (event66 q e) (((e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp only [event66]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_66,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event67 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤((2)*q+2)) ∧ (((3)*q+1)≤e ∧ e≤((3)*q+1))
theorem atom67_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int)) (event67 q e)=
      Identity_left1_0.term_67 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int)) (event67 q e)=
      if ((5)≤(e) ∧ (e)≤((2)*q+2) ∧ ((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)) then orientedCount2 .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int) (q+4) ((2)*q+1) (0:Int) (0:Int) (event67 q e) (((5)≤(e) ∧ (e)≤((2)*q+2) ∧ ((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp only [event67]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_67,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event68 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤((2)*q+2)) ∧ (((2)*q+p.1+(-1))≤e ∧ e≤((4)*q))
theorem atom68_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int)) (event68 q e)=
      Identity_left1_0.term_68 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int)) (event68 q e)=
      if ((5)≤(e) ∧ (e)≤((2)*q+2) ∧ (e)≤((4)*q)) then orientedCount2 .rect (q+4) (min ((2)*q+1) ((-2)*q+e+1)) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int) (q+4) (min ((2)*q+1) ((-2)*q+e+1)) (0:Int) (0:Int) (event68 q e) (((5)≤(e) ∧ (e)≤((2)*q+2) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp only [event68]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_68,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event69 (q e : Int) (p : Int×Int) : Prop := (((3)*q+1)≤e ∧ e≤((3)*q+1)) ∧ (((2)*q+p.1+(-1))≤e ∧ e≤((4)*q))
theorem atom69_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int)) (event69 q e)=
      Identity_left1_0.term_69 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int)) (event69 q e)=
      if (((3)*q+1)≤(e) ∧ (e)≤((3)*q+1) ∧ (e)≤((4)*q)) then orientedCount2 .rect (q+4) (min ((2)*q+1) ((-2)*q+e+1)) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int) (q+4) (min ((2)*q+1) ((-2)*q+e+1)) (0:Int) (0:Int) (event69 q e) ((((3)*q+1)≤(e) ∧ (e)≤((3)*q+1) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp only [event69]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_69,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event70 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤((2)*q+2)) ∧ (((3)*q+1)≤e ∧ e≤((3)*q+1)) ∧ (((2)*q+p.1+(-1))≤e ∧ e≤((4)*q))
theorem atom70_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int)) (event70 q e)=
      Identity_left1_0.term_70 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int)) (event70 q e)=
      if ((5)≤(e) ∧ (e)≤((2)*q+2) ∧ ((3)*q+1)≤(e) ∧ (e)≤((3)*q+1) ∧ (e)≤((4)*q)) then orientedCount2 .rect (q+4) (min ((2)*q+1) ((-2)*q+e+1)) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int) (q+4) (min ((2)*q+1) ((-2)*q+e+1)) (0:Int) (0:Int) (event70 q e) (((5)≤(e) ∧ (e)≤((2)*q+2) ∧ ((3)*q+1)≤(e) ∧ (e)≤((3)*q+1) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp only [event70]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_70,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event71 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤((2)*q+2))
theorem atom71_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event71 q e)=
      Identity_left1_0.term_71 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event71 q e)=
      if ((5)≤(e) ∧ (e)≤((2)*q+2)) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event71 q e) (((5)≤(e) ∧ (e)≤((2)*q+2)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp only [event71]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_71,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event72 (q e : Int) (p : Int×Int) : Prop := (((3)*q+1)≤e ∧ e≤((4)*q+(-1)))
theorem atom72_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event72 q e)=
      Identity_left1_0.term_72 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event72 q e)=
      if (((3)*q+1)≤(e) ∧ (e)≤((4)*q+(-1))) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event72 q e) ((((3)*q+1)≤(e) ∧ (e)≤((4)*q+(-1))))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp only [event72]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_72,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event73 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤((2)*q+2)) ∧ (((3)*q+1)≤e ∧ e≤((4)*q+(-1)))
theorem atom73_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event73 q e)=
      Identity_left1_0.term_73 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event73 q e)=
      if ((5)≤(e) ∧ (e)≤((2)*q+2) ∧ ((3)*q+1)≤(e) ∧ (e)≤((4)*q+(-1))) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event73 q e) (((5)≤(e) ∧ (e)≤((2)*q+2) ∧ ((3)*q+1)≤(e) ∧ (e)≤((4)*q+(-1))))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp only [event73]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_73,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event74 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(q+2))
theorem atom74_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (4) (q+1) (0:Int) (0:Int) (0:Int)) (event74 q e)=
      Identity_left1_0.term_74 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (4) (q+1) (0:Int) (0:Int) (0:Int)) (event74 q e)=
      if ((5)≤(e) ∧ (e)≤(q+2)) then orientedCount2 .rect (4) (q+1) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (4) (q+1) (0:Int) (0:Int) (0:Int) (4) (q+1) (0:Int) (0:Int) (event74 q e) (((5)≤(e) ∧ (e)≤(q+2)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (4) (q+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp only [event74]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_74,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event75 (q e : Int) (p : Int×Int) : Prop := (((2)*q+p.1)≤e ∧ e≤((4)*q))
theorem atom75_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (4) (q+1) (0:Int) (0:Int) (0:Int)) (event75 q e)=
      Identity_left1_0.term_75 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (4) (q+1) (0:Int) (0:Int) (0:Int)) (event75 q e)=
      if ((e)≤((4)*q)) then orientedCount2 .rect (4) (min (q+1) ((-2)*q+e)) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (4) (q+1) (0:Int) (0:Int) (0:Int) (4) (min (q+1) ((-2)*q+e)) (0:Int) (0:Int) (event75 q e) (((e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (4) (q+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp only [event75]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_75,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event76 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(q+2)) ∧ (((2)*q+p.1)≤e ∧ e≤((4)*q))
theorem atom76_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .rect (4) (q+1) (0:Int) (0:Int) (0:Int)) (event76 q e)=
      Identity_left1_0.term_76 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (4) (q+1) (0:Int) (0:Int) (0:Int)) (event76 q e)=
      if ((5)≤(e) ∧ (e)≤(q+2) ∧ (e)≤((4)*q)) then orientedCount2 .rect (4) (min (q+1) ((-2)*q+e)) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (4) (q+1) (0:Int) (0:Int) (0:Int) (4) (min (q+1) ((-2)*q+e)) (0:Int) (0:Int) (event76 q e) (((5)≤(e) ∧ (e)≤(q+2) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (4) (q+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp only [event76]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_76,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event77 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(p.1))
theorem atom77_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .upper (q+3) ((2)*q+1) (4) (q+1) (0:Int)) (event77 q e)=
      Identity_left1_0.term_77 q e := by
  classical
  have hc : 2*tally (orientedPoints .upper (q+3) ((2)*q+1) (4) (q+1) (0:Int)) (event77 q e)=
      if ((5)≤(e)) then orientedCount2 .upper (max (q+3) (e)) ((2)*q+1) (4) (q+1) (0:Int) else 0 := by
    apply tally_oriented_predicate .upper (q+3) ((2)*q+1) (4) (q+1) (0:Int) (max (q+3) (e)) ((2)*q+1) (4) (q+1) (event77 q e) (((5)≤(e)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .upper (q+3) ((2)*q+1) (4) (q+1) (0:Int) p.1 p.2).mp hp
      simp only [event77]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_77,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event78 (q e : Int) (p : Int×Int) : Prop := (((2)*q+p.2)≤e ∧ e≤((4)*q))
theorem atom78_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .upper (q+3) ((2)*q+1) (4) (q+1) (0:Int)) (event78 q e)=
      Identity_left1_0.term_78 q e := by
  classical
  have hc : 2*tally (orientedPoints .upper (q+3) ((2)*q+1) (4) (q+1) (0:Int)) (event78 q e)=
      if ((e)≤((4)*q)) then orientedCount2 .upper (q+3) ((2)*q+1) (4) (min (q+1) ((-2)*q+e)) (0:Int) else 0 := by
    apply tally_oriented_predicate .upper (q+3) ((2)*q+1) (4) (q+1) (0:Int) (q+3) ((2)*q+1) (4) (min (q+1) ((-2)*q+e)) (event78 q e) (((e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .upper (q+3) ((2)*q+1) (4) (q+1) (0:Int) p.1 p.2).mp hp
      simp only [event78]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_78,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event79 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(p.1)) ∧ (((2)*q+p.2)≤e ∧ e≤((4)*q))
theorem atom79_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .upper (q+3) ((2)*q+1) (4) (q+1) (0:Int)) (event79 q e)=
      Identity_left1_0.term_79 q e := by
  classical
  have hc : 2*tally (orientedPoints .upper (q+3) ((2)*q+1) (4) (q+1) (0:Int)) (event79 q e)=
      if ((5)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .upper (max (q+3) (e)) ((2)*q+1) (4) (min (q+1) ((-2)*q+e)) (0:Int) else 0 := by
    apply tally_oriented_predicate .upper (q+3) ((2)*q+1) (4) (q+1) (0:Int) (max (q+3) (e)) ((2)*q+1) (4) (min (q+1) ((-2)*q+e)) (event79 q e) (((5)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .upper (q+3) ((2)*q+1) (4) (q+1) (0:Int) p.1 p.2).mp hp
      simp only [event79]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_79,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event80 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(p.1))
theorem atom80_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .upper (q+3) ((2)*q+1) (q+3) ((2)*q+1) (0:Int)) (event80 q e)=
      Identity_left1_0.term_80 q e := by
  classical
  have hc : 2*tally (orientedPoints .upper (q+3) ((2)*q+1) (q+3) ((2)*q+1) (0:Int)) (event80 q e)=
      if ((5)≤(e)) then orientedCount2 .upper (max (q+3) (e)) ((2)*q+1) (q+3) ((2)*q+1) (0:Int) else 0 := by
    apply tally_oriented_predicate .upper (q+3) ((2)*q+1) (q+3) ((2)*q+1) (0:Int) (max (q+3) (e)) ((2)*q+1) (q+3) ((2)*q+1) (event80 q e) (((5)≤(e)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .upper (q+3) ((2)*q+1) (q+3) ((2)*q+1) (0:Int) p.1 p.2).mp hp
      simp only [event80]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_80,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event81 (q e : Int) (p : Int×Int) : Prop := (((2)*q+p.2+(-1))≤e ∧ e≤((4)*q))
theorem atom81_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .upper (q+3) ((2)*q+1) (q+3) ((2)*q+1) (0:Int)) (event81 q e)=
      Identity_left1_0.term_81 q e := by
  classical
  have hc : 2*tally (orientedPoints .upper (q+3) ((2)*q+1) (q+3) ((2)*q+1) (0:Int)) (event81 q e)=
      if ((e)≤((4)*q)) then orientedCount2 .upper (q+3) ((2)*q+1) (q+3) (min ((2)*q+1) ((-2)*q+e+1)) (0:Int) else 0 := by
    apply tally_oriented_predicate .upper (q+3) ((2)*q+1) (q+3) ((2)*q+1) (0:Int) (q+3) ((2)*q+1) (q+3) (min ((2)*q+1) ((-2)*q+e+1)) (event81 q e) (((e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .upper (q+3) ((2)*q+1) (q+3) ((2)*q+1) (0:Int) p.1 p.2).mp hp
      simp only [event81]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_81,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event82 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(p.1)) ∧ (((2)*q+p.2+(-1))≤e ∧ e≤((4)*q))
theorem atom82_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .upper (q+3) ((2)*q+1) (q+3) ((2)*q+1) (0:Int)) (event82 q e)=
      Identity_left1_0.term_82 q e := by
  classical
  have hc : 2*tally (orientedPoints .upper (q+3) ((2)*q+1) (q+3) ((2)*q+1) (0:Int)) (event82 q e)=
      if ((5)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .upper (max (q+3) (e)) ((2)*q+1) (q+3) (min ((2)*q+1) ((-2)*q+e+1)) (0:Int) else 0 := by
    apply tally_oriented_predicate .upper (q+3) ((2)*q+1) (q+3) ((2)*q+1) (0:Int) (max (q+3) (e)) ((2)*q+1) (q+3) (min ((2)*q+1) ((-2)*q+e+1)) (event82 q e) (((5)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .upper (q+3) ((2)*q+1) (q+3) ((2)*q+1) (0:Int) p.1 p.2).mp hp
      simp only [event82]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_82,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event83 (q e : Int) (p : Int×Int) : Prop := (((4)*q)≤e ∧ e≤((4)*q))
theorem atom83_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .rect (q+3) (q+3) (q+3) (q+3) (0:Int)) (event83 q e)=
      Identity_left1_0.term_83 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (q+3) (q+3) (q+3) (q+3) (0:Int)) (event83 q e)=
      if (((4)*q)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect (q+3) (q+3) (q+3) (q+3) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (q+3) (q+3) (q+3) (q+3) (0:Int) (q+3) (q+3) (q+3) (q+3) (event83 q e) ((((4)*q)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (q+3) (q+3) (q+3) (q+3) (0:Int) p.1 p.2).mp hp
      simp only [event83]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_83,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event84 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(q+3))
theorem atom84_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event84 q e)=
      Identity_left1_0.term_84 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event84 q e)=
      if ((5)≤(e) ∧ (e)≤(q+3)) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event84 q e) (((5)≤(e) ∧ (e)≤(q+3)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp only [event84]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_84,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event85 (q e : Int) (p : Int×Int) : Prop := (((3)*q+2)≤e ∧ e≤((4)*q))
theorem atom85_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event85 q e)=
      Identity_left1_0.term_85 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event85 q e)=
      if (((3)*q+2)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event85 q e) ((((3)*q+2)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp only [event85]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_85,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event86 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(q+3)) ∧ (((3)*q+2)≤e ∧ e≤((4)*q))
theorem atom86_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event86 q e)=
      Identity_left1_0.term_86 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event86 q e)=
      if ((5)≤(e) ∧ (e)≤(q+3) ∧ ((3)*q+2)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event86 q e) (((5)≤(e) ∧ (e)≤(q+3) ∧ ((3)*q+2)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp only [event86]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_86,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event87 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(q+2))
theorem atom87_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event87 q e)=
      Identity_left1_0.term_87 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event87 q e)=
      if ((5)≤(e) ∧ (e)≤(q+2)) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event87 q e) (((5)≤(e) ∧ (e)≤(q+2)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp only [event87]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_87,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event88 (q e : Int) (p : Int×Int) : Prop := (((2)*q+1)≤e ∧ e≤((4)*q))
theorem atom88_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event88 q e)=
      Identity_left1_0.term_88 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event88 q e)=
      if (((2)*q+1)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event88 q e) ((((2)*q+1)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp only [event88]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_88,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event89 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(q+2)) ∧ (((2)*q+1)≤e ∧ e≤((4)*q))
theorem atom89_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event89 q e)=
      Identity_left1_0.term_89 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event89 q e)=
      if ((5)≤(e) ∧ (e)≤(q+2) ∧ ((2)*q+1)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event89 q e) (((5)≤(e) ∧ (e)≤(q+2) ∧ ((2)*q+1)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp only [event89]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_89,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event90 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(p.1))
theorem atom90_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (q+3) ((2)*q+(-1)) (0:Int) (0:Int) (0:Int)) (event90 q e)=
      Identity_left1_0.term_90 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (q+3) ((2)*q+(-1)) (0:Int) (0:Int) (0:Int)) (event90 q e)=
      if ((5)≤(e)) then orientedCount2 .rect (max (q+3) (e)) ((2)*q+(-1)) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (q+3) ((2)*q+(-1)) (0:Int) (0:Int) (0:Int) (max (q+3) (e)) ((2)*q+(-1)) (0:Int) (0:Int) (event90 q e) (((5)≤(e)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (q+3) ((2)*q+(-1)) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp only [event90]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_90,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event91 (q e : Int) (p : Int×Int) : Prop := (((2)*q+1)≤e ∧ e≤((4)*q))
theorem atom91_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (q+3) ((2)*q+(-1)) (0:Int) (0:Int) (0:Int)) (event91 q e)=
      Identity_left1_0.term_91 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (q+3) ((2)*q+(-1)) (0:Int) (0:Int) (0:Int)) (event91 q e)=
      if (((2)*q+1)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect (q+3) ((2)*q+(-1)) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (q+3) ((2)*q+(-1)) (0:Int) (0:Int) (0:Int) (q+3) ((2)*q+(-1)) (0:Int) (0:Int) (event91 q e) ((((2)*q+1)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (q+3) ((2)*q+(-1)) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp only [event91]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_91,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event92 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤(p.1)) ∧ (((2)*q+1)≤e ∧ e≤((4)*q))
theorem atom92_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .rect (q+3) ((2)*q+(-1)) (0:Int) (0:Int) (0:Int)) (event92 q e)=
      Identity_left1_0.term_92 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (q+3) ((2)*q+(-1)) (0:Int) (0:Int) (0:Int)) (event92 q e)=
      if ((5)≤(e) ∧ ((2)*q+1)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect (max (q+3) (e)) ((2)*q+(-1)) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (q+3) ((2)*q+(-1)) (0:Int) (0:Int) (0:Int) (max (q+3) (e)) ((2)*q+(-1)) (0:Int) (0:Int) (event92 q e) (((5)≤(e) ∧ ((2)*q+1)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (q+3) ((2)*q+(-1)) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp only [event92]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_92,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event93 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤((4)*q))
theorem atom93_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event93 q e)=
      Identity_left1_0.term_93 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int)) (event93 q e)=
      if ((5)≤(e) ∧ (e)≤((4)*q)) then orientedCount2 .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) (event93 q e) (((5)≤(e) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp only [event93]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_93,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event94 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤((2)*q+2))
theorem atom94_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (4) (q+1) (0:Int) (0:Int) (0:Int)) (event94 q e)=
      Identity_left1_0.term_94 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (4) (q+1) (0:Int) (0:Int) (0:Int)) (event94 q e)=
      if ((5)≤(e) ∧ (e)≤((2)*q+2)) then orientedCount2 .rect (4) (q+1) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (4) (q+1) (0:Int) (0:Int) (0:Int) (4) (q+1) (0:Int) (0:Int) (event94 q e) (((5)≤(e) ∧ (e)≤((2)*q+2)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (4) (q+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp only [event94]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_94,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event95 (q e : Int) (p : Int×Int) : Prop := (((3)*q+1)≤e ∧ e≤((3)*q+1))
theorem atom95_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (4) (q+1) (0:Int) (0:Int) (0:Int)) (event95 q e)=
      Identity_left1_0.term_95 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (4) (q+1) (0:Int) (0:Int) (0:Int)) (event95 q e)=
      if (((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)) then orientedCount2 .rect (4) (q+1) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (4) (q+1) (0:Int) (0:Int) (0:Int) (4) (q+1) (0:Int) (0:Int) (event95 q e) ((((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (4) (q+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp only [event95]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_95,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event96 (q e : Int) (p : Int×Int) : Prop := (((2)*q+p.1)≤e ∧ e≤((4)*q))
theorem atom96_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (4) (q+1) (0:Int) (0:Int) (0:Int)) (event96 q e)=
      Identity_left1_0.term_96 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (4) (q+1) (0:Int) (0:Int) (0:Int)) (event96 q e)=
      if ((e)≤((4)*q)) then orientedCount2 .rect (4) (min (q+1) ((-2)*q+e)) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (4) (q+1) (0:Int) (0:Int) (0:Int) (4) (min (q+1) ((-2)*q+e)) (0:Int) (0:Int) (event96 q e) (((e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (4) (q+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp only [event96]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_96,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event97 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤((2)*q+2)) ∧ (((3)*q+1)≤e ∧ e≤((3)*q+1))
theorem atom97_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .rect (4) (q+1) (0:Int) (0:Int) (0:Int)) (event97 q e)=
      Identity_left1_0.term_97 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (4) (q+1) (0:Int) (0:Int) (0:Int)) (event97 q e)=
      if ((5)≤(e) ∧ (e)≤((2)*q+2) ∧ ((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)) then orientedCount2 .rect (4) (q+1) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (4) (q+1) (0:Int) (0:Int) (0:Int) (4) (q+1) (0:Int) (0:Int) (event97 q e) (((5)≤(e) ∧ (e)≤((2)*q+2) ∧ ((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (4) (q+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp only [event97]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_97,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event98 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤((2)*q+2)) ∧ (((2)*q+p.1)≤e ∧ e≤((4)*q))
theorem atom98_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .rect (4) (q+1) (0:Int) (0:Int) (0:Int)) (event98 q e)=
      Identity_left1_0.term_98 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (4) (q+1) (0:Int) (0:Int) (0:Int)) (event98 q e)=
      if ((5)≤(e) ∧ (e)≤((2)*q+2) ∧ (e)≤((4)*q)) then orientedCount2 .rect (4) (min (q+1) ((-2)*q+e)) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (4) (q+1) (0:Int) (0:Int) (0:Int) (4) (min (q+1) ((-2)*q+e)) (0:Int) (0:Int) (event98 q e) (((5)≤(e) ∧ (e)≤((2)*q+2) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (4) (q+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp only [event98]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_98,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event99 (q e : Int) (p : Int×Int) : Prop := (((3)*q+1)≤e ∧ e≤((3)*q+1)) ∧ (((2)*q+p.1)≤e ∧ e≤((4)*q))
theorem atom99_count (q e : Int) :
    (-1:Int)*2*tally (orientedPoints .rect (4) (q+1) (0:Int) (0:Int) (0:Int)) (event99 q e)=
      Identity_left1_0.term_99 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (4) (q+1) (0:Int) (0:Int) (0:Int)) (event99 q e)=
      if (((3)*q+1)≤(e) ∧ (e)≤((3)*q+1) ∧ (e)≤((4)*q)) then orientedCount2 .rect (4) (min (q+1) ((-2)*q+e)) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (4) (q+1) (0:Int) (0:Int) (0:Int) (4) (min (q+1) ((-2)*q+e)) (0:Int) (0:Int) (event99 q e) ((((3)*q+1)≤(e) ∧ (e)≤((3)*q+1) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (4) (q+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp only [event99]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (-1:Int)*z) hc
  simpa only [Identity_left1_0.term_99,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event100 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤((2)*q+2)) ∧ (((3)*q+1)≤e ∧ e≤((3)*q+1)) ∧ (((2)*q+p.1)≤e ∧ e≤((4)*q))
theorem atom100_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (4) (q+1) (0:Int) (0:Int) (0:Int)) (event100 q e)=
      Identity_left1_0.term_100 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (4) (q+1) (0:Int) (0:Int) (0:Int)) (event100 q e)=
      if ((5)≤(e) ∧ (e)≤((2)*q+2) ∧ ((3)*q+1)≤(e) ∧ (e)≤((3)*q+1) ∧ (e)≤((4)*q)) then orientedCount2 .rect (4) (min (q+1) ((-2)*q+e)) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (4) (q+1) (0:Int) (0:Int) (0:Int) (4) (min (q+1) ((-2)*q+e)) (0:Int) (0:Int) (event100 q e) (((5)≤(e) ∧ (e)≤((2)*q+2) ∧ ((3)*q+1)≤(e) ∧ (e)≤((3)*q+1) ∧ (e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (4) (q+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp only [event100]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_100,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event101 (q e : Int) (p : Int×Int) : Prop := ((5)≤e ∧ e≤((2)*q+2))
theorem atom101_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int)) (event101 q e)=
      Identity_left1_0.term_101 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int)) (event101 q e)=
      if ((5)≤(e) ∧ (e)≤((2)*q+2)) then orientedCount2 .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int) (q+4) ((2)*q+1) (0:Int) (0:Int) (event101 q e) (((5)≤(e) ∧ (e)≤((2)*q+2)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp only [event101]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_101,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event102 (q e : Int) (p : Int×Int) : Prop := (((3)*q+1)≤e ∧ e≤((3)*q+1))
theorem atom102_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int)) (event102 q e)=
      Identity_left1_0.term_102 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int)) (event102 q e)=
      if (((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)) then orientedCount2 .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int) (q+4) ((2)*q+1) (0:Int) (0:Int) (event102 q e) ((((3)*q+1)≤(e) ∧ (e)≤((3)*q+1)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp only [event102]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_102,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
def event103 (q e : Int) (p : Int×Int) : Prop := (((2)*q+p.1+(-1))≤e ∧ e≤((4)*q))
theorem atom103_count (q e : Int) :
    (1:Int)*2*tally (orientedPoints .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int)) (event103 q e)=
      Identity_left1_0.term_103 q e := by
  classical
  have hc : 2*tally (orientedPoints .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int)) (event103 q e)=
      if ((e)≤((4)*q)) then orientedCount2 .rect (q+4) (min ((2)*q+1) ((-2)*q+e+1)) (0:Int) (0:Int) (0:Int) else 0 := by
    apply tally_oriented_predicate .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int) (q+4) (min ((2)*q+1) ((-2)*q+e+1)) (0:Int) (0:Int) (event103 q e) (((e)≤((4)*q)))
    · omega
    · omega
    · omega
    · omega
    · intro p hp
      have hb := (orientedPoints_mem .rect (q+4) ((2)*q+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
      simp only [event103]
      omega
  simp only [orientedCount2_guarded] at hc
  have hs := congrArg (fun z : Int => (1:Int)*z) hc
  simpa only [Identity_left1_0.term_103,guardedCount2,triangleBox2,tri2,pos,Int.mul_assoc,Int.one_mul,Int.mul_zero,Int.zero_mul,Int.neg_zero] using hs
#print axioms atom58_count
#print axioms atom59_count
#print axioms atom60_count
#print axioms atom61_count
#print axioms atom62_count
#print axioms atom63_count
#print axioms atom64_count
#print axioms atom65_count
#print axioms atom66_count
#print axioms atom67_count
#print axioms atom68_count
#print axioms atom69_count
#print axioms atom70_count
#print axioms atom71_count
#print axioms atom72_count
#print axioms atom73_count
#print axioms atom74_count
#print axioms atom75_count
#print axioms atom76_count
#print axioms atom77_count
#print axioms atom78_count
#print axioms atom79_count
#print axioms atom80_count
#print axioms atom81_count
#print axioms atom82_count
#print axioms atom83_count
#print axioms atom84_count
#print axioms atom85_count
#print axioms atom86_count
#print axioms atom87_count
#print axioms atom88_count
#print axioms atom89_count
#print axioms atom90_count
#print axioms atom91_count
#print axioms atom92_count
#print axioms atom93_count
#print axioms atom94_count
#print axioms atom95_count
#print axioms atom96_count
#print axioms atom97_count
#print axioms atom98_count
#print axioms atom99_count
#print axioms atom100_count
#print axioms atom101_count
#print axioms atom102_count
#print axioms atom103_count
end
end LuRazLattice.AtomCounts
