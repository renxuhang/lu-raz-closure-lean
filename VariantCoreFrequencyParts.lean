import ThreeRowComplete
import LuRazCoreFrequencies

namespace LuRazThreeRow
open LuRazClosure LuRazEnumeration
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000

noncomputable def CountAt (l : List (Nat → Prop)) (e : Nat) : Int := by
  classical
  exact ((l.filter (fun R => decide (R e))).length : Int)

theorem count_at_append (a b : List (Nat → Prop)) (e : Nat) :
    CountAt (a++b) e = CountAt a e + CountAt b e := by
  classical
  simp only [CountAt,List.filter_append,List.length_append,Int.natCast_add]

theorem count_at_present (l : List (Nat → Prop)) (e : Nat)
    (h : ∀ R∈l, R e) : CountAt l e=(l.length : Int) := by
  classical
  have hf : l.filter (fun R => decide (R e))=l :=
    List.filter_eq_self.mpr (fun R hR => decide_eq_true (h R hR))
  simp only [CountAt,hf]

theorem count_at_absent (l : List (Nat → Prop)) (e : Nat)
    (h : ∀ R∈l, ¬R e) : CountAt l e=0 := by
  classical
  have hf : l.filter (fun R => decide (R e))=[] := by
    apply List.filter_eq_nil_iff.mpr
    intro R hR h'
    exact h R hR (of_decide_eq_true h')
  simp only [CountAt,hf,List.length_nil,Int.natCast_zero]

theorem count_at_perm (a b : List (Nat → Prop)) (h : a.Perm b) (e : Nat) :
    CountAt a e=CountAt b e := by
  classical
  exact congrArg (fun n : Nat => (n:Int)) (h.filter (fun R => decide (R e))).length_eq

def OldCoreFrequency2 (q : Int) (e : Nat) : Int :=
  if e=1 then 19*q*q+25*q-44 else
  if e=2 then 17*q*q+25*q-34 else
  if e=3 then 17*q*q+27*q-48 else 16*q*q+30*q-46

def NewCoreFrequency2 (q : Int) (e : Nat) : Int :=
  if e=1 then 19*q*q+17*q-26 else
  if e=2 then 17*q*q+21*q-30 else
  if e=3 then 17*q*q+23*q-36 else 16*q*q+34*q-46

def OldChangedFrequency2 (q : Int) (e : Nat) : Int :=
  if e=1 then 13*q*q+17*q-34 else
  if e=2 then 17*q*q+7*q-30 else
  if e=3 then 17*q*q+27*q-52 else 10*q*q+22*q-42

def NewChangedFrequency2 (q : Int) (e : Nat) : Int :=
  if e=1 then 13*q*q+9*q-16 else
  if e=2 then 17*q*q+3*q-26 else
  if e=3 then 17*q*q+23*q-40 else 10*q*q+26*q-42

theorem old_core_frequency2 (q e : Nat) (hq : 4≤q) (he : 1≤e ∧ e≤4) :
    2*CountAt (closureMembers q) e=OldCoreFrequency2 (q:Int) e := by
  have hc : e=1 ∨ e=2 ∨ e=3 ∨ e=4 := by omega
  rcases hc with rfl | rfl | rfl | rfl
  · exact containingOneMembers_length q hq
  · exact containingTwoMembers_length q hq
  · exact containingThreeMembers_length q hq
  · exact containingFourMembers_length q hq

theorem old_changed_frequency2 (q e : Nat) (hq : 4≤q) (he : 1≤e ∧ e≤4) :
    ∃ l : List (Nat → Prop), l.Nodup ∧
      (∀ R, R∈l ↔ LuRazClosure.Generated q R ∧ Changed R) ∧
      2*CountAt l e=OldChangedFrequency2 (q:Int) e := by
  obtain ⟨l0,hn0,he0,hl0⟩ := LuRazClosure.small_cardinality q hq 5 (by omega)
  obtain ⟨l1,hn1,he1,hl1⟩ := LuRazClosure.core23_cardinality q hq
  obtain ⟨l2,hn2,he2,hl2⟩ := LuRazClosure.core123_cardinality q hq
  let l3 : List (Nat → Prop) := []
  have hn3 : l3.Nodup := List.nodup_nil
  have he3 : ∀ R, R∈l3 ↔ LuRazClosure.Generated q R ∧ Core12 R := by
    intro R; simp [l3,old_core12_empty q hq R]
  have hl3 : l3.length=0 := rfl
  obtain ⟨l4,hn4,he4,hl4⟩ := LuRazClosure.core134_cardinality q hq
  obtain ⟨l5,hn5,he5,hl5⟩ := LuRazClosure.core234_cardinality q hq
  obtain ⟨l6,hn6,he6,hl6⟩ := LuRazClosure.full_cardinality q hq
  have he0' : ∀ R, R∈l0 ↔ LuRazClosure.Generated q R ∧ Core5 R := by
    intro R; simpa [CoreSmallAt,Core5] using he0 R
  have hl0' : l0.length=5 := by simpa [smallCount] using hl0
  have h := seven_enumerations (LuRazClosure.Generated q) l0 hn0 he0' l1 hn1 he1 l2 hn2 he2 l3 hn3 he3 l4 hn4 he4 l5 hn5 he5 l6 hn6 he6
  refine ⟨l0 ++ l1 ++ l2 ++ l3 ++ l4 ++ l5 ++ l6,h.1,h.2,?_⟩
  have hc : e=1 ∨ e=2 ∨ e=3 ∨ e=4 := by omega
  rcases hc with rfl | rfl | rfl | rfl
  ·
    have f0 : CountAt l0 1=(l0.length : Int) := by
      apply count_at_present
      intro R hR
      have hh := ((he0' R).mp hR).2
      unfold Core5 at hh
      exact hh.1
    have f1 : CountAt l1 1=0 := by
      apply count_at_absent
      intro R hR
      have hh := ((he1 R).mp hR).2
      unfold Core23 at hh
      exact hh.1
    have f2 : CountAt l2 1=(l2.length : Int) := by
      apply count_at_present
      intro R hR
      have hh := ((he2 R).mp hR).2
      unfold Core123 at hh
      exact hh.1
    have f3 : CountAt l3 1=0 := by
      apply count_at_absent
      intro R hR
      have hh := ((he3 R).mp hR).2
      unfold Core12 at hh
      exact hh.1
    have f4 : CountAt l4 1=(l4.length : Int) := by
      apply count_at_present
      intro R hR
      have hh := ((he4 R).mp hR).2
      unfold Core134 at hh
      exact hh.1
    have f5 : CountAt l5 1=0 := by
      apply count_at_absent
      intro R hR
      have hh := ((he5 R).mp hR).2
      unfold Core234 at hh
      exact hh.1
    have f6 : CountAt l6 1=(l6.length : Int) := by
      apply count_at_present
      intro R hR
      have hh := ((he6 R).mp hR).2
      unfold CoreFull at hh
      exact hh.1
    simp only [count_at_append,f0,f1,f2,f3,f4,f5,f6,OldChangedFrequency2,Nat.reduceEqDiff,ite_true,ite_false]
    simp only [Int.mul_assoc] at *
    omega
  ·
    have f0 : CountAt l0 2=0 := by
      apply count_at_absent
      intro R hR
      have hh := ((he0' R).mp hR).2
      unfold Core5 at hh
      exact hh.2.1
    have f1 : CountAt l1 2=(l1.length : Int) := by
      apply count_at_present
      intro R hR
      have hh := ((he1 R).mp hR).2
      unfold Core23 at hh
      exact hh.2.1
    have f2 : CountAt l2 2=(l2.length : Int) := by
      apply count_at_present
      intro R hR
      have hh := ((he2 R).mp hR).2
      unfold Core123 at hh
      exact hh.2.1
    have f3 : CountAt l3 2=0 := by
      apply count_at_absent
      intro R hR
      have hh := ((he3 R).mp hR).2
      unfold Core12 at hh
      exact hh.2.1
    have f4 : CountAt l4 2=0 := by
      apply count_at_absent
      intro R hR
      have hh := ((he4 R).mp hR).2
      unfold Core134 at hh
      exact hh.2.1
    have f5 : CountAt l5 2=(l5.length : Int) := by
      apply count_at_present
      intro R hR
      have hh := ((he5 R).mp hR).2
      unfold Core234 at hh
      exact hh.2.1
    have f6 : CountAt l6 2=(l6.length : Int) := by
      apply count_at_present
      intro R hR
      have hh := ((he6 R).mp hR).2
      unfold CoreFull at hh
      exact hh.2.1
    simp only [count_at_append,f0,f1,f2,f3,f4,f5,f6,OldChangedFrequency2,Nat.reduceEqDiff,ite_true,ite_false]
    simp only [Int.mul_assoc] at *
    omega
  ·
    have f0 : CountAt l0 3=(l0.length : Int) := by
      apply count_at_present
      intro R hR
      have hh := ((he0' R).mp hR).2
      unfold Core5 at hh
      exact hh.2.2.1
    have f1 : CountAt l1 3=(l1.length : Int) := by
      apply count_at_present
      intro R hR
      have hh := ((he1 R).mp hR).2
      unfold Core23 at hh
      exact hh.2.2.1
    have f2 : CountAt l2 3=(l2.length : Int) := by
      apply count_at_present
      intro R hR
      have hh := ((he2 R).mp hR).2
      unfold Core123 at hh
      exact hh.2.2.1
    have f3 : CountAt l3 3=(l3.length : Int) := by
      apply count_at_present
      intro R hR
      have hh := ((he3 R).mp hR).2
      unfold Core12 at hh
      exact hh.2.2.1
    have f4 : CountAt l4 3=(l4.length : Int) := by
      apply count_at_present
      intro R hR
      have hh := ((he4 R).mp hR).2
      unfold Core134 at hh
      exact hh.2.2.1
    have f5 : CountAt l5 3=(l5.length : Int) := by
      apply count_at_present
      intro R hR
      have hh := ((he5 R).mp hR).2
      unfold Core234 at hh
      exact hh.2.2.1
    have f6 : CountAt l6 3=(l6.length : Int) := by
      apply count_at_present
      intro R hR
      have hh := ((he6 R).mp hR).2
      unfold CoreFull at hh
      exact hh.2.2.1
    simp only [count_at_append,f0,f1,f2,f3,f4,f5,f6,OldChangedFrequency2,Nat.reduceEqDiff,ite_true,ite_false]
    simp only [Int.mul_assoc] at *
    omega
  ·
    have f0 : CountAt l0 4=0 := by
      apply count_at_absent
      intro R hR
      have hh := ((he0' R).mp hR).2
      unfold Core5 at hh
      exact hh.2.2.2
    have f1 : CountAt l1 4=0 := by
      apply count_at_absent
      intro R hR
      have hh := ((he1 R).mp hR).2
      unfold Core23 at hh
      exact hh.2.2.2
    have f2 : CountAt l2 4=0 := by
      apply count_at_absent
      intro R hR
      have hh := ((he2 R).mp hR).2
      unfold Core123 at hh
      exact hh.2.2.2
    have f3 : CountAt l3 4=(l3.length : Int) := by
      apply count_at_present
      intro R hR
      have hh := ((he3 R).mp hR).2
      unfold Core12 at hh
      exact hh.2.2.2
    have f4 : CountAt l4 4=(l4.length : Int) := by
      apply count_at_present
      intro R hR
      have hh := ((he4 R).mp hR).2
      unfold Core134 at hh
      exact hh.2.2.2
    have f5 : CountAt l5 4=(l5.length : Int) := by
      apply count_at_present
      intro R hR
      have hh := ((he5 R).mp hR).2
      unfold Core234 at hh
      exact hh.2.2.2
    have f6 : CountAt l6 4=(l6.length : Int) := by
      apply count_at_present
      intro R hR
      have hh := ((he6 R).mp hR).2
      unfold CoreFull at hh
      exact hh.2.2.2
    simp only [count_at_append,f0,f1,f2,f3,f4,f5,f6,OldChangedFrequency2,Nat.reduceEqDiff,ite_true,ite_false]
    simp only [Int.mul_assoc] at *
    omega

theorem new_changed_frequency2 (q e : Nat) (hq : 4≤q) (he : 1≤e ∧ e≤4) :
    ∃ l : List (Nat → Prop), l.Nodup ∧
      (∀ R, R∈l ↔ Generated q R ∧ Changed R) ∧
      2*CountAt l e=NewChangedFrequency2 (q:Int) e := by
  obtain ⟨l0,hn0,he0,hl0⟩ := core5_cardinality q hq
  obtain ⟨l1,hn1,he1,hl1⟩ := LuRazThreeRow.core23_cardinality q hq
  obtain ⟨l2,hn2,he2,hl2⟩ := core123_new_cardinality q hq
  obtain ⟨l3,hn3,he3,hl3⟩ := core12_cardinality q hq
  obtain ⟨l4,hn4,he4,hl4⟩ := core134_new_cardinality q hq
  obtain ⟨l5,hn5,he5,hl5⟩ := LuRazThreeRow.core234_cardinality q hq
  obtain ⟨l6,hn6,he6,hl6⟩ := full_new_cardinality q hq
  have h := seven_enumerations (Generated q) l0 hn0 he0 l1 hn1 he1 l2 hn2 he2 l3 hn3 he3 l4 hn4 he4 l5 hn5 he5 l6 hn6 he6
  refine ⟨l0 ++ l1 ++ l2 ++ l3 ++ l4 ++ l5 ++ l6,h.1,h.2,?_⟩
  have hc : e=1 ∨ e=2 ∨ e=3 ∨ e=4 := by omega
  rcases hc with rfl | rfl | rfl | rfl
  ·
    have f0 : CountAt l0 1=(l0.length : Int) := by
      apply count_at_present
      intro R hR
      have hh := ((he0 R).mp hR).2
      unfold Core5 at hh
      exact hh.1
    have f1 : CountAt l1 1=0 := by
      apply count_at_absent
      intro R hR
      have hh := ((he1 R).mp hR).2
      unfold Core23 at hh
      exact hh.1
    have f2 : CountAt l2 1=(l2.length : Int) := by
      apply count_at_present
      intro R hR
      have hh := ((he2 R).mp hR).2
      unfold Core123 at hh
      exact hh.1
    have f3 : CountAt l3 1=0 := by
      apply count_at_absent
      intro R hR
      have hh := ((he3 R).mp hR).2
      unfold Core12 at hh
      exact hh.1
    have f4 : CountAt l4 1=(l4.length : Int) := by
      apply count_at_present
      intro R hR
      have hh := ((he4 R).mp hR).2
      unfold Core134 at hh
      exact hh.1
    have f5 : CountAt l5 1=0 := by
      apply count_at_absent
      intro R hR
      have hh := ((he5 R).mp hR).2
      unfold Core234 at hh
      exact hh.1
    have f6 : CountAt l6 1=(l6.length : Int) := by
      apply count_at_present
      intro R hR
      have hh := ((he6 R).mp hR).2
      unfold CoreFull at hh
      exact hh.1
    simp only [count_at_append,f0,f1,f2,f3,f4,f5,f6,NewChangedFrequency2,Nat.reduceEqDiff,ite_true,ite_false]
    simp only [Int.mul_assoc] at *
    omega
  ·
    have f0 : CountAt l0 2=0 := by
      apply count_at_absent
      intro R hR
      have hh := ((he0 R).mp hR).2
      unfold Core5 at hh
      exact hh.2.1
    have f1 : CountAt l1 2=(l1.length : Int) := by
      apply count_at_present
      intro R hR
      have hh := ((he1 R).mp hR).2
      unfold Core23 at hh
      exact hh.2.1
    have f2 : CountAt l2 2=(l2.length : Int) := by
      apply count_at_present
      intro R hR
      have hh := ((he2 R).mp hR).2
      unfold Core123 at hh
      exact hh.2.1
    have f3 : CountAt l3 2=0 := by
      apply count_at_absent
      intro R hR
      have hh := ((he3 R).mp hR).2
      unfold Core12 at hh
      exact hh.2.1
    have f4 : CountAt l4 2=0 := by
      apply count_at_absent
      intro R hR
      have hh := ((he4 R).mp hR).2
      unfold Core134 at hh
      exact hh.2.1
    have f5 : CountAt l5 2=(l5.length : Int) := by
      apply count_at_present
      intro R hR
      have hh := ((he5 R).mp hR).2
      unfold Core234 at hh
      exact hh.2.1
    have f6 : CountAt l6 2=(l6.length : Int) := by
      apply count_at_present
      intro R hR
      have hh := ((he6 R).mp hR).2
      unfold CoreFull at hh
      exact hh.2.1
    simp only [count_at_append,f0,f1,f2,f3,f4,f5,f6,NewChangedFrequency2,Nat.reduceEqDiff,ite_true,ite_false]
    simp only [Int.mul_assoc] at *
    omega
  ·
    have f0 : CountAt l0 3=(l0.length : Int) := by
      apply count_at_present
      intro R hR
      have hh := ((he0 R).mp hR).2
      unfold Core5 at hh
      exact hh.2.2.1
    have f1 : CountAt l1 3=(l1.length : Int) := by
      apply count_at_present
      intro R hR
      have hh := ((he1 R).mp hR).2
      unfold Core23 at hh
      exact hh.2.2.1
    have f2 : CountAt l2 3=(l2.length : Int) := by
      apply count_at_present
      intro R hR
      have hh := ((he2 R).mp hR).2
      unfold Core123 at hh
      exact hh.2.2.1
    have f3 : CountAt l3 3=(l3.length : Int) := by
      apply count_at_present
      intro R hR
      have hh := ((he3 R).mp hR).2
      unfold Core12 at hh
      exact hh.2.2.1
    have f4 : CountAt l4 3=(l4.length : Int) := by
      apply count_at_present
      intro R hR
      have hh := ((he4 R).mp hR).2
      unfold Core134 at hh
      exact hh.2.2.1
    have f5 : CountAt l5 3=(l5.length : Int) := by
      apply count_at_present
      intro R hR
      have hh := ((he5 R).mp hR).2
      unfold Core234 at hh
      exact hh.2.2.1
    have f6 : CountAt l6 3=(l6.length : Int) := by
      apply count_at_present
      intro R hR
      have hh := ((he6 R).mp hR).2
      unfold CoreFull at hh
      exact hh.2.2.1
    simp only [count_at_append,f0,f1,f2,f3,f4,f5,f6,NewChangedFrequency2,Nat.reduceEqDiff,ite_true,ite_false]
    simp only [Int.mul_assoc] at *
    omega
  ·
    have f0 : CountAt l0 4=0 := by
      apply count_at_absent
      intro R hR
      have hh := ((he0 R).mp hR).2
      unfold Core5 at hh
      exact hh.2.2.2
    have f1 : CountAt l1 4=0 := by
      apply count_at_absent
      intro R hR
      have hh := ((he1 R).mp hR).2
      unfold Core23 at hh
      exact hh.2.2.2
    have f2 : CountAt l2 4=0 := by
      apply count_at_absent
      intro R hR
      have hh := ((he2 R).mp hR).2
      unfold Core123 at hh
      exact hh.2.2.2
    have f3 : CountAt l3 4=(l3.length : Int) := by
      apply count_at_present
      intro R hR
      have hh := ((he3 R).mp hR).2
      unfold Core12 at hh
      exact hh.2.2.2
    have f4 : CountAt l4 4=(l4.length : Int) := by
      apply count_at_present
      intro R hR
      have hh := ((he4 R).mp hR).2
      unfold Core134 at hh
      exact hh.2.2.2
    have f5 : CountAt l5 4=(l5.length : Int) := by
      apply count_at_present
      intro R hR
      have hh := ((he5 R).mp hR).2
      unfold Core234 at hh
      exact hh.2.2.2
    have f6 : CountAt l6 4=(l6.length : Int) := by
      apply count_at_present
      intro R hR
      have hh := ((he6 R).mp hR).2
      unfold CoreFull at hh
      exact hh.2.2.2
    simp only [count_at_append,f0,f1,f2,f3,f4,f5,f6,NewChangedFrequency2,Nat.reduceEqDiff,ite_true,ite_false]
    simp only [Int.mul_assoc] at *
    omega

