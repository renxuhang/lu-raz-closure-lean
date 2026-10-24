import LatticeCounting

namespace LuRazLattice
open LuRazEnumeration
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

theorem trianglePoints_mem (al au bl bu c x y : Int) :
    (x,y)∈trianglePoints al au bl bu c ↔
      al≤x ∧ x≤au ∧ bl≤y ∧ y≤bu ∧ x+c≤y := by
  constructor
  · intro hm
    obtain ⟨i,hi,hr⟩ := List.mem_flatMap.mp hm
    obtain ⟨j,hj,he⟩ := List.mem_map.mp hr
    have hip := List.mem_range.mp hi
    have hjs := List.mem_filter.mp hj
    have hjp := List.mem_range.mp hjs.1
    have hle := of_decide_eq_true hjs.2
    have hx : al+(i:Int)=x := congrArg Prod.fst he
    have hy : bl+(j:Int)=y := congrArg Prod.snd he
    omega
  · intro h
    let i := (x-al).toNat
    let j := (y-bl).toNat
    have hi : (i:Int)=x-al := by dsimp [i]; omega
    have hj : (j:Int)=y-bl := by dsimp [j]; omega
    apply List.mem_flatMap.mpr
    refine ⟨i,List.mem_range.mpr (by omega),?_⟩
    apply List.mem_map.mpr
    refine ⟨j,List.mem_filter.mpr ⟨List.mem_range.mpr (by omega),decide_eq_true (by omega)⟩,?_⟩
    apply Prod.ext <;> simp only [Prod.fst,Prod.snd] <;> omega

theorem trianglePoints_nodup (al au bl bu c : Int) :
    (trianglePoints al au bl bu c).Nodup := by
  unfold trianglePoints
  apply nodup_flatMap_separated _ _ List.nodup_range
  · intro i _
    unfold triangleRow
    apply nodup_map_injective
    · intro j k he
      have hy := congrArg Prod.snd he
      simp only [Prod.snd] at hy
      omega
    · exact List.Nodup.sublist List.filter_sublist List.nodup_range
  · intro i hi j hj x hx y hy he
    obtain ⟨s,_,hs⟩ := List.mem_map.mp hx
    obtain ⟨t,_,ht⟩ := List.mem_map.mp hy
    have h0 := congrArg Prod.fst (hs.trans (he.trans ht.symm))
    simp only [Prod.fst] at h0
    omega

def rectanglePoints (al au bl bu : Int) : List (Int×Int) :=
    trianglePoints al au bl bu (bl-au)

theorem rectanglePoints_mem (al au bl bu x y : Int) :
    (x,y)∈rectanglePoints al au bl bu ↔ al≤x ∧ x≤au ∧ bl≤y ∧ y≤bu := by
  rw [rectanglePoints,trianglePoints_mem]
  omega

theorem triangleBox2_rectangle (al au bl bu : Int) :
    triangleBox2 al au bl bu (bl-au)=rectangleBox2 al au bl bu := by
  by_cases ha : al≤au
  · by_cases hb : bl≤bu
    · have h0 : max 0 (bu-(bl-au)+1-al)=bu-(bl-au)+1-al := by omega
      have h1 : max 0 (bu-(bl-au)-au)=bu-(bl-au)-au := by omega
      have h2 : max 0 (bl-(bl-au)-al)=bl-(bl-au)-al := by omega
      have h3 : max 0 (bl-(bl-au)-au-1)=0 := by omega
      have h4 : max 0 (au-al+1)=au-al+1 := by omega
      have h5 : max 0 (bu-bl+1)=bu-bl+1 := by omega
      have hab : al≤au ∧ bl≤bu := ⟨ha,hb⟩
      simp only [triangleBox2,rectangleBox2,tri2,pos,hab,ite_true,h0,h1,h2,h3,h4,h5]
      grind
    · have hh : ¬(al≤au ∧ bl≤bu) := by omega
      have hz : max 0 (bu-bl+1)=0 := by omega
      simp [triangleBox2,rectangleBox2,pos,hh,hz]
  · have hh : ¬(al≤au ∧ bl≤bu) := by omega
    have hz : max 0 (au-al+1)=0 := by omega
    simp [triangleBox2,rectangleBox2,pos,hh,hz]

theorem rectanglePoints_length (al au bl bu : Int) :
    2*((rectanglePoints al au bl bu).length:Int)=rectangleBox2 al au bl bu := by
  rw [rectanglePoints,trianglePoints_length,triangleBox2_rectangle]

def boxPoints (triangle : Bool) (al au bl bu c : Int) : List (Int×Int) :=
    if triangle then trianglePoints al au bl bu c else rectanglePoints al au bl bu

def boxCount2 (triangle : Bool) (al au bl bu c : Int) : Int :=
    if triangle then triangleBox2 al au bl bu c else rectangleBox2 al au bl bu

theorem boxPoints_mem (triangle : Bool) (al au bl bu c x y : Int) :
    (x,y)∈boxPoints triangle al au bl bu c ↔
      al≤x ∧ x≤au ∧ bl≤y ∧ y≤bu ∧ (triangle=true → x+c≤y) := by
  cases triangle <;> simp [boxPoints,trianglePoints_mem,rectanglePoints_mem]

theorem boxPoints_nodup (triangle : Bool) (al au bl bu c : Int) :
    (boxPoints triangle al au bl bu c).Nodup := by
  cases triangle <;> exact trianglePoints_nodup _ _ _ _ _

theorem boxPoints_length (triangle : Bool) (al au bl bu c : Int) :
    2*((boxPoints triangle al au bl bu c).length:Int)=boxCount2 triangle al au bl bu c := by
  cases triangle
  · exact rectanglePoints_length _ _ _ _
  · exact trianglePoints_length _ _ _ _ _

theorem boxPoints_clip (triangle : Bool) (al au bl bu c xl xu yl yu : Int) :
    ((boxPoints triangle al au bl bu c).filter
      (fun p => decide (xl≤p.1 ∧ p.1≤xu ∧ yl≤p.2 ∧ p.2≤yu))).Perm
      (boxPoints triangle (max al xl) (min au xu) (max bl yl) (min bu yu) c) := by
  apply (List.perm_ext_iff_of_nodup
    (List.Nodup.sublist List.filter_sublist (boxPoints_nodup _ _ _ _ _ _))
    (boxPoints_nodup _ _ _ _ _ _)).mpr
  intro p
  obtain ⟨x,y⟩ := p
  simp only [List.mem_filter,boxPoints_mem,decide_eq_true_eq,Prod.fst,Prod.snd]
  cases triangle <;> simp_all <;> omega

#print axioms trianglePoints_mem
#print axioms trianglePoints_nodup
#print axioms rectanglePoints_length
#print axioms boxPoints_clip
end LuRazLattice
