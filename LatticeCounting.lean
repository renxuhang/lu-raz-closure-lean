import FrequencyBridge
import EnumerationCounting

namespace LuRazLattice
open LuRazCounting
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

def pos (x : Int) : Int := max 0 x
def tri2 (x : Int) : Int := pos x*(pos x+1)

theorem tri2_step (x : Int) : tri2 x-tri2 (x-1)=2*pos x := by
  by_cases hx : x≤0
  · have h1 : max 0 x=0 := by omega
    have h2 : max 0 (x-1)=0 := by omega
    simp [tri2,pos,h1,h2]
  · have h1 : max 0 x=x := by omega
    have h2 : max 0 (x-1)=x-1 := by omega
    simp only [tri2,pos,h1,h2]
    grind

theorem twice_sum_pos_desc (K s : Int) (n : Nat) :
    2*sumTo (fun i => pos (K-s-(i:Int))) n = tri2 (K-s)-tri2 (K-s-(n:Int)) := by
  induction n with
  | zero => simp [sumTo]
  | succ n ih =>
    have hs := tri2_step (K-s-(n:Int))
    have he : K-s-((n+1:Nat):Int)=K-s-(n:Int)-1 := by omega
    simp only [sumTo,Int.natCast_add,Int.natCast_one]
    rw [show K-s-((n:Int)+1)=K-s-(n:Int)-1 by omega]
    omega

def triangleBox2 (al au bl bu c : Int) : Int :=
  if al≤au ∧ bl≤bu then
    tri2 (bu-c+1-al)-tri2 (bu-c-au)-tri2 (bl-c-al)+tri2 (bl-c-au-1)
  else 0

def rectangleBox2 (al au bl bu : Int) : Int :=
  2*pos (au-al+1)*pos (bu-bl+1)

theorem interval_as_pos_difference (m : Nat) (v : Int) :
    intervalCount m v ((m:Int)-1) = pos ((m:Int)-v)-pos (-v) := by
  unfold intervalCount pos
  omega

theorem twice_sum_triangle_inner (al c bl bu : Int) (n : Nat) :
    2*sumTo (fun i => pos (bu-c+1-al-(i:Int))-pos (bl-c-al-(i:Int))) n =
      tri2 (bu-c+1-al)-tri2 (bu-c+1-al-(n:Int))-
      tri2 (bl-c-al)+tri2 (bl-c-al-(n:Int)) := by
  have hd : sumTo (fun i => pos (bu-c+1-al-(i:Int))-pos (bl-c-al-(i:Int))) n =
      sumTo (fun i => pos (bu-c+1-al-(i:Int))) n-
      sumTo (fun i => pos (bl-c-al-(i:Int))) n := by
    induction n with
    | zero => rfl
    | succ n ih => simp only [sumTo]; omega
  have h1 := twice_sum_pos_desc (bu-c+1) al n
  have h2 := twice_sum_pos_desc (bl-c) al n
  rw [hd]
  omega

theorem sum_map_range (f : Nat → Int) (n : Nat) :
    ((List.range n).map f).sum=sumTo f n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.range_succ,List.map_append,List.sum_append,ih,sumTo]

theorem count_shifted_interval (s lo hi : Int) (n : Nat) :
    (((List.range n).filter (fun (i:Nat) => decide (lo≤s+(i:Int) ∧ s+(i:Int)≤hi))).length : Int)=
      intervalCount n (lo-s) (hi-s) := by
  rw [←sumTo_filter]
  calc
    _=sumTo (fun i => mark (lo-s≤(i:Int) ∧ (i:Int)≤hi-s)) n := by
      apply sumTo_congr
      intro i _
      apply mark_congr
      omega
    _=_ := sumTo_interval n (lo-s) (hi-s)

def triangleRow (al bl bu c : Int) (i : Nat) : List (Int×Int) :=
    ((List.range (bu-bl+1).toNat).filter (fun (j:Nat) => decide (al+(i:Int)+c≤bl+(j:Int)))).map
      (fun (j:Nat) => (al+(i:Int),bl+(j:Int)))

def trianglePoints (al au bl bu c : Int) : List (Int×Int) :=
    (List.range (au-al+1).toNat).flatMap (triangleRow al bl bu c)

theorem triangleRow_length (al bl bu c : Int) (hb : bl≤bu) (i : Nat) :
    ((triangleRow al bl bu c i).length : Int)=
      pos (bu-c+1-al-(i:Int))-pos (bl-c-al-(i:Int)) := by
  have hnb : ((bu-bl+1).toNat:Int)=bu-bl+1 := by omega
  unfold triangleRow
  rw [List.length_map]
  have hc := count_shifted_interval bl (al+(i:Int)+c) bu (bu-bl+1).toNat
  have hf : (List.range (bu-bl+1).toNat).filter (fun (j:Nat) => decide (al+(i:Int)+c≤bl+(j:Int)))=
      (List.range (bu-bl+1).toNat).filter (fun (j:Nat) => decide (al+(i:Int)+c≤bl+(j:Int) ∧ bl+(j:Int)≤bu)) := by
    apply List.filter_congr
    intro j hj
    have hjb := List.mem_range.mp hj
    have hx : bl+(j:Int)≤bu := by omega
    simp only [hx,and_true]
  rw [hf,hc]
  unfold intervalCount pos
  omega

theorem trianglePoints_length (al au bl bu c : Int) :
    2*((trianglePoints al au bl bu c).length : Int)=triangleBox2 al au bl bu c := by
  by_cases ha : al≤au
  · by_cases hb : bl≤bu
    · have hna : ((au-al+1).toNat:Int)=au-al+1 := by omega
      have he : ((trianglePoints al au bl bu c).length : Int)=
          sumTo (fun i => pos (bu-c+1-al-(i:Int))-pos (bl-c-al-(i:Int))) (au-al+1).toNat := by
        unfold trianglePoints
        rw [LuRazEnumeration.int_length_flatMap]
        have hm :
            (List.range (au-al+1).toNat).map (fun (i:Nat) => ((triangleRow al bl bu c i).length:Int))=
            (List.range (au-al+1).toNat).map (fun (i:Nat) =>
              pos (bu-c+1-al-(i:Int))-pos (bl-c-al-(i:Int))) := by
          apply List.map_congr_left
          intro i _
          exact triangleRow_length al bl bu c hb i
        rw [hm,sum_map_range]
      rw [he,twice_sum_triangle_inner]
      unfold triangleBox2
      rw [ite_eq_left ⟨ha,hb⟩]
      rw [hna]
      rw [show bu-c+1-al-(au-al+1)=bu-c-au by omega,
        show bl-c-al-(au-al+1)=bl-c-au-1 by omega]
    · have hn : (bu-bl+1).toNat=0 := by omega
      simp [trianglePoints,triangleRow,hn,triangleBox2,hb]
      have hz (l : List Nat) : (l.map (fun _ => (0:Nat))).sum=0 := by
        induction l with
        | nil => rfl
        | cons a l ih => simp [ih]
      rw [hz]
      rfl
  · have hn : (au-al+1).toNat=0 := by omega
    simp [trianglePoints,hn,triangleBox2,ha]

#print axioms tri2_step
#print axioms twice_sum_pos_desc
#print axioms interval_as_pos_difference
#print axioms twice_sum_triangle_inner
#print axioms trianglePoints_length
end LuRazLattice
