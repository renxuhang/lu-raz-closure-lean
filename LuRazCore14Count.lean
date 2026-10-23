import LuRazCore14Enumeration

namespace LuRazClosure
open LuRazEnumeration
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

theorem scalar_middle2 (x y : Int) : x*(2*y)=2*(x*y) := Int.mul_left_comm x 2 y
theorem scalar_middle3 (x y : Int) : x*(3*y)=3*(x*y) := Int.mul_left_comm x 3 y
theorem scalar_middle4 (x y : Int) : x*(4*y)=4*(x*y) := Int.mul_left_comm x 4 y

theorem early_pairs_count (q : Nat) (hq : 4 ≤ q) (C : Nat → Nat → NF14) :
    2*((pairs C 5 (q-1) (g q) (fun a => 4*q-2-g q a)).length : Int) =
      ((q:Int)-1)*(3*(q:Int)-6) := by
  have h := pairs_length_linear C 5 (q-1) (g q) (fun a => 4*q-2-g q a) (2*(q:Int)+1) (by
    intro a ha
    unfold g
    split <;> omega)
  have hc : ((q-1:Nat):Int)=(q:Int)-1 := by omega
  rw [hc] at h
  simp only [Int.mul_add,Int.mul_sub,Int.add_mul,Int.sub_mul,Int.mul_assoc] at h ⊢
  simp only [scalar_middle2,scalar_middle3,scalar_middle4] at h ⊢
  omega

theorem late_pairs_count (q : Nat) (hq : 4 ≤ q) (C : Nat → Nat → NF14) :
    2*((pairs C (q+4) (q-2) (g q) (fun a => 4*q-2-g q a)).length : Int) =
      ((q:Int)-2)*((q:Int)-1) := by
  have h := pairs_length_linear C (q+4) (q-2) (g q) (fun a => 4*q-2-g q a) (2*(q:Int)+2) (by
    intro a ha
    unfold g
    split <;> omega)
  have hc : ((q-2:Nat):Int)=(q:Int)-2 := by omega
  have hs : ((q+4:Nat):Int)=(q:Int)+4 := by omega
  rw [hc,hs] at h
  simp only [Int.mul_add,Int.mul_sub,Int.add_mul,Int.sub_mul,Int.mul_assoc] at h ⊢
  simp only [scalar_middle2,scalar_middle3,scalar_middle4] at h ⊢
  omega

theorem enum14_base_split (q : Nat) (hq : 4 ≤ q) :
    enum14Group q 0 =
      pairs NF14.base 5 (q-1) (g q) (fun a => 4*q-2-g q a) ++
      pairs NF14.base (q+4) (q-2) (g q) (fun a => 4*q-2-g q a) := by
  have hs : 5+(q-1)=q+4 := by omega
  have hn : (q-1)+(q-2)=2*q-3 := by omega
  simpa only [hs,hn,enum14Group] using
    pairs_split NF14.base 5 (q-1) (q-2) (g q) (fun a => 4*q-2-g q a)

theorem enum14_base_count (q : Nat) (hq : 4 ≤ q) :
    2*((enum14Group q 0).length : Int)=4*((q:Int)-1)*((q:Int)-2) := by
  have h1 := early_pairs_count q hq NF14.base
  have h2 := late_pairs_count q hq NF14.base
  rw [enum14_base_split q hq,List.length_append,Int.natCast_add]
  simp only [Int.mul_add,Int.mul_sub,Int.add_mul,Int.sub_mul,Int.mul_assoc] at h1 h2 ⊢
  simp only [scalar_middle2,scalar_middle3,scalar_middle4] at h1 h2 ⊢
  omega

theorem enum14_agap_count (q : Nat) (hq : 4 ≤ q) :
    2*((enum14Group q 1).length : Int)=((q:Int)-2)*((q:Int)-1) :=
  late_pairs_count q hq NF14.agap

theorem enum14_bgap_split (q : Nat) (hq : 4 ≤ q) :
    enum14Group q 2 =
      pairs NF14.bgap 5 (q-1) (g q) (fun a => 3*q+1-g q a) ++
      pairs NF14.bgap (q+4) 1 (g q) (fun a => 3*q+1-g q a) := by
  have hs : 5+(q-1)=q+4 := by omega
  have hn : (q-1)+1=q := by omega
  simpa only [hs,hn,enum14Group] using
    pairs_split NF14.bgap 5 (q-1) 1 (g q) (fun a => 3*q+1-g q a)

theorem enum14_bgap_count (q : Nat) (hq : 4 ≤ q) :
    2*((enum14Group q 2).length : Int)=(q:Int)*((q:Int)-1)+2 := by
  have h := pairs_length_linear NF14.bgap 5 (q-1) (g q) (fun a => 3*q+1-g q a) ((q:Int)+4) (by
    intro a ha
    unfold g
    split <;> omega)
  have hc : ((q-1:Nat):Int)=(q:Int)-1 := by omega
  rw [hc] at h
  have hg : g q (q+4)=3*q := by unfold g; split <;> omega
  have hlast : (pairs NF14.bgap (q+4) 1 (g q) (fun a => 3*q+1-g q a)).length=1 := by
    simp [pairs,hg]
  rw [enum14_bgap_split q hq,List.length_append,Int.natCast_add,hlast]
  simp only [Int.mul_add,Int.mul_sub,Int.add_mul,Int.sub_mul,Int.mul_assoc] at h ⊢
  simp only [scalar_middle2,scalar_middle3,scalar_middle4] at h ⊢
  omega

theorem enum14_joined_count (q : Nat) (hq : 4 ≤ q) :
    ((enum14Group q 3).length : Int)=2*(q:Int)-3 := by
  simp only [enum14Group,List.length_map,List.length_range']
  omega

theorem enum14_double_count (q : Nat) : ((enum14Group q 4).length : Int)=1 := by rfl

theorem enum14_ajoined_count (q : Nat) (hq : 4 ≤ q) :
    ((enum14Group q 5).length : Int)=(q:Int)-2 := by
  simp only [enum14Group,List.length_map,List.length_range']
  omega

theorem enum14_length (q : Nat) (hq : 4 ≤ q) :
    ((enum14 q).length : Int)=3*(q:Int)*(q:Int)-5*(q:Int)+2 := by
  have h0 := enum14_base_count q hq
  have h1 := enum14_agap_count q hq
  have h2 := enum14_bgap_count q hq
  have h3 := enum14_joined_count q hq
  have h4 := enum14_double_count q
  have h5 := enum14_ajoined_count q hq
  have he : enum14 q=enum14Group q 0 ++ enum14Group q 1 ++ enum14Group q 2 ++
      enum14Group q 3 ++ enum14Group q 4 ++ enum14Group q 5 := by
    have hr : List.range 6=[0,1,2,3,4,5] := by decide
    unfold enum14
    rw [hr]
    simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc]
  rw [he]
  simp only [List.length_append,Int.natCast_add]
  simp only [Int.mul_add,Int.mul_sub,Int.add_mul,Int.sub_mul,Int.mul_assoc] at h0 h1 h2 ⊢
  omega

end LuRazClosure

