import LuRazCore123Enumeration
namespace LuRazClosure
open LuRazEnumeration
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

theorem enum123_high_length (q : Nat) (hq : 4≤q) :
    2*((enum123Group q 1).length : Int)=3*(q:Int)*(q:Int)-7*(q:Int)+4 := by
  let C := fun r s => NF123.high (rankP q s) (rankP q r)
  have hf := triangular_pairs_count C (2*q-3)
  have hl := triangular_pairs_count C (q-2)
  have hs := pairs_split C 0 (q-2) (q-1) (fun _ => 0) (fun r => r+1)
  have hn : 2*q-3=(q-2)+(q-1) := by omega
  have he : (pairs C 0 (2*q-3) (fun _ => 0) (fun r => r+1)).length=
      (pairs C 0 (q-2) (fun _ => 0) (fun r => r+1)).length+(enum123Group q 1).length := by
    rw [hn,hs,List.length_append]
    simp only [Nat.zero_add]
    rfl
  rw [he,Int.natCast_add] at hf
  have hc0 : ((2*q-3:Nat):Int)=2*(q:Int)-3 := by omega
  have hc1 : ((q-2:Nat):Int)=(q:Int)-2 := by omega
  rw [hc0] at hf
  rw [hc1] at hl
  have hqq : (q:Int)*(2*(q:Int))=2*((q:Int)*(q:Int)) := Int.mul_left_comm (q:Int) 2 (q:Int)
  simp only [Int.mul_add,Int.mul_sub,Int.add_mul,Int.sub_mul,Int.mul_assoc,hqq] at hf hl ⊢
  omega

theorem enum123_length (q : Nat) (hq : 4≤q) :
    2*((enum123 q).length : Int)=3*(q:Int)*(q:Int)+7*(q:Int)-14 := by
  have h0 : ((enum123Group q 0).length : Int)=(q:Int)-2 := by simp only [enum123Group,List.length_map,List.length_range']; omega
  have h1 := enum123_high_length q hq
  have h2 : ((enum123Group q 2).length : Int)=1 := rfl
  have h3 : ((enum123Group q 3).length : Int)=(q:Int)-2 := by simp only [enum123Group,List.length_map,List.length_range']; omega
  have h4 : ((enum123Group q 4).length : Int)=1 := rfl
  have h5 : ((enum123Group q 5).length : Int)=2*(q:Int)-4 := by simpa only [enum123Group,enum23Group,List.length_map] using enum23_creg_count q hq
  have h6 : ((enum123Group q 6).length : Int)=1 := rfl
  have h7 : ((enum123Group q 7).length : Int)=2*(q:Int)-2 := by simp only [enum123Group,List.length_map,List.length_range']; omega
  have h8 : ((enum123Group q 8).length : Int)=(q:Int)-2 := by simp only [enum123Group,List.length_map,List.length_range']; omega
  have he : enum123 q=enum123Group q 0 ++ enum123Group q 1 ++ enum123Group q 2 ++ enum123Group q 3 ++ enum123Group q 4 ++ enum123Group q 5 ++ enum123Group q 6 ++ enum123Group q 7 ++ enum123Group q 8 := by
    have hr : List.range 9=[0,1,2,3,4,5,6,7,8] := by decide
    unfold enum123
    rw [hr]
    simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc]
  rw [he]
  simp only [List.length_append,Int.natCast_add]
  omega
end LuRazClosure
