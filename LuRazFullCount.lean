import LuRazFullEnumeration
namespace LuRazClosure
open LuRazEnumeration
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000
set_option linter.unusedSimpArgs false

theorem enumFull_leftGap_count (q : Nat) (hq : 4≤q) :
    2*((enumFullGroup q 10).length : Int)=(2*(q:Int)-5)*(2*(q:Int)-4) := by
  have h := pairs_length_linear NFFull.leftGap 5 (2*q-5) (fun p => p+2) (fun p => 2*q-p) (2*(q:Int)) (by intro p hp; omega)
  have hc : ((2*q-5:Nat):Int)=2*(q:Int)-5 := by omega
  rw [hc] at h
  have hs : ((5:Nat):Int)=5 := by decide
  rw [hs] at h
  have ha : 2*(2*(q:Int))-2*(5:Int)-(2*(q:Int)-5)+1=2*(q:Int)-4 := by omega
  rw [ha] at h
  exact h

theorem enumFull_rightGap_count (q : Nat) (hq : 4≤q) :
    2*((enumFullGroup q 12).length : Int)=(2*(q:Int)-3)*(2*(q:Int)-2) := by
  have h := pairs_length_linear NFFull.rightGap (2*q+2) (2*q-3) (fun b => b+2) (fun b => 4*q-b-1) (4*(q:Int)-1) (by intro b hb; omega)
  have hc0 : ((2*q-3:Nat):Int)=2*(q:Int)-3 := by omega
  have hc1 : ((2*q+2:Nat):Int)=2*(q:Int)+2 := by omega
  rw [hc0,hc1] at h
  have ha : 2*(4*(q:Int)-1)-2*(2*(q:Int)+2)-(2*(q:Int)-3)+1=2*(q:Int)-2 := by omega
  rw [ha] at h
  exact h

theorem enumFull_isolated_count (q : Nat) (hq : 4≤q) :
    ((enumFullGroup q 13).length : Int)=((q:Int)-2)*((q:Int)-2) := by
  have h := pairs_length_constant NFFull.isolatedR (2*q+2) (q-2) (fun _ => 3*q+3) (q-2)
  change (enumFullGroup q 13).length=(q-2)*(q-2) at h
  rw [h,Int.natCast_mul]
  have hc : ((q-2:Nat):Int)=(q:Int)-2 := by omega
  rw [hc]

theorem enumFull_length (q : Nat) (hq : 4≤q) :
    ((enumFull q).length : Int)=5*(q:Int)*(q:Int)-5*(q:Int)+1 := by
  have h0 : (enumFullGroup q 0).length=2 := by simp [enumFullGroup]
  have h1 : (enumFullGroup q 1).length=q-1 := by simp [enumFullGroup]
  have h2 : (enumFullGroup q 2).length=q-3 := by simp [enumFullGroup]
  have h3 : (enumFullGroup q 3).length=2 := by simp [enumFullGroup]
  have h4 : (enumFullGroup q 4).length=q-2 := by simp [enumFullGroup]
  have h6 : (enumFullGroup q 6).length=2*q-4 := by simp [enumFullGroup]
  have h7 : (enumFullGroup q 7).length=1 := by simp [enumFullGroup]
  have h8 : (enumFullGroup q 8).length=2*q-2 := by simp [enumFullGroup]
  have h9 : (enumFullGroup q 9).length=2*q-4 := by simp [enumFullGroup]
  have h11 : (enumFullGroup q 11).length=1 := by simp [enumFullGroup]
  have h5 : ((enumFullGroup q 5).length : Int)=4*(q:Int)-6 := by
    have h := pairs_length_constant NFFull.noH1Short 4 (2*q-3) (fun _ => 0) 2
    change (enumFullGroup q 5).length=(2*q-3)*2 at h
    rw [h]
    omega
  have h10 := enumFull_leftGap_count q hq
  have h12 := enumFull_rightGap_count q hq
  have h13 := enumFull_isolated_count q hq
  have he : enumFull q=enumFullGroup q 0 ++ enumFullGroup q 1 ++ enumFullGroup q 2 ++ enumFullGroup q 3 ++ enumFullGroup q 4 ++ enumFullGroup q 5 ++ enumFullGroup q 6 ++ enumFullGroup q 7 ++ enumFullGroup q 8 ++ enumFullGroup q 9 ++ enumFullGroup q 10 ++ enumFullGroup q 11 ++ enumFullGroup q 12 ++ enumFullGroup q 13 := by
    have hr : List.range 14=[0,1,2,3,4,5,6,7,8,9,10,11,12,13] := by decide
    unfold enumFull
    rw [hr]
    simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc]
  rw [he]
  simp only [List.length_append,Int.natCast_add]
  have hqq : (q:Int)*(2*(q:Int))=2*((q:Int)*(q:Int)) := Int.mul_left_comm (q:Int) 2 (q:Int)
  simp only [Int.mul_add,Int.mul_sub,Int.add_mul,Int.sub_mul,Int.mul_assoc,hqq] at h10 h12 h13 ⊢
  omega
end LuRazClosure
