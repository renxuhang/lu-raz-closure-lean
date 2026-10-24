import SixRowDifferencePredicates
import EnumerationCounting

namespace LuRazSixRowClosure.Difference
open LuRazClosure LuRazEnumeration
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false

def regularParams (q : Nat) : List Nat :=
  List.range' 4 (q-2) ++ List.range' (q+4) (q-3)
def pParams (q : Nat) : List Nat :=
  List.range' 4 (q-2) ++ List.range' (q+3) (q-1)
def dParams (q : Nat) : List Nat :=
  0 :: (List.range' 4 (q-2) ++ List.range' (q+3) (q-3))
def rightParams (q : Nat) : List Nat :=
  0 :: List.range' (3*q+2) (q-2)
def c14Params (q : Nat) : List Nat :=
  List.range' (2*q+4) (q-2) ++ List.range' (3*q+3) (q-3)

theorem regularParams_exact (q : Nat) (hq : 4≤q) (t : Nat) :
    t∈regularParams q ↔ P q t ∧ t≤2*q ∧ t≠q+3 := by
  simp [regularParams,range_mem,P]
  omega

theorem pParams_exact (q : Nat) (hq : 4≤q) (t : Nat) : t∈pParams q ↔ P q t := by
  simp [pParams,range_mem,P]
  omega

theorem dParams_exact (q : Nat) (hq : 4≤q) (t : Nat) :
    t∈dParams q ↔ t=0 ∨ (P q t ∧ t≤2*q-1) := by
  simp [dParams,range_mem,P]
  omega

theorem rightParams_exact (q : Nat) (hq : 4≤q) (t : Nat) :
    t∈rightParams q ↔ t=0 ∨ (3*q+2≤t ∧ t≤4*q-1) := by
  simp [rightParams,range_mem]
  omega

theorem c14Params_exact (q : Nat) (hq : 4≤q) (t : Nat) :
    t∈c14Params q ↔ 2*q+4≤t ∧ t≤4*q-1 ∧ t≠3*q+2 := by
  simp [c14Params,range_mem]
  omega

def removedGroup (q : Nat) : Nat → List RemovedForm
  | 0 => [.r2]
  | 1 => [.r3]
  | 2 => (List.range' 0 2).map RemovedForm.r4
  | 3 => [.r5]
  | 4 => (regularParams q).map RemovedForm.r6regular
  | 5 => [.r6exception]
  | 6 => (dParams q).map RemovedForm.r6d
  | 7 => (List.range' 0 3).map RemovedForm.r7fresh
  | 8 => (List.range' 4 (q-2)).map RemovedForm.r7e
  | 9 => (List.range' 4 (2*q-4)).map RemovedForm.r7d
  | 10 => (List.range' (2*q+2) 2).map RemovedForm.r10
  | 11 => (List.range' 5 (2*q-3)).map RemovedForm.r11j
  | 12 => (List.range' (q+4) (q-2)).map RemovedForm.r11aj
  | 13 => (List.range' (2*q+2) 2).map RemovedForm.r11ak
  | 14 => (List.range' 0 4).map RemovedForm.r12
  | 15 => (List.range' (2*q+2) (q-2)).map RemovedForm.r13cj
  | 16 => (List.range' (2*q+2) (2*q-4)).map RemovedForm.r13zj
  | 17 => (List.range' (2*q+2) (q-2)).map RemovedForm.r13czj
  | 18 => (List.range' 0 3).map RemovedForm.r13points
  | 19 => (List.range' 0 3).map RemovedForm.r14points
  | 20 => (List.range' (2*q+4) (2*q-4)).map RemovedForm.r14line
  | 21 => (c14Params q).map RemovedForm.r14c
  | 22 => (List.range' 0 2).map RemovedForm.r15points
  | 23 => (List.range' 6 (2*q-3)).map RemovedForm.r15right
  | 24 => (List.range' (q+4) (q-1)).map RemovedForm.r15gap
  | 25 => (List.range' (2*q+4) (2*q-4)).map RemovedForm.r15line
  | 26 => (List.range' 4 (q-2)).map (fun p => RemovedForm.r15short p (2*q+2)) ++ (List.range' 4 (q-2)).map (fun p => RemovedForm.r15short p (2*q+3))
  | _ => []

def removedList (q : Nat) : List RemovedForm :=
  (List.range 27).flatMap (removedGroup q)

theorem removedGroup_exact (q : Nat) (hq : 4≤q) (k : Nat) (hk : k<27) (z : RemovedForm) :
    z∈removedGroup q k ↔ z.Valid q ∧ z.tag=k := by
  have hc : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨ k=7 ∨ k=8 ∨ k=9 ∨ k=10 ∨ k=11 ∨ k=12 ∨ k=13 ∨ k=14 ∨ k=15 ∨ k=16 ∨ k=17 ∨ k=18 ∨ k=19 ∨ k=20 ∨ k=21 ∨ k=22 ∨ k=23 ∨ k=24 ∨ k=25 ∨ k=26 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals cases z <;>
    simp [removedGroup,List.mem_map,LuRazThreeRow.exists_fixed,range_mem,regularParams_exact q hq,
      pParams_exact q hq,dParams_exact q hq,rightParams_exact q hq,c14Params_exact q hq,
      RemovedForm.Valid,RemovedForm.tag] <;> omega

theorem removedList_exact (q : Nat) (hq : 4≤q) (z : RemovedForm) :
    z∈removedList q ↔ z.Valid q := by
  constructor
  · intro h
    obtain ⟨k,hk,hz⟩ := List.mem_flatMap.mp h
    exact ((removedGroup_exact q hq k (List.mem_range.mp hk) z).mp hz).1
  · intro hz
    have ht : z.tag<27 := by cases z <;> simp [RemovedForm.tag]
    exact List.mem_flatMap.mpr ⟨z.tag,List.mem_range.mpr ht,
      (removedGroup_exact q hq z.tag ht z).mpr ⟨hz,rfl⟩⟩

theorem removedList_length (q : Nat) (hq : 4≤q) :
    ((removedList q).length : Int)=25*(q : Int)-24 := by
  simp [removedList,List.range_succ,removedGroup,regularParams,pParams,dParams,rightParams,c14Params]
  omega

def addedGroup (q : Nat) : Nat → List AddedForm
  | 0 => (List.range' 0 2).map AddedForm.n4
  | 1 => (List.range' 0 7).map AddedForm.n5
  | 2 => (regularParams q).map AddedForm.n6regular
  | 3 => [.n6exception]
  | 4 => (pParams q).map AddedForm.n6e
  | 5 => (regularParams q).map AddedForm.n7regular
  | 6 => [.n7exception]
  | 7 => (rightParams q).map AddedForm.n7right
  | 8 => [.n7point]
  | 9 => (List.range' (2*q+1) 3).map AddedForm.n10
  | 10 => (List.range' 5 (2*q-3)).map AddedForm.n11j
  | 11 => (List.range' (q+4) (q-2)).map AddedForm.n11aj
  | 12 => (List.range' (2*q+2) 2).map AddedForm.n11ak
  | 13 => (List.range' (2*q+2) (q-1)).map AddedForm.n13plain
  | 14 => (List.range' (2*q+2) (q-2)).map AddedForm.n13isolated
  | 15 => (List.range' (3*q+1) (q-3)).map AddedForm.n13right
  | _ => []

def addedList (q : Nat) : List AddedForm :=
  (List.range 16).flatMap (addedGroup q)

theorem addedGroup_exact (q : Nat) (hq : 4≤q) (k : Nat) (hk : k<16) (z : AddedForm) :
    z∈addedGroup q k ↔ z.Valid q ∧ z.tag=k := by
  have hc : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨ k=7 ∨ k=8 ∨ k=9 ∨ k=10 ∨ k=11 ∨ k=12 ∨ k=13 ∨ k=14 ∨ k=15 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals cases z <;>
    simp [addedGroup,List.mem_map,LuRazThreeRow.exists_fixed,range_mem,regularParams_exact q hq,
      pParams_exact q hq,dParams_exact q hq,rightParams_exact q hq,c14Params_exact q hq,
      AddedForm.Valid,AddedForm.tag] <;> omega

theorem addedList_exact (q : Nat) (hq : 4≤q) (z : AddedForm) :
    z∈addedList q ↔ z.Valid q := by
  constructor
  · intro h
    obtain ⟨k,hk,hz⟩ := List.mem_flatMap.mp h
    exact ((addedGroup_exact q hq k (List.mem_range.mp hk) z).mp hz).1
  · intro hz
    have ht : z.tag<16 := by cases z <;> simp [AddedForm.tag]
    exact List.mem_flatMap.mpr ⟨z.tag,List.mem_range.mpr ht,
      (addedGroup_exact q hq z.tag ht z).mpr ⟨hz,rfl⟩⟩

theorem addedList_length (q : Nat) (hq : 4≤q) :
    ((addedList q).length : Int)=13*(q : Int)-8 := by
  simp [addedList,List.range_succ,addedGroup,regularParams,pParams,dParams,rightParams,c14Params]
  omega

end LuRazSixRowClosure.Difference

