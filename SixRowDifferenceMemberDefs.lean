import SixRowGlobalDifference
import SixRowDifferenceListsNodup

namespace LuRazSixRowClosure
open LuRazClosure LuRazEnumeration Difference
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

def RemovedMembers (q : Nat) : List (Nat → Prop) :=
  (removedList q).map (RemovedForm.eval q)

def AddedMembers (q : Nat) : List (Nat → Prop) :=
  (addedList q).map (AddedForm.eval q)

theorem removed_members_exact (q : Nat) (hq : 4≤q) (R : Nat → Prop) :
    R∈RemovedMembers q ↔ Removed q R := by
  constructor
  · intro h
    obtain ⟨z,hz,he⟩ := List.mem_map.mp h
    exact ⟨z,(removedList_exact q hq z).mp hz,fun e => Iff.of_eq (congrFun he e)⟩
  · rintro ⟨z,hz,he⟩
    exact List.mem_map.mpr ⟨z,(removedList_exact q hq z).mpr hz,
      funext (fun e => propext (he e))⟩

theorem added_members_exact (q : Nat) (hq : 4≤q) (R : Nat → Prop) :
    R∈AddedMembers q ↔ Added q R := by
  constructor
  · intro h
    obtain ⟨z,hz,he⟩ := List.mem_map.mp h
    exact ⟨z,(addedList_exact q hq z).mp hz,fun e => Iff.of_eq (congrFun he e)⟩
  · rintro ⟨z,hz,he⟩
    exact List.mem_map.mpr ⟨z,(addedList_exact q hq z).mpr hz,
      funext (fun e => propext (he e))⟩

theorem removed_members_difference_exact (q : Nat) (hq : 4≤q) (R : Nat → Prop) :
    R∈RemovedMembers q ↔ LuRazThreeRow.Generated q R ∧ ¬Generated q R :=
  (removed_members_exact q hq R).trans (removed_exact q hq R).symm

theorem added_members_difference_exact (q : Nat) (hq : 4≤q) (R : Nat → Prop) :
    R∈AddedMembers q ↔ Generated q R ∧ ¬LuRazThreeRow.Generated q R :=
  (added_members_exact q hq R).trans (added_exact q hq R).symm

theorem removed_members_length (q : Nat) (hq : 4≤q) :
    ((RemovedMembers q).length : Int)=25*(q:Int)-24 := by
  simpa only [RemovedMembers,List.length_map] using removedList_length q hq

theorem added_members_length (q : Nat) (hq : 4≤q) :
    ((AddedMembers q).length : Int)=13*(q:Int)-8 := by
  simpa only [AddedMembers,List.length_map] using addedList_length q hq

end LuRazSixRowClosure
