import ThreeRowFullAdditions

namespace LuRazThreeRow
open LuRazClosure LuRazEnumeration
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

def AddFull.tag : AddFull → Nat
  | .right _ => 0 | .gap _ => 1 | .point => 2

def addFullGroup (q : Nat) : Nat → List AddFull
  | 0 => (List.range' 6 (2*q-3)).map AddFull.right
  | 1 => (List.range' (q+4) (q-1)).map AddFull.gap
  | 2 => [.point]
  | _ => []

def addFullList (q : Nat) : List AddFull := (List.range 3).flatMap (addFullGroup q)

theorem add_full_group_exact (q : Nat) (hq : 4≤q) (k : Nat) (hk : k<3) (z : AddFull) :
    z∈addFullGroup q k ↔ z.Valid q ∧ z.tag=k := by
  have hc : k=0 ∨ k=1 ∨ k=2 := by omega
  rcases hc with rfl | rfl | rfl
  all_goals cases z <;> simp [addFullGroup,List.mem_map,range_mem,AddFull.Valid,AddFull.tag] <;> omega

theorem add_full_list_exact (q : Nat) (hq : 4≤q) (z : AddFull) : z∈addFullList q ↔ z.Valid q := by
  constructor
  · intro h
    obtain ⟨k,hk,hz⟩ := List.mem_flatMap.mp h
    exact ((add_full_group_exact q hq k (List.mem_range.mp hk) z).mp hz).1
  · intro hz
    have ht : z.tag<3 := by cases z <;> simp [AddFull.tag]
    exact List.mem_flatMap.mpr ⟨z.tag,List.mem_range.mpr ht,
      (add_full_group_exact q hq _ ht z).mpr ⟨hz,rfl⟩⟩

theorem add_full_group_nodup (q k : Nat) (hk : k<3) : (addFullGroup q k).Nodup := by
  have hc : k=0 ∨ k=1 ∨ k=2 := by omega
  rcases hc with rfl | rfl | rfl
  · exact nodup_map_injective AddFull.right (fun _ _ h => AddFull.right.inj h) _ List.nodup_range'
  · exact nodup_map_injective AddFull.gap (fun _ _ h => AddFull.gap.inj h) _ List.nodup_range'
  · simp [addFullGroup]

theorem add_full_list_nodup (q : Nat) (hq : 4≤q) : (addFullList q).Nodup := by
  apply nodup_flatMap_separated _ _ List.nodup_range
  · intro k hk
    exact add_full_group_nodup q k (List.mem_range.mp hk)
  · intro k hk j hj z hz w hw he
    have hzk := ((add_full_group_exact q hq k (List.mem_range.mp hk) z).mp hz).2
    have hwj := ((add_full_group_exact q hq j (List.mem_range.mp hj) w).mp hw).2
    subst w
    omega

theorem add_full_list_length (q : Nat) (hq : 4≤q) : ((addFullList q).length : Int)=3*(q:Int)-3 := by
  have hr : List.range 3=[0,1,2] := by decide
  unfold addFullList
  rw [hr]
  simp [addFullGroup,List.length_map,List.length_range']
  omega

def addFullMembers (q : Nat) : List (Nat → Prop) := (addFullList q).map (AddFull.eval q)

theorem add_full_members_nodup (q : Nat) (hq : 4≤q) : (addFullMembers q).Nodup := by
  apply nodup_map_on _ _ (add_full_list_nodup q hq)
  intro a ha b hb he
  exact add_full_unique q hq a b ((add_full_list_exact q hq a).mp ha) ((add_full_list_exact q hq b).mp hb)
    (fun e => Iff.of_eq (congrFun he e))

/-- There are at least 3q-3 rigorously constructed new full-core members outside the old closure. -/
theorem full_addition_cardinality (q : Nat) (hq : 4≤q) :
    ∃ l : List (Nat → Prop), l.Nodup ∧
      (∀ R∈l, Generated q R ∧ CoreFull R ∧ ¬LuRazClosure.Generated q R) ∧
      (l.length : Int)=3*(q:Int)-3 := by
  refine ⟨addFullMembers q,add_full_members_nodup q hq,?_,?_⟩
  · intro R hR
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hR
    have hv := (add_full_list_exact q hq z).mp hz
    exact ⟨add_full_generated q hq z hv,add_full_core q hq z hv,add_full_not_old q hq z hv⟩
  · simpa only [addFullMembers,List.length_map] using add_full_list_length q hq

end LuRazThreeRow
