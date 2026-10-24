import Exhaustive134Exact
namespace LuRazThreeRow
open LuRazClosure LuRazEnumeration
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000
set_option linter.unusedSimpArgs false

def Normal134.tag : Normal134 → Nat
  | .old (.ej _) => 0 | .old (.cj _) => 1 | .old (.zj _) => 2
  | .old (.czj _) => 3 | .old (.zjb _) => 4 | .old (.cjb _) => 5
  | .fresh .lp => 6 | .fresh .lb => 7 | .fresh (.zz _) => 8 | .fresh (.cz _) => 9
  | _ => 10
def normal134Group (q : Nat) : Nat → List Normal134
  | 0 => [.old (.ej 5)]
  | 1 => ((List.range' (2*q+2) (2*q-4)).filter (fun b => decide (b≠3*q))).map (fun b => Normal134.old (.cj b))
  | 2 => (List.range' (2*q+2) (2*q-4)).map (fun b => Normal134.old (.zj b))
  | 3 => (List.range' (2*q+2) (q-2)).map (fun b => Normal134.old (.czj b))
  | 4 => (List.range' (2*q+2) (q-1)).map (fun b => Normal134.old (.zjb b))
  | 5 => (List.range' (2*q+2) (q-2)).map (fun b => Normal134.old (.cjb b))
  | 6 => [.fresh .lp]
  | 7 => [.fresh .lb]
  | 8 => (List.range' (2*q+1) (2*q-3)).map (fun b => Normal134.fresh (.zz b))
  | 9 => (List.range' (2*q+2) (q-2)).map (fun b => Normal134.fresh (.cz b))
  | _ => []
def normal134List (q : Nat) : List Normal134 := (List.range 10).flatMap (normal134Group q)

theorem normal134_group_exact (q : Nat) (hq : 4≤q) (k : Nat) (hk : k<10) (z : Normal134) :
    z∈normal134Group q k ↔ z.Valid q ∧ z.tag=k := by
  have hc : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨ k=7 ∨ k=8 ∨ k=9 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals cases z <;> rename_i z <;> cases z <;>
    simp [normal134Group,List.mem_map,range_mem,Normal134.Valid,Valid134,Cut134,
      NF134.Valid,Fresh134.Valid,Normal134.tag] <;> omega

theorem normal134_list_exact (q : Nat) (hq : 4≤q) (z : Normal134) : z∈normal134List q ↔ z.Valid q := by
  constructor
  · intro h
    obtain ⟨k,hk,hz⟩ := List.mem_flatMap.mp h
    exact ((normal134_group_exact q hq k (List.mem_range.mp hk) z).mp hz).1
  · intro hz
    have ht : z.tag<10 := by
      cases z <;> rename_i z <;> cases z <;> simp_all [Normal134.tag,Normal134.Valid,Valid134,Cut134]
    exact List.mem_flatMap.mpr ⟨z.tag,List.mem_range.mpr ht,
      (normal134_group_exact q hq _ ht z).mpr ⟨hz,rfl⟩⟩

theorem normal134_group_nodup (q k : Nat) (hk : k<10) : (normal134Group q k).Nodup := by
  have hc : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨ k=7 ∨ k=8 ∨ k=9 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl 
  · simp [normal134Group]
  · apply nodup_map_injective (fun b => Normal134.old (.cj b))
      (fun _ _ h => NF134.cj.inj (Normal134.old.inj h))
    exact List.Nodup.sublist List.filter_sublist List.nodup_range'
  · apply nodup_map_injective (fun b => Normal134.old (.zj b))
      (fun _ _ h => NF134.zj.inj (Normal134.old.inj h))
    exact List.nodup_range'
  · apply nodup_map_injective (fun b => Normal134.old (.czj b))
      (fun _ _ h => NF134.czj.inj (Normal134.old.inj h))
    exact List.nodup_range'
  · apply nodup_map_injective (fun b => Normal134.old (.zjb b))
      (fun _ _ h => NF134.zjb.inj (Normal134.old.inj h))
    exact List.nodup_range'
  · apply nodup_map_injective (fun b => Normal134.old (.cjb b))
      (fun _ _ h => NF134.cjb.inj (Normal134.old.inj h))
    exact List.nodup_range'
  · simp [normal134Group]
  · simp [normal134Group]
  · apply nodup_map_injective (fun b => Normal134.fresh (.zz b))
      (fun _ _ h => Fresh134.zz.inj (Normal134.fresh.inj h))
    exact List.nodup_range'
  · apply nodup_map_injective (fun b => Normal134.fresh (.cz b))
      (fun _ _ h => Fresh134.cz.inj (Normal134.fresh.inj h))
    exact List.nodup_range'

theorem normal134_list_nodup (q : Nat) (hq : 4≤q) : (normal134List q).Nodup := by
  apply nodup_flatMap_separated _ _ List.nodup_range
  · intro k hk
    exact normal134_group_nodup q k (List.mem_range.mp hk)
  · intro k hk j hj z hz w hw he
    have hzk := ((normal134_group_exact q hq k (List.mem_range.mp hk) z).mp hz).2
    have hwj := ((normal134_group_exact q hq j (List.mem_range.mp hj) w).mp hw).2
    subst w
    omega

theorem normal134_list_length (q : Nat) (hq : 4≤q) : ((normal134List q).length : Int)=10*(q:Int)-16 := by
  have hm : 3*q∈List.range' (2*q+2) (2*q-4) := (range_mem _ _ _).mpr (by omega)
  have hf := filter_ne_length (List.range' (2*q+2) (2*q-4)) List.nodup_range' (3*q) hm
  simp only [List.length_range'] at hf
  simp at hf
  have hr : List.range 10=[0,1,2,3,4,5,6,7,8,9] := by decide
  unfold normal134List
  rw [hr]
  simp [normal134Group,List.length_map,List.length_range']
  omega

def new134Members (q : Nat) : List (Nat → Prop) := (normal134List q).map (Normal134.eval q)

theorem new134_members_exact (q : Nat) (hq : 4≤q) (R : Nat → Prop) :
    R∈new134Members q ↔ Generated q R ∧ Core134 R := by
  rw [core134_exhaustive q hq R]
  constructor
  · intro h
    obtain ⟨z,hz,he⟩ := List.mem_map.mp h
    exact ⟨z,(normal134_list_exact q hq z).mp hz,fun e => Iff.of_eq (congrFun he.symm e)⟩
  · rintro ⟨z,hz,he⟩
    exact List.mem_map.mpr ⟨z,(normal134_list_exact q hq z).mpr hz,funext (fun e => propext (he e).symm)⟩

theorem new134_members_nodup (q : Nat) (hq : 4≤q) : (new134Members q).Nodup := by
  apply nodup_map_on _ _ (normal134_list_nodup q hq)
  intro a ha b hb he
  exact normal134_unique q hq a b ((normal134_list_exact q hq a).mp ha) ((normal134_list_exact q hq b).mp hb)
    (fun e => Iff.of_eq (congrFun he e))

theorem core134_new_cardinality (q : Nat) (hq : 4≤q) :
    ∃ l : List (Nat → Prop), l.Nodup ∧
      (∀ R, R∈l ↔ Generated q R ∧ Core134 R) ∧ (l.length : Int)=10*(q:Int)-16 :=
  ⟨new134Members q,new134_members_nodup q hq,new134_members_exact q hq,
    by simpa only [new134Members,List.length_map] using normal134_list_length q hq⟩

end LuRazThreeRow
