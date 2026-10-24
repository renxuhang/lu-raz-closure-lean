import VariantFullTailAggregate
import VariantBetaDifferences
import VariantFixedTailCounts

namespace LuRazThreeRow
open LuRazClosure LuRazEnumeration
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000

theorem removed134_tail_count (q e : Nat) (hq : 4≤q) (he : 5≤e) (hen : e≤4*q) :
    CountAt ((removed134 q).map (NF134.eval q)) e=
      (removedTailGroups (q:Int) (e:Int)).getD 5 0 +
      (removedTailGroups (q:Int) (e:Int)).getD 6 0 +
      (removedTailGroups (q:Int) (e:Int)).getD 7 0 := by
  have hl : (removed134 q).map (NF134.eval q)=
      ((List.range' 6 (2*q-4)).map (fun a => NF134.eval q (.ej a))) ++
      ((List.range' (q+4) (q-2)).map (fun a => NF134.eval q (.aej a))) ++
      (((List.range 3).map NF134.extra).map (NF134.eval q)) := by
    have hr : List.range 3=[0,1,2] := by decide
    unfold removed134
    rw [hr]
    simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,removed134Group,
      List.map_append,List.map_map,Function.comp_def,List.append_assoc,hr]
  rw [hl]
  simp only [count_at_append]
  rw [removed134_right_tail q e hq he hen,removed134_gap_tail q e hq he hen,
    removed134_points_tail q e hq he hen]
  simp only [removedTailGroups,List.getD,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]

theorem fresh134_tail_count (q e : Nat) (hq : 4≤q) (he : 5≤e) (hen : e≤4*q) :
    CountAt ((fresh134List q).map (Fresh134.eval q)) e=
      (addedTailGroups (q:Int) (e:Int)).getD 3 0 +
      (addedTailGroups (q:Int) (e:Int)).getD 4 0 +
      (addedTailGroups (q:Int) (e:Int)).getD 5 0 := by
  have hl : (fresh134List q).map (Fresh134.eval q)=
      [Fresh134.eval q .lp,Fresh134.eval q .lb] ++
      ((List.range' (2*q+1) (2*q-3)).map (fun a => Fresh134.eval q (.zz a))) ++
      ((List.range' (2*q+2) (q-2)).map (fun a => Fresh134.eval q (.cz a))) := by
    simp only [fresh134List,List.map_append,List.map_cons,List.map_nil,List.map_map,Function.comp_def]
  rw [hl]
  simp only [count_at_append]
  rw [fresh134_points_tail q e hq he hen,fresh134_zz_tail q e hq he hen,
    fresh134_cz_tail q e hq he hen]
  simp only [addedTailGroups,List.getD,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]

theorem removed_tail_count (q e : Nat) (hq : 4≤q) (he : 5≤e) (hen : e≤4*q) :
    CountAt (VariantRemovedMembers q) e=(removedTailGroups (q:Int) (e:Int)).sum := by
  simp only [VariantRemovedMembers,count_at_append]
  rw [removed5_tail_count q e hq he hen,removed23_tail_eq q e hq he,
    removed123_tail_eq q e hq he,removed134_tail_count q e hq he hen,
    loss_members_tail_eq q e hq he hen]
  simp only [removedTailGroups,List.getD,List.getElem?_cons_zero,List.getElem?_cons_succ,
    Option.getD_some,List.sum_cons,List.sum_nil]
  omega

theorem added_tail_count (q e : Nat) (hq : 4≤q) (he : 5≤e) (hen : e≤4*q) :
    CountAt (VariantAddedMembers q) e=(addedTailGroups (q:Int) (e:Int)).sum := by
  simp only [VariantAddedMembers,count_at_append]
  rw [added5_tail_count q e hq he hen,fresh123_tail_count q e hq he hen,
    members12_tail_count q e hq he hen,fresh134_tail_count q e hq he hen,
    extra234_tail_eq q e hq he,add_full_members_tail_eq q e hq he hen]
  simp only [addedTailGroups,List.getD,List.getElem?_cons_zero,List.getElem?_cons_succ,
    Option.getD_some,List.sum_cons,List.sum_nil]
  omega

theorem delta_raw_tail (q e : Nat) (hq : 4≤q) (he : 5≤e) (hen : e≤4*q) :
    DeltaRaw q e=tailDelta (q:Int) (e:Int) := by
  unfold DeltaRaw tailDelta
  rw [removed_tail_count q e hq he hen,added_tail_count q e hq he hen]

end LuRazThreeRow
