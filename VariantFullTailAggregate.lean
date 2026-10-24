import VariantTailRangeCounts

namespace LuRazThreeRow
open LuRazClosure LuRazEnumeration LuRazCounting LuRazLattice
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

theorem loss_members_tail_eq (q e : Nat) (hq : 4≤q) (he : 5≤e) (hen : e≤4*q) :
    CountAt (lossMembers q) e =
      (removedTailGroups (q:Int) (e:Int)).getD 8 0 +
      (removedTailGroups (q:Int) (e:Int)).getD 9 0 +
      (removedTailGroups (q:Int) (e:Int)).getD 10 0 +
      (removedTailGroups (q:Int) (e:Int)).getD 11 0 := by
  have hl : lossMembers q =
      ((List.range' (2*q+4) (2*q-4)).map (fun a => NFFull.eval q (.noH1ZL a))) ++
      [NFFull.eval q .noH1Exception,NFFull.eval q (.noH2 (4*q))] ++
      ((List.range' (2*q+2) (2*q-4)).map (fun a => NFFull.eval q (.rightGap a (4*q)))) ++
      ((List.range' (2*q+2) (q-2)).map (fun a => NFFull.eval q (.isolatedR a (4*q)))) := by
    have hr : List.range 5=[0,1,2,3,4] := by decide
    unfold lossMembers lossList
    rw [hr]
    simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,lossGroup,List.map_append,
      List.map_cons,List.map_nil,List.map_map,Function.comp_def,List.append_assoc,List.cons_append,List.nil_append]
  rw [hl]
  simp only [count_at_append]
  rw [loss_left_tail q e hq he hen,loss_points_tail q e hq he hen,
    loss_right_tail q e hq he hen,loss_isolated_tail q e hq he hen]
  simp only [removedTailGroups,List.getD,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]

theorem add_full_members_tail_eq (q e : Nat) (hq : 4≤q) (he : 5≤e) (hen : e≤4*q) :
    CountAt (addFullMembers q) e =
      (addedTailGroups (q:Int) (e:Int)).getD 8 0 +
      (addedTailGroups (q:Int) (e:Int)).getD 9 0 +
      (addedTailGroups (q:Int) (e:Int)).getD 10 0 := by
  have hl : addFullMembers q =
      ((List.range' 6 (2*q-3)).map (fun a => AddFull.eval q (.right a))) ++
      ((List.range' (q+4) (q-1)).map (fun a => AddFull.eval q (.gap a))) ++
      [AddFull.eval q .point] := by
    have hr : List.range 3=[0,1,2] := by decide
    unfold addFullMembers addFullList
    rw [hr]
    simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,addFullGroup,List.map_append,
      List.map_cons,List.map_nil,List.map_map,Function.comp_def,List.append_assoc,List.cons_append,List.nil_append]
  rw [hl]
  simp only [count_at_append]
  rw [addfull_right_tail q e hq he hen,addfull_gap_tail q e hq he hen,addfull_point_tail q e hq he hen]
  simp only [addedTailGroups,List.getD,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]

end LuRazThreeRow
