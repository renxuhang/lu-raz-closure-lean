import SixRowDifferenceLists

namespace LuRazSixRowClosure.Difference
open LuRazClosure LuRazEnumeration
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

theorem nodup_two_ranges (s n t m : Nat) (hsep : s+n≤t) :
    (List.range' s n ++ List.range' t m).Nodup := by
  rw [List.nodup_append]
  refine ⟨List.nodup_range',List.nodup_range',?_⟩
  intro a ha b hb he
  have ha := (range_mem a s n).mp ha
  have hb := (range_mem b t m).mp hb
  omega

theorem regularParams_nodup (q : Nat) (hq : 4≤q) : (regularParams q).Nodup := by
  apply nodup_two_ranges
  omega

theorem pParams_nodup (q : Nat) (hq : 4≤q) : (pParams q).Nodup := by
  apply nodup_two_ranges
  omega

theorem dParams_nodup (q : Nat) (hq : 4≤q) : (dParams q).Nodup := by
  rw [dParams,List.nodup_cons]
  refine ⟨?_,nodup_two_ranges _ _ _ _ (by omega)⟩
  simp [range_mem] <;> omega

theorem rightParams_nodup (q : Nat) (hq : 4≤q) : (rightParams q).Nodup := by
  rw [rightParams,List.nodup_cons]
  refine ⟨?_,List.nodup_range'⟩
  simp [range_mem] <;> omega

theorem c14Params_nodup (q : Nat) (hq : 4≤q) : (c14Params q).Nodup := by
  apply nodup_two_ranges
  omega

theorem removedGroup_nodup (q : Nat) (hq : 4≤q) (k : Nat) (hk : k<27) :
    (removedGroup q k).Nodup := by
  have hc : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨ k=7 ∨ k=8 ∨ k=9 ∨ k=10 ∨ k=11 ∨ k=12 ∨ k=13 ∨ k=14 ∨ k=15 ∨ k=16 ∨ k=17 ∨ k=18 ∨ k=19 ∨ k=20 ∨ k=21 ∨ k=22 ∨ k=23 ∨ k=24 ∨ k=25 ∨ k=26 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp [removedGroup]
  · simp [removedGroup]
  · exact nodup_map_injective RemovedForm.r4 (fun _ _ h => RemovedForm.r4.inj h) _ List.nodup_range'
  · simp [removedGroup]
  · exact nodup_map_injective RemovedForm.r6regular (fun _ _ h => RemovedForm.r6regular.inj h) _ (regularParams_nodup q hq)
  · simp [removedGroup]
  · exact nodup_map_injective RemovedForm.r6d (fun _ _ h => RemovedForm.r6d.inj h) _ (dParams_nodup q hq)
  · exact nodup_map_injective RemovedForm.r7fresh (fun _ _ h => RemovedForm.r7fresh.inj h) _ List.nodup_range'
  · exact nodup_map_injective RemovedForm.r7e (fun _ _ h => RemovedForm.r7e.inj h) _ List.nodup_range'
  · exact nodup_map_injective RemovedForm.r7d (fun _ _ h => RemovedForm.r7d.inj h) _ List.nodup_range'
  · exact nodup_map_injective RemovedForm.r10 (fun _ _ h => RemovedForm.r10.inj h) _ List.nodup_range'
  · exact nodup_map_injective RemovedForm.r11j (fun _ _ h => RemovedForm.r11j.inj h) _ List.nodup_range'
  · exact nodup_map_injective RemovedForm.r11aj (fun _ _ h => RemovedForm.r11aj.inj h) _ List.nodup_range'
  · exact nodup_map_injective RemovedForm.r11ak (fun _ _ h => RemovedForm.r11ak.inj h) _ List.nodup_range'
  · exact nodup_map_injective RemovedForm.r12 (fun _ _ h => RemovedForm.r12.inj h) _ List.nodup_range'
  · exact nodup_map_injective RemovedForm.r13cj (fun _ _ h => RemovedForm.r13cj.inj h) _ List.nodup_range'
  · exact nodup_map_injective RemovedForm.r13zj (fun _ _ h => RemovedForm.r13zj.inj h) _ List.nodup_range'
  · exact nodup_map_injective RemovedForm.r13czj (fun _ _ h => RemovedForm.r13czj.inj h) _ List.nodup_range'
  · exact nodup_map_injective RemovedForm.r13points (fun _ _ h => RemovedForm.r13points.inj h) _ List.nodup_range'
  · exact nodup_map_injective RemovedForm.r14points (fun _ _ h => RemovedForm.r14points.inj h) _ List.nodup_range'
  · exact nodup_map_injective RemovedForm.r14line (fun _ _ h => RemovedForm.r14line.inj h) _ List.nodup_range'
  · exact nodup_map_injective RemovedForm.r14c (fun _ _ h => RemovedForm.r14c.inj h) _ (c14Params_nodup q hq)
  · exact nodup_map_injective RemovedForm.r15points (fun _ _ h => RemovedForm.r15points.inj h) _ List.nodup_range'
  · exact nodup_map_injective RemovedForm.r15right (fun _ _ h => RemovedForm.r15right.inj h) _ List.nodup_range'
  · exact nodup_map_injective RemovedForm.r15gap (fun _ _ h => RemovedForm.r15gap.inj h) _ List.nodup_range'
  · exact nodup_map_injective RemovedForm.r15line (fun _ _ h => RemovedForm.r15line.inj h) _ List.nodup_range'
  · rw [removedGroup,List.nodup_append]
    refine ⟨nodup_map_injective _ (fun _ _ h => (RemovedForm.r15short.inj h).1) _ List.nodup_range',
      nodup_map_injective _ (fun _ _ h => (RemovedForm.r15short.inj h).1) _ List.nodup_range',?_⟩
    intro a ha b hb he
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp ha
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hb
    have hh := (RemovedForm.r15short.inj he).2
    omega

theorem removedList_nodup (q : Nat) (hq : 4≤q) : (removedList q).Nodup := by
  apply nodup_flatMap_separated _ _ List.nodup_range
  · intro k hk
    exact removedGroup_nodup q hq k (List.mem_range.mp hk)
  · intro k hk j hj z hz w hw he
    have hzk := ((removedGroup_exact q hq k (List.mem_range.mp hk) z).mp hz).2
    have hwj := ((removedGroup_exact q hq j (List.mem_range.mp hj) w).mp hw).2
    subst w
    omega

theorem addedGroup_nodup (q : Nat) (hq : 4≤q) (k : Nat) (hk : k<16) :
    (addedGroup q k).Nodup := by
  have hc : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨ k=7 ∨ k=8 ∨ k=9 ∨ k=10 ∨ k=11 ∨ k=12 ∨ k=13 ∨ k=14 ∨ k=15 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact nodup_map_injective AddedForm.n4 (fun _ _ h => AddedForm.n4.inj h) _ List.nodup_range'
  · exact nodup_map_injective AddedForm.n5 (fun _ _ h => AddedForm.n5.inj h) _ List.nodup_range'
  · exact nodup_map_injective AddedForm.n6regular (fun _ _ h => AddedForm.n6regular.inj h) _ (regularParams_nodup q hq)
  · simp [addedGroup]
  · exact nodup_map_injective AddedForm.n6e (fun _ _ h => AddedForm.n6e.inj h) _ (pParams_nodup q hq)
  · exact nodup_map_injective AddedForm.n7regular (fun _ _ h => AddedForm.n7regular.inj h) _ (regularParams_nodup q hq)
  · simp [addedGroup]
  · exact nodup_map_injective AddedForm.n7right (fun _ _ h => AddedForm.n7right.inj h) _ (rightParams_nodup q hq)
  · simp [addedGroup]
  · exact nodup_map_injective AddedForm.n10 (fun _ _ h => AddedForm.n10.inj h) _ List.nodup_range'
  · exact nodup_map_injective AddedForm.n11j (fun _ _ h => AddedForm.n11j.inj h) _ List.nodup_range'
  · exact nodup_map_injective AddedForm.n11aj (fun _ _ h => AddedForm.n11aj.inj h) _ List.nodup_range'
  · exact nodup_map_injective AddedForm.n11ak (fun _ _ h => AddedForm.n11ak.inj h) _ List.nodup_range'
  · exact nodup_map_injective AddedForm.n13plain (fun _ _ h => AddedForm.n13plain.inj h) _ List.nodup_range'
  · exact nodup_map_injective AddedForm.n13isolated (fun _ _ h => AddedForm.n13isolated.inj h) _ List.nodup_range'
  · exact nodup_map_injective AddedForm.n13right (fun _ _ h => AddedForm.n13right.inj h) _ List.nodup_range'

theorem addedList_nodup (q : Nat) (hq : 4≤q) : (addedList q).Nodup := by
  apply nodup_flatMap_separated _ _ List.nodup_range
  · intro k hk
    exact addedGroup_nodup q hq k (List.mem_range.mp hk)
  · intro k hk j hj z hz w hw he
    have hzk := ((addedGroup_exact q hq k (List.mem_range.mp hk) z).mp hz).2
    have hwj := ((addedGroup_exact q hq j (List.mem_range.mp hj) w).mp hw).2
    subst w
    omega

end LuRazSixRowClosure.Difference


