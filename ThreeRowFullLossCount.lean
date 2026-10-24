import ThreeRowFullObstructions

namespace LuRazThreeRow
open LuRazClosure LuRazEnumeration
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

def lossGroup (q : Nat) : Nat → List NFFull
  | 0 => (List.range' (2*q+4) (2*q-4)).map NFFull.noH1ZL
  | 1 => [.noH1Exception]
  | 2 => [.noH2 (4*q)]
  | 3 => (List.range' (2*q+2) (2*q-4)).map (fun b => NFFull.rightGap b (4*q))
  | 4 => (List.range' (2*q+2) (q-2)).map (fun b => NFFull.isolatedR b (4*q))
  | _ => []

def lossTag : NFFull → Nat
  | .noH1ZL _ => 0 | .noH1Exception => 1 | .noH2 _ => 2
  | .rightGap _ _ => 3 | .isolatedR _ _ => 4 | _ => 5

def lossList (q : Nat) : List NFFull := (List.range 5).flatMap (lossGroup q)

theorem exists_fixed (P : Nat → Prop) (b : Nat) (Q : Prop) :
    (∃ a, P a ∧ a=b ∧ Q) ↔ P b ∧ Q := by
  constructor
  · rintro ⟨a,ha,rfl,hq⟩; exact ⟨ha,hq⟩
  · exact fun h => ⟨b,h.1,rfl,h.2⟩

theorem loss_group_exact (q : Nat) (hq : 4≤q) (k : Nat) (hk : k<5) (z : NFFull) :
    z∈lossGroup q k ↔ z.Valid q ∧ LostFull q z ∧ lossTag z=k := by
  have hc : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl
  all_goals cases z <;> simp [lossGroup,List.mem_map,range_mem,NFFull.Valid,LostFull,lossTag,exists_fixed] <;> omega

theorem loss_list_exact (q : Nat) (hq : 4≤q) (z : NFFull) :
    z∈lossList q ↔ z.Valid q ∧ LostFull q z := by
  constructor
  · intro h
    obtain ⟨k,hk,hz⟩ := List.mem_flatMap.mp h
    have hh := (loss_group_exact q hq k (List.mem_range.mp hk) z).mp hz
    exact ⟨hh.1,hh.2.1⟩
  · intro h
    have ht : lossTag z<5 := by cases z <;> simp_all [LostFull,lossTag]
    exact List.mem_flatMap.mpr ⟨lossTag z,List.mem_range.mpr ht,
      (loss_group_exact q hq _ ht z).mpr ⟨h.1,h.2,rfl⟩⟩

theorem loss_group_nodup (q k : Nat) (hk : k<5) : (lossGroup q k).Nodup := by
  have hc : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl
  · exact nodup_map_injective NFFull.noH1ZL (fun _ _ h => NFFull.noH1ZL.inj h) _ List.nodup_range'
  · simp [lossGroup]
  · simp [lossGroup]
  · exact nodup_map_injective (fun b => NFFull.rightGap b (4*q))
      (fun _ _ h => (NFFull.rightGap.inj h).1) _ List.nodup_range'
  · exact nodup_map_injective (fun b => NFFull.isolatedR b (4*q))
      (fun _ _ h => (NFFull.isolatedR.inj h).1) _ List.nodup_range'

theorem loss_list_nodup (q : Nat) (hq : 4≤q) : (lossList q).Nodup := by
  apply nodup_flatMap_separated _ _ List.nodup_range
  · intro k hk
    exact loss_group_nodup q k (List.mem_range.mp hk)
  · intro k hk j hj z hz w hw he
    have hzk := ((loss_group_exact q hq k (List.mem_range.mp hk) z).mp hz).2.2
    have hwj := ((loss_group_exact q hq j (List.mem_range.mp hj) w).mp hw).2.2
    subst w
    omega

theorem loss_list_length (q : Nat) (hq : 4≤q) : ((lossList q).length : Int)=5*(q:Int)-8 := by
  have hr : List.range 5=[0,1,2,3,4] := by decide
  unfold lossList
  rw [hr]
  simp [lossGroup,List.length_flatMap,List.length_map,List.length_range']
  omega

def lossMembers (q : Nat) : List (Nat → Prop) := (lossList q).map (NFFull.eval q)

theorem loss_members_nodup (q : Nat) (hq : 4≤q) : (lossMembers q).Nodup := by
  apply nodup_map_on _ _ (loss_list_nodup q hq)
  intro a ha b hb he
  exact NFFull.unique q hq a b ((loss_list_exact q hq a).mp ha).1 ((loss_list_exact q hq b).mp hb).1
    (fun e => Iff.of_eq (congrFun he e))

/-- A rigorous lower bound on the number of old full-core members that disappear. -/
theorem full_loss_cardinality (q : Nat) (hq : 4≤q) :
    ∃ l : List (Nat → Prop), l.Nodup ∧
      (∀ R∈l, LuRazClosure.Generated q R ∧ CoreFull R ∧ ¬Generated q R) ∧
      (l.length : Int)=5*(q:Int)-8 := by
  refine ⟨lossMembers q,loss_members_nodup q hq,?_,?_⟩
  · intro R hR
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hR
    have hv := (loss_list_exact q hq z).mp hz
    refine ⟨NFFull.generated q hq z hv.1,?_,lost_full_not_generated q hq z hv.1 hv.2⟩
    exact NFFull.core q hq z hv.1
  · simpa only [lossMembers,List.length_map] using loss_list_length q hq

end LuRazThreeRow
