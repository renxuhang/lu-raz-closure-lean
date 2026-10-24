import ThreeRowCore23

namespace LuRazThreeRow
open LuRazClosure LuRazEnumeration
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

theorem rankP_short (q k : Nat) (hq : 4≤q) :
    k<2*q-4 ↔ (k<2*q-3 ∧ rankP q k≤2*q) := by
  unfold rankP
  split <;> omega

theorem enumP_short_exact (q : Nat) (hq : 4≤q) (p : Nat) :
    p∈enumP q (2*q-4) ↔ P q p ∧ p≤2*q := by
  constructor
  · intro hp
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hp
    have h := (rankP_short q k hq).mp (List.mem_range.mp hk)
    exact ⟨rankP_valid q k hq h.1,h.2⟩
  · rintro ⟨hp,hpl⟩
    obtain ⟨k,hk,he⟩ := rankP_surjective q p hq hp
    exact List.mem_map.mpr ⟨k,List.mem_range.mpr ((rankP_short q k hq).mpr
      ⟨hk,by rw [he]; exact hpl⟩),he⟩

def new23Group (q : Nat) : Nat → List NF23
  | 0 => pairs (fun r s => NF23.lp (rankP q s) (rankP q r)) 0 (2*q-4) (fun _ => 0) (fun r => r+1)
  | 1 => [.filledM]
  | 2 => (enumP q (2*q-5)).map NF23.dgap
  | 3 => [.full]
  | 4 => ((enumP q (2*q-4)).filter (fun p => decide (p≠q+3))).map NF23.creg
  | 5 => [.cexception]
  | _ => []

def new23 (q : Nat) : List NF23 := (List.range 6).flatMap (new23Group q)

theorem new23_group_tag (q k : Nat) (hk : k<6) (z : NF23) (hz : z∈new23Group q k) : z.tag=k := by
  have hc : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨a,b,_,_,rfl⟩ := (pairs_mem _ _ _ _ _ _).mp hz; rfl
  · have he : z=NF23.filledM := by simpa [new23Group] using hz
    subst z; rfl
  · obtain ⟨a,_,rfl⟩ := List.mem_map.mp hz; rfl
  · have he : z=NF23.full := by simpa [new23Group] using hz
    subst z; rfl
  · obtain ⟨a,_,rfl⟩ := List.mem_map.mp hz; rfl
  · have he : z=NF23.cexception := by simpa [new23Group] using hz
    subst z; rfl

theorem new23_group_valid (q : Nat) (hq : 4≤q) (k : Nat) (hk : k<6)
    (z : NF23) (hz : z∈new23Group q k) : Valid23 q z := by
  have hc : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨a,b,ha,hb,rfl⟩ := (pairs_mem _ _ _ _ _ _).mp hz
    have har := (rankP_short q a hq).mp (by omega)
    have hbr := (rankP_short q b hq).mp (by omega)
    exact ⟨⟨rankP_valid q b hq hbr.1,rankP_valid q a hq har.1,
      (rankP_le q b a).mpr (by omega)⟩,har.2⟩
  · have he : z=NF23.filledM := by simpa [new23Group] using hz
    subst z; exact ⟨True.intro,True.intro⟩
  · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hz
    exact ⟨(enumP_low_exact q hq a).mp ha,True.intro⟩
  · have he : z=NF23.full := by simpa [new23Group] using hz
    subst z; exact ⟨True.intro,True.intro⟩
  · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hz
    have hf := List.mem_filter.mp ha
    have hp := (enumP_short_exact q hq a).mp hf.1
    exact ⟨⟨hp.1,of_decide_eq_true hf.2⟩,hp.2⟩
  · have he : z=NF23.cexception := by simpa [new23Group] using hz
    subst z; exact ⟨True.intro,True.intro⟩

theorem new23_valid_group (q : Nat) (hq : 4≤q) (z : NF23) (hz : Valid23 q z) : z∈new23Group q z.tag := by
  cases z with
  | lp t p =>
    obtain ⟨s,hs,hst⟩ := rankP_surjective q t hq hz.1.1
    obtain ⟨r,hr,hrp⟩ := rankP_surjective q p hq hz.1.2.1
    have hsr : s≤r := (rankP_le q s r).mp (by rw [hst,hrp]; exact hz.1.2.2)
    have hrs : r<2*q-4 := (rankP_short q r hq).mpr ⟨hr,by rw [hrp]; exact hz.2⟩
    apply (pairs_mem _ _ _ _ _ _).mpr
    exact ⟨r,s,by omega,by omega,by rw [hst,hrp]⟩
  | filledM => simp [new23Group,NF23.tag]
  | dgap p => exact List.mem_map.mpr ⟨p,(enumP_low_exact q hq p).mpr hz.1,rfl⟩
  | full => simp [new23Group,NF23.tag]
  | creg t =>
    exact List.mem_map.mpr ⟨t,List.mem_filter.mpr
      ⟨(enumP_short_exact q hq t).mpr ⟨hz.1.1,hz.2⟩,decide_eq_true hz.1.2⟩,rfl⟩
  | cexception => simp [new23Group,NF23.tag]

theorem new23_exact (q : Nat) (hq : 4≤q) (z : NF23) : z∈new23 q ↔ Valid23 q z := by
  constructor
  · intro hz
    obtain ⟨k,hk,hzk⟩ := List.mem_flatMap.mp hz
    exact new23_group_valid q hq k (List.mem_range.mp hk) z hzk
  · intro hz
    exact List.mem_flatMap.mpr ⟨z.tag,List.mem_range.mpr (NF23.tag_lt z),new23_valid_group q hq z hz⟩

theorem new23_group_nodup (q k : Nat) (hk : k<6) : (new23Group q k).Nodup := by
  have hc : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · apply pairs_nodup
    intro a b c d he
    have hi := NF23.lp.inj he
    exact ⟨rankP_injective q a c hi.2,rankP_injective q b d hi.1⟩
  · simp [new23Group]
  · exact nodup_map_injective NF23.dgap (fun _ _ h => NF23.dgap.inj h) _ (enumP_nodup q (2*q-5))
  · simp [new23Group]
  · apply nodup_map_injective NF23.creg (fun _ _ h => NF23.creg.inj h)
    exact List.Nodup.sublist List.filter_sublist (enumP_nodup q (2*q-4))
  · simp [new23Group]

theorem new23_nodup (q : Nat) : (new23 q).Nodup := by
  apply nodup_flatMap_separated _ _ List.nodup_range
  · intro k hk
    exact new23_group_nodup q k (List.mem_range.mp hk)
  · intro k hk j hj z hz w hw he
    have hzk := new23_group_tag q k (List.mem_range.mp hk) z hz
    have hwj := new23_group_tag q j (List.mem_range.mp hj) w hw
    subst w
    omega

theorem new23_length (q : Nat) (hq : 4≤q) :
    ((new23 q).length : Int)=2*(q:Int)*(q:Int)-3*(q:Int)-1 := by
  have h0 := triangular_pairs_count (fun r s => NF23.lp (rankP q s) (rankP q r)) (2*q-4)
  have hc : ((2*q-4:Nat):Int)=2*(q:Int)-4 := by omega
  rw [hc] at h0
  have hmem := (enumP_short_exact q hq (q+3)).mpr (by unfold P; omega)
  have h4 := filter_ne_length (enumP q (2*q-4)) (enumP_nodup q (2*q-4)) (q+3) hmem
  have he : new23 q=new23Group q 0 ++ new23Group q 1 ++ new23Group q 2 ++
      new23Group q 3 ++ new23Group q 4 ++ new23Group q 5 := by
    have hr : List.range 6=[0,1,2,3,4,5] := by decide
    unfold new23
    rw [hr]
    simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc]
  rw [he]
  simp only [new23Group,enumP,List.length_map,List.length_range,List.length_append,
    List.length_singleton,Int.natCast_add] at h4 ⊢
  have h0' : 2*((new23Group q 0).length : Int)=(2*(q:Int)-4)*(2*(q:Int)-3) := by
    have hc2 : 2*(q:Int)-4+1=2*(q:Int)-3 := by omega
    rw [hc2] at h0
    exact h0
  change ((new23Group q 0).length : Int) + 1 + ((2*q-5:Nat):Int) + 1 +
    ((((List.range (2*q-4)).map (rankP q)).filter (fun p => decide (p≠q+3))).length : Int) + 1 = _
  grind

def new23Members (q : Nat) : List (Nat → Prop) := (new23 q).map (NF23.eval q)

theorem new23_members_exact (q : Nat) (hq : 4≤q) (R : Nat → Prop) :
    R∈new23Members q ↔ Generated q R ∧ Core23 R := by
  rw [core23_exact q hq R]
  constructor
  · intro h
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp h
    exact ⟨z,(new23_exact q hq z).mp hz,fun _ => Iff.rfl⟩
  · rintro ⟨z,hz,he⟩
    exact List.mem_map.mpr ⟨z,(new23_exact q hq z).mpr hz,funext (fun e => propext (he e).symm)⟩

theorem new23_members_nodup (q : Nat) (hq : 4≤q) : (new23Members q).Nodup := by
  apply nodup_map_on _ _ (new23_nodup q)
  intro a ha b hb he
  exact NF23.unique q hq a b ((new23_exact q hq a).mp ha).1 ((new23_exact q hq b).mp hb).1
    (fun e => Iff.of_eq (congrFun he e))

theorem core23_cardinality (q : Nat) (hq : 4≤q) :
    ∃ l : List (Nat → Prop), l.Nodup ∧
      (∀ R, R∈l ↔ Generated q R ∧ Core23 R) ∧
      (l.length : Int)=2*(q:Int)*(q:Int)-3*(q:Int)-1 :=
  ⟨new23Members q,new23_members_nodup q hq,new23_members_exact q hq,
    by simpa only [new23Members,List.length_map] using new23_length q hq⟩

end LuRazThreeRow
