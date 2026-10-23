import LuRazPEnumeration

namespace LuRazClosure
open LuRazEnumeration
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

def NF23.tag : NF23 → Nat
  | .lp _ _ => 0 | .filledM => 1 | .dgap _ => 2
  | .full => 3 | .creg _ => 4 | .cexception => 5

def enum23Group (q : Nat) : Nat → List NF23
  | 0 => pairs (fun r s => NF23.lp (rankP q s) (rankP q r)) 0 (2*q-3) (fun _ => 0) (fun r => r+1)
  | 1 => [.filledM]
  | 2 => (enumP q (2*q-5)).map NF23.dgap
  | 3 => [.full]
  | 4 => ((enumP q (2*q-3)).filter (fun p => decide (p≠q+3))).map NF23.creg
  | 5 => [.cexception]
  | _ => []

def enum23 (q : Nat) : List NF23 := (List.range 6).flatMap (enum23Group q)

theorem NF23.tag_lt (z : NF23) : z.tag<6 := by cases z <;> simp [NF23.tag]

theorem enum23Group_tag (q k : Nat) (hk : k<6) (z : NF23) (hz : z∈enum23Group q k) : z.tag=k := by
  have hc : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 := by omega
  rcases hc with h | h | h | h | h | h <;> subst k
  · obtain ⟨a,b,_,_,rfl⟩ := (pairs_mem _ _ _ _ _ _).mp hz
    rfl
  · have he : z=NF23.filledM := by simpa only [enum23Group,List.mem_cons,List.not_mem_nil,or_false] using hz
    subst z; rfl
  · obtain ⟨a,_,rfl⟩ := List.mem_map.mp hz
    rfl
  · have he : z=NF23.full := by simpa only [enum23Group,List.mem_cons,List.not_mem_nil,or_false] using hz
    subst z; rfl
  · obtain ⟨a,_,rfl⟩ := List.mem_map.mp hz
    rfl
  · have he : z=NF23.cexception := by simpa only [enum23Group,List.mem_cons,List.not_mem_nil,or_false] using hz
    subst z; rfl

theorem enum23Group_valid (q : Nat) (hq : 4≤q) (k : Nat) (hk : k<6)
    (z : NF23) (hz : z∈enum23Group q k) : z.Valid q := by
  have hc : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 := by omega
  rcases hc with h | h | h | h | h | h <;> subst k
  · obtain ⟨a,b,ha,hb,rfl⟩ := (pairs_mem _ _ _ _ _ _).mp hz
    exact ⟨rankP_valid q b hq (by omega),rankP_valid q a hq (by omega),(rankP_le q b a).mpr (by omega)⟩
  · have he : z=NF23.filledM := by simpa only [enum23Group,List.mem_cons,List.not_mem_nil,or_false] using hz
    subst z; exact True.intro
  · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hz
    exact (enumP_low_exact q hq a).mp ha
  · have he : z=NF23.full := by simpa only [enum23Group,List.mem_cons,List.not_mem_nil,or_false] using hz
    subst z; exact True.intro
  · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hz
    have hf := List.mem_filter.mp ha
    exact ⟨(enumP_exact q hq a).mp hf.1,of_decide_eq_true hf.2⟩
  · have he : z=NF23.cexception := by simpa only [enum23Group,List.mem_cons,List.not_mem_nil,or_false] using hz
    subst z; exact True.intro

theorem NF23.valid_mem_group (q : Nat) (hq : 4≤q) (z : NF23) (hz : z.Valid q) : z∈enum23Group q z.tag := by
  cases z with
  | lp t p =>
    obtain ⟨s,hs,hst⟩ := rankP_surjective q t hq hz.1
    obtain ⟨r,hr,hrp⟩ := rankP_surjective q p hq hz.2.1
    have hsr : s≤r := (rankP_le q s r).mp (by rw [hst,hrp]; exact hz.2.2)
    apply (pairs_mem _ _ _ _ _ _).mpr
    exact ⟨r,s,by omega,by omega,by rw [hst,hrp]⟩
  | filledM => simp only [enum23Group,NF23.tag,List.mem_cons,true_or]
  | dgap p =>
    exact List.mem_map.mpr ⟨p,(enumP_low_exact q hq p).mpr hz,rfl⟩
  | full => simp only [enum23Group,NF23.tag,List.mem_cons,true_or]
  | creg t =>
    apply List.mem_map.mpr
    refine ⟨t,List.mem_filter.mpr ⟨(enumP_exact q hq t).mpr hz.1,?_⟩,rfl⟩
    exact decide_eq_true hz.2
  | cexception => simp only [enum23Group,NF23.tag,List.mem_cons,true_or]

theorem enum23_exact (q : Nat) (hq : 4≤q) (z : NF23) : z∈enum23 q ↔ z.Valid q := by
  constructor
  · intro hz
    obtain ⟨k,hk,hzk⟩ := List.mem_flatMap.mp hz
    exact enum23Group_valid q hq k (List.mem_range.mp hk) z hzk
  · intro hz
    exact List.mem_flatMap.mpr ⟨z.tag,List.mem_range.mpr (NF23.tag_lt z),NF23.valid_mem_group q hq z hz⟩

theorem enum23Group_nodup (q k : Nat) (hk : k<6) : (enum23Group q k).Nodup := by
  have hc : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 := by omega
  rcases hc with h | h | h | h | h | h <;> subst k
  · apply pairs_nodup
    intro a b c d heq
    have hi := NF23.lp.inj heq
    exact ⟨rankP_injective q a c hi.2,rankP_injective q b d hi.1⟩
  · simp [enum23Group]
  · exact nodup_map_injective NF23.dgap (fun _ _ h => NF23.dgap.inj h) _ (enumP_nodup q (2*q-5))
  · simp [enum23Group]
  · apply nodup_map_injective NF23.creg (fun _ _ h => NF23.creg.inj h)
    exact List.Nodup.sublist List.filter_sublist (enumP_nodup q (2*q-3))
  · simp [enum23Group]

theorem enum23_nodup (q : Nat) : (enum23 q).Nodup := by
  apply nodup_flatMap_separated _ _ List.nodup_range
  · intro k hk
    exact enum23Group_nodup q k (List.mem_range.mp hk)
  · intro k hk j hj z hz w hw heq
    have hzk := enum23Group_tag q k (List.mem_range.mp hk) z hz
    have hwj := enum23Group_tag q j (List.mem_range.mp hj) w hw
    subst w
    omega

end LuRazClosure
