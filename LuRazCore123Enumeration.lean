import LuRazCore123Unique
namespace LuRazClosure
open LuRazEnumeration
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

def NF123.tag : NF123 → Nat
  | .low _ => 0
  | .high _ _ => 1
  | .filled  => 2
  | .dg _ => 3
  | .full  => 4
  | .creg _ => 5
  | .cex  => 6
  | .er _ => 7
  | .ed _ => 8

def enum123Group (q : Nat) : Nat → List NF123
  | 0 => (List.range' 4 (q-2)).map NF123.low
  | 1 => pairs (fun r s => NF123.high (rankP q s) (rankP q r)) (q-2) (q-1) (fun _ => 0) (fun r => r+1)
  | 2 => [.filled]
  | 3 => (List.range' (q+2) (q-2)).map NF123.dg
  | 4 => [.full]
  | 5 => ((enumP q (2*q-3)).filter (fun p => decide (p≠q+3))).map NF123.creg
  | 6 => [.cex]
  | 7 => (List.range' 4 (2*q-2)).map NF123.er
  | 8 => (List.range' 4 (q-2)).map NF123.ed
  | _ => []
def enum123 (q : Nat) : List NF123 := (List.range 9).flatMap (enum123Group q)

theorem NF123.tag_lt (z : NF123) : z.tag<9 := by cases z <;> simp [NF123.tag]

theorem enum123Group_tag (q k : Nat) (hk : k<9) (z : NF123) (hz : z∈enum123Group q k) : z.tag=k := by
  have hc : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨ k=7 ∨ k=8 := by omega
  rcases hc with h | h | h | h | h | h | h | h | h <;> subst k
  · obtain ⟨a,_,rfl⟩ := List.mem_map.mp hz
    rfl
  · obtain ⟨a,b,_,_,rfl⟩ := (pairs_mem _ _ _ _ _ _).mp hz
    rfl
  · have he : z=NF123.filled := by simpa [enum123Group] using hz
    subst z; rfl
  · obtain ⟨a,_,rfl⟩ := List.mem_map.mp hz
    rfl
  · have he : z=NF123.full := by simpa [enum123Group] using hz
    subst z; rfl
  · obtain ⟨a,_,rfl⟩ := List.mem_map.mp hz
    rfl
  · have he : z=NF123.cex := by simpa [enum123Group] using hz
    subst z; rfl
  · obtain ⟨a,_,rfl⟩ := List.mem_map.mp hz
    rfl
  · obtain ⟨a,_,rfl⟩ := List.mem_map.mp hz
    rfl

theorem enum123Group_valid (q : Nat) (hq : 4≤q) (k : Nat) (hk : k<9)
    (z : NF123) (hz : z∈enum123Group q k) : z.Valid q := by
  have hc : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨ k=7 ∨ k=8 := by omega
  rcases hc with h | h | h | h | h | h | h | h | h <;> subst k
  · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hz
    have hb := (range_mem _ _ _).mp ha
    change 4≤a ∧ a≤q+1
    omega
  · obtain ⟨a,b,ha,hb,rfl⟩ := (pairs_mem _ _ _ _ _ _).mp hz
    have hpa := rankP_valid q a hq (by omega)
    have hpb := rankP_valid q b hq (by omega)
    have hlo : q+3≤rankP q a := by
      unfold rankP
      split <;> omega
    exact ⟨hpb,hpa,hlo,(rankP_le q b a).mpr (by omega)⟩
  · have he : z=NF123.filled := by simpa [enum123Group] using hz
    subst z; exact True.intro
  · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hz
    have hb := (range_mem _ _ _).mp ha
    change q+2≤a ∧ a≤2*q-1
    omega
  · have he : z=NF123.full := by simpa [enum123Group] using hz
    subst z; exact True.intro
  · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hz
    have hf := List.mem_filter.mp ha
    exact ⟨(enumP_exact q hq a).mp hf.1,of_decide_eq_true hf.2⟩
  · have he : z=NF123.cex := by simpa [enum123Group] using hz
    subst z; exact True.intro
  · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hz
    have hb := (range_mem _ _ _).mp ha
    change 4≤a ∧ a≤2*q+1
    omega
  · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hz
    have hb := (range_mem _ _ _).mp ha
    change 4≤a ∧ a≤q+1
    omega

theorem NF123.valid_mem_group (q : Nat) (hq : 4≤q) (z : NF123) (hz : z.Valid q) : z∈enum123Group q z.tag := by
  cases z with
  | low t => exact List.mem_map.mpr ⟨t,(range_mem _ _ _).mpr (by have hb : 4≤t ∧ t≤q+1 := hz; omega),rfl⟩
  | high t p =>
    obtain ⟨s,hs,hst⟩ := rankP_surjective q t hq hz.1
    obtain ⟨r,hr,hrp⟩ := rankP_surjective q p hq hz.2.1
    have hsr : s≤r := (rankP_le q s r).mp (by rw [hst,hrp]; exact hz.2.2.2)
    have hlo : q-2≤r := by
      have hp : q+3≤p := hz.2.2.1
      unfold rankP at hrp
      split at hrp <;> omega
    apply (pairs_mem _ _ _ _ _ _).mpr
    exact ⟨r,s,by omega,by omega,by rw [hst,hrp]⟩
  | filled => simp [enum123Group,NF123.tag]
  | dg p => exact List.mem_map.mpr ⟨p,(range_mem _ _ _).mpr (by have hb : q+2≤p ∧ p≤2*q-1 := hz; omega),rfl⟩
  | full => simp [enum123Group,NF123.tag]
  | creg t =>
    exact List.mem_map.mpr ⟨t,List.mem_filter.mpr ⟨(enumP_exact q hq t).mpr hz.1,decide_eq_true hz.2⟩,rfl⟩
  | cex => simp [enum123Group,NF123.tag]
  | er p => exact List.mem_map.mpr ⟨p,(range_mem _ _ _).mpr (by have hb : 4≤p ∧ p≤2*q+1 := hz; omega),rfl⟩
  | ed p => exact List.mem_map.mpr ⟨p,(range_mem _ _ _).mpr (by have hb : 4≤p ∧ p≤q+1 := hz; omega),rfl⟩

theorem enum123_exact (q : Nat) (hq : 4≤q) (z : NF123) : z∈enum123 q ↔ z.Valid q := by
  constructor
  · intro hz
    obtain ⟨k,hk,hzk⟩ := List.mem_flatMap.mp hz
    exact enum123Group_valid q hq k (List.mem_range.mp hk) z hzk
  · intro hz
    exact List.mem_flatMap.mpr ⟨z.tag,List.mem_range.mpr (NF123.tag_lt z),NF123.valid_mem_group q hq z hz⟩

theorem enum123Group_nodup (q k : Nat) (hk : k<9) : (enum123Group q k).Nodup := by
  have hc : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨ k=7 ∨ k=8 := by omega
  rcases hc with h | h | h | h | h | h | h | h | h <;> subst k
  · exact nodup_map_injective NF123.low (fun _ _ h => NF123.low.inj h) _ List.nodup_range'
  · apply pairs_nodup
    intro a b c d heq
    have hi := NF123.high.inj heq
    exact ⟨rankP_injective q a c hi.2,rankP_injective q b d hi.1⟩
  · simp [enum123Group]
  · exact nodup_map_injective NF123.dg (fun _ _ h => NF123.dg.inj h) _ List.nodup_range'
  · simp [enum123Group]
  · apply nodup_map_injective NF123.creg (fun _ _ h => NF123.creg.inj h)
    exact List.Nodup.sublist List.filter_sublist (enumP_nodup q (2*q-3))
  · simp [enum123Group]
  · exact nodup_map_injective NF123.er (fun _ _ h => NF123.er.inj h) _ List.nodup_range'
  · exact nodup_map_injective NF123.ed (fun _ _ h => NF123.ed.inj h) _ List.nodup_range'

theorem enum123_nodup (q : Nat) : (enum123 q).Nodup := by
  apply nodup_flatMap_separated _ _ List.nodup_range
  · intro k hk
    exact enum123Group_nodup q k (List.mem_range.mp hk)
  · intro k hk j hj z hz w hw heq
    have hzk := enum123Group_tag q k (List.mem_range.mp hk) z hz
    have hwj := enum123Group_tag q j (List.mem_range.mp hj) w hw
    subst w
    omega
end LuRazClosure
