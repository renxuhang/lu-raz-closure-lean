import LuRazCore234Unique
namespace LuRazClosure
open LuRazEnumeration
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

def NF234.tag : NF234 → Nat
  | .kr _ _ => 0 | .dg _ => 1 | .km _ => 2 | .ck _ => 3 | .last => 4

def enum234Group (q : Nat) : Nat → List NF234
  | 0 => pairs (fun r k => NF234.kr (rankP q r) k) 0 (2*q-3) (fun _ => 0) (fun _ => 2)
  | 1 => (enumP q (2*q-5)).map NF234.dg
  | 2 => [.km 0,.km 1]
  | 3 => [.ck 0,.ck 1]
  | 4 => [.last]
  | _ => []
def enum234 (q : Nat) : List NF234 := (List.range 5).flatMap (enum234Group q)

theorem NF234.tag_lt (z : NF234) : z.tag<5 := by cases z <;> simp [NF234.tag]

theorem enum234Group_tag (q k : Nat) (hk : k<5) (z : NF234) (hz : z∈enum234Group q k) : z.tag=k := by
  have hc : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 := by omega
  rcases hc with h | h | h | h | h <;> subst k
  · obtain ⟨a,b,_,_,rfl⟩ := (pairs_mem _ _ _ _ _ _).mp hz
    rfl
  · obtain ⟨a,_,rfl⟩ := List.mem_map.mp hz
    rfl
  · have he : z=NF234.km 0 ∨ z=NF234.km 1 := by simpa [enum234Group] using hz
    rcases he with h | h <;> subst z <;> rfl
  · have he : z=NF234.ck 0 ∨ z=NF234.ck 1 := by simpa [enum234Group] using hz
    rcases he with h | h <;> subst z <;> rfl
  · have he : z=NF234.last := by simpa [enum234Group] using hz
    subst z; rfl

theorem enum234Group_valid (q : Nat) (hq : 4≤q) (k : Nat) (hk : k<5)
    (z : NF234) (hz : z∈enum234Group q k) : z.Valid q := by
  have hc : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 := by omega
  rcases hc with h | h | h | h | h <;> subst k
  · obtain ⟨a,b,ha,hb,rfl⟩ := (pairs_mem _ _ _ _ _ _).mp hz
    exact ⟨rankP_valid q a hq (by omega),by omega⟩
  · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hz
    exact (enumP_low_exact q hq a).mp ha
  · have he : z=NF234.km 0 ∨ z=NF234.km 1 := by simpa [enum234Group] using hz
    rcases he with h | h <;> subst z <;> simp [NF234.Valid]
  · have he : z=NF234.ck 0 ∨ z=NF234.ck 1 := by simpa [enum234Group] using hz
    rcases he with h | h <;> subst z <;> simp [NF234.Valid]
  · have he : z=NF234.last := by simpa [enum234Group] using hz
    subst z; exact True.intro

theorem NF234.valid_mem_group (q : Nat) (hq : 4≤q) (z : NF234) (hz : z.Valid q) : z∈enum234Group q z.tag := by
  cases z with
  | kr p k =>
    obtain ⟨r,hr,hrp⟩ := rankP_surjective q p hq hz.1
    apply (pairs_mem _ _ _ _ _ _).mpr
    exact ⟨r,k,by omega,by have hk : k<2 := hz.2; omega,by rw [hrp]⟩
  | dg p => exact List.mem_map.mpr ⟨p,(enumP_low_exact q hq p).mpr hz,rfl⟩
  | km k =>
    have hk : k<2 := hz
    have hs : k=0 ∨ k=1 := by omega
    rcases hs with h | h <;> subst k <;> simp [NF234.tag,enum234Group]
  | ck k =>
    have hk : k<2 := hz
    have hs : k=0 ∨ k=1 := by omega
    rcases hs with h | h <;> subst k <;> simp [NF234.tag,enum234Group]
  | last => simp [enum234Group,NF234.tag]

theorem enum234_exact (q : Nat) (hq : 4≤q) (z : NF234) : z∈enum234 q ↔ z.Valid q := by
  constructor
  · intro hz
    obtain ⟨k,hk,hzk⟩ := List.mem_flatMap.mp hz
    exact enum234Group_valid q hq k (List.mem_range.mp hk) z hzk
  · intro hz
    exact List.mem_flatMap.mpr ⟨z.tag,List.mem_range.mpr (NF234.tag_lt z),NF234.valid_mem_group q hq z hz⟩

theorem enum234Group_nodup (q k : Nat) (hk : k<5) : (enum234Group q k).Nodup := by
  have hc : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 := by omega
  rcases hc with h | h | h | h | h <;> subst k
  · apply pairs_nodup
    intro a b c d heq
    have hi := NF234.kr.inj heq
    exact ⟨rankP_injective q a c hi.1,hi.2⟩
  · exact nodup_map_injective NF234.dg (fun _ _ h => NF234.dg.inj h) _ (enumP_nodup q (2*q-5))
  · simp [enum234Group]
  · simp [enum234Group]
  · simp [enum234Group]

theorem enum234_nodup (q : Nat) : (enum234 q).Nodup := by
  apply nodup_flatMap_separated _ _ List.nodup_range
  · intro k hk
    exact enum234Group_nodup q k (List.mem_range.mp hk)
  · intro k hk j hj z hz w hw heq
    have hzk := enum234Group_tag q k (List.mem_range.mp hk) z hz
    have hwj := enum234Group_tag q j (List.mem_range.mp hj) w hw
    subst w
    omega

theorem enum234_length (q : Nat) (hq : 4≤q) :
    ((enum234 q).length : Int)=6*(q:Int)-6 := by
  have h0 := pairs_length_constant (fun r k => NF234.kr (rankP q r) k) 0 (2*q-3) (fun _ => 0) 2
  change (enum234Group q 0).length=(2*q-3)*2 at h0
  have h1 : (enum234Group q 1).length=2*q-5 := by simp [enum234Group,enumP]
  have h2 : (enum234Group q 2).length=2 := rfl
  have h3 : (enum234Group q 3).length=2 := rfl
  have h4 : (enum234Group q 4).length=1 := rfl
  have he : enum234 q=enum234Group q 0 ++ enum234Group q 1 ++ enum234Group q 2 ++ enum234Group q 3 ++ enum234Group q 4 := by
    have hr : List.range 5=[0,1,2,3,4] := by decide
    unfold enum234
    rw [hr]
    simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc]
  rw [he]
  simp only [List.length_append,Int.natCast_add,h0,h1,h2,h3,h4]
  omega
end LuRazClosure
