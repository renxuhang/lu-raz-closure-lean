import LuRazCore124Unique
import EnumerationCounting
namespace LuRazClosure
open LuRazEnumeration
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

def NF124.tag : NF124 → Nat
  | .interval _ _ => 0 | .agap _ _ => 1 | .ak _ => 2

def ak124 : List NF24 := [.k1,.k2,.joinK,.fill1,.fill2]

def enum124Group (q : Nat) : Nat → List NF124
  | 0 => pairs NF124.interval 5 (2*q-3) (fun _ => 0) (fun _ => 3)
  | 1 => pairs NF124.agap (q+4) (q-2) (fun _ => 0) (fun _ => 3)
  | 2 => ak124.map NF124.ak
  | _ => []
def enum124 (q : Nat) : List NF124 := (List.range 3).flatMap (enum124Group q)

theorem NF124.tag_lt (z : NF124) : z.tag<3 := by cases z <;> simp [NF124.tag]
theorem ak124_exact (z : NF24) : z∈ak124 ↔ z≠.dBig := by cases z <;> decide

theorem enum124Group_tag (q k : Nat) (hk : k<3) (z : NF124)
    (hz : z∈enum124Group q k) : z.tag=k := by
  have hc : k=0 ∨ k=1 ∨ k=2 := by omega
  rcases hc with h | h | h <;> subst k
  · obtain ⟨a,b,_,_,rfl⟩ := (pairs_mem _ _ _ _ _ _).mp hz
    rfl
  · obtain ⟨a,b,_,_,rfl⟩ := (pairs_mem _ _ _ _ _ _).mp hz
    rfl
  · obtain ⟨a,_,rfl⟩ := List.mem_map.mp hz
    rfl

theorem enum124Group_valid (q : Nat) (hq : 4≤q) (k : Nat) (hk : k<3)
    (z : NF124) (hz : z∈enum124Group q k) : z.Valid q := by
  have hc : k=0 ∨ k=1 ∨ k=2 := by omega
  rcases hc with h | h | h <;> subst k
  · obtain ⟨a,b,ha,hb,rfl⟩ := (pairs_mem _ _ _ _ _ _).mp hz
    change (5≤a ∧ a≤2*q+1) ∧ b<3
    omega
  · obtain ⟨a,b,ha,hb,rfl⟩ := (pairs_mem _ _ _ _ _ _).mp hz
    change (q+4≤a ∧ a≤2*q+1) ∧ b<3
    omega
  · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hz
    exact (ak124_exact a).mp ha

theorem NF124.valid_mem_group (q : Nat) (hq : 4≤q) (z : NF124)
    (hz : z.Valid q) : z∈enum124Group q z.tag := by
  cases z with
  | interval a k =>
    apply (pairs_mem _ _ _ _ _ _).mpr
    exact ⟨a,k,by have hb : (5≤a ∧ a≤2*q+1) ∧ k<3 := hz; omega,by have hb : (5≤a ∧ a≤2*q+1) ∧ k<3 := hz; omega,rfl⟩
  | agap a k =>
    apply (pairs_mem _ _ _ _ _ _).mpr
    exact ⟨a,k,by have hb : (q+4≤a ∧ a≤2*q+1) ∧ k<3 := hz; omega,by have hb : (q+4≤a ∧ a≤2*q+1) ∧ k<3 := hz; omega,rfl⟩
  | ak z => exact List.mem_map.mpr ⟨z,(ak124_exact z).mpr hz,rfl⟩

theorem enum124_exact (q : Nat) (hq : 4≤q) (z : NF124) : z∈enum124 q ↔ z.Valid q := by
  constructor
  · intro hz
    obtain ⟨k,hk,hzk⟩ := List.mem_flatMap.mp hz
    exact enum124Group_valid q hq k (List.mem_range.mp hk) z hzk
  · intro hz
    exact List.mem_flatMap.mpr ⟨z.tag,List.mem_range.mpr (NF124.tag_lt z),NF124.valid_mem_group q hq z hz⟩

theorem enum124Group_nodup (q k : Nat) (hk : k<3) : (enum124Group q k).Nodup := by
  have hc : k=0 ∨ k=1 ∨ k=2 := by omega
  rcases hc with h | h | h <;> subst k
  · apply pairs_nodup
    intro a b c d heq
    exact NF124.interval.inj heq
  · apply pairs_nodup
    intro a b c d heq
    exact NF124.agap.inj heq
  · apply nodup_map_injective NF124.ak (fun _ _ h => NF124.ak.inj h)
    decide

theorem enum124_nodup (q : Nat) : (enum124 q).Nodup := by
  apply nodup_flatMap_separated _ _ List.nodup_range
  · intro k hk
    exact enum124Group_nodup q k (List.mem_range.mp hk)
  · intro k hk j hj z hz w hw heq
    have hzk := enum124Group_tag q k (List.mem_range.mp hk) z hz
    have hwj := enum124Group_tag q j (List.mem_range.mp hj) w hw
    subst w
    omega

theorem enum124_length (q : Nat) (hq : 4≤q) :
    ((enum124 q).length : Int)=9*(q:Int)-10 := by
  have h0 := pairs_length_constant NF124.interval 5 (2*q-3) (fun _ => 0) 3
  have h1 := pairs_length_constant NF124.agap (q+4) (q-2) (fun _ => 0) 3
  have h2 : (enum124Group q 2).length=5 := rfl
  have he : enum124 q=enum124Group q 0 ++ enum124Group q 1 ++ enum124Group q 2 := by
    have hr : List.range 3=[0,1,2] := by decide
    unfold enum124
    rw [hr]
    simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc]
  change (enum124Group q 0).length=(2*q-3)*3 at h0
  change (enum124Group q 1).length=(q-2)*3 at h1
  rw [he]
  simp only [List.length_append,Int.natCast_add,h0,h1,h2]
  omega

end LuRazClosure
