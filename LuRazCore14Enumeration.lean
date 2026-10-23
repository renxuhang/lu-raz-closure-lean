import LuRazCore14Unique
import EnumerationCounting

namespace LuRazClosure
open LuRazEnumeration
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

def NF14.tag : NF14 → Nat
  | .base _ _ => 0
  | .agap _ _ => 1
  | .bgap _ _ => 2
  | .joined _ => 3
  | .doubleGap => 4
  | .ajoined _ => 5

def enum14Group (q : Nat) : Nat → List NF14
  | 0 => pairs NF14.base 5 (2*q-3) (g q) (fun a => 4*q-2-g q a)
  | 1 => pairs NF14.agap (q+4) (q-2) (g q) (fun a => 4*q-2-g q a)
  | 2 => pairs NF14.bgap 5 q (g q) (fun a => 3*q+1-g q a)
  | 3 => (List.range' 5 (2*q-3)).map NF14.joined
  | 4 => [.doubleGap]
  | 5 => (List.range' (q+4) (q-2)).map NF14.ajoined
  | _ => []

def enum14 (q : Nat) : List NF14 := (List.range 6).flatMap (enum14Group q)

theorem NF14.tag_lt (z : NF14) : z.tag < 6 := by cases z <;> simp [NF14.tag]

theorem enum14Group_tag (q k : Nat) (hk : k<6) (z : NF14)
    (hz : z ∈ enum14Group q k) : z.tag=k := by
  have hc : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 := by omega
  rcases hc with h | h | h | h | h | h <;> subst k
  · obtain ⟨a,b,_,_,rfl⟩ := (pairs_mem _ _ _ _ _ _).mp hz
    rfl
  · obtain ⟨a,b,_,_,rfl⟩ := (pairs_mem _ _ _ _ _ _).mp hz
    rfl
  · obtain ⟨a,b,_,_,rfl⟩ := (pairs_mem _ _ _ _ _ _).mp hz
    rfl
  · obtain ⟨a,_,rfl⟩ := List.mem_map.mp hz
    rfl
  · have he : z=NF14.doubleGap := by simpa only [enum14Group,List.mem_cons,List.not_mem_nil,or_false] using hz
    subst z; rfl
  · obtain ⟨a,_,rfl⟩ := List.mem_map.mp hz
    rfl

theorem enum14Group_valid (q : Nat) (hq : 4 ≤ q) (k : Nat) (hk : k<6)
    (z : NF14) (hz : z ∈ enum14Group q k) : z.Valid q := by
  have hc : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 := by omega
  rcases hc with h | h | h | h | h | h <;> subst k
  · obtain ⟨a,b,ha,hb,rfl⟩ := (pairs_mem _ _ _ _ _ _).mp hz
    have ha' : 5≤a ∧ a≤2*q+1 := by omega
    have hg := g_bounds q a hq ha'
    change JReachable q a b
    unfold JReachable
    omega
  · obtain ⟨a,b,ha,hb,rfl⟩ := (pairs_mem _ _ _ _ _ _).mp hz
    have ha' : 5≤a ∧ a≤2*q+1 := by omega
    have hg := g_bounds q a hq ha'
    change JReachable q a b ∧ q+4≤a
    unfold JReachable
    omega
  · obtain ⟨a,b,ha,hb,rfl⟩ := (pairs_mem _ _ _ _ _ _).mp hz
    have ha' : 5≤a ∧ a≤2*q+1 := by omega
    have hg := g_bounds q a hq ha'
    change JReachable q a b ∧ b≤3*q
    unfold JReachable
    omega
  · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hz
    have ha' := (range_mem a 5 (2*q-3)).mp ha
    change 5≤a ∧ a≤2*q+1
    omega
  · have he : z=NF14.doubleGap := by simpa only [enum14Group,List.mem_cons,List.not_mem_nil,or_false] using hz
    subst z; exact True.intro
  · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hz
    have ha' := (range_mem a (q+4) (q-2)).mp ha
    change q+4≤a ∧ a≤2*q+1
    omega

theorem NF14.valid_mem_group (q : Nat) (hq : 4 ≤ q) (z : NF14) (hz : z.Valid q) :
    z ∈ enum14Group q z.tag := by
  cases z with
  | base a b =>
    change NF14.base a b ∈ pairs NF14.base 5 (2*q-3) (g q) (fun t => 4*q-2-g q t)
    apply (pairs_mem _ _ _ _ _ _).mpr
    have hz' : JReachable q a b := hz
    unfold JReachable at hz'
    exact ⟨a,b,by omega,by omega,rfl⟩
  | agap a b =>
    change NF14.agap a b ∈ pairs NF14.agap (q+4) (q-2) (g q) (fun t => 4*q-2-g q t)
    apply (pairs_mem _ _ _ _ _ _).mpr
    have hz' : JReachable q a b ∧ q+4≤a := hz
    unfold JReachable at hz'
    exact ⟨a,b,by omega,by omega,rfl⟩
  | bgap a b =>
    change NF14.bgap a b ∈ pairs NF14.bgap 5 q (g q) (fun t => 3*q+1-g q t)
    apply (pairs_mem _ _ _ _ _ _).mpr
    have hz' : JReachable q a b ∧ b≤3*q := hz
    have hga := hz'.1.2.2.2.2
    have ha : a≤q+4 := by unfold g at hga; split at hga <;> omega
    unfold JReachable at hz'
    exact ⟨a,b,by omega,by omega,rfl⟩
  | joined a =>
    change NF14.joined a ∈ (List.range' 5 (2*q-3)).map NF14.joined
    apply List.mem_map.mpr
    have ha : 5≤a ∧ a≤2*q+1 := hz
    exact ⟨a,(range_mem _ _ _).mpr (by omega),rfl⟩
  | doubleGap => simp only [enum14Group,NF14.tag,List.mem_cons,true_or]
  | ajoined a =>
    change NF14.ajoined a ∈ (List.range' (q+4) (q-2)).map NF14.ajoined
    apply List.mem_map.mpr
    have ha : q+4≤a ∧ a≤2*q+1 := hz
    exact ⟨a,(range_mem _ _ _).mpr (by omega),rfl⟩

theorem enum14_exact (q : Nat) (hq : 4 ≤ q) (z : NF14) : z ∈ enum14 q ↔ z.Valid q := by
  constructor
  · intro hz
    obtain ⟨k,hk,hzk⟩ := List.mem_flatMap.mp hz
    exact enum14Group_valid q hq k (List.mem_range.mp hk) z hzk
  · intro hz
    exact List.mem_flatMap.mpr ⟨z.tag,List.mem_range.mpr (NF14.tag_lt z),NF14.valid_mem_group q hq z hz⟩

theorem enum14Group_nodup (q k : Nat) (hk : k<6) : (enum14Group q k).Nodup := by
  have hc : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 := by omega
  rcases hc with h | h | h | h | h | h <;> subst k
  · apply pairs_nodup
    intro a b c d h
    exact NF14.base.inj h
  · apply pairs_nodup
    intro a b c d h
    exact NF14.agap.inj h
  · apply pairs_nodup
    intro a b c d h
    exact NF14.bgap.inj h
  · apply nodup_map_injective NF14.joined (fun _ _ h => NF14.joined.inj h) _ List.nodup_range'
  · simp [enum14Group]
  · apply nodup_map_injective NF14.ajoined (fun _ _ h => NF14.ajoined.inj h) _ List.nodup_range'

theorem enum14_nodup (q : Nat) : (enum14 q).Nodup := by
  apply nodup_flatMap_separated _ _ List.nodup_range
  · intro k hk
    exact enum14Group_nodup q k (List.mem_range.mp hk)
  · intro k hk j hj z hz w hw heq
    have hzk := enum14Group_tag q k (List.mem_range.mp hk) z hz
    have hwj := enum14Group_tag q j (List.mem_range.mp hj) w hw
    subst w
    omega

end LuRazClosure

