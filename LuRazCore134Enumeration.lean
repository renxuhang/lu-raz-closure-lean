import LuRazCore134Unique
namespace LuRazClosure
open LuRazEnumeration
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

def NF134.tag : NF134 → Nat
  | .ej _ => 0
  | .aej _ => 1
  | .cj _ => 2
  | .zj _ => 3
  | .czj _ => 4
  | .zjb _ => 5
  | .cjb _ => 6
  | .extra _ => 7

def enum134Group (q : Nat) : Nat → List NF134
  | 0 => (List.range' (5) (2*q-3)).map NF134.ej
  | 1 => (List.range' (q+4) (q-2)).map NF134.aej
  | 2 => ((List.range' (2*q+2) (2*q-4)).filter (fun b => decide (b≠3*q))).map NF134.cj
  | 3 => (List.range' (2*q+2) (2*q-4)).map NF134.zj
  | 4 => (List.range' (2*q+2) (q-2)).map NF134.czj
  | 5 => (List.range' (2*q+2) (q-1)).map NF134.zjb
  | 6 => (List.range' (2*q+2) (q-2)).map NF134.cjb
  | 7 => (List.range' (0) (3)).map NF134.extra
  | _ => []
def enum134 (q : Nat) : List NF134 := (List.range 8).flatMap (enum134Group q)

theorem NF134.tag_lt (z : NF134) : z.tag<8 := by cases z <;> simp [NF134.tag]

theorem enum134Group_tag (q k : Nat) (hk : k<8) (z : NF134) (hz : z∈enum134Group q k) : z.tag=k := by
  have hc : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨ k=7 := by omega
  rcases hc with h | h | h | h | h | h | h | h <;> subst k
  · obtain ⟨a,_,rfl⟩ := List.mem_map.mp hz
    rfl
  · obtain ⟨a,_,rfl⟩ := List.mem_map.mp hz
    rfl
  · obtain ⟨a,_,rfl⟩ := List.mem_map.mp hz
    rfl
  · obtain ⟨a,_,rfl⟩ := List.mem_map.mp hz
    rfl
  · obtain ⟨a,_,rfl⟩ := List.mem_map.mp hz
    rfl
  · obtain ⟨a,_,rfl⟩ := List.mem_map.mp hz
    rfl
  · obtain ⟨a,_,rfl⟩ := List.mem_map.mp hz
    rfl
  · obtain ⟨a,_,rfl⟩ := List.mem_map.mp hz
    rfl

theorem enum134Group_valid (q : Nat) (hq : 4≤q) (k : Nat) (hk : k<8)
    (z : NF134) (hz : z∈enum134Group q k) : z.Valid q := by
  have hc : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨ k=7 := by omega
  rcases hc with h | h | h | h | h | h | h | h <;> subst k
  · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hz
    have hb := (range_mem _ _ _).mp ha
    simp only [NF134.Valid]
    omega
  · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hz
    have hb := (range_mem _ _ _).mp ha
    simp only [NF134.Valid]
    omega
  · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hz
    have hf := List.mem_filter.mp ha
    have hb := (range_mem _ _ _).mp hf.1
    have hn := of_decide_eq_true hf.2
    simp only [NF134.Valid]
    omega
  · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hz
    have hb := (range_mem _ _ _).mp ha
    simp only [NF134.Valid]
    omega
  · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hz
    have hb := (range_mem _ _ _).mp ha
    simp only [NF134.Valid]
    omega
  · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hz
    have hb := (range_mem _ _ _).mp ha
    simp only [NF134.Valid]
    omega
  · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hz
    have hb := (range_mem _ _ _).mp ha
    simp only [NF134.Valid]
    omega
  · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hz
    have hb := (range_mem _ _ _).mp ha
    simp only [NF134.Valid]
    omega

theorem NF134.valid_mem_group (q : Nat) (hq : 4≤q) (z : NF134) (hz : z.Valid q) : z∈enum134Group q z.tag := by
  cases z with
  | ej a =>
    have hb := hz
    simp only [NF134.Valid] at hb
    apply List.mem_map.mpr
    exact ⟨a,(range_mem _ _ _).mpr (by omega),rfl⟩
  | aej a =>
    have hb := hz
    simp only [NF134.Valid] at hb
    apply List.mem_map.mpr
    exact ⟨a,(range_mem _ _ _).mpr (by omega),rfl⟩
  | cj a =>
    have hb := hz
    simp only [NF134.Valid] at hb
    apply List.mem_map.mpr
    exact ⟨a,List.mem_filter.mpr ⟨(range_mem _ _ _).mpr (by omega),decide_eq_true hb.2⟩,rfl⟩
  | zj a =>
    have hb := hz
    simp only [NF134.Valid] at hb
    apply List.mem_map.mpr
    exact ⟨a,(range_mem _ _ _).mpr (by omega),rfl⟩
  | czj a =>
    have hb := hz
    simp only [NF134.Valid] at hb
    apply List.mem_map.mpr
    exact ⟨a,(range_mem _ _ _).mpr (by omega),rfl⟩
  | zjb a =>
    have hb := hz
    simp only [NF134.Valid] at hb
    apply List.mem_map.mpr
    exact ⟨a,(range_mem _ _ _).mpr (by omega),rfl⟩
  | cjb a =>
    have hb := hz
    simp only [NF134.Valid] at hb
    apply List.mem_map.mpr
    exact ⟨a,(range_mem _ _ _).mpr (by omega),rfl⟩
  | extra a =>
    have hb := hz
    simp only [NF134.Valid] at hb
    apply List.mem_map.mpr
    exact ⟨a,(range_mem _ _ _).mpr (by omega),rfl⟩

theorem enum134_exact (q : Nat) (hq : 4≤q) (z : NF134) : z∈enum134 q ↔ z.Valid q := by
  constructor
  · intro hz
    obtain ⟨k,hk,hzk⟩ := List.mem_flatMap.mp hz
    exact enum134Group_valid q hq k (List.mem_range.mp hk) z hzk
  · intro hz
    exact List.mem_flatMap.mpr ⟨z.tag,List.mem_range.mpr (NF134.tag_lt z),NF134.valid_mem_group q hq z hz⟩

theorem enum134Group_nodup (q k : Nat) (hk : k<8) : (enum134Group q k).Nodup := by
  have hc : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨ k=7 := by omega
  rcases hc with h | h | h | h | h | h | h | h <;> subst k
  · apply nodup_map_injective NF134.ej (fun _ _ h => NF134.ej.inj h)
    exact List.nodup_range'
  · apply nodup_map_injective NF134.aej (fun _ _ h => NF134.aej.inj h)
    exact List.nodup_range'
  · apply nodup_map_injective NF134.cj (fun _ _ h => NF134.cj.inj h)
    exact List.Nodup.sublist List.filter_sublist List.nodup_range'
  · apply nodup_map_injective NF134.zj (fun _ _ h => NF134.zj.inj h)
    exact List.nodup_range'
  · apply nodup_map_injective NF134.czj (fun _ _ h => NF134.czj.inj h)
    exact List.nodup_range'
  · apply nodup_map_injective NF134.zjb (fun _ _ h => NF134.zjb.inj h)
    exact List.nodup_range'
  · apply nodup_map_injective NF134.cjb (fun _ _ h => NF134.cjb.inj h)
    exact List.nodup_range'
  · apply nodup_map_injective NF134.extra (fun _ _ h => NF134.extra.inj h)
    exact List.nodup_range'

theorem enum134_nodup (q : Nat) : (enum134 q).Nodup := by
  apply nodup_flatMap_separated _ _ List.nodup_range
  · intro k hk
    exact enum134Group_nodup q k (List.mem_range.mp hk)
  · intro k hk j hj z hz w hw heq
    have hzk := enum134Group_tag q k (List.mem_range.mp hk) z hz
    have hwj := enum134Group_tag q j (List.mem_range.mp hj) w hw
    subst w
    omega

theorem enum134_cj_length (q : Nat) (hq : 4≤q) :
    ((enum134Group q 2).length : Int)=2*(q:Int)-5 := by
  have hm : 3*q∈List.range' (2*q+2) (2*q-4) := (range_mem _ _ _).mpr (by omega)
  have h := filter_ne_length (List.range' (2*q+2) (2*q-4)) List.nodup_range' (3*q) hm
  simp only [List.length_range'] at h
  simp only [enum134Group,List.length_map]
  omega

theorem enum134_length (q : Nat) (hq : 4≤q) :
    ((enum134 q).length : Int)=10*(q:Int)-16 := by
  have h0 : (enum134Group q 0).length=2*q-3 := by simp [enum134Group]
  have h1 : (enum134Group q 1).length=q-2 := by simp [enum134Group]
  have h2 := enum134_cj_length q hq
  have h3 : (enum134Group q 3).length=2*q-4 := by simp [enum134Group]
  have h4 : (enum134Group q 4).length=q-2 := by simp [enum134Group]
  have h5 : (enum134Group q 5).length=q-1 := by simp [enum134Group]
  have h6 : (enum134Group q 6).length=q-2 := by simp [enum134Group]
  have h7 : (enum134Group q 7).length=3 := by simp [enum134Group]
  have he : enum134 q=enum134Group q 0 ++ enum134Group q 1 ++ enum134Group q 2 ++ enum134Group q 3 ++ enum134Group q 4 ++ enum134Group q 5 ++ enum134Group q 6 ++ enum134Group q 7 := by
    have hr : List.range 8=[0,1,2,3,4,5,6,7] := by decide
    unfold enum134
    rw [hr]
    simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc]
  rw [he]
  simp only [List.length_append,Int.natCast_add]
  omega
end LuRazClosure
