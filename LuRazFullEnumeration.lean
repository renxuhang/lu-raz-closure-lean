import LuRazFullUnique
namespace LuRazClosure
open LuRazEnumeration
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000
set_option linter.unusedSimpArgs false

def NFFull.tag : NFFull → Nat
  | .noNInterval _ => 0
  | .noNMJRight _ => 1
  | .noNMJLeft _ => 2
  | .noNMK _ => 3
  | .noNCMJ _ => 4
  | .noH1Short _ _ => 5
  | .noH1ZL _ => 6
  | .noH1Exception  => 7
  | .noH2 _ => 8
  | .noFive _ => 9
  | .leftGap _ _ => 10
  | .full  => 11
  | .rightGap _ _ => 12
  | .isolatedR _ _ => 13

def enumFullGroup (q : Nat) : Nat → List NFFull
  | 0 => (List.range' (0) (2)).map NFFull.noNInterval
  | 1 => (List.range' (2*q+2) (q-1)).map NFFull.noNMJRight
  | 2 => (List.range' (q+5) (q-3)).map NFFull.noNMJLeft
  | 3 => (List.range' (0) (2)).map NFFull.noNMK
  | 4 => (List.range' (2*q+2) (q-2)).map NFFull.noNCMJ
  | 5 => pairs NFFull.noH1Short (4) (2*q-3) (fun _ => 0) (fun _ => 2)
  | 6 => (List.range' (2*q+4) (2*q-4)).map NFFull.noH1ZL
  | 7 => [.noH1Exception]
  | 8 => (List.range' (2*q+3) (2*q-2)).map NFFull.noH2
  | 9 => (List.range' (6) (2*q-4)).map NFFull.noFive
  | 10 => pairs NFFull.leftGap (5) (2*q-5) (fun p => p+2) (fun p => 2*q-p)
  | 11 => [.full]
  | 12 => pairs NFFull.rightGap (2*q+2) (2*q-3) (fun b => b+2) (fun b => 4*q-b-1)
  | 13 => pairs NFFull.isolatedR (2*q+2) (q-2) (fun _ => 3*q+3) (fun _ => q-2)
  | _ => []
def enumFull (q : Nat) : List NFFull := (List.range 14).flatMap (enumFullGroup q)

theorem NFFull.tag_lt (z : NFFull) : z.tag<14 := by cases z <;> simp [NFFull.tag]

theorem enumFullGroup_tag (q k : Nat) (hk : k<14) (z : NFFull) (hz : z∈enumFullGroup q k) : z.tag=k := by
  have hc : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨ k=7 ∨ k=8 ∨ k=9 ∨ k=10 ∨ k=11 ∨ k=12 ∨ k=13 := by omega
  rcases hc with h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst k
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
  · obtain ⟨a,b,_,_,rfl⟩ := (pairs_mem _ _ _ _ _ _).mp hz
    rfl
  · obtain ⟨a,_,rfl⟩ := List.mem_map.mp hz
    rfl
  · have he : z=NFFull.noH1Exception := by simpa [enumFullGroup] using hz
    subst z; rfl
  · obtain ⟨a,_,rfl⟩ := List.mem_map.mp hz
    rfl
  · obtain ⟨a,_,rfl⟩ := List.mem_map.mp hz
    rfl
  · obtain ⟨a,b,_,_,rfl⟩ := (pairs_mem _ _ _ _ _ _).mp hz
    rfl
  · have he : z=NFFull.full := by simpa [enumFullGroup] using hz
    subst z; rfl
  · obtain ⟨a,b,_,_,rfl⟩ := (pairs_mem _ _ _ _ _ _).mp hz
    rfl
  · obtain ⟨a,b,_,_,rfl⟩ := (pairs_mem _ _ _ _ _ _).mp hz
    rfl

theorem enumFullGroup_valid (q : Nat) (hq : 4≤q) (k : Nat) (hk : k<14)
    (z : NFFull) (hz : z∈enumFullGroup q k) : z.Valid q := by
  have hc : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨ k=7 ∨ k=8 ∨ k=9 ∨ k=10 ∨ k=11 ∨ k=12 ∨ k=13 := by omega
  rcases hc with h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst k
  · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hz
    have hb := (range_mem _ _ _).mp ha
    simp only [NFFull.Valid]
    omega
  · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hz
    have hb := (range_mem _ _ _).mp ha
    simp only [NFFull.Valid]
    omega
  · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hz
    have hb := (range_mem _ _ _).mp ha
    simp only [NFFull.Valid]
    omega
  · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hz
    have hb := (range_mem _ _ _).mp ha
    simp only [NFFull.Valid]
    omega
  · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hz
    have hb := (range_mem _ _ _).mp ha
    simp only [NFFull.Valid]
    omega
  · obtain ⟨a,b,ha,hb,rfl⟩ := (pairs_mem _ _ _ _ _ _).mp hz
    simp only [NFFull.Valid]
    omega
  · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hz
    have hb := (range_mem _ _ _).mp ha
    simp only [NFFull.Valid]
    omega
  · have he : z=NFFull.noH1Exception := by simpa [enumFullGroup] using hz
    subst z; exact True.intro
  · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hz
    have hb := (range_mem _ _ _).mp ha
    simp only [NFFull.Valid]
    omega
  · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hz
    have hb := (range_mem _ _ _).mp ha
    simp only [NFFull.Valid]
    omega
  · obtain ⟨a,b,ha,hb,rfl⟩ := (pairs_mem _ _ _ _ _ _).mp hz
    simp only [NFFull.Valid]
    omega
  · have he : z=NFFull.full := by simpa [enumFullGroup] using hz
    subst z; exact True.intro
  · obtain ⟨a,b,ha,hb,rfl⟩ := (pairs_mem _ _ _ _ _ _).mp hz
    simp only [NFFull.Valid]
    omega
  · obtain ⟨a,b,ha,hb,rfl⟩ := (pairs_mem _ _ _ _ _ _).mp hz
    simp only [NFFull.Valid]
    omega

theorem NFFull.valid_mem_group (q : Nat) (hq : 4≤q) (z : NFFull) (hz : z.Valid q) : z∈enumFullGroup q z.tag := by
  cases z with
  | noNInterval k =>
    have hb := hz
    simp only [NFFull.Valid] at hb
    exact List.mem_map.mpr ⟨k,(range_mem _ _ _).mpr (by omega),rfl⟩
  | noNMJRight b =>
    have hb := hz
    simp only [NFFull.Valid] at hb
    exact List.mem_map.mpr ⟨b,(range_mem _ _ _).mpr (by omega),rfl⟩
  | noNMJLeft a =>
    have hb := hz
    simp only [NFFull.Valid] at hb
    exact List.mem_map.mpr ⟨a,(range_mem _ _ _).mpr (by omega),rfl⟩
  | noNMK k =>
    have hb := hz
    simp only [NFFull.Valid] at hb
    exact List.mem_map.mpr ⟨k,(range_mem _ _ _).mpr (by omega),rfl⟩
  | noNCMJ b =>
    have hb := hz
    simp only [NFFull.Valid] at hb
    exact List.mem_map.mpr ⟨b,(range_mem _ _ _).mpr (by omega),rfl⟩
  | noH1Short p k =>
    have hb := hz
    simp only [NFFull.Valid] at hb
    exact (pairs_mem _ _ _ _ _ _).mpr ⟨p,k,by omega,by omega,rfl⟩
  | noH1ZL a =>
    have hb := hz
    simp only [NFFull.Valid] at hb
    exact List.mem_map.mpr ⟨a,(range_mem _ _ _).mpr (by omega),rfl⟩
  | noH1Exception  =>
    simp [enumFullGroup,NFFull.tag]
  | noH2 a =>
    have hb := hz
    simp only [NFFull.Valid] at hb
    exact List.mem_map.mpr ⟨a,(range_mem _ _ _).mpr (by omega),rfl⟩
  | noFive a =>
    have hb := hz
    simp only [NFFull.Valid] at hb
    exact List.mem_map.mpr ⟨a,(range_mem _ _ _).mpr (by omega),rfl⟩
  | leftGap p a =>
    have hb := hz
    simp only [NFFull.Valid] at hb
    exact (pairs_mem _ _ _ _ _ _).mpr ⟨p,a,by omega,by omega,rfl⟩
  | full  =>
    simp [enumFullGroup,NFFull.tag]
  | rightGap b c =>
    have hb := hz
    simp only [NFFull.Valid] at hb
    exact (pairs_mem _ _ _ _ _ _).mpr ⟨b,c,by omega,by omega,rfl⟩
  | isolatedR b c =>
    have hb := hz
    simp only [NFFull.Valid] at hb
    exact (pairs_mem _ _ _ _ _ _).mpr ⟨b,c,by omega,by omega,rfl⟩

theorem enumFull_exact (q : Nat) (hq : 4≤q) (z : NFFull) : z∈enumFull q ↔ z.Valid q := by
  constructor
  · intro hz
    obtain ⟨k,hk,hzk⟩ := List.mem_flatMap.mp hz
    exact enumFullGroup_valid q hq k (List.mem_range.mp hk) z hzk
  · intro hz
    exact List.mem_flatMap.mpr ⟨z.tag,List.mem_range.mpr (NFFull.tag_lt z),NFFull.valid_mem_group q hq z hz⟩

theorem enumFullGroup_nodup (q k : Nat) (hk : k<14) : (enumFullGroup q k).Nodup := by
  have hc : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨ k=7 ∨ k=8 ∨ k=9 ∨ k=10 ∨ k=11 ∨ k=12 ∨ k=13 := by omega
  rcases hc with h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst k
  · exact nodup_map_injective NFFull.noNInterval (fun _ _ h => NFFull.noNInterval.inj h) _ List.nodup_range'
  · exact nodup_map_injective NFFull.noNMJRight (fun _ _ h => NFFull.noNMJRight.inj h) _ List.nodup_range'
  · exact nodup_map_injective NFFull.noNMJLeft (fun _ _ h => NFFull.noNMJLeft.inj h) _ List.nodup_range'
  · exact nodup_map_injective NFFull.noNMK (fun _ _ h => NFFull.noNMK.inj h) _ List.nodup_range'
  · exact nodup_map_injective NFFull.noNCMJ (fun _ _ h => NFFull.noNCMJ.inj h) _ List.nodup_range'
  · exact pairs_nodup NFFull.noH1Short (fun _ _ _ _ h => NFFull.noH1Short.inj h) _ _ _ _
  · exact nodup_map_injective NFFull.noH1ZL (fun _ _ h => NFFull.noH1ZL.inj h) _ List.nodup_range'
  · simp [enumFullGroup]
  · exact nodup_map_injective NFFull.noH2 (fun _ _ h => NFFull.noH2.inj h) _ List.nodup_range'
  · exact nodup_map_injective NFFull.noFive (fun _ _ h => NFFull.noFive.inj h) _ List.nodup_range'
  · exact pairs_nodup NFFull.leftGap (fun _ _ _ _ h => NFFull.leftGap.inj h) _ _ _ _
  · simp [enumFullGroup]
  · exact pairs_nodup NFFull.rightGap (fun _ _ _ _ h => NFFull.rightGap.inj h) _ _ _ _
  · exact pairs_nodup NFFull.isolatedR (fun _ _ _ _ h => NFFull.isolatedR.inj h) _ _ _ _

theorem enumFull_nodup (q : Nat) : (enumFull q).Nodup := by
  apply nodup_flatMap_separated _ _ List.nodup_range
  · intro k hk
    exact enumFullGroup_nodup q k (List.mem_range.mp hk)
  · intro k hk j hj z hz w hw heq
    have hzk := enumFullGroup_tag q k (List.mem_range.mp hk) z hz
    have hwj := enumFullGroup_tag q j (List.mem_range.mp hj) w hw
    subst w
    omega
end LuRazClosure
