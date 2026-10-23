import LuRazSmallUnique
import LuRazFiniteClosure
import LuRazMixedResults

namespace LuRazClosure
open LuRazEnumeration
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

def allSmall : List NFSmall := [.bOnly,.aOnly,.ab,.dOnly,.ad,.cOnly,.cb,.eOnly,.ae,.ce,.ac,.acb]
def enumSmall (k : Nat) : List NFSmall := allSmall.filter (fun z => decide (z.tag=k))
def smallCount : Nat → Nat
  | 0 => 1 | 1 => 2 | 2 => 1 | 3 => 1 | 4 => 2 | 5 => 5 | _ => 0
def smallMembers (q k : Nat) : List (Nat → Prop) := (enumSmall k).map (NFSmall.eval q)

theorem allSmall_nodup : allSmall.Nodup := by decide
theorem allSmall_mem (z : NFSmall) : z∈allSmall := by cases z <;> simp [allSmall]

theorem enumSmall_exact (k : Nat) (z : NFSmall) : z∈enumSmall k ↔ z.tag=k := by
  constructor
  · intro h
    exact of_decide_eq_true (List.mem_filter.mp h).2
  · intro h
    exact List.mem_filter.mpr ⟨allSmall_mem z,decide_eq_true h⟩

theorem enumSmall_nodup (k : Nat) : (enumSmall k).Nodup :=
  List.Nodup.sublist List.filter_sublist allSmall_nodup

theorem enumSmall_length (k : Nat) (hk : k≤5) : (enumSmall k).length=smallCount k := by
  have hc : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 := by omega
  rcases hc with h | h | h | h | h | h <;> subst k <;> decide

theorem small_members_nodup (q k : Nat) (hq : 4≤q) : (smallMembers q k).Nodup := by
  apply nodup_map_on _ _ (enumSmall_nodup k)
  intro a _ b _ heq
  exact NFSmall.unique q hq a b (fun e => Iff.of_eq (congrFun heq e))

theorem small_members_exact (q k : Nat) (hq : 4≤q) (R : Nat → Prop) :
    R∈smallMembers q k ↔ Generated q R ∧ CoreSmallAt k R := by
  constructor
  · intro hR
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hR
    have htag := (enumSmall_exact k z).mp hz
    have hc := NFSmall.core q hq z
    rw [htag] at hc
    exact ⟨NFSmall.generated q hq z,hc⟩
  · rintro ⟨hg,hc⟩
    obtain ⟨z,heq⟩ := (small_closure_exact q hq R).mp ⟨hg,coreSmallAt_small k R hc⟩
    have hzcore := (coreSmallAt_congr z.tag R (z.eval q) heq).mpr (NFSmall.core q hq z)
    have htag : z.tag=k := (coreSmallAt_unique k z.tag R hc hzcore).symm
    refine List.mem_map.mpr ⟨z,(enumSmall_exact k z).mpr htag,?_⟩
    funext e
    exact propext (heq e).symm

theorem small_cardinality (q : Nat) (hq : 4≤q) (k : Nat) (hk : k≤5) :
    ∃ l : List (Nat → Prop), l.Nodup ∧
      (∀ R, R∈l ↔ Generated q R ∧ CoreSmallAt k R) ∧ l.length=smallCount k := by
  refine ⟨smallMembers q k,small_members_nodup q k hq,small_members_exact q k hq,?_⟩
  simpa only [smallMembers,List.length_map] using enumSmall_length k hk

def FinSmallAt (q : Nat) (hq : 4≤q) (k : Nat) (T : Fin (4*q) → Prop) : Prop := k≤5 ∧
  (T ⟨0,by omega⟩ ↔ k=1 ∨ k=3 ∨ k=5) ∧
  (T ⟨1,by omega⟩ ↔ k=2 ∨ k=3) ∧
  (T ⟨2,by omega⟩ ↔ k=4 ∨ k=5) ∧ ¬T ⟨3,by omega⟩

theorem fin_small_iff (q : Nat) (hq : 4≤q) (k : Nat) (T : Fin (4*q) → Prop) :
    CoreSmallAt k (Lift q T) ↔ FinSmallAt q hq k T := by
  unfold CoreSmallAt FinSmallAt
  rw [lift_at q T 1 (by omega),lift_at q T 2 (by omega),
      lift_at q T 3 (by omega),lift_at q T 4 (by omega)]

theorem small_finite_cardinality (q : Nat) (hq : 4≤q) (k : Nat) (hk : k≤5) :
    ∃ l : List (Fin (4*q) → Prop), l.Nodup ∧
      (∀ T, T∈l ↔ FinGenerated q T ∧ FinSmallAt q hq k T) ∧ l.length=smallCount k := by
  obtain ⟨l,hn,he,hl⟩ := small_cardinality q hq k hk
  have ht := transfer_enumeration q hq (CoreSmallAt k) l hn he
  refine ⟨l.map (Restrict q),ht.1,?_,?_⟩
  · intro T
    exact (ht.2.1 T).trans (and_congr Iff.rfl (fin_small_iff q hq k T))
  · rw [List.length_map]
    exact hl

theorem small_finite_for_every_x (x : Nat) (hx : 3≤x) (k : Nat) (hk : k≤5) :
    ∃ l : List (Fin (4*(x+1)) → Prop), l.Nodup ∧
      (∀ T, T∈l ↔ FinGenerated (x+1) T ∧ FinSmallAt (x+1) (by omega) k T) ∧
      l.length=smallCount k := small_finite_cardinality (x+1) (by omega) k hk

end LuRazClosure
