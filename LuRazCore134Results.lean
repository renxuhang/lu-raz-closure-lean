import LuRazCore134Enumeration
import LuRazMixedResults
namespace LuRazClosure
open LuRazEnumeration
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

def core134Members (q : Nat) : List (Nat → Prop) := (enum134 q).map (NF134.eval q)

theorem core134_members_nodup (q : Nat) (hq : 4≤q) : (core134Members q).Nodup := by
  apply nodup_map_on _ _ (enum134_nodup q)
  intro a ha b hb heq
  apply NF134.unique q hq a b ((enum134_exact q hq a).mp ha) ((enum134_exact q hq b).mp hb)
  intro e
  exact Iff.of_eq (congrFun heq e)

theorem core134_members_exact (q : Nat) (hq : 4≤q) (R : Nat → Prop) :
    R∈core134Members q ↔ Generated q R ∧ Core134 R := by
  constructor
  · intro hR
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hR
    have hv := (enum134_exact q hq z).mp hz
    exact (core134_closure_exact q hq (z.eval q)).mpr ⟨z,hv,fun _ => Iff.rfl⟩
  · intro hR
    obtain ⟨z,hz,heq⟩ := (core134_closure_exact q hq R).mp hR
    apply List.mem_map.mpr
    refine ⟨z,(enum134_exact q hq z).mpr hz,?_⟩
    funext e
    exact propext (heq e).symm

theorem core134_cardinality (q : Nat) (hq : 4≤q) :
    ∃ l : List (Nat → Prop), l.Nodup ∧
      (∀ R, R∈l ↔ Generated q R ∧ Core134 R) ∧
      (l.length : Int)=10*(q:Int)-16 := by
  refine ⟨core134Members q,core134_members_nodup q hq,core134_members_exact q hq,?_⟩
  simpa only [core134Members,List.length_map] using enum134_length q hq

def FinCore134 (q : Nat) (hq : 4≤q) (T : Fin (4*q) → Prop) : Prop :=
  T ⟨0,by omega⟩ ∧ ¬T ⟨1,by omega⟩ ∧ T ⟨2,by omega⟩ ∧ T ⟨3,by omega⟩

theorem fin_core134_iff (q : Nat) (hq : 4≤q) (T : Fin (4*q) → Prop) :
    Core134 (Lift q T) ↔ FinCore134 q hq T := by
  unfold Core134 FinCore134
  rw [lift_at q T 1 (by omega),lift_at q T 2 (by omega),
      lift_at q T 3 (by omega),lift_at q T 4 (by omega)]

theorem core134_finite_cardinality (q : Nat) (hq : 4≤q) :
    ∃ l : List (Fin (4*q) → Prop), l.Nodup ∧
      (∀ T, T∈l ↔ FinGenerated q T ∧ FinCore134 q hq T) ∧
      (l.length : Int)=10*(q:Int)-16 := by
  obtain ⟨l,hn,he,hl⟩ := core134_cardinality q hq
  have ht := transfer_enumeration q hq Core134 l hn he
  refine ⟨l.map (Restrict q),ht.1,?_,?_⟩
  · intro T
    exact (ht.2.1 T).trans (and_congr Iff.rfl (fin_core134_iff q hq T))
  · rw [List.length_map]
    exact hl

theorem core134_finite_for_every_x (x : Nat) (hx : 3≤x) :
    ∃ l : List (Fin (4*(x+1)) → Prop), l.Nodup ∧
      (∀ T, T∈l ↔ FinGenerated (x+1) T ∧ FinCore134 (x+1) (by omega) T) ∧
      (l.length : Int)=10*(x:Int)-6 := by
  obtain ⟨l,hn,he,hl⟩ := core134_finite_cardinality (x+1) (by omega)
  refine ⟨l,hn,he,?_⟩
  simp only [Int.natCast_add,Int.natCast_one,Int.mul_add,Int.mul_one] at hl
  omega
end LuRazClosure
