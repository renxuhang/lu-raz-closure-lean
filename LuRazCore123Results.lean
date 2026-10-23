import LuRazCore123Count
import LuRazMixedResults
namespace LuRazClosure
open LuRazEnumeration
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

def core123Members (q : Nat) : List (Nat → Prop) := (enum123 q).map (NF123.eval q)

theorem core123_members_nodup (q : Nat) (hq : 4≤q) : (core123Members q).Nodup := by
  apply nodup_map_on _ _ (enum123_nodup q)
  intro a ha b hb heq
  apply NF123.unique q hq a b ((enum123_exact q hq a).mp ha) ((enum123_exact q hq b).mp hb)
  intro e
  exact Iff.of_eq (congrFun heq e)

theorem core123_members_exact (q : Nat) (hq : 4≤q) (R : Nat → Prop) :
    R∈core123Members q ↔ Generated q R ∧ Core123 R := by
  constructor
  · intro hR
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hR
    have hv := (enum123_exact q hq z).mp hz
    exact (core123_closure_exact q hq (z.eval q)).mpr ⟨z,hv,fun _ => Iff.rfl⟩
  · intro hR
    obtain ⟨z,hz,heq⟩ := (core123_closure_exact q hq R).mp hR
    apply List.mem_map.mpr
    refine ⟨z,(enum123_exact q hq z).mpr hz,?_⟩
    funext e
    exact propext (heq e).symm

theorem core123_cardinality (q : Nat) (hq : 4≤q) :
    ∃ l : List (Nat → Prop), l.Nodup ∧
      (∀ R, R∈l ↔ Generated q R ∧ Core123 R) ∧
      2*(l.length : Int)=3*(q:Int)*(q:Int)+7*(q:Int)-14 := by
  refine ⟨core123Members q,core123_members_nodup q hq,core123_members_exact q hq,?_⟩
  simpa only [core123Members,List.length_map] using enum123_length q hq

def FinCore123 (q : Nat) (hq : 4≤q) (T : Fin (4*q) → Prop) : Prop :=
  T ⟨0,by omega⟩ ∧ T ⟨1,by omega⟩ ∧ T ⟨2,by omega⟩ ∧ ¬T ⟨3,by omega⟩

theorem fin_core123_iff (q : Nat) (hq : 4≤q) (T : Fin (4*q) → Prop) :
    Core123 (Lift q T) ↔ FinCore123 q hq T := by
  unfold Core123 FinCore123
  rw [lift_at q T 1 (by omega),lift_at q T 2 (by omega),
      lift_at q T 3 (by omega),lift_at q T 4 (by omega)]

theorem core123_finite_cardinality (q : Nat) (hq : 4≤q) :
    ∃ l : List (Fin (4*q) → Prop), l.Nodup ∧
      (∀ T, T∈l ↔ FinGenerated q T ∧ FinCore123 q hq T) ∧
      2*(l.length : Int)=3*(q:Int)*(q:Int)+7*(q:Int)-14 := by
  obtain ⟨l,hn,he,hl⟩ := core123_cardinality q hq
  have ht := transfer_enumeration q hq Core123 l hn he
  refine ⟨l.map (Restrict q),ht.1,?_,?_⟩
  · intro T
    exact (ht.2.1 T).trans (and_congr Iff.rfl (fin_core123_iff q hq T))
  · rw [List.length_map]
    exact hl

theorem core123_finite_for_every_x (x : Nat) (hx : 3≤x) :
    ∃ l : List (Fin (4*(x+1)) → Prop), l.Nodup ∧
      (∀ T, T∈l ↔ FinGenerated (x+1) T ∧ FinCore123 (x+1) (by omega) T) ∧
      2*(l.length : Int)=3*(x:Int)*(x:Int)+13*(x:Int)-4 := by
  obtain ⟨l,hn,he,hl⟩ := core123_finite_cardinality (x+1) (by omega)
  refine ⟨l,hn,he,?_⟩
  simp only [Int.natCast_add,Int.natCast_one,Int.mul_add,Int.mul_sub,Int.add_mul,Int.sub_mul,Int.mul_assoc] at hl ⊢
  omega
end LuRazClosure
