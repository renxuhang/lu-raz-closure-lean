import LuRazCore14Count

namespace LuRazClosure
open LuRazEnumeration
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

def core14Members (q : Nat) : List (Nat → Prop) := (enum14 q).map (NF14.eval q)

theorem core14_members_nodup (q : Nat) (hq : 4 ≤ q) : (core14Members q).Nodup := by
  apply nodup_map_on _ _ (enum14_nodup q)
  intro a ha b hb heq
  apply NF14.unique q hq a b ((enum14_exact q hq a).mp ha) ((enum14_exact q hq b).mp hb)
  intro e
  exact Iff.of_eq (congrFun heq e)

theorem core14_members_exact (q : Nat) (hq : 4 ≤ q) (R : Nat → Prop) :
    R ∈ core14Members q ↔ Generated q R ∧ Core14 R := by
  constructor
  · intro hR
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hR
    have hv := (enum14_exact q hq z).mp hz
    exact (core14_closure_exact q hq (z.eval q)).mpr ⟨z,hv,fun _ => Iff.rfl⟩
  · intro hR
    obtain ⟨z,hz,heq⟩ := (core14_closure_exact q hq R).mp hR
    apply List.mem_map.mpr
    refine ⟨z,(enum14_exact q hq z).mpr hz,?_⟩
    funext e
    exact propext (heq e).symm

/-- Exact finite enumeration and cardinality of core {1,4} inside the FULL closure. -/
theorem core14_cardinality (q : Nat) (hq : 4 ≤ q) :
    ∃ l : List (Nat → Prop), l.Nodup ∧
      (∀ R, R ∈ l ↔ Generated q R ∧ Core14 R) ∧
      (l.length : Int)=3*(q:Int)*(q:Int)-5*(q:Int)+2 := by
  refine ⟨core14Members q,core14_members_nodup q hq,core14_members_exact q hq,?_⟩
  simpa only [core14Members,List.length_map] using enum14_length q hq

theorem core14_for_every_x (x : Nat) (hx : 3 ≤ x) :
    ∃ l : List (Nat → Prop), l.Nodup ∧
      (∀ R, R ∈ l ↔ Generated (x+1) R ∧ Core14 R) ∧
      (l.length : Int)=3*(x:Int)*(x:Int)+(x:Int) := by
  obtain ⟨l,hn,heq,hl⟩ := core14_cardinality (x+1) (by omega)
  refine ⟨l,hn,heq,?_⟩
  have hc : ((x+1:Nat):Int)=(x:Int)+1 := by omega
  rw [hc] at hl
  simp only [Int.mul_add,Int.mul_sub,Int.add_mul,Int.sub_mul,Int.mul_assoc] at hl ⊢
  omega

end LuRazClosure
