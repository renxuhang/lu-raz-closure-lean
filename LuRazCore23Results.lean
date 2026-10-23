import LuRazCore23Enumeration

namespace LuRazClosure
open LuRazEnumeration
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

theorem enum23_lp_count (q : Nat) (hq : 4≤q) :
    2*((enum23Group q 0).length : Int)=(2*(q:Int)-3)*(2*(q:Int)-2) := by
  have h := triangular_pairs_count (fun r s => NF23.lp (rankP q s) (rankP q r)) (2*q-3)
  have hc : ((2*q-3:Nat):Int)=2*(q:Int)-3 := by omega
  rw [hc] at h
  have hc2 : 2*(q:Int)-3+1=2*(q:Int)-2 := by omega
  rw [hc2] at h
  exact h

theorem enum23_filled_count (q : Nat) : ((enum23Group q 1).length : Int)=1 := by rfl
theorem enum23_full_count (q : Nat) : ((enum23Group q 3).length : Int)=1 := by rfl
theorem enum23_exception_count (q : Nat) : ((enum23Group q 5).length : Int)=1 := by rfl

theorem enum23_dgap_count (q : Nat) (hq : 4≤q) :
    ((enum23Group q 2).length : Int)=2*(q:Int)-5 := by
  simp only [enum23Group,enumP,List.length_map,List.length_range]
  omega

theorem enum23_creg_count (q : Nat) (hq : 4≤q) :
    ((enum23Group q 4).length : Int)=2*(q:Int)-4 := by
  have hp : P q (q+3) := by unfold P; omega
  have hm := (enumP_exact q hq (q+3)).mpr hp
  have hl := filter_ne_length (enumP q (2*q-3)) (enumP_nodup q (2*q-3)) (q+3) hm
  have hlen : (enumP q (2*q-3)).length=2*q-3 := by simp [enumP]
  rw [hlen] at hl
  simp only [enum23Group,List.length_map]
  omega

theorem enum23_length (q : Nat) (hq : 4≤q) :
    ((enum23 q).length : Int)=2*(q:Int)*(q:Int)-(q:Int)-3 := by
  have h0 := enum23_lp_count q hq
  have h1 := enum23_filled_count q
  have h2 := enum23_dgap_count q hq
  have h3 := enum23_full_count q
  have h4 := enum23_creg_count q hq
  have h5 := enum23_exception_count q
  have he : enum23 q=enum23Group q 0 ++ enum23Group q 1 ++ enum23Group q 2 ++
      enum23Group q 3 ++ enum23Group q 4 ++ enum23Group q 5 := by
    have hr : List.range 6=[0,1,2,3,4,5] := by decide
    unfold enum23
    rw [hr]
    simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc]
  rw [he]
  simp only [List.length_append,Int.natCast_add]
  have hqq : (q:Int)*(2*(q:Int))=2*((q:Int)*(q:Int)) := Int.mul_left_comm (q:Int) 2 (q:Int)
  simp only [Int.mul_add,Int.mul_sub,Int.add_mul,Int.sub_mul,Int.mul_assoc,hqq] at h0 ⊢
  omega

def core23Members (q : Nat) : List (Nat → Prop) := (enum23 q).map (NF23.eval q)

theorem core23_members_nodup (q : Nat) (hq : 4≤q) : (core23Members q).Nodup := by
  apply nodup_map_on _ _ (enum23_nodup q)
  intro a ha b hb heq
  apply NF23.unique q hq a b ((enum23_exact q hq a).mp ha) ((enum23_exact q hq b).mp hb)
  intro e
  exact Iff.of_eq (congrFun heq e)

theorem core23_members_exact (q : Nat) (hq : 4≤q) (R : Nat → Prop) :
    R∈core23Members q ↔ Generated q R ∧ Core23 R := by
  constructor
  · intro hR
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hR
    have hv := (enum23_exact q hq z).mp hz
    exact (core23_closure_exact q hq (z.eval q)).mpr ⟨z,hv,fun _ => Iff.rfl⟩
  · intro hR
    obtain ⟨z,hz,heq⟩ := (core23_closure_exact q hq R).mp hR
    apply List.mem_map.mpr
    refine ⟨z,(enum23_exact q hq z).mpr hz,?_⟩
    funext e
    exact propext (heq e).symm

theorem core23_cardinality (q : Nat) (hq : 4≤q) :
    ∃ l : List (Nat → Prop), l.Nodup ∧
      (∀ R, R∈l ↔ Generated q R ∧ Core23 R) ∧
      (l.length : Int)=2*(q:Int)*(q:Int)-(q:Int)-3 := by
  refine ⟨core23Members q,core23_members_nodup q hq,core23_members_exact q hq,?_⟩
  simpa only [core23Members,List.length_map] using enum23_length q hq

theorem core23_for_every_x (x : Nat) (hx : 3≤x) :
    ∃ l : List (Nat → Prop), l.Nodup ∧
      (∀ R, R∈l ↔ Generated (x+1) R ∧ Core23 R) ∧
      (l.length : Int)=2*(x:Int)*(x:Int)+3*(x:Int)-2 := by
  obtain ⟨l,hn,heq,hl⟩ := core23_cardinality (x+1) (by omega)
  refine ⟨l,hn,heq,?_⟩
  have hc : ((x+1:Nat):Int)=(x:Int)+1 := by omega
  rw [hc] at hl
  simp only [Int.mul_add,Int.mul_sub,Int.add_mul,Int.sub_mul,Int.mul_assoc] at hl ⊢
  omega

end LuRazClosure
