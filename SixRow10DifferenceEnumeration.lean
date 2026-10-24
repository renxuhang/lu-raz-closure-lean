import SixRow10Difference
namespace LuRazSixRowClosure
open LuRazClosure LuRazEnumeration
def all10 : List Low.NF10 := [.k1,.k2,.joinK,.fill1,.fill2,.dSmall,.dBig]
def members10 (q : Nat) : List (Nat→Prop) := all10.map (Low.NF10.eval q)
theorem all10_nodup : all10.Nodup := by decide
theorem all10_mem (z : Low.NF10) : z∈all10 := by cases z <;> simp [all10]
theorem members10_nodup (q : Nat) (hq : 4≤q) : (members10 q).Nodup := by
  apply nodup_map_on _ _ all10_nodup
  intro z _ w _ he
  exact Low.NF10.unique q hq z w (fun e=>iff_of_eq (congrFun he e))
theorem members10_exact (q : Nat) (hq : 4≤q) (R : Nat→Prop) :
    R∈members10 q ↔ Generated q R ∧ Core24 R := by
  rw [Low.core10_exhaustive q hq R]
  constructor
  · intro h
    obtain ⟨z,_,rfl⟩ := List.mem_map.mp h
    exact ⟨z,fun _=>Iff.rfl⟩
  · rintro ⟨z,he⟩
    exact List.mem_map.mpr ⟨z,all10_mem z,funext (fun e=>propext (he e).symm)⟩
theorem core10_cardinality (q : Nat) (hq : 4≤q) :
    ∃l : List (Nat→Prop),l.Nodup ∧ (∀R,R∈l ↔ Generated q R ∧ Core24 R) ∧ l.length=7 :=
  ⟨members10 q,members10_nodup q hq,members10_exact q hq,rfl⟩
end LuRazSixRowClosure
