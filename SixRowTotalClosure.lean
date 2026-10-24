import SixRowDifferenceMembers
import VariantFiniteDifference

namespace LuRazSixRowClosure
open LuRazClosure LuRazEnumeration Difference
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

noncomputable def CommonMembers (q : Nat) : List (Nat → Prop) := by
  classical
  exact (LuRazThreeRow.VariantClosureMembers q).filter (fun R => decide (¬Removed q R))

noncomputable def ClosureMembers (q : Nat) : List (Nat → Prop) :=
  CommonMembers q ++ AddedMembers q

theorem common_members_exact (q : Nat) (hq : 4≤q) (R : Nat → Prop) :
    R∈CommonMembers q ↔ LuRazThreeRow.Generated q R ∧ ¬Removed q R := by
  classical
  simp only [CommonMembers,List.mem_filter,decide_eq_true_eq,
    LuRazThreeRow.variant_closure_members_exact q hq R]

theorem common_members_nodup (q : Nat) (hq : 4≤q) : (CommonMembers q).Nodup := by
  classical
  exact List.Nodup.sublist List.filter_sublist (LuRazThreeRow.variant_closure_members_nodup q hq)

theorem common_removed_partition (q : Nat) (hq : 4≤q) :
    (CommonMembers q ++ RemovedMembers q).Perm (LuRazThreeRow.VariantClosureMembers q) := by
  classical
  have hn : (CommonMembers q ++ RemovedMembers q).Nodup := by
    rw [List.nodup_append]
    refine ⟨common_members_nodup q hq,removed_members_nodup q hq,?_⟩
    intro R hR T hT he
    subst T
    exact ((common_members_exact q hq R).mp hR).2 ((removed_members_exact q hq R).mp hT)
  apply (List.perm_ext_iff_of_nodup hn (LuRazThreeRow.variant_closure_members_nodup q hq)).mpr
  intro R
  rw [List.mem_append,common_members_exact q hq R,removed_members_difference_exact q hq R,
    LuRazThreeRow.variant_closure_members_exact q hq R]
  constructor
  · exact fun h => h.elim And.left And.left
  · intro ho
    by_cases hr : Removed q R
    · exact Or.inr ((removed_exact q hq R).mpr hr)
    · exact Or.inl ⟨ho,hr⟩

theorem closure_members_nodup (q : Nat) (hq : 4≤q) : (ClosureMembers q).Nodup := by
  rw [ClosureMembers,List.nodup_append]
  refine ⟨common_members_nodup q hq,added_members_nodup q hq,?_⟩
  intro R hR T hT he
  subst T
  exact ((added_members_difference_exact q hq R).mp hT).2 ((common_members_exact q hq R).mp hR).1

theorem closure_members_exact (q : Nat) (hq : 4≤q) (R : Nat → Prop) :
    R∈ClosureMembers q ↔ Generated q R := by
  simp only [ClosureMembers,List.mem_append,common_members_exact q hq R,added_members_exact q hq R]
  exact (closure_delta_exact q hq R).symm

theorem closure_members_length (q : Nat) (hq : 4≤q) :
    2*((ClosureMembers q).length : Int)=23*(q:Int)*(q:Int)+7*(q:Int)+2 := by
  have hp := (common_removed_partition q hq).length_eq
  rw [List.length_append] at hp
  have hr := removed_members_length q hq
  have ha := added_members_length q hq
  have ho := LuRazThreeRow.variant_closure_members_length q hq
  simp only [ClosureMembers,List.length_append,Int.natCast_add]
  omega

theorem closure_strict_improvement (q : Nat) (hq : 4≤q) :
    ((LuRazThreeRow.VariantClosureMembers q).length : Int) -
      ((ClosureMembers q).length : Int)=12*(q:Int)-16 := by
  have hp := (common_removed_partition q hq).length_eq
  rw [List.length_append] at hp
  have hr := removed_members_length q hq
  have ha := added_members_length q hq
  simp only [ClosureMembers,List.length_append,Int.natCast_add]
  omega

theorem closure_cardinality (q : Nat) (hq : 4≤q) :
    ∃ l : List (Nat → Prop),l.Nodup ∧
      (∀ R,R∈l ↔ Generated q R) ∧
      2*(l.length : Int)=23*(q:Int)*(q:Int)+7*(q:Int)+2 :=
  ⟨ClosureMembers q,closure_members_nodup q hq,closure_members_exact q hq,
    closure_members_length q hq⟩

end LuRazSixRowClosure
