import ThreeRowWeightTools

namespace LuRazThreeRow
open LuRazClosure LuRazEnumeration LuRazLattice
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
noncomputable section

/-- The actual cardinality of a predicate on a finite type, by filtering all elements. -/
def finiteMemberSize {n : Nat} (T : Fin n → Prop) : Int := by
  classical
  exact (((List.finRange n).filter (fun e => decide (T e))).length : Int)

/-- The sum of the actual finite cardinalities of the family members. -/
def finiteFamilyWeight {n : Nat} (l : List (Fin n → Prop)) : Int :=
  (l.map finiteMemberSize).sum

theorem fin_ground_coordinate_perm (n : Nat) :
    ((List.finRange n).map (fun e => e.val+1)).Perm (List.range' 1 n) := by
  have hn : ((List.finRange n).map (fun e => e.val+1)).Nodup := by
    apply nodup_map_on _ _ (List.nodup_finRange n)
    intro a _ b _ hab
    apply Fin.ext
    omega
  apply (List.perm_ext_iff_of_nodup hn List.nodup_range').mpr
  intro e
  rw [List.mem_map,range_mem]
  constructor
  · rintro ⟨a,ha,he⟩
    have ht := a.isLt
    omega
  · intro he
    refine ⟨⟨e-1,by omega⟩,List.mem_finRange _,?_⟩
    change e-1+1=e
    omega

theorem family_member_size_finite (q : Nat) (R : Nat → Prop) :
    familyMemberSize q R=finiteMemberSize (Restrict q R) := by
  unfold familyMemberSize
  rw [←tally_perm (fin_ground_coordinate_perm (4*q)) R,tally_map]
  rfl

theorem family_total_weight_finite (q : Nat) (l : List (Nat → Prop)) :
    familyTotalWeight q l=finiteFamilyWeight (l.map (Restrict q)) := by
  unfold familyTotalWeight finiteFamilyWeight
  rw [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro R _
  exact family_member_size_finite q R

/-- Each member size counts a duplicate-free exhaustive list of its finite elements. -/
theorem finite_member_size_exact {n : Nat} (T : Fin n → Prop) :
    ∃ l : List (Fin n), l.Nodup ∧ (∀ e,e∈l ↔ T e) ∧
      (l.length : Int)=finiteMemberSize T := by
  classical
  refine ⟨(List.finRange n).filter (fun e => decide (T e)),
    List.Nodup.sublist List.filter_sublist (List.nodup_finRange n),?_,rfl⟩
  intro e
  simp only [List.mem_filter,decide_eq_true_eq,List.mem_finRange,true_and]

#print axioms fin_ground_coordinate_perm
#print axioms family_member_size_finite
#print axioms family_total_weight_finite
#print axioms finite_member_size_exact
end
end LuRazThreeRow
