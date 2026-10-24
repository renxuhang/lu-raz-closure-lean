import SixRowFrequencyBridge
import ThreeRowFiniteWeight

namespace LuRazSixRowSpectrum
open LuRazClosure LuRazEnumeration LuRazThreeRow LuRazSixRowClosure
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

noncomputable def sixRowTotalWeight (q : Nat) : Int :=
  familyTotalWeight q (LuRazSixRowClosure.ClosureMembers q)

noncomputable def removedTotalWeight (q : Nat) : Int :=
  familyTotalWeight q (RemovedMembers q)

noncomputable def addedTotalWeight (q : Nat) : Int :=
  familyTotalWeight q (AddedMembers q)

theorem family_weight_append (q : Nat) (a b : List (Nat → Prop)) :
    familyTotalWeight q (a++b)=familyTotalWeight q a+familyTotalWeight q b := by
  simp only [familyTotalWeight,List.map_append,List.sum_append]

theorem family_weight_perm (q : Nat) (a b : List (Nat → Prop)) (hp : a.Perm b) :
    familyTotalWeight q a=familyTotalWeight q b := by
  rw [family_weight_double_count,family_weight_double_count]
  apply congrArg List.sum
  apply List.map_congr_left
  intro e _
  exact count_at_perm a b hp e

/-- Total cardinality cancels on the same actual common/removed partition. -/
theorem six_row_total_weight_delta (q : Nat) (hq : 4≤q) :
    sixRowTotalWeight q=variantTotalWeight q-removedTotalWeight q+addedTotalWeight q := by
  have hp := family_weight_perm q _ _ (common_removed_partition q hq)
  rw [family_weight_append] at hp
  simp only [sixRowTotalWeight,variantTotalWeight,removedTotalWeight,addedTotalWeight,
    LuRazSixRowClosure.ClosureMembers,family_weight_append]
  omega

/-- Double counts actual incidences; no standard-form weight model is substituted. -/
theorem six_row_total_weight_as_frequency_sum (q : Nat) :
    sixRowTotalWeight q=((List.range' 1 (4*q)).map (sixRowFrequency q)).sum := by
  exact family_weight_double_count q (LuRazSixRowClosure.ClosureMembers q)

theorem removed_total_weight_as_frequency_sum (q : Nat) :
    removedTotalWeight q=((List.range' 1 (4*q)).map (removedFrequency q)).sum := by
  exact family_weight_double_count q (RemovedMembers q)

theorem added_total_weight_as_frequency_sum (q : Nat) :
    addedTotalWeight q=((List.range' 1 (4*q)).map (addedFrequency q)).sum := by
  exact family_weight_double_count q (AddedMembers q)

noncomputable def sixRowFiniteTotalWeight (q : Nat) : Int :=
  finiteFamilyWeight (FinClosureMembers q)

theorem six_row_finite_total_weight_eq (q : Nat) :
    sixRowFiniteTotalWeight q=sixRowTotalWeight q := by
  exact (family_total_weight_finite q (LuRazSixRowClosure.ClosureMembers q)).symm

/-- The weight identity on predicates of the original finite ground set. -/
theorem six_row_finite_total_weight_delta (q : Nat) (hq : 4≤q) :
    finiteFamilyWeight (FinClosureMembers q)=
      finiteFamilyWeight (VariantFinClosureMembers q)-
        finiteFamilyWeight ((RemovedMembers q).map (Restrict q))+
        finiteFamilyWeight ((AddedMembers q).map (Restrict q)) := by
  have h := six_row_total_weight_delta q hq
  simp only [sixRowTotalWeight,variantTotalWeight,removedTotalWeight,addedTotalWeight,
    family_total_weight_finite] at h
  exact h

end LuRazSixRowSpectrum
