import SixRowFiniteClosure
import ThreeRowCompleteSpectrum

namespace LuRazSixRowSpectrum
open LuRazClosure LuRazEnumeration LuRazThreeRow LuRazSixRowClosure
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

/-- Frequency in the duplicate-free enumeration of the actual B closure. -/
noncomputable def sixRowFrequency (q e : Nat) : Int :=
  CountAt (LuRazSixRowClosure.ClosureMembers q) e

noncomputable def removedFrequency (q e : Nat) : Int :=
  CountAt (RemovedMembers q) e

noncomputable def addedFrequency (q e : Nat) : Int :=
  CountAt (AddedMembers q) e

/-- Set-theoretic closure replacement induces the pointwise incidence identity. -/
theorem six_row_frequency_delta (q e : Nat) (hq : 4≤q) :
    sixRowFrequency q e = variantFrequency q e - removedFrequency q e + addedFrequency q e := by
  have hp := count_at_perm _ _ (common_removed_partition q hq) e
  rw [count_at_append] at hp
  simp only [sixRowFrequency,variantFrequency,removedFrequency,addedFrequency,
    LuRazSixRowClosure.ClosureMembers,count_at_append]
  omega

/-- The count is independent of the chosen exhaustive, duplicate-free enumeration. -/
theorem six_row_frequency_enumeration (q e : Nat) (hq : 4≤q)
    (l : List (Nat → Prop)) (hn : l.Nodup)
    (he : ∀R,R∈l ↔ LuRazSixRowClosure.Generated q R) :
    CountAt l e=sixRowFrequency q e := by
  have hp : l.Perm (LuRazSixRowClosure.ClosureMembers q) := by
    apply (List.perm_ext_iff_of_nodup hn (LuRazSixRowClosure.closure_members_nodup q hq)).mpr
    intro R
    rw [he R,LuRazSixRowClosure.closure_members_exact q hq R]
  exact count_at_perm _ _ hp e

theorem six_row_frequency_nonnegative (q e : Nat) : 0≤sixRowFrequency q e := by
  unfold sixRowFrequency CountAt
  omega

theorem six_row_frequency_outside (q e : Nat) (hq : 4≤q)
    (he : e=0 ∨ 4*q<e) : sixRowFrequency q e=0 := by
  apply count_at_absent
  intro R hR hRe
  have hg := (LuRazSixRowClosure.closure_members_exact q hq R).mp hR
  have hs := LuRazSixRowClosure.generated_supported q hq R hg e hRe
  omega

/-- The same count on the actual finite source B, with its original coordinates. -/
noncomputable def sixRowFinFrequency (q : Nat) (e : Fin (4*q)) : Int :=
  VariantFinCountAt q (FinClosureMembers q) e

theorem six_row_fin_frequency_eq (q : Nat) (e : Fin (4*q)) :
    sixRowFinFrequency q e=sixRowFrequency q (e.val+1) := by
  classical
  simp only [sixRowFinFrequency,VariantFinCountAt,FinClosureMembers,sixRowFrequency,
    CountAt,List.filter_map,List.length_map,Function.comp_def,Restrict]
  rfl

theorem six_row_fin_frequency_delta (q : Nat) (e : Fin (4*q)) (hq : 4≤q) :
    sixRowFinFrequency q e=variantFrequency q (e.val+1) -
      removedFrequency q (e.val+1) + addedFrequency q (e.val+1) := by
  rw [six_row_fin_frequency_eq]
  exact six_row_frequency_delta q (e.val+1) hq

/-- A genuine list of precisely the finite B-closure sets containing e. -/
theorem six_row_frequency_finite_exact (q : Nat) (e : Fin (4*q)) (hq : 4≤q) :
    ∃l : List (Fin (4*q) → Prop),l.Nodup ∧
      (∀T,T∈l ↔ LuRazSixRowClosure.FinGenerated q T ∧ T e) ∧
      (l.length : Int)=sixRowFrequency q (e.val+1) := by
  classical
  let l := (FinClosureMembers q).filter (fun T => decide (T e))
  refine ⟨l,List.Nodup.sublist List.filter_sublist (LuRazSixRowClosure.fin_closure_members_nodup q hq),?_,?_⟩
  · intro T
    simp only [l,List.mem_filter,decide_eq_true_eq,LuRazSixRowClosure.fin_closure_members_exact q hq T]
  · change sixRowFinFrequency q e=sixRowFrequency q (e.val+1)
    exact six_row_fin_frequency_eq q e

end LuRazSixRowSpectrum

