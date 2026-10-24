import VariantGlobalDifference

namespace LuRazThreeRow
open LuRazClosure LuRazEnumeration
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

theorem variant_closure_members_length (q : Nat) (hq : 4≤q) :
    2*((VariantClosureMembers q).length : Int)=23*(q:Int)*(q:Int)+31*(q:Int)-30 := by
  obtain ⟨l,hn,he,hl⟩ := closure_new_cardinality q hq
  have hp : (VariantClosureMembers q).Perm l := by
    apply (List.perm_ext_iff_of_nodup (variant_closure_members_nodup q hq) hn).mpr
    intro R
    rw [variant_closure_members_exact q hq R,he R]
  rw [hp.length_eq]
  exact hl

noncomputable def VariantFinClosureMembers (q : Nat) : List (Fin (4*q) → Prop) :=
  (VariantClosureMembers q).map (Restrict q)

noncomputable def VariantFinCountAt (q : Nat) (l : List (Fin (4*q) → Prop))
    (e : Fin (4*q)) : Int := by
  classical
  exact ((l.filter (fun R => decide (R e))).length : Int)

theorem variant_fin_closure_members_nodup (q : Nat) (hq : 4≤q) :
    (VariantFinClosureMembers q).Nodup := by
  apply (transfer_enumeration q hq (fun _ => True) (VariantClosureMembers q)
    (variant_closure_members_nodup q hq) ?_).1
  intro R
  simp only [variant_closure_members_exact q hq R,and_true]

theorem variant_fin_closure_members_exact (q : Nat) (hq : 4≤q) (T : Fin (4*q) → Prop) :
    T∈VariantFinClosureMembers q ↔ FinGenerated q T := by
  have h := transfer_enumeration q hq (fun _ => True) (VariantClosureMembers q)
    (variant_closure_members_nodup q hq) (by
      intro R
      simp only [variant_closure_members_exact q hq R,and_true])
  simpa only [VariantFinClosureMembers,and_true] using h.2.1 T

theorem variant_fin_closure_members_length (q : Nat) (hq : 4≤q) :
    2*((VariantFinClosureMembers q).length : Int)=23*(q:Int)*(q:Int)+31*(q:Int)-30 := by
  simpa only [VariantFinClosureMembers,List.length_map] using variant_closure_members_length q hq

theorem variant_fin_count_delta (q : Nat) (e : Fin (4*q)) (hq : 4≤q) :
    VariantFinCountAt q (VariantFinClosureMembers q) e =
      SourcePieces.elementFrequency q (e.val+1) + DeltaRaw q (e.val+1) := by
  have h := variant_closure_count_delta q (e.val+1) hq
  classical
  have hm : VariantFinCountAt q (VariantFinClosureMembers q) e =
      CountAt (VariantClosureMembers q) (e.val+1) := by
    simp only [VariantFinCountAt,VariantFinClosureMembers,CountAt,List.filter_map,List.length_map,Function.comp_def,Restrict]
    rfl
  exact hm.trans h

end LuRazThreeRow
