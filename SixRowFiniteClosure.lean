import SixRowTotalClosure
import SixRowFiniteBridge

namespace LuRazSixRowClosure
open LuRazClosure
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

noncomputable def FinClosureMembers (q : Nat) : List (Fin (4*q) → Prop) :=
  (ClosureMembers q).map (Restrict q)

theorem fin_closure_members_nodup (q : Nat) (hq : 4≤q) : (FinClosureMembers q).Nodup := by
  apply (transfer_enumeration q hq (fun _ => True) (ClosureMembers q)
    (closure_members_nodup q hq) ?_).1
  intro R
  simp only [closure_members_exact q hq R,and_true]

theorem fin_closure_members_exact (q : Nat) (hq : 4≤q) (T : Fin (4*q) → Prop) :
    T∈FinClosureMembers q ↔ FinGenerated q T := by
  have h := transfer_enumeration q hq (fun _ => True) (ClosureMembers q)
    (closure_members_nodup q hq) (by
      intro R
      simp only [closure_members_exact q hq R,and_true])
  simpa only [FinClosureMembers,and_true] using h.2.1 T

theorem fin_closure_members_length (q : Nat) (hq : 4≤q) :
    2*((FinClosureMembers q).length : Int)=23*(q:Int)*(q:Int)+7*(q:Int)+2 := by
  simpa only [FinClosureMembers,List.length_map] using closure_members_length q hq

theorem finite_closure_cardinality (q : Nat) (hq : 4≤q) :
    ∃ l : List (Fin (4*q) → Prop),l.Nodup ∧
      (∀ T,T∈l ↔ FinGenerated q T) ∧
      2*(l.length : Int)=23*(q:Int)*(q:Int)+7*(q:Int)+2 :=
  ⟨FinClosureMembers q,fin_closure_members_nodup q hq,fin_closure_members_exact q hq,
    fin_closure_members_length q hq⟩

theorem finite_closure_strict_improvement (q : Nat) (hq : 4≤q) :
    ((LuRazThreeRow.VariantFinClosureMembers q).length : Int) -
      ((FinClosureMembers q).length : Int)=12*(q:Int)-16 := by
  simpa only [LuRazThreeRow.VariantFinClosureMembers,FinClosureMembers,List.length_map]
    using closure_strict_improvement q hq

theorem finite_closure_q4 : (FinClosureMembers 4).length=199 := by
  have h := fin_closure_members_length 4 (by omega)
  omega

end LuRazSixRowClosure
