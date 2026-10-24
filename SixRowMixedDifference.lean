import SixRowCore11Difference
import SixRowCore13Difference
import SixRowCore14Difference

namespace LuRazSixRowClosure
open LuRazClosure Difference
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

theorem core11_removed_at (q : Nat) (hq : 4≤q) (R : Nat→Prop) (hc : CoreMask 11 R) :
    (LuRazThreeRow.Generated q R ∧ ¬Generated q R) ↔ RemovedAt q 11 R := by
  rw [core11_removed_exact q hq R ((core_mask_11 R).mp hc)]
  constructor
  · rintro ⟨f,hf,hp,he⟩
    refine ⟨f,hf,?_,fun e => (he e).symm⟩
    cases f <;> simp_all [IsRemoved11,RemovedForm.core]
  · rintro ⟨f,hf,hk,he⟩
    refine ⟨f,hf,?_,fun e => (he e).symm⟩
    cases f <;> simp_all [IsRemoved11,RemovedForm.core]

theorem core11_added_at (q : Nat) (hq : 4≤q) (R : Nat→Prop) (hc : CoreMask 11 R) :
    (Generated q R ∧ ¬LuRazThreeRow.Generated q R) ↔ AddedAt q 11 R := by
  rw [core11_added_exact q hq R ((core_mask_11 R).mp hc)]
  constructor
  · rintro ⟨f,hf,hp,he⟩
    refine ⟨f,hf,?_,fun e => (he e).symm⟩
    cases f <;> simp_all [IsAdded11,AddedForm.core]
  · rintro ⟨f,hf,hk,he⟩
    refine ⟨f,hf,?_,fun e => (he e).symm⟩
    cases f <;> simp_all [IsAdded11,AddedForm.core]

theorem core13_removed_at (q : Nat) (hq : 4≤q) (R : Nat→Prop) (hc : CoreMask 13 R) :
    (LuRazThreeRow.Generated q R ∧ ¬Generated q R) ↔ RemovedAt q 13 R := by
  rw [core13_removed_exact q hq R ((core_mask_13 R).mp hc)]
  constructor
  · rintro ⟨f,hf,hp,he⟩
    refine ⟨f,hf,?_,fun e => (he e).symm⟩
    cases f <;> simp_all [IsRemoved13,RemovedForm.core]
  · rintro ⟨f,hf,hk,he⟩
    refine ⟨f,hf,?_,fun e => (he e).symm⟩
    cases f <;> simp_all [IsRemoved13,RemovedForm.core]

theorem core13_added_at (q : Nat) (hq : 4≤q) (R : Nat→Prop) (hc : CoreMask 13 R) :
    (Generated q R ∧ ¬LuRazThreeRow.Generated q R) ↔ AddedAt q 13 R := by
  rw [core13_added_exact q hq R ((core_mask_13 R).mp hc)]
  constructor
  · rintro ⟨f,hf,hp,he⟩
    refine ⟨f,hf,?_,fun e => (he e).symm⟩
    cases f <;> simp_all [IsAdded13,AddedForm.core]
  · rintro ⟨f,hf,hk,he⟩
    refine ⟨f,hf,?_,fun e => (he e).symm⟩
    cases f <;> simp_all [IsAdded13,AddedForm.core]

theorem core14_removed_at (q : Nat) (hq : 4≤q) (R : Nat→Prop) (hc : CoreMask 14 R) :
    (LuRazThreeRow.Generated q R ∧ ¬Generated q R) ↔ RemovedAt q 14 R := by
  rw [core14_removed_exact q hq R ((core_mask_14 R).mp hc)]
  constructor
  · rintro ⟨f,hf,hp,he⟩
    refine ⟨f,hf,?_,fun e => (he e).symm⟩
    cases f <;> simp_all [IsRemoved14,RemovedForm.core]
  · rintro ⟨f,hf,hk,he⟩
    refine ⟨f,hf,?_,fun e => (he e).symm⟩
    cases f <;> simp_all [IsRemoved14,RemovedForm.core]

theorem core14_added_at (q : Nat) (hq : 4≤q) (R : Nat→Prop) (hc : CoreMask 14 R) :
    (Generated q R ∧ ¬LuRazThreeRow.Generated q R) ↔ AddedAt q 14 R := by
  constructor
  · intro h
    exact False.elim (core14_no_added q hq R ((core_mask_14 R).mp hc) h)
  · rintro ⟨f,hf,hk,he⟩
    cases f <;> simp [AddedForm.core] at hk

end LuRazSixRowClosure
