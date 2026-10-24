import SixRow6Difference
import SixRow7Difference
import SixRowDifferencePredicates
namespace LuRazSixRowClosure
open LuRazClosure Difference
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
theorem removed6_core_iff (f : RemovedForm) : IsRemoved6 f ↔ f.core=6 := by
  cases f <;> simp [IsRemoved6,RemovedForm.core]
theorem added6_core_iff (f : AddedForm) : IsAdded6 f ↔ f.core=6 := by
  cases f <;> simp [IsAdded6,AddedForm.core]
theorem removed7_core_iff (f : RemovedForm) : IsRemoved7 f ↔ f.core=7 := by
  cases f <;> simp [IsRemoved7,RemovedForm.core]
theorem added7_core_iff (f : AddedForm) : IsAdded7 f ↔ f.core=7 := by
  cases f <;> simp [IsAdded7,AddedForm.core]

theorem core6_removed_at (q : Nat) (hq : 4≤q) (R : Nat→Prop) (hc : CoreMask 6 R) :
    (LuRazThreeRow.Generated q R ∧ ¬Generated q R) ↔ RemovedAt q 6 R := by
  have hc6 : Core23 R := by simpa [CoreMask,Core23] using hc
  rw [core6_removed_exact q hq R hc6]
  constructor
  · rintro ⟨f,hf,ht,he⟩
    exact ⟨f,hf,(removed6_core_iff f).mp ht,fun e=>(he e).symm⟩
  · rintro ⟨f,hf,ht,he⟩
    exact ⟨f,hf,(removed6_core_iff f).mpr ht,fun e=>(he e).symm⟩
theorem core6_added_at (q : Nat) (hq : 4≤q) (R : Nat→Prop) (hc : CoreMask 6 R) :
    (Generated q R ∧ ¬LuRazThreeRow.Generated q R) ↔ AddedAt q 6 R := by
  have hc6 : Core23 R := by simpa [CoreMask,Core23] using hc
  rw [core6_added_exact q hq R hc6]
  constructor
  · rintro ⟨f,hf,ht,he⟩
    exact ⟨f,hf,(added6_core_iff f).mp ht,fun e=>(he e).symm⟩
  · rintro ⟨f,hf,ht,he⟩
    exact ⟨f,hf,(added6_core_iff f).mpr ht,fun e=>(he e).symm⟩
theorem core7_removed_at (q : Nat) (hq : 4≤q) (R : Nat→Prop) (hc : CoreMask 7 R) :
    (LuRazThreeRow.Generated q R ∧ ¬Generated q R) ↔ RemovedAt q 7 R := by
  have hc7 : Core123 R := by simpa [CoreMask,Core123] using hc
  rw [core7_removed_exact q hq R hc7]
  constructor
  · rintro ⟨f,hf,ht,he⟩
    exact ⟨f,hf,(removed7_core_iff f).mp ht,fun e=>(he e).symm⟩
  · rintro ⟨f,hf,ht,he⟩
    exact ⟨f,hf,(removed7_core_iff f).mpr ht,fun e=>(he e).symm⟩
theorem core7_added_at (q : Nat) (hq : 4≤q) (R : Nat→Prop) (hc : CoreMask 7 R) :
    (Generated q R ∧ ¬LuRazThreeRow.Generated q R) ↔ AddedAt q 7 R := by
  have hc7 : Core123 R := by simpa [CoreMask,Core123] using hc
  rw [core7_added_exact q hq R hc7]
  constructor
  · rintro ⟨f,hf,ht,he⟩
    exact ⟨f,hf,(added7_core_iff f).mp ht,fun e=>(he e).symm⟩
  · rintro ⟨f,hf,ht,he⟩
    exact ⟨f,hf,(added7_core_iff f).mpr ht,fun e=>(he e).symm⟩
end LuRazSixRowClosure
