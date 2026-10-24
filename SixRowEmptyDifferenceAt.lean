import SixRowEmptyDifference
namespace LuRazSixRowClosure
open Difference
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
theorem thin_added_at (q k : Nat) (hq : 4≤q) (R : Nat→Prop)
    (hk : k=2 ∨ k=3 ∨ k=8 ∨ k=12) (hc : CoreMask k R) :
    (Generated q R ∧ ¬LuRazThreeRow.Generated q R) ↔ AddedAt q k R := by
  constructor
  · intro h; exact False.elim (new_thin_empty q k hq R hk hc h.1)
  · intro h; exact False.elim (thin_no_added q k R hk h)

theorem core2_removed_at (q : Nat) (hq : 4≤q) (R : Nat→Prop) (hc : CoreMask 2 R) :
    (LuRazThreeRow.Generated q R ∧ ¬Generated q R) ↔ RemovedAt q 2 R := by
  have he := (old2_normal q hq R hc).trans (removed_at2_normal q R).symm
  constructor
  · exact fun h=>he.mp h.1
  · exact fun h=>⟨he.mpr h,new_thin_empty q 2 hq R (Or.inl rfl) hc⟩
theorem core2_added_at (q : Nat) (hq : 4≤q) (R : Nat→Prop) (hc : CoreMask 2 R) :
    (Generated q R ∧ ¬LuRazThreeRow.Generated q R) ↔ AddedAt q 2 R :=
  thin_added_at q 2 hq R (Or.inl rfl) hc

theorem core3_removed_at (q : Nat) (hq : 4≤q) (R : Nat→Prop) (hc : CoreMask 3 R) :
    (LuRazThreeRow.Generated q R ∧ ¬Generated q R) ↔ RemovedAt q 3 R := by
  have he := (old3_normal q hq R hc).trans (removed_at3_normal q R).symm
  constructor
  · exact fun h=>he.mp h.1
  · exact fun h=>⟨he.mpr h,new_thin_empty q 3 hq R (Or.inr (Or.inl rfl)) hc⟩
theorem core3_added_at (q : Nat) (hq : 4≤q) (R : Nat→Prop) (hc : CoreMask 3 R) :
    (Generated q R ∧ ¬LuRazThreeRow.Generated q R) ↔ AddedAt q 3 R :=
  thin_added_at q 3 hq R (Or.inr (Or.inl rfl)) hc

theorem core8_removed_at (q : Nat) (hq : 4≤q) (R : Nat→Prop) (hc : CoreMask 8 R) :
    (LuRazThreeRow.Generated q R ∧ ¬Generated q R) ↔ RemovedAt q 8 R := by
  constructor
  · exact fun h=>False.elim (old8_empty q hq R hc h.1)
  · exact fun h=>False.elim (core8_no_removed q R h)
theorem core8_added_at (q : Nat) (hq : 4≤q) (R : Nat→Prop) (hc : CoreMask 8 R) :
    (Generated q R ∧ ¬LuRazThreeRow.Generated q R) ↔ AddedAt q 8 R :=
  thin_added_at q 8 hq R (Or.inr (Or.inr (Or.inl rfl))) hc

theorem core12_removed_at (q : Nat) (hq : 4≤q) (R : Nat→Prop) (hc : CoreMask 12 R) :
    (LuRazThreeRow.Generated q R ∧ ¬Generated q R) ↔ RemovedAt q 12 R := by
  constructor
  · exact fun h=>(old12_removed q hq R hc).mp h.1
  · exact fun h=>⟨(old12_removed q hq R hc).mpr h,new_thin_empty q 12 hq R (Or.inr (Or.inr (Or.inr rfl))) hc⟩
theorem core12_added_at (q : Nat) (hq : 4≤q) (R : Nat→Prop) (hc : CoreMask 12 R) :
    (Generated q R ∧ ¬LuRazThreeRow.Generated q R) ↔ AddedAt q 12 R :=
  thin_added_at q 12 hq R (Or.inr (Or.inr (Or.inr rfl))) hc
end LuRazSixRowClosure
