import SixRowClosureDefs
import SixRowLargeSources

namespace LuRazSixRowClosure
open LuRazClosure LuRazParametric
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

def NeutralChanged (q i : Nat) : Prop :=
  i=1 ∨ i=4 ∨ i=2*q+2 ∨ i=4*q-1 ∨ i=4*q

theorem neutral_row_unchanged (q i e : Nat) (hn : ¬NeutralChanged q i) :
    LuRazSixRow.BRow q i e ↔ LuRazThreeRow.VRow q i e := by
  rw [LuRazSixRow.unchanged_row q i e (by unfold LuRazSixRow.Special NeutralChanged at *; omega),
    LuRazFourRow.unchanged_row q i e (by unfold LuRazFourRow.Special NeutralChanged at *; omega)]

theorem neutral_changed_new (q i : Nat) (hq : 4≤q) (hc : NeutralChanged q i) :
    LuRazSixRow.BRow q i 2 ∨ LuRazSixRow.BRow q i 3 := by
  rcases hc with rfl|rfl|rfl|rfl|rfl
  · exact Or.inl ((LuRazSixRow.unchanged_row q 1 2 (by unfold LuRazSixRow.Special; omega)).mpr
      ((LuRazFourRow.row_one q 2 hq).mpr (by omega)))
  · exact Or.inl ((e6_source q 2 hq).mpr (by unfold E6 I; omega))
  · exact Or.inl ((LuRazSixRow.row_middle q 2 hq).mpr (by omega))
  · exact Or.inr ((LuRazSixRow.row_last q 3 hq).mpr (by omega))
  · exact Or.inr ((c6_source q 3 hq).mpr (by unfold C6; omega))

theorem neutral_changed_old (q i : Nat) (hq : 4≤q) (hc : NeutralChanged q i) :
    LuRazThreeRow.VRow q i 2 ∨ LuRazThreeRow.VRow q i 3 := by
  rcases hc with rfl|rfl|rfl|rfl|rfl
  · apply Or.inl
    rw [LuRazThreeRow.unchanged_row q 1 2 (by unfold LuRazThreeRow.Special; omega),row_case_1 q 1 2 (by omega) rfl]
    omega
  · exact Or.inl ((LuRazThreeRow.row_four q 2 hq).mpr (by omega))
  · apply Or.inl
    rw [LuRazThreeRow.unchanged_row q (2*q+2) 2 (by unfold LuRazThreeRow.Special; omega),
      row_case_8 q (2*q+2) 2 (by omega) rfl]
    omega
  · exact Or.inr ((LuRazThreeRow.row_last q 3 hq).mpr (by omega))
  · apply Or.inr
    rw [LuRazThreeRow.unchanged_row q (4*q) 3 (by unfold LuRazThreeRow.Special; omega),
      row_case_13 q (4*q) 3 (by omega) rfl]
    omega

theorem neutral_generated_iff (q : Nat) (hq : 4≤q) (R : Nat→Prop)
    (h2 : ¬R 2) (h3 : ¬R 3) : Generated q R ↔ LuRazThreeRow.Generated q R := by
  constructor
  · rintro ⟨l,hn,hv,he⟩
    have hs : ∀i∈l,¬NeutralChanged q i := by
      intro i hi hc
      rcases neutral_changed_new q i hq hc with h|h
      · exact h2 ((he 2).mp ⟨i,hi,h⟩)
      · exact h3 ((he 3).mp ⟨i,hi,h⟩)
    refine ⟨l,hn,hv,?_⟩
    intro e
    constructor
    · rintro ⟨i,hi,hie⟩
      exact (he e).mp ⟨i,hi,(neutral_row_unchanged q i e (hs i hi)).mpr hie⟩
    · intro hre
      obtain ⟨i,hi,hie⟩ := (he e).mpr hre
      exact ⟨i,hi,(neutral_row_unchanged q i e (hs i hi)).mp hie⟩
  · rintro ⟨l,hn,hv,he⟩
    have hs : ∀i∈l,¬NeutralChanged q i := by
      intro i hi hc
      rcases neutral_changed_old q i hq hc with h|h
      · exact h2 ((he 2).mp ⟨i,hi,h⟩)
      · exact h3 ((he 3).mp ⟨i,hi,h⟩)
    refine ⟨l,hn,hv,?_⟩
    intro e
    constructor
    · rintro ⟨i,hi,hie⟩
      exact (he e).mp ⟨i,hi,(neutral_row_unchanged q i e (hs i hi)).mp hie⟩
    · intro hre
      obtain ⟨i,hi,hie⟩ := (he e).mpr hre
      exact ⟨i,hi,(neutral_row_unchanged q i e (hs i hi)).mpr hie⟩

theorem core9_unchanged (q : Nat) (hq : 4≤q) (R : Nat→Prop) (hc : Core14 R) :
    Generated q R ↔ LuRazThreeRow.Generated q R :=
  neutral_generated_iff q hq R hc.2.1 hc.2.2.1

end LuRazSixRowClosure
