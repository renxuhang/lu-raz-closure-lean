import SixRowLargeSources
namespace LuRazSixRowClosure.Low
open LuRazClosure LuRazParametric
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

def K0 (q e : Nat) : Prop := e=2 ∨ e=4 ∨ I (2*q+1) (4*q-2) e ∨ e=4*q
def K1 (q e : Nat) : Prop := e=2 ∨ e=4 ∨ I (2*q+2) (4*q-2) e
def K2 (q e : Nat) : Prop := e=2 ∨ e=4 ∨ I (2*q+3) (4*q-2) e ∨ e=4*q
def Fixed24 (q i : Nat) : Prop := i=2*q+1 ∨ i=2*q+2 ∨ i=1 ∨ i=4*q+1
def Mix24 (q : Nat) (u v d b : Prop) (e : Nat) : Prop :=
  (u ∧ K1 q e) ∨ (v ∧ K2 q e) ∨ (d ∧ K0 q e) ∨ (b ∧ BRow q e)


theorem k0_source (q e : Nat) (hq : 4≤q) : LuRazSixRow.BRow q 1 e ↔ K0 q e := by
  rw [LuRazSixRow.unchanged_row q 1 e (by unfold LuRazSixRow.Special; omega),LuRazFourRow.row_one q e hq]
  rfl

theorem k1_source (q e : Nat) (hq : 4≤q) : LuRazSixRow.BRow q (2*q+1) e ↔ K1 q e := by
  rw [large_ordinary q (2*q+1) e (by unfold OrdinaryLarge; omega),LuRazClosure.K1_source q e hq]
  rfl

theorem k2_source (q e : Nat) (hq : 4≤q) : LuRazSixRow.BRow q (2*q+2) e ↔ K2 q e := by
  rw [LuRazSixRow.row_middle q e hq]
  rfl

theorem row_fixed24 (q i : Nat) (hq : 4≤q) (hi : i≤4*q+2)
    (h1 : ¬LuRazSixRow.BRow q i 1) (h3 : ¬LuRazSixRow.BRow q i 3) : Fixed24 q i := by
  by_cases hd : i=1
  · exact Or.inr (Or.inr (Or.inl hd))
  by_cases hz : i=2
  · subst i; exact False.elim (h3 ((z7_source q 3 hq).mpr (by unfold Z7; omega)))
  by_cases he : i=4
  · subst i; exact False.elim (h3 ((e6_source q 3 hq).mpr (by unfold E6; omega)))
  by_cases hm : i=2*q+2
  · exact Or.inr (Or.inl hm)
  by_cases hl : i=4*q-1
  · subst i; exact False.elim (h3 ((h7_source q 3 hq).mpr (by unfold H7; omega)))
  by_cases hc : i=4*q
  · subst i; exact False.elim (h3 ((c6_source q 3 hq).mpr (by unfold C6; omega)))
  have ho : OrdinaryLarge q i := ⟨hd,hz,he,hm,hl,hc⟩
  exact LuRazClosure.row_fixed24 q i hq hi
    (fun h=>h1 ((large_ordinary q i 1 ho).mpr h))
    (fun h=>h3 ((large_ordinary q i 3 ho).mpr h))

theorem core24_mix (q : Nat) (hq : 4≤q) (R : Nat → Prop) (hg : Generated q R) (hc : Core24 R) :
    ∃ u v d b : Prop, (u ∨ v ∨ d) ∧ ∀ e, R e ↔ Mix24 q u v d b e := by
  obtain ⟨l,_,hvalid,hR⟩ := hg
  have hi : ∀ i∈l, Fixed24 q i := by
    intro i him
    apply row_fixed24 q i hq (hvalid i him)
    · intro h; exact hc.1 ((hR 1).mp ⟨i,him,h⟩)
    · intro h; exact hc.2.2.1 ((hR 3).mp ⟨i,him,h⟩)
  have hm : ∀ e, R e ↔ Mix24 q (2*q+1∈l) (2*q+2∈l) (1∈l) (4*q+1∈l) e := by
    intro e
    constructor
    · intro he
      obtain ⟨i,him,hie⟩ := (hR e).mpr he
      rcases hi i him with h | h | h | h <;> subst i
      · exact Or.inl ⟨him,(k1_source q e hq).mp hie⟩
      · exact Or.inr (Or.inl ⟨him,(k2_source q e hq).mp hie⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨him,(k0_source q e hq).mp hie⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨him,(b0_source q e hq).mp hie⟩))
    · intro he
      apply (hR e).mp
      rcases he with h | h | h | h
      · exact ⟨2*q+1,h.1,(k1_source q e hq).mpr h.2⟩
      · exact ⟨2*q+2,h.1,(k2_source q e hq).mpr h.2⟩
      · exact ⟨1,h.1,(k0_source q e hq).mpr h.2⟩
      · exact ⟨4*q+1,h.1,(b0_source q e hq).mpr h.2⟩
  refine ⟨2*q+1∈l,2*q+2∈l,1∈l,4*q+1∈l,?_,hm⟩
  have h4 := (hm 4).mp hc.2.2.2
  rcases h4 with h | h | h | h
  · exact Or.inl h.1
  · exact Or.inr (Or.inl h.1)
  · exact Or.inr (Or.inr h.1)
  · have hh := h.2; unfold BRow I at hh; omega


end LuRazSixRowClosure.Low
