import SixRowSmallNormal
import SixRowLargeSources

namespace LuRazSixRowClosure.Small
open LuRazClosure LuRazParametric
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

def Fixed (q i : Nat) : Prop := i=4*q+2 ∨ i=4*q+1 ∨ i=4*q ∨ i=2 ∨ i=4*q-1

theorem row_fixed (q i : Nat) (hq : 4≤q) (hi : i≤4*q+2)
    (h2 : ¬LuRazSixRow.BRow q i 2) (h4 : ¬LuRazSixRow.BRow q i 4) : Fixed q i := by
  by_cases h1 : i=1
  · subst i
    exact False.elim (h4 ((LuRazSixRow.unchanged_row q 1 4 (by unfold LuRazSixRow.Special; omega)).mpr
      ((LuRazFourRow.row_one q 4 hq).mpr (by omega))))
  by_cases hz : i=2
  · exact Or.inr (Or.inr (Or.inr (Or.inl hz)))
  by_cases he : i=4
  · subst i; exact False.elim (h2 ((e6_source q 2 hq).mpr (by unfold E6 I; omega)))
  by_cases hm : i=2*q+2
  · subst i; exact False.elim (h4 ((LuRazSixRow.row_middle q 4 hq).mpr (by omega)))
  by_cases hl : i=4*q-1
  · exact Or.inr (Or.inr (Or.inr (Or.inr hl)))
  by_cases hc : i=4*q
  · exact Or.inr (Or.inr (Or.inl hc))
  have ho : OrdinaryLarge q i := ⟨h1,hz,he,hm,hl,hc⟩
  have hh := LuRazClosure.row_fixed_small q i hq hi
    (fun h=>h4 ((large_ordinary q i 4 ho).mpr h))
    (fun h=>h2 ((large_ordinary q i 2 ho).mpr h.1))
  rcases hh with h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact False.elim (hc h)
  · exact False.elim (h1 h)
  · exact False.elim (he h)

theorem sa_source (q e : Nat) (hq : 4≤q) : LuRazSixRow.BRow q (4*q+2) e ↔ SA q e :=
  a0_source q e hq
theorem sb_source (q e : Nat) (hq : 4≤q) : LuRazSixRow.BRow q (4*q+1) e ↔ SB q e :=
  b0_source q e hq
theorem sc_source (q e : Nat) (hq : 4≤q) : LuRazSixRow.BRow q (4*q) e ↔ SC q e :=
  c6_source q e hq
theorem sz_source (q e : Nat) (hq : 4≤q) : LuRazSixRow.BRow q 2 e ↔ SZ q e :=
  z7_source q e hq
theorem sl_source (q e : Nat) (hq : 4≤q) : LuRazSixRow.BRow q (4*q-1) e ↔ SL q e :=
  h7_source q e hq

theorem mix_of_generated (q : Nat) (hq : 4≤q) (R : Nat → Prop)
    (hg : Generated q R) (h2 : ¬R 2) (h4 : ¬R 4) :
    ∃ a b c z l : Prop,(a ∨ b ∨ c ∨ z ∨ l) ∧ ∀e,R e ↔ Mix q a b c z l e := by
  obtain ⟨rows,hne,hvalid,hR⟩ := hg
  have hi : ∀i∈rows,Fixed q i := by
    intro i him
    exact row_fixed q i hq (hvalid i him)
      (fun h=>h2 ((hR 2).mp ⟨i,him,h⟩)) (fun h=>h4 ((hR 4).mp ⟨i,him,h⟩))
  refine ⟨4*q+2∈rows,4*q+1∈rows,4*q∈rows,2∈rows,4*q-1∈rows,?_,?_⟩
  · obtain ⟨i,him⟩ := list_nonempty_witness rows hne
    rcases hi i him with h|h|h|h|h <;> subst i
    · exact Or.inl him
    · exact Or.inr (Or.inl him)
    · exact Or.inr (Or.inr (Or.inl him))
    · exact Or.inr (Or.inr (Or.inr (Or.inl him)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr him)))
  · intro e
    constructor
    · intro he
      obtain ⟨i,him,hie⟩ := (hR e).mpr he
      rcases hi i him with h|h|h|h|h <;> subst i
      · exact Or.inl ⟨him,(sa_source q e hq).mp hie⟩
      · exact Or.inr (Or.inl ⟨him,(sb_source q e hq).mp hie⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨him,(sc_source q e hq).mp hie⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨him,(sz_source q e hq).mp hie⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨him,(sl_source q e hq).mp hie⟩)))
    · intro he
      apply (hR e).mp
      rcases he with h|h|h|h|h
      · exact ⟨4*q+2,h.1,(sa_source q e hq).mpr h.2⟩
      · exact ⟨4*q+1,h.1,(sb_source q e hq).mpr h.2⟩
      · exact ⟨4*q,h.1,(sc_source q e hq).mpr h.2⟩
      · exact ⟨2,h.1,(sz_source q e hq).mpr h.2⟩
      · exact ⟨4*q-1,h.1,(sl_source q e hq).mpr h.2⟩

theorem normal_of_generated (q : Nat) (hq : 4≤q) (R : Nat → Prop)
    (hg : Generated q R) (h2 : ¬R 2) (h4 : ¬R 4) :
    ∃x : Normal,∀e,R e ↔ x.eval q e := by
  obtain ⟨a,b,c,z,l,hne,he⟩ := mix_of_generated q hq R hg h2 h4
  obtain ⟨x,hx⟩ := mix_normal q hq a b c z l hne
  exact ⟨x,fun e=>(he e).trans (hx e)⟩

end LuRazSixRowClosure.Small
