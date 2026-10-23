import LuRazCore23

namespace LuRazClosure
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

def ERow (q e : Nat) : Prop := e=1 ∨ e=3 ∨ I (2*q+3) (4*q) e
def SmallCore (R : Nat → Prop) : Prop := ¬R 4 ∧ ¬(R 2 ∧ R 3)
def FixedSmall (q i : Nat) : Prop := i=4*q+2 ∨ i=4*q+1 ∨ i=4*q ∨ i=1 ∨ i=4
def SmallMix (q : Nat) (a b c d f : Prop) (e : Nat) : Prop :=
  (a ∧ ARow q e) ∨ (b ∧ BRow q e) ∨ (c ∧ CRow q e) ∨ (d ∧ DRow q e) ∨ (f ∧ ERow q e)

theorem E_source (q e : Nat) (hq : 4≤q) : LuRazParametric.Row q 4 e ↔ ERow q e := by
  rw [LuRazParametric.row_case_4 q 4 e (by omega) rfl]
  rfl

theorem generated_E (q : Nat) (hq : 4≤q) : Generated q (ERow q) :=
  generated_congr q (generated_row q 4 (by omega)) (fun e => E_source q e hq)

theorem row_fixed_small (q i : Nat) (hq : 4≤q) (hi : i≤4*q+2)
    (h4 : ¬LuRazParametric.Row q i 4)
    (h23 : ¬(LuRazParametric.Row q i 2 ∧ LuRazParametric.Row q i 3)) : FixedSmall q i := by
  have hc : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨
      (5≤i ∧ i≤q+2) ∨ (q+3≤i ∧ i≤2*q) ∨ i=2*q+1 ∨ i=2*q+2 ∨ i=2*q+3 ∨
      (2*q+4≤i ∧ i≤3*q) ∨ i=3*q+1 ∨ (3*q+2≤i ∧ i+1≤4*q) ∨
      i=4*q ∨ i=4*q+1 ∨ i=4*q+2 := by omega
  rcases hc with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact False.elim (h4 ((LuRazParametric.row_case_0 q i 4 (by omega) h).mpr (by omega)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact False.elim (h4 ((LuRazParametric.row_case_2 q i 4 (by omega) h).mpr (by omega)))
  · exact False.elim (h4 ((LuRazParametric.row_case_3 q i 4 (by omega) h).mpr (by omega)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  · exact False.elim (h4 ((LuRazParametric.row_case_5 q i 4 (by omega) h).mpr (by omega)))
  · exact False.elim (h4 ((LuRazParametric.row_case_6 q i 4 (by omega) h).mpr (by omega)))
  · exact False.elim (h4 ((LuRazParametric.row_case_7 q i 4 (by omega) h).mpr (by omega)))
  · exact False.elim (h4 ((LuRazParametric.row_case_8 q i 4 (by omega) h).mpr (by omega)))
  · exact False.elim (h23 ⟨(LuRazParametric.row_case_9 q i 2 (by omega) h).mpr (by omega),
      (LuRazParametric.row_case_9 q i 3 (by omega) h).mpr (by omega)⟩)
  · exact False.elim (h23 ⟨(LuRazParametric.row_case_10 q i 2 (by omega) h).mpr (by omega),
      (LuRazParametric.row_case_10 q i 3 (by omega) h).mpr (by omega)⟩)
  · exact False.elim (h23 ⟨(LuRazParametric.row_case_11 q i 2 (by omega) h).mpr (by omega),
      (LuRazParametric.row_case_11 q i 3 (by omega) h).mpr (by omega)⟩)
  · exact False.elim (h23 ⟨(LuRazParametric.row_case_12 q i 2 (by omega) h).mpr (by omega),
      (LuRazParametric.row_case_12 q i 3 (by omega) h).mpr (by omega)⟩)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inl h)
  · exact Or.inl h

theorem small_mix_of_generated (q : Nat) (hq : 4≤q) (R : Nat → Prop)
    (hg : Generated q R) (hc : SmallCore R) :
    ∃ a b c d f : Prop, (a ∨ b ∨ c ∨ d ∨ f) ∧ ∀ e, R e ↔ SmallMix q a b c d f e := by
  obtain ⟨l,hne,hvalid,hR⟩ := hg
  have hi : ∀ i∈l, FixedSmall q i := by
    intro i him
    apply row_fixed_small q i hq (hvalid i him)
    · intro h
      exact hc.1 ((hR 4).mp ⟨i,him,h⟩)
    · rintro ⟨h2,h3⟩
      exact hc.2 ⟨(hR 2).mp ⟨i,him,h2⟩,(hR 3).mp ⟨i,him,h3⟩⟩
  refine ⟨4*q+2∈l,4*q+1∈l,4*q∈l,1∈l,4∈l,?_,?_⟩
  · obtain ⟨i,him⟩ := list_nonempty_witness l hne
    rcases hi i him with h | h | h | h | h <;> subst i
    · exact Or.inl him
    · exact Or.inr (Or.inl him)
    · exact Or.inr (Or.inr (Or.inl him))
    · exact Or.inr (Or.inr (Or.inr (Or.inl him)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr him)))
  · intro e
    constructor
    · intro he
      obtain ⟨i,him,hie⟩ := (hR e).mpr he
      rcases hi i him with h | h | h | h | h <;> subst i
      · exact Or.inl ⟨him,(A_source q e hq).mp hie⟩
      · exact Or.inr (Or.inl ⟨him,(B_source q e hq).mp hie⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨him,(C_source q e hq).mp hie⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨him,(D_source q e hq).mp hie⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨him,(E_source q e hq).mp hie⟩)))
    · intro he
      apply (hR e).mp
      rcases he with h | h | h | h | h
      · exact ⟨4*q+2,h.1,(A_source q e hq).mpr h.2⟩
      · exact ⟨4*q+1,h.1,(B_source q e hq).mpr h.2⟩
      · exact ⟨4*q,h.1,(C_source q e hq).mpr h.2⟩
      · exact ⟨1,h.1,(D_source q e hq).mpr h.2⟩
      · exact ⟨4,h.1,(E_source q e hq).mpr h.2⟩

end LuRazClosure
