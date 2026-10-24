import ThreeRowCore23
import LuRazCore234Results

namespace LuRazThreeRow
open LuRazClosure LuRazParametric
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

theorem no_one_flip (q i e : Nat) (hq : 4≤q) (h1 : ¬Row q i 1) :
    VRow q i e ↔ (Row q i e ∧ ¬(i=4*q-1 ∧ e=2)) ∨ (i=4*q-1 ∧ e=4) := by
  have hi2 : i≠2 := by
    intro h; exact h1 ((row_case_2 q i 1 (by omega) h).mpr (by omega))
  have hi4 : i≠4 := by
    intro h; exact h1 ((row_case_4 q i 1 (by omega) h).mpr (by omega))
  simp only [VRow,Removed,Added,hi2,hi4,false_and,false_or]

theorem no_one_four_row (q i : Nat) (hq : 4≤q) (hi : i≤4*q+2)
    (h1 : ¬Row q i 1) (h4 : Row q i 4) :
    Row q i 2 ∧ VRow q i 2 ∧ VRow q i 4 ∧ Row q i (2*q+3) := by
  have hr := row_excluding_one q i hq hi h1
  rcases hr with rfl | rfl | rfl | rfl | rfl | ⟨p,hp,rfl⟩
  · rw [C_source q 4 hq] at h4; unfold CRow I at h4; omega
  · rw [D_source q 4 hq] at h4; unfold DRow I at h4; omega
  · rw [B_source q 4 hq] at h4; unfold BRow I at h4; omega
  · have hs : ¬Special q (2*q+1) := by unfold Special; omega
    have hva : ∀ e, VRow q (2*q+1) e ↔ Row q (2*q+1) e := fun e => unchanged_row q _ e hs
    have hsem : ∀ e, Row q (2*q+1) e ↔ K1Row q e := fun e => K1_source q e hq
    simp [hva,hsem,K1Row,I] <;> omega
  · have hs : ¬Special q (2*q+2) := by unfold Special; omega
    have hva : ∀ e, VRow q (2*q+2) e ↔ Row q (2*q+2) e := fun e => unchanged_row q _ e hs
    have hsem : ∀ e, Row q (2*q+2) e ↔ K2Row q e := fun e => K2_source q e hq
    simp [hva,hsem,K2Row,I] <;> omega
  · rw [LRow_source q p 4 hq hp] at h4
    unfold LRow LNormal I beta at h4
    unfold P at hp
    repeat first | (simp_all <;> omega) | split at h4

theorem no_one_two_row (q i : Nat) (hq : 4≤q) (hi : i≤4*q+2)
    (h1 : ¬Row q i 1) (h2 : VRow q i 2) :
    VRow q i (2*q+3) ∨ VRow q i (4*q-1) := by
  have hflip := (no_one_flip q i 2 hq h1).mp h2
  have hn : i≠4*q-1 := by omega
  have hs : ¬Special q i := by
    intro h
    rcases h with h | h | h
    · exact h1 ((row_case_2 q i 1 (by omega) h).mpr (by omega))
    · exact h1 ((row_case_4 q i 1 (by omega) h).mpr (by omega))
    · exact hn h
  have hr := row_excluding_one q i hq hi h1
  simp only [unchanged_row q i _ hs]
  rcases hr with rfl | rfl | rfl | rfl | rfl | ⟨p,hp,rfl⟩
  · rw [unchanged_row q (4*q) 2 hs,C_source q 2 hq] at h2
    unfold CRow I at h2; omega
  · exact Or.inl ((D_source q _ hq).mpr (by unfold DRow I; omega))
  · rw [unchanged_row q (4*q+1) 2 hs,B_source q 2 hq] at h2
    unfold BRow I at h2; omega
  · exact Or.inl ((K1_source q _ hq).mpr (by unfold K1Row I; omega))
  · exact Or.inl ((K2_source q _ hq).mpr (by unfold K2Row I; omega))
  · apply Or.inr
    rw [LRow_source q p _ hq hp]
    unfold P at hp
    unfold LIndex beta at hn
    unfold LRow LNormal I beta
    repeat first | (simp_all <;> omega) | split

/-- A no-one modified union has an old union shadow, and only bits 2 and 4 can differ. -/
theorem no_one_shadow (q : Nat) (hq : 4≤q) (R : Nat → Prop)
    (hg : Generated q R) (h1 : ¬R 1) :
    ∃ T, LuRazClosure.Generated q T ∧ ¬T 1 ∧
      (∀ e, e≠2 → e≠4 → (R e ↔ T e)) ∧
      (R 2 → T 2) ∧ (T 4 → R 4 ∧ R 2) ∧
      (¬T 4 → R 4 → ∀ e, Row q (4*q-1) e → T e) ∧
      (R 2 → R (2*q+3) ∨ R (4*q-1)) := by
  obtain ⟨l,hn,hv,hR⟩ := hg
  let T := ListUnion (Row q) l
  have no1 : ∀ i∈l, ¬Row q i 1 := by
    intro i hi h
    exact h1 ((hR 1).mp ⟨i,hi,(unchanged_column q i 1 (by unfold Special; omega)).mpr h⟩)
  have hT4 : T 4 → R 4 ∧ R 2 := by
    rintro ⟨i,hi,h4⟩
    have hh := no_one_four_row q i hq (hv i hi) (no1 i hi) h4
    exact ⟨(hR 4).mp ⟨i,hi,hh.2.2.1⟩,(hR 2).mp ⟨i,hi,hh.2.1⟩⟩
  refine ⟨T,⟨l,hn,hv,fun _ => Iff.rfl⟩,?_,?_,?_,hT4,?_,?_⟩
  · exact fun ⟨i,hi,h⟩ => no1 i hi h
  · intro e he2 he4
    rw [←hR e]
    constructor
    · rintro ⟨i,hi,hie⟩
      have hf := (no_one_flip q i e hq (no1 i hi)).mp hie
      exact ⟨i,hi,by rcases hf with h | h; exact h.1; omega⟩
    · rintro ⟨i,hi,hie⟩
      exact ⟨i,hi,(no_one_flip q i e hq (no1 i hi)).mpr (Or.inl ⟨hie,by omega⟩)⟩
  · intro h2
    obtain ⟨i,hi,hie⟩ := (hR 2).mpr h2
    have hf := (no_one_flip q i 2 hq (no1 i hi)).mp hie
    rcases hf with h | h
    · exact ⟨i,hi,h.1⟩
    · omega
  · intro ht4 hr4 e he
    obtain ⟨i,hi,hie⟩ := (hR 4).mpr hr4
    have hf := (no_one_flip q i 4 hq (no1 i hi)).mp hie
    have hil : i=4*q-1 := by
      rcases hf with h | h
      · exact False.elim (ht4 ⟨i,hi,h.1⟩)
      · exact h.1
    exact ⟨4*q-1,by simpa only [hil] using hi,he⟩
  · intro h2
    obtain ⟨i,hi,hie⟩ := (hR 2).mpr h2
    exact (no_one_two_row q i hq (hv i hi) (no1 i hi) hie).elim
      (fun h => Or.inl ((hR _).mp ⟨i,hi,h⟩))
      (fun h => Or.inr ((hR _).mp ⟨i,hi,h⟩))

end LuRazThreeRow
