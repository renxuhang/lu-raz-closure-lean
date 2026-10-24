import ExhaustiveCovers

namespace LuRazThreeRow
open LuRazClosure LuRazParametric
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

theorem no4_mid_row (q i : Nat) (hq : 4≤q) (hi : i≤4*q+2)
    (h4 : ¬VRow q i 4) (hh : VRow q i (2*q+1)) : VRow q i (2*q+2) := by
  by_cases hs : Special q i
  · rcases hs with rfl | rfl | rfl
    · rw [row_two q _ hq] at hh; omega
    · rw [row_four q _ hq] at hh; omega
    · exact False.elim (h4 ((row_last q 4 hq).mpr (by omega)))
  have hv : ∀ e, VRow q i e ↔ Row q i e := fun e => unchanged_row q i e hs
  rw [hv] at h4 hh ⊢
  have hr := row_excluding_four q i hq hi h4
  rcases hr with rfl | rfl | rfl | rfl | rfl | ⟨p,hp,rfl⟩
  · rw [C_source q _ hq] at hh ⊢; unfold CRow I at *; omega
  · rw [D_source q _ hq]; unfold DRow I; omega
  · rw [B_source q _ hq] at hh; unfold BRow I at hh; omega
  · rw [A_source q _ hq] at hh; unfold ARow I at hh; omega
  · rw [E_source q _ hq] at hh; unfold ERow I at hh; omega
  · have hpl : p≤2*q := by
      unfold Special LIndex beta at hs
      unfold P at hp
      split at hs <;> omega
    rw [LRow_source q p _ hq hp] at hh
    unfold LRow LNormal I beta at hh
    unfold P at hp
    repeat first | (simp_all <;> omega) | split at hh

theorem no4_mid (q : Nat) (hq : 4≤q) (R : Nat → Prop)
    (hg : Generated q R) (h4 : ¬R 4) : R (2*q+1) → R (2*q+2) := by
  intro hh
  obtain ⟨i,hi,hie,hsub⟩ := point_covered q hg hh
  exact hsub _ (no4_mid_row q i hq hi (fun h => h4 (hsub _ h)) hie)

theorem no4_no_last_row (q i : Nat) (hq : 4≤q) (hi : i≤4*q+2)
    (h4 : ¬VRow q i 4) (hn : ¬VRow q i (4*q-1)) : i=4*q ∨ i=4*q+2 ∨ i=4 := by
  by_cases hs : Special q i
  · rcases hs with rfl | rfl | rfl
    · exact False.elim (hn ((row_two q _ hq).mpr (by omega)))
    · exact Or.inr (Or.inr rfl)
    · exact False.elim (h4 ((row_last q 4 hq).mpr (by omega)))
  have hv : ∀ e, VRow q i e ↔ Row q i e := fun e => unchanged_row q i e hs
  rw [hv] at h4 hn
  have hr := row_excluding_four q i hq hi h4
  rcases hr with rfl | rfl | rfl | rfl | rfl | ⟨p,hp,rfl⟩
  · exact Or.inl rfl
  · rw [D_source q _ hq] at hn; unfold DRow I at hn; omega
  · rw [B_source q _ hq] at hn; unfold BRow I at hn; omega
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)
  · rw [LRow_source q p _ hq hp] at hn
    unfold LRow LNormal I beta at hn
    unfold Special LIndex beta at hs
    unfold P at hp
    repeat first | (simp_all <;> omega) | split at hn | split at hs

inductive Fresh123 where | e | ae | ce deriving DecidableEq, Repr
def Fresh123.eval (q : Nat) : Fresh123 → Nat → Prop
  | .e => EPrime q
  | .ae => fun e => EPrime q e ∨ ARow q e
  | .ce => fun e => EPrime q e ∨ CRow q e

theorem core123_no_last (q : Nat) (hq : 4≤q) (R : Nat → Prop)
    (hg : Generated q R) (hc : Core123 R) (hn : ¬R (4*q-1)) :
    ∃ z : Fresh123, ∀ e, R e ↔ z.eval q e := by
  classical
  obtain ⟨l,hne,hv,hR⟩ := hg
  have hr : ∀ i∈l, i=4*q ∨ i=4*q+2 ∨ i=4 := by
    intro i hi
    exact no4_no_last_row q i hq (hv i hi)
      (fun h => hc.2.2.2 ((hR 4).mp ⟨i,hi,h⟩))
      (fun h => hn ((hR _).mp ⟨i,hi,h⟩))
  have hE : 4∈l := by
    obtain ⟨i,hi,h2⟩ := (hR 2).mpr hc.2.1
    rcases hr i hi with rfl | rfl | rfl
    · rw [c_source q _ hq] at h2; unfold CRow I at h2; omega
    · rw [a_source q _ hq] at h2; unfold ARow I at h2; omega
    · exact hi
  have he : ∀ e, R e ↔ EPrime q e ∨ ((4*q+2∈l)∧ARow q e) ∨ ((4*q∈l)∧CRow q e) := by
    intro e
    rw [←hR e]
    constructor
    · rintro ⟨i,hi,hie⟩
      rcases hr i hi with rfl | rfl | rfl
      · exact Or.inr (Or.inr ⟨hi,(c_source q e hq).mp hie⟩)
      · exact Or.inr (Or.inl ⟨hi,(a_source q e hq).mp hie⟩)
      · exact Or.inl ((e_source q e hq).mp hie)
    · rintro (h | ⟨hi,h⟩ | ⟨hi,h⟩)
      · exact ⟨4,hE,(e_source q e hq).mpr h⟩
      · exact ⟨4*q+2,hi,(a_source q e hq).mpr h⟩
      · exact ⟨4*q,hi,(c_source q e hq).mpr h⟩
  by_cases hC : 4*q∈l
  · refine ⟨.ce,?_⟩
    intro e
    rw [he e]
    unfold Fresh123.eval EPrime ARow CRow I
    by_cases hA : 4*q+2∈l <;> simp only [hA,hC,true_and,false_and,false_or] <;> omega
  · by_cases hA : 4*q+2∈l
    · refine ⟨.ae,?_⟩
      intro e
      rw [he e]
      simp [Fresh123.eval,hA,hC]
    · refine ⟨.e,?_⟩
      intro e
      rw [he e]
      simp [Fresh123.eval,hA,hC]

theorem fresh123_generated (q : Nat) (hq : 4≤q) (z : Fresh123) : Generated q (z.eval q) := by
  have he := generated_congr q (generated_row q 4 (by omega)) (fun e => e_source q e hq)
  cases z with
  | e => exact he
  | ae => exact generated_join q he (generated_congr q (generated_row q (4*q+2) (by omega)) (fun e => a_source q e hq))
  | ce => exact generated_join q he (generated_c q hq)

theorem fresh123_core (q : Nat) (hq : 4≤q) (z : Fresh123) : Core123 (z.eval q) := by
  cases z <;> simp [Core123,Fresh123.eval,EPrime,ARow,CRow,I] <;> omega

theorem fresh123_no_last (q : Nat) (hq : 4≤q) (z : Fresh123) : ¬z.eval q (4*q-1) := by
  cases z <;> simp only [Fresh123.eval,EPrime,ARow,CRow,I] <;> omega

theorem fresh123_unique (q : Nat) (hq : 4≤q) (z w : Fresh123)
    (he : ∀ e, z.eval q e ↔ w.eval q e) : z=w := by
  have h5 := he 5
  have hq3 := he (q+3)
  cases z <;> cases w <;> simp only [Fresh123.eval,EPrime,ARow,CRow,I] at h5 hq3 <;>
    simp_all <;> omega

end LuRazThreeRow
