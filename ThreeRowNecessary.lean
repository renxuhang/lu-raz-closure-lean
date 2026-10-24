import ThreeRowGenerated
namespace LuRazThreeRow
open LuRazParametric LuRazClosure
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

theorem row_two_end (q i : Nat) (hq : 4≤q) (hi : i≤4*q+2)
    (he : VRow q i (2)) : VRow q i (4*q-2) ∨ VRow q i (4*q-1) := by
  by_cases hs : Special q i
  · rcases hs with rfl | rfl | rfl
    · have hv : ∀ e, VRow q (2) e ↔ _ := fun e => row_two q e hq
      simp only [hv] at he ⊢
      simp_all [Special] <;> omega
    · have hv : ∀ e, VRow q (4) e ↔ _ := fun e => row_four q e hq
      simp only [hv] at he ⊢
      simp_all [Special] <;> omega
    · have hv : ∀ e, VRow q (4*q-1) e ↔ _ := fun e => row_last q e hq
      simp only [hv] at he ⊢
      simp_all [Special] <;> omega
  have hv : ∀ e, VRow q i e ↔ Row q i e := fun e => unchanged_row q i e hs
  simp only [hv] at he ⊢
  have hp : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨
      (5≤i ∧ i≤q+2) ∨ (q+3≤i ∧ i≤2*q) ∨ i=2*q+1 ∨ i=2*q+2 ∨ i=2*q+3 ∨
      (2*q+4≤i ∧ i≤3*q) ∨ i=3*q+1 ∨ (3*q+2≤i ∧ i+1≤4*q) ∨
      i=4*q ∨ i=4*q+1 ∨ i=4*q+2 := by omega
  rcases hp with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · have hc : ∀ e, Row q i e ↔ _ := fun e => row_case_0 q i e (by omega) h
    simp only [hc] at he ⊢
    simp_all [Special] <;> omega
  · have hc : ∀ e, Row q i e ↔ _ := fun e => row_case_1 q i e (by omega) h
    simp only [hc] at he ⊢
    simp_all [Special] <;> omega
  · have hc : ∀ e, Row q i e ↔ _ := fun e => row_case_2 q i e (by omega) h
    simp only [hc] at he ⊢
    simp_all [Special] <;> omega
  · have hc : ∀ e, Row q i e ↔ _ := fun e => row_case_3 q i e (by omega) h
    simp only [hc] at he ⊢
    simp_all [Special] <;> omega
  · have hc : ∀ e, Row q i e ↔ _ := fun e => row_case_4 q i e (by omega) h
    simp only [hc] at he ⊢
    simp_all [Special] <;> omega
  · have hc : ∀ e, Row q i e ↔ _ := fun e => row_case_5 q i e (by omega) h
    simp only [hc] at he ⊢
    simp_all [Special] <;> omega
  · have hc : ∀ e, Row q i e ↔ _ := fun e => row_case_6 q i e (by omega) h
    simp only [hc] at he ⊢
    simp_all [Special] <;> omega
  · have hc : ∀ e, Row q i e ↔ _ := fun e => row_case_7 q i e (by omega) h
    simp only [hc] at he ⊢
    simp_all [Special] <;> omega
  · have hc : ∀ e, Row q i e ↔ _ := fun e => row_case_8 q i e (by omega) h
    simp only [hc] at he ⊢
    simp_all [Special] <;> omega
  · have hc : ∀ e, Row q i e ↔ _ := fun e => row_case_9 q i e (by omega) h
    simp only [hc] at he ⊢
    simp_all [Special] <;> omega
  · have hc : ∀ e, Row q i e ↔ _ := fun e => row_case_10 q i e (by omega) h
    simp only [hc] at he ⊢
    simp_all [Special] <;> omega
  · have hc : ∀ e, Row q i e ↔ _ := fun e => row_case_11 q i e (by omega) h
    simp only [hc] at he ⊢
    simp_all [Special] <;> omega
  · have hc : ∀ e, Row q i e ↔ _ := fun e => row_case_12 q i e (by omega) h
    simp only [hc] at he ⊢
    simp_all [Special] <;> omega
  · have hc : ∀ e, Row q i e ↔ _ := fun e => row_case_13 q i e (by omega) h
    simp only [hc] at he ⊢
    simp_all [Special] <;> omega
  · have hc : ∀ e, Row q i e ↔ _ := fun e => row_case_14 q i e (by omega) h
    simp only [hc] at he ⊢
    simp_all [Special] <;> omega
  · have hc : ∀ e, Row q i e ↔ _ := fun e => row_case_15 q i e (by omega) h
    simp only [hc] at he ⊢
    simp_all [Special] <;> omega

theorem row_four_middle (q i : Nat) (hq : 4≤q) (hi : i≤4*q+2)
    (he : VRow q i (4)) : VRow q i (2*q+1) ∨ VRow q i (2*q+2) ∨ VRow q i (2*q+3) := by
  by_cases hs : Special q i
  · rcases hs with rfl | rfl | rfl
    · have hv : ∀ e, VRow q (2) e ↔ _ := fun e => row_two q e hq
      simp only [hv] at he ⊢
      simp_all [Special] <;> omega
    · have hv : ∀ e, VRow q (4) e ↔ _ := fun e => row_four q e hq
      simp only [hv] at he ⊢
      simp_all [Special] <;> omega
    · have hv : ∀ e, VRow q (4*q-1) e ↔ _ := fun e => row_last q e hq
      simp only [hv] at he ⊢
      simp_all [Special] <;> omega
  have hv : ∀ e, VRow q i e ↔ Row q i e := fun e => unchanged_row q i e hs
  simp only [hv] at he ⊢
  have hp : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨
      (5≤i ∧ i≤q+2) ∨ (q+3≤i ∧ i≤2*q) ∨ i=2*q+1 ∨ i=2*q+2 ∨ i=2*q+3 ∨
      (2*q+4≤i ∧ i≤3*q) ∨ i=3*q+1 ∨ (3*q+2≤i ∧ i+1≤4*q) ∨
      i=4*q ∨ i=4*q+1 ∨ i=4*q+2 := by omega
  rcases hp with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · have hc : ∀ e, Row q i e ↔ _ := fun e => row_case_0 q i e (by omega) h
    simp only [hc] at he ⊢
    simp_all [Special] <;> omega
  · have hc : ∀ e, Row q i e ↔ _ := fun e => row_case_1 q i e (by omega) h
    simp only [hc] at he ⊢
    simp_all [Special] <;> omega
  · have hc : ∀ e, Row q i e ↔ _ := fun e => row_case_2 q i e (by omega) h
    simp only [hc] at he ⊢
    simp_all [Special] <;> omega
  · have hc : ∀ e, Row q i e ↔ _ := fun e => row_case_3 q i e (by omega) h
    simp only [hc] at he ⊢
    simp_all [Special] <;> omega
  · have hc : ∀ e, Row q i e ↔ _ := fun e => row_case_4 q i e (by omega) h
    simp only [hc] at he ⊢
    simp_all [Special] <;> omega
  · have hc : ∀ e, Row q i e ↔ _ := fun e => row_case_5 q i e (by omega) h
    simp only [hc] at he ⊢
    simp_all [Special] <;> omega
  · have hc : ∀ e, Row q i e ↔ _ := fun e => row_case_6 q i e (by omega) h
    simp only [hc] at he ⊢
    simp_all [Special] <;> omega
  · have hc : ∀ e, Row q i e ↔ _ := fun e => row_case_7 q i e (by omega) h
    simp only [hc] at he ⊢
    simp_all [Special] <;> omega
  · have hc : ∀ e, Row q i e ↔ _ := fun e => row_case_8 q i e (by omega) h
    simp only [hc] at he ⊢
    simp_all [Special] <;> omega
  · have hc : ∀ e, Row q i e ↔ _ := fun e => row_case_9 q i e (by omega) h
    simp only [hc] at he ⊢
    simp_all [Special] <;> omega
  · have hc : ∀ e, Row q i e ↔ _ := fun e => row_case_10 q i e (by omega) h
    simp only [hc] at he ⊢
    simp_all [Special] <;> omega
  · have hc : ∀ e, Row q i e ↔ _ := fun e => row_case_11 q i e (by omega) h
    simp only [hc] at he ⊢
    simp_all [Special] <;> omega
  · have hc : ∀ e, Row q i e ↔ _ := fun e => row_case_12 q i e (by omega) h
    simp only [hc] at he ⊢
    simp_all [Special] <;> omega
  · have hc : ∀ e, Row q i e ↔ _ := fun e => row_case_13 q i e (by omega) h
    simp only [hc] at he ⊢
    simp_all [Special] <;> omega
  · have hc : ∀ e, Row q i e ↔ _ := fun e => row_case_14 q i e (by omega) h
    simp only [hc] at he ⊢
    simp_all [Special] <;> omega
  · have hc : ∀ e, Row q i e ↔ _ := fun e => row_case_15 q i e (by omega) h
    simp only [hc] at he ⊢
    simp_all [Special] <;> omega

theorem row_prefix_middle (q i : Nat) (hq : 4≤q) (hi : i≤4*q+2)
    (he : VRow q i (q+3)) : VRow q i (2*q+1) ∨ VRow q i (4*q-1) := by
  by_cases hs : Special q i
  · rcases hs with rfl | rfl | rfl
    · have hv : ∀ e, VRow q (2) e ↔ _ := fun e => row_two q e hq
      simp only [hv] at he ⊢
      simp_all [Special] <;> omega
    · have hv : ∀ e, VRow q (4) e ↔ _ := fun e => row_four q e hq
      simp only [hv] at he ⊢
      simp_all [Special] <;> omega
    · have hv : ∀ e, VRow q (4*q-1) e ↔ _ := fun e => row_last q e hq
      simp only [hv] at he ⊢
      simp_all [Special] <;> omega
  have hv : ∀ e, VRow q i e ↔ Row q i e := fun e => unchanged_row q i e hs
  simp only [hv] at he ⊢
  have hp : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨
      (5≤i ∧ i≤q+2) ∨ (q+3≤i ∧ i≤2*q) ∨ i=2*q+1 ∨ i=2*q+2 ∨ i=2*q+3 ∨
      (2*q+4≤i ∧ i≤3*q) ∨ i=3*q+1 ∨ (3*q+2≤i ∧ i+1≤4*q) ∨
      i=4*q ∨ i=4*q+1 ∨ i=4*q+2 := by omega
  rcases hp with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · have hc : ∀ e, Row q i e ↔ _ := fun e => row_case_0 q i e (by omega) h
    simp only [hc] at he ⊢
    simp_all [Special] <;> omega
  · have hc : ∀ e, Row q i e ↔ _ := fun e => row_case_1 q i e (by omega) h
    simp only [hc] at he ⊢
    simp_all [Special] <;> omega
  · have hc : ∀ e, Row q i e ↔ _ := fun e => row_case_2 q i e (by omega) h
    simp only [hc] at he ⊢
    simp_all [Special] <;> omega
  · have hc : ∀ e, Row q i e ↔ _ := fun e => row_case_3 q i e (by omega) h
    simp only [hc] at he ⊢
    simp_all [Special] <;> omega
  · have hc : ∀ e, Row q i e ↔ _ := fun e => row_case_4 q i e (by omega) h
    simp only [hc] at he ⊢
    simp_all [Special] <;> omega
  · have hc : ∀ e, Row q i e ↔ _ := fun e => row_case_5 q i e (by omega) h
    simp only [hc] at he ⊢
    simp_all [Special] <;> omega
  · have hc : ∀ e, Row q i e ↔ _ := fun e => row_case_6 q i e (by omega) h
    simp only [hc] at he ⊢
    simp_all [Special] <;> omega
  · have hc : ∀ e, Row q i e ↔ _ := fun e => row_case_7 q i e (by omega) h
    simp only [hc] at he ⊢
    simp_all [Special] <;> omega
  · have hc : ∀ e, Row q i e ↔ _ := fun e => row_case_8 q i e (by omega) h
    simp only [hc] at he ⊢
    simp_all [Special] <;> omega
  · have hc : ∀ e, Row q i e ↔ _ := fun e => row_case_9 q i e (by omega) h
    simp only [hc] at he ⊢
    simp_all [Special] <;> omega
  · have hc : ∀ e, Row q i e ↔ _ := fun e => row_case_10 q i e (by omega) h
    simp only [hc] at he ⊢
    simp_all [Special] <;> omega
  · have hc : ∀ e, Row q i e ↔ _ := fun e => row_case_11 q i e (by omega) h
    simp only [hc] at he ⊢
    simp_all [Special] <;> omega
  · have hc : ∀ e, Row q i e ↔ _ := fun e => row_case_12 q i e (by omega) h
    simp only [hc] at he ⊢
    simp_all [Special] <;> omega
  · have hc : ∀ e, Row q i e ↔ _ := fun e => row_case_13 q i e (by omega) h
    simp only [hc] at he ⊢
    simp_all [Special] <;> omega
  · have hc : ∀ e, Row q i e ↔ _ := fun e => row_case_14 q i e (by omega) h
    simp only [hc] at he ⊢
    simp_all [Special] <;> omega
  · have hc : ∀ e, Row q i e ↔ _ := fun e => row_case_15 q i e (by omega) h
    simp only [hc] at he ⊢
    simp_all [Special] <;> omega

theorem generated_two_end (q : Nat) (hq : 4≤q) (R : Nat → Prop)
    (hg : Generated q R) (he : R (2)) : R (4*q-2) ∨ R (4*q-1) := by
  obtain ⟨i,hi,hie,hsub⟩ := point_covered q hg he
  exact (row_two_end q i hq hi hie).elim
    (fun h => Or.inl (hsub _ h)) (fun h => Or.inr (hsub _ h))

theorem generated_four_middle (q : Nat) (hq : 4≤q) (R : Nat → Prop)
    (hg : Generated q R) (he : R (4)) : R (2*q+1) ∨ R (2*q+2) ∨ R (2*q+3) := by
  obtain ⟨i,hi,hie,hsub⟩ := point_covered q hg he
  rcases row_four_middle q i hq hi hie with h | h | h
  · exact Or.inl (hsub _ h)
  · exact Or.inr (Or.inl (hsub _ h))
  · exact Or.inr (Or.inr (hsub _ h))

theorem generated_prefix_middle (q : Nat) (hq : 4≤q) (R : Nat → Prop)
    (hg : Generated q R) (he : R (q+3)) : R (2*q+1) ∨ R (4*q-1) := by
  obtain ⟨i,hi,hie,hsub⟩ := point_covered q hg he
  exact (row_prefix_middle q i hq hi hie).elim
    (fun h => Or.inl (hsub _ h)) (fun h => Or.inr (hsub _ h))

end LuRazThreeRow
