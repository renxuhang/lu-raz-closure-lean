import ThreeRowGenerated
import LuRazCore23

namespace LuRazThreeRow
open LuRazClosure LuRazParametric
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

def Core12 (R : Nat → Prop) : Prop := ¬R 1 ∧ ¬R 2 ∧ R 3 ∧ R 4

theorem row_core12 (q i : Nat) (hq : 4 ≤ q) (hi : i ≤ 4*q+2)
    (h1 : ¬VRow q i 1) (h2 : ¬VRow q i 2) :
    i=4*q-1 ∨ i=4*q ∨ i=4*q+1 := by
  by_cases hs : Special q i
  · rcases hs with rfl | rfl | rfl
    · exact False.elim (h1 ((row_two q 1 hq).mpr (by omega)))
    · exact False.elim (h1 ((row_four q 1 hq).mpr (by omega)))
    · exact Or.inl rfl
  rw [unchanged_row q i 1 hs] at h1
  rw [unchanged_row q i 2 hs] at h2
  have hp : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨
      (5≤i ∧ i≤q+2) ∨ (q+3≤i ∧ i≤2*q) ∨ i=2*q+1 ∨ i=2*q+2 ∨ i=2*q+3 ∨
      (2*q+4≤i ∧ i≤3*q) ∨ i=3*q+1 ∨ (3*q+2≤i ∧ i+1≤4*q) ∨
      i=4*q ∨ i=4*q+1 ∨ i=4*q+2 := by omega
  rcases hp with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact False.elim (h1 ((row_case_0 q i 1 (by omega) h).mpr (by omega)))
  · exact False.elim (h2 ((row_case_1 q i 2 (by omega) h).mpr (by omega)))
  · exact False.elim (h1 ((row_case_2 q i 1 (by omega) h).mpr (by omega)))
  · exact False.elim (h1 ((row_case_3 q i 1 (by omega) h).mpr (by omega)))
  · exact False.elim (h1 ((row_case_4 q i 1 (by omega) h).mpr (by omega)))
  · exact False.elim (h1 ((row_case_5 q i 1 (by omega) h).mpr (by omega)))
  · exact False.elim (h1 ((row_case_6 q i 1 (by omega) h).mpr (by omega)))
  · exact False.elim (h2 ((row_case_7 q i 2 (by omega) h).mpr (by omega)))
  · exact False.elim (h2 ((row_case_8 q i 2 (by omega) h).mpr (by omega)))
  · exact False.elim (h2 ((row_case_9 q i 2 (by omega) h).mpr (by omega)))
  · exact False.elim (h2 ((row_case_10 q i 2 (by omega) h).mpr (by omega)))
  · exact False.elim (h2 ((row_case_11 q i 2 (by omega) h).mpr (by omega)))
  · exact False.elim (h2 ((row_case_12 q i 2 (by omega) h).mpr (by omega)))
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · exact False.elim (h1 ((row_case_15 q i 1 (by omega) h).mpr (by omega)))

def LPrime (q e : Nat) : Prop := e=3 ∨ e=4 ∨ I 5 (2*q+1) e ∨ e=4*q

theorem last_source (q e : Nat) (hq : 4 ≤ q) : VRow q (4*q-1) e ↔ LPrime q e := by
  rw [row_last q e hq]
  unfold LPrime I
  omega

theorem c_source (q e : Nat) (hq : 4 ≤ q) : VRow q (4*q) e ↔ CRow q e := by
  rw [unchanged_row q (4*q) e (by unfold Special; omega)]
  exact C_source q e hq

theorem b_source (q e : Nat) (hq : 4 ≤ q) : VRow q (4*q+1) e ↔ BRow q e := by
  rw [unchanged_row q (4*q+1) e (by unfold Special; omega)]
  exact B_source q e hq

def Mix12 (q : Nat) (c b : Prop) (e : Nat) : Prop :=
  LPrime q e ∨ (c ∧ CRow q e) ∨ (b ∧ BRow q e)

theorem core12_mix (q : Nat) (hq : 4 ≤ q) (R : Nat → Prop)
    (hg : Generated q R) (hc : Core12 R) :
    ∃ c b : Prop, ∀ e, R e ↔ Mix12 q c b e := by
  obtain ⟨l,hn,hv,hR⟩ := hg
  have allowed : ∀ i∈l, i=4*q-1 ∨ i=4*q ∨ i=4*q+1 := by
    intro i hi
    exact row_core12 q i hq (hv i hi)
      (fun h => hc.1 ((hR 1).mp ⟨i,hi,h⟩))
      (fun h => hc.2.1 ((hR 2).mp ⟨i,hi,h⟩))
  have hlast : 4*q-1 ∈ l := by
    obtain ⟨i,hi,h4⟩ := (hR 4).mpr hc.2.2.2
    rcases allowed i hi with h | h | h
    · simpa only [h] using hi
    · subst i
      rw [c_source q 4 hq] at h4
      unfold CRow I at h4
      omega
    · subst i
      rw [b_source q 4 hq] at h4
      unfold BRow I at h4
      omega
  refine ⟨4*q∈l,4*q+1∈l,?_⟩
  intro e
  rw [←hR e]
  constructor
  · rintro ⟨i,hi,hie⟩
    rcases allowed i hi with h | h | h
    · subst i; exact Or.inl ((last_source q e hq).mp hie)
    · subst i; exact Or.inr (Or.inl ⟨hi,(c_source q e hq).mp hie⟩)
    · subst i; exact Or.inr (Or.inr ⟨hi,(b_source q e hq).mp hie⟩)
  · intro h
    rcases h with h | ⟨hi,h⟩ | ⟨hi,h⟩
    · exact ⟨4*q-1,hlast,(last_source q e hq).mpr h⟩
    · exact ⟨4*q,hi,(c_source q e hq).mpr h⟩
    · exact ⟨4*q+1,hi,(b_source q e hq).mpr h⟩

theorem mix12_generated (q : Nat) (hq : 4 ≤ q) (c b : Prop) : Generated q (Mix12 q c b) := by
  have hl := generated_congr q (generated_row q (4*q-1) (by omega)) (fun e => last_source q e hq)
  have hc := generated_congr q (generated_row q (4*q) (by omega)) (fun e => c_source q e hq)
  have hb := generated_congr q (generated_row q (4*q+1) (by omega)) (fun e => b_source q e hq)
  apply generated_congr q (generated_optional q (generated_optional q hl hc c) hb b)
  intro e
  unfold Mix12
  exact or_assoc

theorem mix12_core (q : Nat) (hq : 4 ≤ q) (c b : Prop) : Core12 (Mix12 q c b) := by
  refine ⟨?_,?_,?_,?_⟩
  all_goals unfold Mix12 LPrime CRow BRow I
  all_goals omega

theorem core12_exact (q : Nat) (hq : 4 ≤ q) (R : Nat → Prop) :
    Generated q R ∧ Core12 R ↔ ∃ c b : Prop, ∀ e, R e ↔ Mix12 q c b e := by
  constructor
  · exact fun h => core12_mix q hq R h.1 h.2
  · rintro ⟨c,b,he⟩
    refine ⟨generated_congr q (mix12_generated q hq c b) (fun e => (he e).symm),?_⟩
    have hc := mix12_core q hq c b
    unfold Core12 at *
    rw [he 1,he 2,he 3,he 4]
    exact hc

theorem mix12_flags (q : Nat) (hq : 4 ≤ q) (c b : Prop) :
    (Mix12 q c b (2*q+2) ↔ c) ∧ (Mix12 q c b (3*q+2) ↔ b) := by
  unfold Mix12 LPrime CRow BRow I
  constructor <;> (by_cases hc : c <;> by_cases hb : b <;> simp_all <;> omega)

theorem mix12_unique (q : Nat) (hq : 4 ≤ q) (c b c' b' : Prop)
    (he : ∀ e, Mix12 q c b e ↔ Mix12 q c' b' e) : (c ↔ c') ∧ (b ↔ b') := by
  have h1 := he (2*q+2)
  have h2 := he (3*q+2)
  rw [(mix12_flags q hq c b).1,(mix12_flags q hq c' b').1] at h1
  rw [(mix12_flags q hq c b).2,(mix12_flags q hq c' b').2] at h2
  exact ⟨h1,h2⟩

end LuRazThreeRow
