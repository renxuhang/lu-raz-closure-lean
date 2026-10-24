import ThreeRowGenerated
import ThreeRowCore12
import LuRazCore23Results

namespace LuRazThreeRow
open LuRazClosure LuRazParametric
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

def Avoid23 (q : Nat) : NF23 → Prop
  | .lp _ p => p ≤ 2*q
  | .creg t => t ≤ 2*q
  | _ => True

def Valid23 (q : Nat) (z : NF23) : Prop := z.Valid q ∧ Avoid23 q z

theorem core23_row_unchanged (q i : Nat) (hq : 4 ≤ q)
    (h1 : ¬VRow q i 1) (h4 : ¬VRow q i 4) : ¬Special q i := by
  intro h
  rcases h with rfl | rfl | rfl
  · exact h1 ((row_two q 1 hq).mpr (by omega))
  · exact h1 ((row_four q 1 hq).mpr (by omega))
  · exact h4 ((row_last q 4 hq).mpr (by omega))

theorem core23_row_horns (q i : Nat) (hq : 4 ≤ q) (hi : i ≤ 4*q+2)
    (h1 : ¬VRow q i 1) (h4 : ¬VRow q i 4) :
    (VRow q i (2*q+1) → VRow q i (2*q+2)) ∧
    (VRow q i 2 → VRow q i (2*q+3) ∨ VRow q i (4*q-1)) := by
  have hs := core23_row_unchanged q i hq h1 h4
  have hr := row_excluding_one_four q i hq hi
    (by rwa [unchanged_row q i 1 hs] at h1)
    (by rwa [unchanged_row q i 4 hs] at h4)
  simp only [unchanged_row q i _ hs]
  rcases hr with rfl | rfl | rfl | ⟨p,hp,rfl⟩
  · simp only [C_source q _ hq,CRow,I]
    constructor <;> omega
  · simp only [D_source q _ hq,DRow,I]
    constructor <;> omega
  · simp only [B_source q _ hq,BRow,I]
    constructor <;> omega
  · have hpl : p ≤ 2*q := by
      unfold Special LIndex beta at hs
      unfold P at hp
      split at hs <;> omega
    simp only [LRow_source q p _ hq hp,LRow,LNormal,I,beta]
    unfold P at hp
    repeat first | (constructor <;> omega) | split

theorem core23_old (q : Nat) (hq : 4 ≤ q) (R : Nat → Prop)
    (hg : Generated q R) (hc : Core23 R) : LuRazClosure.Generated q R := by
  obtain ⟨l,hn,hv,hR⟩ := hg
  have hs : ∀ i∈l, ¬Special q i := by
    intro i hi
    exact core23_row_unchanged q i hq
      (fun h => hc.1 ((hR 1).mp ⟨i,hi,h⟩))
      (fun h => hc.2.2.2 ((hR 4).mp ⟨i,hi,h⟩))
  refine ⟨l,hn,hv,?_⟩
  intro e
  rw [←hR e]
  constructor
  · rintro ⟨i,hi,hie⟩
    exact ⟨i,hi,(unchanged_row q i e (hs i hi)).mpr hie⟩
  · rintro ⟨i,hi,hie⟩
    exact ⟨i,hi,(unchanged_row q i e (hs i hi)).mp hie⟩

theorem core23_horns (q : Nat) (hq : 4 ≤ q) (R : Nat → Prop)
    (hg : Generated q R) (hc : Core23 R) :
    (R (2*q+1) → R (2*q+2)) ∧ (R (2*q+3) ∨ R (4*q-1)) := by
  have row_horns : ∀ i, i ≤ 4*q+2 → (∀ e, VRow q i e → R e) →
      (VRow q i (2*q+1) → VRow q i (2*q+2)) ∧
      (VRow q i 2 → VRow q i (2*q+3) ∨ VRow q i (4*q-1)) := by
    intro i hi hsub
    exact core23_row_horns q i hq hi (fun h => hc.1 (hsub 1 h))
      (fun h => hc.2.2.2 (hsub 4 h))
  constructor
  · intro he
    obtain ⟨i,hi,hie,hsub⟩ := point_covered q hg he
    exact hsub _ ((row_horns i hi hsub).1 hie)
  · obtain ⟨i,hi,hie,hsub⟩ := point_covered q hg hc.2.1
    exact ((row_horns i hi hsub).2 hie).elim
      (fun h => Or.inl (hsub _ h)) (fun h => Or.inr (hsub _ h))

theorem normal23_avoids (q : Nat) (hq : 4 ≤ q) (z : NF23) (hz : z.Valid q)
    (h1 : z.eval q (2*q+1) → z.eval q (2*q+2))
    (h2 : z.eval q (2*q+3) ∨ z.eval q (4*q-1)) : Avoid23 q z := by
  cases z with
  | lp t p =>
    change p ≤ 2*q
    by_cases hp : p ≤ 2*q
    · exact hp
    · have hz' := hz
      simp only [NF23.Valid,P] at hz'
      have hpp : p=2*q+1 := by omega
      have hn := h1
      simp only [NF23.eval,LRow,LNormal,I,beta] at hn
      repeat first | (simp_all <;> omega) | split at hn
  | creg t =>
    change t ≤ 2*q
    simp only [NF23.Valid,P] at hz
    simp only [NF23.eval,I,beta] at h2
    repeat first | (simp_all <;> omega) | split at h2
  | filledM => trivial
  | dgap p => trivial
  | full => trivial
  | cexception => trivial

theorem l_source (q p e : Nat) (hq : 4 ≤ q) (hp : P q p) (hpl : p ≤ 2*q) :
    VRow q (LIndex q p) e ↔ LRow q p p e := by
  rw [unchanged_row q (LIndex q p) e ?_]
  · exact LRow_source q p e hq hp
  · unfold Special LIndex beta
    unfold P at hp
    split <;> omega

theorem generated_l (q t p : Nat) (hq : 4 ≤ q) (ht : P q t) (hp : P q p)
    (htp : t ≤ p) (hpl : p ≤ 2*q) : Generated q (LRow q t p) := by
  have hbt := beta_bounds q t hq ht
  have hbp := beta_bounds q p hq hp
  have ht' := generated_congr q (generated_row q (LIndex q t) (by unfold LIndex; omega))
    (fun e => l_source q t e hq ht (by omega))
  have hp' := generated_congr q (generated_row q (LIndex q p) (by unfold LIndex; omega))
    (fun e => l_source q p e hq hp hpl)
  apply generated_congr q (generated_join q ht' hp')
  intro e
  have h := LRow_join q t t p p e hq ht ht hp hp (by omega) (by omega)
  simpa only [Nat.min_eq_left htp,Nat.max_eq_right htp] using h

theorem generated_c (q : Nat) (hq : 4 ≤ q) : Generated q (CRow q) :=
  generated_congr q (generated_row q (4*q) (by omega)) (fun e => c_source q e hq)

theorem generated_d (q : Nat) (hq : 4 ≤ q) : Generated q (DRow q) := by
  apply generated_congr q (generated_row q 1 (by omega))
  intro e
  rw [unchanged_row q 1 e (by unfold Special; omega)]
  exact D_source q e hq

theorem generated_b (q : Nat) (hq : 4 ≤ q) : Generated q (BRow q) :=
  generated_congr q (generated_row q (4*q+1) (by omega)) (fun e => b_source q e hq)

theorem generated_mixed23 (q t p : Nat) (hq : 4 ≤ q) (ht : P q t) (hp : P q p)
    (htp : t ≤ p) (hpl : p ≤ 2*q) (u v w : Prop) : Generated q (Mixed23 q t p u v w) := by
  apply generated_congr q (generated_optional q
    (generated_optional q (generated_optional q (generated_l q t p hq ht hp htp hpl)
      (generated_c q hq) u) (generated_d q hq) v) (generated_b q hq) w)
  intro e
  simp only [Mixed23,or_assoc]

theorem normal23_generated (q : Nat) (hq : 4 ≤ q) (z : NF23) (hz : Valid23 q z) :
    Generated q (z.eval q) := by
  have hpe : P q (q+3) := by unfold P; omega
  cases z with
  | lp t p => exact generated_l q t p hq hz.1.1 hz.1.2.1 hz.1.2.2 hz.2
  | filledM =>
    apply generated_congr q (generated_mixed23 q (q+3) (q+3) hq hpe hpe (by omega) (by omega) False False True)
    intro e
    simp only [Mixed23,NF23.eval,false_and,false_or,true_and,LRow,LNormal,I,beta,BRow]
    repeat first | (simp_all <;> omega) | split
  | dgap p =>
    have hp : P q p ∧ p≤2*q-1 := hz.1
    apply generated_congr q (generated_mixed23 q p p hq hp.1 hp.1 (by omega) (by omega) False True False)
    intro e
    simp only [Mixed23,NF23.eval,false_and,false_or,or_false,true_and,LRow,LNormal,I,beta,DRow]
    unfold P at hp
    repeat first | (simp_all <;> omega) | split
  | full =>
    apply generated_congr q (generated_join q (generated_c q hq) (generated_d q hq))
    intro e
    simp only [NF23.eval,CRow,DRow,I]
    omega
  | creg t =>
    have ht : P q t ∧ t≠q+3 := hz.1
    have htl : t≤2*q := hz.2
    apply generated_congr q (generated_mixed23 q t t hq ht.1 ht.1 (by omega) htl True False False)
    intro e
    simp only [Mixed23,NF23.eval,false_and,false_or,or_false,true_and,LRow,LNormal,I,beta,CRow]
    unfold P at ht
    repeat first | (simp_all <;> omega) | split
  | cexception =>
    apply generated_congr q (generated_mixed23 q (q+3) (q+3) hq hpe hpe (by omega) (by omega) True False False)
    intro e
    simp only [Mixed23,NF23.eval,false_and,false_or,or_false,true_and,LRow,LNormal,I,beta,CRow]
    repeat first | (simp_all <;> omega) | split

theorem core23_exact (q : Nat) (hq : 4 ≤ q) (R : Nat → Prop) :
    Generated q R ∧ Core23 R ↔ ∃ z : NF23, Valid23 q z ∧ ∀ e, R e ↔ z.eval q e := by
  constructor
  · intro h
    have hold := core23_old q hq R h.1 h.2
    obtain ⟨z,hz,he⟩ := (core23_closure_exact q hq R).mp ⟨hold,h.2⟩
    have hh := core23_horns q hq R h.1 h.2
    have hz1 : z.eval q (2*q+1) → z.eval q (2*q+2) :=
      fun h => (he _).mp (hh.1 ((he _).mpr h))
    have hz2 := hh.2
    rw [he _,he _] at hz2
    exact ⟨z,⟨hz,normal23_avoids q hq z hz hz1 hz2⟩,he⟩
  · rintro ⟨z,hz,he⟩
    refine ⟨generated_congr q (normal23_generated q hq z hz) (fun e => (he e).symm),?_⟩
    have hc := NF23.core q hq z hz.1
    unfold Core23 at *
    rw [he 1,he 2,he 3,he 4]
    exact hc

end LuRazThreeRow
