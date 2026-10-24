import SixRowCore13Parts
import ExhaustiveCovers

namespace LuRazSixRowClosure
open LuRazClosure LuRazParametric LuRazEnumeration
set_option maxRecDepth 32768
set_option maxHeartbeats 14000000
set_option linter.unusedSimpArgs false

def DPrime14 (q e : Nat) : Prop := e=2 ∨ e=4 ∨ I (2*q+1) (4*q-2) e ∨ e=4*q

def E14 (q e : Nat) : Prop := e=2 ∨ e=3 ∨ I (2*q+3) (4*q) e

def KPrime14 (q e : Nat) : Prop := e=2 ∨ e=4 ∨ I (2*q+3) (4*q-2) e ∨ e=4*q

def Restricted14 (q i : Nat) : Prop :=
  i=4 ∨ i=1 ∨ i=4*q ∨ i=4*q+1 ∨ i=2*q+1 ∨ i=2*q+2 ∨
  ∃ p,P q p ∧ p≤2*q ∧ i=LIndex q p

theorem original_row14 (q i e : Nat) (hi : i≠1 ∧ i≠2 ∧ i≠4 ∧ i≠2*q+2 ∧ i≠4*q-1 ∧ i≠4*q) :
    LuRazSixRow.BRow q i e ↔ Row q i e := by
  rw [LuRazSixRow.unchanged_row q i e (by unfold LuRazSixRow.Special; omega),
    LuRazFourRow.unchanged_row q i e (by unfold LuRazFourRow.Special; omega),
    LuRazThreeRow.unchanged_row q i e (by unfold LuRazThreeRow.Special; omega)]

theorem d_source14 (q e : Nat) (hq : 4≤q) : LuRazSixRow.BRow q 1 e ↔ DPrime14 q e := by
  rw [LuRazSixRow.unchanged_row q 1 e (by unfold LuRazSixRow.Special; omega),LuRazFourRow.row_one q e hq]
  rfl

theorem e_source14 (q e : Nat) (hq : 4≤q) : LuRazSixRow.BRow q 4 e ↔ E14 q e := by
  rw [LuRazSixRow.unchanged_row q 4 e (by unfold LuRazSixRow.Special; omega),LuRazFourRow.row_four q e hq]
  rfl

theorem k1_source14 (q e : Nat) (hq : 4≤q) : LuRazSixRow.BRow q (2*q+1) e ↔ K1Row q e := by
  rw [original_row14 q (2*q+1) e (by omega)]
  exact K1_source q e hq

theorem k2_source14 (q e : Nat) (hq : 4≤q) : LuRazSixRow.BRow q (2*q+2) e ↔ KPrime14 q e := by
  rw [LuRazSixRow.row_middle q e hq]
  rfl

theorem l_source14 (q p e : Nat) (hq : 4≤q) (hp : P q p) (hps : p≤2*q) :
    LuRazSixRow.BRow q (LIndex q p) e ↔ LRow q p p e := by
  rw [original_row14 q (LIndex q p) e (by unfold LIndex beta; unfold P at hp; split <;> omega)]
  exact LRow_source q p e hq hp

theorem row_no1_14 (q i : Nat) (hq : 4≤q) (hi : i≤4*q+2)
    (h1 : ¬LuRazSixRow.BRow q i 1) : Restricted14 q i := by
  by_cases hs : LuRazSixRow.Special q i
  · rcases hs with rfl | rfl | rfl
    · unfold Restricted14; omega
    · exact False.elim (h1 ((LuRazSixRow.row_last q 1 hq).mpr (by omega)))
    · unfold Restricted14; omega
  rw [LuRazSixRow.unchanged_row q i 1 hs] at h1
  by_cases hs' : LuRazFourRow.Special q i
  · rcases hs' with rfl | rfl | rfl
    · unfold Restricted14; omega
    · unfold Restricted14; omega
    · exact False.elim (hs (Or.inr (Or.inl rfl)))
  rw [LuRazFourRow.unchanged_row q i 1 hs'] at h1
  by_cases hs'' : LuRazThreeRow.Special q i
  · rcases hs'' with rfl | rfl | rfl
    · exact False.elim (h1 ((LuRazThreeRow.row_two q 1 hq).mpr (by omega)))
    · exact False.elim (hs' (Or.inr (Or.inl rfl)))
    · exact False.elim (hs (Or.inr (Or.inl rfl)))
  rw [LuRazThreeRow.unchanged_row q i 1 hs''] at h1
  have hr := row_excluding_one q i hq hi h1
  rcases hr with h | h | h | h | h | ⟨p,hp,he⟩
  all_goals try (unfold Restricted14; omega)
  have hps : p≤2*q := by
    unfold LuRazSixRow.Special at hs
    unfold LIndex beta at he
    unfold P at hp
    split at he <;> omega
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨p,hp,hps,he⟩)))))

theorem no1_three_last14 (q i : Nat) (hq : 4≤q) (hi : i≤4*q+2)
    (h1 : ¬LuRazSixRow.BRow q i 1) (h3 : LuRazSixRow.BRow q i 3) :
    LuRazSixRow.BRow q i (4*q-1) := by
  rcases row_no1_14 q i hq hi h1 with rfl | rfl | rfl | rfl | rfl | rfl | ⟨p,hp,hps,rfl⟩
  · rw [e_source14 q (4*q-1) hq]; unfold E14 I; omega
  · rw [d_source14 q 3 hq] at h3; unfold DPrime14 I at h3; omega
  · rw [c_source q (4*q-1) hq]; unfold CPrime I; omega
  · rw [b_source q 3 hq] at h3; unfold LuRazClosure.BRow I at h3; omega
  · rw [k1_source14 q 3 hq] at h3; unfold K1Row I at h3; omega
  · rw [k2_source14 q 3 hq] at h3; unfold KPrime14 I at h3; omega
  · rw [l_source14 q p (4*q-1) hq hp hps]
    unfold LRow LNormal I beta
    unfold P at hp
    repeat first | omega | split

theorem no1_four_index14 (q i : Nat) (hq : 4≤q) (hi : i≤4*q+2)
    (h1 : ¬LuRazSixRow.BRow q i 1) (h4 : LuRazSixRow.BRow q i 4) :
    i=1 ∨ i=2*q+1 ∨ i=2*q+2 := by
  rcases row_no1_14 q i hq hi h1 with rfl | rfl | rfl | rfl | rfl | rfl | ⟨p,hp,hps,rfl⟩
  · rw [e_source14 q 4 hq] at h4; unfold E14 I at h4; omega
  · omega
  · rw [c_source q 4 hq] at h4; unfold CPrime I at h4; omega
  · rw [b_source q 4 hq] at h4; unfold LuRazClosure.BRow I at h4; omega
  · omega
  · omega
  · rw [l_source14 q p 4 hq hp hps] at h4
    unfold LRow LNormal I beta at h4
    unfold LIndex beta
    unfold P at hp
    repeat first | omega | split | split at h4

theorem core14_horns (q : Nat) (hq : 4≤q) (R : Nat → Prop)
    (hg : Generated q R) (hc : Core234 R) :
    R (4*q-1) ∧ (R (4*q) ∨ R (2*q+2)) ∧ R (2*q+3) := by
  obtain ⟨i,hi,hi3,hsub⟩ := point_covered q hg hc.2.2.1
  have hn := hsub _ (no1_three_last14 q i hq hi (fun h => hc.1 (hsub 1 h)) hi3)
  obtain ⟨j,hj,hj4,hjsub⟩ := point_covered q hg hc.2.2.2
  have hjc := no1_four_index14 q j hq hj (fun h => hc.1 (hjsub 1 h)) hj4
  refine ⟨hn,?_,?_⟩
  · rcases hjc with rfl | rfl | rfl
    · exact Or.inl (hjsub _ ((d_source14 q (4*q) hq).mpr (by unfold DPrime14 I; omega)))
    · exact Or.inr (hjsub _ ((k1_source14 q (2*q+2) hq).mpr (by unfold K1Row I; omega)))
    · exact Or.inl (hjsub _ ((k2_source14 q (4*q) hq).mpr (by unfold KPrime14 I; omega)))
  · rcases hjc with rfl | rfl | rfl
    · exact hjsub _ ((d_source14 q (2*q+3) hq).mpr (by unfold DPrime14 I; omega))
    · exact hjsub _ ((k1_source14 q (2*q+3) hq).mpr (by unfold K1Row I; omega))
    · exact hjsub _ ((k2_source14 q (2*q+3) hq).mpr (by unfold KPrime14 I; omega))

theorem old_nf_cover14 (q : Nat) (hq : 4≤q) (R : Nat → Prop) (hc : Core234 R)
    (hn : R (4*q-1)) (i j e : Nat)
    (hsi : ∀ f,LuRazSixRow.BRow q i f → R f) (hsj : ∀ f,LuRazSixRow.BRow q j f → R f)
    (hie : LuRazSixRow.BRow q i e) (w : NF234) (hw : w.Valid q)
    (hpt : ∀ f,LuRazSixRow.BRow q i f → w.eval q f)
    (hcov : ∀ f,w.eval q f → LuRazSixRow.BRow q i f ∨ LuRazSixRow.BRow q j f ∨
      f=2 ∨ f=3 ∨ f=4 ∨ f=4*q-1) :
    ∃ T,LuRazClosure.Generated q T ∧ T e ∧ ∀ f,T f → R f := by
  refine ⟨w.eval q,NF234.generated q hq w hw,hpt e hie,?_⟩
  intro f hf
  rcases hcov f hf with h | h | rfl | rfl | rfl | rfl
  · exact hsi f h
  · exact hsj f h
  · exact hc.2.1
  · exact hc.2.2.1
  · exact hc.2.2.2
  · exact hn

theorem core14_original (q : Nat) (hq : 4≤q) (R : Nat → Prop)
    (hg : Generated q R) (hc : Core234 R) : LuRazClosure.Generated q R := by
  have hn := (core14_horns q hq R hg hc).1
  apply LuRazThreeRow.old_of_local_covers q R 4 hc.2.2.2
  intro e he
  obtain ⟨i,hi,hie,hsi⟩ := point_covered q hg he
  have hir := row_no1_14 q i hq hi (fun h => hc.1 (hsi 1 h))
  rcases hir with rfl | rfl | rfl | rfl | rfl | rfl | ⟨p,hp,hps,rfl⟩
  · apply old_nf_cover14 q hq R hc hn 4 4 e hsi hsi hie (.kr 4 1) (by simp [NF234.Valid,P]; omega)
    · intro f hf
      rw [e_source14 q f hq] at hf
      simp [NF234.eval,T234,E14,I] at hf ⊢
      omega
    · intro f hf
      rw [e_source14 q f hq]
      simp [NF234.eval,T234,E14,I] at hf ⊢
      omega
  · apply old_nf_cover14 q hq R hc hn 1 1 e hsi hsi hie (.dg 4) (by simp [NF234.Valid,P]; omega)
    · intro f hf
      rw [d_source14 q f hq] at hf
      simp [NF234.eval,T234,DPrime14,I] at hf ⊢
      omega
    · intro f hf
      rw [d_source14 q f hq]
      simp [NF234.eval,T234,DPrime14,I] at hf ⊢
      omega
  · obtain ⟨j,hj,hj4,hsj⟩ := point_covered q hg hc.2.2.2
    have hjc := no1_four_index14 q j hq hj (fun h => hc.1 (hsj 1 h)) hj4
    rcases hjc with rfl | rfl | rfl
    · apply old_nf_cover14 q hq R hc hn (4*q) 1 e hsi hsj hie (.kr (2*q+1) 0) (by simp [NF234.Valid,P]; omega)
      · intro f hf
        rw [c_source q f hq] at hf
        simp [NF234.eval,T234,CPrime,I] at hf ⊢
        omega
      · intro f hf
        rw [c_source q f hq,d_source14 q f hq]
        simp [NF234.eval,T234,CPrime,DPrime14,I] at hf ⊢
        omega
    · apply old_nf_cover14 q hq R hc hn (4*q) (2*q+1) e hsi hsj hie (.ck 1) (by simp [NF234.Valid])
      · intro f hf
        rw [c_source q f hq] at hf
        simp [NF234.eval,T234,CPrime,I] at hf ⊢
        omega
      · intro f hf
        rw [c_source q f hq,k1_source14 q f hq]
        simp [NF234.eval,T234,CPrime,K1Row,I] at hf ⊢
        omega
    · apply old_nf_cover14 q hq R hc hn (4*q) (2*q+2) e hsi hsj hie (.kr (2*q+1) 1) (by simp [NF234.Valid,P]; omega)
      · intro f hf
        rw [c_source q f hq] at hf
        simp [NF234.eval,T234,CPrime,I] at hf ⊢
        omega
      · intro f hf
        rw [c_source q f hq,k2_source14 q f hq]
        simp [NF234.eval,T234,CPrime,KPrime14,I] at hf ⊢
        omega
  · refine ⟨Row q (4*q+1),LuRazClosure.generated_row q _ (by omega),?_,?_⟩
    · exact (original_row14 q _ e (by omega)).mp hie
    · intro f hf
      exact hsi f ((original_row14 q _ f (by omega)).mpr hf)
  · refine ⟨Row q (2*q+1),LuRazClosure.generated_row q _ (by omega),?_,?_⟩
    · exact (original_row14 q _ e (by omega)).mp hie
    · intro f hf
      exact hsi f ((original_row14 q _ f (by omega)).mpr hf)
  · apply old_nf_cover14 q hq R hc hn (2*q+2) (2*q+2) e hsi hsi hie (.kr 4 1) (by simp [NF234.Valid,P]; omega)
    · intro f hf
      rw [k2_source14 q f hq] at hf
      simp [NF234.eval,T234,KPrime14,I] at hf ⊢
      omega
    · intro f hf
      rw [k2_source14 q f hq]
      simp [NF234.eval,T234,KPrime14,I] at hf ⊢
      omega
  · have hix : (LIndex q p)≠1 ∧ (LIndex q p)≠2 ∧ (LIndex q p)≠4 ∧
        (LIndex q p)≠2*q+2 ∧ (LIndex q p)≠4*q-1 ∧ (LIndex q p)≠4*q := by
      unfold LIndex beta
      unfold P at hp
      split <;> omega
    refine ⟨Row q (LIndex q p),LuRazClosure.generated_row q _ hi,?_,?_⟩
    · exact (original_row14 q _ e hix).mp hie
    · intro f hf
      exact hsi f ((original_row14 q _ f hix).mpr hf)

end LuRazSixRowClosure
