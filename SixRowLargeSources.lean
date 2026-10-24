import SixRowClosureDefs
namespace LuRazSixRowClosure
open LuRazClosure LuRazParametric LuRazSixRow
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

def C6 (q e : Nat) : Prop := e=3 ∨ I 5 (2*q+1) e ∨ e=3*q+1 ∨ e=4*q-1
def E6 (q e : Nat) : Prop := e=2 ∨ e=3 ∨ I (2*q+3) (4*q) e
def Z7 (q e : Nat) : Prop := e=1 ∨ e=3 ∨ I 5 (2*q) e ∨ e=4*q-1 ∨ e=4*q
def H7 (q e : Nat) : Prop := e=1 ∨ e=3 ∨ I 5 (2*q+2) e
def OrdinaryLarge (q i : Nat) : Prop :=
  i≠1 ∧ i≠2 ∧ i≠4 ∧ i≠2*q+2 ∧ i≠4*q-1 ∧ i≠4*q

theorem large_ordinary (q i e : Nat) (hi : OrdinaryLarge q i) :
    LuRazSixRow.BRow q i e ↔ Row q i e := by
  rw [LuRazSixRow.unchanged_row q i e (by unfold LuRazSixRow.Special; unfold OrdinaryLarge at hi; omega),
    LuRazFourRow.unchanged_row q i e (by unfold LuRazFourRow.Special; unfold OrdinaryLarge at hi; omega),
    LuRazThreeRow.unchanged_row q i e (by unfold LuRazThreeRow.Special; unfold OrdinaryLarge at hi; omega)]

theorem c6_source (q e : Nat) (hq : 4≤q) : LuRazSixRow.BRow q (4*q) e ↔ C6 q e := by
  rw [LuRazSixRow.row_n q e hq]; rfl
theorem e6_source (q e : Nat) (hq : 4≤q) : LuRazSixRow.BRow q 4 e ↔ E6 q e := by
  rw [LuRazSixRow.unchanged_row q 4 e (by unfold LuRazSixRow.Special; omega),LuRazFourRow.row_four q e hq]; rfl
theorem z7_source (q e : Nat) (hq : 4≤q) : LuRazSixRow.BRow q 2 e ↔ Z7 q e := by
  rw [LuRazSixRow.unchanged_row q 2 e (by unfold LuRazSixRow.Special; omega),LuRazFourRow.row_two q e hq]; rfl
theorem h7_source (q e : Nat) (hq : 4≤q) : LuRazSixRow.BRow q (4*q-1) e ↔ H7 q e := by
  rw [LuRazSixRow.row_last q e hq]; rfl
theorem b0_source (q e : Nat) (hq : 4≤q) :
    LuRazSixRow.BRow q (4*q+1) e ↔ LuRazClosure.BRow q e := by
  rw [large_ordinary q (4*q+1) e (by unfold OrdinaryLarge; omega),LuRazClosure.B_source q e hq]
theorem a0_source (q e : Nat) (hq : 4≤q) :
    LuRazSixRow.BRow q (4*q+2) e ↔ ARow q e := by
  rw [large_ordinary q (4*q+2) e (by unfold OrdinaryLarge; omega),LuRazClosure.A_source q e hq]
theorem l6_source (q p e : Nat) (hq : 4≤q) (hp : P q p) (hph : p≤2*q) :
    LuRazSixRow.BRow q (LIndex q p) e ↔ LRow q p p e := by
  have hpb := hp
  unfold P at hpb
  have hb := beta_bounds q p hq hp
  have hbi : OrdinaryLarge q (LIndex q p) := by
    unfold OrdinaryLarge LIndex beta at *
    split <;> omega
  rw [large_ordinary q (LIndex q p) e hbi,LRow_source q p e hq hp]

theorem generated_c6 (q : Nat) (hq : 4≤q) : Generated q (C6 q) :=
  generated_congr q (generated_row q (4*q) (by omega)) (fun e=>c6_source q e hq)
theorem generated_e6 (q : Nat) (hq : 4≤q) : Generated q (E6 q) :=
  generated_congr q (generated_row q 4 (by omega)) (fun e=>e6_source q e hq)
theorem generated_b0 (q : Nat) (hq : 4≤q) : Generated q (LuRazClosure.BRow q) :=
  generated_congr q (generated_row q (4*q+1) (by omega)) (fun e=>b0_source q e hq)
theorem generated_a0 (q : Nat) (hq : 4≤q) : Generated q (ARow q) :=
  generated_congr q (generated_row q (4*q+2) (by omega)) (fun e=>a0_source q e hq)
theorem generated_z7 (q : Nat) (hq : 4≤q) : Generated q (Z7 q) :=
  generated_congr q (generated_row q 2 (by omega)) (fun e=>z7_source q e hq)
theorem generated_h7 (q : Nat) (hq : 4≤q) : Generated q (H7 q) :=
  generated_congr q (generated_row q (4*q-1) (by omega)) (fun e=>h7_source q e hq)
theorem generated_l6 (q t p : Nat) (hq : 4≤q) (ht : P q t) (hp : P q p)
    (htp : t≤p) (hph : p≤2*q) : Generated q (LRow q t p) := by
  have h1 := generated_congr q (generated_row q (LIndex q t) (by
    have hb := beta_bounds q t hq ht; unfold LIndex; omega)) (fun e=>l6_source q t e hq ht (by omega))
  have h2 := generated_congr q (generated_row q (LIndex q p) (by
    have hb := beta_bounds q p hq hp; unfold LIndex; omega)) (fun e=>l6_source q p e hq hp hph)
  apply generated_congr q (generated_join q h1 h2)
  intro e
  have he := LRow_join q t t p p e hq ht ht hp hp (by omega) (by omega)
  simpa only [Nat.min_eq_left htp,Nat.max_eq_right htp] using he

def Restricted6 (q i : Nat) : Prop := i=4*q ∨ i=4 ∨ i=4*q+1 ∨
  ∃p,P q p ∧ p≤2*q ∧ i=LIndex q p

theorem no_one_four_source6 (q i : Nat) (hq : 4≤q) (hi : i≤4*q+2)
    (h1 : ¬LuRazSixRow.BRow q i 1) (h4 : ¬LuRazSixRow.BRow q i 4) : Restricted6 q i := by
  by_cases h : i=1
  · subst i
    exact False.elim (h4 ((LuRazSixRow.unchanged_row q 1 4 (by unfold LuRazSixRow.Special; omega)).mpr
      ((LuRazFourRow.row_one q 4 hq).mpr (by omega))))
  by_cases h2 : i=2
  · subst i; exact False.elim (h1 ((z7_source q 1 hq).mpr (by unfold Z7; omega)))
  by_cases he : i=4
  · exact Or.inr (Or.inl he)
  by_cases hk : i=2*q+2
  · subst i; exact False.elim (h4 ((LuRazSixRow.row_middle q 4 hq).mpr (by omega)))
  by_cases hl : i=4*q-1
  · subst i; exact False.elim (h1 ((h7_source q 1 hq).mpr (by unfold H7; omega)))
  by_cases hc : i=4*q
  · exact Or.inl hc
  have ho : OrdinaryLarge q i := ⟨h,h2,he,hk,hl,hc⟩
  have hr := row_excluding_one_four q i hq hi
    (fun hh=>h1 ((large_ordinary q i 1 ho).mpr hh))
    (fun hh=>h4 ((large_ordinary q i 4 ho).mpr hh))
  rcases hr with hr|hr|hr|⟨p,hp,hr⟩
  · exact False.elim (hc hr)
  · exact False.elim (h hr)
  · exact Or.inr (Or.inr (Or.inl hr))
  · refine Or.inr (Or.inr (Or.inr ⟨p,hp,?_,hr⟩))
    have hp' := hp
    unfold P at hp'
    unfold LIndex beta at hr
    split at hr <;> omega

end LuRazSixRowClosure
