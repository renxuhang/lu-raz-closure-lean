import ThreeRowNoOne

namespace LuRazThreeRow
open LuRazClosure LuRazParametric
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

theorem old234_in_new (q : Nat) (hq : 4≤q) (R : Nat → Prop)
    (hg : LuRazClosure.Generated q R) (hc : Core234 R) : Generated q R := by
  obtain ⟨l,hn,hv,hR⟩ := hg
  have no1 : ∀ i∈l, ¬Row q i 1 := fun i hi h => hc.1 ((hR 1).mp ⟨i,hi,h⟩)
  obtain ⟨j,hj,hj4⟩ := (hR 4).mpr hc.2.2.2
  have hjN := no_one_four_row q j hq (hv j hj) (no1 j hj) hj4
  refine ⟨l,hn,hv,?_⟩
  intro e
  constructor
  · rintro ⟨i,hi,hie⟩
    rcases (no_one_flip q i e hq (no1 i hi)).mp hie with h | h
    · exact (hR e).mp ⟨i,hi,h.1⟩
    · rw [h.2]; exact hc.2.2.2
  · intro he
    by_cases he2 : e=2
    · subst e; exact ⟨j,hj,hjN.2.1⟩
    · obtain ⟨i,hi,hie⟩ := (hR e).mpr he
      exact ⟨i,hi,(no_one_flip q i e hq (no1 i hi)).mpr (Or.inl ⟨hie,by omega⟩)⟩

def Four (q : Nat) (z : NF23) (e : Nat) : Prop := e=4 ∨ z.eval q e

def Extra234 (q : Nat) : NF23 → Prop
  | .lp t p => P q t ∧ t≤2*q ∧ p=2*q+1
  | .creg t => P q t ∧ t≤2*q ∧ t≠q+3
  | _ => False

theorem extra234_old_valid (q : Nat) (hq : 4≤q) (z : NF23) (hz : Extra234 q z) : z.Valid q := by
  cases z <;> simp only [Extra234] at hz
  case lp t p =>
    simp only [NF23.Valid]
    refine ⟨hz.1,?_,?_⟩
    · unfold P; omega
    · omega
  case creg t => exact ⟨hz.1,hz.2.2⟩
  all_goals exact False.elim hz

theorem extra234_generated (q : Nat) (hq : 4≤q) (z : NF23) (hz : Extra234 q z) :
    Generated q (Four q z) := by
  have hl := generated_congr q (generated_row q (4*q-1) (by omega)) (fun e => last_source q e hq)
  cases z <;> simp only [Extra234] at hz
  case lp t p =>
    have hlt := generated_l q t t hq hz.1 hz.1 (by omega) hz.2.1
    apply generated_congr q (generated_join q hl hlt)
    intro e
    have hp := hz.1
    unfold P at hp
    simp only [Four,NF23.eval,LPrime,LRow,LNormal,I,beta]
    repeat first | (simp_all <;> omega) | split
  case creg t =>
    have hlt := generated_l q t t hq hz.1 hz.1 (by omega) hz.2.1
    apply generated_congr q (generated_join q (generated_join q hl hlt) (generated_c q hq))
    intro e
    have hp := hz.1
    unfold P at hp
    simp only [Four,NF23.eval,LPrime,LRow,LNormal,CRow,I,beta]
    repeat first | (simp_all <;> omega) | split
  all_goals exact False.elim hz

theorem extra234_core (q : Nat) (hq : 4≤q) (z : NF23) (hz : Extra234 q z) : Core234 (Four q z) := by
  have hc := NF23.core q hq z (extra234_old_valid q hq z hz)
  unfold Core234 Core23 Four at *
  simp_all

theorem extra234_no_mid (q : Nat) (hq : 4≤q) (z : NF23) (hz : Extra234 q z) :
    ¬Four q z (2*q+3) := by
  cases z <;> simp only [Extra234] at hz
  case lp t p =>
    simp only [Four,NF23.eval,LRow,LNormal,I,beta]
    unfold P at hz
    repeat first | (simp_all <;> omega) | split
  case creg t =>
    simp only [Four,NF23.eval,I,beta]
    unfold P at hz
    repeat first | (simp_all <;> omega) | split
  all_goals exact False.elim hz

theorem old234_mid (q : Nat) (hq : 4≤q) (R : Nat → Prop)
    (hg : LuRazClosure.Generated q R) (hc : Core234 R) : R (2*q+3) := by
  obtain ⟨l,_,hv,hR⟩ := hg
  obtain ⟨i,hi,h4⟩ := (hR 4).mpr hc.2.2.2
  have no1 : ¬Row q i 1 := fun h => hc.1 ((hR 1).mp ⟨i,hi,h⟩)
  exact (hR _).mp ⟨i,hi,(no_one_four_row q i hq (hv i hi) no1 h4).2.2.2⟩

theorem normal23_containing_last (q : Nat) (hq : 4≤q) (z : NF23) (hz : z.Valid q)
    (hh : z.eval q (2*q)) (hh1 : z.eval q (2*q+1)) (hn : z.eval q (4*q))
    (h2 : z.eval q (2*q+3) ∨ z.eval q (4*q-1)) : z=NF23.full ∨ Extra234 q z := by
  cases z with
  | lp t p =>
    right
    simp only [NF23.Valid,P] at hz
    simp only [NF23.eval,LRow,LNormal,I,beta] at hh hh1 hn h2
    simp only [Extra234,P]
    by_cases hb : t≤q+1 <;> by_cases hx : t=q+3 ∧ p=q+3
    all_goals simp_all <;> omega
  | filledM =>
    simp only [NF23.eval,I] at hh1
    omega
  | dgap p =>
    simp only [NF23.Valid,P] at hz
    simp only [NF23.eval,I] at hh
    omega
  | full => exact Or.inl rfl
  | creg t =>
    right
    simp only [NF23.Valid,P] at hz
    simp only [NF23.eval,I,beta] at h2
    simp only [Extra234,P]
    repeat first | (simp_all <;> omega) | split at h2
  | cexception =>
    simp only [NF23.eval,I] at hn
    omega

theorem four_full_old (q : Nat) (hq : 4≤q) : LuRazClosure.Generated q (Four q .full) := by
  have hp : P q (2*q+1) := by unfold P; omega
  apply LuRazClosure.generated_congr q (NF234.generated q hq (.kr (2*q+1) 0) ⟨hp,by decide⟩)
  intro e
  simp only [NF234.eval,T234,Four,NF23.eval,I]
  omega

theorem core234_exact (q : Nat) (hq : 4≤q) (R : Nat → Prop) :
    Generated q R ∧ Core234 R ↔
      (LuRazClosure.Generated q R ∧ Core234 R) ∨
      ∃ z : NF23, Extra234 q z ∧ ∀ e, R e ↔ Four q z e := by
  constructor
  · intro h
    obtain ⟨T,hT,ht1,hout,hT2,hT4,hlast,hhorn⟩ := no_one_shadow q hq R h.1 h.2.1
    by_cases ht4 : T 4
    · left
      refine ⟨LuRazClosure.generated_congr q hT ?_,h.2⟩
      intro e
      by_cases he2 : e=2
      · subst e; exact iff_of_true (hT2 h.2.2.1) h.2.2.1
      by_cases he4 : e=4
      · subst e; exact iff_of_true ht4 h.2.2.2.2
      exact (hout e he2 he4).symm
    · have htc : Core23 T := ⟨ht1,hT2 h.2.2.1,
        (hout 3 (by decide) (by decide)).mp h.2.2.2.1,ht4⟩
      have hl := hlast ht4 h.2.2.2.2
      have hm (e : Nat) (he : e=2*q ∨ e=2*q+1 ∨ e=4*q) : T e := by
        apply hl e
        rw [row_case_12 q (4*q-1) e (by omega) (by omega)]
        omega
      obtain ⟨z,hz,he⟩ := (core23_closure_exact q hq T).mp ⟨hT,htc⟩
      have hz2 := hhorn h.2.2.1
      rw [hout _ (by omega) (by omega),hout _ (by omega) (by omega),he _,he _] at hz2
      have hzc := normal23_containing_last q hq z hz ((he _).mp (hm _ (by omega)))
        ((he _).mp (hm _ (by omega))) ((he _).mp (hm _ (by omega))) hz2
      have hRz : ∀ e, R e ↔ Four q z e := by
        intro e
        unfold Four
        by_cases he2 : e=2
        · subst e
          have ht2 := (he 2).mp htc.2.1
          simp [h.2.2.1,ht2]
        by_cases he4 : e=4
        · subst e; simp [h.2.2.2.2]
        rw [hout e he2 he4,he e]
        simp [he4]
      rcases hzc with rfl | hextra
      · left
        exact ⟨LuRazClosure.generated_congr q (four_full_old q hq) (fun e => (hRz e).symm),h.2⟩
      · exact Or.inr ⟨z,hextra,hRz⟩
  · rintro (h | ⟨z,hz,he⟩)
    · exact ⟨old234_in_new q hq R h.1 h.2,h.2⟩
    · refine ⟨generated_congr q (extra234_generated q hq z hz) (fun e => (he e).symm),?_⟩
      have hc := extra234_core q hq z hz
      unfold Core234 at *
      rw [he 1,he 2,he 3,he 4]
      exact hc

end LuRazThreeRow
