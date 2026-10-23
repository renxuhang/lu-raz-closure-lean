import LuRazSmallResults
namespace LuRazClosure
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

def K1Row (q e : Nat) : Prop := e=2 ∨ e=4 ∨ I (2*q+2) (4*q-2) e
def K2Row (q e : Nat) : Prop := e=2 ∨ e=4 ∨ I (2*q+3) (4*q-1) e
def Core24 (R : Nat → Prop) : Prop := ¬R 1 ∧ R 2 ∧ ¬R 3 ∧ R 4
def Fixed24 (q i : Nat) : Prop := i=2*q+1 ∨ i=2*q+2 ∨ i=1 ∨ i=4*q+1
def Mix24 (q : Nat) (u v d b : Prop) (e : Nat) : Prop :=
  (u ∧ K1Row q e) ∨ (v ∧ K2Row q e) ∨ (d ∧ DRow q e) ∨ (b ∧ BRow q e)

theorem K1_source (q e : Nat) (hq : 4≤q) : LuRazParametric.Row q (2*q+1) e ↔ K1Row q e := by
  rw [LuRazParametric.row_case_7 q (2*q+1) e (by omega) rfl]
  unfold K1Row I
  omega

theorem K2_source (q e : Nat) (hq : 4≤q) : LuRazParametric.Row q (2*q+2) e ↔ K2Row q e := by
  rw [LuRazParametric.row_case_8 q (2*q+2) e (by omega) rfl]
  unfold K2Row I
  omega

theorem generated_K1 (q : Nat) (hq : 4≤q) : Generated q (K1Row q) :=
  generated_congr q (generated_row q (2*q+1) (by omega)) (fun e => K1_source q e hq)

theorem generated_K2 (q : Nat) (hq : 4≤q) : Generated q (K2Row q) :=
  generated_congr q (generated_row q (2*q+2) (by omega)) (fun e => K2_source q e hq)

theorem row_fixed24 (q i : Nat) (hq : 4≤q) (hi : i≤4*q+2)
    (h1 : ¬LuRazParametric.Row q i 1) (h3 : ¬LuRazParametric.Row q i 3) : Fixed24 q i := by
  have hc : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨
      (5≤i ∧ i≤q+2) ∨ (q+3≤i ∧ i≤2*q) ∨ i=2*q+1 ∨ i=2*q+2 ∨ i=2*q+3 ∨
      (2*q+4≤i ∧ i≤3*q) ∨ i=3*q+1 ∨ (3*q+2≤i ∧ i+1≤4*q) ∨
      i=4*q ∨ i=4*q+1 ∨ i=4*q+2 := by omega
  rcases hc with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact False.elim (h1 ((LuRazParametric.row_case_0 q i 1 (by omega) h).mpr (by omega)))
  · exact Or.inr (Or.inr (Or.inl h))
  · exact False.elim (h1 ((LuRazParametric.row_case_2 q i 1 (by omega) h).mpr (by omega)))
  · exact False.elim (h1 ((LuRazParametric.row_case_3 q i 1 (by omega) h).mpr (by omega)))
  · exact False.elim (h1 ((LuRazParametric.row_case_4 q i 1 (by omega) h).mpr (by omega)))
  · exact False.elim (h1 ((LuRazParametric.row_case_5 q i 1 (by omega) h).mpr (by omega)))
  · exact False.elim (h1 ((LuRazParametric.row_case_6 q i 1 (by omega) h).mpr (by omega)))
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact False.elim (h3 ((LuRazParametric.row_case_9 q i 3 (by omega) h).mpr (by omega)))
  · exact False.elim (h3 ((LuRazParametric.row_case_10 q i 3 (by omega) h).mpr (by omega)))
  · exact False.elim (h3 ((LuRazParametric.row_case_11 q i 3 (by omega) h).mpr (by omega)))
  · exact False.elim (h3 ((LuRazParametric.row_case_12 q i 3 (by omega) h).mpr (by omega)))
  · exact False.elim (h3 ((LuRazParametric.row_case_13 q i 3 (by omega) h).mpr (by omega)))
  · exact Or.inr (Or.inr (Or.inr h))
  · exact False.elim (h1 ((LuRazParametric.row_case_15 q i 1 (by omega) h).mpr (by omega)))

theorem core24_mix (q : Nat) (hq : 4≤q) (R : Nat → Prop) (hg : Generated q R) (hc : Core24 R) :
    ∃ u v d b : Prop, (u ∨ v) ∧ ∀ e, R e ↔ Mix24 q u v d b e := by
  obtain ⟨l,_,hvalid,hR⟩ := hg
  have hi : ∀ i∈l, Fixed24 q i := by
    intro i him
    apply row_fixed24 q i hq (hvalid i him)
    · intro h; exact hc.1 ((hR 1).mp ⟨i,him,h⟩)
    · intro h; exact hc.2.2.1 ((hR 3).mp ⟨i,him,h⟩)
  have hm : ∀ e, R e ↔ Mix24 q (2*q+1∈l) (2*q+2∈l) (1∈l) (4*q+1∈l) e := by
    intro e
    constructor
    · intro he
      obtain ⟨i,him,hie⟩ := (hR e).mpr he
      rcases hi i him with h | h | h | h <;> subst i
      · exact Or.inl ⟨him,(K1_source q e hq).mp hie⟩
      · exact Or.inr (Or.inl ⟨him,(K2_source q e hq).mp hie⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨him,(D_source q e hq).mp hie⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨him,(B_source q e hq).mp hie⟩))
    · intro he
      apply (hR e).mp
      rcases he with h | h | h | h
      · exact ⟨2*q+1,h.1,(K1_source q e hq).mpr h.2⟩
      · exact ⟨2*q+2,h.1,(K2_source q e hq).mpr h.2⟩
      · exact ⟨1,h.1,(D_source q e hq).mpr h.2⟩
      · exact ⟨4*q+1,h.1,(B_source q e hq).mpr h.2⟩
  refine ⟨2*q+1∈l,2*q+2∈l,1∈l,4*q+1∈l,?_,hm⟩
  have h4 := (hm 4).mp hc.2.2.2
  rcases h4 with h | h | h | h
  · exact Or.inl h.1
  · exact Or.inr h.1
  · have hh := h.2; unfold DRow I at hh; omega
  · have hh := h.2; unfold BRow I at hh; omega

inductive NF24 where
  | k1 | k2 | joinK | fill1 | fill2 | dBig
  deriving DecidableEq, Repr

def NF24.eval (q : Nat) : NF24 → Nat → Prop
  | .k1 => K1Row q
  | .k2 => K2Row q
  | .joinK => fun e => K1Row q e ∨ K2Row q e
  | .fill1 => fun e => K1Row q e ∨ BRow q e
  | .fill2 => fun e => K2Row q e ∨ BRow q e
  | .dBig => fun e => K1Row q e ∨ DRow q e

theorem mix24_normal (q : Nat) (hq : 4≤q) (u v d b : Prop) (huv : u ∨ v) :
    ∃ z : NF24, ∀ e, Mix24 q u v d b e ↔ z.eval q e := by
  classical
  by_cases hd : d
  · rcases huv with hu | hv
    · refine ⟨.dBig,?_⟩
      intro e
      simp only [Mix24,NF24.eval,hd,hu,true_and,false_and,false_or,or_false] <;>
        (simp only [K1Row,K2Row,DRow,BRow,I] <;> omega)
    · refine ⟨.dBig,?_⟩
      intro e
      simp only [Mix24,NF24.eval,hd,hv,true_and,false_and,false_or,or_false] <;>
        (simp only [K1Row,K2Row,DRow,BRow,I] <;> omega)
  · by_cases hu : u
    · by_cases hv : v
      · by_cases hb : b
        · refine ⟨.fill1,?_⟩
          intro e
          simp only [Mix24,NF24.eval,hd,hu,hv,hb,true_and,false_and,false_or,or_false] <;>
            (simp only [K1Row,K2Row,DRow,BRow,I] <;> omega)
        · refine ⟨.joinK,?_⟩
          intro e
          simp only [Mix24,NF24.eval,hd,hu,hv,hb,true_and,false_and,false_or,or_false] <;>
            (simp only [K1Row,K2Row,DRow,BRow,I] <;> omega)
      · by_cases hb : b
        · refine ⟨.fill1,?_⟩
          intro e
          simp only [Mix24,NF24.eval,hd,hu,hv,hb,true_and,false_and,false_or,or_false] <;>
            (simp only [K1Row,K2Row,DRow,BRow,I] <;> omega)
        · refine ⟨.k1,?_⟩
          intro e
          simp only [Mix24,NF24.eval,hd,hu,hv,hb,true_and,false_and,false_or,or_false] <;>
            (simp only [K1Row,K2Row,DRow,BRow,I] <;> omega)
    · have hv : v := by rcases huv with h | h; exact False.elim (hu h); exact h
      by_cases hb : b
      · refine ⟨.fill2,?_⟩
        intro e
        simp only [Mix24,NF24.eval,hd,hu,hv,hb,true_and,false_and,false_or,or_false] <;>
          (simp only [K1Row,K2Row,DRow,BRow,I] <;> omega)
      · refine ⟨.k2,?_⟩
        intro e
        simp only [Mix24,NF24.eval,hd,hu,hv,hb,true_and,false_and,false_or,or_false] <;>
          (simp only [K1Row,K2Row,DRow,BRow,I] <;> omega)

theorem NF24.generated (q : Nat) (hq : 4≤q) (z : NF24) : Generated q (z.eval q) := by
  cases z with
  | k1 => exact generated_K1 q hq
  | k2 => exact generated_K2 q hq
  | joinK => exact generated_join q (generated_K1 q hq) (generated_K2 q hq)
  | fill1 => exact generated_join q (generated_K1 q hq) (generated_B q hq)
  | fill2 => exact generated_join q (generated_K2 q hq) (generated_B q hq)
  | dBig => exact generated_join q (generated_K1 q hq) (generated_D q hq)

theorem NF24.core (q : Nat) (hq : 4≤q) (z : NF24) : Core24 (z.eval q) := by
  cases z <;> simp only [Core24,NF24.eval,K1Row,K2Row,DRow,BRow,I] <;> (simp_all <;> omega)

theorem core24_closure_exact (q : Nat) (hq : 4≤q) (R : Nat → Prop) :
    (Generated q R ∧ Core24 R) ↔ ∃ z : NF24, ∀ e, R e ↔ z.eval q e := by
  constructor
  · rintro ⟨hg,hc⟩
    obtain ⟨u,v,d,b,huv,heq⟩ := core24_mix q hq R hg hc
    obtain ⟨z,hz⟩ := mix24_normal q hq u v d b huv
    exact ⟨z,fun e => (heq e).trans (hz e)⟩
  · rintro ⟨z,heq⟩
    have hc := NF24.core q hq z
    exact ⟨generated_congr q (NF24.generated q hq z) (fun e => (heq e).symm),
      fun h => hc.1 ((heq 1).mp h),(heq 2).mpr hc.2.1,
      fun h => hc.2.2.1 ((heq 3).mp h),(heq 4).mpr hc.2.2.2⟩

end LuRazClosure
