import Exhaustive123Rows
namespace LuRazThreeRow
open LuRazClosure LuRazParametric
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

def Cut123 (q : Nat) : NF123 → Prop
  | .high _ p | .er p => p≤2*q
  | .creg t => t≤2*q
  | _ => True
def Valid123 (q : Nat) (z : NF123) : Prop := z.Valid q ∧ Cut123 q z

theorem retained123_conditions (q : Nat) (hq : 4≤q) (z : NF123) (hz : z.Valid q) :
    Cut123 q z ↔ z.eval q (4*q-1) ∧ (z.eval q (2*q+1) → z.eval q (2*q+2)) := by
  cases z <;> simp only [NF123.Valid,P] at hz <;>
    simp only [Cut123,NF123.eval,NF123.body,NF23.eval,LRow,LNormal,TwoPiece,I,beta] <;>
    repeat first | (simp_all <;> omega) | split

theorem image123_short (q : Nat) (hq : 4≤q) (z : NF23) (hz : z.Valid q)
    (hcut : Avoid23 q z) (a f : Prop) : Generated q (Image123 q z a f) := by
  have hg := normal23_generated q hq z ⟨hz,hcut⟩
  have hA := generated_congr q (generated_row q (4*q+2) (by omega)) (fun e => a_source q e hq)
  have hE := generated_congr q (generated_join q
    (generated_congr q (generated_row q 4 (by omega)) (fun e => e_source q e hq))
    (generated_b q hq)) (show ∀ e, (EPrime q e ∨ BRow q e) ↔ (ERow q e ∨ e=2) from by
      intro e; unfold EPrime BRow ERow I; omega)
  apply generated_congr q (generated_optional q (generated_optional q hg hA a) hE f)
  intro e
  have h2 := (NF23.core q hq z hz).2.1
  unfold Image123
  by_cases he : e=2
  · subst e; simp [h2]
  · simp only [he,or_false]
    exact or_assoc

theorem retained123_generated (q : Nat) (hq : 4≤q) (z : NF123) (hhz : Valid123 q z) : Generated q (z.eval q) := by
  have hz := hhz.1
  have hcut := hhz.2
  have hp4 : P q 4 := by unfold P; omega
  cases z with
  | low t =>
    have htBounds : 4≤t ∧ t≤q+1 := hz
    have ht : P q t := by have hb : 4≤t ∧ t≤q+1 := hz; unfold P; omega
    have hg := image123_short q hq (.lp t t) (⟨ht,ht,by omega⟩) (by change t≤2*q; omega) True False
    apply generated_congr q hg
    intro e
    simp only [Image123,NF123.eval,NF123.body,NF23.eval,ARow,ERow,TwoPiece,LRow,LNormal,I,beta,true_and,false_and,false_or,or_false]
    repeat first | omega | (simp_all <;> omega) | split
  | high t p =>
    have hb : P q t ∧ P q p ∧ q+3≤p ∧ t≤p := hz
    have hp := hb.2.1
    have hp' := hp
    unfold P at hp'
    have hg := image123_short q hq (.lp t p) (⟨hb.1,hp,hb.2.2.2⟩) hcut True False
    apply generated_congr q hg
    intro e
    simp only [Image123,NF123.eval,NF123.body,NF23.eval,ARow,ERow,TwoPiece,LRow,LNormal,I,beta,true_and,false_and,false_or,or_false]
    repeat first | omega | (simp_all <;> omega) | split
  | filled =>
    have hg := image123_short q hq (.filledM) (True.intro) True.intro True False
    apply generated_congr q hg
    intro e
    simp only [Image123,NF123.eval,NF123.body,NF23.eval,ARow,ERow,TwoPiece,LRow,LNormal,I,beta,true_and,false_and,false_or,or_false]
    repeat first | omega | (simp_all <;> omega) | split
  | full =>
    have hg := image123_short q hq (.full) (True.intro) True.intro True False
    apply generated_congr q hg
    intro e
    simp only [Image123,NF123.eval,NF123.body,NF23.eval,ARow,ERow,TwoPiece,LRow,LNormal,I,beta,true_and,false_and,false_or,or_false]
    repeat first | omega | (simp_all <;> omega) | split
  | creg t =>
    have hg := image123_short q hq (.creg t) (hz) hcut True False
    apply generated_congr q hg
    intro e
    simp only [Image123,NF123.eval,NF123.body,NF23.eval,ARow,ERow,TwoPiece,LRow,LNormal,I,beta,true_and,false_and,false_or,or_false]
    repeat first | omega | (simp_all <;> omega) | split
  | cex =>
    have hg := image123_short q hq (.cexception) (True.intro) True.intro True False
    apply generated_congr q hg
    intro e
    simp only [Image123,NF123.eval,NF123.body,NF23.eval,ARow,ERow,TwoPiece,LRow,LNormal,I,beta,true_and,false_and,false_or,or_false]
    repeat first | omega | (simp_all <;> omega) | split
  | dg p =>
    have hb : q+2≤p ∧ p≤2*q-1 := hz
    by_cases he : p=q+2
    · have hg := image123_short q hq (.dgap 4) ⟨hp4,by omega⟩ True.intro True False
      apply generated_congr q hg
      intro e
      simp only [Image123,NF123.eval,NF123.body,NF23.eval,ARow,TwoPiece,I,true_and,false_and,or_false]
      omega
    · have hp : P q p := by unfold P; omega
      have hg := image123_short q hq (.dgap p) ⟨hp,hb.2⟩ True.intro True False
      apply generated_congr q hg
      intro e
      simp only [Image123,NF123.eval,NF123.body,NF23.eval,ARow,TwoPiece,I,true_and,false_and,or_false]
      omega
  | er p =>
    have hb : 4≤p ∧ p≤2*q+1 := hz
    by_cases he : p=q+2
    · have hg := image123_short q hq (.lp 4 4) ⟨hp4,hp4,by omega⟩ (by change 4≤2*q; omega) True True
      apply generated_congr q hg
      intro e
      simp only [Image123,NF123.eval,NF123.body,NF23.eval,ARow,ERow,TwoPiece,LRow,LNormal,I,beta,true_and]
      repeat first | omega | (simp_all <;> omega) | split
    · have hp : P q p := by unfold P; omega
      have hg := image123_short q hq (.lp p p) ⟨hp,hp,by omega⟩ hcut False True
      apply generated_congr q hg
      intro e
      simp only [Image123,NF123.eval,NF123.body,NF23.eval,ARow,ERow,TwoPiece,LRow,LNormal,I,beta,true_and,false_and,false_or]
      repeat first | omega | (simp_all <;> omega) | split
  | ed p =>
    have hb : 4≤p ∧ p≤q+1 := hz
    have hp : P q p := by unfold P; omega
    have hg := image123_short q hq (.dgap p) ⟨hp,by omega⟩ True.intro False True
    apply generated_congr q hg
    intro e
    simp only [Image123,NF123.eval,NF123.body,NF23.eval,ARow,ERow,TwoPiece,I,true_and,false_and,false_or]
    omega

theorem core123_exhaustive (q : Nat) (hq : 4≤q) (R : Nat → Prop) :
    Generated q R ∧ Core123 R ↔
      (∃ z : NF123, Valid123 q z ∧ ∀ e, R e ↔ z.eval q e) ∨
      (∃ z : Fresh123, ∀ e, R e ↔ z.eval q e) := by
  classical
  constructor
  · intro h
    by_cases hn : R (4*q-1)
    · have ho := core123_old_if_last q hq R h.1 h.2 hn
      obtain ⟨z,hz,he⟩ := (core123_closure_exact q hq R).mp ⟨ho,h.2⟩
      have hmid := no4_mid q hq R h.1 h.2.2.2.2
      have hzcond : z.eval q (4*q-1) ∧ (z.eval q (2*q+1) → z.eval q (2*q+2)) :=
        ⟨(he _).mp hn,fun hh => (he _).mp (hmid ((he _).mpr hh))⟩
      exact Or.inl ⟨z,⟨hz,(retained123_conditions q hq z hz).mpr hzcond⟩,he⟩
    · exact Or.inr (core123_no_last q hq R h.1 h.2 hn)
  · rintro (⟨z,hz,he⟩ | ⟨z,he⟩)
    · refine ⟨generated_congr q (retained123_generated q hq z hz) (fun e => (he e).symm),?_⟩
      have hc := NF123.core q hq z hz.1
      unfold Core123 at *
      rw [he 1,he 2,he 3,he 4]
      exact hc
    · refine ⟨generated_congr q (fresh123_generated q hq z) (fun e => (he e).symm),?_⟩
      have hc := fresh123_core q hq z
      unfold Core123 at *
      rw [he 1,he 2,he 3,he 4]
      exact hc

theorem retained_fresh123_disjoint (q : Nat) (hq : 4≤q) (z : NF123) (hz : Valid123 q z)
    (w : Fresh123) : ¬(∀ e, z.eval q e ↔ w.eval q e) := by
  intro he
  exact fresh123_no_last q hq w ((he _).mp ((retained123_conditions q hq z hz.1).mp hz.2).1)

end LuRazThreeRow
