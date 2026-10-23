import LuRazCore123
namespace LuRazClosure
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

inductive NF123 where
  | low (t : Nat) | high (t p : Nat) | filled | dg (p : Nat) | full
  | creg (t : Nat) | cex | er (p : Nat) | ed (p : Nat)
  deriving DecidableEq, Repr

def NF123.Valid (q : Nat) : NF123 → Prop
  | .low t => 4≤t ∧ t≤q+1
  | .high t p => P q t ∧ P q p ∧ q+3≤p ∧ t≤p
  | .filled | .full | .cex => True
  | .dg p => q+2≤p ∧ p≤2*q-1
  | .creg t => P q t ∧ t≠q+3
  | .er p => 4≤p ∧ p≤2*q+1
  | .ed p => 4≤p ∧ p≤q+1

def NF123.body (q : Nat) : NF123 → Nat → Prop
  | .low t => TwoPiece (q+2) (beta q t) (4*q)
  | .high t p => LRow q t p
  | .filled => NF23.eval q .filledM
  | .dg p | .ed p => TwoPiece p (2*q+1) (4*q)
  | .full => NF23.eval q .full
  | .creg t => NF23.eval q (.creg t)
  | .cex => NF23.eval q .cexception
  | .er p => TwoPiece p (2*q+3) (4*q)
def NF123.eval (q : Nat) (z : NF123) (e : Nat) : Prop := e=1 ∨ z.body q e

theorem a_image123_normal (q : Nat) (hq : 4≤q) (z : NF23) (hz : z.Valid q) :
    ∃ w : NF123, w.Valid q ∧ ∀ e, Image123 q z True False e ↔ w.eval q e := by
  cases z with
  | lp t p =>
    have ht := hz.1
    have hp := hz.2.1
    have htp := hz.2.2
    have ht' := ht
    have hp' := hp
    unfold P at ht' hp'
    by_cases hl : p≤q+1
    · refine ⟨.low t,by change 4≤t ∧ t≤q+1; omega,?_⟩
      intro e
      simp only [Image123,NF123.eval,NF123.body,NF23.eval,ARow,LRow,LNormal,TwoPiece,I,beta,true_and,false_and,or_false]
      repeat first | (simp_all <;> omega) | split
    · refine ⟨.high t p,⟨ht,hp,by omega,htp⟩,?_⟩
      intro e
      simp only [Image123,NF123.eval,NF123.body,NF23.eval,ARow,LRow,LNormal,TwoPiece,I,beta,true_and,false_and,or_false]
      repeat first | (simp_all <;> omega) | split
  | filledM =>
    refine ⟨.filled,True.intro,?_⟩
    intro e
    simp only [Image123,NF123.eval,NF123.body,NF23.eval,ARow,I,true_and,false_and,or_false]
    omega
  | dgap p =>
    have hp : P q p ∧ p≤2*q-1 := hz
    refine ⟨.dg (max p (q+2)),by change q+2≤max p (q+2) ∧ max p (q+2)≤2*q-1; omega,?_⟩
    intro e
    simp only [Image123,NF123.eval,NF123.body,NF23.eval,ARow,TwoPiece,I,true_and,false_and,or_false]
    omega
  | full =>
    refine ⟨.full,True.intro,?_⟩
    intro e
    simp only [Image123,NF123.eval,NF123.body,NF23.eval,ARow,I,true_and,false_and,or_false]
    omega
  | creg t =>
    refine ⟨.creg t,hz,?_⟩
    intro e
    simp only [Image123,NF123.eval,NF123.body,NF23.eval,ARow,I,true_and,false_and,or_false]
    omega
  | cexception =>
    refine ⟨.cex,True.intro,?_⟩
    intro e
    simp only [Image123,NF123.eval,NF123.body,NF23.eval,ARow,I,true_and,false_and,or_false]
    omega

theorem e_image123_normal (q : Nat) (hq : 4≤q) (z : NF23) (hz : z.Valid q) (a : Prop) :
    ∃ w : NF123, w.Valid q ∧ ∀ e, Image123 q z a True e ↔ w.eval q e := by
  classical
  cases z with
  | lp t p =>
    have ht := hz.1
    have hp := hz.2.1
    have htp := hz.2.2
    have ht' := ht
    have hp' := hp
    unfold P at ht' hp'
    by_cases ha : a
    · refine ⟨.er (max p (q+2)),by change 4≤max p (q+2) ∧ max p (q+2)≤2*q+1; omega,?_⟩
      intro e
      simp only [Image123,NF123.eval,NF123.body,NF23.eval,ARow,ERow,LRow,LNormal,TwoPiece,I,beta,ha,true_and]
      repeat first | (simp_all <;> omega) | split
    · refine ⟨.er p,by change 4≤p ∧ p≤2*q+1; omega,?_⟩
      intro e
      simp only [Image123,NF123.eval,NF123.body,NF23.eval,ARow,ERow,LRow,LNormal,TwoPiece,I,beta,ha,true_and,false_and,false_or]
      repeat first | (simp_all <;> omega) | split
  | filledM =>
    refine ⟨.er (q+3),by change 4≤q+3 ∧ q+3≤2*q+1; omega,?_⟩
    intro e
    by_cases ha : a <;> simp only [Image123,NF123.eval,NF123.body,NF23.eval,ARow,ERow,TwoPiece,I,ha,true_and,false_and,false_or] <;> omega
  | dgap p =>
    have hp : P q p ∧ p≤2*q-1 := hz
    have hp' := hp.1
    unfold P at hp'
    by_cases ha : a
    · refine ⟨.dg (max p (q+2)),by change q+2≤max p (q+2) ∧ max p (q+2)≤2*q-1; omega,?_⟩
      intro e
      simp only [Image123,NF123.eval,NF123.body,NF23.eval,ARow,ERow,TwoPiece,I,ha,true_and]
      omega
    · by_cases hl : p≤q+1
      · refine ⟨.ed p,by change 4≤p ∧ p≤q+1; omega,?_⟩
        intro e
        simp only [Image123,NF123.eval,NF123.body,NF23.eval,ARow,ERow,TwoPiece,I,ha,true_and,false_and,false_or]
        omega
      · refine ⟨.dg p,by change q+2≤p ∧ p≤2*q-1; omega,?_⟩
        intro e
        simp only [Image123,NF123.eval,NF123.body,NF23.eval,ARow,ERow,TwoPiece,I,ha,true_and,false_and,false_or]
        omega
  | full =>
    refine ⟨.full,True.intro,?_⟩
    intro e
    by_cases ha : a <;> simp only [Image123,NF123.eval,NF123.body,NF23.eval,ARow,ERow,I,ha,true_and,false_and,false_or] <;> omega
  | creg t =>
    refine ⟨.full,True.intro,?_⟩
    intro e
    have hb := beta_bounds q t hq hz.1
    by_cases ha : a <;> simp only [Image123,NF123.eval,NF123.body,NF23.eval,ARow,ERow,I,ha,true_and,false_and,false_or] <;> omega
  | cexception =>
    refine ⟨.full,True.intro,?_⟩
    intro e
    by_cases ha : a <;> simp only [Image123,NF123.eval,NF123.body,NF23.eval,ARow,ERow,I,ha,true_and,false_and,false_or] <;> omega

theorem image123_normal (q : Nat) (hq : 4≤q) (z : NF23) (hz : z.Valid q) (a f : Prop) (hA : a∨f) :
    ∃ w : NF123, w.Valid q ∧ ∀ e, Image123 q z a f e ↔ w.eval q e := by
  classical
  by_cases hf : f
  · simpa only [hf] using e_image123_normal q hq z hz a
  · have ha : a := by rcases hA with h | h; exact h; exact False.elim (hf h)
    simpa only [ha,hf] using a_image123_normal q hq z hz
end LuRazClosure
