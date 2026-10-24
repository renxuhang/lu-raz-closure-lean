import SixRow7Parts
namespace LuRazSixRowClosure
open LuRazClosure LuRazParametric
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
def Keep7 (q : Nat) : NF123→Prop
  | .low _ | .filled | .full | .cex => True
  | .high _ p => p≤2*q
  | .creg t => t≤2*q
  | .er p => q+2≤p ∧ p≤2*q
  | .dg _ | .ed _ => False
inductive NF7 where
  | old (z : NF123) | creg (t : Nat) | cex | right (c : Nat) | rex | point
  deriving DecidableEq, Repr
def NF7.Valid (q : Nat) : NF7→Prop
  | .old z => z.Valid q ∧ Keep7 q z
  | .creg t => P q t ∧ t≤2*q ∧ t≠q+3
  | .cex | .rex | .point => True
  | .right c => 3*q+2≤c ∧ c≤4*q-1
def NF7.eval (q : Nat) : NF7→Nat→Prop
  | .old z => z.eval q
  | .creg t => fun e=>e=1 ∨ NF6.eval q (.creg t) e
  | .cex => fun e=>e=1 ∨ NF6.eval q .cex e
  | .right c => fun e=>e=1 ∨ e=2 ∨ e=3 ∨ I 5 (2*q+2) e ∨ I c (4*q) e
  | .rex => fun e=>e=1 ∨ e=2 ∨ e=3 ∨ I 5 (2*q+2) e ∨ I (3*q+2) (4*q-1) e
  | .point => fun e=>e=1 ∨ e=2 ∨ e=3 ∨ I 5 (2*q+1) e ∨ I (2*q+3) (4*q) e

theorem image7_normal (q : Nat) (hq : 4≤q) (z : NF6) (hz : z.Valid q)
    (a b c : Prop) (habc : a∨b∨c) :
    ∃w : NF7,w.Valid q ∧ ∀e,Image7 q z a b c e ↔ w.eval q e := by
  classical
  have hzb := hz
  simp only [NF6.Valid,P] at hzb
  cases z with
  | lp t p =>
    simp only [NF6.Valid,P] at hz hzb
    by_cases hc : c
    · by_cases htl : t≤q+1
      ·
        refine ⟨.old (.creg t),?_,?_⟩
        · simp only [NF7.Valid,Keep7,NF123.Valid,P,beta] <;>
            repeat first | omega | (simp_all <;> omega) | split
        · intro e
          by_cases ha0 : a <;> by_cases hb0 : b <;>
            simp only [Image7,NF7.eval,NF123.eval,NF123.body,NF6.eval,NF23.eval,ARow,Z7,H7,LRow,LNormal,TwoPiece,I,beta,ha0,hb0,hc,true_and,false_and,or_false,false_or] <;>
            repeat first | omega | (simp_all <;> omega) | split
      · by_cases hte : t=q+3
        · by_cases hpe : p=q+3
          · by_cases hb : b
            ·
              refine ⟨.right (3*q+2),?_,?_⟩
              · simp only [NF7.Valid,Keep7,NF123.Valid,P,beta] <;>
                  repeat first | omega | (simp_all <;> omega) | split
              · intro e
                by_cases ha0 : a <;> by_cases hb0 : b <;>
                  simp only [Image7,NF7.eval,NF123.eval,NF123.body,NF6.eval,NF23.eval,ARow,Z7,H7,LRow,LNormal,TwoPiece,I,beta,ha0,hb0,hc,true_and,false_and,or_false,false_or] <;>
                  repeat first | omega | (simp_all <;> omega) | split
            ·
              refine ⟨.rex,?_,?_⟩
              · simp only [NF7.Valid,Keep7,NF123.Valid,P,beta] <;>
                  repeat first | omega | (simp_all <;> omega) | split
              · intro e
                by_cases ha0 : a <;> by_cases hb0 : b <;>
                  simp only [Image7,NF7.eval,NF123.eval,NF123.body,NF6.eval,NF23.eval,ARow,Z7,H7,LRow,LNormal,TwoPiece,I,beta,ha0,hb0,hc,true_and,false_and,or_false,false_or] <;>
                  repeat first | omega | (simp_all <;> omega) | split
          ·
            refine ⟨.right (3*q+2),?_,?_⟩
            · simp only [NF7.Valid,Keep7,NF123.Valid,P,beta] <;>
                repeat first | omega | (simp_all <;> omega) | split
            · intro e
              by_cases ha0 : a <;> by_cases hb0 : b <;>
                simp only [Image7,NF7.eval,NF123.eval,NF123.body,NF6.eval,NF23.eval,ARow,Z7,H7,LRow,LNormal,TwoPiece,I,beta,ha0,hb0,hc,true_and,false_and,or_false,false_or] <;>
                repeat first | omega | (simp_all <;> omega) | split
        ·
          refine ⟨.right (beta q t),?_,?_⟩
          · simp only [NF7.Valid,Keep7,NF123.Valid,P,beta] <;>
              repeat first | omega | (simp_all <;> omega) | split
          · intro e
            by_cases ha0 : a <;> by_cases hb0 : b <;>
              simp only [Image7,NF7.eval,NF123.eval,NF123.body,NF6.eval,NF23.eval,ARow,Z7,H7,LRow,LNormal,TwoPiece,I,beta,ha0,hb0,hc,true_and,false_and,or_false,false_or] <;>
              repeat first | omega | (simp_all <;> omega) | split
    · by_cases hb : b
      ·
        refine ⟨.old (.high t (2*q)),?_,?_⟩
        · simp only [NF7.Valid,Keep7,NF123.Valid,P,beta] <;>
            repeat first | omega | (simp_all <;> omega) | split
        · intro e
          by_cases ha0 : a <;> by_cases hb0 : b <;>
            simp only [Image7,NF7.eval,NF123.eval,NF123.body,NF6.eval,NF23.eval,ARow,Z7,H7,LRow,LNormal,TwoPiece,I,beta,ha0,hb0,hc,true_and,false_and,or_false,false_or] <;>
            repeat first | omega | (simp_all <;> omega) | split
      · have ha : a := habc.elim id (fun h=>False.elim (h.elim hb hc))
        by_cases hpl : p≤q+1
        ·
          refine ⟨.old (.low t),?_,?_⟩
          · simp only [NF7.Valid,Keep7,NF123.Valid,P,beta] <;>
              repeat first | omega | (simp_all <;> omega) | split
          · intro e
            by_cases ha0 : a <;> by_cases hb0 : b <;>
              simp only [Image7,NF7.eval,NF123.eval,NF123.body,NF6.eval,NF23.eval,ARow,Z7,H7,LRow,LNormal,TwoPiece,I,beta,ha0,hb0,hc,true_and,false_and,or_false,false_or] <;>
              repeat first | omega | (simp_all <;> omega) | split
        ·
          refine ⟨.old (.high t p),?_,?_⟩
          · simp only [NF7.Valid,Keep7,NF123.Valid,P,beta] <;>
              repeat first | omega | (simp_all <;> omega) | split
          · intro e
            by_cases ha0 : a <;> by_cases hb0 : b <;>
              simp only [Image7,NF7.eval,NF123.eval,NF123.body,NF6.eval,NF23.eval,ARow,Z7,H7,LRow,LNormal,TwoPiece,I,beta,ha0,hb0,hc,true_and,false_and,or_false,false_or] <;>
              repeat first | omega | (simp_all <;> omega) | split
  | filled =>
    simp only [NF6.Valid,P] at hz hzb
    by_cases hc : c
    ·
      refine ⟨.right (3*q+2),?_,?_⟩
      · simp only [NF7.Valid,Keep7,NF123.Valid,P,beta] <;>
          repeat first | omega | (simp_all <;> omega) | split
      · intro e
        by_cases ha0 : a <;> by_cases hb0 : b <;>
          simp only [Image7,NF7.eval,NF123.eval,NF123.body,NF6.eval,NF23.eval,ARow,Z7,H7,LRow,LNormal,TwoPiece,I,beta,ha0,hb0,hc,true_and,false_and,or_false,false_or] <;>
          repeat first | omega | (simp_all <;> omega) | split
    · by_cases hb : b
      ·
        refine ⟨.old (.high (q+3) (2*q)),?_,?_⟩
        · simp only [NF7.Valid,Keep7,NF123.Valid,P,beta] <;>
            repeat first | omega | (simp_all <;> omega) | split
        · intro e
          by_cases ha0 : a <;> by_cases hb0 : b <;>
            simp only [Image7,NF7.eval,NF123.eval,NF123.body,NF6.eval,NF23.eval,ARow,Z7,H7,LRow,LNormal,TwoPiece,I,beta,ha0,hb0,hc,true_and,false_and,or_false,false_or] <;>
            repeat first | omega | (simp_all <;> omega) | split
      · have ha : a := habc.elim id (fun h=>False.elim (h.elim hb hc))
        refine ⟨.old .filled,?_,?_⟩
        · simp only [NF7.Valid,Keep7,NF123.Valid,P,beta] <;>
            repeat first | omega | (simp_all <;> omega) | split
        · intro e
          by_cases ha0 : a <;> by_cases hb0 : b <;>
            simp only [Image7,NF7.eval,NF123.eval,NF123.body,NF6.eval,NF23.eval,ARow,Z7,H7,LRow,LNormal,TwoPiece,I,beta,ha0,hb0,hc,true_and,false_and,or_false,false_or] <;>
            repeat first | omega | (simp_all <;> omega) | split
  | creg t =>
    simp only [NF6.Valid,P] at hz hzb
    by_cases hc : c
    ·
      refine ⟨.old (.creg t),?_,?_⟩
      · simp only [NF7.Valid,Keep7,NF123.Valid,P,beta] <;>
          repeat first | omega | (simp_all <;> omega) | split
      · intro e
        by_cases ha0 : a <;> by_cases hb0 : b <;>
          simp only [Image7,NF7.eval,NF123.eval,NF123.body,NF6.eval,NF23.eval,ARow,Z7,H7,LRow,LNormal,TwoPiece,I,beta,ha0,hb0,hc,true_and,false_and,or_false,false_or] <;>
          repeat first | omega | (simp_all <;> omega) | split
    ·
      refine ⟨.creg t,?_,?_⟩
      · simp only [NF7.Valid,Keep7,NF123.Valid,P,beta] <;>
          repeat first | omega | (simp_all <;> omega) | split
      · intro e
        by_cases ha0 : a <;> by_cases hb0 : b <;>
          simp only [Image7,NF7.eval,NF123.eval,NF123.body,NF6.eval,NF23.eval,ARow,Z7,H7,LRow,LNormal,TwoPiece,I,beta,ha0,hb0,hc,true_and,false_and,or_false,false_or] <;>
          repeat first | omega | (simp_all <;> omega) | split
  | cex =>
    simp only [NF6.Valid,P] at hz hzb
    by_cases hc : c
    · by_cases hb : b
      ·
        refine ⟨.old (.creg (q+1)),?_,?_⟩
        · simp only [NF7.Valid,Keep7,NF123.Valid,P,beta] <;>
            repeat first | omega | (simp_all <;> omega) | split
        · intro e
          by_cases ha0 : a <;> by_cases hb0 : b <;>
            simp only [Image7,NF7.eval,NF123.eval,NF123.body,NF6.eval,NF23.eval,ARow,Z7,H7,LRow,LNormal,TwoPiece,I,beta,ha0,hb0,hc,true_and,false_and,or_false,false_or] <;>
            repeat first | omega | (simp_all <;> omega) | split
      ·
        refine ⟨.old .cex,?_,?_⟩
        · simp only [NF7.Valid,Keep7,NF123.Valid,P,beta] <;>
            repeat first | omega | (simp_all <;> omega) | split
        · intro e
          by_cases ha0 : a <;> by_cases hb0 : b <;>
            simp only [Image7,NF7.eval,NF123.eval,NF123.body,NF6.eval,NF23.eval,ARow,Z7,H7,LRow,LNormal,TwoPiece,I,beta,ha0,hb0,hc,true_and,false_and,or_false,false_or] <;>
            repeat first | omega | (simp_all <;> omega) | split
    · by_cases hb : b
      ·
        refine ⟨.creg (q+1),?_,?_⟩
        · simp only [NF7.Valid,Keep7,NF123.Valid,P,beta] <;>
            repeat first | omega | (simp_all <;> omega) | split
        · intro e
          by_cases ha0 : a <;> by_cases hb0 : b <;>
            simp only [Image7,NF7.eval,NF123.eval,NF123.body,NF6.eval,NF23.eval,ARow,Z7,H7,LRow,LNormal,TwoPiece,I,beta,ha0,hb0,hc,true_and,false_and,or_false,false_or] <;>
            repeat first | omega | (simp_all <;> omega) | split
      ·
        refine ⟨.cex,?_,?_⟩
        · simp only [NF7.Valid,Keep7,NF123.Valid,P,beta] <;>
            repeat first | omega | (simp_all <;> omega) | split
        · intro e
          by_cases ha0 : a <;> by_cases hb0 : b <;>
            simp only [Image7,NF7.eval,NF123.eval,NF123.body,NF6.eval,NF23.eval,ARow,Z7,H7,LRow,LNormal,TwoPiece,I,beta,ha0,hb0,hc,true_and,false_and,or_false,false_or] <;>
            repeat first | omega | (simp_all <;> omega) | split
  | er p =>
    simp only [NF6.Valid,P] at hz hzb
    by_cases hc : c
    ·
      refine ⟨.old .full,?_,?_⟩
      · simp only [NF7.Valid,Keep7,NF123.Valid,P,beta] <;>
          repeat first | omega | (simp_all <;> omega) | split
      · intro e
        by_cases ha0 : a <;> by_cases hb0 : b <;>
          simp only [Image7,NF7.eval,NF123.eval,NF123.body,NF6.eval,NF23.eval,ARow,Z7,H7,LRow,LNormal,TwoPiece,I,beta,ha0,hb0,hc,true_and,false_and,or_false,false_or] <;>
          repeat first | omega | (simp_all <;> omega) | split
    · by_cases hb : b
      · by_cases hph : p=2*q+1
        ·
          refine ⟨.point,?_,?_⟩
          · simp only [NF7.Valid,Keep7,NF123.Valid,P,beta] <;>
              repeat first | omega | (simp_all <;> omega) | split
          · intro e
            by_cases ha0 : a <;> by_cases hb0 : b <;>
              simp only [Image7,NF7.eval,NF123.eval,NF123.body,NF6.eval,NF23.eval,ARow,Z7,H7,LRow,LNormal,TwoPiece,I,beta,ha0,hb0,hc,true_and,false_and,or_false,false_or] <;>
              repeat first | omega | (simp_all <;> omega) | split
        ·
          refine ⟨.old (.er (2*q)),?_,?_⟩
          · simp only [NF7.Valid,Keep7,NF123.Valid,P,beta] <;>
              repeat first | omega | (simp_all <;> omega) | split
          · intro e
            by_cases ha0 : a <;> by_cases hb0 : b <;>
              simp only [Image7,NF7.eval,NF123.eval,NF123.body,NF6.eval,NF23.eval,ARow,Z7,H7,LRow,LNormal,TwoPiece,I,beta,ha0,hb0,hc,true_and,false_and,or_false,false_or] <;>
              repeat first | omega | (simp_all <;> omega) | split
      · have ha : a := habc.elim id (fun h=>False.elim (h.elim hb hc))
        by_cases hph : p=2*q+1
        ·
          refine ⟨.point,?_,?_⟩
          · simp only [NF7.Valid,Keep7,NF123.Valid,P,beta] <;>
              repeat first | omega | (simp_all <;> omega) | split
          · intro e
            by_cases ha0 : a <;> by_cases hb0 : b <;>
              simp only [Image7,NF7.eval,NF123.eval,NF123.body,NF6.eval,NF23.eval,ARow,Z7,H7,LRow,LNormal,TwoPiece,I,beta,ha0,hb0,hc,true_and,false_and,or_false,false_or] <;>
              repeat first | omega | (simp_all <;> omega) | split
        · by_cases hpl : p≤q+1
          ·
            refine ⟨.old (.er (q+2)),?_,?_⟩
            · simp only [NF7.Valid,Keep7,NF123.Valid,P,beta] <;>
                repeat first | omega | (simp_all <;> omega) | split
            · intro e
              by_cases ha0 : a <;> by_cases hb0 : b <;>
                simp only [Image7,NF7.eval,NF123.eval,NF123.body,NF6.eval,NF23.eval,ARow,Z7,H7,LRow,LNormal,TwoPiece,I,beta,ha0,hb0,hc,true_and,false_and,or_false,false_or] <;>
                repeat first | omega | (simp_all <;> omega) | split
          ·
            refine ⟨.old (.er p),?_,?_⟩
            · simp only [NF7.Valid,Keep7,NF123.Valid,P,beta] <;>
                repeat first | omega | (simp_all <;> omega) | split
            · intro e
              by_cases ha0 : a <;> by_cases hb0 : b <;>
                simp only [Image7,NF7.eval,NF123.eval,NF123.body,NF6.eval,NF23.eval,ARow,Z7,H7,LRow,LNormal,TwoPiece,I,beta,ha0,hb0,hc,true_and,false_and,or_false,false_or] <;>
                repeat first | omega | (simp_all <;> omega) | split

theorem core7_normal (q : Nat) (hq : 4≤q) (R : Nat→Prop)
    (hg : Generated q R) (hc : Core123 R) : ∃z : NF7,z.Valid q ∧ ∀e,R e ↔ z.eval q e := by
  obtain ⟨z,hz,a,b,c,hf,he⟩ := core7_image q hq R hg hc
  obtain ⟨w,hw,hn⟩ := image7_normal q hq z hz a b c hf
  exact ⟨w,hw,fun e=>(he e).trans (hn e)⟩
end LuRazSixRowClosure
