import LuRazTotalClosure
namespace LuRazClosure
namespace SourcePieces
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
def p24Domain (q a b : Nat) : Prop := (4)≤(a:Int) ∧ (a:Int)≤((1)*(q:Int)+1) ∧ (0:Int)≤(b:Int) ∧ (b:Int)≤(0:Int)
def p24NF (q a b : Nat) : NF123 := .low a
def p24Set (q a b e : Nat) : Prop := (e=1 ∨ e=2 ∨ e=3) ∨ (((5)≤(e:Int) ∧ (e:Int)≤((1)*(q:Int)+2)) ∨ (((2)*(q:Int)+(1)*(a:Int))≤(e:Int) ∧ (e:Int)≤((4)*(q:Int))))
theorem p24_valid (q a b : Nat) (hq : 4≤q) (hd : p24Domain q a b) : (p24NF q a b).Valid q := by
  simp only [p24Domain] at hd
  simp only [p24NF,NF123.Valid,P,JReachable,g]
  repeat first | omega | split
theorem p24_eval (q a b e : Nat) (hq : 4≤q) (hd : p24Domain q a b) :
    (p24NF q a b).eval q e ↔ p24Set q a b e := by
  simp only [p24Domain] at hd
  simp only [p24NF,p24Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p24_generated (q a b : Nat) (hq : 4≤q) (hd : p24Domain q a b) :
    Generated q (p24Set q a b) := by
  exact generated_congr q (NF123.generated q hq (p24NF q a b) (p24_valid q a b hq hd)) (p24_eval q a b · hq hd)
def p25Domain (q a b : Nat) : Prop := ((1)*(q:Int)+3)≤(a:Int) ∧ (a:Int)≤((2)*(q:Int)+1) ∧ (4)≤(b:Int) ∧ (b:Int)≤((1)*(q:Int)+1) ∧ (b:Int)≤(a:Int)+(0:Int)
def p25NF (q a b : Nat) : NF123 := .high b a
def p25Set (q a b e : Nat) : Prop := (e=1 ∨ e=2 ∨ e=3) ∨ ((((5)≤(e:Int) ∧ (e:Int)≤((1)*(a:Int))) ∨ (((2)*(q:Int)+(1)*(b:Int))≤(e:Int) ∧ (e:Int)≤((4)*(q:Int)))) ∧ ¬(a=q+3 ∧ b=q+3 ∧ e=4*q))
theorem p25_valid (q a b : Nat) (hq : 4≤q) (hd : p25Domain q a b) : (p25NF q a b).Valid q := by
  simp only [p25Domain] at hd
  simp only [p25NF,NF123.Valid,P,JReachable,g]
  repeat first | omega | split
theorem p25_eval (q a b e : Nat) (hq : 4≤q) (hd : p25Domain q a b) :
    (p25NF q a b).eval q e ↔ p25Set q a b e := by
  simp only [p25Domain] at hd
  simp only [p25NF,p25Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p25_generated (q a b : Nat) (hq : 4≤q) (hd : p25Domain q a b) :
    Generated q (p25Set q a b) := by
  exact generated_congr q (NF123.generated q hq (p25NF q a b) (p25_valid q a b hq hd)) (p25_eval q a b · hq hd)
def p26Domain (q a b : Nat) : Prop := ((1)*(q:Int)+3)≤(a:Int) ∧ (a:Int)≤((2)*(q:Int)+1) ∧ ((1)*(q:Int)+3)≤(b:Int) ∧ (b:Int)≤((2)*(q:Int)+1) ∧ (b:Int)≤(a:Int)+(0:Int)
def p26NF (q a b : Nat) : NF123 := .high b a
def p26Set (q a b e : Nat) : Prop := (e=1 ∨ e=2 ∨ e=3) ∨ ((((5)≤(e:Int) ∧ (e:Int)≤((1)*(a:Int))) ∨ (((2)*(q:Int)+(1)*(b:Int)+(-1))≤(e:Int) ∧ (e:Int)≤((4)*(q:Int)))) ∧ ¬(a=q+3 ∧ b=q+3 ∧ e=4*q))
theorem p26_valid (q a b : Nat) (hq : 4≤q) (hd : p26Domain q a b) : (p26NF q a b).Valid q := by
  simp only [p26Domain] at hd
  simp only [p26NF,NF123.Valid,P,JReachable,g]
  repeat first | omega | split
theorem p26_eval (q a b e : Nat) (hq : 4≤q) (hd : p26Domain q a b) :
    (p26NF q a b).eval q e ↔ p26Set q a b e := by
  simp only [p26Domain] at hd
  simp only [p26NF,p26Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p26_generated (q a b : Nat) (hq : 4≤q) (hd : p26Domain q a b) :
    Generated q (p26Set q a b) := by
  exact generated_congr q (NF123.generated q hq (p26NF q a b) (p26_valid q a b hq hd)) (p26_eval q a b · hq hd)
def p28Domain (q a b : Nat) : Prop := (0:Int)≤(a:Int) ∧ (a:Int)≤(0:Int) ∧ (0:Int)≤(b:Int) ∧ (b:Int)≤(0:Int)
def p28NF (q a b : Nat) : NF123 := .filled
def p28Set (q a b e : Nat) : Prop := (e=1 ∨ e=2 ∨ e=3) ∨ (((5)≤(e:Int) ∧ (e:Int)≤((1)*(q:Int)+3)) ∨ (((3)*(q:Int)+2)≤(e:Int) ∧ (e:Int)≤((4)*(q:Int))))
theorem p28_valid (q a b : Nat) (hq : 4≤q) (hd : p28Domain q a b) : (p28NF q a b).Valid q := by
  simp only [p28Domain] at hd
  simp only [p28NF,NF123.Valid,P,JReachable,g]
  repeat first | omega | split
theorem p28_eval (q a b e : Nat) (hq : 4≤q) (hd : p28Domain q a b) :
    (p28NF q a b).eval q e ↔ p28Set q a b e := by
  simp only [p28Domain] at hd
  simp only [p28NF,p28Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p28_generated (q a b : Nat) (hq : 4≤q) (hd : p28Domain q a b) :
    Generated q (p28Set q a b) := by
  exact generated_congr q (NF123.generated q hq (p28NF q a b) (p28_valid q a b hq hd)) (p28_eval q a b · hq hd)
def p29Domain (q a b : Nat) : Prop := (0:Int)≤(a:Int) ∧ (a:Int)≤(0:Int) ∧ (0:Int)≤(b:Int) ∧ (b:Int)≤(0:Int)
def p29NF (q a b : Nat) : NF123 := .dg (q+2)
def p29Set (q a b e : Nat) : Prop := (e=1 ∨ e=2 ∨ e=3) ∨ (((5)≤(e:Int) ∧ (e:Int)≤((1)*(q:Int)+2)) ∨ (((2)*(q:Int)+1)≤(e:Int) ∧ (e:Int)≤((4)*(q:Int))))
theorem p29_valid (q a b : Nat) (hq : 4≤q) (hd : p29Domain q a b) : (p29NF q a b).Valid q := by
  simp only [p29Domain] at hd
  simp only [p29NF,NF123.Valid,P,JReachable,g]
  repeat first | omega | split
theorem p29_eval (q a b e : Nat) (hq : 4≤q) (hd : p29Domain q a b) :
    (p29NF q a b).eval q e ↔ p29Set q a b e := by
  simp only [p29Domain] at hd
  simp only [p29NF,p29Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p29_generated (q a b : Nat) (hq : 4≤q) (hd : p29Domain q a b) :
    Generated q (p29Set q a b) := by
  exact generated_congr q (NF123.generated q hq (p29NF q a b) (p29_valid q a b hq hd)) (p29_eval q a b · hq hd)
def p30Domain (q a b : Nat) : Prop := ((1)*(q:Int)+3)≤(a:Int) ∧ (a:Int)≤((2)*(q:Int)+(-1)) ∧ (0:Int)≤(b:Int) ∧ (b:Int)≤(0:Int)
def p30NF (q a b : Nat) : NF123 := .dg a
def p30Set (q a b e : Nat) : Prop := (e=1 ∨ e=2 ∨ e=3) ∨ (((5)≤(e:Int) ∧ (e:Int)≤((1)*(a:Int))) ∨ (((2)*(q:Int)+1)≤(e:Int) ∧ (e:Int)≤((4)*(q:Int))))
theorem p30_valid (q a b : Nat) (hq : 4≤q) (hd : p30Domain q a b) : (p30NF q a b).Valid q := by
  simp only [p30Domain] at hd
  simp only [p30NF,NF123.Valid,P,JReachable,g]
  repeat first | omega | split
theorem p30_eval (q a b e : Nat) (hq : 4≤q) (hd : p30Domain q a b) :
    (p30NF q a b).eval q e ↔ p30Set q a b e := by
  simp only [p30Domain] at hd
  simp only [p30NF,p30Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p30_generated (q a b : Nat) (hq : 4≤q) (hd : p30Domain q a b) :
    Generated q (p30Set q a b) := by
  exact generated_congr q (NF123.generated q hq (p30NF q a b) (p30_valid q a b hq hd)) (p30_eval q a b · hq hd)
def p31Domain (q a b : Nat) : Prop := (0:Int)≤(a:Int) ∧ (a:Int)≤(0:Int) ∧ (0:Int)≤(b:Int) ∧ (b:Int)≤(0:Int)
def p31NF (q a b : Nat) : NF123 := .full
def p31Set (q a b e : Nat) : Prop := (e=1 ∨ e=2 ∨ e=3) ∨ (((5)≤(e:Int) ∧ (e:Int)≤((4)*(q:Int))))
theorem p31_valid (q a b : Nat) (hq : 4≤q) (hd : p31Domain q a b) : (p31NF q a b).Valid q := by
  simp only [p31Domain] at hd
  simp only [p31NF,NF123.Valid,P,JReachable,g]
  repeat first | omega | split
theorem p31_eval (q a b e : Nat) (hq : 4≤q) (hd : p31Domain q a b) :
    (p31NF q a b).eval q e ↔ p31Set q a b e := by
  simp only [p31Domain] at hd
  simp only [p31NF,p31Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p31_generated (q a b : Nat) (hq : 4≤q) (hd : p31Domain q a b) :
    Generated q (p31Set q a b) := by
  exact generated_congr q (NF123.generated q hq (p31NF q a b) (p31_valid q a b hq hd)) (p31_eval q a b · hq hd)
def p32Domain (q a b : Nat) : Prop := (4)≤(a:Int) ∧ (a:Int)≤((1)*(q:Int)+1) ∧ (0:Int)≤(b:Int) ∧ (b:Int)≤(0:Int)
def p32NF (q a b : Nat) : NF123 := .creg a
def p32Set (q a b e : Nat) : Prop := (e=1 ∨ e=2 ∨ e=3) ∨ (((5)≤(e:Int) ∧ (e:Int)≤((2)*(q:Int)+2)) ∨ (((3)*(q:Int)+1)≤(e:Int) ∧ (e:Int)≤((3)*(q:Int)+1)) ∨ (((2)*(q:Int)+(1)*(a:Int))≤(e:Int) ∧ (e:Int)≤((4)*(q:Int))))
theorem p32_valid (q a b : Nat) (hq : 4≤q) (hd : p32Domain q a b) : (p32NF q a b).Valid q := by
  simp only [p32Domain] at hd
  simp only [p32NF,NF123.Valid,P,JReachable,g]
  repeat first | omega | split
theorem p32_eval (q a b e : Nat) (hq : 4≤q) (hd : p32Domain q a b) :
    (p32NF q a b).eval q e ↔ p32Set q a b e := by
  simp only [p32Domain] at hd
  simp only [p32NF,p32Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p32_generated (q a b : Nat) (hq : 4≤q) (hd : p32Domain q a b) :
    Generated q (p32Set q a b) := by
  exact generated_congr q (NF123.generated q hq (p32NF q a b) (p32_valid q a b hq hd)) (p32_eval q a b · hq hd)
def p33Domain (q a b : Nat) : Prop := ((1)*(q:Int)+4)≤(a:Int) ∧ (a:Int)≤((2)*(q:Int)+1) ∧ (0:Int)≤(b:Int) ∧ (b:Int)≤(0:Int)
def p33NF (q a b : Nat) : NF123 := .creg a
def p33Set (q a b e : Nat) : Prop := (e=1 ∨ e=2 ∨ e=3) ∨ (((5)≤(e:Int) ∧ (e:Int)≤((2)*(q:Int)+2)) ∨ (((3)*(q:Int)+1)≤(e:Int) ∧ (e:Int)≤((3)*(q:Int)+1)) ∨ (((2)*(q:Int)+(1)*(a:Int)+(-1))≤(e:Int) ∧ (e:Int)≤((4)*(q:Int))))
theorem p33_valid (q a b : Nat) (hq : 4≤q) (hd : p33Domain q a b) : (p33NF q a b).Valid q := by
  simp only [p33Domain] at hd
  simp only [p33NF,NF123.Valid,P,JReachable,g]
  repeat first | omega | split
theorem p33_eval (q a b e : Nat) (hq : 4≤q) (hd : p33Domain q a b) :
    (p33NF q a b).eval q e ↔ p33Set q a b e := by
  simp only [p33Domain] at hd
  simp only [p33NF,p33Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p33_generated (q a b : Nat) (hq : 4≤q) (hd : p33Domain q a b) :
    Generated q (p33Set q a b) := by
  exact generated_congr q (NF123.generated q hq (p33NF q a b) (p33_valid q a b hq hd)) (p33_eval q a b · hq hd)
def p34Domain (q a b : Nat) : Prop := (0:Int)≤(a:Int) ∧ (a:Int)≤(0:Int) ∧ (0:Int)≤(b:Int) ∧ (b:Int)≤(0:Int)
def p34NF (q a b : Nat) : NF123 := .cex
def p34Set (q a b e : Nat) : Prop := (e=1 ∨ e=2 ∨ e=3) ∨ (((5)≤(e:Int) ∧ (e:Int)≤((2)*(q:Int)+2)) ∨ (((3)*(q:Int)+1)≤(e:Int) ∧ (e:Int)≤((4)*(q:Int)+(-1))))
theorem p34_valid (q a b : Nat) (hq : 4≤q) (hd : p34Domain q a b) : (p34NF q a b).Valid q := by
  simp only [p34Domain] at hd
  simp only [p34NF,NF123.Valid,P,JReachable,g]
  repeat first | omega | split
theorem p34_eval (q a b e : Nat) (hq : 4≤q) (hd : p34Domain q a b) :
    (p34NF q a b).eval q e ↔ p34Set q a b e := by
  simp only [p34Domain] at hd
  simp only [p34NF,p34Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p34_generated (q a b : Nat) (hq : 4≤q) (hd : p34Domain q a b) :
    Generated q (p34Set q a b) := by
  exact generated_congr q (NF123.generated q hq (p34NF q a b) (p34_valid q a b hq hd)) (p34_eval q a b · hq hd)
def p35Domain (q a b : Nat) : Prop := (4)≤(a:Int) ∧ (a:Int)≤((1)*(q:Int)+1) ∧ (0:Int)≤(b:Int) ∧ (b:Int)≤(0:Int)
def p35NF (q a b : Nat) : NF123 := .er a
def p35Set (q a b e : Nat) : Prop := (e=1 ∨ e=2 ∨ e=3) ∨ (((5)≤(e:Int) ∧ (e:Int)≤((1)*(a:Int))) ∨ (((2)*(q:Int)+3)≤(e:Int) ∧ (e:Int)≤((4)*(q:Int))))
theorem p35_valid (q a b : Nat) (hq : 4≤q) (hd : p35Domain q a b) : (p35NF q a b).Valid q := by
  simp only [p35Domain] at hd
  simp only [p35NF,NF123.Valid,P,JReachable,g]
  repeat first | omega | split
theorem p35_eval (q a b e : Nat) (hq : 4≤q) (hd : p35Domain q a b) :
    (p35NF q a b).eval q e ↔ p35Set q a b e := by
  simp only [p35Domain] at hd
  simp only [p35NF,p35Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p35_generated (q a b : Nat) (hq : 4≤q) (hd : p35Domain q a b) :
    Generated q (p35Set q a b) := by
  exact generated_congr q (NF123.generated q hq (p35NF q a b) (p35_valid q a b hq hd)) (p35_eval q a b · hq hd)
def p36Domain (q a b : Nat) : Prop := ((1)*(q:Int)+3)≤(a:Int) ∧ (a:Int)≤((2)*(q:Int)+1) ∧ (0:Int)≤(b:Int) ∧ (b:Int)≤(0:Int)
def p36NF (q a b : Nat) : NF123 := .er a
def p36Set (q a b e : Nat) : Prop := (e=1 ∨ e=2 ∨ e=3) ∨ (((5)≤(e:Int) ∧ (e:Int)≤((1)*(a:Int))) ∨ (((2)*(q:Int)+3)≤(e:Int) ∧ (e:Int)≤((4)*(q:Int))))
theorem p36_valid (q a b : Nat) (hq : 4≤q) (hd : p36Domain q a b) : (p36NF q a b).Valid q := by
  simp only [p36Domain] at hd
  simp only [p36NF,NF123.Valid,P,JReachable,g]
  repeat first | omega | split
theorem p36_eval (q a b e : Nat) (hq : 4≤q) (hd : p36Domain q a b) :
    (p36NF q a b).eval q e ↔ p36Set q a b e := by
  simp only [p36Domain] at hd
  simp only [p36NF,p36Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p36_generated (q a b : Nat) (hq : 4≤q) (hd : p36Domain q a b) :
    Generated q (p36Set q a b) := by
  exact generated_congr q (NF123.generated q hq (p36NF q a b) (p36_valid q a b hq hd)) (p36_eval q a b · hq hd)
def p37Domain (q a b : Nat) : Prop := (0:Int)≤(a:Int) ∧ (a:Int)≤(0:Int) ∧ (0:Int)≤(b:Int) ∧ (b:Int)≤(0:Int)
def p37NF (q a b : Nat) : NF123 := .er (q+2)
def p37Set (q a b e : Nat) : Prop := (e=1 ∨ e=2 ∨ e=3) ∨ (((5)≤(e:Int) ∧ (e:Int)≤((1)*(q:Int)+2)) ∨ (((2)*(q:Int)+3)≤(e:Int) ∧ (e:Int)≤((4)*(q:Int))))
theorem p37_valid (q a b : Nat) (hq : 4≤q) (hd : p37Domain q a b) : (p37NF q a b).Valid q := by
  simp only [p37Domain] at hd
  simp only [p37NF,NF123.Valid,P,JReachable,g]
  repeat first | omega | split
theorem p37_eval (q a b e : Nat) (hq : 4≤q) (hd : p37Domain q a b) :
    (p37NF q a b).eval q e ↔ p37Set q a b e := by
  simp only [p37Domain] at hd
  simp only [p37NF,p37Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p37_generated (q a b : Nat) (hq : 4≤q) (hd : p37Domain q a b) :
    Generated q (p37Set q a b) := by
  exact generated_congr q (NF123.generated q hq (p37NF q a b) (p37_valid q a b hq hd)) (p37_eval q a b · hq hd)
def p38Domain (q a b : Nat) : Prop := (4)≤(a:Int) ∧ (a:Int)≤((1)*(q:Int)+1) ∧ (0:Int)≤(b:Int) ∧ (b:Int)≤(0:Int)
def p38NF (q a b : Nat) : NF123 := .ed a
def p38Set (q a b e : Nat) : Prop := (e=1 ∨ e=2 ∨ e=3) ∨ (((5)≤(e:Int) ∧ (e:Int)≤((1)*(a:Int))) ∨ (((2)*(q:Int)+1)≤(e:Int) ∧ (e:Int)≤((4)*(q:Int))))
theorem p38_valid (q a b : Nat) (hq : 4≤q) (hd : p38Domain q a b) : (p38NF q a b).Valid q := by
  simp only [p38Domain] at hd
  simp only [p38NF,NF123.Valid,P,JReachable,g]
  repeat first | omega | split
theorem p38_eval (q a b e : Nat) (hq : 4≤q) (hd : p38Domain q a b) :
    (p38NF q a b).eval q e ↔ p38Set q a b e := by
  simp only [p38Domain] at hd
  simp only [p38NF,p38Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p38_generated (q a b : Nat) (hq : 4≤q) (hd : p38Domain q a b) :
    Generated q (p38Set q a b) := by
  exact generated_congr q (NF123.generated q hq (p38NF q a b) (p38_valid q a b hq hd)) (p38_eval q a b · hq hd)
def p39Domain (q a b : Nat) : Prop := (5)≤(a:Int) ∧ (a:Int)≤((1)*(q:Int)+3) ∧ (0:Int)≤(b:Int) ∧ (b:Int)≤((4)*(q:Int)+(-3)) ∧ (a:Int)+((2)*(q:Int)+(-3))≤(b:Int)
def p39NF (q a b : Nat) : NF14 := .base a b
def p39Set (q a b e : Nat) : Prop := (e=1 ∨ e=4) ∨ ((((1)*(a:Int))≤(e:Int) ∧ (e:Int)≤((1)*(b:Int))))
theorem p39_valid (q a b : Nat) (hq : 4≤q) (hd : p39Domain q a b) : (p39NF q a b).Valid q := by
  simp only [p39Domain] at hd
  simp only [p39NF,NF14.Valid,P,JReachable,g]
  repeat first | omega | split
theorem p39_eval (q a b e : Nat) (hq : 4≤q) (hd : p39Domain q a b) :
    (p39NF q a b).eval q e ↔ p39Set q a b e := by
  simp only [p39Domain] at hd
  simp only [p39NF,p39Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p39_generated (q a b : Nat) (hq : 4≤q) (hd : p39Domain q a b) :
    Generated q (p39Set q a b) := by
  exact generated_congr q (NF14.generated q hq (p39NF q a b) (p39_valid q a b hq hd)) (p39_eval q a b · hq hd)
def p40Domain (q a b : Nat) : Prop := ((1)*(q:Int)+4)≤(a:Int) ∧ (a:Int)≤((2)*(q:Int)+1) ∧ (0:Int)≤(b:Int) ∧ (b:Int)≤((4)*(q:Int)+(-3)) ∧ (a:Int)+((2)*(q:Int)+(-4))≤(b:Int)
def p40NF (q a b : Nat) : NF14 := .base a b
def p40Set (q a b e : Nat) : Prop := (e=1 ∨ e=4) ∨ ((((1)*(a:Int))≤(e:Int) ∧ (e:Int)≤((1)*(b:Int))))
theorem p40_valid (q a b : Nat) (hq : 4≤q) (hd : p40Domain q a b) : (p40NF q a b).Valid q := by
  simp only [p40Domain] at hd
  simp only [p40NF,NF14.Valid,P,JReachable,g]
  repeat first | omega | split
theorem p40_eval (q a b e : Nat) (hq : 4≤q) (hd : p40Domain q a b) :
    (p40NF q a b).eval q e ↔ p40Set q a b e := by
  simp only [p40Domain] at hd
  simp only [p40NF,p40Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p40_generated (q a b : Nat) (hq : 4≤q) (hd : p40Domain q a b) :
    Generated q (p40Set q a b) := by
  exact generated_congr q (NF14.generated q hq (p40NF q a b) (p40_valid q a b hq hd)) (p40_eval q a b · hq hd)
def p41Domain (q a b : Nat) : Prop := ((1)*(q:Int)+4)≤(a:Int) ∧ (a:Int)≤((2)*(q:Int)+1) ∧ (0:Int)≤(b:Int) ∧ (b:Int)≤((4)*(q:Int)+(-3)) ∧ (a:Int)+((2)*(q:Int)+(-4))≤(b:Int)
def p41NF (q a b : Nat) : NF14 := .agap a b
def p41Set (q a b e : Nat) : Prop := (e=1 ∨ e=4) ∨ (((5)≤(e:Int) ∧ (e:Int)≤((1)*(q:Int)+2)) ∨ (((1)*(a:Int))≤(e:Int) ∧ (e:Int)≤((1)*(b:Int))))
theorem p41_valid (q a b : Nat) (hq : 4≤q) (hd : p41Domain q a b) : (p41NF q a b).Valid q := by
  simp only [p41Domain] at hd
  simp only [p41NF,NF14.Valid,P,JReachable,g]
  repeat first | omega | split
theorem p41_eval (q a b e : Nat) (hq : 4≤q) (hd : p41Domain q a b) :
    (p41NF q a b).eval q e ↔ p41Set q a b e := by
  simp only [p41Domain] at hd
  simp only [p41NF,p41Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p41_generated (q a b : Nat) (hq : 4≤q) (hd : p41Domain q a b) :
    Generated q (p41Set q a b) := by
  exact generated_congr q (NF14.generated q hq (p41NF q a b) (p41_valid q a b hq hd)) (p41_eval q a b · hq hd)
def p42Domain (q a b : Nat) : Prop := (5)≤(a:Int) ∧ (a:Int)≤((1)*(q:Int)+3) ∧ (0:Int)≤(b:Int) ∧ (b:Int)≤((3)*(q:Int)) ∧ (a:Int)+((2)*(q:Int)+(-3))≤(b:Int)
def p42NF (q a b : Nat) : NF14 := .bgap a b
def p42Set (q a b e : Nat) : Prop := (e=1 ∨ e=4) ∨ ((((1)*(a:Int))≤(e:Int) ∧ (e:Int)≤((1)*(b:Int))) ∨ (((3)*(q:Int)+2)≤(e:Int) ∧ (e:Int)≤((4)*(q:Int))))
theorem p42_valid (q a b : Nat) (hq : 4≤q) (hd : p42Domain q a b) : (p42NF q a b).Valid q := by
  simp only [p42Domain] at hd
  simp only [p42NF,NF14.Valid,P,JReachable,g]
  repeat first | omega | split
theorem p42_eval (q a b e : Nat) (hq : 4≤q) (hd : p42Domain q a b) :
    (p42NF q a b).eval q e ↔ p42Set q a b e := by
  simp only [p42Domain] at hd
  simp only [p42NF,p42Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p42_generated (q a b : Nat) (hq : 4≤q) (hd : p42Domain q a b) :
    Generated q (p42Set q a b) := by
  exact generated_congr q (NF14.generated q hq (p42NF q a b) (p42_valid q a b hq hd)) (p42_eval q a b · hq hd)
def p43Domain (q a b : Nat) : Prop := ((1)*(q:Int)+4)≤(a:Int) ∧ (a:Int)≤((1)*(q:Int)+4) ∧ (0:Int)≤(b:Int) ∧ (b:Int)≤((3)*(q:Int)) ∧ (a:Int)+((2)*(q:Int)+(-4))≤(b:Int)
def p43NF (q a b : Nat) : NF14 := .bgap a b
def p43Set (q a b e : Nat) : Prop := (e=1 ∨ e=4) ∨ ((((1)*(a:Int))≤(e:Int) ∧ (e:Int)≤((1)*(b:Int))) ∨ (((3)*(q:Int)+2)≤(e:Int) ∧ (e:Int)≤((4)*(q:Int))))
theorem p43_valid (q a b : Nat) (hq : 4≤q) (hd : p43Domain q a b) : (p43NF q a b).Valid q := by
  simp only [p43Domain] at hd
  simp only [p43NF,NF14.Valid,P,JReachable,g]
  repeat first | omega | split
theorem p43_eval (q a b e : Nat) (hq : 4≤q) (hd : p43Domain q a b) :
    (p43NF q a b).eval q e ↔ p43Set q a b e := by
  simp only [p43Domain] at hd
  simp only [p43NF,p43Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p43_generated (q a b : Nat) (hq : 4≤q) (hd : p43Domain q a b) :
    Generated q (p43Set q a b) := by
  exact generated_congr q (NF14.generated q hq (p43NF q a b) (p43_valid q a b hq hd)) (p43_eval q a b · hq hd)
def p44Domain (q a b : Nat) : Prop := (5)≤(a:Int) ∧ (a:Int)≤((2)*(q:Int)+1) ∧ (0:Int)≤(b:Int) ∧ (b:Int)≤(0:Int)
def p44NF (q a b : Nat) : NF14 := .joined a
def p44Set (q a b e : Nat) : Prop := (e=1 ∨ e=4) ∨ ((((1)*(a:Int))≤(e:Int) ∧ (e:Int)≤((4)*(q:Int))))
theorem p44_valid (q a b : Nat) (hq : 4≤q) (hd : p44Domain q a b) : (p44NF q a b).Valid q := by
  simp only [p44Domain] at hd
  simp only [p44NF,NF14.Valid,P,JReachable,g]
  repeat first | omega | split
theorem p44_eval (q a b e : Nat) (hq : 4≤q) (hd : p44Domain q a b) :
    (p44NF q a b).eval q e ↔ p44Set q a b e := by
  simp only [p44Domain] at hd
  simp only [p44NF,p44Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p44_generated (q a b : Nat) (hq : 4≤q) (hd : p44Domain q a b) :
    Generated q (p44Set q a b) := by
  exact generated_congr q (NF14.generated q hq (p44NF q a b) (p44_valid q a b hq hd)) (p44_eval q a b · hq hd)
def p45Domain (q a b : Nat) : Prop := (0:Int)≤(a:Int) ∧ (a:Int)≤(0:Int) ∧ (0:Int)≤(b:Int) ∧ (b:Int)≤(0:Int)
def p45NF (q a b : Nat) : NF14 := .doubleGap
def p45Set (q a b e : Nat) : Prop := (e=1 ∨ e=4) ∨ (((5)≤(e:Int) ∧ (e:Int)≤((1)*(q:Int)+2)) ∨ (((1)*(q:Int)+4)≤(e:Int) ∧ (e:Int)≤((3)*(q:Int))) ∨ (((3)*(q:Int)+2)≤(e:Int) ∧ (e:Int)≤((4)*(q:Int))))
theorem p45_valid (q a b : Nat) (hq : 4≤q) (hd : p45Domain q a b) : (p45NF q a b).Valid q := by
  simp only [p45Domain] at hd
  simp only [p45NF,NF14.Valid,P,JReachable,g]
  repeat first | omega | split
theorem p45_eval (q a b e : Nat) (hq : 4≤q) (hd : p45Domain q a b) :
    (p45NF q a b).eval q e ↔ p45Set q a b e := by
  simp only [p45Domain] at hd
  simp only [p45NF,p45Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p45_generated (q a b : Nat) (hq : 4≤q) (hd : p45Domain q a b) :
    Generated q (p45Set q a b) := by
  exact generated_congr q (NF14.generated q hq (p45NF q a b) (p45_valid q a b hq hd)) (p45_eval q a b · hq hd)
def p46Domain (q a b : Nat) : Prop := ((1)*(q:Int)+4)≤(a:Int) ∧ (a:Int)≤((2)*(q:Int)+1) ∧ (0:Int)≤(b:Int) ∧ (b:Int)≤(0:Int)
def p46NF (q a b : Nat) : NF14 := .ajoined a
def p46Set (q a b e : Nat) : Prop := (e=1 ∨ e=4) ∨ (((5)≤(e:Int) ∧ (e:Int)≤((1)*(q:Int)+2)) ∨ (((1)*(a:Int))≤(e:Int) ∧ (e:Int)≤((4)*(q:Int))))
theorem p46_valid (q a b : Nat) (hq : 4≤q) (hd : p46Domain q a b) : (p46NF q a b).Valid q := by
  simp only [p46Domain] at hd
  simp only [p46NF,NF14.Valid,P,JReachable,g]
  repeat first | omega | split
theorem p46_eval (q a b e : Nat) (hq : 4≤q) (hd : p46Domain q a b) :
    (p46NF q a b).eval q e ↔ p46Set q a b e := by
  simp only [p46Domain] at hd
  simp only [p46NF,p46Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p46_generated (q a b : Nat) (hq : 4≤q) (hd : p46Domain q a b) :
    Generated q (p46Set q a b) := by
  exact generated_congr q (NF14.generated q hq (p46NF q a b) (p46_valid q a b hq hd)) (p46_eval q a b · hq hd)
#print axioms p24_valid
#print axioms p24_eval
#print axioms p24_generated
#print axioms p25_valid
#print axioms p25_eval
#print axioms p25_generated
#print axioms p26_valid
#print axioms p26_eval
#print axioms p26_generated
#print axioms p28_valid
#print axioms p28_eval
#print axioms p28_generated
#print axioms p29_valid
#print axioms p29_eval
#print axioms p29_generated
#print axioms p30_valid
#print axioms p30_eval
#print axioms p30_generated
#print axioms p31_valid
#print axioms p31_eval
#print axioms p31_generated
#print axioms p32_valid
#print axioms p32_eval
#print axioms p32_generated
#print axioms p33_valid
#print axioms p33_eval
#print axioms p33_generated
#print axioms p34_valid
#print axioms p34_eval
#print axioms p34_generated
#print axioms p35_valid
#print axioms p35_eval
#print axioms p35_generated
#print axioms p36_valid
#print axioms p36_eval
#print axioms p36_generated
#print axioms p37_valid
#print axioms p37_eval
#print axioms p37_generated
#print axioms p38_valid
#print axioms p38_eval
#print axioms p38_generated
#print axioms p39_valid
#print axioms p39_eval
#print axioms p39_generated
#print axioms p40_valid
#print axioms p40_eval
#print axioms p40_generated
#print axioms p41_valid
#print axioms p41_eval
#print axioms p41_generated
#print axioms p42_valid
#print axioms p42_eval
#print axioms p42_generated
#print axioms p43_valid
#print axioms p43_eval
#print axioms p43_generated
#print axioms p44_valid
#print axioms p44_eval
#print axioms p44_generated
#print axioms p45_valid
#print axioms p45_eval
#print axioms p45_generated
#print axioms p46_valid
#print axioms p46_eval
#print axioms p46_generated
end SourcePieces
end LuRazClosure
